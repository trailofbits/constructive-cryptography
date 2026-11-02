module

public import Commons.Definitions.Ideal
public import RandomSystems.Typed.QueryRouting
public import RandomSystems.Typed.ParallelAll
/-!
# Two callers of one retained permutation

`sharedStrongURP` routes two caller-tagged bidirectional interfaces to one `StrongURP`.
`request_domain` certifies the sum of the caller allowances. `sharedStrongURP_eq_sample` exposes the
same retained permutation for both callers by the existing sampling and routing attachment laws.

```text
  false.forward(x) ─┐                       ┌───────────────────────┐
                   ├── erase caller tag ───►│ StrongURP: retain π   │
   true.inverse(y) ─┘                       │ forward π; inverse π⁻¹│
       caller reply ◄── restore caller ────└───────────────────────┘
```

`sharedStrongURP_inverse_mass_eq_zero` gives mass zero to the cross-caller transcript
`forward(x) ⇒ y; inverse(y) ⇒ z` when `z ≠ x`. With Boolean inputs and one query per caller,
`independent_roundTrip_mass_pos` gives positive mass to `x = y = false`, `z = true`, witnessed
by the identity and the swap. The closing example combines these facts to separate the shared
system from `parallelAll` on that same interface.
-/

@[expose] public section

open SystemAlgebra Commons Probability Probability.Distribution
open scoped SystemAlgebra
namespace SystemAlgebra.Tests.SharedRouting

-- `X` is the finite permutation alphabet; `q c` bounds the total queries by caller `c : Bool`.
variable (X : Type) [Fintype X] (q : Bool → ℕ)
/-- Caller `c` has both permutation directions and at most `q c` queries in total.
The existing family interface tags each port with `c : Bool`. -/
abbrev callers : Interface :=
  Interface.tensorAll fun c => Bidirectional X (q c)
/-- Erase the caller tag, preserving the permutation direction and input value. -/
def request
    -- `u` carries the caller tag, permutation direction, and input value.
    (u : Σ o, (callers X q).X o) : Σ j, (Bidirectional X (q false + q true)).X j :=
  ⟨u.1.2, u.2⟩
/-- Return the inside reply value at the retained outside caller and direction. -/
def answer
    -- `u` identifies the outside caller and direction; `r` carries the inside reply value.
    (u : Σ o, (callers X q).X o) (r : Σ j, (Bidirectional X (q false + q true)).Y j) :
    (callers X q).Y u.1 := by
  obtain ⟨⟨c, i⟩, x⟩ := u
  obtain ⟨j, y⟩ := r
  cases i <;> cases j <;> exact y
/-- The entire inside history has at most `q false + q true` queries. The certificate covers
both callers together, including pending queries, regardless of the inside replies. -/
lemma request_domain
    -- `hx` admits the combined caller history `xs` on the family interface.
    (xs : List (Σ o, (callers X q).X o)) (hx : (callers X q).domain xs) :
    (Bidirectional X (q false + q true)).domain (xs.map (request X q)) := by
  apply Interface.queryBudget_domain_map (request X q) _ hx
  change (∑ c : Bool, q c) ≤ q false + q true
  rw [Fintype.sum_bool, Nat.add_comm]
/-- Both callers reach one `StrongURP`, with its allowance equal to the sum of their bounds.
The router changes labels only; the permutation and its inverse stay in the shared component. -/
noncomputable def sharedStrongURP : TypedSystem (callers X q) :=
  TypedConverter.routing (request X q) (answer X q) (request_domain X q) •
    StrongURP X (q := q false + q true)
open Classical in
/-- One permutation is sampled for the whole interaction; each caller sees its forward map
and its inverse. Attachment preserves the sample before applying the one-query functional law. -/
lemma sharedStrongURP_eq_sample :
    sharedStrongURP X q = TypedSystem.sample (uniform (Equiv.Perm X)) (fun π =>
      TypedSystem.ofFunction (A := callers X q) (fun
        | ⟨_, .forward⟩ => fun x => π x
        | ⟨_, .inverse⟩ => fun y => π.symm y)) := by
  unfold sharedStrongURP StrongURP
  -- Every caller reaches the same retained draw of the attached component.
  rw [TypedConverter.smul_sample]
  congr 1
  funext π
  -- For each fixed permutation, erasing and restoring the caller changes only its label.
  rw [TypedConverter.routing_smul_ofFunction]
  congr 1
  funext l x
  obtain ⟨c, i⟩ := l
  cases i <;> rfl
/-- Caller `false` asks `forward(x)` and gets `y`; caller `true` asks `inverse(y)` and gets `z`.
Each caller makes one query, and the inside component receives both. -/
def roundTrip
    -- `x` is the forward query, `y` its reply and the inverse query, and `z` the inverse reply.
    (x y z : X) :
    List ((Σ o, (callers X q).X o) × (Σ o, (callers X q).Y o)) :=
  [(⟨⟨false, .forward⟩, x⟩, ⟨⟨false, .forward⟩, y⟩),
   (⟨⟨true, .inverse⟩, y⟩, ⟨⟨true, .inverse⟩, z⟩)]

/-- Cross-caller inversion cannot return `z ≠ x`: both calls use the same permutation. -/
lemma sharedStrongURP_inverse_mass_eq_zero
    -- `x` is the forward query, `y` its reply and the inverse query, and `z` the inverse reply.
    (x y z : X)
    -- `hz` says the inverse reply differs from the original input `x`.
    (hz : z ≠ x) :
    (sharedStrongURP X q).1 (roundTrip X q x y z) = 0 := by
  classical
  rw [sharedStrongURP_eq_sample, TypedSystem.sample_mass]
  -- Every retained permutation gives zero mass to the inconsistent round trip.
  apply Finset.sum_eq_zero
  intro π _
  rw [TypedSystem.ofFunction_mass]
  split_ifs with hc
  · -- Matching the fixed permutation forces `y = π x` and `z = π.symm y`, hence `z = x`.
    have hforward := hc.2 _ (List.mem_cons_self)
    have hinverse := hc.2 _ (List.mem_cons_of_mem _ (List.mem_cons_self))
    have hy : y = π x := eq_of_heq (Sigma.mk.inj_iff.mp hforward).2
    have hz' : z = π.symm y := eq_of_heq (Sigma.mk.inj_iff.mp hinverse).2
    exact False.elim (hz (hz'.trans ((congrArg π.symm hy).trans (π.symm_apply_apply x))))
  · exact mul_zero _

/-- Each caller's one-query allowance admits the two-call transcript, but a single shared
inside allowance does not. The aggregate certificate must therefore charge both callers. -/
example :
    (callers Bool (fun _ => 1)).domain
        ((roundTrip Bool (fun _ => 1) false false true).map Prod.fst) ∧
      ¬ (Bidirectional Bool 1).domain
        (((roundTrip Bool (fun _ => 1) false false true).map Prod.fst).map
          (request Bool (fun _ => 1))) := by
  constructor
  · refine ⟨List.cons_ne_nil _ _, fun c => ?_⟩
    cases c <;>
      simp only [roundTrip, List.map_cons, List.map_nil, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
        restrict_cons_self, restrict_cons_ne Bool.false_ne_true,
        restrict_cons_ne (Ne.symm Bool.false_ne_true), restrict_nil,
        List.cons_ne_nil, false_or, List.length_cons, List.length_nil, Nat.zero_add,
        le_refl, and_true]
    all_goals exact List.cons_ne_nil _ _
  · intro hd
    have hlength := hd.2
    simp only [List.length_map, roundTrip, List.length_cons, List.length_nil] at hlength
    omega

/-- Independent copies can disagree across callers: the identity answers the forward call,
and the swap answers the inverse call. Both permutations have positive uniform mass. -/
lemma independent_roundTrip_mass_pos :
    0 < (TypedSystem.parallelAll (fun _ : Bool => StrongURP Bool (q := 1))).1
      (roundTrip Bool (fun _ => 1) false false true) := by
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_mass]
  have hc : RandomSystem.parallelAllConsistent
      ((roundTrip Bool (fun _ => 1) false false true).map
        ((Equiv.sigmaAssoc fun _ : Bool => (Bidirectional Bool 1).X).prodCongr
          (Equiv.sigmaAssoc fun _ : Bool => (Bidirectional Bool 1).Y))) := by
    intro t ht
    simp only [roundTrip, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at ht
    rcases ht with rfl | rfl <;> rfl
  rw [ite_eq_left hc]
  -- The parallel law multiplies separate component probabilities.
  apply Finset.prod_pos
  intro c _
  -- Use the equality instance retained by the existing uniform permutation law.
  let : DecidableEq Bool := Classical.decEq Bool
  rw [StrongURP, TypedSystem.sample_mass]
  -- One positive supported witness suffices because all other summands are nonnegative.
  apply Finset.sum_pos'
  · intro π _
    exact mul_nonneg (uniform_nonNeg π) (RandomSystem.mass_nonneg _ _)
  · -- Each caller's factor uses its own witness: identity at `false`, swap at `true`.
    let π : Equiv.Perm Bool := if c then Equiv.swap false true else Equiv.refl Bool
    refine ⟨π, Finsupp.mem_support_iff.mpr (ne_of_gt ?_), ?_⟩
    · rw [uniform_apply]
      exact one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    apply mul_pos
    · rw [uniform_apply]
      exact one_div_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    convert (zero_lt_one : (0 : ℝ) < 1) using 1
    cases c <;>
      simp only [roundTrip, List.map_cons, List.map_nil, Equiv.prodCongr_apply,
        Prod.map, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
        RandomSystem.restrictExchanges, Bool.false_eq_true,
        Bool.true_eq_false, ↓reduceDIte, List.filterMap_cons, List.filterMap_nil]
    all_goals
      -- The one-query projection is admitted and matches its witness, so its mass is one.
      apply TypedSystem.ofFunction_mass_eq_one
      · exact Or.inr ⟨List.cons_ne_nil _ _, le_refl 1⟩
      · intro t ht
        obtain rfl := List.mem_singleton.mp ht
        simp only [π, Bool.false_eq_true, ite_false, ite_true, Equiv.refl_apply,
          Equiv.symm_swap, Equiv.swap_apply_left]

/-- Sharing one retained permutation differs from placing independent copies at the callers. -/
example : sharedStrongURP Bool (fun _ => 1) ≠
    TypedSystem.parallelAll (fun _ : Bool => StrongURP Bool (q := 1)) := by
  intro he
  have hm := congrArg (fun R : TypedSystem (callers Bool (fun _ => 1)) =>
    R.1 (roundTrip Bool (fun _ => 1) false false true)) he
  rw [sharedStrongURP_inverse_mass_eq_zero Bool _ _ _ _ (Ne.symm Bool.false_ne_true)] at hm
  exact independent_roundTrip_mass_pos.ne' hm.symm

#print axioms Interface.queryBudget_domain_map
#print axioms sharedStrongURP_eq_sample
#print axioms sharedStrongURP_inverse_mass_eq_zero
#print axioms independent_roundTrip_mass_pos

end SystemAlgebra.Tests.SharedRouting

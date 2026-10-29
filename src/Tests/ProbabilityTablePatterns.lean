import Probability.Counting

/-!
# Uniform random-table laws

Examples of `uniform_mass_transcript_eq`, `Pr[F matches h] = (1/|Y|)^d` for a transcript `h`
answered by a function, with `d` the number of distinct inputs of `h`, and of
`fTransform_eval_uniform_eq_of_same_fibers`,
`Law(i ↦ F (left i)) = Law(i ↦ G (right i))` for query maps with the same equality pattern.
Further examples cover the birthday and pair bounds, fresh and projected replies, events on
disjoint coordinates, and a projection that is not uniform.

```text
h = [(false, true), (false, true)]                  mass 1/2        one coordinate, repeated
h = [(false, true), (false, false)]                 mass 0          contradictory replies
h = [(false, true), (true, false), (false, true)]   mass (1/2)^2    two coordinates, one repeat
i ↦ F false  vs  i ↦ G 0,  G : Fin 3 → Bool         equal laws      different table domains
n ↦ F (n even)  vs  n ↦ G (some (n even)),  n : ℕ   equal laws      infinite index type
ULift.{1} Bool → ULift.{2} Bool                     (1/|Y|)^d       other universes
¬ InjOn F {false},  ¬ InjOn F {false, true}         ≤ 0,  ≤ 1/2     birthday bound
F false = true ∧ F true = false                     halves mass     fresh coordinate
∃ i ≠ j in {0} ⊆ ℕ, δ = -1                          ≤ 0             empty pair event
F true = predict (F false), predict ≡ false         1/2             non-injective predictor
F false = (true, false) ∧ (F true).1 = true         halves mass     projected fresh reply
(F x).1 = z.2.1 for some z ∈ h, z.1 ≠ x             ≤ |h|/2 · mass  projected collision
f 0 = true ∧ f 1 = false,  f : Fin 3 → Bool         factors         fresh output, base {0}
(a, b) ↦ false on uniform Bool × Bool               Pr[true] = 0    not uniform on Bool
good (F false) ∧ output (F true), universes 1, 3, 2 factors         disjoint coordinates
```
-/

namespace Probability.Counting.Tests

/-- `h = [(false, true), (false, true)]` has one distinct input, so for `F` uniform on
`Bool → Bool`, `Pr[F false = true] = (1/2)^1`, not `(1/2)^2`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)), f z.1 = z.2) =
      (1 / 2 : ℝ) := by
  -- `h` is answered by negation `g x = !x`: both entries are `(false, true)` and `!false = true`.
  have hg : ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    have hz' : z = (false, true) := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using hz
    subst z
    rfl
  -- The transcript law with `|S| = |{false}| = 1` and `|Y| = |Bool| = 2` gives `(1/2)^1 = 1/2`.
  convert uniform_mass_transcript_eq
    ([(false, true), (false, true)] : List (Bool × Bool)) (fun x => !x) hg using 1
  norm_num

/-- `h = [(false, true), (false, false)]` gives two replies to one input:
`Pr[F false = true ∧ F false = false] = 0`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, false)] : List (Bool × Bool)), f z.1 = z.2) =
      0 := by
  -- An event satisfied by no table has mass 0.
  apply Distribution.mass_eq_zero_of_forall_not
  -- For any table `F`, `F false = true` and `F false = false` give `true = false`.
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Bool.eq_true_and_eq_false_self] at hf

/-- `h = [(false, true), (true, false), (false, true)]` has distinct inputs `{false, true}`:
`Pr[F false = true ∧ F true = false] = (1/2)^2`; the repeated `(false, true)` adds no factor. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      f z.1 = z.2) = (1 / (2 : ℝ)) ^ 2 := by
  -- `h` is answered by negation: `!false = true` and `!true = false`, entry by entry.
  have hg : ∀ z ∈ ([(false, true), (true, false), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> rfl
  -- The transcript law with `|S| = |{false, true}| = 2` and `|Y| = |Bool| = 2` gives `(1/2)^2`.
  convert uniform_mass_transcript_eq
    ([(false, true), (true, false), (false, true)] : List (Bool × Bool)) (fun x => !x) hg
    using 1
  norm_num

/-- `left i = false` in `Bool` and `right i = 0` in `Fin 3`, for `i : Fin 2`: for `F` uniform on
`Bool → Bool` and `G` uniform on `Fin 3 → Bool`,
`Law(F false, F false) = Law(G 0, G 0)`, both `(U, U)` with `U` uniform on `Bool`. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun _ : Fin 2 => f false)
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Fin 3 → Bool => fun _ : Fin 2 => f 0)
        (Distribution.uniform (Fin 3 → Bool)) := by
  -- Both query maps are constant, so `left i = left j` and `right i = right j` both hold.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  exact iff_of_true rfl rfl

/-- `left n = (n % 2 == 0)` in `Bool` and `right n = some (left n)` in `Option Bool`, for
`n : ℕ`. Both have the classes even and odd, so both outputs have the law of
`(U, V, U, V, …)` with `U`, `V` independent uniform on `Bool`; the index type is infinite. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun n : Nat => f (n % 2 == 0))
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Option Bool → Bool => fun n : Nat =>
        f (some (n % 2 == 0))) (Distribution.uniform (Option Bool → Bool)) := by
  -- `some a = some b ↔ a = b`, so the pattern condition `left i = left j ↔ right i = right j`
  -- becomes `left i = left j ↔ left i = left j`.
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  simp only [Option.some.injEq]

/-- With `X = ULift.{1} Bool` and `Y = ULift.{2} Bool`, a transcript `h` answered by `g` has
`Pr[F matches h] = (1/|Y|)^d`, `d` the number of distinct inputs of `h`. -/
example (h : List (ULift.{1} Bool × ULift.{2} Bool))
    (g : ULift.{1} Bool → ULift.{2} Bool) (hg : ∀ z ∈ h, g z.1 = z.2) :
    (Distribution.uniform (ULift.{1} Bool → ULift.{2} Bool)).mass
        (fun f => ∀ z ∈ h, f z.1 = z.2) =
      (1 / (Fintype.card (ULift.{2} Bool) : ℝ)) ^ (h.map Prod.fst).toFinset.card := by
  -- The transcript law holds at any universes of `X` and `Y`.
  exact uniform_mass_transcript_eq h g hg

/-- `F` uniform on `Bool → Bool`, `s = {false}`: `Pr[F not injective on s] ≤ C(1, 2)/2 = 0`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f ({false} : Finset Bool)) ≤ 0 := by
  -- The birthday bound with `|s| = 1`: `C(1, 2) = 0`.
  simpa only [Finset.coe_singleton, Set.injOn_singleton, not_true_eq_false, Finset.card_singleton,
    Nat.choose_succ_self, CharP.cast_eq_zero, Fintype.card_bool, Nat.cast_ofNat, zero_div] using
    uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) ({false} : Finset Bool)

/-- `F` uniform on `Bool → Bool`, `s = {false, true}`: not injective on `s` is
`F false = F true`, and `Pr ≤ C(2, 2)/2 = 1/2`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f (Finset.univ : Finset Bool)) ≤ (1 / 2 : ℝ) := by
  -- The birthday bound with `|s| = 2` and `|Y| = 2`: one pair, `C(2, 2)/2 = 1/2`.
  simpa only [Fintype.univ_bool, Finset.coe_insert, Finset.coe_singleton, Set.injOn_pair,
    Bool.true_eq_false, imp_false, Decidable.not_not, one_div, Finset.mem_singleton,
    not_false_eq_true, Finset.card_insert_of_notMem, Finset.card_singleton, Nat.reduceAdd,
    Nat.choose_self, Nat.cast_one, Fintype.card_bool, Nat.cast_ofNat] using
    uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) Finset.univ

/-- `F` uniform on `Bool → Bool`, fresh coordinate `true` under the first-reply event
`F false = true`: `Pr[F false = true ∧ F true = false] = Pr[F false = true] / 2`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => f false = true ∧ f true = false) =
      (Distribution.uniform (Bool → Bool)).mass (fun f => f false = true) / 2 := by
  -- The fresh-coordinate law with `x = true`, `y = false` and `|Y| = 2`.
  apply uniform_mass_fresh_eval_eq
  -- Tables agreeing off `true` agree at `false`, so the event ignores `F true`.
  intro f g he
  simp only [he false (by simp only [ne_eq, Bool.false_eq_true, not_false_eq_true])]

/-- For any nonnegative `P : Distribution ℕ`, not necessarily normalized, and the singleton
`s = {0}` of the infinite index type `ℕ`, the pair event `∃ i, j ∈ s, i ≠ j ∧ bad i j` is empty:
the pair bound gives mass `≤ C(1, 2) · δ = 0` even for `δ = -1`. -/
example (P : Distribution ℕ) (hP : P.NonNeg) (bad : ℕ → ℕ → ℕ → Prop)
    (hsym : ∀ i j ω, bad i j ω → bad j i ω) :
    P.mass (fun ω => ∃ i ∈ ({0} : Finset ℕ), ∃ j ∈ ({0} : Finset ℕ),
      i ≠ j ∧ bad i j ω) ≤ 0 := by
  -- The pair bound with `δ = -1`.
  have h := Distribution.mass_exists_pair_le_choose P hP {0} bad hsym (-1)
    (by
      -- Vacuous: `i, j ∈ {0}` gives `i = 0 = j`, contradicting `i ≠ j`.
      intro i hi j hj hij
      have hi0 := Finset.mem_singleton.mp hi
      have hj0 := Finset.mem_singleton.mp hj
      exact (hij (hi0.trans hj0.symm)).elim)
  -- `C(1, 2) = 0`, so the bound is `0 · (-1) = 0`.
  simpa only [Finset.card_singleton, Nat.choose_eq_zero_of_lt (show 1 < 2 by omega),
    Nat.cast_zero, zero_mul] using h

/-- A constant predictor is not injective, but it still guesses a fresh Boolean reply with
probability `1/2`: `Pr[F true = (fun _ => false) (F false)] = 1/2`. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => f true = (fun _ : Bool => false) (f false)) = (1 / 2 : ℝ) := by
  -- The graph law with `x = false`, `z = true` and `|Y| = 2`; `predict` need not be injective.
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using
    uniform_two_outputs_graph_mass false true Bool.false_ne_true (fun _ : Bool => false)

/-- `Prod.fst` sends the uniform law on `Bool × Bool` to the uniform law on `Bool`. -/
lemma pair_first_uniform :
    Distribution.fTransform Prod.fst (Distribution.uniform (Bool × Bool)) =
      Distribution.uniform Bool := by
  rw [← Distribution.prod_uniform, Distribution.fTransform_fst_prod,
    Distribution.weight_uniform, one_smul]

/-- For uniform `f : Bool → Bool × Bool`,
`Pr[f false = (true, false) ∧ (f true).1 = true] = Pr[f false = (true, false)] / 2`:
the event keeps the full old reply, the new test reads only the first bit. -/
example : (Distribution.uniform (Bool → Bool × Bool)).mass
    (fun f => f false = (true, false) ∧ (f true).1 = true) =
      (Distribution.uniform (Bool → Bool × Bool)).mass
        (fun f => f false = (true, false)) / 2 := by
  apply uniform_mass_fresh_projected_eval_eq Prod.fst pair_first_uniform
  -- The event reads only `f false`, not the fresh coordinate `true`.
  intro f g he
  simp only [he false Bool.false_ne_true]

/-- The collision bound with `project = Prod.fst`, `|Z| = 2`: the history keeps full replies
`(a, (b₁, b₂))`, while the bad event compares first bits only. -/
example (h : List (Bool × (Bool × Bool))) (x : Bool)
    (hg : ∀ a ∈ h, ∀ b ∈ h, a.2.1 = b.2.1 → a.1 = b.1) :
    (Distribution.uniform (Bool → Bool × Bool)).mass (fun f =>
      (∀ z ∈ h, f z.1 = z.2) ∧ ∃ z ∈ h, z.1 ≠ x ∧ (f x).1 = z.2.1) ≤
        (h.length : ℝ) / 2 *
          (Distribution.uniform (Bool → Bool × Bool)).mass
            (fun f => ∀ z ∈ h, f z.1 = z.2) := by
  simpa only [Fintype.card_bool, Nat.cast_ofNat] using
    uniform_mass_transcript_projected_collision_le Prod.fst
    pair_first_uniform h x hg

/-- For uniform `f : Fin 3 → Bool`, `base = {0}` and `next () = 1`:
`Pr[f 0 = true ∧ f 1 = false] = Pr[f 0 = true] · Pr_{g ← U(Unit → Bool)}[g () = false]`. -/
example : (Distribution.uniform (Fin 3 → Bool)).mass
    (fun f => f 0 = true ∧ f 1 = false) =
      (Distribution.uniform (Fin 3 → Bool)).mass (fun f => f 0 = true) *
        (Distribution.uniform (Unit → Bool)).mass (fun g => g () = false) := by
  -- `next` is injective, `1 ∉ {0}`, fallback `false`; `good` reads only `f 0`.
  simpa only [Fin.isValue] using uniform_mass_fresh_outputs_eq ({0} : Finset (Fin 3))
    (fun _ : Unit => 1) (by intro a b _; cases a; cases b; rfl)
    (by intro i; cases i; simp only [Fin.isValue, Finset.mem_singleton, one_ne_zero,
      not_false_eq_true]) false
    (fun f => f 0 = true) (fun g => g () = false)
    (by
      intro f g h
      have h0 := h 0 (Finset.mem_singleton_self _)
      simp only [h0])

/-- The constant projection `p (a, b) = false` does not send the uniform law on `Bool × Bool`
to the uniform law on `Bool`: `Pr[p (a, b) = true] = 0`, whereas `Pr_U[true] = 1/2`. -/
example : Distribution.fTransform (fun _ : Bool × Bool => false)
    (Distribution.uniform (Bool × Bool)) ≠ Distribution.uniform Bool := by
  -- Assume the laws are equal; then they give the event `{true}` the same mass.
  intro h
  have hm := congrArg (fun P : Distribution Bool => P.mass (fun b => b = true)) h
  -- Left: `Pr[false = true] = 0`, no pair satisfies it. Right: `Pr_U[true] = 1/|Bool| = 1/2`.
  -- So `0 = 1/2`, a contradiction.
  rw [Distribution.mass_fTransform,
    Distribution.mass_eq_zero_of_forall_not _ (fun _ => Bool.false_ne_true),
    Distribution.mass_singleton, Distribution.uniform_apply] at hm
  norm_num at hm

/-- The base and output index types and reply alphabet may inhabit different universes:
`B = ULift.{1} Unit`, `I = ULift.{3} Unit`, `Y = ULift.{2} Bool`. For uniform `F : Bool → Y`,
base query `false` and next query `true`,
`Pr[good (F false) ∧ output (F true)] = Pr[good (F false)] · Pr_{g ← U(I → Y)}[output g]`. -/
example (good : (ULift.{1} Unit → ULift.{2} Bool) → Prop)
    (output : (ULift.{3} Unit → ULift.{2} Bool) → Prop) :
    (Distribution.uniform (Bool → ULift.{2} Bool)).mass
        (fun f => good (fun _ => f false) ∧ output (fun _ => f true)) =
      (Distribution.uniform (Bool → ULift.{2} Bool)).mass
        (fun f => good (fun _ => f false)) *
          (Distribution.uniform (ULift.{3} Unit → ULift.{2} Bool)).mass output := by
  refine uniform_mass_disjoint_events (fun _ : ULift.{1} Unit => false)
    (fun _ : ULift.{3} Unit => true) ?_ good output
  -- The two constant query maps have singleton sources and distinct images.
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (Subsingleton.elim a b)
    | inr b => exact (Bool.false_ne_true h).elim
  | inr a =>
    cases b with
    | inl b => exact (Bool.false_ne_true h.symm).elim
    | inr b => exact congrArg Sum.inr (Subsingleton.elim a b)

#print axioms Probability.Counting.uniform_mass_transcript_eq
#print axioms Probability.Counting.fTransform_eval_uniform_eq_of_same_fibers
#print axioms Probability.Counting.uniform_mass_fresh_eval_eq
#print axioms Probability.Counting.uniform_mass_not_injOn_le_choose
#print axioms Probability.Counting.uniform_mass_transcript_projected_collision_le
#print axioms Probability.Counting.uniform_mass_disjoint_events
#print axioms Probability.Counting.uniform_mass_fresh_outputs_eq
#print axioms Probability.Distribution.mass_exists_pair_le_choose

end Probability.Counting.Tests

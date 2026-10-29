import RandomSystems.Typed.ParallelAllAttachment
import RandomSystems.Typed.ParallelAllRegroup

import RandomSystems.Typed.ParallelAllPresentation
import ConstructiveCryptography.Notation

/-!
# Typed finite parallel families

Audits of `⨂ k, A k`, `∥ k, R k` and `⨂ₘ k, α k` over `K = Bool`:

* a heterogeneous family (alphabet `Bool`, budget 2; alphabet `Unit`, budget 1) has bound
  `2 + 1 = 3`, and fixed functions on it assemble componentwise;
* its domain is checked per component: two queries at the budget-1 component are rejected,
  although `2 ≤ 3`;
* replies only at the queried label: a reply at another component, or at another port of the
  queried component, has mass 0;
* DDCs `a k` with bounds `b k` give `⨂ₘ k, ofDDC (a k) = ofDDC (tensorAllL a)`, of bound
  `max_k b k`;
* `parallelAllPDS P` presents `∥ k, ofPDS (P k)`, also on the heterogeneous family;
* one bit drawn once outside `∥` differs from one bit drawn per component inside `∥`, and any
  PDS presenting the retained bit, sampled independently per component, has the latter law;
* the prefix `∥ k, R k` and the binary infix `R ∥ S` parse together.

`sharedBit`, one draw outside `∥`:

                    ┌─ c ← U(Bool) ─┐
  ── ⟨false,()⟩ ──▶│ fixedBit c    │
  ◀─ ⟨false,()⟩ ⇒ c│               │
  ── ⟨true,()⟩ ───▶│ fixedBit c    │
  ◀─ ⟨true,()⟩ ⇒ c │               │
                    └───────────────┘

`independentBit`, one draw per component, inside `∥`:

                     ┌───────────────┐
  ── ⟨false,()⟩ ───▶│ c₀ ← U(Bool)  │
  ◀─ ⟨false,()⟩ ⇒ c₀│ fixedBit c₀   │
                     ├───────────────┤
  ── ⟨true,()⟩ ────▶│ c₁ ← U(Bool)  │
  ◀─ ⟨true,()⟩ ⇒ c₁ │ fixedBit c₁   │
                     └───────────────┘

The mixed replies `⟨false,()⟩ ⇒ false`, `⟨true,()⟩ ⇒ true` have probability 0 for
`sharedBit` and `1/2 · 1/2 = 1/4` for `independentBit`.
-/

namespace SystemAlgebra.Tests

open SystemAlgebra
open scoped SystemAlgebra

noncomputable section

/-- Two components with different alphabets and budgets, each with the single port `()`:
`false` has `X = Y = Bool` and at most 2 queries, `true` has `X = Y = Unit` and at most 1. -/
def heterogeneousFamily : Bool → Interface
  | false => Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2
  | true => Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 1

/-- The bound of the family is the sum of the budgets, `2 + 1`. -/
example : (⨂ k, heterogeneousFamily k).bound = 3 := by
  simp only [Fintype.univ_bool, heterogeneousFamily, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Nat.reduceAdd]

/-- Fixed functions on the heterogeneous family assemble componentwise:
`ofFunction (fun ⟨k, i⟩ x => f k i x) = ∥ k, ofFunction (f k)`. -/
example (f : ∀ k i, (heterogeneousFamily k).X i → (heterogeneousFamily k).Y i) :
    TypedSystem.ofFunction (A := ⨂ k, heterogeneousFamily k)
      (fun l x => f l.1 l.2 x) =
      ∥ k, TypedSystem.ofFunction (f k) :=
  TypedSystem.ofFunction_parallelAll f

/-- **Heterogeneous presentations**: for laws `P k` on DDSs on `heterogeneousFamily k` with
exact domains, `∥ k, ofPDS (P k) = ofPDS (parallelAllPDS P)`, although the two components use
different alphabets and budgets. -/
example (P : ∀ k : Bool, Probability.Distribution.ProbDist
    {s : InterfaceSystem (heterogeneousFamily k).I (heterogeneousFamily k).X
      (heterogeneousFamily k).Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧
        ∀ h, (s h).Dom ↔ (heterogeneousFamily k).domain h}) :
    (∥ k, TypedSystem.ofPDS (P k)) =
      TypedSystem.ofPDS (TypedSystem.parallelAllPDS P) :=
  TypedSystem.parallelAll_ofPDS P

/-- **Per-component budgets**: `⟨true, ()⟩(())` twice is rejected. Its length 2 is within the
sum bound 3, but `h|true = [(), ()]` exceeds the budget 1 of component `true`. -/
example : ¬ (⨂ k, heterogeneousFamily k).domain
    [⟨⟨true, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩] := by
  -- Admission would make the projection `h|true` empty or admitted by `true`'s budget.
  intro h
  have ht := h.2 true
  -- `h|true = [(), ()]`: nonempty, and two queries exceed the budget 1.
  simp only [List.map_cons, List.map_nil, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
    restrict_cons_self, restrict_nil] at ht
  change ([(⟨(), ()⟩ : Σ _ : Unit, Unit), ⟨(), ()⟩] = [] ∨
    (Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 1).domain
      [⟨(), ()⟩, ⟨(), ()⟩]) at ht
  norm_num [Interface.queryBudget, List.cons_ne_nil] at ht

/-- **Wrong component**: `⟨false, ()⟩(true)` answered `⟨true, ()⟩ ⇒ ()` has mass 0. The reply
`()` is well typed at component `true`, but not at the queried label. -/
example (R : ∀ k, TypedSystem (heterogeneousFamily k)) :
    (∥ k, R k).1 [(⟨⟨false, ()⟩, true⟩, ⟨⟨true, ()⟩, ()⟩)] = 0 := by
  -- The mass is `∏ k, (R k)(h|k)` if every reply carries its query's tag, and 0 otherwise.
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_mass]
  -- The query tag `false` differs from the reply tag `true`: inconsistent, so mass 0.
  simp only [RandomSystem.parallelAllConsistent, List.map_cons, List.map_nil,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, Bool.false_eq_true, ↓reduceIte]

/-- **Right component, wrong port**: components with ports `false`, `true`, both
`() ⇒ Bool`; `⟨true, false⟩(())` answered `⟨true, true⟩ ⇒ false` has mass 0. Matching
component tags are not enough. -/
example (R : Bool → TypedSystem
    (Interface.queryBudget Bool (fun _ => Unit) (fun _ => Bool) 2)) :
    (∥ k, R k).1 [(⟨⟨true, false⟩, ()⟩, ⟨⟨true, true⟩, false⟩)] = 0 := by
  -- `R true` replies at its queried port: `false(())` answered `true ⇒ false` has mass 0.
  have hz : (R true).1 [(⟨false, ()⟩, ⟨true, false⟩)] = 0 :=
    (R true).2 [] _ _ (by intro h; cases h)
  -- The tags agree, so the mass is `(R true)(h|true) · (R false)(h|false)`, with
  -- `h|true` the one exchange above and `h|false = []`.
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_mass]
  simp only [RandomSystem.parallelAllConsistent, List.map_cons, List.map_nil,
    Equiv.prodCongr_apply, Prod.map_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq, ↓reduceIte,
    Fintype.univ_bool, Finset.prod_insert, Finset.mem_singleton, Bool.true_eq_false,
    not_false_eq_true, Finset.prod_singleton, RandomSystem.restrictExchanges_cons_self]
  -- The factor of component `true` is 0.
  change (R true).1 [(⟨false, ()⟩, ⟨true, false⟩)] * _ = 0
  rw [hz, zero_mul]

/-- **Deterministic converters**: let each `a k` be a DDC from `(B k).domain` (inside) to
`(A k).domain` (outside), making at most `b k` inside queries per outside query, with the
`b k` allowed to differ. Then `⨂ₘ k, ofDDC (a k) = ofDDC (tensorAllL a)`, where `tensorAllL a`
has bound `max_k b k` and domains `⨂ k, A k` (outside) and `⨂ k, B k` (inside). -/
example {A B : Bool → Interface} {b : Bool → ℕ}
    (a : ∀ k, InsideOutsideSystem (A k).I (B k).I (A k).X (A k).Y (B k).X (B k).Y)
    (ha : ∀ k, IsDDCFrom (B k).domain (A k).domain (b k) (a k)) :
    (⨂ₘ k, TypedConverter.ofDDC (a k) (ha k)) =
      TypedConverter.ofDDC (tensorAllL a) (IsDDCFrom.tensorAllL ha) :=
  PDCBehavior.tensorAll_ofDDC ha

/-- One port `()`, input `()`, reply in `Bool`; at most one query. -/
abbrev bitInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- On `bitInterface`, no randomness or state: `()(()) ⇒ c`. -/
def fixedBit (c : Bool) : TypedSystem bitInterface :=
  TypedSystem.ofFunction fun _ _ => c

/-- On `⨂ _k : Bool, bitInterface`: one `c ← U(Bool)`, drawn outside `∥` and shared by both
components; `⟨k, ()⟩(()) ⇒ c` for each `k`. -/
def sharedBit : TypedSystem (⨂ _k : Bool, bitInterface) :=
  TypedSystem.sample (Probability.Distribution.uniform Bool)
    (fun c => ∥ _k : Bool, fixedBit c)

/-- On `⨂ _k : Bool, bitInterface`: each component draws its own `cₖ ← U(Bool)` inside `∥`;
`⟨k, ()⟩(()) ⇒ cₖ`, with `c₀`, `c₁` independent. -/
def independentBit : TypedSystem (⨂ _k : Bool, bitInterface) :=
  ∥ _k : Bool, TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit

/-- The transcript `⟨false, ()⟩(()) ⇒ false`, then `⟨true, ()⟩(()) ⇒ true`: the two
components reply with different bits. -/
def mixedReplies : List
    ((Σ l, (⨂ _k : Bool, bitInterface).X l) ×
      (Σ l, (⨂ _k : Bool, bitInterface).Y l)) :=
  [(⟨⟨false, ()⟩, ()⟩, ⟨⟨false, ()⟩, false⟩),
    (⟨⟨true, ()⟩, ()⟩, ⟨⟨true, ()⟩, true⟩)]

/-- **One shared bit**: `Pr[mixedReplies] = ∑ c, 1/2 · Pr_c[mixedReplies] = 0`, since for
each `c` both components reply `c`. -/
lemma sharedBit_mixedReplies_eq_zero : sharedBit.1 mixedReplies = 0 := by
  -- Average over the shared `c`; every term vanishes.
  rw [sharedBit, TypedSystem.sample_mass]
  apply Finset.sum_eq_zero
  intro c _
  -- For fixed `c`, the family of constants is the constant function (`ofFunction_parallelAll`).
  have he : (∥ _k : Bool, fixedBit c) =
      TypedSystem.ofFunction (A := ⨂ _k : Bool, bitInterface) (fun _ _ => c) := by
    simpa only [fixedBit] using (TypedSystem.ofFunction_parallelAll
      (A := fun _k : Bool => bitInterface) (fun _k _ _ => c)).symm
  -- It gives `mixedReplies` mass 1 only if `c = false` and `c = true`, so mass 0.
  rw [he, TypedSystem.ofFunction_mass]
  simp only [mixedReplies, reduceCtorEq, ne_eq, List.map_cons, List.map_nil, false_or,
    List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, Sigma.mk.injEq, heq_eq_eq,
    Bool.false_eq, true_and, forall_eq, Bool.true_eq, Bool.eq_false_and_eq_true_self, and_false,
    ↓reduceIte, mul_zero]

/-- **Independent bits**: `Pr[mixedReplies] = Pr[c₀ = false] · Pr[c₁ = true] = 1/4`. -/
lemma independentBit_mixedReplies_eq_quarter :
    independentBit.1 mixedReplies = (1 / 4 : ℝ) := by
  -- The mass is the product over components on the regrouped transcript, if consistent.
  rw [independentBit, TypedSystem.parallelAll_mass, RandomSystem.parallelAll_mass]
  -- Each reply carries its query's tag.
  have hc : RandomSystem.parallelAllConsistent
      (mixedReplies.map ((Equiv.sigmaAssoc fun _k : Bool => bitInterface.X).prodCongr
        (Equiv.sigmaAssoc fun _k : Bool => bitInterface.Y))) := by
    simp only [mixedReplies, RandomSystem.parallelAllConsistent, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      Equiv.prodCongr_apply, Prod.map_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk, and_self]
  rw [if_pos hc]
  -- One component, one exchange: `()(()) ⇒ c` has mass `Pr[c' = c] = 1/2` for `c' ← U(Bool)`.
  have single (c : Bool) :
      (TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit).1
        [(⟨(), ()⟩, ⟨(), c⟩)] = (1 / 2 : ℝ) := by
    rw [TypedSystem.sample_mass]
    cases c <;>
      norm_num [Fintype.univ_bool, fixedBit, TypedSystem.ofFunction_mass, bitInterface,
        Probability.Distribution.uniform_apply]
  -- Project over `univ = {true, false}`: `h|true = [()(()) ⇒ true]`, `h|false = [()(()) ⇒ false]`.
  simp only [mixedReplies, List.map_cons, List.map_nil, Equiv.prodCongr_apply,
    Prod.map_apply, Equiv.sigmaAssoc, Equiv.coe_fn_mk, Fintype.univ_bool,
    Finset.prod_insert, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.prod_singleton, RandomSystem.restrictExchanges_cons_self,
    RandomSystem.restrictExchanges_cons_of_ne (show false ≠ true by intro h; cases h),
    RandomSystem.restrictExchanges_cons_of_ne (show true ≠ false by intro h; cases h)]
  change (TypedSystem.sample _ fixedBit).1 [(⟨(), ()⟩, ⟨(), true⟩)] *
    (TypedSystem.sample _ fixedBit).1 [(⟨(), ()⟩, ⟨(), false⟩)] = _
  -- `1/2 · 1/2 = 1/4`.
  rw [single, single]
  norm_num

/-- **Independent presentations of a retained bit**: let `P` be any law on DDSs on
`bitInterface` with `ofPDS P = sample U(Bool) fixedBit`, one bit `c ← U(Bool)` drawn once and
answered `()(()) ⇒ c`. Sampling one DDS per component, `st ∼ piDep (fun _ => P)`, gives

  `ofPDS (parallelAllPDS (fun _ => P)) mixedReplies = 1/4`,

the mass of `independentBit`, not the mass `0` of `sharedBit`. -/
example (P : Probability.Distribution.ProbDist
    {s : InterfaceSystem bitInterface.I bitInterface.X bitInterface.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ bitInterface.domain h})
    (hp : TypedSystem.ofPDS P =
      TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit) :
    (TypedSystem.ofPDS (TypedSystem.parallelAllPDS (fun _ : Bool => P))).1 mixedReplies =
      (1 / 4 : ℝ) := by
  -- Back to the behavior: `ofPDS (parallelAllPDS (fun _ => P)) = ∥ _k, ofPDS P`.
  rw [← TypedSystem.parallelAll_ofPDS]
  -- Each component `ofPDS P` is the retained bit, so the system is `independentBit`.
  simp only [hp]
  -- Its `mixedReplies` mass is `1/2 · 1/2 = 1/4`.
  exact independentBit_mixedReplies_eq_quarter

/-- One bit shared outside `∥` differs from independent bits inside `∥`. -/
example : sharedBit ≠ independentBit := by
  -- Equal systems give `mixedReplies` equal mass, but `0 ≠ 1/4`.
  intro he
  have hm := congrArg (fun R : TypedSystem (⨂ _k : Bool, bitInterface) => R.1 mixedReplies) he
  rw [sharedBit_mixedReplies_eq_zero, independentBit_mixedReplies_eq_quarter] at hm
  norm_num at hm

/-- Locality elaborates directly for heterogeneous stochastic components. -/
example (α : ∀ k, TypedConverter (heterogeneousFamily k) (heterogeneousFamily k))
    (R : ∀ k, TypedSystem (heterogeneousFamily k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) :=
  TypedConverter.parallelAll_attach α R

/-- The same statement admits the empty family without a positive budget assumption. -/
example {A B : Empty → Interface} (α : ∀ k, TypedConverter (A k) (B k))
    (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) :=
  TypedConverter.parallelAll_attach α R

/-- A component budget of one permits two total queries; a shared total budget of one does not. -/
example :
    (⨂ _k : Bool, bitInterface).domain
      [⟨⟨false, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩] ∧
    ¬ (Interface.queryBudget (Σ _k : Bool, Unit) (fun _ => Unit) (fun _ => Bool) 1).domain
      [⟨⟨false, ()⟩, ()⟩, ⟨⟨true, ()⟩, ()⟩] := by
  simp [Interface.tensorAll, parallelAllInputs, bitInterface,
    Interface.queryBudget, Equiv.sigmaAssoc, SystemAlgebra.restrict]

/-- The binary bridge retains both the family tag and the component's local port. -/
example {A : Option Unit → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (⨂ k, A k).X l) × (Σ l, (⨂ k, A k).Y l))) :
    (∥ k, R k).1 h = (TypedSystem.parallel (R none) (R (some ()))).1
      (h.map ((Interface.optionFamilyAlphabet fun k => (A k).X).prodCongr
        (Interface.optionFamilyAlphabet fun k => (A k).Y))) :=
  TypedSystem.parallelAll_option_mass R h

#print axioms SystemAlgebra.parAll_interconnect_all
#print axioms SystemAlgebra.trim_apply_tensorAllL_parAll
#print axioms SystemAlgebra.TypedConverter.parallelAll_attach
#print axioms SystemAlgebra.TypedConverter.parallelAll_attach_ofFunction
#print axioms SystemAlgebra.TypedSystem.parallelAll_option_mass


/-- The prefix finite-family notation and the binary parallel notation parse together:
`(∥ k, R k) ∥ S` groups the family as the left component of the binary product. -/
example {A : Bool → Interface} {B : Interface}
    (R : ∀ k, TypedSystem (A k)) (S : TypedSystem B) :
    (∥ k, R k) ∥ S = TypedSystem.parallel (TypedSystem.parallelAll R) S := rfl

-- The finite parallel family stays within the standard axioms.
#print axioms SystemAlgebra.TypedSystem.parallelAll
#print axioms SystemAlgebra.TypedSystem.ofFunction_parallelAll
#print axioms SystemAlgebra.TypedConverter.parallelAll
#print axioms SystemAlgebra.TypedSystem.parallelAll_ofPDS

end
end SystemAlgebra.Tests

import ConstructiveCryptography.Substitution.Implication
import ConstructiveCryptography.Substitution.Reduction

set_option autoImplicit false

/-!
# Concrete and mixed substitution chains

A chain may mix uses of assumptions, each bounded by a distinguisher-indexed error, with
statistical steps bounded by a distance; a selection of positions marks the assumption uses.
The errors of all steps add up along the chain.

Chains are the `Implication` witnesses of `ConstructiveCryptography.Substitution.Basic`, and
errors are read in a `DistinguisherAdvantage` model of
`ConstructiveCryptography.Substitution.Reduction`. Three kinds of data are kept apart:

```text
resource identities   start_eq, link_eq, end_eq                exact equalities, no error
approximation bounds  error j D, loss j D, statisticalError j  one budget per position j
multiplicity counts   usageCount, selectedUsageCount           numbers of positions, no error
```

For each distinguisher `D`, the conclusion bounds the advantage between the two endpoints by
the sum over all positions of that position's budget at `D`. Budgets are attached to
positions, so a regrouping by assumption name, `Σᵢ selectedUsageCount i • εᵢ`, needs equal
budgets at equal names and is not stated here.

## Main definitions

* `Implication.selectedUsageCount`: uses of an assumption at the selected positions

## Main results

* `Implication.substitutesWithin`: a chain of concrete steps
* `Implication.substitutesWithin_of_mixed`: a chain of concrete and statistical steps

Source: Banfi 2023, §2.3.1; Jost, Theorem 2.2.10.
-/

namespace ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication

open CategoryTheory
open scoped BigOperators

universe u v w x y

variable
    -- `C` is the category of interfaces; `A ⟶ B` is a converter with outside `A`, inside `B`.
    {C : Type u} [Category.{v} C]
    -- `Phi A` is the type of resources on `A`; `attach α : Phi B → Phi A` for `α : A ⟶ B`.
    {Phi : C → Type w} [ResourceTheory C Phi]
-- ι (iota) names the assumptions; `boundary i : C` is the interface of assumption `i`.
variable {ι : Type x} {boundary : ι → C}
-- `systems i b : Phi (boundary i)` is `X_{i,b}`: `false ↦ X_{i,0}`, `true ↦ X_{i,1}`.
variable {systems : ∀ i, Bool → Phi (boundary i)}
variable
    -- `target : C` is the chain's interface; chains have `uses + 1` positions.
    {target : C} {uses : Nat}
    -- `Distinguisher A` is the type of candidate distinguishers on interface `A`.
    {Distinguisher : C → Type y}

/-- Count only the positions justified by the selected named assumptions.
Banfi, Section 2.3.1 (printed pp. 14--15): "the number of times each
substitution"; approximate steps used instead of assumptions are excluded.

```text
selectedUsageCount selected i = #{ j | selected j = true ∧ index j = i }
```

which is at most `usageCount i` (this bound is not stated as a lemma). -/
def selectedUsageCount [DecidableEq ι]
    (implication : Implication boundary systems target uses)
    -- `selected j = true` marks position `j` as a use of a named assumption, `false` as a
    -- statistical step; `assumption : ι` is the name whose selected uses are counted.
    (selected : Fin (uses + 1) → Bool) (assumption : ι) : Nat :=
  (Finset.univ.filter fun position =>
    selected position = true ∧ implication.index position = assumption).card

/-- An explicit finite implication accumulates the concrete losses at its
transformed, oriented steps. Banfi, Section 2.3.3 (printed p. 16), keeps
the loss "ε(Dκρ)" dependent on the actual reduced distinguisher. The endpoints substitute
within `D ↦ Σⱼ error j D`; only the advantage triangle inequality and the exact joins are
used, not symmetry. -/
lemma substitutesWithin
    -- `model` selects `model.admissible A` and the advantage `model.advantage A D S T` on
    -- each interface `A`.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `implication` is the chain from `targetLeft` to `targetRight` on `target`.
    (implication : Implication boundary systems target uses)
    -- `error j D` is the budget of position `j` for the distinguisher `D` on `target`.
    (error : Fin (uses + 1) → Distinguisher target → ENNReal)
    -- `step j`: the transformed, oriented pair `ρⱼ(X_{iⱼ,bⱼ})`, `ρⱼ(X_{iⱼ,¬bⱼ})` on `target`
    -- substitutes within `error j`; reducing this to a premise on `boundary (index j)` (e.g.
    -- by `SubstitutesWithin.attach`) is the caller's task.
    (step : ∀ position, model.SubstitutesWithin (error position)
      (attach (implication.transformation position)
        (systems (implication.index position) (implication.direction position)))
      (attach (implication.transformation position)
        (systems (implication.index position) (!(implication.direction position))))) :
    model.SubstitutesWithin (fun distinguisher => ∑ position, error position distinguisher)
      implication.targetLeft implication.targetRight := by
  intro distinguisher admitted
  -- The finite triangle calculation uses only the displayed exact joins: for a fixed
  -- distinguisher, steps `left j`, `right j` with `right j = left (j + 1)` give
  -- `advantage (left 0) (right n) ≤ Σⱼ budget j`, by induction on the number of steps.
  have chain : ∀ (n : Nat) (left right : Fin (n + 1) → Phi target)
      (budget : Fin (n + 1) → ENNReal),
      (∀ position, model.advantage target distinguisher (left position) (right position) ≤
        budget position) →
      (∀ position : Fin n, right position.castSucc = left position.succ) →
      model.advantage target distinguisher (left 0) (right (Fin.last n)) ≤
        ∑ position, budget position := by
    intro n
    induction n with
    | zero =>
      intro left right budget bounds _
      exact (bounds 0).trans_eq (Fin.sum_univ_one budget).symm
    | succ n inductionHypothesis =>
      intro left right budget bounds joins
      -- Retain the prefix, then join the last pair at its exact middle.
      have prefixBound := inductionHypothesis
        (fun i => left i.castSucc) (fun i => right i.castSucc)
        (fun i => budget i.castSucc) (fun i => bounds i.castSucc)
        (fun i => joins i.castSucc)
      have lastBound := bounds (Fin.last (n + 1))
      have join := joins (Fin.last n)
      rw [show (Fin.last n).succ = Fin.last (n + 1) from rfl] at join
      rw [← join] at lastBound
      -- One application of the advantage triangle adds this step's budget.
      exact (model.advantage_triangle target distinguisher (left 0)
        (right (Fin.last n).castSucc) (right (Fin.last (n + 1)))).trans
        ((add_le_add prefixBound lastBound).trans_eq (Fin.sum_univ_castSucc budget).symm)
  have result := chain uses
    (fun position => attach (implication.transformation position)
      (systems (implication.index position) (implication.direction position)))
    (fun position => attach (implication.transformation position)
      (systems (implication.index position) (!(implication.direction position))))
    (fun position => error position distinguisher)
    (fun position => step position distinguisher admitted) implication.link_eq
  -- The initial and final exact descriptions recover the claimed endpoints.
  rw [implication.start_eq, implication.end_eq]
  exact result

/-- Mix supplied concrete substitutions and statistical steps without
turning a computational premise into a scalar-distance assertion.
Banfi, Section 2.3.1 (printed p. 15): "rather than a substitution".
`selected` explicitly chooses the assumption positions; the remaining
positions contribute their supplied statistical error once each. For every admitted `D` on
`target`:

```text
advantage D targetLeft targetRight ≤ Σⱼ (if selected j then loss j D else statisticalError j)
```

No distance bound is required for a computational step; a statistical step contributes the
same scalar for every `D`. -/
lemma substitutesWithin_of_mixed
    -- `CompatiblePseudoMetric C Phi` selects the resource `distance` used for statistical steps.
    [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    -- `model` selects the admitted distinguishers and their advantage on each interface.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `implication` is the chain from `targetLeft` to `targetRight` on `target`.
    (implication : Implication boundary systems target uses)
    -- `selected j = true` for a computational assumption use, `false` for a statistical step.
    (selected : Fin (uses + 1) → Bool)
    -- `loss j D` is the distinguisher-dependent budget of a selected position `j`.
    (loss : Fin (uses + 1) → Distinguisher target → ENNReal)
    -- `statisticalError j` is the scalar budget of an unselected position `j`.
    (statisticalError : Fin (uses + 1) → ENNReal)
    -- `advantage_le_distance`: every admitted `D` on `target` has advantage at most `distance`,
    -- for all pairs; a strong assumption on the model, not a consequence of the algebra.
    (advantage_le_distance : ∀ distinguisher ∈ model.admissible target,
      ∀ left right, model.advantage target distinguisher left right ≤
        distance left right)
    -- `assumptions j`: for selected `j`, the transformed, oriented pair substitutes within
    -- `loss j`.
    (assumptions : ∀ position, selected position = true →
      model.SubstitutesWithin (loss position)
        (attach (implication.transformation position)
          (systems (implication.index position) (implication.direction position)))
        (attach (implication.transformation position)
          (systems (implication.index position) (!(implication.direction position)))))
    -- `statistical j`: for unselected `j`, the transformed, oriented pair has
    -- `distance ≤ statisticalError j`.
    (statistical : ∀ position, selected position = false →
      distance
        (attach (implication.transformation position)
          (systems (implication.index position) (implication.direction position)))
        (attach (implication.transformation position)
          (systems (implication.index position) (!(implication.direction position)))) ≤
        statisticalError position) :
    model.SubstitutesWithin
      (fun distinguisher => ∑ position,
        if selected position then loss position distinguisher else statisticalError position)
      implication.targetLeft implication.targetRight := by
  apply substitutesWithin model implication
  intro position distinguisher admitted
  -- The supplied selection, not automation, chooses the justification.
  cases selectedEq : selected position with
  | false =>
    -- Only an actual distance bound justifies a statistical contribution.
    simpa only [selectedEq, Bool.false_eq_true, ↓reduceIte] using
      (advantage_le_distance distinguisher admitted _ _).trans
        (statistical position selectedEq)
  | true =>
    -- A named assumption keeps its full distinguisher-dependent loss.
    simpa only [selectedEq, ↓reduceIte] using
      assumptions position selectedEq distinguisher admitted

end ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication

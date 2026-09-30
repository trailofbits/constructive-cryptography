import ConstructiveCryptography.Substitution.Implication
import ConstructiveCryptography.Substitution.Reduction

set_option autoImplicit false

/-!
# Concrete and mixed substitution chains

A chain may mix uses of assumptions, each bounded by a distinguisher-indexed error, with
statistical steps bounded by a distance; a selection of positions marks the assumption uses.
The errors of all steps add up along the chain.

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

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
variable {ι : Type x} {boundary : ι → C}
variable {systems : ∀ i, Bool → Phi (boundary i)}
variable {target : C} {uses : Nat} {Distinguisher : C → Type y}

/-- Count only the positions justified by the selected named assumptions.
Banfi, Section 2.3.1 (printed pp. 14--15): "the number of times each
substitution"; approximate steps used instead of assumptions are excluded. -/
def selectedUsageCount [DecidableEq ι]
    (implication : Implication boundary systems target uses)
    (selected : Fin (uses + 1) → Bool) (assumption : ι) : Nat :=
  (Finset.univ.filter fun position =>
    selected position = true ∧ implication.index position = assumption).card

/-- An explicit finite implication accumulates the concrete losses at its
transformed, oriented steps. Banfi, Section 2.3.3 (printed p. 16), keeps
the loss "ε(Dκρ)" dependent on the actual reduced distinguisher. -/
theorem substitutesWithin
    (model : DistinguisherAdvantage C Phi Distinguisher)
    (implication : Implication boundary systems target uses)
    (error : Fin (uses + 1) → Distinguisher target → ENNReal)
    (step : ∀ position, model.SubstitutesWithin (error position)
      (attach (implication.transformation position)
        (systems (implication.index position) (implication.direction position)))
      (attach (implication.transformation position)
        (systems (implication.index position) (!(implication.direction position))))) :
    model.SubstitutesWithin (fun distinguisher => ∑ position, error position distinguisher)
      implication.targetLeft implication.targetRight := by
  intro distinguisher admitted
  -- The finite triangle calculation uses only the displayed exact joins.
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
positions contribute their supplied statistical error once each. -/
theorem substitutesWithin_of_mixed [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    (model : DistinguisherAdvantage C Phi Distinguisher)
    (implication : Implication boundary systems target uses)
    (selected : Fin (uses + 1) → Bool)
    (loss : Fin (uses + 1) → Distinguisher target → ENNReal)
    (statisticalError : Fin (uses + 1) → ENNReal)
    (advantage_le_distance : ∀ distinguisher ∈ model.admissible target,
      ∀ left right, model.advantage target distinguisher left right ≤
        distance left right)
    (assumptions : ∀ position, selected position = true →
      model.SubstitutesWithin (loss position)
        (attach (implication.transformation position)
          (systems (implication.index position) (implication.direction position)))
        (attach (implication.transformation position)
          (systems (implication.index position) (!(implication.direction position)))))
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

import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card

set_option autoImplicit false

/-!
# Substitutions between resources

A substitution relation relates resources on the same interface; it is symmetric,
transitive and preserved by attaching a converter. An implication witness is a finite chain
of named assumptions, each used in one direction under a converter, whose consecutive
transformed systems are equal. A witness transports valid premises to its target, and
distance bounds on the premises to the sum of the bounds.

## Main definitions

* `SubstitutionRelation C`: substitution relations
* `SubstitutionRelation.Implication`: implication witnesses
* `SubstitutionRelation.Implication.usageCount`: the number of uses of an assumption

## Main results

* `SubstitutionRelation.substitutes_of_hybrid`: the hybrid argument (Banfi, Lemma 2.3.2)
* `SubstitutionRelation.distance_hybrid_le`: the hybrid argument for distances
* `SubstitutionRelation.Implication.substitutes`,
  `SubstitutionRelation.Implication.distance_le`: validity of a witness

Source: Banfi 2023, Definition 2.3.1 and §2.3.1.
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory
open scoped BigOperators

universe u v w x

/-- A source-selected substitution relation in every resource fibre.

Banfi 2023, Definition 2.3.1 (printed p. 13): “Symmetry: `S ≃ T ⇐⇒ T ≃ S`.
Transitivity: `S ≃ T ∧ T ≃ U =⇒ S ≃ U`. Preservation: `S ≃ T =⇒
ρ(S) ≃ ρ(T)`.” Same-fibre typing expresses the definition's compatibility
requirement; `preserved` is its black-box transformation law. -/
structure SubstitutionRelation
    (C : Type u) [Category.{v} C]
    {Phi : C → Type w} [ResourceTheory C Phi] where
  substitutes : ∀ A : C, Phi A → Phi A → Prop
  symmetric : ∀ A : C, Std.Symm (substitutes A)
  transitive : ∀ A : C, IsTrans (Phi A) (substitutes A)
  preserved : ∀ {A B : C} (converter : A ⟶ B)
      {left right : Phi B},
    substitutes B left right →
      substitutes A (attach converter left)
        (attach converter right)

namespace SubstitutionRelation

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- Symmetry in Banfi's iff form. -/
theorem substitutes_symm_iff
    (relation : SubstitutionRelation C)
    {A : C} {left right : Phi A} :
    relation.substitutes A left right ↔
      relation.substitutes A right left :=
  ⟨(relation.symmetric A).symm left right,
    (relation.symmetric A).symm right left⟩

/-- The abstract hybrid argument for a nonempty typed family of substitutions.

Banfi 2023, Lemma 2.3.2 (printed p. 16): if `Sᵢ ≃ Tᵢ` and
`ρᵢ(Tᵢ) ≡ ρᵢ₊₁(Sᵢ₊₁)`, then `ρ₁(S₁) ≃ ρₙ(Tₙ)`. Independence is a property of
the concrete systems used to establish the premises; the abstract chain uses
only preservation, the printed exact-behavior joins, and transitivity. -/
theorem substitutes_of_hybrid
    (relation : SubstitutionRelation C)
    {n : Nat} {target : C} {source : Fin (n + 1) → C}
    (left right : ∀ i, Phi (source i))
    (transformation : ∀ i, target ⟶ source i)
    (step : ∀ i, relation.substitutes (source i) (left i) (right i))
    (link : ∀ i : Fin n,
      attach (transformation i.castSucc) (right i.castSucc) =
        attach (transformation i.succ) (left i.succ)) :
    relation.substitutes target
      (attach (transformation 0) (left 0))
      (attach (transformation (Fin.last n))
        (right (Fin.last n))) := by
  induction n with
  | zero =>
      -- A one-step hybrid is preservation under its named transformation.
      exact relation.preserved (transformation 0) (step 0)
  | succ n inductionHypothesis =>
      -- Apply the hybrid argument to every step except the final one.
      have prefixChain := inductionHypothesis
        (source := fun i => source i.castSucc)
        (left := fun i => left i.castSucc)
        (right := fun i => right i.castSucc)
        (transformation := fun i => transformation i.castSucc)
        (step := fun i => step i.castSucc)
        (link := fun i => by simpa using link i.castSucc)
      -- Preserve the final premise under its named transformation.
      have finalStep := relation.preserved
        (transformation (Fin.last (n + 1))) (step (Fin.last (n + 1)))
      -- The printed exact-behavior equation identifies the two middle systems.
      have finalLink := link (Fin.last n)
      rw [show (Fin.last n).succ = Fin.last (n + 1) by rfl] at finalLink
      rw [← finalLink] at finalStep
      -- Transitivity closes the extended hybrid chain.
      exact (relation.transitive target).trans _ _ _ prefixChain finalStep

/-- The quantitative transformed hybrid bound for the selected fibre
distance.

Banfi 2023, Section 2.3.1 (printed p. 15): “we then collect the sum of such
`p_i`'s into a value `ε`.” Each supplied step is first transformed using
converter non-expansion; the exact-behavior joins contribute no additional
error. -/
theorem distance_hybrid_le [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    {n : Nat} {target : C} {source : Fin (n + 1) → C}
    (left right : ∀ i, Phi (source i))
    (transformation : ∀ i, target ⟶ source i)
    (error : Fin (n + 1) → ENNReal)
    (step : ∀ i, distance (left i) (right i) ≤ error i)
    (link : ∀ i : Fin n,
      attach (transformation i.castSucc) (right i.castSucc) =
        attach (transformation i.succ) (left i.succ)) :
    distance
        (attach (transformation 0) (left 0))
        (attach (transformation (Fin.last n))
          (right (Fin.last n))) ≤
      ∑ i, error i := by
  induction n with
  | zero =>
      -- The only transformed step is bounded by converter non-expansion.
      simpa [Fin.sum_univ_one] using
        (distance_attach_le (transformation 0) (left 0) (right 0)).trans
          (step 0)
  | succ n inductionHypothesis =>
      -- Apply the quantitative hybrid to every step except the final one.
      have prefixBound := inductionHypothesis
        (source := fun i => source i.castSucc)
        (left := fun i => left i.castSucc)
        (right := fun i => right i.castSucc)
        (transformation := fun i => transformation i.castSucc)
        (error := fun i => error i.castSucc)
        (step := fun i => step i.castSucc)
        (link := fun i => by simpa using link i.castSucc)
      -- Transform the final statistical step without increasing its error.
      have finalBound :=
        (distance_attach_le (transformation (Fin.last (n + 1)))
          (left (Fin.last (n + 1))) (right (Fin.last (n + 1)))).trans
          (step (Fin.last (n + 1)))
      -- The exact-behavior join identifies the final intermediate system.
      have finalLink := link (Fin.last n)
      rw [show (Fin.last n).succ = Fin.last (n + 1) by rfl] at finalLink
      rw [← finalLink] at finalBound
      -- The triangle inequality adds precisely the prefix and final errors.
      refine (distance_triangle
        (attach (transformation 0) (left 0))
        (attach (transformation (Fin.last n).castSucc)
          (right (Fin.last n).castSucc))
        (attach (transformation (Fin.last (n + 1)))
          (right (Fin.last (n + 1))))).trans ?_
      rw [Fin.sum_univ_castSucc]
      exact add_le_add prefixBound finalBound

/-- Banfi's explicit witness that a finite collection of security notions
implies a target notion.

Banfi 2023, Section 2.3.1 (printed pp. 14--15) specifies assumption indices
`iⱼ`, direction bits `bⱼ`, transformations `ρⱼ`, the two endpoint equations,
and exact-behavior equations between consecutive transformed systems. `uses +
1` is the source's nonempty number of substitution steps. -/
structure Implication
    {ι : Type x} (boundary : ι → C)
    (systems : ∀ i, Bool → Phi (boundary i))
    (target : C) (uses : Nat) where
  targetLeft : Phi target
  targetRight : Phi target
  index : Fin (uses + 1) → ι
  direction : Fin (uses + 1) → Bool
  transformation : ∀ j, target ⟶ boundary (index j)
  start_eq :
    targetLeft = attach (transformation 0)
      (systems (index 0) (direction 0))
  link_eq : ∀ j : Fin uses,
    attach (transformation j.castSucc)
        (systems (index j.castSucc) (!(direction j.castSucc))) =
      attach (transformation j.succ)
        (systems (index j.succ) (direction j.succ))
  end_eq :
    targetRight = attach (transformation (Fin.last uses))
      (systems (index (Fin.last uses)) (!(direction (Fin.last uses))))

namespace Implication

variable {ι : Type x} {boundary : ι → C}
variable {systems : ∀ i, Bool → Phi (boundary i)}
variable {target : C} {uses : Nat}

/-- The number of times one premise is used in an implication witness.

Banfi 2023, Section 2.3.1 (printed p. 14) defines `tᵢ` as the cardinality of
the substitution positions whose assumption index is `i`. -/
def usageCount [DecidableEq ι]
    (implication : Implication boundary systems target uses)
    (assumption : ι) : Nat :=
  (Finset.univ.filter fun use => implication.index use = assumption).card

/-- An explicit Banfi implication witness transports valid premise
substitutions to the target substitution. -/
theorem substitutes
    (relation : SubstitutionRelation C)
    (implication : Implication boundary systems target uses)
    (premise : ∀ i,
      relation.substitutes (boundary i) (systems i false) (systems i true)) :
    relation.substitutes target implication.targetLeft implication.targetRight := by
  have oriented (use : Fin (uses + 1)) :
      relation.substitutes (boundary (implication.index use))
        (systems (implication.index use) (implication.direction use))
        (systems (implication.index use) (!(implication.direction use))) := by
    cases directionEq : implication.direction use with
    | false =>
        -- A false direction bit uses the premise in its stated orientation.
        simpa only [directionEq, Bool.not_false] using
          premise (implication.index use)
    | true =>
        -- A true direction bit uses symmetry to reverse the premise.
        have reversed :=
          (relation.symmetric (boundary (implication.index use))).symm _ _
            (premise (implication.index use))
        simpa only [directionEq, Bool.not_true] using reversed
  -- The implication's joins are precisely an abstract transformed hybrid.
  have chain := substitutes_of_hybrid relation
    (left := fun use =>
      systems (implication.index use) (implication.direction use))
    (right := fun use =>
      systems (implication.index use) (!(implication.direction use)))
    (transformation := implication.transformation)
    (step := oriented)
    (link := implication.link_eq)
  -- Replace the convenient endpoint descriptions by the target systems.
  rw [implication.start_eq, implication.end_eq]
  exact chain

/-- The quantitative implication bound obtained by replacing every
substitution use with a supplied statistical-distance bound.

This is Banfi 2023, Section 2.3.1's quantitative extension (printed p. 15):
the implication retains the same transformations, direction bits, exact
joins, and endpoints, while its step errors add. -/
theorem distance_le [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    (implication : Implication boundary systems target uses)
    (error : Fin (uses + 1) → ENNReal)
    (step : ∀ use,
      distance (systems (implication.index use) false)
        (systems (implication.index use) true) ≤ error use) :
    distance implication.targetLeft implication.targetRight ≤
      ∑ use, error use := by
  have oriented (use : Fin (uses + 1)) :
      distance
          (systems (implication.index use) (implication.direction use))
          (systems (implication.index use) (!(implication.direction use))) ≤
        error use := by
    cases directionEq : implication.direction use with
    | false =>
        -- A false bit keeps the supplied distance bound's orientation.
        simpa only [directionEq, Bool.not_false] using step use
    | true =>
        -- Fibre distance symmetry reverses a true-bit step at no cost.
        simpa only [directionEq, Bool.not_true, distance,
          CryptographicAlgebra.distance, edist_comm] using step use
  -- Sum the explicitly transformed and oriented statistical steps.
  have chain := distance_hybrid_le
    (left := fun use =>
      systems (implication.index use) (implication.direction use))
    (right := fun use =>
      systems (implication.index use) (!(implication.direction use)))
    (transformation := implication.transformation)
    (error := error)
    (step := oriented)
    (link := implication.link_eq)
  -- Replace the convenient endpoint descriptions by the target systems.
  rw [implication.start_eq, implication.end_eq]
  exact chain

end Implication
end SubstitutionRelation
end ConstructiveCryptography.CryptographicAlgebra

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

Attachment `attach α : Phi B → Phi A` of a converter `α : A ⟶ B` is Banfi's `ρ(S)` for a
transformation `ρ`. The pseudo-distance `distance` may take value `∞`, and distance `0` does
not imply equality.

## Implication chains

An `Implication boundary systems target uses` is Banfi's chain of `uses + 1` steps, indexed
by positions `j : Fin (uses + 1)`. Assumption `i` has the two systems `X_{i,b}` =
`systems i b`. Writing `ρⱼ` for `attach (transformation j)`, `iⱼ` for `index j` and `bⱼ` for
`direction j`:

```text
targetLeft  ═ ρ₀(X_{i₀,b₀})     start_eq
            ≃ ρ₀(X_{i₀,¬b₀})    use of assumption i₀ at position 0
            ═ ρ₁(X_{i₁,b₁})     link_eq 0
            ≃ …                 uses at positions 1, …, n, joined by link_eq 1, …, n-1
            ≃ ρₙ(X_{iₙ,¬bₙ})
targetRight ═ ρₙ(X_{iₙ,¬bₙ})    end_eq
```

Here `n = uses`, so position `n` is `Fin.last uses`, and `¬bⱼ` is `!(direction j)`.
`═` marks an exact equality of resources (a field of the witness); `≃` marks one use of a
premise, transported by preservation, or, in `distance_le`, a step whose distance is at most
its error. The multiplicity of assumption `i` is `usageCount i`, the number of positions `j`
with `index j = i`; it counts uses, not errors, and a position contributes one use whatever
its direction.

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
requirement; `preserved` is its black-box transformation law.

The relation is a selected datum, one relation per fibre. Neither reflexivity nor any link to
equality, a distance or a distinguisher is assumed; concrete choices are made by the caller
(for example `generatedRelation` in `Substitution.Implication`). -/
structure SubstitutionRelation
    -- `C` is the category of interfaces; an arrow `A ⟶ B` is a converter with outside `A`
    -- and inside `B`.
    (C : Type u) [Category.{v} C]
    -- `Phi` assigns to each interface `A : C` its fibre `Phi A` of resources; `ResourceTheory`
    -- supplies `attach : (A ⟶ B) → Phi B → Phi A`.
    {Phi : C → Type w} [ResourceTheory C Phi] where
  /-- `substitutes A S T` is Banfi's `S ≃ T` for two resources `S T : Phi A` on the same
  interface `A`: `T` may replace `S` in that fibre. Resources on different interfaces are
  never compared. -/
  substitutes : ∀ A : C, Phi A → Phi A → Prop
  /-- Symmetry in every fibre: `S ≃ T` implies `T ≃ S`. -/
  symmetric : ∀ A : C, Std.Symm (substitutes A)
  /-- Transitivity in every fibre: `S ≃ T` and `T ≃ U` imply `S ≃ U`. -/
  transitive : ∀ A : C, IsTrans (Phi A) (substitutes A)
  /-- Preservation: attaching any converter `converter : A ⟶ B` (a transformation `ρ` with
  outside `A`, inside `B`) to both sides of `left ≃ right` on `B` gives
  `attach converter left ≃ attach converter right` on `A`. It is required for every converter of
  `C`, not only for a selected efficient class. -/
  preserved : ∀ {A B : C} (converter : A ⟶ B)
      {left right : Phi B},
    substitutes B left right →
      substitutes A (attach converter left)
        (attach converter right)

namespace SubstitutionRelation

-- `C` is the category of interfaces; `A ⟶ B` is a converter with outside `A`, inside `B`.
variable {C : Type u} [Category.{v} C]
-- `Phi A` is the type of resources on interface `A`; `attach α : Phi B → Phi A` for
-- `α : A ⟶ B`.
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- Symmetry in Banfi's iff form: on one interface `A`, `left ≃ right` holds exactly when
`right ≃ left` does. -/
lemma substitutes_symm_iff
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
only preservation, the printed exact-behavior joins, and transitivity.

Steps are indexed from zero by `i : Fin (n + 1)`, so the family is nonempty and the last
position `Fin.last n` is written `n`:

```text
ρ₀(S₀) ≃ ρ₀(T₀) = ρ₁(S₁) ≃ ρ₁(T₁) = … = ρₙ(Sₙ) ≃ ρₙ(Tₙ)
```

Each `≃` is `step i` transported by `preserved`, each `=` is a `link` equality, and the
`≃` steps are joined by `transitive`. -/
theorem substitutes_of_hybrid
    -- `relation.substitutes A S T` is the selected `S ≃ T` in which premises and conclusion
    -- are read.
    (relation : SubstitutionRelation C)
    -- `n` is one less than the number of steps; `i : Fin (n + 1)` selects a step.
    {n : Nat}
    -- `target : C` is the interface of the conclusion; `source i : C` is the interface of step
    -- `i`, possibly different for different steps.
    {target : C} {source : Fin (n + 1) → C}
    -- `left i = Sᵢ` and `right i = Tᵢ` are the two sides of step `i`, both in `Phi (source i)`.
    (left right : ∀ i, Phi (source i))
    -- `transformation i = ρᵢ` (rho), outside `target`, inside `source i`, moves step `i` to
    -- `target`.
    (transformation : ∀ i, target ⟶ source i)
    -- `step i` is the premise `Sᵢ ≃ Tᵢ` in the fibre `Phi (source i)`.
    (step : ∀ i, relation.substitutes (source i) (left i) (right i))
    -- `link i` is the exact join `ρᵢ(Tᵢ) = ρᵢ₊₁(Sᵢ₊₁)` on `target`, for each of the `n`
    -- adjacent pairs; the conclusion is `ρ₀(S₀) ≃ ρₙ(Tₙ)`.
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
error. The chain data are as in `substitutes_of_hybrid`, with each substitution premise
replaced by a distance bound:

```text
d(ρ₀ S₀, ρₙ Tₙ) ≤ Σᵢ d(ρᵢ Sᵢ, ρᵢ Tᵢ)     triangle inequality across the exact links
               ≤ Σᵢ d(Sᵢ, Tᵢ)           attachment is non-expanding (distance_attach_le)
               ≤ Σᵢ error i             step
```

The sum is untruncated `ENNReal` addition, so a single infinite budget makes the bound
trivial. -/
lemma distance_hybrid_le
    -- `CompatiblePseudoMetric C Phi` selects `distance` on each fibre `Phi A`, possibly `∞`;
    -- attachment does not increase it.
    [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    -- `n + 1` steps `i : Fin (n + 1)`; `target` is the conclusion's interface and `source i`
    -- the interface of step `i`.
    {n : Nat} {target : C} {source : Fin (n + 1) → C}
    -- `left i = Sᵢ` and `right i = Tᵢ` are the two sides of step `i`.
    (left right : ∀ i, Phi (source i))
    -- `transformation i = ρᵢ` (rho), outside `target`, inside `source i`.
    (transformation : ∀ i, target ⟶ source i)
    -- `error i` is the budget of step `i`, possibly `∞`.
    (error : Fin (n + 1) → ENNReal)
    -- `step i` bounds the untransformed distance: `distance Sᵢ Tᵢ ≤ error i`.
    (step : ∀ i, distance (left i) (right i) ≤ error i)
    -- `link i` is the exact join `ρᵢ(Tᵢ) = ρᵢ₊₁(Sᵢ₊₁)` on `target`.
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
1` is the source's nonempty number of substitution steps; see the module's chain diagram.

A witness is pure data plus exact equations: it records which premise is invoked where, but
does not by itself assert any premise. Validity is concluded by `Implication.substitutes` or
`Implication.distance_le` from separately supplied premises. -/
structure Implication
    -- ι (iota) is the type of assumption names, possibly infinite; `boundary i : C` is the
    -- interface of assumption `i`.
    {ι : Type x} (boundary : ι → C)
    -- `systems i b` is Banfi's `X_{i,b}` in `Phi (boundary i)`: `b = false` gives `X_{i,0}`,
    -- `b = true` gives `X_{i,1}`.
    (systems : ∀ i, Bool → Phi (boundary i))
    -- `target : C` is the interface of the implied substitution; `uses : Nat` is one less
    -- than the number of steps, so positions are `Fin (uses + 1)`.
    (target : C) (uses : Nat) where
  /-- The left endpoint `Y₀` of the implied substitution on `target`. -/
  targetLeft : Phi target
  /-- The right endpoint of the implied substitution on `target`. -/
  targetRight : Phi target
  /-- `index j = iⱼ`: the name of the assumption used at position `j`. Repetitions are allowed;
  their number is `usageCount`. -/
  index : Fin (uses + 1) → ι
  /-- `direction j = bⱼ`: step `j` runs from `systems (index j) bⱼ` to
  `systems (index j) (!bⱼ)`; `false` uses the premise as stated, `true` reversed. -/
  direction : Fin (uses + 1) → Bool
  /-- `transformation j = ρⱼ`: the converter with outside `target` and inside the interface
  `boundary (index j)` of the assumption used at position `j`. -/
  transformation : ∀ j, target ⟶ boundary (index j)
  /-- The left endpoint is exactly the first step's starting system, `Y₀ = ρ₀(X_{i₀,b₀})`. -/
  start_eq :
    targetLeft = attach (transformation 0)
      (systems (index 0) (direction 0))
  /-- Exact joins: for each adjacent pair `j, j + 1`, the end of step `j` equals the start of
  step `j + 1`, `ρⱼ(X_{iⱼ,¬bⱼ}) = ρⱼ₊₁(X_{iⱼ₊₁,bⱼ₊₁})` as resources on `target`. -/
  link_eq : ∀ j : Fin uses,
    attach (transformation j.castSucc)
        (systems (index j.castSucc) (!(direction j.castSucc))) =
      attach (transformation j.succ)
        (systems (index j.succ) (direction j.succ))
  /-- The right endpoint is exactly the last step's final system, `ρₙ(X_{iₙ,¬bₙ})` with
  `n = uses`. -/
  end_eq :
    targetRight = attach (transformation (Fin.last uses))
      (systems (index (Fin.last uses)) (!(direction (Fin.last uses))))

namespace Implication

-- ι (iota) names the assumptions; `boundary i : C` is the interface of assumption `i`.
variable {ι : Type x} {boundary : ι → C}
-- `systems i b : Phi (boundary i)` is `X_{i,b}`, with `false ↦ X_{i,0}`, `true ↦ X_{i,1}`.
variable {systems : ∀ i, Bool → Phi (boundary i)}
-- `target : C` is the implied substitution's interface; chains have `uses + 1` positions.
variable {target : C} {uses : Nat}

/-- The number of times one premise is used in an implication witness.

Banfi 2023, Section 2.3.1 (printed p. 14) defines `tᵢ` as the cardinality of
the substitution positions whose assumption index is `i`:

```text
usageCount assumption = #{ j : Fin (uses + 1) | index j = assumption }
```

Both orientations of a use count, and an assumption not occurring in the chain has count `0`.
The count records multiplicity only; it carries no error. -/
def usageCount [DecidableEq ι]
    (implication : Implication boundary systems target uses)
    (assumption : ι) : Nat :=
  (Finset.univ.filter fun use => implication.index use = assumption).card

/-- An explicit Banfi implication witness transports valid premise
substitutions to the target substitution. Each position is oriented by its direction bit,
using `symmetric` when the bit is `true`, and the chain is then an instance of
`substitutes_of_hybrid`. -/
lemma substitutes
    -- `relation.substitutes A S T` is the selected `S ≃ T` in which premises and conclusion
    -- are read.
    (relation : SubstitutionRelation C)
    -- `implication` is the chain; the conclusion is `targetLeft ≃ targetRight` on `target`.
    (implication : Implication boundary systems target uses)
    -- `premise i` is `X_{i,0} ≃ X_{i,1}` in `Phi (boundary i)`, for every `i : ι`, also names
    -- the chain never uses.
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
joins, and endpoints, while its step errors add:

```text
distance targetLeft targetRight ≤ Σ_{use : Fin (uses + 1)} error use
```

an untruncated `ENNReal` sum. With a common budget `εᵢ` per assumption name, this sum is
`Σᵢ usageCount i • εᵢ`, but that regrouping is not stated here. The direction bit costs nothing
because `distance` is symmetric. -/
lemma distance_le
    -- `CompatiblePseudoMetric C Phi` selects `distance` on each fibre, possibly `∞`.
    [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    -- `implication` is the chain from `targetLeft` to `targetRight` on `target`.
    (implication : Implication boundary systems target uses)
    -- `error use` is the budget of position `use`, indexed by position rather than by name,
    -- so two uses of one assumption may have different budgets.
    (error : Fin (uses + 1) → ENNReal)
    -- `step use` bounds the untransformed pair of `i = implication.index use`:
    -- `distance X_{i,0} X_{i,1} ≤ error use`.
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

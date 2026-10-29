import ConstructiveCryptography.CryptographicAlgebra.Relaxation
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric

set_option autoImplicit false

/-!
# Distinguisher-indexed reductions

A distinguisher advantage assigns to each admitted distinguisher on an interface a symmetric
advantage satisfying the triangle inequality. Two systems substitute within an error
function when every admitted distinguisher has advantage at most its error. These
substitutions are symmetric, add errors, follow from statistical bounds, and are transported
by attachment along a reduction of distinguishers. The reduction relaxation of a
specification collects the resources within the error of one of its resources.

## Reductions

A reduction for a converter `α : A ⟶ B` (outside `A`, inside `B`) is a map
`reduce : Distinguisher A → Distinguisher B`, Banfi's `D ↦ D ∘ ρ` with `ρ = α`. It goes in the
same direction as `α`, opposite to attachment `Phi B → Phi A`; below, `α S` is `attach α S`:

```text
   Distinguisher A ──reduce──▶ Distinguisher B
   Phi A ◀──attach α──── Phi B
   advantage A D (α S) (α T) = advantage B (reduce D) S T     (advantage_eq)
   error at D on A           = error (reduce D) on B
```

Admissibility of `reduce D` and the advantage equation are explicit hypotheses; nothing
asserts that composing with an arbitrary converter keeps a distinguisher efficient.

## Main definitions

* `DistinguisherAdvantage C Systems Distinguisher`: admitted distinguishers and their
  advantage
* `DistinguisherAdvantage.SubstitutesWithin`: substitution within an error function
* `Specification.reductionRelaxation`: the reduction relaxation

## Main results

* `SubstitutesWithin.symm`, `SubstitutesWithin.trans`, `SubstitutesWithin.of_statistical`,
  `SubstitutesWithin.of_distance`, `SubstitutesWithin.attach`,
  `SubstitutesWithin.attach_serial`
* `Specification.constructs_singleton_reductionRelaxation_iff`,
  `Specification.map_reductionRelaxation_subset`

Source: Banfi 2023, §2.3.3; Jost, Definitions 2.2.8–2.2.9 and Theorem 2.2.10.
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory

universe u v w x

/-- A typed family of admissible distinguishers and its advantage function.

Banfi 2023, Section 2.3.3 (printed p. 16) defines concrete substitution by
requiring `Δ_D(S, T) ≤ ε(D)` “for all poly-time (distinguishing) programs.”
The three advantage laws below are exactly the symmetry and triangle facts
used by the substitution and reduction-relaxation calculations. The laws hold for every
distinguisher, admitted or not. -/
structure DistinguisherAdvantage
    -- `C` is the type of interfaces; no category structure is needed here.
    (C : Type u)
    -- `Systems A` is the type of resources compared on `A : C`; `Distinguisher A` contains all
    -- candidate distinguishers on `A`, admitted or not.
    (Systems : C → Type w) (Distinguisher : C → Type x) where
  /-- The distinguishers admitted at each resource interface, Banfi's “poly-time” programs: the
  class over which `SubstitutesWithin` quantifies. It is an arbitrary subset, possibly empty;
  efficiency is only the caller's choice of this set, and no closure property is assumed. -/
  admissible : ∀ A, Set (Distinguisher A)
  /-- The distinguishing advantage `Δ_D(S, T)` of `D : Distinguisher A` between two resources
  `S T : Systems A` in one fibre, possibly `∞`. It is an abstract pseudo-distance per
  distinguisher, not assumed bounded by `1` or derived from a concrete experiment; advantage
  `0` for every admitted `D` does not make `S` and `T` equal. -/
  advantage : ∀ A, Distinguisher A → Systems A → Systems A → ENNReal
  /-- A distinguisher has zero advantage between identical resources. -/
  advantage_self : ∀ A distinguisher resource,
    advantage A distinguisher resource resource = 0
  /-- Distinguishing advantage is symmetric in the compared resources. -/
  advantage_symm : ∀ A distinguisher left right,
    advantage A distinguisher left right = advantage A distinguisher right left
  /-- Distinguishing advantage satisfies the triangle inequality. -/
  advantage_triangle : ∀ A distinguisher left middle right,
    advantage A distinguisher left right ≤
      advantage A distinguisher left middle + advantage A distinguisher middle right

namespace DistinguisherAdvantage

-- `C` is the type of interfaces; `Systems A` contains the resources and `Distinguisher A` the
-- candidate distinguishers on `A : C`.
variable {C : Type u} {Systems : C → Type w} {Distinguisher : C → Type x}

/-- Concrete substitution within one explicit distinguisher-indexed error
function.

Banfi 2023, Section 2.3.3 (printed p. 16) uses the condition
`Δ_D(S, T) ≤ ε(D)` for every admitted distinguisher `D`.

```text
model.SubstitutesWithin error left right  :⇔
  ∀ D ∈ model.admissible A, model.advantage A D left right ≤ error D
```

Inadmissible distinguishers are unconstrained, and with no admitted distinguisher the
statement holds vacuously. Error `0` is not equality of `left` and `right`. -/
def SubstitutesWithin
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Systems Distinguisher)
    -- `error D` is Banfi's `ε(D)`, a budget for each distinguisher `D` on `A`, possibly `∞`.
    {A : C} (error : Distinguisher A → ENNReal)
    -- `left`, `right : Systems A` are the two compared resources.
    (left right : Systems A) : Prop :=
  ∀ distinguisher, distinguisher ∈ model.admissible A →
    model.advantage A distinguisher left right ≤ error distinguisher

/-- Reversing a concrete substitution preserves its error function: a bound
`Δ_D(left, right) ≤ error D` for every admitted `D` gives `Δ_D(right, left) ≤ error D`. -/
lemma SubstitutesWithin.symm
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} {error : Distinguisher A → ENNReal}
    {left right : Systems A}
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin error right left := by
  intro distinguisher admitted
  -- Symmetry rewrites the reversed advantage to the supplied one.
  rw [← model.advantage_symm A distinguisher left right]
  exact substitution distinguisher admitted

/-- Consecutive concrete substitutions add their pointwise errors.

Jost 2020, Theorem 2.2.10 (printed p. 22): “the errors just adding up.”
The same distinguisher is used at both steps, so the budgets add pointwise in `D`. -/
theorem SubstitutesWithin.trans
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Systems Distinguisher)
    -- `firstError` and `secondError` are the per-distinguisher budgets of the two steps on `A`.
    {A : C} {firstError secondError : Distinguisher A → ENNReal}
    -- `left`, `middle`, `right : Systems A` are the three resources of the chain.
    {left middle right : Systems A}
    -- `first`: `left` to `middle` within `firstError`; `second`: `middle` to `right` within
    -- `secondError`. The conclusion's budget is their pointwise sum.
    (first : model.SubstitutesWithin firstError left middle)
    (second : model.SubstitutesWithin secondError middle right) :
    model.SubstitutesWithin (fun distinguisher =>
      firstError distinguisher + secondError distinguisher) left right := by
  intro distinguisher admitted
  -- Apply the advantage triangle inequality at the named middle resource.
  exact (model.advantage_triangle A distinguisher left middle right).trans
      (add_le_add (first distinguisher admitted) (second distinguisher admitted))

/-- A uniform statistical observation bound gives a constant concrete loss.
Banfi, §2.3.1 (p. 15): “rather than a substitution”. The observation may be a
transcript distribution; a resource metric or category is not required.
The conclusion is substitution within the constant error function `fun _ => error`. -/
lemma SubstitutesWithin.of_statistical
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Systems Distinguisher)
    -- `statistical D R S` is any comparison of `R`, `S : Systems A` that may depend on `D`,
    -- for example a distance of the transcript laws `D` observes.
    {A : C} {statistical : Distinguisher A → Systems A → Systems A → ENNReal}
    -- `domination` says `model.advantage A D R S ≤ statistical D R S` for admitted `D` and
    -- all `R`, `S`.
    (domination : ∀ D ∈ model.admissible A, ∀ R S,
      model.advantage A D R S ≤ statistical D R S)
    -- `left`, `right` are the compared pair and `error : ENNReal` one scalar budget.
    {left right : Systems A} {error : ENNReal}
    -- `bound` says `statistical D left right ≤ error` for every admitted `D`.
    (bound : ∀ D ∈ model.admissible A, statistical D left right ≤ error) :
    model.SubstitutesWithin (fun _ => error) left right := by
  intro D admitted
  exact (domination D admitted left right).trans (bound D admitted)

-- `C` now has converters `A ⟶ B` (outside `A`, inside `B`); `Phi A` is the type of resources
-- on `A`, with `attach α : Phi B → Phi A` for `α : A ⟶ B`.
variable [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]

/-- A statistical step supplies a constant concrete loss `fun _ => error`, provided the
selected advantage is dominated by distance. Banfi, Section 2.3.1 (printed p. 15),
allows an approximate step "rather than a substitution". The domination
hypothesis is explicit; no computational premise is promoted to a metric bound. -/
lemma SubstitutesWithin.of_distance
    -- `CompatiblePseudoMetric C Phi` selects the resource `distance` on each fibre.
    [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `left`, `right : Phi A` are the compared pair and `error : ENNReal` one scalar budget.
    {A : C} {left right : Phi A} {error : ENNReal}
    -- `domination` says every admitted distinguisher's advantage on `A` is at most `distance`,
    -- for all pairs `first`, `second`.
    (domination : ∀ distinguisher ∈ model.admissible A,
      ∀ first second, model.advantage A distinguisher first second ≤
        distance first second)
    -- `bound` is `distance left right ≤ error`.
    (bound : distance left right ≤ error) :
    model.SubstitutesWithin (fun _ => error) left right := by
  intro distinguisher admitted
  -- Statistical distance controls this admitted distinguisher's advantage.
  exact (domination distinguisher admitted left right).trans bound

/-- An explicit black-box reduction transports a concrete substitution through
converter attachment and precomposes its error function.

Banfi 2023, Section 2.3.3 (printed p. 16) defines the transformed loss by
`ε'(D) := ε(D ∘ ρ)`. The `reduce` argument is that composed distinguisher;
its admissibility and the displayed advantage equality remain explicit. The loss is
evaluated at the actual reduced distinguisher, not at a worst case over `B`. -/
lemma SubstitutesWithin.attach
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `converter = ρ` (rho) is the transformation, outside `A`, inside `B`.
    {A B : C} (converter : A ⟶ B)
    -- `reduce : Distinguisher A → Distinguisher B` is Banfi's `D ↦ D ∘ ρ`; its intended
    -- reading (`D` with `converter` absorbed) is not assumed, only the two hypotheses below.
    (reduce : Distinguisher A → Distinguisher B)
    -- `reduce_admissible` says admitted `D` on `A` gives admitted `reduce D` on `B`.
    (reduce_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduce distinguisher ∈ model.admissible B)
    -- `advantage_eq`: `Δ_D(ρ left, ρ right) = Δ_{reduce D}(left, right)` for every `D`,
    -- admitted or not, and all `left`, `right : Phi B`.
    (advantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (attach converter left)
          (attach converter right) =
        model.advantage B (reduce distinguisher) left right)
    -- `error D'` is the budget on `B`; `left`, `right : Phi B` are the inner pair.
    {error : Distinguisher B → ENNReal}
    {left right : Phi B}
    -- `substitution`: `left`, `right` substitute within `error`; the attached pair is then
    -- within `D ↦ error (reduce D)`.
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin (fun distinguisher => error (reduce distinguisher))
      (attach converter left)
      (attach converter right) := by
  intro distinguisher admitted
  -- Replace the transformed advantage by that of the supplied reduction.
  rw [advantage_eq]
  -- Efficiency closure admits the reduced distinguisher at the source fibre.
  exact substitution (reduce distinguisher)
    (reduce_admissible distinguisher admitted)

/-- Serial black-box reductions compose by nesting their distinguisher maps.

This is the iterated form of Banfi 2023, Section 2.3.3 (printed p. 16):
the final loss is `error (reduceInner (reduceOuter D))`, matching successive
precomposition by the two named transformations.

Converters `outer : A ⟶ B` and `inner : B ⟶ D` compose to `outer ≫ inner : A ⟶ D`, and
attachment applies `inner` first. The reductions run the other way along the same chain:

```text
interfaces      A ──outer──▶ B ──inner──▶ D
distinguishers  Dist A ──reduceOuter──▶ Dist B ──reduceInner──▶ Dist D
resources       Phi A ◀──attach outer── Phi B ◀──attach inner── Phi D
```

Here `D` is the innermost interface, not a distinguisher. -/
lemma SubstitutesWithin.attach_serial
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `A`, `B`, `D` are interfaces (`D` is not a distinguisher); `outer : A ⟶ B` and
    -- `inner : B ⟶ D` compose to `outer ≫ inner : A ⟶ D`, and attachment applies `inner` first.
    {A B D : C} (outer : A ⟶ B) (inner : B ⟶ D)
    -- `reduceOuter` reduces distinguishers on `A` to `B` for `outer`; `reduceInner` reduces
    -- distinguishers on `B` to `D` for `inner`.
    (reduceOuter : Distinguisher A → Distinguisher B)
    (reduceInner : Distinguisher B → Distinguisher D)
    -- `reduceOuter_admissible`, `reduceInner_admissible`: each reduction sends admitted
    -- distinguishers to admitted ones.
    (reduceOuter_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduceOuter distinguisher ∈ model.admissible B)
    (reduceInner_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible B →
        reduceInner distinguisher ∈ model.admissible D)
    -- `outerAdvantage_eq`: `Δ_D'(outer left, outer right) = Δ_{reduceOuter D'}(left, right)`.
    (outerAdvantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (ConstructiveCryptography.CryptographicAlgebra.attach
            outer left)
          (ConstructiveCryptography.CryptographicAlgebra.attach
            outer right) =
        model.advantage B (reduceOuter distinguisher) left right)
    -- `innerAdvantage_eq`: `Δ_D'(inner left, inner right) = Δ_{reduceInner D'}(left, right)`.
    (innerAdvantage_eq : ∀ distinguisher left right,
      model.advantage B distinguisher
          (ConstructiveCryptography.CryptographicAlgebra.attach
            inner left)
          (ConstructiveCryptography.CryptographicAlgebra.attach
            inner right) =
        model.advantage D (reduceInner distinguisher) left right)
    -- `error` is the budget on the innermost interface `D`; `left`, `right : Phi D`.
    {error : Distinguisher D → ENNReal}
    {left right : Phi D}
    -- `substitution`: `left`, `right` substitute within `error`; the attached pair on `A` is
    -- then within `D' ↦ error (reduceInner (reduceOuter D'))`.
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin
      (fun distinguisher => error (reduceInner (reduceOuter distinguisher)))
      (ConstructiveCryptography.CryptographicAlgebra.attach
        (outer ≫ inner) left)
      (ConstructiveCryptography.CryptographicAlgebra.attach
        (outer ≫ inner) right) := by
  -- First reduce through the inner transformation.
  have innerSubstitution := SubstitutesWithin.attach model inner reduceInner
    reduceInner_admissible innerAdvantage_eq substitution
  -- Then reduce the resulting statement through the outer transformation.
  have outerSubstitution := SubstitutesWithin.attach model outer reduceOuter
    reduceOuter_admissible outerAdvantage_eq innerSubstitution
  -- Serial attachment applies the inner converter first.
  simpa only [ConstructiveCryptography.CryptographicAlgebra.attach_serial]
    using outerSubstitution

end DistinguisherAdvantage

namespace Specification

-- `C` is the type of interfaces; `Phi A` contains the resources and `Distinguisher A` the
-- candidate distinguishers on `A : C`.
variable {C : Type u} {Phi : C → Type w} {Distinguisher : C → Type x}

/-- Jost's pointwise reduction relaxation for one explicit advantage model and
distinguisher-indexed error function.

Jost 2020, Definition 2.2.9 (printed p. 22):
“`R^ε := {S | ∀D : |Δ^D(R,S)| ≤ ε(D)}`.”

For a center `R : Phi A`, the pointwise relaxation is
`{S | model.SubstitutesWithin error R S}`, the center written first as in Jost; a
specification is relaxed to the union of these sets over its members (see
`mem_reductionRelaxation_iff`). Jost's “`∀D`” ranges over `model.admissible A` here, and
his `|Δ^D(R,S)|` is the nonnegative `model.advantage A D R S`.
Extensivity, `R ∈ R^ε`, holds because `advantage_self` gives advantage `0`. -/
noncomputable def reductionRelaxation
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `error D` is Jost's `ε(D)`, a budget for each distinguisher `D` on `A`.
    {A : C} (error : Distinguisher A → ENNReal) :
    ConstructiveCryptography.Relaxation (Phi A) :=
  ConstructiveCryptography.Relaxation.ofPointwise
    (fun center => {resource | model.SubstitutesWithin error center resource})
    (fun resource distinguisher _ => by
      -- Reflexive advantage is zero and every error is nonnegative.
      rw [model.advantage_self]
      exact bot_le)

/-- Membership in a relaxed specification: `resource` lies in the reduction relaxation of
`source` exactly when some `center ∈ source` has `resource` within `error` of it. -/
@[simp]
lemma mem_reductionRelaxation_iff
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A : C} {error : Distinguisher A → ENNReal}
    {source : Specification (Phi A)} {resource : Phi A} :
    resource ∈ reductionRelaxation model error source ↔
      ∃ center ∈ source, model.SubstitutesWithin error center resource :=
  ConstructiveCryptography.Relaxation.mem_ofPointwise_iff

/-- Successive reduction relaxations add their errors pointwise.

Jost 2020, Theorem 2.2.10 (printed p. 22):
`(R^{ε₁})^{ε₂} ⊆ R^{ε₁+ε₂}`.
The sum is pointwise, untruncated `ENNReal` addition. The inclusion may be strict. -/
theorem reductionRelaxation_reductionRelaxation_subset
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `firstError = ε₁` (epsilon) and `secondError = ε₂` are the budgets of the first and
    -- second relaxation.
    {A : C} (firstError secondError : Distinguisher A → ENNReal)
    -- `source = R` is any specification on `A`.
    (source : Specification (Phi A)) :
    reductionRelaxation model secondError
        (reductionRelaxation model firstError source) ⊆
      reductionRelaxation model
        (fun distinguisher => firstError distinguisher + secondError distinguisher)
        source := by
  intro resource relaxed
  rw [mem_reductionRelaxation_iff] at relaxed ⊢
  obtain ⟨middle, middleRelaxed, second⟩ := relaxed
  rw [mem_reductionRelaxation_iff] at middleRelaxed
  obtain ⟨center, admitted, first⟩ := middleRelaxed
  -- Transitivity uses the same distinguisher at both consecutive steps.
  exact ⟨center, admitted,
    DistinguisherAdvantage.SubstitutesWithin.trans model first second⟩

-- `C` now has converters `A ⟶ B` (outside `A`, inside `B`), with `attach : Phi B → Phi A`.
variable [Category.{v} C] [ResourceTheory C Phi]

/-- A concrete real/ideal reduction bound is the existing singleton
construction into Jost's reduction relaxation.

Jost, Definition 2.2.9 (printed p. 22): "R^ε := {S | ∀D : |Δᴰ(R,S)| ≤ ε(D)}".
MR16, Definition 1 (printed p. 11): "π R ⊆ S". The supplied ideal may
already have its explicitly chosen simulator attached.

The construction `{real} —protocol→ {ideal}^error` holds exactly when
`Δ_D(attach protocol real, ideal) ≤ error D` for every admitted `D` on `A`. The relaxation
compares center first; symmetry of the advantage reconciles the two orders. -/
lemma constructs_singleton_reductionRelaxation_iff
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `protocol : A ⟶ B` (outside `A`, inside `B`) is attached to `real : Phi B`;
    -- `ideal : Phi A` is the single center of the target specification.
    {A B : C} {protocol : A ⟶ B} {real : Phi B} {ideal : Phi A}
    -- `error D` is the budget for each distinguisher `D` on `A`.
    {error : Distinguisher A → ENNReal} :
    Constructs protocol {real} (reductionRelaxation model error {ideal}) ↔
      model.SubstitutesWithin error (attach protocol real) ideal := by
  constructor
  · intro construction
    -- The singleton target supplies its unique center, namely the ideal.
    obtain ⟨center, centerEq, bound⟩ := (mem_reductionRelaxation_iff model).mp
      (constructs_iff.mp construction real (Set.mem_singleton _))
    obtain rfl := Set.mem_singleton_iff.mp centerEq
    exact DistinguisherAdvantage.SubstitutesWithin.symm model bound
  · intro bound
    apply constructs_iff.mpr
    intro resource admitted
    obtain rfl := Set.mem_singleton_iff.mp admitted
    -- Symmetry reconciles the real-first comparison with Jost's center-first set.
    exact (mem_reductionRelaxation_iff model).mpr
      ⟨ideal, Set.mem_singleton _, DistinguisherAdvantage.SubstitutesWithin.symm model bound⟩

/-- Converter attachment pulls a reduction relaxation through its image and
precomposes the error function with the explicit reduction.

Jost 2020, Theorem 2.2.11 (printed p. 22) states
`π(R^ε) ⊆ (πR)^{ε_π}` with `ε_π(D) := ε(Dπ(·))`.

Here `map converter` is the direct image on `A` under attachment, and `ε_π` is
`D ↦ error (reduce D)`. -/
theorem map_reductionRelaxation_subset
    -- `model` selects admitted distinguishers and their per-distinguisher advantage.
    (model : DistinguisherAdvantage C Phi Distinguisher)
    -- `converter = π` (pi), outside `A`, inside `B`.
    {A B : C} (converter : A ⟶ B)
    -- `reduce` is Jost's `D ↦ Dπ(·)`, from distinguishers on `A` to distinguishers on `B`.
    (reduce : Distinguisher A → Distinguisher B)
    -- `reduce_admissible` and `advantage_eq` are as in
    -- `DistinguisherAdvantage.SubstitutesWithin.attach`.
    (reduce_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduce distinguisher ∈ model.admissible B)
    (advantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (attach converter left)
          (attach converter right) =
        model.advantage B (reduce distinguisher) left right)
    -- `error = ε` is the budget on the inside interface `B`; `source = R` is a specification
    -- on `B`.
    (error : Distinguisher B → ENNReal) (source : Specification (Phi B)) :
    map converter (reductionRelaxation model error source) ⊆
      reductionRelaxation model (fun distinguisher => error (reduce distinguisher))
        (map converter source) := by
  rintro resource ⟨original, originalRelaxed, rfl⟩
  rw [mem_reductionRelaxation_iff] at originalRelaxed ⊢
  obtain ⟨center, admitted, close⟩ := originalRelaxed
  -- Attach the converter to the selected unrelaxed center.
  refine ⟨attach converter center, ⟨center, admitted, rfl⟩, ?_⟩
  -- Banfi's composed distinguisher supplies the transformed bound.
  exact DistinguisherAdvantage.SubstitutesWithin.attach model
    converter reduce reduce_admissible advantage_eq close

end Specification
end ConstructiveCryptography.CryptographicAlgebra

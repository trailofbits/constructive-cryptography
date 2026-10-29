import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.Specification.Metric
import Mathlib.Topology.EMetricSpace.Lipschitz

set_option autoImplicit false

/-!
# Compatible pseudo-metrics

A pseudo-metric on the resources of each interface is compatible with the cryptographic
algebra when attachment is non-expanding and parallel composition adds distances (Maurer
2011, Definition 2; MR16, Definition 2, printed p. 11). A converter then constructs `T`
from `S` within `ε` when every attached resource of `S` is within `ε` of `T`; approximate
constructions compose serially and in parallel with additive errors.

Notation is as in `ConstructiveCryptography.CryptographicAlgebra.Basic`: `α : A ⟶ B` is a
converter with outside `A` and inside `B`, and `attach α : Phi B → Phi A`. Each resource type
`Phi A` carries its own selected extended pseudo-metric `fibreMetric A`, written
`distance R S : ENNReal`. Distances may be `∞`, and `distance R S = 0` does not imply
`R = S`. Error budgets `ε : ENNReal` are scalars added without truncation (`a + ∞ = ∞`);
they are not bounded test outputs. The metric is an abstract field: nothing here says it
comes from distinguishers or random systems (`CompatibleDistinguisherClass` adds that).

## Main definitions

* `CompatiblePseudoMetric C Φ`: a cryptographic algebra with a compatible pseudo-metric
* `CryptographicAlgebra.distance`: the distance of two resources on one interface
* `CryptographicAlgebra.Specification.ConstructsWithin`: approximate construction

## Main results

* `CryptographicAlgebra.distance_attach_le`, `CryptographicAlgebra.distance_parallel_le`:
  the compatibility conditions
* `CryptographicAlgebra.distance_eq_of_mutual_attach`: opposite attachments preserving a
  chosen pair preserve its distance; `distance_attach_iso` is the isomorphism case
* `CryptographicAlgebra.Specification.ConstructsWithin.serial`,
  `CryptographicAlgebra.Specification.ConstructsWithin.parallel`: composition with additive
  errors
-/

namespace ConstructiveCryptography

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

open CryptographicAlgebra in
/-- **A compatible pseudo-metric** (Maurer 2011, Definition 2): a pseudo-metric on the
resources of each interface such that attachment is non-expanding, `d(αR, αS) ≤ d(R, S)`
(condition 4), and parallel composition adds distances, `d(R ∥ R′, S ∥ S′) ≤ d(R, S) +
d(R′, S′)` (condition 3).

Both laws quantify over all converters and resources, not over a selected efficient class.
MR16, Definition 2 (printed p. 11) states only non-expansion, for converters at either
interface side (`d(αR, αS)` and `d(Rβ, Sβ)`); here both are attachments of typed converters.
The parallel law is Maurer 2011's condition 3 and is an additional assumption relative to
MR16's definition. -/
class CompatiblePseudoMetric
    -- Objects `A : C` are interfaces, morphisms `A ⟶ B` converters, and `A ⊗ B` places two
    -- interfaces side by side.
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    -- `Phi A` is the type of resources on `A`, with attachment; the inherited `laxMonoidal`
    -- supplies the `parallel` composition used in `edist_parallel_le`.
    (Phi : C → Type w) [ResourceTheory C Phi] extends CryptographicAlgebra C Phi where
  /-- The selected extended pseudo-metric on the resources of interface `A`; values lie in
  `ENNReal`, may be `∞`, and zero distance need not mean equality. Different interfaces
  carry unrelated metrics, linked only by the two laws below. -/
  fibreMetric : ∀ A : C, PseudoEMetricSpace (Phi A)
  /-- Non-expansion, `d_A(αR, αS) ≤ d_B(R, S)`: attaching `converter : A ⟶ B` to
  `left, right : Phi B` gives resources on `A` no farther apart in `fibreMetric A` than
  `left, right` are in `fibreMetric B`. -/
  edist_smul_le : ∀ {A B : C} (converter : A ⟶ B) (left right : Phi B),
    @edist _ (fibreMetric A).toEDist (attach converter left)
        (attach converter right) ≤
      @edist _ (fibreMetric B).toEDist left right
  /-- Subadditivity under parallel: the distance on `A ⊗ B` between `left ∥ right` and
  `left' ∥ right'` is at most the sum of the component distances on `A` and on `B`. -/
  edist_parallel_le : ∀ {A B : C} (left left' : Phi A)
      (right right' : Phi B),
    @edist _ (fibreMetric (A ⊗ B)).toEDist (resourceParallel laxMonoidal left right)
        (resourceParallel laxMonoidal left' right') ≤
      @edist _ (fibreMetric A).toEDist left left' + @edist _ (fibreMetric B).toEDist right right'

namespace CryptographicAlgebra

-- Objects `A : C` are interfaces; `α : A ⟶ B` is a converter with outside `A` and inside `B`;
-- `A ⊗ B` places two interfaces side by side.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
-- `Phi A` is the type of resources on `A`; attaching `α : A ⟶ B` maps `Phi B` to `Phi A`.
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- The distance of two resources on one interface: `distance R S = edist R S` in the
selected `fibreMetric A`, an element of `ENNReal` (possibly `∞`). -/
noncomputable def distance [CompatiblePseudoMetric C Phi] {A : C}
    (left right : Phi A) : ENNReal :=
  @edist _ (CompatiblePseudoMetric.fibreMetric A).toEDist left right

/-- Every resource is at distance zero from itself. -/
@[simp]
lemma distance_self [CompatiblePseudoMetric C Phi] {A : C}
    (resource : Phi A) :
    distance resource resource = 0 := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_self resource

/-- Symmetry of the selected resource distance. -/
lemma distance_comm [CompatiblePseudoMetric C Phi] {A : C}
    (left right : Phi A) :
    distance left right = distance right left := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_comm left right

/-- The triangle inequality in the selected fibre distance on `Phi A`, in `ENNReal`. -/
lemma distance_triangle [CompatiblePseudoMetric C Phi] {A : C}
    (left middle right : Phi A) :
    distance left right ≤
      distance left middle +
        distance middle right := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_triangle left middle right

/-- Converter attachment is non-expanding in the selected fibre distances: for
`converter : A ⟶ B` and `left, right : Phi B`,
`distance (converter • left) (converter • right) ≤ distance left right`, the left side in
`Phi A` and the right in `Phi B`. -/
lemma distance_attach_le [CompatiblePseudoMetric C Phi] {A B : C}
    (converter : A ⟶ B) (left right : Phi B) :
    distance (attach converter left)
        (attach converter right) ≤
      distance left right :=
  CompatiblePseudoMetric.edist_smul_le converter left right

/-- If two converters agree on an ideal resource, replacing that resource
on each side bounds the distance between their real outputs:

```text
d(left • real, right • real) ≤ d(left • real, left • ideal) + d(right • ideal, right • real)
                             ≤ d(real, ideal) + d(real, ideal)
```

The bound is the doubled `ENNReal` sum, untruncated.

Maurer--Renner 2016, Definition 2 (printed p. 11): “d(αR, αS) ≤ d(R, S)”.
The triangle inequality applies this law twice, using the supplied equality of the two
ideal attachments. -/
theorem distance_attach_le_add_of_eq [CompatiblePseudoMetric C Phi] {A B : C}
    -- `left right : A ⟶ B` are two converters; `real ideal : Phi B` two resources inside.
    (left right : A ⟶ B) (real ideal : Phi B)
    -- `equal`: the converters agree on `ideal`, `left • ideal = right • ideal`.
    (equal : attach left ideal = attach right ideal) :
    distance (attach left real)
        (attach right real) ≤
      distance real ideal + distance real ideal := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) B
  exact ConstructiveCryptography.Specification.edist_apply_le_add_of_eq
    (attach left) (attach right)
    (LipschitzWith.of_edist_le (distance_attach_le left))
    (LipschitzWith.of_edist_le (distance_attach_le right)) real ideal equal

/-- Opposite attachments that exchange two resource pairs preserve their distance. Attachment
is contravariant, so `forward : A ⟶ B` maps `Φ B → Φ A` and `backward : B ⟶ A` maps back:

```text
                 attach forward
  R, S : Φ B   ──────────────────▶   R', S' : Φ A
               ◀──────────────────
                 attach backward
```

Maurer--Renner 2016, Definition 2
(printed p. 11): “A metric d on Φ is called non-expanding if d(αR, αS) ≤ d(R, S) for all α”.
With the four pair equalities, one application in each direction gives
`d(R', S') = d(forward R, forward S) ≤ d(R, S) = d(backward R', backward S') ≤ d(R', S')`.
Nothing else is assumed: the converters need not be inverse, nor the metric separated. -/
lemma distance_eq_of_mutual_attach [CompatiblePseudoMetric C Phi] {A B : C}
    -- `attach forward` maps `Phi B → Phi A`; `attach backward` maps `Phi A → Phi B`.
    (forward : A ⟶ B) (backward : B ⟶ A)
    -- `left right : Phi B` are the diagram's `R, S`; `left' right' : Phi A` are `R', S'`.
    (left right : Phi B) (left' right' : Phi A)
    -- `hforwardLeft`, `hforwardRight`: attaching `forward` sends `left, right` to
    -- `left', right'`.
    (hforwardLeft : attach forward left = left')
    (hforwardRight : attach forward right = right')
    -- `hbackwardLeft`, `hbackwardRight`: attaching `backward` sends `left', right'` back.
    (hbackwardLeft : attach backward left' = left)
    (hbackwardRight : attach backward right' = right) :
    distance left' right' = distance left right := by
  apply le_antisymm
  · -- d(R', S') = d(forward R, forward S) ≤ d(R, S), by non-expansion of `forward`.
    rw [← hforwardLeft, ← hforwardRight]
    exact distance_attach_le forward left right
  · -- d(R, S) = d(backward R', backward S') ≤ d(R', S'), by non-expansion of `backward`.
    rw [← hbackwardLeft, ← hbackwardRight]
    exact distance_attach_le backward left' right'

/-- Attachment along an interface isomorphism preserves the selected fibre distance exactly.
This is `distance_eq_of_mutual_attach` with `forward = relabel.hom` and
`backward = relabel.inv`: the forward equations hold by definition, and
`relabel.inv ≫ relabel.hom = 𝟙 B` supplies the backward ones. -/
lemma distance_attach_iso [CompatiblePseudoMetric C Phi] {A B : C}
    (relabel : A ≅ B) (left right : Phi B) :
    distance (attach relabel.hom left)
        (attach relabel.hom right) =
      distance left right := by
  -- The pair lemma with `R' = attach hom R`, `S' = attach hom S`; forward equations are `rfl`.
  apply distance_eq_of_mutual_attach relabel.hom relabel.inv left right
    (attach relabel.hom left) (attach relabel.hom right) rfl rfl
  -- Backward on `R`: attaching `hom`, then `inv`, is attaching `inv ≫ hom = 𝟙 B`.
  · rw [← attach_serial, relabel.inv_hom_id, attach_identity]
  -- Backward on `S`: the same identity.
  · rw [← attach_serial, relabel.inv_hom_id, attach_identity]

/-- Ordered resource parallel is jointly non-expanding: for `left, left' : Phi A` and
`right, right' : Phi B`, the distance on `A ⊗ B` of the two parallel compositions is at most
`distance left left' + distance right right'`. This is the field `edist_parallel_le`. -/
lemma distance_parallel_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left left' : Phi A) (right right' : Phi B) :
    distance (parallel left right)
        (parallel left' right') ≤
      distance left left' +
        distance right right' :=
  CompatiblePseudoMetric.edist_parallel_le left left' right right'

/-- Ordered parallel with an unchanged right component is non-expanding in
the left component. -/
lemma distance_parallel_left_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left left' : Phi A) (right : Phi B) :
    distance (parallel left right)
        (parallel left' right) ≤
      distance left left' := by
  -- Apply joint non-expansion with identical right components.
  exact (distance_parallel_le left left' right right).trans_eq
    (by rw [distance_self, add_zero])

/-- Ordered parallel with an unchanged left component is non-expanding in
the right component. -/
lemma distance_parallel_right_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left : Phi A) (right right' : Phi B) :
    distance (parallel left right)
        (parallel left right') ≤
      distance right right' := by
  -- Apply joint non-expansion with identical left components.
  exact (distance_parallel_le left left right right').trans_eq
    (by rw [distance_self, zero_add])

namespace Specification

/-- Approximate construction: every attached source resource is within `error` of an
admitted target resource:

```text
ConstructsWithin converter source target error
  ⟺  ∀ R ∈ source, ∃ T ∈ target, distance (converter • R) T ≤ error
```

measured in the selected `fibreMetric A`. The witness `T` may depend on `R`. With
`error = 0` this asserts zero pseudo-distance, not membership; with `error = ∞` it asserts
only that `target` is nonempty whenever `source` is. -/
abbrev ConstructsWithin [CompatiblePseudoMetric C Phi] {A B : C}
    -- `converter : A ⟶ B` has outside interface `A` and inside interface `B`.
    (converter : A ⟶ B)
    -- `source` is a specification on the inside `B`; `target` one on the outside `A`.
    (source : Specification (Phi B)) (target : Specification (Phi A))
    -- `error : ENNReal` is a scalar budget, possibly `0` or `∞`.
    (error : ENNReal) : Prop :=
  @ConstructiveCryptography.Specification.ConstructsWithin _ _
    (CompatiblePseudoMetric.fibreMetric A).toEDist
    (attach converter) source target error

/-- Approximate construction holds exactly when every admitted source
resource attaches within the error bound of an admitted target resource. -/
lemma constructsWithin_iff [CompatiblePseudoMetric C Phi] {A B : C}
    {converter : A ⟶ B} {source : Specification (Phi B)}
    {target : Specification (Phi A)} {error : ENNReal} :
    ConstructsWithin converter source target error ↔
      ∀ resource ∈ source, ∃ ideal ∈ target,
        distance (attach converter resource) ideal ≤
          error := by
  -- Expose the resource-algebra names for the underlying functorial relation.
  rfl

/-- Singleton approximate construction is exactly the selected fibre-distance
bound after converter attachment. -/
lemma constructsWithin_singleton_iff [CompatiblePseudoMetric C Phi] {A B : C}
    {converter : A ⟶ B} {source : Phi B}
    {target : Phi A} {error : ENNReal} :
    ConstructsWithin converter
        ({source} : Specification (Phi B)) ({target} : Specification (Phi A))
        error ↔
      distance (attach converter source) target ≤
        error := by
  -- Singleton membership fixes both source and target witnesses.
  rw [constructsWithin_iff]
  simp only [Set.mem_singleton_iff, forall_eq, exists_eq_left]

/-- Approximate construction is invariant under equality of converters
between the same interfaces. -/
lemma constructsWithin_iff_of_converter_eq [CompatiblePseudoMetric C Phi]
    {A B : C} {left right : A ⟶ B} (equal : left = right)
    {source : Specification (Phi B)} {target : Specification (Phi A)}
    {error : ENNReal} :
    ConstructsWithin left source target error ↔
      ConstructsWithin right source target error := by
  -- Substitute the converter equality in the construction relation.
  subst right
  rfl

/-- The identity converter constructs every specification from itself with error zero,
each resource being its own witness. -/
@[simp]
lemma constructsWithin_identity [CompatiblePseudoMetric C Phi] {A : C}
    (source : Specification (Phi A)) :
    ConstructsWithin (𝟙 A) source source 0 := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  intro resource member
  exact ⟨resource, member, by simp [attach_identity]⟩

/-- Approximate constructions compose serially with additive error: `first ≫ second`
constructs `target` from `source` within `innerError + outerError` (untruncated `ENNReal`
sum). For `R ∈ source`, with witnesses `M ∈ middle` and `T ∈ target`:

```text
d(first • (second • R), T) ≤ d(first • (second • R), first • M) + d(first • M, T)
                           ≤ d(second • R, M) + d(first • M, T)   non-expansion of first
                           ≤ innerError + outerError
```

The inner error is carried through `first` unchanged because attachment is non-expanding. -/
lemma ConstructsWithin.serial [CompatiblePseudoMetric C Phi]
    -- `first : A ⟶ B` is the outer converter and `second : B ⟶ D` the inner one.
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    -- `source` lies on the inside interface `D` and `middle` on the intermediate `B`.
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    -- `target` lies on the outside `A`; `innerError`, `outerError` are the steps' budgets.
    {target : Specification (Phi A)} {innerError outerError : ENNReal}
    -- `inner`: `second` constructs `middle` from `source` within `innerError`.
    (inner : ConstructsWithin second source middle innerError)
    -- `outer`: `first` constructs `target` from `middle` within `outerError`.
    (outer : ConstructsWithin first middle target outerError) :
    ConstructsWithin (first ≫ second) source target
      (innerError + outerError) := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) B
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  change ConstructiveCryptography.Specification.ConstructsWithin
    (attach (first ≫ second)) source target (innerError + outerError)
  rw [show attach (first ≫ second) =
      attach first ∘ attach second from
    funext (attach_serial first second)]
  exact ConstructiveCryptography.Specification.ConstructsWithin.serial inner outer
    (LipschitzWith.of_edist_le (distance_attach_le first))

/-- Approximate constructions compose in ordered parallel with additive
error: `leftConverter ⊗ₘ rightConverter` constructs `parallel leftTarget rightTarget` from
`parallel leftSource rightSource` within `leftError + rightError`. The proof uses
`attach_parallel` to act componentwise and `distance_parallel_le` to add the component
distances. -/
lemma ConstructsWithin.parallel [CompatiblePseudoMetric C Phi]
    {A A' B B' : C}
    -- `leftConverter` has outside `A`, inside `A'`; `rightConverter` outside `B`, inside `B'`.
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    -- `leftSource` on `A'` and `leftTarget` on `A` are the left component's specifications.
    {leftSource : Specification (Phi A')} {leftTarget : Specification (Phi A)}
    -- `rightSource` on `B'` and `rightTarget` on `B` are the right component's.
    {rightSource : Specification (Phi B')} {rightTarget : Specification (Phi B)}
    -- `leftError` and `rightError` are the components' budgets, added untruncated.
    {leftError rightError : ENNReal}
    -- `leftConstruction`: `leftConverter` constructs `leftTarget` from `leftSource` within
    -- `leftError`.
    (leftConstruction : ConstructsWithin leftConverter
      leftSource leftTarget leftError)
    -- `rightConstruction`: `rightConverter` constructs `rightTarget` from `rightSource`
    -- within `rightError`.
    (rightConstruction : ConstructsWithin rightConverter
      rightSource rightTarget rightError) :
    ConstructsWithin (leftConverter ⊗ₘ rightConverter)
      (parallel leftSource rightSource)
      (parallel leftTarget rightTarget)
      (leftError + rightError) := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) B
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) (A ⊗ B)
  -- Apply locality and the selected parallel distance law to the generic theorem.
  exact ConstructiveCryptography.Specification.ConstructsWithin.parallel
    leftConstruction rightConstruction
    (CryptographicAlgebra.parallel) (CryptographicAlgebra.parallel)
    (attach (leftConverter ⊗ₘ rightConverter))
    (attach_parallel leftConverter rightConverter) (distance_parallel_le)

/-- Left context-insensitivity for approximate construction: if `converter : A ⟶ A'`
constructs `target` from `source` within `error`, then `converter ⊗ₘ 𝟙 B` constructs
`parallel target context` from `parallel source context` within the same `error`, for every
`context` on `B`; the unchanged context contributes distance zero. -/
lemma ConstructsWithin.left_context [CompatiblePseudoMetric C Phi]
    {A A' B : C} {converter : A ⟶ A'}
    {source : Specification (Phi A')} {target : Specification (Phi A)}
    {error : ENNReal}
    (construction : ConstructsWithin converter source target error)
    (context : Specification (Phi B)) :
    ConstructsWithin (converter ⊗ₘ 𝟙 B)
      (Specification.parallel source context)
      (Specification.parallel target context) error := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) (A ⊗ B)
  -- The selected ordered parallel supplies locality and the context distance law.
  exact ConstructiveCryptography.Specification.ConstructsWithin.left_context construction context
    CryptographicAlgebra.parallel CryptographicAlgebra.parallel (attach (converter ⊗ₘ 𝟙 B))
    (fun x y => by rw [attach_parallel, attach_identity]) (distance_parallel_left_le)

/-- Right context-insensitivity for approximate construction: if `converter : B ⟶ B'`
constructs `target` from `source` within `error`, then `𝟙 A ⊗ₘ converter` constructs
`parallel context target` from `parallel context source` within `error`, for every
`context` on `A`. -/
lemma ConstructsWithin.right_context [CompatiblePseudoMetric C Phi]
    {A B B' : C} {converter : B ⟶ B'}
    {source : Specification (Phi B')} {target : Specification (Phi B)}
    {error : ENNReal}
    (context : Specification (Phi A))
    (construction : ConstructsWithin converter source target error) :
    ConstructsWithin (𝟙 A ⊗ₘ converter)
      (Specification.parallel context source)
      (Specification.parallel context target) error := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) B
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) (A ⊗ B)
  -- The context stays on the left throughout the construction.
  exact ConstructiveCryptography.Specification.ConstructsWithin.right_context context construction
    CryptographicAlgebra.parallel CryptographicAlgebra.parallel (attach (𝟙 A ⊗ₘ converter))
    (fun x y => by rw [attach_parallel, attach_identity]) (distance_parallel_right_le)

end Specification

end CryptographicAlgebra

end ConstructiveCryptography

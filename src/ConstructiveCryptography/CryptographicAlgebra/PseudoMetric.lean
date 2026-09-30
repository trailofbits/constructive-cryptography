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

## Main definitions

* `CompatiblePseudoMetric C Φ`: a cryptographic algebra with a compatible pseudo-metric
* `CryptographicAlgebra.distance`: the distance of two resources on one interface
* `CryptographicAlgebra.Specification.ConstructsWithin`: approximate construction

## Main results

* `CryptographicAlgebra.distance_attach_le`, `CryptographicAlgebra.distance_parallel_le`:
  the compatibility conditions
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
d(R′, S′)` (condition 3). -/
class CompatiblePseudoMetric
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (Phi : C → Type w) [ResourceTheory C Phi] extends CryptographicAlgebra C Phi where
  fibreMetric : ∀ A : C, PseudoEMetricSpace (Phi A)
  edist_smul_le : ∀ {A B : C} (converter : A ⟶ B) (left right : Phi B),
    @edist _ (fibreMetric A).toEDist (attach converter left)
        (attach converter right) ≤
      @edist _ (fibreMetric B).toEDist left right
  edist_parallel_le : ∀ {A B : C} (left left' : Phi A)
      (right right' : Phi B),
    @edist _ (fibreMetric (A ⊗ B)).toEDist (resourceParallel laxMonoidal left right)
        (resourceParallel laxMonoidal left' right') ≤
      @edist _ (fibreMetric A).toEDist left left' + @edist _ (fibreMetric B).toEDist right right'

namespace CryptographicAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi]

/-- The distance of two resources on one interface. -/
noncomputable def distance [CompatiblePseudoMetric C Phi] {A : C}
    (left right : Phi A) : ENNReal :=
  @edist _ (CompatiblePseudoMetric.fibreMetric A).toEDist left right

@[simp]
theorem distance_self [CompatiblePseudoMetric C Phi] {A : C}
    (resource : Phi A) :
    distance resource resource = 0 := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_self resource

/-- Symmetry of the selected resource distance. -/
theorem distance_comm [CompatiblePseudoMetric C Phi] {A : C}
    (left right : Phi A) :
    distance left right = distance right left := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_comm left right

theorem distance_triangle [CompatiblePseudoMetric C Phi] {A : C}
    (left middle right : Phi A) :
    distance left right ≤
      distance left middle +
        distance middle right := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  exact edist_triangle left middle right

/-- Converter attachment is non-expanding in the selected fibre distances. -/
theorem distance_attach_le [CompatiblePseudoMetric C Phi] {A B : C}
    (converter : A ⟶ B) (left right : Phi B) :
    distance (attach converter left)
        (attach converter right) ≤
      distance left right :=
  CompatiblePseudoMetric.edist_smul_le converter left right

/-- If two converters agree on an ideal resource, replacing that resource
on each side bounds the distance between their real outputs.

Maurer--Renner 2016, Definition 2 (printed p. 11): “d(αR, αS) ≤ d(R, S)”.
The triangle inequality applies this law twice. Jost, Proposition 2.2.17
(printed pp. 29–30), identifies constructions through attachment equations;
here equality of the two ideal attachments is an explicit premise, rather
than a property assumed of arbitrary converters. -/
theorem distance_attach_le_add_of_eq [CompatiblePseudoMetric C Phi] {A B : C}
    (left right : A ⟶ B) (real ideal : Phi B)
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

/-- Attachment along an interface isomorphism preserves the selected fibre
distance exactly. -/
theorem distance_attach_iso [CompatiblePseudoMetric C Phi] {A B : C}
    (relabel : A ≅ B) (left right : Phi B) :
    distance (attach relabel.hom left)
        (attach relabel.hom right) =
      distance left right := by
  apply le_antisymm
  · -- Non-expansion gives the forward inequality.
    exact distance_attach_le relabel.hom left right
  · -- Apply the inverse isomorphism to obtain the reverse inequality.
    calc
      distance left right =
          distance
            (attach relabel.inv
              (attach relabel.hom left))
            (attach relabel.inv
              (attach relabel.hom right)) := by
                rw [← attach_serial relabel.inv relabel.hom,
                  ← attach_serial relabel.inv relabel.hom]
                simp
      _ ≤ distance
            (attach relabel.hom left)
            (attach relabel.hom right) :=
          distance_attach_le relabel.inv _ _

/-- Ordered resource parallel is jointly non-expanding. -/
theorem distance_parallel_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left left' : Phi A) (right right' : Phi B) :
    distance (parallel left right)
        (parallel left' right') ≤
      distance left left' +
        distance right right' :=
  CompatiblePseudoMetric.edist_parallel_le left left' right right'

/-- Ordered parallel with an unchanged right component is non-expanding in
the left component. -/
theorem distance_parallel_left_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left left' : Phi A) (right : Phi B) :
    distance (parallel left right)
        (parallel left' right) ≤
      distance left left' := by
  -- Apply joint non-expansion with identical right components.
  exact (distance_parallel_le left left' right right).trans_eq
    (by rw [distance_self, add_zero])

/-- Ordered parallel with an unchanged left component is non-expanding in
the right component. -/
theorem distance_parallel_right_le [CompatiblePseudoMetric C Phi] {A B : C}
    (left : Phi A) (right right' : Phi B) :
    distance (parallel left right)
        (parallel left right') ≤
      distance right right' := by
  -- Apply joint non-expansion with identical left components.
  exact (distance_parallel_le left left right right').trans_eq
    (by rw [distance_self, zero_add])

namespace Specification

/-- Approximate construction: every attached source resource is within `error` of an
admitted target resource. -/
abbrev ConstructsWithin [CompatiblePseudoMetric C Phi] {A B : C}
    (converter : A ⟶ B)
    (source : Specification (Phi B)) (target : Specification (Phi A))
    (error : ENNReal) : Prop :=
  @ConstructiveCryptography.Specification.ConstructsWithin _ _
    (CompatiblePseudoMetric.fibreMetric A).toEDist
    (attach converter) source target error

/-- Approximate construction holds exactly when every admitted source
resource attaches within the error bound of an admitted target resource. -/
theorem constructsWithin_iff [CompatiblePseudoMetric C Phi] {A B : C}
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
theorem constructsWithin_singleton_iff [CompatiblePseudoMetric C Phi] {A B : C}
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
theorem constructsWithin_iff_of_converter_eq [CompatiblePseudoMetric C Phi]
    {A B : C} {left right : A ⟶ B} (equal : left = right)
    {source : Specification (Phi B)} {target : Specification (Phi A)}
    {error : ENNReal} :
    ConstructsWithin left source target error ↔
      ConstructsWithin right source target error := by
  -- Substitute the converter equality in the construction relation.
  subst right
  rfl

@[simp]
theorem constructsWithin_identity [CompatiblePseudoMetric C Phi] {A : C}
    (source : Specification (Phi A)) :
    ConstructsWithin (𝟙 A) source source 0 := by
  let := CompatiblePseudoMetric.fibreMetric (Phi := Phi) A
  intro resource member
  exact ⟨resource, member, by simp [attach_identity]⟩

/-- Approximate constructions compose serially with additive error. -/
theorem ConstructsWithin.serial [CompatiblePseudoMetric C Phi]
    {A B D : C} {first : A ⟶ B} {second : B ⟶ D}
    {source : Specification (Phi D)} {middle : Specification (Phi B)}
    {target : Specification (Phi A)} {innerError outerError : ENNReal}
    (inner : ConstructsWithin second source middle innerError)
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
error. -/
theorem ConstructsWithin.parallel [CompatiblePseudoMetric C Phi]
    {A A' B B' : C}
    {leftConverter : A ⟶ A'} {rightConverter : B ⟶ B'}
    {leftSource : Specification (Phi A')} {leftTarget : Specification (Phi A)}
    {rightSource : Specification (Phi B')} {rightTarget : Specification (Phi B)}
    {leftError rightError : ENNReal}
    (leftConstruction : ConstructsWithin leftConverter
      leftSource leftTarget leftError)
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

/-- Left context-insensitivity for approximate construction. -/
theorem ConstructsWithin.left_context [CompatiblePseudoMetric C Phi]
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

/-- Right context-insensitivity for approximate construction. -/
theorem ConstructsWithin.right_context [CompatiblePseudoMetric C Phi]
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

import ConstructiveCryptography.Specification.Action
import ConstructiveCryptography.Specification.Relaxation.Closure
import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Converter-class closure

`star Γ S` is the image of `S` under converters in the chosen submonoid `Γ`.
The identity gives extensivity and multiplication gives idempotence.
`starClosure Γ` packages the same operation as a Mathlib `ClosureOperator`.
Maps commuting with the admitted action preserve exact construction between
star-closed specifications, by `image_star_subset` and `Constructs.star`.
The simulator rules establish membership in the target closure from an explicit
equation; the constructing map may start from a different carrier.
-/

namespace ConstructiveCryptography.Specification

universe u v w

variable {C : Type u} {X : Type v} [Monoid C] [MulAction C X]

/-- Closure under a selected class of converters.

MR16, Section 3.4 (printed p. 8): “R* := RΣ = {Rβ | R ∈ R, β ∈ Σ}”.
The chosen action includes the attachment position; the class is explicit. -/
def star (converters : Submonoid C) (source : Specification X) : Specification X :=
  Set.image2 (· • ·) (converters : Set C) source

/-- The identity converter admits each original resource.

MR16, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”. -/
theorem subset_star (converters : Submonoid C) (source : Specification X) :
    source ⊆ star converters source := by
  intro resource admitted
  exact ⟨1, converters.one_mem, resource, admitted, one_smul C resource⟩

/-- Closure under converters is idempotent.

MR16, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”.
Jost, Section 2.2.5 (printed pp. 23–24), uses a specified converter class;
the submonoid here supplies its identity and composition closure. -/
theorem star_idem (converters : Submonoid C) (source : Specification X) :
    star converters (star converters source) = star converters source := by
  apply Set.Subset.antisymm
  · -- Replace two admitted converters by their admitted product.
    rintro resource ⟨outer, outerAdmitted, _, ⟨inner, innerAdmitted,
      original, sourceAdmitted, rfl⟩, rfl⟩
    exact ⟨outer * inner, converters.mul_mem outerAdmitted innerAdmitted,
      original, sourceAdmitted, mul_smul outer inner original⟩
  · -- The identity converter gives the reverse inclusion.
    exact subset_star converters _

/-- The converter-class closure as a Mathlib closure operator. -/
def starClosure (converters : Submonoid C) : ClosureOperator (Specification X) :=
  ClosureOperator.mk' (star converters)
    (fun _ _ included => Set.image2_subset Set.Subset.rfl included)
    (subset_star converters) (fun source => (star_idem converters source).le)

/-- A commuting map carries converter-class closure into the closure of its image.

MR16, Section 3.3 (printed p. 8): “(αR)β = α(Rβ)”.
The commutation equation is required only for the admitted converters. -/
theorem image_star_subset {f : X → X} {converters : Submonoid C}
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource)
    (source : Specification X) :
    f '' star converters source ⊆ star converters (f '' source) := by
  -- Decompose the image and its admitted converter witness.
  rintro resource ⟨_, ⟨converter, admitted, original, sourceAdmitted, rfl⟩, rfl⟩
  -- Commute the map past that converter, retaining the same witness.
  exact ⟨converter, admitted, f original, ⟨original, sourceAdmitted, rfl⟩,
    (commutes converter admitted original).symm⟩

/-- Exact construction is compatible with converter-class closure.

MR16, Lemma 3 (printed p. 11): “R —π→ S ⟹ R* —π→ S*”.
Jost, Section 2.2.5 and Corollary 2.2.13 (printed pp. 23–24), treats
simulation-based specifications as a specialization and derives composition
from commutation and inclusion. Here the map and its commutation law are explicit. -/
theorem Constructs.star {f : X → X} {converters : Submonoid C}
    {source target : Specification X}
    (construction : Constructs f source target)
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource) :
    Constructs f (star converters source) (star converters target) := by
  -- Apply specification-map compatibility using monotonicity of star closure.
  exact construction.map (starClosure converters) (starClosure converters)
    (starClosure converters).monotone (image_star_subset commutes)

/-- An admitted simulator equation establishes construction into star closure.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”. Jost, Section 2.2.5
(printed p. 23), treats simulation-based specifications as a specialization.
The constructing map may have a different source carrier. -/
theorem constructs_star_of_simulator {Y : Type w} {f : Y → X}
    {converters : Submonoid C} {real : Y} {ideal : X}
    (simulator : C) (admitted : simulator ∈ converters)
    (equation : f real = simulator • ideal) :
    Constructs f {real} (star converters {ideal}) := by
  rintro resource rfl
  -- The selected simulator witnesses membership in the ideal closure.
  exact ⟨simulator, admitted, ideal, rfl, equation.symm⟩

/-- A simulator for each source resource establishes the corresponding specification.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”.
At exact equality the same witnesses establish image inclusion. -/
theorem constructs_star_of_simulators {Y : Type w} {f : Y → X}
    {converters : Submonoid C} {real : Specification Y} {ideal : X}
    (simulates : ∀ resource ∈ real, ∃ simulator ∈ converters,
      f resource = simulator • ideal) :
    Constructs f real (star converters {ideal}) := by
  intro resource sourceAdmitted
  -- Keep the simulator chosen for this particular source resource.
  obtain ⟨simulator, admitted, equation⟩ := simulates resource sourceAdmitted
  exact ⟨simulator, admitted, ideal, rfl, equation.symm⟩

end ConstructiveCryptography.Specification

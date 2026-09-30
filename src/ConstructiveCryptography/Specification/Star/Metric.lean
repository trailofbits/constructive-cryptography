import ConstructiveCryptography.Specification.Star
import ConstructiveCryptography.Specification.Metric

/-!
# Scalar comparison and converter-class closure

Admitted converter actions preserve distance bounds when they are non-expanding.
Simulator witnesses use the distance on the target resource carrier.
-/

namespace ConstructiveCryptography.Specification

universe u v w

variable {C : Type u} {X : Type v} [Monoid C] [MulAction C X] [EDist X]

/-- Non-expanding admitted actions preserve construction after star closure.

MR16, Definition 2 and Lemma 3 (printed p. 11), supply non-expansion and
“R —π→ S ⟹ R* —π→ S*”. Jost, Corollary 2.2.13 (printed p. 24),
uses commutation and comparison compatibility for simulation specifications.
The scalar bound here uses non-expansion only of the admitted class. -/
theorem ConstructsWithin.star {f : X → X} {converters : Submonoid C}
    {source target : Specification X} {error : ENNReal}
    (construction : ConstructsWithin f source target error)
    (commutes : ∀ converter ∈ converters, ∀ resource,
      f (converter • resource) = converter • f resource)
    (nonexpanding : ∀ converter ∈ converters, ∀ R S : X,
      edist (converter • R) (converter • S) ≤ edist R S) :
    ConstructsWithin f (star converters source) (star converters target) error := by
  -- Apply the original construction to the source center.
  rintro resource ⟨converter, admitted, original, sourceAdmitted, rfl⟩
  obtain ⟨ideal, idealAdmitted, close⟩ := construction original sourceAdmitted
  -- Apply the same admitted converter to the ideal center.
  refine ⟨converter • ideal, ⟨converter, admitted, ideal, idealAdmitted, rfl⟩, ?_⟩
  -- Commutation and non-expansion preserve the original error.
  rw [commutes converter admitted original]
  exact (nonexpanding converter admitted (f original) ideal).trans close

/-- One simulator distance bound proves construction into a star-relaxed ideal.

MR16, Equation (3) (printed p. 12): “πR ≈ε Sσ”. The simulator remains
an explicit witness; no distance on the real resource carrier is required. -/
theorem constructsWithin_star_of_simulator {Y : Type w} {f : Y → X}
    {converters : Submonoid C} {real : Y} {ideal : X} {error : ENNReal}
    (simulator : C) (admitted : simulator ∈ converters)
    (close : edist (f real) (simulator • ideal) ≤ error) :
    ConstructsWithin f {real} (star converters {ideal}) error := by
  rintro resource rfl
  -- Retain the simulator witness and its supplied distance bound.
  exact ⟨simulator • ideal, ⟨simulator, admitted, ideal, rfl, rfl⟩, close⟩

/-- Pointwise simulator bounds establish the source specification.

MR16, Lemma 5, proof (printed p. 12): “Sσ ∈ SΣ = S*”.
The ideal center is fixed here and the simulator may depend on the real resource. -/
theorem constructsWithin_star_of_simulators {Y : Type w} {f : Y → X}
    {converters : Submonoid C} {real : Specification Y} {ideal : X} {error : ENNReal}
    (simulates : ∀ resource ∈ real, ∃ simulator ∈ converters,
      edist (f resource) (simulator • ideal) ≤ error) :
    ConstructsWithin f real (star converters {ideal}) error := by
  intro resource sourceAdmitted
  -- Keep the simulator and bound supplied for this source resource.
  obtain ⟨simulator, admitted, close⟩ := simulates resource sourceAdmitted
  exact ⟨simulator • ideal, ⟨simulator, admitted, ideal, rfl, rfl⟩, close⟩

end ConstructiveCryptography.Specification

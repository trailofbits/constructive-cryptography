import ConstructiveCryptography.InterfaceAlgebra
import RandomSystems.Typed.Functional

/-!
# Revealed H-coefficient regression examples

The zero-error argument uses an arbitrary resource and an empty bad event. The marginal
checks retain kernel normalization, and the weighted-class identity supports more than two
classes without changing the system's domain.
-/

open Probability SystemAlgebra
open scoped NNReal

namespace SystemAlgebra.Tests.RevealedHCoefficient

/-- Revealing a constant adds no distinguishing error, at every interface and budget. -/
noncomputable def constantReveal (A : Interface) (S : TypedSystem A) :
    RandomSystem.HCoefficient S.1 S.1 0 := by
  classical
  let P := Distribution.ProbDist.single ()
  have hp : S.1 = RandomSystem.mix P (fun _ => S.1) := by
    -- A point mixture retains exactly the original cumulative probabilities.
    apply RandomSystem.ext
    intro h
    simp [RandomSystem.mix_mass, P, Distribution.ProbDist.single]
  -- Both extended laws append the same constant; there are no bad transcripts.
  simpa using RandomSystem.HCoefficient.ofGoodBad P (fun _ => S.1) hp (fun _ => S.2) S.2
    (fun _ _ => ()) (fun _ => Finsupp.single () 1)
    (fun _ => Distribution.isProbDist_single ()) (fun _ => False) (ε₁ := 0) (ε₂ := 0)
    le_rfl
    (fun τ _ => by
      rcases τ with ⟨h, ⟨⟩⟩
      simp [RandomSystem.kernelMass, RandomSystem.revealMass, P, Distribution.ProbDist.single])
    (fun _ _ _ _ => by simp [Distribution.mass])

/-- The systems bound reaches the existing CC distance without changing the model. -/
example (A : Interface) (S : TypedSystem A) :
    ConstructiveCryptography.CryptographicAlgebra.distance S S ≤ (0 : ℝ≥0) :=
  Interface.distance_le_of_hCoefficient (constantReveal A S)

/-- Arbitrary finite transcript classes retain their own errors. -/
example {T : Type} (law : Distribution T) (classOf : T → Fin 3) (error : Fin 3 → ℝ) :
    law.expect (fun t => error (classOf t)) =
      ∑ c, error c * law.mass (fun t => classOf t = c) :=
  Distribution.expect_comp_eq_sum_mass law classOf error

/-- A zero conditional law is not a normalized reveal, even on a zero-query interface. -/
example : ¬ (0 : Distribution Unit).isProbDist := by
  intro h
  have hw := h.weight_eq
  norm_num [Distribution.weight] at hw

#print axioms RandomSystem.statDist_sLaw_le_of_reveal
#print axioms RandomSystem.HCoefficient.transcriptDistance_le_nnreal
#print axioms Interface.distance_le_of_hCoefficient
#print axioms constantReveal

end SystemAlgebra.Tests.RevealedHCoefficient

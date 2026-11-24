import Tests.Rendering.Proofs

/-! Real calculation, substitution and H-coefficient examples for native and exported views. -/

set_option linter.hashCommand false

open CategoryTheory ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra DSLExamples SubstitutionRelation

namespace Rendering.ProofGallery
variable {C : Type} [Category C] [CategoryTheory.MonoidalCategory C]
variable {Phi : C → Type} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
variable {A : C} (worlds : Bool → Phi A)
variable (loss : Fin 2 → ENNReal)
variable (localBound : ∀ j : Fin 2, distance (worlds false) (worlds true) ≤ loss j)

#cc_proof_show ProofTests.roundTrip worlds
#cc_proof_show (ProofTests.roundTrip worlds).distance_le loss localBound

variable {n : Nat} (symbolic : Implication (fun _ : Unit => A) (fun _ => worlds) A n)
#cc_proof_show symbolic

-- The navigation presents the exact elaborated relations and the supplied justification.
example (R : Phi A) : (𝟙 A ≫ 𝟙 A) • R = R := by
  calc
    (𝟙 A ≫ 𝟙 A) • R = (𝟙 A) • ((𝟙 A) • R) := attach_serial _ _ R
    _ = (𝟙 A) • R := attach_identity _
    _ = R := attach_identity _

end Rendering.ProofGallery

namespace Rendering.ProofGallery.Concrete
variable {A : Interface} (R S : TypedSystem A) (ε : NNReal)
variable (w : RandomSystem.HCoefficient R.1 S.1 ε)
#cc_proof_show w
#cc_proof_show Interface.distance_le_of_hCoefficient w

#cc_proof_show SystemAlgebra.Tests.RevealedHCoefficient.halfBadReveal
  (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3)
  (Counter (budget := 3))

-- With automatic viewing enabled, the cursor on this definition also shows the argument.
noncomputable def counterArgument :=
  SystemAlgebra.Tests.RevealedHCoefficient.halfBadReveal
    (Interface.queryBudget Counter.Port Counter.Input Counter.Output 3)
    (Counter (budget := 3))

end Rendering.ProofGallery.Concrete

module

public import Commons.Definitions.ActiveUserBank
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for active-user bank specifications and registration

Exercises `ActiveUserBank` over `Interface` using CC's custom notation (`Δ`, `•`, `∥`,
`—[...; ...]→`) and checks tactic interoperability with `cc_normalize`, `cc_construct`, and
`cc_calc statistical`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.ActiveUserBank

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra Commons
open scoped SystemAlgebra

/-- Registration on interfaces bounds the registered distance by the filtered bank error. -/
example {Registry B B' Out : Interface} (registry : TypedSystem Registry)
    (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B)
    {idealBank R : TypedSystem B} {ε : ENNReal}
    (hR : Δ (filterRows • R) (filterRows • idealBank) ≤ ε) :
    Δ (filterRegistration • (registry ∥ filterRows • R))
      (filterRegistration • (registry ∥ filterRows • idealBank)) ≤ ε :=
  ActiveUserBank.registration_distance_le registry filterRegistration filterRows
    (ActiveUserBank.mem_specification_iff.mpr hR)

/-- The bank specification is non-empty at every budget, including `0`. -/
example {B B' : Interface} (idealBank : TypedSystem B) (filterRows : B' ⟶ B) :
    idealBank ∈ ActiveUserBank.specification idealBank filterRows 0 :=
  ActiveUserBank.idealBank_mem_specification idealBank filterRows 0

/-- `cc_normalize` unfolds the composed registration converter `(filterRegistration ≫ (𝟙 ⊗ₘ
filterRows)) • (registry ∥ R)` to the nested registered bank presentation. -/
example {Registry B B' Out : Interface} (registry : TypedSystem Registry)
    (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B) (R : TypedSystem B) :
    (filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows)) • (registry ∥ R) =
      filterRegistration • (registry ∥ filterRows • R) := by
  cc_normalize

/-- `cc_construct` closes the singleton registration construction from
`ActiveUserBank.registration_distance_le` after `cc_normalize`. -/
example {Registry B B' Out : Interface} (registry : TypedSystem Registry)
    (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B)
    {idealBank R : TypedSystem B} {ε : ENNReal}
    (hR : R ∈ ActiveUserBank.specification idealBank filterRows ε) :
    {registry ∥ R} —[filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows); ε]→
      {filterRegistration • (registry ∥ filterRows • idealBank)} := by
  cc_construct
  cc_normalize
  exact ActiveUserBank.registration_distance_le registry filterRegistration filterRows hR

/-- `cc_calc statistical` chains `ActiveUserBank.registration_distance_le` with a second
statistical hop under an outer converter `α`. -/
example {Registry B B' Out Outer : Interface} (registry : TypedSystem Registry)
    (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B) (α : Outer ⟶ Out)
    {idealBank R : TypedSystem B} {S : TypedSystem Out} {ε δ : ENNReal}
    (hR : R ∈ ActiveUserBank.specification idealBank filterRows ε)
    (hS : Δ (filterRegistration • (registry ∥ filterRows • idealBank)) S ≤ δ) :
    Δ (α • (filterRegistration • (registry ∥ filterRows • R))) (α • S) ≤ ε + δ := by
  cc_calc statistical
    α • (filterRegistration • (registry ∥ filterRows • R))
      ≈[ε] α • (filterRegistration • (registry ∥ filterRows • idealBank)) :=
      ActiveUserBank.registration_distance_le registry filterRegistration filterRows hR
    _ ≈[δ] α • S := hS

#print axioms ActiveUserBank.registration_constructs
#print axioms ActiveUserBank.registration_distance_le

end Tests.ActiveUserBank

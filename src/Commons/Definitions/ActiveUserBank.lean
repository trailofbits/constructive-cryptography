module

public import ConstructiveCryptography.Notation.Basic

/-!
# Active-user bank specifications and generic registration

In MR16 [1, §§2–4], applications are proved once against a non-singleton specification and
instantiated per backend. `ActiveUserBank.specification idealBank filterRows ε` collects every
bank whose row-filtered view lies within `ε` of `filterRows • idealBank`.
`ActiveUserBank.registration_constructs` shows once, over any `CryptographicAlgebra` with a
compatible pseudo-metric, that running an issuing `registry` in parallel and attaching a
registration filter constructs the registered ideal bank within the same `ε`;
`ActiveUserBank.registration_distance_le` is its distance form.

## References

1. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back).
   TCC 2016-B. Cryptology ePrint Archive, Paper 2016/903.
2. M. Backendal, M. Bellare, F. Günther and M. Scarlata. When Messages are Keys: Is HMAC a
   dual-PRF? CRYPTO 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open scoped SystemAlgebra

universe u v w

namespace ActiveUserBank

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- Banks whose row-filtered view lies within `ε` of `filterRows • idealBank` [1, §§2–4]. -/
def specification {B B' : C} (idealBank : Phi B) (filterRows : B' ⟶ B) (ε : ENNReal) :
    ConstructiveCryptography.Specification (Phi B) :=
  {R | {R} —[filterRows; ε]→ {filterRows • idealBank}}

/-- Membership in `specification` is the filtered distance bound. -/
lemma mem_specification_iff {B B' : C} {idealBank R : Phi B} {filterRows : B' ⟶ B}
    {ε : ENNReal} :
    R ∈ specification idealBank filterRows ε ↔
      Δ (filterRows • R) (filterRows • idealBank) ≤ ε :=
  constructsWithin_singleton_iff

/-- The ideal bank meets every budget. -/
lemma idealBank_mem_specification {B B' : C} (idealBank : Phi B) (filterRows : B' ⟶ B)
    (ε : ENNReal) : idealBank ∈ specification idealBank filterRows ε := by
  rw [mem_specification_iff, distance_self]
  exact bot_le

/-- Enlarging the budget enlarges the specification. -/
lemma specification_mono {B B' : C} (idealBank : Phi B) (filterRows : B' ⟶ B)
    {ε ε' : ENNReal} (hle : ε ≤ ε') :
    specification idealBank filterRows ε ⊆ specification idealBank filterRows ε' :=
  fun _ h => mem_specification_iff.mpr ((mem_specification_iff.mp h).trans hle)

/-- **Generic registration** [2, §3.3, Fig. 1]: attaching an issuing `registry` in parallel and a
registration filter `filterRegistration` constructs the registered ideal bank within the same `ε`.

```text
{registry} ∥ Bank_ε  ──(𝟙 ⊗ₘ filterRows)──▶  {registry} ∥ {filterRows • ideal}      within ε
                     ──filterRegistration─▶  {filterRegistration • (registry ∥ …)}  exact
```
-/
theorem registration_constructs {Registry B B' Out : C}
    (registry : Phi Registry) (filterRegistration : Out ⟶ Registry ⊗ B')
    (filterRows : B' ⟶ B) (idealBank : Phi B) (ε : ENNReal) :
    Specification.parallel {registry} (specification idealBank filterRows ε)
      —[filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows); ε]→
      {filterRegistration • (registry ∥ filterRows • idealBank)} := by
  have bank : specification idealBank filterRows ε —[filterRows; ε]→ {filterRows • idealBank} :=
    fun R hR => hR R rfl
  have inner := ConstructsWithin.right_context {registry} bank
  rw [Specification.parallel_singleton] at inner
  have outer :
      {registry ∥ filterRows • idealBank} —[filterRegistration; 0]→
        {filterRegistration • (registry ∥ filterRows • idealBank)} := by
    rw [constructsWithin_singleton_iff, distance_self]
  simpa only [add_zero] using ConstructsWithin.serial inner outer

/-- Distance form of `registration_constructs` for any bank `R` in the specification. -/
theorem registration_distance_le {Registry B B' Out : C}
    (registry : Phi Registry) (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B)
    {idealBank R : Phi B} {ε : ENNReal} (hR : R ∈ specification idealBank filterRows ε) :
    Δ (filterRegistration • (registry ∥ filterRows • R))
      (filterRegistration • (registry ∥ filterRows • idealBank)) ≤ ε := by
  obtain ⟨T, hT, hle⟩ := registration_constructs registry filterRegistration filterRows idealBank ε
    (registry ∥ R) ⟨registry, rfl, R, hR, rfl⟩
  obtain rfl := Set.mem_singleton_iff.mp hT
  rwa [attach_serial, attach_parallel, attach_identity] at hle

end ActiveUserBank

end Commons

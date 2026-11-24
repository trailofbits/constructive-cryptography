module

public import ConstructiveCryptography.CryptographicAlgebra.Epsilon
public import ConstructiveCryptography.Notation.Basic

/-!
# Active-user bank specifications and generic registration

A bank qualifies when its visible rows are within `ε` of the ideal bank's visible rows.
The row filter determines which differences count. `ActiveUserBank.registration_constructs`
puts a common registry beside both filtered views and applies the same registration converter.
Neither operation increases the error. `ActiveUserBank.registration_distance_le` gives the
bound for an individual bank.

## References

1. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back).
   TCC 2016-B. Cryptology ePrint Archive, Paper 2016/903.
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

-- `Phi B` carries the bank resources on interface `B : C`; `Δ` compares two such resources.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- Pull back the closed `ε`-relaxation “R^ε = {R′ | ∃R ∈ R : R′ ≈ε R}” [1, §2.3, p. 5]
along the row filter. -/
def specification {B B' : C}
    -- `idealBank` supplies the reference on `B`; `filterRows` exposes a view on `B'`.
    (idealBank : Phi B) (filterRows : B' ⟶ B) (ε : ENNReal) :
    ConstructiveCryptography.Specification (Phi B) :=
  attach filterRows ⁻¹' (epsilonRelaxation ε {filterRows • idealBank})

/-- Membership in `specification` is the filtered distance bound. -/
lemma mem_specification_iff {B B' : C} {idealBank R : Phi B} {filterRows : B' ⟶ B}
    {ε : ENNReal} :
    R ∈ specification idealBank filterRows ε ↔
      Δ (filterRows • R) (filterRows • idealBank) ≤ ε := by
  simp only [specification, Set.mem_preimage, mem_epsilonRelaxation_iff,
    Set.mem_singleton_iff, exists_eq_left]

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

/-- Registration preserves the row-filtered error `ε`.

```text
bank R  ──filterRows──▶  view  ──registry ∥ (·)──▶  pair  ──filterRegistration──▶  output
                         ≤ ε                         ≤ ε                           ≤ ε
```
Each bound compares the indicated stage for `R` and for `idealBank`. -/
theorem registration_constructs {Registry B B' Out : C}
    -- `registry` is shared by both constructions; `filterRegistration` observes the pair on `Out`.
    (registry : Phi Registry) (filterRegistration : Out ⟶ Registry ⊗ B')
    -- `filterRows` exposes the bank on `B'`, where `ε` bounds its distance to the ideal view.
    (filterRows : B' ⟶ B) (idealBank : Phi B) (ε : ENNReal) :
    Specification.parallel {registry} (specification idealBank filterRows ε)
      —[filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows); ε]→
      {filterRegistration • (registry ∥ filterRows • idealBank)} := by
  have bank : specification idealBank filterRows ε —[filterRows; ε]→ {filterRows • idealBank} :=
    constructs_epsilonRelaxation_iff.mp (fun _ hR => hR)
  -- Adding the same registry on the left preserves the row bound.
  have inner := ConstructsWithin.right_context {registry} bank
  rw [Specification.parallel_singleton] at inner
  -- On the ideal pair, the last attachment produces the target exactly.
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
  calc
    _ ≤ Δ (registry ∥ filterRows • R) (registry ∥ filterRows • idealBank) :=
      distance_attach_le filterRegistration _ _
    _ ≤ Δ (filterRows • R) (filterRows • idealBank) := distance_parallel_right_le registry _ _
    _ ≤ ε := mem_specification_iff.mp hR

end ActiveUserBank

end Commons

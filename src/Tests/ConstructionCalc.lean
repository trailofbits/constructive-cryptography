module

public import Commons.Definitions.ActiveUserBank
public import Commons.Definitions.Indifferentiability
public import ConstructiveCryptography

/-!
# Construction calculation chains (`cc_calc constructs`)

Exercises construction chains over pure `ResourceTheory`, abstract
`CryptographicAlgebra` / `CompatiblePseudoMetric`, and concrete `Interface` (`ActiveUserBank`
and `Indifferentiability`), including mixed exact/approximate steps, converter and budget
normalization, coexistence with `cc_calc statistical`, negative failure guards, and axioms.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.ConstructionCalc

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Commons
open scoped SystemAlgebra

section ResourceTheoryOnly

universe u v w
variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]

/-- Pure exact chains work in any `ResourceTheory` without a metric or monoidal structure,
composing converters in attachment order and normalizing associativity and identities. -/
example {A B D E : C} (π₁ : D ⟶ E) (π₂ : B ⟶ D) (π₃ : A ⟶ B)
    (R₀ : Specification (Phi E)) (R₁ : Specification (Phi D))
    (R₂ : Specification (Phi B)) (R₃ : Specification (Phi A))
    (h₁ : R₀ —[π₁]→ R₁) (h₂ : R₁ —[π₂]→ R₂) (h₃ : R₂ —[π₃]→ R₃) :
    R₀ —[(π₃ ≫ π₂) ≫ π₁]→ R₃ := by
  cc_calc constructs
    R₀ —[π₁]→ R₁ := h₁
    _  —[π₂]→ R₂ := h₂
    _  —[π₃]→ R₃ := h₃

/-- Exact specification equalities may appear before, between, and after exact construction steps,
and intermediate specifications may be written explicitly or reused with `_`. -/
example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ R₀' : Specification (Phi D)) (R₁ R₁' : Specification (Phi B))
    (R₂ R₂' : Specification (Phi A))
    (h₀ : R₀ = R₀') (h₁ : R₀' —[π₁]→ R₁) (h₁₂ : R₁ = R₁')
    (h₂ : R₁' —[π₂]→ R₂) (h₃ : R₂ = R₂') :
    R₀ —[𝟙 A ≫ π₂ ≫ 𝟙 B ≫ π₁]→ R₂' := by
  cc_calc constructs
    R₀  = R₀' := h₀
    _   —[π₁]→ R₁ := h₁
    R₁  = R₁' := h₁₂
    _   —[π₂]→ R₂ := h₂
    _   = R₂' := h₃

/-- Single-step construction surrounded by exact specification equalities. -/
example {A B : C} (π : A ⟶ B) (R₀ R₀' : Specification (Phi B)) (R₁ R₁' : Specification (Phi A))
    (h₀ : R₀ = R₀') (h : R₀' —[π]→ R₁) (h₁ : R₁ = R₁') :
    R₀ —[π]→ R₁' := by
  cc_calc constructs
    R₀ = R₀' := h₀
    _  —[π]→ R₁ := h
    _  = R₁' := h₁

/-- Closing the current construction leaves unrelated pending goals available. -/
example {A B : C} (π : A ⟶ B)
    (R : Specification (Phi B)) (S : Specification (Phi A))
    (h : R —[π]→ S) : (R —[π]→ S) ∧ True := by
  constructor
  first
  | cc_calc constructs
      R —[π]→ S := h
  trivial

end ResourceTheoryOnly

section AbstractMetric

universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- Pure approximate chains sum scalar budgets and normalize both associativity of converters
and associativity of `ENNReal` addition, closing both `ConstructsWithin` and `epsilonRelaxation`. -/
theorem abstract_approx_chain {A B D E : C} (π₁ : D ⟶ E) (π₂ : B ⟶ D) (π₃ : A ⟶ B)
    (R₀ : Specification (Phi E)) (R₁ : Specification (Phi D))
    (R₂ : Specification (Phi B)) (R₃ : Specification (Phi A))
    {ε₁ ε₂ ε₃ : ENNReal}
    (h₁ : R₀ —[π₁; ε₁]→ R₁) (h₂ : R₁ —[π₂; ε₂]→ R₂) (h₃ : R₂ —[π₃; ε₃]→ R₃) :
    (R₀ —[(π₃ ≫ π₂) ≫ π₁; ε₁ + (ε₂ + ε₃)]→ R₃) ∧
      (R₀ —[(π₃ ≫ π₂) ≫ π₁]→ epsilonRelaxation (ε₁ + (ε₂ + ε₃)) R₃) := by
  constructor
  · cc_calc constructs
      R₀ —[π₁; ε₁]→ R₁ := h₁
      _  —[π₂; ε₂]→ R₂ := h₂
      _  —[π₃; ε₃]→ R₃ := h₃
  · cc_calc constructs
      R₀ —[π₁; ε₁]→ R₁ := h₁
      _  —[π₂; ε₂]→ R₂ := h₂
      _  —[π₃; ε₃]→ R₃ := h₃

/-- Mixing exact and approximate steps in either order produces the exact scalar budget without
spurious `0 + ε` or `ε + 0` summands, and explicit `0` budgets also normalize away. -/
example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ : Specification (Phi B)) (R₂ : Specification (Phi A))
    {ε : ENNReal}
    (h₁ : R₀ —[π₁]→ R₁) (h₂ : R₁ —[π₂; ε]→ R₂) :
    R₀ —[π₂ ≫ π₁; ε]→ R₂ := by
  cc_calc constructs
    R₀ —[π₁]→ R₁ := h₁
    _  —[π₂; ε]→ R₂ := h₂

example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ : Specification (Phi B)) (R₂ : Specification (Phi A))
    {ε : ENNReal}
    (h₁ : R₀ —[π₁; ε]→ R₁) (h₂ : R₁ —[π₂]→ R₂) :
    R₀ —[π₂ ≫ π₁; ε]→ R₂ := by
  cc_calc constructs
    R₀ —[π₁; ε]→ R₁ := h₁
    _  —[π₂]→ R₂ := h₂

example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ : Specification (Phi B)) (R₂ : Specification (Phi A))
    {ε : ENNReal}
    (h₁ : R₀ —[π₁; 0]→ R₁) (h₂ : R₁ —[π₂; ε]→ R₂) :
    R₀ —[π₂ ≫ π₁; ε]→ R₂ := by
  cc_calc constructs
    R₀ —[π₁; 0]→ R₁ := h₁
    _  —[π₂; ε]→ R₂ := h₂

/-- Pure exact chains also close zero-error approximate and `epsilonRelaxation 0` goals. -/
example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ : Specification (Phi B)) (R₂ : Specification (Phi A))
    (h₁ : R₀ —[π₁]→ R₁) (h₂ : R₁ —[π₂]→ R₂) :
    (R₀ —[π₂ ≫ π₁; 0]→ R₂) ∧ (R₀ —[π₂ ≫ π₁]→ epsilonRelaxation 0 R₂) := by
  constructor
  · cc_calc constructs
      R₀ —[π₁]→ R₁ := h₁
      _  —[π₂]→ R₂ := h₂
  · cc_calc constructs
      R₀ —[π₁]→ R₁ := h₁
      _  —[π₂]→ R₂ := h₂

/-- Whiskered and tensored converter compositions normalize structurally across steps. -/
example {H H' H'' P Q R : C} (π : H ⟶ H'') (κ : H' ⟶ H) (σ₁ : Q ⟶ R) (σ₂ : P ⟶ Q)
    (S₀ : Specification (Phi (H'' ⊗ P))) (S₁ : Specification (Phi (H ⊗ P)))
    (S₂ : Specification (Phi (H' ⊗ P)))
    (T₀ : Specification (Phi (H ⊗ R))) (T₁ : Specification (Phi (H ⊗ Q)))
    (T₂ : Specification (Phi (H ⊗ P)))
    (U₀ : Specification (Phi (H'' ⊗ R))) (U₁ : Specification (Phi (H ⊗ Q)))
    (U₂ : Specification (Phi (H' ⊗ P)))
    {ε δ : ENNReal}
    (hR₁ : S₀ —[π ▷ P; ε]→ S₁) (hR₂ : S₁ —[κ ▷ P; δ]→ S₂)
    (hL₁ : T₀ —[H ◁ σ₁]→ T₁) (hL₂ : T₁ —[H ◁ σ₂; ε]→ T₂)
    (hT₁ : U₀ —[π ⊗ₘ σ₁; ε]→ U₁) (hT₂ : U₁ —[κ ⊗ₘ σ₂; δ]→ U₂) :
    (S₀ —[(κ ≫ π) ▷ P; ε + δ]→ S₂) ∧
      (T₀ —[H ◁ (σ₂ ≫ σ₁); ε]→ T₂) ∧
      (U₀ —[(κ ≫ π) ⊗ₘ (σ₂ ≫ σ₁); ε + δ]→ U₂) := by
  refine ⟨?_, ?_, ?_⟩
  · cc_calc constructs
      S₀ —[π ▷ P; ε]→ S₁ := hR₁
      _  —[κ ▷ P; δ]→ S₂ := hR₂
  · cc_calc constructs
      T₀ —[H ◁ σ₁]→ T₁ := hL₁
      _  —[H ◁ σ₂; ε]→ T₂ := hL₂
  · cc_calc constructs
      U₀ —[π ⊗ₘ σ₁; ε]→ U₁ := hT₁
      _  —[κ ⊗ₘ σ₂; δ]→ U₂ := hT₂

/-- Approximate steps directly accept `Constructs ... (epsilonRelaxation ε ...)` proofs. -/
example {A B D : C} (π₁ : B ⟶ D) (π₂ : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ : Specification (Phi B)) (R₂ : Specification (Phi A))
    {ε δ : ENNReal}
    (h₁ : R₀ —[π₁]→ epsilonRelaxation ε R₁)
    (h₂ : R₁ —[π₂]→ epsilonRelaxation δ R₂) :
    R₀ —[π₂ ≫ π₁; ε + δ]→ R₂ := by
  cc_calc constructs
    R₀ —[π₁; ε]→ R₁ := h₁
    _  —[π₂; δ]→ R₂ := h₂

end AbstractMetric

section ConcreteInterface

/-- Multi-step `ActiveUserBank` registration + outer converter chain on `Interface`, using
`cc_construct`, `cc_normalize`, and `cc_calc constructs`, alongside `cc_calc statistical`. -/
example {Registry B B' Out Outer : Interface} (registry : TypedSystem Registry)
    (filterRegistration : Out ⟶ Registry ⊗ B') (filterRows : B' ⟶ B) (α : Outer ⟶ Out)
    {idealBank R : TypedSystem B} {S : TypedSystem Out} {ε δ : ENNReal}
    (hR : R ∈ ActiveUserBank.specification idealBank filterRows ε)
    (hS : Δ (filterRegistration • (registry ∥ filterRows • idealBank)) S ≤ δ) :
    (({registry ∥ R} : Specification (TypedSystem (Registry ⊗ B)))
      —[α ≫ filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows); ε + δ]→ {α • S}) ∧
      Δ (α • (filterRegistration • (registry ∥ filterRows • R))) (α • S) ≤ ε + δ := by
  constructor
  · cc_calc constructs
      ({registry ∥ R} : Specification (TypedSystem (Registry ⊗ B)))
        —[filterRegistration ≫ (𝟙 Registry ⊗ₘ filterRows); ε]→
          {filterRegistration • (registry ∥ filterRows • idealBank)} := by
          cc_construct
          cc_normalize
          exact ActiveUserBank.registration_distance_le registry filterRegistration filterRows hR
      _ —[α; δ]→ {α • S} := by
          cc_construct
          exact (distance_attach_le α _ _).trans hS
  · cc_calc statistical
      α • (filterRegistration • (registry ∥ filterRows • R))
        ≈[ε] α • (filterRegistration • (registry ∥ filterRows • idealBank)) :=
        ActiveUserBank.registration_distance_le registry filterRegistration filterRows hR
      _ ≈[δ] α • S := hS

/-- Multi-step indifferentiability chain on `Interface`:
`Indifferentiability.constructs_of_simulator` feeds into two lifted application steps, composing
`((app₂ ≫ app₁) ▷ P) ≫ protocol` into `Indifferentiability.specification`. -/
example {H H₁ H₂ P Q B : Interface} (protocol : H ⊗ P ⟶ B)
    (app₁ : H₁ ⟶ H) (app₂ : H₂ ⟶ H₁)
    (simulators : Set (P ⟶ Q)) (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem B) (ideal : TypedSystem (H ⊗ Q))
    (mid : TypedSystem (H₁ ⊗ Q)) (target : TypedSystem (H₂ ⊗ Q))
    {ε δ₁ δ₂ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ ε)
    (hApp₁ : Δ ((app₁ ▷ Q) • ideal) mid ≤ δ₁)
    (hApp₂ : Δ ((app₂ ▷ Q) • mid) target ≤ δ₂) :
    ({real} : Specification (TypedSystem B)) —[((app₂ ≫ app₁) ▷ P) ≫ protocol]→
      Indifferentiability.specification target simulators (ε + δ₁ + δ₂) := by
  cc_calc constructs
    ({real} : Specification (TypedSystem B))
      —[protocol; ε]→ simulatorImage simulators {ideal} :=
      Indifferentiability.constructs_of_simulator simulator admitted indifferentiable
    _ —[app₁ ▷ P; δ₁]→ simulatorImage simulators {mid} :=
      ConstructsWithin.simulatorImage app₁ simulators (by cc_construct; exact hApp₁)
    _ —[app₂ ▷ P; δ₂]→ simulatorImage simulators {target} :=
      ConstructsWithin.simulatorImage app₂ simulators (by cc_construct; exact hApp₂)

end ConcreteInterface

section NegativeTests

universe u v w
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- Negative guards: missing construction steps, leading `_`, mismatched intermediates,
incomplete proofs, approximate steps on an unrelaxed exact goal, and wrong converters or budgets
must all fail cleanly without leaving open goals. -/
example {A B D : C} (π₁ : B ⟶ D) (π₂ _π₂' : A ⟶ B)
    (R₀ : Specification (Phi D)) (R₁ _R₁' : Specification (Phi B)) (R₂ : Specification (Phi A))
    {ε δ : ENNReal}
    (h₁ : R₀ —[π₁]→ R₁) (h₂ : R₁ —[π₂]→ R₂)
    (h₁a : R₀ —[π₁; ε]→ R₁) (h₂a : R₁ —[π₂; δ]→ R₂) :
    (R₀ —[π₂ ≫ π₁]→ R₂) ∧ (R₀ —[π₂ ≫ π₁; ε + δ]→ R₂) := by
  -- Equality-only block has no construction step.
  fail_if_success
    have : R₀ —[𝟙 D]→ R₀ := by
      cc_calc constructs
        R₀ = R₀ := rfl
  -- Leading `_` has no previous specification.
  fail_if_success
    have : R₀ —[π₂ ≫ π₁]→ R₂ := by
      cc_calc constructs
        _ —[π₁]→ R₁ := h₁
        _ —[π₂]→ R₂ := h₂
  -- Mismatched intermediate specification fails.
  fail_if_success
    have : R₀ —[π₂ ≫ π₁]→ R₂ := by
      cc_calc constructs
        R₀ —[π₁]→ R₁ := h₁
        _R₁' —[π₂]→ R₂ := by exact (by assumption)
  -- Incomplete tactic step (`by skip`) fails without leaving open goals.
  fail_if_success
    have : R₀ —[π₂ ≫ π₁]→ R₂ := by
      cc_calc constructs
        R₀ —[π₁]→ R₁ := by skip
        _  —[π₂]→ R₂ := h₂
  -- Approximate step cannot close an unrelaxed exact construction goal.
  fail_if_success
    have : R₀ —[π₂ ≫ π₁]→ R₂ := by
      cc_calc constructs
        R₀ —[π₁; ε]→ R₁ := h₁a
        _  —[π₂]→ R₂ := h₂
  -- Wrong converter fails.
  fail_if_success
    have : R₀ —[_π₂' ≫ π₁]→ R₂ := by
      cc_calc constructs
        R₀ —[π₁]→ R₁ := h₁
        _  —[π₂]→ R₂ := h₂
  -- Wrong scalar budget fails.
  fail_if_success
    have : R₀ —[π₂ ≫ π₁; ε]→ R₂ := by
      cc_calc constructs
        R₀ —[π₁; ε]→ R₁ := h₁a
        _  —[π₂; δ]→ R₂ := h₂a
  constructor
  · cc_calc constructs
      R₀ —[π₁]→ R₁ := h₁
      _  —[π₂]→ R₂ := h₂
  · cc_calc constructs
      R₀ —[π₁; ε]→ R₁ := h₁a
      _  —[π₂; δ]→ R₂ := h₂a

end NegativeTests

#print axioms Constructs.toConstructsWithin
#print axioms Constructs.serial_within
#print axioms ConstructsWithin.serial_exact
#print axioms Tests.ConstructionCalc.abstract_approx_chain

end Tests.ConstructionCalc

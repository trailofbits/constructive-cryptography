module

public import Commons.Definitions.Indifferentiability
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution
public import RandomSystems.Typed.DSL.Syntax
public import RandomSystems.Typed.SamplingDistance

/-!
# Tests for indifferentiability composition over `simulatorImage`

* `constructs_of_simulatorImage`, `Constructs.serial_simulatorImage`, and
  `Constructs.serial_simulatorImage_whiskerRight` instantiated on `Interface` under custom CC
  notation (`Δ`, `•`, `—[...]→`, `—[...; ...]→`).
* General `protocol : H ⊗ P ⟶ B` mixed theorem (`mixed_application_of_indifferentiability` and
  `Commons.Indifferentiability.compose_mixed`) and whiskered corollary
  `mixed_application_of_indifferentiability_whiskerRight` on `Interface` with `TypedSystem.sample`.
* Proof-command compatibility with `cc_normalize`, `cc_construct`, and `cc_calc statistical`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.IndifferentiabilityComposition

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability Commons
open scoped NNReal SystemAlgebra SystemAlgebra.DSL

/-- MR16 Lemma 5 and serial indifferentiability composition on `Interface` with unequal ports. -/
example {H H' P Q B : Interface} (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H)
    (simulators : Set (P ⟶ Q)) (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem B) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε δ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ ε)
    (idealApplication : Δ ((application ▷ Q) • ideal) target ≤ δ) :
    ({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol]→
      Indifferentiability.specification target simulators (ε + δ) :=
  Indifferentiability.compose
    (Indifferentiability.constructs_of_simulator simulator admitted indifferentiable)
    (by cc_construct; exact idealApplication)

/-- Whiskered honest-port construction composes into `(κ ≫ π) ▷ P`. -/
example {H H' H'' P Q : Interface} (π : H ⟶ H'') (κ : H' ⟶ H)
    (simulators : Set (P ⟶ Q)) (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem (H'' ⊗ P)) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε δ : ENNReal}
    (indifferentiable : Δ ((π ▷ P) • real) ((H ◁ simulator) • ideal) ≤ ε)
    (idealApplication : Δ ((κ ▷ Q) • ideal) target ≤ δ) :
    ({real} : Specification (TypedSystem (H'' ⊗ P))) —[(κ ≫ π) ▷ P]→
      Indifferentiability.specification target simulators (ε + δ) :=
  Constructs.serial_simulatorImage_whiskerRight
    (constructs_of_simulatorImage simulator admitted indifferentiable)
    (by cc_construct; exact idealApplication)

/-- General shared-primitive mixed application (`protocol : H ⊗ P ⟶ B`, e.g. `B = P`) via
`Commons.Indifferentiability.compose_mixed` and `TypedSystem.sample`. -/
example {H H' P Q : Interface} {K : Type} (law : Distribution K)
    [Distribution.IsProbability law]
    (protocol : H ⊗ P ⟶ P) (application : K → (H' ⟶ H)) (simulators : Set (P ⟶ Q))
    (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem P) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε : ℝ≥0} {δ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ (ε : ENNReal))
    (idealApplication : Δ (sample k ← law; (application k ▷ Q) • ideal) target ≤ δ) :
    (sample k ← law; ((application k ▷ P) ≫ protocol) • real) ∈
      Indifferentiability.specification target simulators ((ε : ENNReal) + δ) :=
  Indifferentiability.compose_mixed
    (TypedSystem.sample law) (TypedSystem.sample law) simulator admitted
    (fun f => TypedConverter.smul_sample (H' ◁ simulator) law f)
    (fun a b hab => by
      simpa only [Interface.cc_distance_eq] using
        TypedSystem.transcriptDistance_sample_le law a b ε hab)
    indifferentiable idealApplication

/-- Whiskered keyed application from indifferentiability on `Interface` via
`mixed_application_of_indifferentiability_whiskerRight`. -/
example {H H' H'' P Q : Interface} {K : Type} (law : Distribution K)
    [Distribution.IsProbability law]
    (π : H ⟶ H'') (κ : K → (H' ⟶ H)) (simulators : Set (P ⟶ Q))
    (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem (H'' ⊗ P)) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε : ℝ≥0} {δ : ENNReal}
    (indifferentiable : Δ ((π ▷ P) • real) ((H ◁ simulator) • ideal) ≤ (ε : ENNReal))
    (idealApplication : Δ (sample k ← law; (κ k ▷ Q) • ideal) target ≤ δ) :
    (sample k ← law; ((κ k ≫ π) ▷ P) • real) ∈
      Indifferentiability.specification target simulators ((ε : ENNReal) + δ) :=
  mixed_application_of_indifferentiability_whiskerRight
    (TypedSystem.sample law) (TypedSystem.sample law) simulator admitted
    (fun f => TypedConverter.smul_sample (H' ◁ simulator) law f)
    (fun a b hab => by
      simpa only [Interface.cc_distance_eq] using
        TypedSystem.transcriptDistance_sample_le law a b ε hab)
    indifferentiable idealApplication

/-- `cc_normalize` unfolds serial attachment and hoists retained samples under custom notation. -/
example {H H' P Q B : Interface} {K : Type} (law : Distribution K)
    [Distribution.IsProbability law]
    (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H) (simulator : P ⟶ Q)
    (real : TypedSystem B) (f : K → TypedSystem (H' ⊗ Q)) :
    ((application ▷ P) ≫ protocol) • real = (application ▷ P) • (protocol • real) ∧
      (H' ◁ simulator) • (sample k ← law; f k) = sample k ← law; (H' ◁ simulator) • f k := by
  constructor <;> cc_normalize

/-- `cc_construct` and `cc_calc statistical` work directly with indifferentiability bounds under
custom CC notation. -/
example {H H' P Q B : Interface} (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H)
    (simulator : P ⟶ Q) (real : TypedSystem B) (ideal : TypedSystem (H ⊗ Q))
    (target : TypedSystem (H' ⊗ Q)) {ε δ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ ε)
    (idealApplication : Δ ((application ▷ Q) • ideal) target ≤ δ) :
    ({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol; ε + δ]→
      {(H' ◁ simulator) • target} := by
  cc_construct
  have exchange : (application ▷ P) • ((H ◁ simulator) • ideal) =
      (H' ◁ simulator) • ((application ▷ Q) • ideal) := by
    change attach (application ▷ P) (attach (H ◁ simulator) ideal) =
      attach (H' ◁ simulator) (attach (application ▷ Q) ideal)
    simp only [← attach_serial, whisker_exchange]
  cc_calc statistical
    ((application ▷ P) ≫ protocol) • real
      = (application ▷ P) • (protocol • real) := by cc_normalize
    _ ≈[ε] (application ▷ P) • ((H ◁ simulator) • ideal) := indifferentiable
    _ = (H' ◁ simulator) • ((application ▷ Q) • ideal) := exchange
    _ ≈[δ] (H' ◁ simulator) • target := idealApplication

/-- Two-layer indifferentiability transitivity on `Interface` with unequal ports `P`, `Q`, `R`,
both into `Set.image2 (· ≫ ·) outer inner` and into an explicitly budgeted `composites` class. -/
example {H H' P Q R B : Interface} (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H)
    (outer : Set (P ⟶ Q)) (inner : Set (Q ⟶ R)) (composites : Set (P ⟶ R))
    (admitted : ∀ σ ∈ outer, ∀ τ ∈ inner, σ ≫ τ ∈ composites)
    (σ : P ⟶ Q) (hσ : σ ∈ outer) (τ : Q ⟶ R) (hτ : τ ∈ inner)
    (real : TypedSystem B) (middle : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ R))
    {ε δ : ENNReal}
    (hOuter : Δ (protocol • real) ((H ◁ σ) • middle) ≤ ε)
    (hInner : Δ ((application ▷ Q) • middle) ((H' ◁ τ) • target) ≤ δ) :
    (({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol]→
      Indifferentiability.specification target (Set.image2 (· ≫ ·) outer inner) (ε + δ)) ∧
      (({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol]→
        Indifferentiability.specification target composites (ε + δ)) := by
  have cOuter := Indifferentiability.constructs_of_simulator σ hσ hOuter
  have cInner := Indifferentiability.constructs_of_simulator τ hτ hInner
  exact ⟨Indifferentiability.trans cOuter cInner,
    Indifferentiability.trans_subset admitted cOuter cInner⟩

/-- `cc_normalize` unfolds serial composite-simulator attachment on `Interface`. -/
example {H' P Q R : Interface} (σ : P ⟶ Q) (τ : Q ⟶ R) (target : TypedSystem (H' ⊗ R)) :
    (H' ◁ (σ ≫ τ)) • target = (H' ◁ σ) • ((H' ◁ τ) • target) := by
  rw [whiskerLeft_comp]
  cc_normalize

#print axioms constructs_of_simulatorImage
#print axioms Constructs.serial_simulatorImage
#print axioms Constructs.serial_simulatorImage_whiskerRight
#print axioms Constructs.serial_simulatorImage_trans
#print axioms Constructs.serial_simulatorImage_trans_subset
#print axioms mixed_application_of_indifferentiability
#print axioms mixed_application_of_indifferentiability_whiskerRight
#print axioms Indifferentiability.constructs_of_simulator
#print axioms Indifferentiability.compose
#print axioms Indifferentiability.trans
#print axioms Indifferentiability.trans_subset
#print axioms Indifferentiability.compose_mixed

end Tests.IndifferentiabilityComposition

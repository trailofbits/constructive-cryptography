module

public import ConstructiveCryptography.CryptographicAlgebra.SimulatorComposition
public import ConstructiveCryptography.Notation.Basic

/-!
# Indifferentiability composition over right-port simulator images

Builds on `simulatorImage` (`CryptographicAlgebra.Star`) and `simulatorImage_comp`
(`CryptographicAlgebra.SimulatorComposition`) to provide MR16's simulator witness rule and
indifferentiability composition theorems [1, Lemmas 1–3 & 5, pp. 11–12]:

* `constructs_of_simulatorImage`: a concrete right-port simulator `σ ∈ simulators` with
  `Δ (protocol • real) ((H ◁ σ) • ideal) ≤ error` proves
  `{real} —[protocol]→ epsilonRelaxation error (simulatorImage simulators {ideal})`.
* `Constructs.serial_simulatorImage` and `Constructs.serial_simulatorImage_whiskerRight`:
  compose an indifferentiable realization with an application proved against the ideal resource,
  adding `indifferentiabilityError + applicationError`.
* `mixed_application_of_indifferentiability` and
  `mixed_application_of_indifferentiability_whiskerRight`: keyed or mixed application under an
  arbitrary attachment-commuting, convex mixing operation (such as `TypedSystem.sample`).

```text
{real}  ──[ protocol ]──────────▶  (simulatorImage Σ source)^ε     indifferentiability
source  ──[ κ ▷ Q ; δ ]─────────▶  target                          ideal-world application
──────────────────────────────────────────────────────────────────────────────────────────
{real}  ──[ (κ ▷ P) ≫ protocol ]▶  (simulatorImage Σ target)^(ε+δ) Lemmas 1–3 of [1]
```

## References

1. U. Maurer and R. Renner. *From Indifferentiability to Constructive Cryptography (and Back)*.
   In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016.
   Cryptology ePrint Archive, Paper 2016/903.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography.CryptographicAlgebra.Specification

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra

universe u v w s

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- **MR16, Lemma 5, for right-port simulators** [1, p. 12]: an admitted simulator witnessing
`Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ error` proves construction into the
`error`-relaxation of `simulatorImage simulators {ideal}`. -/
theorem constructs_of_simulatorImage {H P Q B : C}
    -- `protocol : H ⊗ P ⟶ B` exposes honest interface `H` and public interface `P`.
    {protocol : H ⊗ P ⟶ B} {simulators : Set (P ⟶ Q)}
    -- `real : Phi B` is the real resource and `ideal : Phi (H ⊗ Q)` the ideal one.
    {real : Phi B} {ideal : Phi (H ⊗ Q)} {error : ENNReal}
    (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (close : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ error) :
    ({real} : Specification (Phi B)) —[protocol]→
      epsilonRelaxation error
        (simulatorImage simulators ({ideal} : Specification (Phi (H ⊗ Q)))) := by
  rintro resource rfl
  refine mem_epsilonRelaxation_iff.mpr ⟨(H ◁ simulator) • ideal, ?_, close⟩
  rw [simulatorImage_eq_image2]
  exact ⟨simulator, admitted, ideal, Set.mem_singleton ideal, rfl⟩

/-- **Composition with indifferentiability** [1, Lemmas 1–3, p. 11]: composing an indifferentiable
realization `protocol` with an honest-port application `κ ▷ Q` adds their errors. -/
theorem Constructs.serial_simulatorImage {H H' P Q B : C}
    -- `protocol : H ⊗ P ⟶ B` is the indifferentiable construction and `κ : H' ⟶ H` the
    -- honest-port application.
    {protocol : H ⊗ P ⟶ B} {κ : H' ⟶ H} {simulators : Set (P ⟶ Q)}
    {real : Specification (Phi B)} {source : Specification (Phi (H ⊗ Q))}
    {target : Specification (Phi (H' ⊗ Q))}
    {indifferentiabilityError applicationError : ENNReal}
    (indifferentiable : real —[protocol]→
      Specification.epsilonRelaxation indifferentiabilityError
        (Specification.simulatorImage simulators source))
    (idealApplication : source —[κ ▷ Q; applicationError]→ target) :
    real —[(κ ▷ P) ≫ protocol]→
      Specification.epsilonRelaxation (indifferentiabilityError + applicationError)
        (Specification.simulatorImage simulators target) :=
  Constructs.serial_epsilonRelaxation indifferentiable
    (constructs_epsilonRelaxation_iff.mpr
      (ConstructsWithin.simulatorImage κ simulators idealApplication))

/-- `Constructs.serial_simulatorImage` for an honest-port construction `π ▷ P`, simplifying
`(κ ▷ P) ≫ (π ▷ P)` to `(κ ≫ π) ▷ P`. -/
theorem Constructs.serial_simulatorImage_whiskerRight {H H' H'' P Q : C}
    {π : H ⟶ H''} {κ : H' ⟶ H} {simulators : Set (P ⟶ Q)}
    {real : Specification (Phi (H'' ⊗ P))} {source : Specification (Phi (H ⊗ Q))}
    {target : Specification (Phi (H' ⊗ Q))}
    {indifferentiabilityError applicationError : ENNReal}
    (indifferentiable : real —[π ▷ P]→
      Specification.epsilonRelaxation indifferentiabilityError
        (Specification.simulatorImage simulators source))
    (idealApplication : source —[κ ▷ Q; applicationError]→ target) :
    real —[(κ ≫ π) ▷ P]→
      Specification.epsilonRelaxation (indifferentiabilityError + applicationError)
        (Specification.simulatorImage simulators target) := by
  have composite : (κ ≫ π) ▷ P = (κ ▷ P) ≫ (π ▷ P) := comp_whiskerRight κ π P
  rw [constructs_iff_of_converter_eq composite]
  exact Constructs.serial_simulatorImage indifferentiable idealApplication

/-- **Mixed or keyed application from indifferentiability**: composing a keyed family `κ k` with
an indifferentiable realization `protocol : H ⊗ P ⟶ B` under an attachment-commuting, convex
mixing operation yields `(simulatorImage simulators {target})^(ε + δ)` with one simulator
serving every key. -/
theorem mixed_application_of_indifferentiability {H H' P Q B : C} {K : Type s}
    -- `protocol : H ⊗ P ⟶ B` is any indifferentiable construction (including shared-primitive
    -- protocols with `B = P`); `κ k : H' ⟶ H` selects the honest-port application for key `k`.
    {protocol : H ⊗ P ⟶ B} {κ : K → (H' ⟶ H)} {simulators : Set (P ⟶ Q)}
    {real : Phi B} {ideal : Phi (H ⊗ Q)} {target : Phi (H' ⊗ Q)}
    {indifferentiabilityError applicationError : ENNReal}
    (mixOutside : (K → Phi (H' ⊗ P)) → Phi (H' ⊗ P))
    (mixIdeal : (K → Phi (H' ⊗ Q)) → Phi (H' ⊗ Q))
    (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (commutes : ∀ f : K → Phi (H' ⊗ Q),
      (H' ◁ simulator) • mixIdeal f = mixOutside (fun k => (H' ◁ simulator) • f k))
    (convex : ∀ a b : K → Phi (H' ⊗ P),
      (∀ k, Δ (a k) (b k) ≤ indifferentiabilityError) →
        Δ (mixOutside a) (mixOutside b) ≤ indifferentiabilityError)
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤
      indifferentiabilityError)
    (idealApplication : Δ (mixIdeal (fun k => (κ k ▷ Q) • ideal)) target ≤
      applicationError) :
    mixOutside (fun k => ((κ k ▷ P) ≫ protocol) • real) ∈
      epsilonRelaxation (indifferentiabilityError + applicationError)
        (simulatorImage simulators ({target} : Specification (Phi (H' ⊗ Q)))) := by
  refine mem_epsilonRelaxation_iff.mpr ⟨(H' ◁ simulator) • target, ?_, ?_⟩
  · rw [simulatorImage_eq_image2]
    exact ⟨simulator, admitted, target, Set.mem_singleton target, rfl⟩
  -- Split each keyed application from the underlying construction.
  have split : (fun k => ((κ k ▷ P) ≫ protocol) • real) =
      fun k => (κ k ▷ P) • (protocol • real) := by
    funext k
    exact attach_serial (κ k ▷ P) protocol real
  -- Move the simulator outside each keyed application and then outside the mixture.
  have simulated : mixOutside (fun k => (κ k ▷ P) • ((H ◁ simulator) • ideal)) =
      (H' ◁ simulator) • (mixIdeal (fun k => (κ k ▷ Q) • ideal)) := by
    rw [commutes]
    congr 1
    funext k
    change attach (κ k ▷ P) (attach (H ◁ simulator) ideal) =
      attach (H' ◁ simulator) (attach (κ k ▷ Q) ideal)
    simp only [← attach_serial, whisker_exchange]
  rw [split]
  let middle := mixOutside fun k => (κ k ▷ P) • ((H ◁ simulator) • ideal)
  refine (distance_triangle _ middle _).trans (add_le_add ?_ ?_)
  · exact convex _ _ (fun k => (distance_attach_le (κ k ▷ P) _ _).trans indifferentiable)
  · dsimp only [middle]
    rw [simulated]
    exact (distance_attach_le (H' ◁ simulator) _ _).trans idealApplication

/-- `mixed_application_of_indifferentiability` for an honest-port construction `π ▷ P`,
rewriting `(κ k ▷ P) ≫ (π ▷ P)` to `(κ k ≫ π) ▷ P`. -/
theorem mixed_application_of_indifferentiability_whiskerRight {H H' H'' P Q : C} {K : Type s}
    {π : H ⟶ H''} {κ : K → (H' ⟶ H)} {simulators : Set (P ⟶ Q)}
    {real : Phi (H'' ⊗ P)} {ideal : Phi (H ⊗ Q)} {target : Phi (H' ⊗ Q)}
    {indifferentiabilityError applicationError : ENNReal}
    (mixOutside : (K → Phi (H' ⊗ P)) → Phi (H' ⊗ P))
    (mixIdeal : (K → Phi (H' ⊗ Q)) → Phi (H' ⊗ Q))
    (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (commutes : ∀ f : K → Phi (H' ⊗ Q),
      (H' ◁ simulator) • mixIdeal f = mixOutside (fun k => (H' ◁ simulator) • f k))
    (convex : ∀ a b : K → Phi (H' ⊗ P),
      (∀ k, Δ (a k) (b k) ≤ indifferentiabilityError) →
        Δ (mixOutside a) (mixOutside b) ≤ indifferentiabilityError)
    (indifferentiable : Δ ((π ▷ P) • real) ((H ◁ simulator) • ideal) ≤
      indifferentiabilityError)
    (idealApplication : Δ (mixIdeal (fun k => (κ k ▷ Q) • ideal)) target ≤
      applicationError) :
    mixOutside (fun k => ((κ k ≫ π) ▷ P) • real) ∈
      epsilonRelaxation (indifferentiabilityError + applicationError)
        (simulatorImage simulators ({target} : Specification (Phi (H' ⊗ Q)))) := by
  simpa only [comp_whiskerRight] using
    mixed_application_of_indifferentiability mixOutside mixIdeal simulator admitted
      commutes convex indifferentiable idealApplication

end ConstructiveCryptography.CryptographicAlgebra.Specification

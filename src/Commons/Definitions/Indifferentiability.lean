module

public import ConstructiveCryptography.CryptographicAlgebra.Indifferentiability
public import ConstructiveCryptography.Notation.Basic

/-!
# Indifferentiability specification

The specification contains resources within `ε` of `(H ◁ σ) • ideal` for some admitted
`σ` [1, §§3.4, 4.2, pp. 8, 12]. `constructs_of_simulator` supplies this witness.
`compose`, `trans`, `trans_subset`, and `compose_mixed` apply the algebra's composition laws to
this specification.

## References

1. U. Maurer and R. Renner. *From Indifferentiability to Constructive Cryptography (and Back)*.
   In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016.
   Cryptology ePrint Archive, Paper 2016/903.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons.Indifferentiability

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open scoped SystemAlgebra

universe u v w s

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]

/-- **Indifferentiability specification** [1, §§3.4, 4.2, pp. 8, 12]: the `error`-relaxation of
`simulatorImage simulators {ideal}`, i.e. the resources on `H ⊗ P` within `error` of
`(H ◁ σ) • ideal` for some admitted simulator `σ ∈ simulators`. -/
noncomputable abbrev specification {H P Q : C}
    -- `ideal : Phi (H ⊗ Q)` presents honest port `H` and simulator port `Q`.
    (ideal : Phi (H ⊗ Q))
    -- `simulators : Set (P ⟶ Q)` is the admitted simulator class `Σ`.
    (simulators : Set (P ⟶ Q))
    -- `error : ENNReal` is the distinguishing budget `ε`.
    (error : ENNReal) :
    ConstructiveCryptography.Specification (Phi (H ⊗ P)) :=
  epsilonRelaxation error
    (simulatorImage simulators ({ideal} : ConstructiveCryptography.Specification (Phi (H ⊗ Q))))

/-- An admitted simulator witnessing `Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ error`
constructs `specification ideal simulators error` from `{real}` [1, Lemma 5, p. 12]. -/
lemma constructs_of_simulator {H P Q B : C} {protocol : H ⊗ P ⟶ B}
    {simulators : Set (P ⟶ Q)} {real : Phi B} {ideal : Phi (H ⊗ Q)}
    {error : ENNReal} (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (close : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ error) :
    ({real} : ConstructiveCryptography.Specification (Phi B)) —[protocol]→
      specification ideal simulators error :=
  constructs_of_simulatorImage simulator admitted close

/-- Composing an indifferentiable realization with an application `application ▷ Q` proved against
`ideal` constructs `(simulatorImage simulators target)^(ε + δ)` [1, Lemmas 1–3, p. 11]. -/
lemma compose {H H' P Q B : C} {protocol : H ⊗ P ⟶ B} {application : H' ⟶ H}
    {simulators : Set (P ⟶ Q)} {real : ConstructiveCryptography.Specification (Phi B)}
    {ideal : Phi (H ⊗ Q)} {target : ConstructiveCryptography.Specification (Phi (H' ⊗ Q))}
    {indifferentiabilityError applicationError : ENNReal}
    (indifferentiable : real —[protocol]→
      specification ideal simulators indifferentiabilityError)
    (idealApplication :
      ({ideal} : ConstructiveCryptography.Specification (Phi (H ⊗ Q)))
        —[application ▷ Q; applicationError]→ target) :
    real —[(application ▷ P) ≫ protocol]→
      epsilonRelaxation (indifferentiabilityError + applicationError)
        (simulatorImage simulators target) :=
  Constructs.serial_simulatorImage indifferentiable idealApplication

/-- **Transitivity of indifferentiability**: composing two indifferentiable constructions yields
`specification target (Set.image2 (· ≫ ·) outer inner) (outerError + innerError)`. -/
lemma trans {H H' P Q R B : C} {protocol : H ⊗ P ⟶ B} {application : H' ⟶ H}
    {outer : Set (P ⟶ Q)} {inner : Set (Q ⟶ R)}
    {real : ConstructiveCryptography.Specification (Phi B)}
    {middle : Phi (H ⊗ Q)} {target : Phi (H' ⊗ R)}
    {outerError innerError : ENNReal}
    (hOuter : real —[protocol]→ specification middle outer outerError)
    (hInner : ({middle} : ConstructiveCryptography.Specification (Phi (H ⊗ Q)))
      —[application ▷ Q]→ specification target inner innerError) :
    real —[(application ▷ P) ≫ protocol]→
      specification target (Set.image2 (· ≫ ·) outer inner) (outerError + innerError) :=
  Constructs.serial_simulatorImage_trans hOuter hInner

/-- Transitivity of indifferentiability into an explicitly budgeted composite simulator class
`composites` admitting `σ ≫ τ` for every `σ ∈ outer` and `τ ∈ inner`. -/
lemma trans_subset {H H' P Q R B : C} {protocol : H ⊗ P ⟶ B} {application : H' ⟶ H}
    {outer : Set (P ⟶ Q)} {inner : Set (Q ⟶ R)} {composites : Set (P ⟶ R)}
    {real : ConstructiveCryptography.Specification (Phi B)}
    {middle : Phi (H ⊗ Q)} {target : Phi (H' ⊗ R)}
    {outerError innerError : ENNReal}
    (admitted : ∀ σ ∈ outer, ∀ τ ∈ inner, σ ≫ τ ∈ composites)
    (hOuter : real —[protocol]→ specification middle outer outerError)
    (hInner : ({middle} : ConstructiveCryptography.Specification (Phi (H ⊗ Q)))
      —[application ▷ Q]→ specification target inner innerError) :
    real —[(application ▷ P) ≫ protocol]→
      specification target composites (outerError + innerError) :=
  Constructs.serial_simulatorImage_trans_subset admitted hOuter hInner

/-- Composing a keyed or mixed application `application k` with an arbitrary indifferentiable
realization `protocol : H ⊗ P ⟶ B` yields `specification target simulators (ε + δ)`. -/
lemma compose_mixed {H H' P Q B : C} {K : Type s}
    {protocol : H ⊗ P ⟶ B} {application : K → (H' ⟶ H)} {simulators : Set (P ⟶ Q)}
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
    (idealApplication : Δ (mixIdeal (fun k => (application k ▷ Q) • ideal)) target ≤
      applicationError) :
    mixOutside (fun k => ((application k ▷ P) ≫ protocol) • real) ∈
      specification target simulators (indifferentiabilityError + applicationError) :=
  mixed_application_of_indifferentiability mixOutside mixIdeal simulator admitted
    commutes convex indifferentiable idealApplication

end Commons.Indifferentiability

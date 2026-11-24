module

public import ConstructiveCryptography.Instances.Algebra
public import ConstructiveCryptography.Notation.Basic
public import RandomSystems.Typed.KeyGuessing

/-!
# CC distance wrappers for transcript ratios and key guessing

Restates the typed-system transcript-ratio and hidden-key guessing bounds of
`RandomSystems.Typed.KeyGuessing` in `Δ` notation for the canonical `Interface` metric, so they
plug directly into `cc_calc statistical` and CC security statements.

## Main results

* `Interface.distance_le_of_transcript_ratio`: `Δ R S ≤ ε` from an everywhere pointwise ratio
* `Interface.sample_distance_le_of_bad_keys`: `Δ ≤ ε` for a hidden uniform key off a bad-key event
* `Interface.sample_distance_le_of_key_guesses`: `Δ ≤ budget / |K|` from bounded candidate lists
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra.Interface

open Probability
open scoped NNReal SystemAlgebra

/-- An everywhere pointwise transcript ratio bounds the CC distance `Δ R S ≤ ε`. -/
lemma distance_le_of_transcript_ratio {A : Interface} (R S : TypedSystem A) (ε : ℝ≥0)
    (hratio : ∀ h, (1 - (ε : ℝ)) * S.1 h ≤ R.1 h) :
    Δ R S ≤ (ε : ENNReal) :=
  TypedSystem.distance_le_of_transcript_ratio R S ε hratio

/-- Adaptive CC distance bound `Δ ≤ ε` for a uniform hidden key agreeing with `g seed` off a
bad-key event of mass at most `ε` per seed and input history. -/
lemma sample_distance_le_of_bad_keys {A : Interface} {K Ω : Type} [Fintype K] [Nonempty K]
    (P : Distribution Ω) [Distribution.IsProbability P]
    (f : Ω → K → ∀ i, A.X i → A.Y i) (g : Ω → ∀ i, A.X i → A.Y i)
    (bad : Ω → List (Sigma A.X) → K → Prop) (ε : ℝ≥0)
    (hbad : ∀ seed xs, xs = [] ∨ A.domain xs →
      (Distribution.uniform K).mass (bad seed xs) ≤ (ε : ℝ))
    (hagree : ∀ seed k xs, ¬ bad seed xs k → ∀ x ∈ xs, f seed k x.1 x.2 = g seed x.1 x.2) :
    Δ (sample seed ← P; sample k ←$ 𝒰[K]; TypedSystem.ofFunction (f seed k))
      (sample seed ← P; TypedSystem.ofFunction (g seed)) ≤ (ε : ENNReal) :=
  TypedSystem.sample_distance_le_of_bad_keys P f g bad ε hbad hagree

/-- Adaptive CC distance bound `Δ ≤ budget / |K|` when a uniform hidden key agrees with `g seed`
outside a candidate list of length at most `budget`. -/
lemma sample_distance_le_of_key_guesses {A : Interface} {K Ω : Type} [Fintype K] [Nonempty K]
    (P : Distribution Ω) [Distribution.IsProbability P]
    (f : Ω → K → ∀ i, A.X i → A.Y i) (g : Ω → ∀ i, A.X i → A.Y i)
    (guesses : Ω → List (Sigma A.X) → List K) (budget : Nat)
    (hbudget : ∀ seed xs, xs = [] ∨ A.domain xs → (guesses seed xs).length ≤ budget)
    (hagree : ∀ seed k xs, k ∉ guesses seed xs → ∀ x ∈ xs, f seed k x.1 x.2 = g seed x.1 x.2) :
    Δ (sample seed ← P; sample k ←$ 𝒰[K]; TypedSystem.ofFunction (f seed k))
      (sample seed ← P; TypedSystem.ofFunction (g seed)) ≤
      (((budget : ℝ≥0) / Fintype.card K : ℝ≥0) : ENNReal) :=
  TypedSystem.sample_distance_le_of_key_guesses P f g guesses budget hbudget hagree

end SystemAlgebra.Interface

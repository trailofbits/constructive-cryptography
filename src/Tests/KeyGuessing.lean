module

public import ConstructiveCryptography.Instances.KeyGuessing
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution
public import Probability.Counting.Guessing
public import RandomSystems.Typed.KeyGuessing
public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.SampleLaws

/-!
# Tests for uniform guessing, retained-sample laws, and key-guessing ratios

Consumer tests and axiom audits for:

* `Probability.Counting.{uniform_mass_mem_list_le, fTransform_update_uniform}`
* `SystemAlgebra.TypedSystem.{sample_const, sample_uniform_equiv, parallel_ofFunction}`
* `SystemAlgebra.TypedSystem.{distance_le_of_transcript_ratio, transcript_ratio_chain,
  sample_ratio_of_bad_keys, sample_distance_le_of_bad_keys, sample_distance_le_of_key_guesses}`
* `SystemAlgebra.Interface.{distance_le_of_transcript_ratio, sample_distance_le_of_bad_keys,
  sample_distance_le_of_key_guesses}` and `cc_normalize` / `cc_calc statistical` compatibility
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.KeyGuessing

open Probability SystemAlgebra CategoryTheory CategoryTheory.MonoidalCategory
open scoped NNReal SystemAlgebra

/-- Repeated guesses in a list on `Fin 4` obey the list-length guessing bound. -/
example :
    (Distribution.uniform (Fin 4)).mass (fun k => k ∈ ([0, 0, 1] : List (Fin 4))) ≤
      (3 : ℝ) / (Fintype.card (Fin 4) : ℝ) := by
  simpa using Counting.uniform_mass_mem_list_le ([0, 0, 1] : List (Fin 4))

/-- Resampling one coordinate of a uniform `Bool → Bool` preserves uniformity. -/
example :
    Distribution.fTransform (fun p : (Bool → Bool) × Bool => Function.update p.1 true p.2)
      (Distribution.uniform ((Bool → Bool) × Bool)) = Distribution.uniform (Bool → Bool) :=
  Counting.fTransform_update_uniform true

/-- An ignored uniform draw leaves a fixed typed system unchanged, directly and via
`cc_normalize`. -/
example :
    let A := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1
    let R : TypedSystem A := TypedSystem.ofFunction fun _ b => !b
    (sample _k ←$ 𝒰[Bool]; R) = R := by
  intro A R
  cc_normalize

/-- `cc_normalize` drops ignored draws inside converter attachment and parallel composition. -/
example {A B C : Interface} (α : A ⟶ B) (R : TypedSystem B) (S : TypedSystem C) :
    (α ⊗ₘ 𝟙 C) • ((sample _k ←$ 𝒰[Bool]; R) ∥ (sample _j ←$ 𝒰[Unit]; S)) =
      (α • R) ∥ S := by
  cc_normalize

/-- Reparametrizing a uniform draw by swapping `false` and `true` preserves the retained-sample
system. -/
example :
    let A := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1
    let e : Bool ≃ Bool := Equiv.swap false true
    let R : Bool → TypedSystem A := fun k => TypedSystem.ofFunction fun _ b => xor k b
    (sample k ←$ 𝒰[Bool]; R k) = (sample k ←$ 𝒰[Bool]; R (e k)) :=
  TypedSystem.sample_uniform_equiv (Equiv.swap false true) _

/-- Two deterministic one-query systems side by side equal the combined `Sum.rec` function. -/
example :
    let A := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1
    let B := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 1
    (TypedSystem.ofFunction (A := A) fun _ b => !b) ∥
        (TypedSystem.ofFunction (A := B) fun _ u => u) =
      TypedSystem.ofFunction (A := Interface.tensor A B)
        (Sum.rec (fun _ b => !b) (fun _ u => u)) := by
  intro A B
  rw [Interface.cc_parallel_eq]
  exact TypedSystem.parallel_ofFunction _ _

/-- Pointwise transcript ratios telescope additively along a finite chain. -/
example {A : Interface} (S : Nat → TypedSystem A) (n : Nat) (ε : ℝ≥0)
    (hstep : ∀ d < n, ∀ h, (1 - (ε : ℝ)) * (S (d + 1)).1 h ≤ (S d).1 h)
    (h : List (Sigma A.X × Sigma A.Y)) :
    (1 - (n : ℝ) * ε) * (S n).1 h ≤ (S 0).1 h :=
  TypedSystem.transcript_ratio_chain S n ε hstep h

/-- Adaptive key-guessing bound in `Δ` notation on a `q`-query interface over `Fin 4`: querying
`k` returns `true` while every other query returns `false`, giving distance at most `q / 4` from
the constant-`false` oracle. -/
lemma keyGuess_distance_le (q : Nat) :
    let A := Interface.queryBudget Unit (fun _ => Fin 4) (fun _ => Bool) q
    Δ (sample _u ←$ 𝒰[Unit]; sample k ←$ 𝒰[Fin 4];
        TypedSystem.ofFunction (A := A) fun _ x => decide (x = k))
      (sample _u ←$ 𝒰[Unit];
        TypedSystem.ofFunction (A := A) fun _ _ => false) ≤
      (((q : ℝ≥0) / Fintype.card (Fin 4) : ℝ≥0) : ENNReal) := by
  intro A
  refine Interface.sample_distance_le_of_key_guesses (A := A) (Distribution.uniform Unit)
    (fun _ k _ x => decide (x = k)) (fun _ _ _ => false)
    (fun _ xs => xs.map Sigma.snd) q ?_ ?_
  · intro _ xs hxs
    rcases hxs with rfl | hd
    · simp
    · simpa only [List.length_map] using hd.2
  · intro _ k xs hnot x hx
    have hne : x.2 ≠ k := by
      intro he
      exact hnot (List.mem_map.mpr ⟨x, hx, he⟩)
    simp [hne]

/-- `cc_calc statistical` and `cc_normalize` compose `Interface.sample_distance_le_of_key_guesses`
with converter attachment, ignored-sample elimination, and a downstream statistical hop. -/
example (q : Nat) {Out : Interface}
    (α : Out ⟶ Interface.queryBudget Unit (fun _ => Fin 4) (fun _ => Bool) q)
    (S : TypedSystem Out) (δ : ENNReal)
    (hS : Δ (α • TypedSystem.ofFunction fun _ _ => false) S ≤ δ) :
    let A := Interface.queryBudget Unit (fun _ => Fin 4) (fun _ => Bool) q
    Δ (α • (sample k ←$ 𝒰[Fin 4]; TypedSystem.ofFunction (A := A) fun _ x => decide (x = k))) S ≤
      (((q : ℝ≥0) / Fintype.card (Fin 4) : ℝ≥0) : ENNReal) + δ := by
  intro A
  have hreal :
      α • (sample k ←$ 𝒰[Fin 4]; TypedSystem.ofFunction (A := A) fun _ x => decide (x = k)) =
      α • (sample _u ←$ 𝒰[Unit]; sample k ←$ 𝒰[Fin 4];
        TypedSystem.ofFunction (A := A) fun _ x => decide (x = k)) := by
    cc_normalize
  have hideal :
      α • (sample _u ←$ 𝒰[Unit]; TypedSystem.ofFunction (A := A) fun _ _ => false) =
      α • TypedSystem.ofFunction (A := A) fun _ _ => false := by
    cc_normalize
  cc_calc statistical
    α • (sample k ←$ 𝒰[Fin 4]; TypedSystem.ofFunction (A := A) fun _ x => decide (x = k)) =
      α • (sample _u ←$ 𝒰[Unit]; sample k ←$ 𝒰[Fin 4];
        TypedSystem.ofFunction (A := A) fun _ x => decide (x = k)) := hreal
    _ ≈[(((q : ℝ≥0) / Fintype.card (Fin 4) : ℝ≥0) : ENNReal)]
      α • (sample _u ←$ 𝒰[Unit]; TypedSystem.ofFunction (A := A) fun _ _ => false) :=
      keyGuess_distance_le q
    _ = α • TypedSystem.ofFunction (A := A) fun _ _ => false := hideal
    _ ≈[δ] S := hS

#print axioms Probability.Counting.uniform_mass_mem_list_le
#print axioms Probability.Counting.fTransform_update_uniform
#print axioms SystemAlgebra.TypedSystem.sample_const
#print axioms SystemAlgebra.TypedSystem.sample_uniform_equiv
#print axioms SystemAlgebra.TypedSystem.parallel_ofFunction
#print axioms SystemAlgebra.TypedSystem.distance_le_of_transcript_ratio
#print axioms SystemAlgebra.TypedSystem.transcript_ratio_chain
#print axioms SystemAlgebra.TypedSystem.sample_ratio_of_bad_keys
#print axioms SystemAlgebra.TypedSystem.sample_distance_le_of_bad_keys
#print axioms SystemAlgebra.TypedSystem.sample_distance_le_of_key_guesses
#print axioms SystemAlgebra.Interface.distance_le_of_transcript_ratio
#print axioms SystemAlgebra.Interface.sample_distance_le_of_bad_keys
#print axioms SystemAlgebra.Interface.sample_distance_le_of_key_guesses

end Tests.KeyGuessing

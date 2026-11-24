module

public import Probability.Counting.Guessing
public import RandomSystems.Distance.HCoefficient
public import RandomSystems.Typed.Functional

/-!
# Transcript ratios and hidden-key guessing on typed systems

Fix an ideal seed `seed : Ω` and a transcript `h`. When a uniform hidden key `k ←$ K` agrees
with the ideal function outside a small exceptional-key event per seed and input history,
averaging over the seed yields a pointwise transcript ratio (`sample_ratio_of_bad_keys`),
which the H-coefficient theorem turns into an adaptive `transcriptDistance` bound
(`distance_le_of_transcript_ratio`, `sample_distance_le_of_bad_keys`,
`sample_distance_le_of_key_guesses`). Pointwise ratios compose additively along finite chains
(`transcript_ratio_chain`).

## Main results

* `distance_le_of_transcript_ratio`: an everywhere ratio `(1 - ε) * S h ≤ R h` bounds
  `R.1.transcriptDistance S.1 ≤ ε`
* `transcript_ratio_chain`: pointwise ratios telescope with additive error `length * ε`
* `sample_ratio_of_bad_keys`: pointwise ratio for a hidden uniform key off a small bad-key event
* `sample_distance_le_of_bad_keys`, `sample_distance_le_of_key_guesses`: adaptive
  `transcriptDistance` bounds for hidden-key guessing
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra.TypedSystem

open Probability
open scoped NNReal SystemAlgebra

/-- An everywhere pointwise transcript ratio bounds the adaptive transcript distance via the
H-coefficient theorem (`RandomSystem.transcriptDistance_le_add_of_ratio_on_good`) with empty
bad-transcript set. -/
lemma distance_le_of_transcript_ratio {A : Interface} (R S : TypedSystem A) (ε : ℝ≥0)
    (hratio : ∀ h, (1 - (ε : ℝ)) * S.1 h ≤ R.1 h) :
    R.1.transcriptDistance S.1 ≤ (ε : ENNReal) := by
  have bound := RandomSystem.transcriptDistance_le_add_of_ratio_on_good R.2 S.2
    (Bad := fun _ => False) (ε₁ := ε) (ε₂ := 0)
    (fun h _ => hratio h)
    (fun _ _ _ _ => le_of_eq (Distribution.mass_eq_zero_of_forall_not _ fun _ h => h))
  simpa only [ENNReal.coe_zero, add_zero] using bound

/-- Pointwise transcript ratios compose along a finite chain with additive error, including when
`length * ε ≥ 1`. -/
lemma transcript_ratio_chain {A : Interface} (S : Nat → TypedSystem A) (length : Nat) (ε : ℝ≥0)
    (hstep : ∀ d < length, ∀ h, (1 - (ε : ℝ)) * (S (d + 1)).1 h ≤ (S d).1 h)
    (h : List (Sigma A.X × Sigma A.Y)) :
    (1 - (length : ℝ) * ε) * (S length).1 h ≤ (S 0).1 h := by
  have he : 0 ≤ (ε : ℝ) := ε.coe_nonneg
  have step (n : Nat) (hn : n ≤ length) :
      (1 - (n : ℝ) * ε) * (S n).1 h ≤ (S 0).1 h := by
    induction n with
    | zero => simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, le_refl]
    | succ n ih =>
      by_cases hnε : (n + 1 : Nat) * (ε : ℝ) ≤ 1
      · have hnε' : 0 ≤ 1 - (n : ℝ) * ε := by
          simp only [Nat.cast_add, Nat.cast_one] at hnε
          nlinarith
        have hm := mul_le_mul_of_nonneg_left (hstep n hn h) hnε'
        have hp : 1 - (n + 1 : Nat) * (ε : ℝ) ≤ (1 - (n : ℝ) * ε) * (1 - ε) := by
          simp only [Nat.cast_add, Nat.cast_one]
          nlinarith [sq_nonneg (ε : ℝ), Nat.cast_nonneg (α := ℝ) n]
        calc
          _ ≤ ((1 - (n : ℝ) * ε) * (1 - ε)) * (S (n + 1)).1 h :=
            mul_le_mul_of_nonneg_right hp (RandomSystem.mass_nonneg _ _)
          _ ≤ (1 - (n : ℝ) * ε) * (S n).1 h := by simpa only [mul_assoc] using hm
          _ ≤ _ := ih (Nat.le_of_succ_le hn)
      · exact (mul_nonpos_of_nonpos_of_nonneg (by linarith)
          (RandomSystem.mass_nonneg _ _)).trans (RandomSystem.mass_nonneg _ _)
  exact step length le_rfl

/-- A uniform hidden key agreeing with the ideal function `g seed` outside a bad-key event of
probability at most `ε` per seed and input history yields a pointwise transcript ratio. -/
lemma sample_ratio_of_bad_keys {A : Interface} {K Ω : Type} [Fintype K] [Nonempty K]
    (P : Distribution Ω) [Distribution.IsProbability P]
    (f : Ω → K → ∀ i, A.X i → A.Y i) (g : Ω → ∀ i, A.X i → A.Y i)
    (bad : Ω → List (Sigma A.X) → K → Prop) (ε : ℝ≥0)
    (hbad : ∀ seed xs, xs = [] ∨ A.domain xs →
      (Distribution.uniform K).mass (bad seed xs) ≤ (ε : ℝ))
    (hagree : ∀ seed k xs, ¬ bad seed xs k → ∀ x ∈ xs, f seed k x.1 x.2 = g seed x.1 x.2)
    (h : List (Sigma A.X × Sigma A.Y)) :
    (1 - (ε : ℝ)) * (sample seed ← P; ofFunction (g seed)).1 h ≤
      (sample seed ← P; sample k ←$ 𝒰[K]; ofFunction (f seed k)).1 h := by
  classical
  let realAt (seed : Ω) := sample k ←$ 𝒰[K]; ofFunction (f seed k)
  let idealAt (seed : Ω) := ofFunction (g seed)
  -- For a fixed ideal seed and transcript, every good key reproduces all transcript replies.
  have local_ratio (seed : Ω) :
      (1 - (ε : ℝ)) * (idealAt seed).1 h ≤ (realAt seed).1 h := by
    rw [ofFunction_mass]
    split_ifs with hh
    · rw [mul_one, sample_ofFunction_mass_eq]
      have hd : h.map Prod.fst = [] ∨ A.domain (h.map Prod.fst) := by
        rcases hh.1 with he | hd
        · exact Or.inl (he ▸ rfl)
        · exact Or.inr hd
      let B := bad seed (h.map Prod.fst)
      have hb : (Distribution.uniform K).mass B ≤ (ε : ℝ) := hbad seed _ hd
      have hg : 1 - (ε : ℝ) ≤ (Distribution.uniform K).mass (fun k => ¬ B k) := by
        have he := Distribution.mass_add_compl (Distribution.uniform K) B
        rw [Distribution.weight_uniform] at he
        linarith
      refine hg.trans (Distribution.mass_mono Distribution.uniform_nonNeg ?_)
      intro k hk
      refine ⟨hh.1, fun z hz => ?_⟩
      rw [hagree seed k _ hk z.1 (List.mem_map.mpr ⟨z, hz, rfl⟩)]
      exact hh.2 z hz
    · rw [mul_zero]
      exact RandomSystem.mass_nonneg _ _
  -- Average the pointwise ratio over the seed law without resampling.
  change (1 - (ε : ℝ)) * (sample seed ← P; idealAt seed).1 h ≤ _
  rw [sample_mass, Finset.mul_sum]
  change _ ≤ ∑ seed ∈ P.support, P seed * (realAt seed).1 h
  apply Finset.sum_le_sum
  intro seed _
  rw [← mul_assoc, mul_comm (1 - (ε : ℝ)), mul_assoc]
  exact mul_le_mul_of_nonneg_left (local_ratio seed) (Distribution.IsProbability.nonNeg seed)

/-- Adaptive transcript-distance bound for a uniform hidden key agreeing with `g seed` off a
bad-key event of mass at most `ε` per seed and input history. -/
lemma sample_distance_le_of_bad_keys {A : Interface} {K Ω : Type} [Fintype K] [Nonempty K]
    (P : Distribution Ω) [Distribution.IsProbability P]
    (f : Ω → K → ∀ i, A.X i → A.Y i) (g : Ω → ∀ i, A.X i → A.Y i)
    (bad : Ω → List (Sigma A.X) → K → Prop) (ε : ℝ≥0)
    (hbad : ∀ seed xs, xs = [] ∨ A.domain xs →
      (Distribution.uniform K).mass (bad seed xs) ≤ (ε : ℝ))
    (hagree : ∀ seed k xs, ¬ bad seed xs k → ∀ x ∈ xs, f seed k x.1 x.2 = g seed x.1 x.2) :
    (sample seed ← P; sample k ←$ 𝒰[K]; ofFunction (f seed k)).1.transcriptDistance
      (sample seed ← P; ofFunction (g seed)).1 ≤ (ε : ENNReal) :=
  distance_le_of_transcript_ratio _ _ ε (sample_ratio_of_bad_keys P f g bad ε hbad hagree)

/-- Adaptive transcript-distance bound `budget / |K|` when a uniform hidden key agrees with
`g seed` outside a candidate list of length at most `budget`. -/
lemma sample_distance_le_of_key_guesses {A : Interface} {K Ω : Type} [Fintype K] [Nonempty K]
    (P : Distribution Ω) [Distribution.IsProbability P]
    (f : Ω → K → ∀ i, A.X i → A.Y i) (g : Ω → ∀ i, A.X i → A.Y i)
    (guesses : Ω → List (Sigma A.X) → List K) (budget : Nat)
    (hbudget : ∀ seed xs, xs = [] ∨ A.domain xs → (guesses seed xs).length ≤ budget)
    (hagree : ∀ seed k xs, k ∉ guesses seed xs → ∀ x ∈ xs, f seed k x.1 x.2 = g seed x.1 x.2) :
    (sample seed ← P; sample k ←$ 𝒰[K]; ofFunction (f seed k)).1.transcriptDistance
      (sample seed ← P; ofFunction (g seed)).1 ≤
        (((budget : ℝ≥0) / Fintype.card K : ℝ≥0) : ENNReal) := by
  apply sample_distance_le_of_bad_keys P f g (fun seed xs k => k ∈ guesses seed xs)
    ((budget : ℝ≥0) / Fintype.card K) _ hagree
  intro seed xs hd
  refine (Counting.uniform_mass_mem_list_le _).trans ?_
  change _ ≤ (budget : ℝ) / Fintype.card K
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hbudget seed xs hd)) (by positivity)

end SystemAlgebra.TypedSystem

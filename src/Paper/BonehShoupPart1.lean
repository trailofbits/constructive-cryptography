import Informalization
import Tests.Informalization.BonehShoupPart1

/-!
# Boneh–Shoup Part 1 — Pure Paper Register (Register A: Game-Based)

Paper-centric formalization and informalization of Benchmarks B7 & B8:
- Theorem 2.2: Perfect Security of the One-Time Pad (B7)
- Theorem 3.2: Parallel Composition of PRGs (B8)
- Theorem 3.3: Sequential Composition of PRGs (B8)
- Theorem 3.11: Statistical Distance Bounds Distinguishing Advantage (B7)
- Theorem 4.7: The Difference Lemma (B7)
-/

open Probability Probability.Distribution Tests.Informalization.BonehShoupPart1
open scoped VerboseCC Probability.CryptoNotation

namespace Paper.BonehShoupPart1

paper_register_ns Paper.BonehShoupPart1 gameBased

-- Clean finite interval `{1, ..., n}` notation so sums never print `Icc(1, n)`
@[math_notation "\\{1, \\dots, #1\\}"]
def oneTo (n : ℕ) : Finset ℕ := Finset.Icc 1 n

-- Clean Paper-register adversary descriptions (eliminating "against outputs in {R}")
paper_describe_for Tests.Informalization.BonehShoupPart1.PRGAdversary
  "PRG adversary" (plural := "PRG adversaries") (carrier := false) (varStyle := .mathcal)

paper_describe_for Tests.Informalization.BonehShoupPart1.DistAdversary
  "distinguishing adversary" (plural := "distinguishing adversaries") (carrier := false) (varStyle := .mathcal)

/-- Type-level elementary wrapper around `A` realizing reduction `target`, rendering cleanly as
    `an elementary wrapper B around A`. -/
@[paper_describe "elementary wrapper" (plural := "elementary wrappers") (carrier := false) (varStyle := .mathcal) (qualifier := "around {A}")]
structure ElementaryWrapper {Out Challenge : Type}
    (A : PRGAdversary Out) (target : PRGAdversary Challenge) where
  adv : PRGAdversary Challenge
  is_reduction : adv = target

@[math_notation "#1"]
def ElementaryWrapper.toAdv {Out Challenge : Type}
    {A : PRGAdversary Out} {target : PRGAdversary Challenge}
    (B : ElementaryWrapper A target) : PRGAdversary Challenge :=
  B.adv

-- ============================================================================
-- Shared private distribution helpers
-- ============================================================================

private lemma uniform_prob_apply {A : Type} [Fintype A] [Nonempty A] (a : A) :
    ((𝒰[A] : Distribution A) a) = 1 / (Fintype.card A : ℝ) :=
  Probability.Distribution.uniform_apply a

private lemma uniform_prob_weight {A : Type} [Fintype A] [Nonempty A] :
    (𝒰[A] : Distribution A).weight = 1 :=
  Probability.Distribution.weight_uniform

private lemma sampleBind_apply {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (K : A → ProbDist B) (b : B) :
    ((sampleBind P K : Distribution B) b) =
      ∑ a : A, ((P : Distribution A) a) * ((K a : Distribution B) b) := by
  classical
  change (Finsupp.onFinset Finset.univ
    (fun b => ∑ a : A, (P : Distribution A) a * (K a : Distribution B) b)
    (fun _ _ => Finset.mem_univ _)) b = _
  rw [Finsupp.onFinset_apply]

private lemma pairDist_apply {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (Q : ProbDist B) (ab : A × B) :
    ((pairDist P Q : Distribution (A × B)) ab) =
      ((P : Distribution A) ab.1) * ((Q : Distribution B) ab.2) := by
  classical
  change (Finsupp.onFinset Finset.univ
    (fun ab : A × B => (P : Distribution A) ab.1 * (Q : Distribution B) ab.2)
    (fun _ _ => Finset.mem_univ _)) ab = _
  rw [Finsupp.onFinset_apply]

private lemma expectOf_pushDist {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (g : A → B) (f : B → ℝ) :
    expectOf (pushDist P g) f = expectOf P (fun a => f (g a)) := by
  classical
  unfold expectOf pushDist
  exact Probability.Distribution.expect_fTransform (P : Distribution A) g f

private lemma expectOf_vecDist_eq {n : ℕ} {R : Type} [Fintype R]
    (μ : Fin n → ProbDist R) (f : (Fin n → R) → ℝ) :
    expectOf (vecDist μ) f =
      ∑ v : Fin n → R, (∏ i : Fin n, ((μ i : Distribution R) (v i))) * f v := by
  classical
  unfold expectOf vecDist
  rw [Probability.Distribution.expect_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  dsimp only
  simp [Finsupp.onFinset_apply]

private lemma vecDist_uniform_eq {n : ℕ} {A : Type} [Fintype A] [Nonempty A] :
    (fun v : Fin n → A => ∏ _i : Fin n, ((𝒰[A] : Distribution A) (v _i))) =
      fun v => (𝒰[Fin n → A] : Distribution (Fin n → A)) v := by
  funext v
  simp_rw [uniform_prob_apply]
  rw [Fintype.card_fun, Fintype.card_fin, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [one_div_pow, Nat.cast_pow]

-- ============================================================================
-- Section 2.1: Perfect Security of the One-Time Pad (Theorem 2.2)
-- ============================================================================

namespace OneTimePad

/-- Length-indexed one-time pad cipher, removing the dummy `E = E_{OTP}` hypothesis. -/
@[math_notation "\\mathcal{E}_{\\mathrm{OTP}}^{(#1)}"]
noncomputable def otpScheme (L : ℕ) :
    ShannonCipher (BitString L) (BitString L) (BitString L) :=
  oneTimePad L

/-- Key-fiber cardinality in native OTP notation (`#{k ∈ {0,1}^L : k ⊕ m = c}`). -/
@[math_notation "\\#\\{k \\in \\{0,1\\}^{#1} : k \\oplus #2 = #3\\}"]
noncomputable def otpFiberCount (L : ℕ) (m c : BitString L) : ℕ :=
  keyFiberCount (oneTimePad L) m c

/-- Encryption distribution mass `Pr[E_{OTP}(k, m) = c]` under uniform `k ← {0,1}^L`. -/
@[math_notation "\\Pr\\!\\left[\\mathcal{E}_{\\mathrm{OTP}}^{(#1)}(k, #2) = #3\\right]"]
noncomputable def otpCipherProb (L : ℕ) (m c : BitString L) : ℝ :=
  probOf (cipherDist (oneTimePad L) m) (fun y => y = c)

/-- Uniform bitstring probability `2^{-L}`. -/
@[math_notation "2^{-#1}"]
noncomputable def twoPowNeg (L : ℕ) : ℝ :=
  (1 : ℝ) / ((2 ^ L : ℕ) : ℝ)

private lemma otp_fiber_eq_one (L : ℕ) (m c : BitString L) :
    otpFiberCount L m c = 1 := by
  classical
  unfold otpFiberCount keyFiberCount oneTimePad
  simp only [Finset.card_eq_one]
  refine ⟨xorBits m c, ?_⟩
  ext k
  simp [xorBits_eq_iff]

private lemma otp_cipher_prob_eq (L : ℕ) (m c : BitString L) :
    otpCipherProb L m c = twoPowNeg L := by
  classical
  unfold otpCipherProb twoPowNeg cipherDist oneTimePad probOf pushDist
  dsimp
  rw [Probability.Distribution.mass_fTransform]
  rw [Probability.Distribution.mass_congr (𝒰[BitString L] : Distribution (BitString L))
    (fun k => xorBits_eq_iff k m c)]
  rw [Probability.Distribution.mass_singleton]
  rw [uniform_prob_apply]
  have hcard : Fintype.card (BitString L) = 2 ^ L := by
    simp [BitString]
  rw [hcard]

theorem theorem2_2_otp_perfect_security (L : ℕ) :
    PerfectlySecure (otpScheme L) := by
  We note hKey : ∀ (m c k : BitString L), xorBits k m = c ↔ k = xorBits m c by
    by_leaf "Since $(k \\oplus m) \\oplus m = k$, solving $k \\oplus m = c$ yields the unique key $k = m \\oplus c$." {
      exact fun m c k => xorBits_eq_iff k m c
    }
  We note hProb : ∀ (m c : BitString L), otpCipherProb L m c = twoPowNeg L by
    by_leaf "Since $k$ is chosen uniformly from $\\{0,1\\}^L$, the unique key $k = m \\oplus c$ occurs with probability $2^{-L}$." {
      exact fun m c => otp_cipher_prob_eq L m c
    }
  by_leaf "Since every ciphertext $c \\in \\{0,1\\}^L$ occurs with identical probability $2^{-L}$ independent of the plaintext $m$, the cipher $\\mathcal{E}_{\\mathrm{OTP}}^{(L)}$ is perfectly secure." {
    exact theorem2_1_perfect_security_of_const_fiber (otpScheme L)
      (fun c => ⟨1, fun m => otp_fiber_eq_one L m c⟩)
  }

informal_title theorem2_2_otp_perfect_security
  "Perfect Security of the One-Time Pad"

paper_setting_ns Paper.BonehShoupPart1.OneTimePad
  "Let $\\mathcal{E}_{\\mathrm{OTP}} = (E, D)$ be the one-time pad over $\\{0,1\\}^L$, where a key $k \\leftarrow \\{0,1\\}^L$ is chosen uniformly at random and encryption sets $c = k \\oplus m$."
  (anchor := Paper.BonehShoupPart1.OneTimePad.theorem2_2_otp_perfect_security)
  (title := "Section 2.1 — Perfect Security of the One-Time Pad")
  (register := gameBased)

paper_motivation Paper.BonehShoupPart1.OneTimePad.theorem2_2_otp_perfect_security
  "Every $(m, c) \\in \\{0,1\\}^L \\times \\{0,1\\}^L$ is linked by a unique key $k = m \\oplus c$, so every ciphertext occurs with probability $2^{-L}$ independent of $m$."

informal_section_prelude Paper.BonehShoupPart1.OneTimePad.theorem2_2_otp_perfect_security
  "construction" "Definition 2.1 & Construction 2.1" "One-Time Pad"
  "A Shannon cipher $\\mathcal{E} = (E, D)$ over $(\\mathcal{K}, \\mathcal{M}, \\mathcal{C})$ is *perfectly secure* if for all $m_0, m_1 \\in \\mathcal{M}$, the distributions $E(k, m_0)$ and $E(k, m_1)$ (for $k \\leftarrow \\mathcal{K}$) are identical.\n> Construction 2.1 ($\\mathcal{E}_{\\mathrm{OTP}}$): take $\\mathcal{K} = \\mathcal{M} = \\mathcal{C} = \\{0,1\\}^L$ with $E(k, m) := k \\oplus m$ and $D(k, c) := k \\oplus c$."

end OneTimePad

-- ============================================================================
-- Section 3.4.1: Parallel Composition of PRGs (Theorem 3.2)
-- ============================================================================

namespace ParallelPRG

/-- 1-based parallel hybrid coordinate distribution: first `j` blocks (`1..j`) from `G`,
    remaining `n - j` blocks (`j+1..n`) uniform in `R`. -/
noncomputable def parHybridCoord {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (G : S → R) (j : ℕ) (i : Fin n) : ProbDist R :=
  if i.val < j then pushDist 𝒰[S] G else 𝒰[R]

/-- 1-based parallel hybrid output distribution `H_j`. -/
noncomputable def parHybridDist {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    (G : S → R) (n j : ℕ) : ProbDist (VecSpace n R) :=
  vecDist (fun i => parHybridCoord G j i)

/-- Acceptance probability `p_j = Pr[A(H_j) = 1]`. -/
@[math_notation "p_{#3}"]
noncomputable def parHybridProb {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) (j : ℕ) : ℝ :=
  expectOf (parHybridDist G n j) (fun vec => (A.run vec) true)

/-- Splice helper in 1-based ordering: `i = 1..ω-1` from `G(s_i)`, `i = ω` set to `r`,
    `i = ω+1..n` uniform `r_i`. -/
def parSplice {S R : Type} (G : S → R) (n : ℕ) (ω : Fin n) (r : R)
    (sVec : Fin n → S) (rVec : Fin n → R) : VecSpace n R :=
  fun i => if i.val < ω.val then G (sVec i) else if i = ω then r else rVec i

/-- 1-based parallel composition reduction `B`. -/
@[math_notation "\\mathrm{Red}_{\\mathrm{par}}\\!\\left(#1, #2\\right)"]
noncomputable def parReduction {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) (hn : n ≥ 1) : PRGAdversary R :=
  letI : NeZero n := ⟨by omega⟩
  { run := fun r =>
      sampleBind 𝒰[Fin n] fun ω =>
        sampleBind (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) fun sr =>
          A.run (parSplice G n ω r sr.1 sr.2) }

private lemma parHybridProb_zero {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) :
    parHybridProb A G 0 = prgExp1 A := by
  classical
  unfold parHybridProb parHybridDist parHybridCoord prgExp1
  rw [expectOf_vecDist_eq]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h := congrFun (vecDist_uniform_eq (n := n) (A := R)) v
  rw [h]

private lemma parHybridProb_n {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) :
    parHybridProb A G n = prgExp0 A (parallelPRG G n) := by
  classical
  unfold parHybridProb parHybridDist parHybridCoord prgExp0 parallelPRG
  rw [expectOf_vecDist_eq]
  have hlt : ∀ i : Fin n, i.val < n := fun i => i.isLt
  simp only [hlt, ↓reduceIte]
  have hpush : ∀ v : Fin n → R,
      (∏ i : Fin n, ((pushDist 𝒰[S] G : Distribution R) (v i))) =
        ∑ s : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) s) *
          if (fun i => G (s i)) = v then 1 else 0 := by
    intro v
    have hcoord : ∀ i : Fin n,
        ((pushDist 𝒰[S] G : Distribution R) (v i)) =
          ∑ si : S, ((𝒰[S] : Distribution S) si) * (if G si = v i then (1 : ℝ) else 0) := by
      intro i
      unfold pushDist
      rw [← Probability.Distribution.mass_singleton _ (v i)]
      rw [Probability.Distribution.mass_fTransform]
      rw [Probability.Distribution.mass_eq_sum]
      refine Finset.sum_congr rfl fun si _ => ?_
      split_ifs <;> ring
    simp_rw [hcoord]
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    · exact congrFun (vecDist_uniform_eq (n := n) (A := S)) s
    · split_ifs with h
      · subst h
        simp
      · have hne : ∃ i : Fin n, G (s i) ≠ v i := by
          by_contra hall
          push Not at hall
          exact h (funext hall)
        rcases hne with ⟨i0, hi0⟩
        exact Finset.prod_eq_zero (Finset.mem_univ i0) (by simp [hi0])
  simp_rw [hpush, Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (fun i => G (s i))]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · intro hmem
    exact False.elim (hmem (Finset.mem_univ _))

private lemma expectOf_parSplice_dist {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R)
    (ω : Fin n) (Q : ProbDist R) :
    expectOf Q (fun r =>
      expectOf (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) (fun sr =>
        ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true))) =
      expectOf (vecDist fun i : Fin n =>
        if i.val < ω.val then pushDist 𝒰[S] G else if i = ω then Q else 𝒰[R])
        (fun v => ((A.run v : Distribution Bool) true)) := by
  classical
  rw [expectOf_vecDist_eq]
  unfold expectOf
  simp_rw [Probability.Distribution.expect_eq_sum, pairDist_apply]
  have hLHS :
      (∑ r : R, ((Q : Distribution R) r) *
        ∑ sr : (Fin n → S) × (Fin n → R),
          (((𝒰[Fin n → S] : Distribution (Fin n → S)) sr.1) *
           ((𝒰[Fin n → R] : Distribution (Fin n → R)) sr.2)) *
          ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true)) =
      ∑ v : Fin n → R,
        (∑ r : R, ((Q : Distribution R) r) *
          ∑ sVec : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ∑ rVec : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0)) *
          ((A.run v : Distribution Bool) true) := by
    have hsplit : ∀ (r : R) (sVec : Fin n → S) (rVec : Fin n → R),
        ((A.run (parSplice G n ω r sVec rVec) : Distribution Bool) true) =
          ∑ v : Fin n → R,
            (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
              ((A.run v : Distribution Bool) true) := by
      intro r sVec rVec
      rw [Finset.sum_eq_single (parSplice G n ω r sVec rVec)]
      · simp
      · intro v _ hv
        simp [Ne.symm hv]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    simp_rw [Fintype.sum_prod_type]
    have hsplitProd :
        (∑ r : R, ((Q : Distribution R) r) *
          ∑ sVec : Fin n → S, ∑ rVec : Fin n → R,
            ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            ((A.run (parSplice G n ω r sVec rVec) : Distribution Bool) true)) =
        ∑ r : R, ((Q : Distribution R) r) *
          ∑ sVec : Fin n → S, ∑ rVec : Fin n → R,
            ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            ∑ v : Fin n → R,
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
                ((A.run v : Distribution Bool) true) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun sVec _ => Finset.sum_congr rfl fun rVec _ => ?_
      rw [hsplit r sVec rVec]
    have hpushIn :
        (∑ r : R, ((Q : Distribution R) r) *
          ∑ sVec : Fin n → S, ∑ rVec : Fin n → R,
            ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            ∑ v : Fin n → R,
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
                ((A.run v : Distribution Bool) true)) =
        ∑ r : R, ∑ sVec : Fin n → S, ∑ rVec : Fin n → R, ∑ v : Fin n → R,
          ((Q : Distribution R) r) *
            ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
            ((A.run v : Distribution Bool) true) := by
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun sVec _ =>
        Finset.sum_congr rfl fun rVec _ => Finset.sum_congr rfl fun v _ => by ring
    have hRHS_expand :
        (∑ v : Fin n → R,
          (∑ r : R, ((Q : Distribution R) r) *
            ∑ sVec : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
              ∑ rVec : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
                (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0)) *
            ((A.run v : Distribution Bool) true)) =
        ∑ v : Fin n → R, ∑ r : R, ∑ sVec : Fin n → S, ∑ rVec : Fin n → R,
          ((Q : Distribution R) r) *
            ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
            ((A.run v : Distribution Bool) true) := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      simp_rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun sVec _ => Finset.sum_congr rfl fun rVec _ => by ring
    rw [hsplitProd, hpushIn, hRHS_expand]
    calc (∑ r : R, ∑ sVec : Fin n → S, ∑ rVec : Fin n → R, ∑ v : Fin n → R,
            ((Q : Distribution R) r) *
              ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
              ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
              ((A.run v : Distribution Bool) true))
        = ∑ r : R, ∑ sVec : Fin n → S, ∑ v : Fin n → R, ∑ rVec : Fin n → R,
            ((Q : Distribution R) r) *
              ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
              ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
              ((A.run v : Distribution Bool) true) := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ r : R, ∑ v : Fin n → R, ∑ sVec : Fin n → S, ∑ rVec : Fin n → R,
            ((Q : Distribution R) r) *
              ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
              ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
              (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) *
              ((A.run v : Distribution Bool) true) := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hLHS]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  have hind : ∀ (r : R) (sVec : Fin n → S) (rVec : Fin n → R),
      (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0) =
        (if r = v ω then (1 : ℝ) else 0) *
        (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
        (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1) := by
    intro r sVec rVec
    by_cases heq : parSplice G n ω r sVec rVec = v
    · simp only [heq, ↓reduceIte]
      have hω : r = v ω := by
        have := congrFun heq ω
        simpa [parSplice] using this
      have h1 : ∀ i : Fin n, i.val < ω.val → G (sVec i) = v i := by
        intro i hi
        have := congrFun heq i
        simpa [parSplice, hi] using this
      have h2 : ∀ i : Fin n, ω.val < i.val → rVec i = v i := by
        intro i hi
        have hlt : ¬ i.val < ω.val := by omega
        have hne : i ≠ ω := Fin.ne_of_gt hi
        have := congrFun heq i
        simpa [parSplice, hlt, hne] using this
      simp only [hω, ↓reduceIte, one_mul]
      rw [Finset.prod_eq_one (fun i _ => by
        by_cases hi : i.val < ω.val
        · simp [hi, h1 i hi]
        · simp [hi])]
      rw [Finset.prod_eq_one (fun i _ => by
        by_cases hi : ω.val < i.val
        · simp [hi, h2 i hi]
        · simp [hi])]
      ring
    · simp only [heq, ↓reduceIte]
      have hne : ∃ i : Fin n, parSplice G n ω r sVec rVec i ≠ v i := by
        by_contra hall
        push Not at hall
        exact heq (funext hall)
      rcases hne with ⟨i0, hi0⟩
      by_cases h1 : i0.val < ω.val
      · have hG : G (sVec i0) ≠ v i0 := by simpa [parSplice, h1] using hi0
        have hp : (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i0) (by simp [h1, hG])
        rw [hp]; ring
      · by_cases h2 : i0 = ω
        · subst h2
          have hr : r ≠ v i0 := by simpa [parSplice] using hi0
          simp [hr]
        · have hgt : ω.val < i0.val := by
            have := Fin.val_ne_of_ne h2
            omega
          have hr : rVec i0 ≠ v i0 := by simpa [parSplice, h1, h2] using hi0
          have hp : (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i0) (by simp [hgt, hr])
          rw [hp]; ring
  have hrSum : ∀ (r : R) (sVec : Fin n → S),
      (∑ rVec : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
        (if parSplice G n ω r sVec rVec = v then (1 : ℝ) else 0)) =
      (if r = v ω then (1 : ℝ) else 0) *
      (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
      (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1) := by
    intro r sVec
    simp_rw [hind r sVec]
    have hpull :
        ∑ rVec : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
          ((if r = v ω then (1 : ℝ) else 0) *
           (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
           (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1)) =
        (if r = v ω then (1 : ℝ) else 0) *
        (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
        ∑ rVec : Fin n → R,
          (∏ i : Fin n, ((𝒰[R] : Distribution R) (rVec i)) *
            (if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1)) := by
      calc ∑ rVec : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) rVec) *
            ((if r = v ω then (1 : ℝ) else 0) *
             (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
             (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1))
          = ∑ rVec : Fin n → R,
              ((if r = v ω then (1 : ℝ) else 0) *
               (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) *
              ((∏ i : Fin n, ((𝒰[R] : Distribution R) (rVec i))) *
               (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1)) := by
            refine Finset.sum_congr rfl fun rVec _ => ?_
            rw [← congrFun (vecDist_uniform_eq (n := n) (A := R)) rVec]; ring
        _ = ((if r = v ω then (1 : ℝ) else 0) *
             (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) *
            ∑ rVec : Fin n → R,
              ((∏ i : Fin n, ((𝒰[R] : Distribution R) (rVec i))) *
               (∏ i : Fin n, if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1)) := by
            rw [Finset.mul_sum]
        _ = _ := by
            congr 1; refine Finset.sum_congr rfl fun rVec _ => ?_
            rw [← Finset.prod_mul_distrib]
    rw [hpull]
    congr 1
    have hps :
        (∏ i : Fin n, ∑ ri : R, ((𝒰[R] : Distribution R) ri) *
          (if ω.val < i.val then (if ri = v i then (1 : ℝ) else 0) else 1)) =
        ∑ rVec : Fin n → R, ∏ i : Fin n, ((𝒰[R] : Distribution R) (rVec i)) *
          (if ω.val < i.val then (if rVec i = v i then (1 : ℝ) else 0) else 1) :=
      Fintype.prod_sum fun i ri => ((𝒰[R] : Distribution R) ri) *
        (if ω.val < i.val then (if ri = v i then (1 : ℝ) else 0) else 1)
    rw [← hps]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : ω.val < i.val
    · simp only [hi, ↓reduceIte]
      rw [Finset.sum_eq_single (v i)]
      · simp
      · intro ri _ hri
        simp [hri]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ _))
    · simp only [hi, ↓reduceIte, mul_one]
      have hw := (𝒰[R] : ProbDist R).2.2
      rw [Probability.Distribution.weight_eq_sum] at hw
      exact hw
  simp_rw [hrSum]
  have hsSum : ∀ r : R,
      (∑ sVec : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
        ((if r = v ω then (1 : ℝ) else 0) *
         (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
         (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1))) =
      (if r = v ω then (1 : ℝ) else 0) *
      (∏ i : Fin n, if i.val < ω.val then ((pushDist 𝒰[S] G : Distribution R) (v i)) else 1) *
      (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1) := by
    intro r
    have hpull :
        ∑ sVec : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
          ((if r = v ω then (1 : ℝ) else 0) *
           (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
           (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1)) =
        (if r = v ω then (1 : ℝ) else 0) *
        (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1) *
        ∑ sVec : Fin n → S,
          (∏ i : Fin n, ((𝒰[S] : Distribution S) (sVec i)) *
            (if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) := by
      calc ∑ sVec : Fin n → S, ((𝒰[Fin n → S] : Distribution (Fin n → S)) sVec) *
            ((if r = v ω then (1 : ℝ) else 0) *
             (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) *
             (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1))
          = ∑ sVec : Fin n → S,
              ((if r = v ω then (1 : ℝ) else 0) *
               (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1)) *
              ((∏ i : Fin n, ((𝒰[S] : Distribution S) (sVec i))) *
               (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) := by
            refine Finset.sum_congr rfl fun sVec _ => ?_
            rw [← congrFun (vecDist_uniform_eq (n := n) (A := S)) sVec]; ring
        _ = ((if r = v ω then (1 : ℝ) else 0) *
             (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1)) *
            ∑ sVec : Fin n → S,
              ((∏ i : Fin n, ((𝒰[S] : Distribution S) (sVec i))) *
               (∏ i : Fin n, if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) := by
            rw [Finset.mul_sum]
        _ = _ := by
            congr 1; refine Finset.sum_congr rfl fun sVec _ => ?_
            rw [← Finset.prod_mul_distrib]
    rw [hpull]
    have hprod_s :
        ∑ sVec : Fin n → S,
          (∏ i : Fin n, ((𝒰[S] : Distribution S) (sVec i)) *
            (if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1)) =
        ∏ i : Fin n, if i.val < ω.val then ((pushDist 𝒰[S] G : Distribution R) (v i)) else 1 := by
      have hps :
          (∏ i : Fin n, ∑ si : S, ((𝒰[S] : Distribution S) si) *
            (if i.val < ω.val then (if G si = v i then (1 : ℝ) else 0) else 1)) =
          ∑ sVec : Fin n → S, ∏ i : Fin n, ((𝒰[S] : Distribution S) (sVec i)) *
            (if i.val < ω.val then (if G (sVec i) = v i then (1 : ℝ) else 0) else 1) :=
        Fintype.prod_sum fun i si => ((𝒰[S] : Distribution S) si) *
          (if i.val < ω.val then (if G si = v i then (1 : ℝ) else 0) else 1)
      rw [← hps]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hi : i.val < ω.val
      · simp only [hi, ↓reduceIte]
        unfold pushDist
        rw [← Probability.Distribution.mass_singleton _ (v i)]
        rw [Probability.Distribution.mass_fTransform]
        rw [Probability.Distribution.mass_eq_sum]
        refine Finset.sum_congr rfl fun si _ => ?_
        split_ifs <;> ring
      · simp only [hi, ↓reduceIte, mul_one]
        have hw := (𝒰[S] : ProbDist S).2.2
        rw [Probability.Distribution.weight_eq_sum] at hw
        exact hw
    rw [hprod_s]; ring
  simp_rw [hsSum]
  have hQ :
      (∑ r : R, ((Q : Distribution R) r) *
        ((if r = v ω then (1 : ℝ) else 0) *
         (∏ i : Fin n, if i.val < ω.val then ((pushDist 𝒰[S] G : Distribution R) (v i)) else 1) *
         (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1))) =
      ((Q : Distribution R) (v ω)) *
      (∏ i : Fin n, if i.val < ω.val then ((pushDist 𝒰[S] G : Distribution R) (v i)) else 1) *
      (∏ i : Fin n, if ω.val < i.val then ((𝒰[R] : Distribution R) (v i)) else 1) := by
    rw [Finset.sum_eq_single (v ω)]
    · simp; ring
    · intro r _ hr
      simp [hr]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  rw [hQ]
  have hQprod :
      ((Q : Distribution R) (v ω)) =
        ∏ i : Fin n, if i = ω then ((Q : Distribution R) (v i)) else 1 := by
    rw [Finset.prod_eq_single ω]
    · simp
    · intro i _ hi
      simp [hi]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  rw [hQprod]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hlt : i.val < ω.val
  · have hne : i ≠ ω := Fin.ne_of_lt hlt
    have hgt : ¬ ω.val < i.val := by omega
    simp [hlt, hne, hgt]
  · by_cases heq : i = ω
    · subst heq; simp
    · have hgt : ω.val < i.val := by
        have := Fin.val_ne_of_ne heq
        omega
      simp [hlt, heq, hgt]

private lemma parReduction_exp0 {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) (hn : n ≥ 1) :
    prgExp0 (parReduction A G hn) G =
      (1 / (n : ℝ)) * ∑ k ∈ oneTo n, parHybridProb A G k := by
  classical
  have : NeZero n := ⟨by omega⟩
  unfold prgExp0 parReduction
  have hexp :
      expectOf 𝒰[S] (fun s =>
        ((sampleBind 𝒰[Fin n] fun ω =>
          sampleBind (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) fun sr =>
            A.run (parSplice G n ω (G s) sr.1 sr.2) : Distribution Bool) true)) =
      expectOf 𝒰[Fin n] (fun ω =>
        expectOf (pushDist 𝒰[S] G) (fun r =>
          expectOf (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) (fun sr =>
            ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true)))) := by
    simp_rw [expectOf_pushDist]
    unfold expectOf
    simp_rw [Probability.Distribution.expect_eq_sum, sampleBind_apply, pairDist_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ =>
      Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun sr _ => by ring
  rw [hexp]
  have hω : ∀ ω : Fin n,
      expectOf (pushDist 𝒰[S] G) (fun r =>
        expectOf (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) (fun sr =>
          ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true))) =
      parHybridProb A G (ω.val + 1) := by
    intro ω
    rw [expectOf_parSplice_dist A G ω (pushDist 𝒰[S] G)]
    unfold parHybridProb parHybridDist parHybridCoord
    rw [expectOf_vecDist_eq, expectOf_vecDist_eq]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hlt : i.val < ω.val
    · have hlt' : i.val < ω.val + 1 := by omega
      simp [hlt, hlt']
    · by_cases heq : i = ω
      · simp [heq]
      · have hlt' : ¬ i.val < ω.val + 1 := by
          have := Fin.val_ne_of_ne heq
          omega
        simp [hlt, heq, hlt']
  simp_rw [hω]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  simp_rw [uniform_prob_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]
  unfold oneTo
  congr 1
  refine Finset.sum_bij (fun (ω : Fin n) _ => ω.val + 1) ?_ ?_ ?_ ?_
  · intro ω _; simp [Finset.mem_Icc, ω.isLt]
  · intro a _ b _ hab; exact Fin.ext (Nat.succ.inj hab)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only; omega
  · intro ω _; rfl

private lemma parReduction_exp1 {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    {n : ℕ} (A : PRGAdversary (VecSpace n R)) (G : S → R) (hn : n ≥ 1) :
    prgExp1 (parReduction A G hn) =
      (1 / (n : ℝ)) * ∑ k ∈ oneTo n, parHybridProb A G (k - 1) := by
  classical
  have : NeZero n := ⟨by omega⟩
  unfold prgExp1 parReduction
  have hexp :
      expectOf 𝒰[R] (fun r =>
        ((sampleBind 𝒰[Fin n] fun ω =>
          sampleBind (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) fun sr =>
            A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true)) =
      expectOf 𝒰[Fin n] (fun ω =>
        expectOf 𝒰[R] (fun r =>
          expectOf (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) (fun sr =>
            ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true)))) := by
    unfold expectOf
    simp_rw [Probability.Distribution.expect_eq_sum, sampleBind_apply, pairDist_apply]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun sr _ => ?_
    ring
  rw [hexp]
  have hω : ∀ ω : Fin n,
      expectOf 𝒰[R] (fun r =>
        expectOf (pairDist 𝒰[Fin n → S] 𝒰[Fin n → R]) (fun sr =>
          ((A.run (parSplice G n ω r sr.1 sr.2) : Distribution Bool) true))) =
      parHybridProb A G ω.val := by
    intro ω
    rw [expectOf_parSplice_dist A G ω 𝒰[R]]
    unfold parHybridProb parHybridDist parHybridCoord
    rw [expectOf_vecDist_eq, expectOf_vecDist_eq]
    refine Finset.sum_congr rfl fun v _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hlt : i.val < ω.val
    · simp [hlt]
    · by_cases heq : i = ω
      · simp [heq]
      · simp [hlt, heq]
  simp_rw [hω]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  simp_rw [uniform_prob_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]
  unfold oneTo
  congr 1
  refine Finset.sum_bij (fun (ω : Fin n) _ => ω.val + 1) ?_ ?_ ?_ ?_
  · intro ω _; simp [Finset.mem_Icc, ω.isLt]
  · intro a _ b _ hab; exact Fin.ext (Nat.succ.inj hab)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only; omega
  · intro ω _; simp

private lemma par_telescoping_eq {n : ℕ} (hn : n ≥ 1) (p : ℕ → ℝ)
    (hB0 hB1 : ℝ)
    (heq0 : hB0 = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, p k)
    (heq1 : hB1 = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, p (k - 1)) :
    |p n - p 0| = (n : ℝ) * |hB0 - hB1| := by
  unfold oneTo at heq0 heq1
  have hIcc0 : ∑ k ∈ Finset.Icc 1 n, p (k - 1) = ∑ j ∈ Finset.range n, p j := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  have hIcc1 : ∑ k ∈ Finset.Icc 1 n, p k = ∑ j ∈ Finset.range n, p (j + 1) := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk; simp only [Finset.mem_Icc] at hk; congr 1; omega
  have htele := scaled_telescoping_abs (n := n) p
  rw [← hIcc0, ← hIcc1, ← heq1, ← heq0, abs_sub_comm hB1 hB0, abs_sub_comm (p 0) (p n)] at htele
  exact eq_mul_of_div_eq (Nat.succ_le_iff.mp hn) htele

theorem theorem3_2_parallel_prg_composition
    {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    (G : S → R) (n : ℕ) (hn : n ≥ 1)
    (A : PRGAdversary (VecSpace n R)) :
    ∃ B : ElementaryWrapper A (parReduction A G hn),
      prgAdv A (parallelPRG G n) = (n : ℝ) * prgAdv B.toAdv G := by
  Proof overview
    "For each $0 \\le j \\le n$, define Hybrid $H_j$ by generating the first $j$ blocks $1, \\dots, j$ as $G(s_i)$ ($s_i \\leftarrow \\mathcal{S}$) and sampling the remaining $n - j$ blocks $j+1, \\dots, n$ uniformly from $\\mathcal{R}$, and let $p_j := \\Pr[\\mathcal{A}(H_j) = 1]$"
  We note hEnds :
      parHybridProb A G 0 = prgExp1 A ∧ parHybridProb A G n = prgExp0 A (parallelPRG G n) by
    constructor
    · by_leaf "In $H_0$, all $n$ blocks are sampled uniformly from $\\mathcal{R}$, matching Experiment 1." {
        exact parHybridProb_zero A G
      }
    · by_leaf "In $H_n$, all $n$ blocks are computed via $G(s_i)$, matching Experiment 0 for $G'$." {
        exact parHybridProb_n A G
      }
  reduction_step B : PRGAdversary R := parReduction A G hn
    box "Reduction $\\mathcal{B}$"
    "Upon receiving $r \\in \\mathcal{R}$:\n\
     sample $\\omega \\leftarrow \\{1, \\dots, n\\}$\n\
     for $i = 1, \\dots, \\omega - 1$ do $s_i \\leftarrow \\mathcal{S}$; $r_i \\leftarrow G(s_i)$\n\
     $r_\\omega \\leftarrow r$\n\
     for $i = \\omega + 1, \\dots, n$ do $r_i \\leftarrow \\mathcal{R}$\n\
     run $b \\leftarrow \\mathcal{A}(r_1, \\dots, r_n)$ and output $b$"
  We note hB0 :
      prgExp0 B G = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, parHybridProb A G k
      explaining "since $\\omega$ is chosen uniformly from $\\{1, \\dots, n\\}$" by
    by_leaf "Conditioning on $\\omega = k \\in \\{1, \\dots, n\\}$ when $r = G(s)$, blocks $1, \\dots, k$ come from $G$ and blocks $k+1, \\dots, n$ come from $\\mathcal{R}$, matching $H_k$." {
      exact parReduction_exp0 A G hn
    }
  We note hB1 :
      prgExp1 B = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, parHybridProb A G (k - 1) by
    by_leaf "Conditioning on $\\omega = k \\in \\{1, \\dots, n\\}$ when $r \\leftarrow \\mathcal{R}$, blocks $1, \\dots, k-1$ come from $G$ and blocks $k, \\dots, n$ come from $\\mathcal{R}$, matching $H_{k-1}$." {
      exact parReduction_exp1 A G hn
    }
  by_leaf "Telescoping the hybrid average gives $\\mathrm{PRGadv}[\\mathcal{B}, G] = \\frac{1}{n}|p_n - p_0| = \\frac{1}{n}\\,\\mathrm{PRGadv}[\\mathcal{A}, G']$, so $\\mathrm{PRGadv}[\\mathcal{A}, G'] = n \\cdot \\mathrm{PRGadv}[\\mathcal{B}, G]$." {
    refine ⟨⟨B, rfl⟩, ?_⟩
    unfold prgAdv ElementaryWrapper.toAdv
    dsimp only
    rw [← hEnds.2, ← hEnds.1]
    exact par_telescoping_eq hn (fun j => parHybridProb A G j) (prgExp0 B G) (prgExp1 B) hB0 hB1
  }

informal_title theorem3_2_parallel_prg_composition
  "Parallel Composition of Pseudorandom Generators"

informal_theorem_notation theorem3_2_parallel_prg_composition
  (parallelPRG G n) "G'" "the $n$-fold parallel composition $G^{\\| n}$"

paper_setting_ns Paper.BonehShoupPart1.ParallelPRG
  "Let $\\mathcal{S}$ and $\\mathcal{R}$ be finite sets, let $G : \\mathcal{S} \\to \\mathcal{R}$ be a PRG, and for $n \\ge 1$ let $G' := G^{\\| n} : \\mathcal{S}^n \\to \\mathcal{R}^n$ denote its $n$-fold parallel composition."
  (suppress := ["S", "R", "G"])
  (anchor := Paper.BonehShoupPart1.ParallelPRG.theorem3_2_parallel_prg_composition)
  (title := "Section 3.4.1 — Parallel Composition of Pseudorandom Generators")
  (register := gameBased)

paper_motivation Paper.BonehShoupPart1.ParallelPRG.theorem3_2_parallel_prg_composition
  "If $G$ is a secure PRG, then $G' = G^{\\| n}$ is also a secure PRG. A hybrid argument across $n$ coordinates bounds the distinguishing advantage of $\\mathcal{A}$ by $n$ times that of an elementary wrapper $\\mathcal{B}$ around $\\mathcal{A}$."

informal_section_prelude Paper.BonehShoupPart1.ParallelPRG.theorem3_2_parallel_prg_composition
  "construction" "Attack Game 3.1 & Construction 3.1" "Parallel Composition PRG"
  "For a PRG $G : \\mathcal{S} \\to \\mathcal{R}$ and adversary $\\mathcal{A}$, let $\\Pr_0[\\mathcal{A}, G] := \\Pr[\\mathcal{A}(G(s)) = 1]$ ($s \\leftarrow \\mathcal{S}$), let $\\Pr_1[\\mathcal{A}] := \\Pr[\\mathcal{A}(r) = 1]$ ($r \\leftarrow \\mathcal{R}$), and let $\\mathrm{PRGadv}[\\mathcal{A}, G] := |\\Pr_0[\\mathcal{A}, G] - \\Pr_1[\\mathcal{A}]|$.\n> Construction 3.1 (Parallel composition $G' = G^{\\| n} : \\mathcal{S}^n \\to \\mathcal{R}^n$): on input $(s_1, \\dots, s_n) \\in \\mathcal{S}^n$, output $G'(s_1, \\dots, s_n) := (G(s_1), \\dots, G(s_n))$."

end ParallelPRG

-- ============================================================================
-- Section 3.4.2: Sequential Composition of PRGs (Theorem 3.3)
-- ============================================================================

namespace SequentialPRG

/-- Acceptance probability `p_j = Pr[A(H_j) = 1]` (`0 ≤ j ≤ n`). -/
@[math_notation "p_{#3}"]
noncomputable def seqHybridProb' {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary (VecSpace n R × S)) (G : S → R × S) (j : ℕ) : ℝ :=
  seqHybridProb A G j

private lemma seqFill_succ {R S : Type} (G : S → R × S) (n k : ℕ)
    (buf : Fin n → R) (s : S) :
    seqFill G n (k + 1) buf s =
      let p := G s
      seqFill G n k (fun i => if i.val = n - (k + 1) then p.1 else buf i) p.2 := by
  rfl

private lemma seqFill_zero {R S : Type} (G : S → R × S) (n : ℕ)
    (buf : Fin n → R) (s : S) :
    seqFill G n 0 buf s = (buf, s) := rfl

private lemma seqFill_agree {R S : Type} (G : S → R × S) (n k : ℕ)
    (buf₁ buf₂ : Fin n → R) (s : S)
    (hagree : ∀ i : Fin n, i.val < n - k → buf₁ i = buf₂ i) :
    seqFill G n k buf₁ s = seqFill G n k buf₂ s := by
  induction k generalizing buf₁ buf₂ s with
  | zero =>
    rw [seqFill_zero, seqFill_zero]
    congr 1
    funext i
    exact hagree i i.isLt
  | succ k ih =>
    rw [seqFill_succ, seqFill_succ]
    apply ih
    intro i hi
    split_ifs with heq
    · rfl
    · refine hagree i ?_
      omega

private lemma seqHybridProb_zero {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary (VecSpace n R × S)) (G : S → R × S) :
    seqHybridProb' A G 0 = prgExp0 A (seqPRG G n) := by
  classical
  unfold seqHybridProb' seqHybridProb seqHybridDist prgExp0 seqPRG
  rw [expectOf_pushDist]
  simp only [Nat.sub_zero]
  have hagree : ∀ (bs : (Fin n → R) × S),
      seqFill G n n bs.1 bs.2 = seqFill G n n (fun _ => Classical.arbitrary R) bs.2 := by
    intro bs
    exact seqFill_agree G n n bs.1 _ bs.2 (fun i hi => by omega)
  simp_rw [hagree]
  unfold expectOf
  simp_rw [Probability.Distribution.expect_eq_sum, pairDist_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hw := (𝒰[Fin n → R] : ProbDist (Fin n → R)).2.2
  rw [Probability.Distribution.weight_eq_sum] at hw
  calc ∑ buf : Fin n → R,
        ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) * ((𝒰[S] : Distribution S) s) *
          ((A.run (seqFill G n n (fun _ => Classical.arbitrary R) s) : Distribution Bool) true)
      = (∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf)) *
          (((𝒰[S] : Distribution S) s) *
            ((A.run (seqFill G n n (fun _ => Classical.arbitrary R) s) : Distribution Bool) true)) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => ?_; ring
    _ = ((𝒰[S] : Distribution S) s) *
          ((A.run (seqFill G n n (fun _ => Classical.arbitrary R) s) : Distribution Bool) true) := by
        rw [hw, one_mul]

private lemma seqHybridProb_n {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary (VecSpace n R × S)) (G : S → R × S) :
    seqHybridProb' A G n = prgExp1 A := by
  classical
  unfold seqHybridProb' seqHybridProb seqHybridDist prgExp1
  rw [expectOf_pushDist]
  simp only [Nat.sub_self, seqFill_zero]
  unfold expectOf
  simp_rw [Probability.Distribution.expect_eq_sum, pairDist_apply]
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp_rw [uniform_prob_apply]
  rw [Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

private lemma seqReduction_exp0 {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary (VecSpace n R × S)) (G : S → R × S) (hn : n ≥ 1) :
    prgExp0 (seqReduction A G (Nat.succ_le_iff.mp hn)) G =
      (1 / (n : ℝ)) * ∑ k ∈ oneTo n, seqHybridProb' A G (k - 1) := by
  classical
  have : NeZero n := ⟨by omega⟩
  unfold prgExp0 seqReduction
  have hω_step : ∀ (ω : Fin n) (buf : Fin n → R) (s : S),
      seqFill G n (n - (ω.val + 1)) (fun i => if i.val = ω.val then (G s).1 else buf i) (G s).2 =
        seqFill G n (n - ω.val) buf s := by
    intro ω buf s
    have hsub : n - ω.val = (n - (ω.val + 1)) + 1 := by omega
    rw [hsub, seqFill_succ]
    have hsub2 : n - (n - (ω.val + 1) + 1) = ω.val := by omega
    rw [hsub2]
  have hexp :
      expectOf 𝒰[S] (fun s =>
        ((sampleBind 𝒰[Fin n] fun ω =>
          sampleBind 𝒰[Fin n → R] fun buf =>
            A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then (G s).1 else buf i) (G s).2) : Distribution Bool) true)) =
      expectOf 𝒰[Fin n] (fun ω => seqHybridProb' A G ω.val) := by
    unfold seqHybridProb' seqHybridProb seqHybridDist
    simp_rw [expectOf_pushDist]
    unfold expectOf
    simp_rw [Probability.Distribution.expect_eq_sum, sampleBind_apply, pairDist_apply,
      Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun buf _ => ?_
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hω_step ω buf s]
    ring
  rw [hexp]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  simp_rw [uniform_prob_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]
  unfold oneTo
  congr 1
  refine Finset.sum_bij (fun (ω : Fin n) _ => ω.val + 1) ?_ ?_ ?_ ?_
  · intro ω _; simp [Finset.mem_Icc, ω.isLt]
  · intro a _ b _ hab; exact Fin.ext (Nat.succ.inj hab)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only; omega
  · intro ω _; simp

private lemma seqReduction_exp1 {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary (VecSpace n R × S)) (G : S → R × S) (hn : n ≥ 1) :
    prgExp1 (seqReduction A G (Nat.succ_le_iff.mp hn)) =
      (1 / (n : ℝ)) * ∑ k ∈ oneTo n, seqHybridProb' A G k := by
  classical
  have : NeZero n := ⟨by omega⟩
  unfold prgExp1 seqReduction
  have hω_swap : ∀ (ω : Fin n) (s' : S),
      ∑ r : R, ∑ buf : Fin n → R,
        ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
          ((A.run (seqFill G n (n - (ω.val + 1))
            (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true) =
      ∑ buf : Fin n → R,
        ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
          ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true) := by
    intro ω s'
    let swapFn : R × (Fin n → R) → R × (Fin n → R) :=
      fun p => (p.2 ω, fun i => if i = ω then p.1 else p.2 i)
    have hinv : Function.Involutive swapFn := by
      intro ⟨r, buf⟩
      apply Prod.ext
      · simp [swapFn]
      · funext i
        dsimp [swapFn]
        split_ifs with hi <;> simp [hi]
    have hbij :
        ∑ p : R × (Fin n → R),
          ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
            ((A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then p.1 else p.2 i) s') : Distribution Bool) true) =
        ∑ p : R × (Fin n → R),
          ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
            ((A.run (seqFill G n (n - (ω.val + 1)) p.2 s') : Distribution Bool) true) := by
      refine Finset.sum_bij (fun p _ => swapFn p)
        (fun _ _ => Finset.mem_univ _)
        (fun a _ b _ hab => hinv.injective hab)
        (fun y _ => ⟨swapFn y, Finset.mem_univ _, hinv y⟩)
        (fun p _ => ?_)
      simp_rw [uniform_prob_apply]
      congr 1
      dsimp [swapFn]
      have hbuf : (fun i : Fin n => if i.val = ω.val then p.1 else p.2 i) =
          (fun i => if i = ω then p.1 else p.2 i) := by
        funext i; simp [Fin.ext_iff]
      rw [hbuf]
    have hsplitL :
        ∑ r : R, ∑ buf : Fin n → R,
          ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
            ((A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true) =
        ∑ p : R × (Fin n → R),
          ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
            ((A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then p.1 else p.2 i) s') : Distribution Bool) true) :=
      (Fintype.sum_prod_type (fun p : R × (Fin n → R) =>
        ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
          ((A.run (seqFill G n (n - (ω.val + 1))
            (fun i => if i.val = ω.val then p.1 else p.2 i) s') : Distribution Bool) true))).symm
    have hsplitR :
        ∑ p : R × (Fin n → R),
          ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
            ((A.run (seqFill G n (n - (ω.val + 1)) p.2 s') : Distribution Bool) true) =
        ∑ r : R, ∑ buf : Fin n → R,
          ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
            ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true) :=
      Fintype.sum_prod_type (fun p : R × (Fin n → R) =>
        ((𝒰[R] : Distribution R) p.1) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) p.2) *
          ((A.run (seqFill G n (n - (ω.val + 1)) p.2 s') : Distribution Bool) true))
    rw [hsplitL, hbij, hsplitR, Finset.sum_comm]
    refine Finset.sum_congr rfl fun buf _ => ?_
    have hwR := (𝒰[R] : ProbDist R).2.2
    rw [Probability.Distribution.weight_eq_sum] at hwR
    calc ∑ r : R, ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
            ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true)
        = (∑ r : R, ((𝒰[R] : Distribution R) r)) *
            (((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
              ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true)) := by
          rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun _ _ => ?_; ring
      _ = ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
            ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true) := by
          rw [hwR, one_mul]
  have hexp :
      expectOf 𝒰[R × S] (fun rs =>
        ((sampleBind 𝒰[Fin n] fun ω =>
          sampleBind 𝒰[Fin n → R] fun buf =>
            A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then rs.1 else buf i) rs.2) : Distribution Bool) true)) =
      expectOf 𝒰[Fin n] (fun ω => seqHybridProb' A G (ω.val + 1)) := by
    unfold seqHybridProb' seqHybridProb seqHybridDist
    simp_rw [expectOf_pushDist]
    unfold expectOf
    simp_rw [Probability.Distribution.expect_eq_sum, sampleBind_apply, pairDist_apply,
      Fintype.sum_prod_type]
    have hL0 :
        (∑ r : R, ∑ s' : S, ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
          ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
            ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
              ((A.run (seqFill G n (n - (ω.val + 1))
                (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true)) =
        ∑ r : R, ∑ s' : S, ∑ ω : Fin n,
          ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
            (((𝒰[Fin n] : Distribution (Fin n)) ω) *
              ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                ((A.run (seqFill G n (n - (ω.val + 1))
                  (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true)) := by
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s' _ => Finset.mul_sum _ _ _
    have hL1 :
        (∑ ω : Fin n, ∑ r : R,
          ∑ s' : S, ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
            (((𝒰[Fin n] : Distribution (Fin n)) ω) *
              ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                ((A.run (seqFill G n (n - (ω.val + 1))
                  (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true))) =
        ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
          ∑ s' : S, ((𝒰[S] : Distribution S) s') *
            ∑ r : R, ∑ buf : Fin n → R,
              ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                ((A.run (seqFill G n (n - (ω.val + 1))
                  (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true) := by
      refine Finset.sum_congr rfl fun ω _ => ?_
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun r _ =>
        Finset.sum_congr rfl fun buf _ => ?_
      simp_rw [uniform_prob_apply]
      rw [Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]
      ring
    calc (∑ r : R, ∑ s' : S, ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
            ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
              ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                ((A.run (seqFill G n (n - (ω.val + 1))
                  (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true))
        = ∑ r : R, ∑ s' : S, ∑ ω : Fin n,
            ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
              (((𝒰[Fin n] : Distribution (Fin n)) ω) *
                ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                  ((A.run (seqFill G n (n - (ω.val + 1))
                    (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true)) := hL0
      _ = ∑ r : R, ∑ ω : Fin n, ∑ s' : S,
            ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
              (((𝒰[Fin n] : Distribution (Fin n)) ω) *
                ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                  ((A.run (seqFill G n (n - (ω.val + 1))
                    (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true)) := by
          refine Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ ω : Fin n, ∑ r : R, ∑ s' : S,
            ((𝒰[R × S] : Distribution (R × S)) (r, s')) *
              (((𝒰[Fin n] : Distribution (Fin n)) ω) *
                ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                  ((A.run (seqFill G n (n - (ω.val + 1))
                    (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true)) :=
          Finset.sum_comm
      _ = ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
            ∑ s' : S, ((𝒰[S] : Distribution S) s') *
              ∑ r : R, ∑ buf : Fin n → R,
                ((𝒰[R] : Distribution R) r) * ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                  ((A.run (seqFill G n (n - (ω.val + 1))
                    (fun i => if i.val = ω.val then r else buf i) s') : Distribution Bool) true) := hL1
      _ = ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
            ∑ s' : S, ((𝒰[S] : Distribution S) s') *
              ∑ buf : Fin n → R, ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) *
                ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          congr 1; refine Finset.sum_congr rfl fun s' _ => ?_
          congr 1; exact hω_swap ω s'
      _ = ∑ ω : Fin n, ((𝒰[Fin n] : Distribution (Fin n)) ω) *
            ∑ buf : Fin n → R, ∑ s' : S,
              ((𝒰[Fin n → R] : Distribution (Fin n → R)) buf) * ((𝒰[S] : Distribution S) s') *
                ((A.run (seqFill G n (n - (ω.val + 1)) buf s') : Distribution Bool) true) := by
          refine Finset.sum_congr rfl fun ω _ => ?_
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun buf _ => Finset.sum_congr rfl fun s' _ => by ring
  rw [hexp]
  unfold expectOf
  rw [Probability.Distribution.expect_eq_sum]
  simp_rw [uniform_prob_apply, Fintype.card_fin]
  rw [← Finset.mul_sum]
  unfold oneTo
  congr 1
  refine Finset.sum_bij (fun (ω : Fin n) _ => ω.val + 1) ?_ ?_ ?_ ?_
  · intro ω _; simp [Finset.mem_Icc, ω.isLt]
  · intro a _ b _ hab; exact Fin.ext (Nat.succ.inj hab)
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp only; omega
  · intro ω _; rfl

private lemma seq_telescoping_eq {n : ℕ} (hn : n ≥ 1) (p : ℕ → ℝ)
    (hB0 hB1 : ℝ)
    (heq0 : hB0 = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, p (k - 1))
    (heq1 : hB1 = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, p k) :
    |p 0 - p n| = (n : ℝ) * |hB0 - hB1| := by
  unfold oneTo at heq0 heq1
  have hIcc0 : ∑ k ∈ Finset.Icc 1 n, p (k - 1) = ∑ j ∈ Finset.range n, p j := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k _; rfl
  have hIcc1 : ∑ k ∈ Finset.Icc 1 n, p k = ∑ j ∈ Finset.range n, p (j + 1) := by
    refine Finset.sum_bij (fun k _ => k - 1) ?_ ?_ ?_ ?_
    · intro k hk; simp only [Finset.mem_Icc, Finset.mem_range] at *; omega
    · intro a ha b hb hab; simp only [Finset.mem_Icc] at ha hb; omega
    · intro j hj; simp only [Finset.mem_range] at hj
      refine ⟨j + 1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro k hk; simp only [Finset.mem_Icc] at hk; congr 1; omega
  have htele := scaled_telescoping_abs (n := n) p
  rw [← hIcc0, ← hIcc1, ← heq0, ← heq1] at htele
  exact eq_mul_of_div_eq (Nat.succ_le_iff.mp hn) htele

theorem theorem3_3_sequential_prg_composition
    {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    (G : S → R × S) (n : ℕ) (hn : n ≥ 1)
    (A : PRGAdversary (VecSpace n R × S)) :
    ∃ B : ElementaryWrapper A (seqReduction A G (Nat.succ_le_iff.mp hn)),
      prgAdv A (seqPRG G n) = (n : ℝ) * prgAdv B.toAdv G := by
  Proof overview
    "For each $0 \\le j \\le n$, define Hybrid $H_j$ by sampling the first $j$ output blocks $r_1, \\dots, r_j \\leftarrow \\mathcal{R}$ and an intermediate state $s_j \\leftarrow \\mathcal{S}$ uniformly, then iterating $(r_i, s_i) \\leftarrow G(s_{i-1})$ for $i = j+1, \\dots, n$ to output $((r_1, \\dots, r_n), s_n)$, and let $p_j := \\Pr[\\mathcal{A}(H_j) = 1]$"
  We note hEnds :
      seqHybridProb' A G 0 = prgExp0 A (seqPRG G n) ∧ seqHybridProb' A G n = prgExp1 A by
    constructor
    · by_leaf "In $H_0$, all $n$ iterations run from $s_0 \\leftarrow \\mathcal{S}$, matching Experiment 0 for $G'$." {
        exact seqHybridProb_zero A G
      }
    · by_leaf "In $H_n$, zero iterations remain after sampling all $n$ blocks and $s_n$ uniformly, matching Experiment 1." {
        exact seqHybridProb_n A G
      }
  reduction_step B : PRGAdversary (R × S) := seqReduction A G (Nat.succ_le_iff.mp hn)
    box "Reduction $\\mathcal{B}$"
    "Upon receiving $(r, s') \\in \\mathcal{R} \\times \\mathcal{S}$:\n\
     sample $\\omega \\leftarrow \\{1, \\dots, n\\}$\n\
     for $i = 1, \\dots, \\omega - 1$ do $r_i \\leftarrow \\mathcal{R}$\n\
     $(r_\\omega, s_\\omega) \\leftarrow (r, s')$\n\
     for $i = \\omega + 1, \\dots, n$ do $(r_i, s_i) \\leftarrow G(s_{i-1})$\n\
     run $b \\leftarrow \\mathcal{A}((r_1, \\dots, r_n), s_n)$ and output $b$"
  We note hB0 :
      prgExp0 B G = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, seqHybridProb' A G (k - 1)
      explaining "since $\\omega$ is chosen uniformly from $\\{1, \\dots, n\\}$" by
    by_leaf "Conditioning on $\\omega = k \\in \\{1, \\dots, n\\}$ when $(r, s') = G(s_{k-1})$, the challenge implements step $k$ of $G$, matching $H_{k-1}$." {
      exact seqReduction_exp0 A G hn
    }
  We note hB1 :
      prgExp1 B = (1 / (n : ℝ)) * ∑ k ∈ oneTo n, seqHybridProb' A G k by
    by_leaf "Conditioning on $\\omega = k \\in \\{1, \\dots, n\\}$ when $(r, s') \\leftarrow \\mathcal{R} \\times \\mathcal{S}$, blocks $1, \\dots, k$ are uniform and $s_k$ is uniform, matching $H_k$." {
      exact seqReduction_exp1 A G hn
    }
  by_leaf "Telescoping the hybrid average gives $\\mathrm{PRGadv}[\\mathcal{B}, G] = \\frac{1}{n}|p_0 - p_n| = \\frac{1}{n}\\,\\mathrm{PRGadv}[\\mathcal{A}, G']$, so $\\mathrm{PRGadv}[\\mathcal{A}, G'] = n \\cdot \\mathrm{PRGadv}[\\mathcal{B}, G]$." {
    refine ⟨⟨B, rfl⟩, ?_⟩
    unfold prgAdv ElementaryWrapper.toAdv
    dsimp only
    rw [← hEnds.1, ← hEnds.2]
    exact seq_telescoping_eq hn (fun j => seqHybridProb' A G j) (prgExp0 B G) (prgExp1 B) hB0 hB1
  }

informal_title theorem3_3_sequential_prg_composition
  "Sequential Composition of Pseudorandom Generators"

informal_theorem_notation theorem3_3_sequential_prg_composition
  (seqPRG G n) "G'" "the $n$-step sequential composition $G^{\\mathrm{seq}\\, n}$"

paper_setting_ns Paper.BonehShoupPart1.SequentialPRG
  "Let $\\mathcal{S}$ and $\\mathcal{R}$ be finite sets, let $G : \\mathcal{S} \\to \\mathcal{R} \\times \\mathcal{S}$ be a PRG, and for $n \\ge 1$ let $G' := G^{\\mathrm{seq}\\, n} : \\mathcal{S} \\to \\mathcal{R}^n \\times \\mathcal{S}$ denote its $n$-step sequential composition."
  (suppress := ["R", "S", "G"])
  (anchor := Paper.BonehShoupPart1.SequentialPRG.theorem3_3_sequential_prg_composition)
  (title := "Section 3.4.2 — Sequential Composition of Pseudorandom Generators")
  (register := gameBased)

paper_motivation Paper.BonehShoupPart1.SequentialPRG.theorem3_3_sequential_prg_composition
  "If $G$ is a secure PRG, then its $n$-fold sequential composition $G' = G^{\\mathrm{seq}\\, n}$ is also a secure PRG, with advantage bounded by $n$ times that of an elementary wrapper $\\mathcal{B}$ around $\\mathcal{A}$."

informal_section_prelude Paper.BonehShoupPart1.SequentialPRG.theorem3_3_sequential_prg_composition
  "construction" "Construction 3.2" "Sequential Composition PRG"
  "For a PRG $G : \\mathcal{S} \\to \\mathcal{R} \\times \\mathcal{S}$ and $n \\ge 1$, the $n$-step sequential composition $G' = G^{\\mathrm{seq}\\, n} : \\mathcal{S} \\to \\mathcal{R}^n \\times \\mathcal{S}$ works as follows:\n> on input $s_0 \\in \\mathcal{S}$:\n> for $i = 1, \\dots, n$ do\n>   $(r_i, s_i) \\leftarrow G(s_{i-1})$\n> output $((r_1, \\dots, r_n), s_n)$."

end SequentialPRG

-- ============================================================================
-- Section 3.11: Statistical Distance Bounds Distinguishing Advantage (Theorem 3.11)
-- ============================================================================

namespace StatDist

theorem theorem3_11_statDist_bounds_distAdv
    {R : Type} [Fintype R] (P₀ P₁ : ProbDist R) (A : DistAdversary R) :
    distAdv A P₀ P₁ ≤ Probability.statDist (P₀ : Distribution R) (P₁ : Distribution R) := by
  We note hCoin : ∀ (t : A.Coins),
      |probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t)| ≤
        Probability.statDist (P₀ : Distribution R) (P₁ : Distribution R) by
    by_leaf "For any fixed coin tape $t \\in \\mathcal{T}_{\\mathcal{A}}$, writing $R'_t := \\{x \\in \\mathcal{R} : \\mathcal{A}(x; t) = 1\\}$ gives $P_0[R'_t] - P_1[R'_t] = \\sum_{x \\in R'_t}(P_0(x) - P_1(x)) \\le \\sum_{x : P_0(x) > P_1(x)}(P_0(x) - P_1(x)) = \\frac{1}{2}\\sum_{x \\in \\mathcal{R}}|P_0(x) - P_1(x)| = \\Delta(P_0, P_1)$, since $\\sum_{x \\in \\mathcal{R}}(P_0(x) - P_1(x)) = 0$. Applying the symmetric argument to $P_1 - P_0$ yields $|P_0[R'_t] - P_1[R'_t]| \\le \\Delta(P_0, P_1)$." {
      exact fun t => theorem3_10_statDist_bounds_event P₀ P₁ (acceptEvent A t)
    }
  by_leaf "Averaging over the adversary's internal random coins $t \\leftarrow \\mathcal{T}_{\\mathcal{A}}$ via the triangle inequality gives $\\mathrm{Distadv}[\\mathcal{A}, P_0, P_1] \\le \\mathbb{E}_t[|P_0[R'_t] - P_1[R'_t]|] \\le \\Delta(P_0, P_1)$." {
    unfold distAdv distWinProb
    calc |expectOf 𝒰[A.Coins] (fun t => probOf P₀ (acceptEvent A t)) -
            expectOf 𝒰[A.Coins] (fun t => probOf P₁ (acceptEvent A t))|
        ≤ expectOf 𝒰[A.Coins] (fun t => |probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t)|) := by
          unfold expectOf
          exact Probability.Distribution.abs_expect_sub_expect_le_expect
            (Probability.Distribution.uniform_nonNeg (A := A.Coins)) _ _ _ (fun _ => le_rfl)
      _ ≤ Probability.statDist (P₀ : Distribution R) (P₁ : Distribution R) *
            (𝒰[A.Coins] : Distribution A.Coins).weight := by
          unfold expectOf
          exact Probability.Distribution.expect_le_mul_weight
            (Probability.Distribution.uniform_nonNeg (A := A.Coins)) (fun t _ => hCoin t)
      _ = Probability.statDist (P₀ : Distribution R) (P₁ : Distribution R) := by
          rw [uniform_prob_weight (A := A.Coins), mul_one]
  }

informal_title theorem3_11_statDist_bounds_distAdv
  "Statistical Distance Bounds Distinguishing Advantage"

informal_binder theorem3_11_statDist_bounds_distAdv "R" "\\mathcal{R}"

paper_setting_ns Paper.BonehShoupPart1.StatDist
  "Fix a finite set $\\mathcal{R}$. For probability distributions $P_0, P_1$ on $\\mathcal{R}$, their statistical distance is $\\Delta(P_0, P_1) := \\frac{1}{2}\\sum_{x \\in \\mathcal{R}} |P_0(x) - P_1(x)|$. Any distinguishing adversary $\\mathcal{A}$ draws internal coins $t \\leftarrow \\mathcal{T}_{\\mathcal{A}}$ and induces coin-fixed acceptance events $R'_t := \\{x \\in \\mathcal{R} : \\mathcal{A}(x; t) = 1\\}$."
  (suppress := ["R"])
  (anchor := Paper.BonehShoupPart1.StatDist.theorem3_11_statDist_bounds_distAdv)
  (title := "Section 3.11 — Statistical Distance and Distinguishing Advantage")
  (register := gameBased)

paper_motivation Paper.BonehShoupPart1.StatDist.theorem3_11_statDist_bounds_distAdv
  "No distinguishing adversary (deterministic or randomized) can achieve advantage exceeding the statistical distance $\\Delta(P_0, P_1)$."

informal_section_prelude Paper.BonehShoupPart1.StatDist.theorem3_11_statDist_bounds_distAdv
  "definition" "Definition 3.6 & Attack Game 3.3" "Distinguishing Advantage"
  "In Attack Game 3.3 for distributions $P_0, P_1$ on $\\mathcal{R}$ and adversary $\\mathcal{A}$, the challenger chooses $b \\leftarrow \\{0,1\\}$, samples $x \\leftarrow P_b$, and sends $x$ to $\\mathcal{A}$, whose distinguishing advantage is $\\mathrm{Distadv}[\\mathcal{A}, P_0, P_1] := |\\Pr[\\mathcal{A}(P_0) = 1] - \\Pr[\\mathcal{A}(P_1) = 1]|$."

end StatDist

-- ============================================================================
-- Section 4.4.3: The Difference Lemma (Theorem 4.7)
-- ============================================================================

namespace DiffLemma

/-- Idiomatic Boneh–Shoup identical-until-bad event relation (`W_0 ∧ ¬Z iff W_1 ∧ ¬Z`). -/
@[math_notation "#1 \\land \\overline{#3} \\text{ iff } #2 \\land \\overline{#3}"]
def IdenticalUntilBad {Ω : Type} (W₀ W₁ Z : Ω → Prop) : Prop :=
  ∀ ω : Ω, W₀ ω ∧ ¬ Z ω ↔ W₁ ω ∧ ¬ Z ω

theorem theorem4_7_difference_lemma
    {Ω : Type} (P : ProbDist Ω) (W₀ W₁ Z : Ω → Prop)
    (hEquiv : IdenticalUntilBad W₀ W₁ Z) :
    |probOf P W₀ - probOf P W₁| ≤ probOf P Z := by
  We note hDiff : probOf P W₀ - probOf P W₁ = probOf P (evAnd W₀ Z) - probOf P (evAnd W₁ Z) by
    by_leaf "By the law of total probability, $P[W_0] = P[W_0 \\land Z] + P[W_0 \\land \\overline{Z}]$ and $P[W_1] = P[W_1 \\land Z] + P[W_1 \\land \\overline{Z}]$; since $P[W_0 \\land \\overline{Z}] = P[W_1 \\land \\overline{Z}]$ by hypothesis, subtracting cancels the $\\overline{Z}$ terms." {
      have h0 := probOf_split P Z W₀
      have h1 := probOf_split P Z W₁
      have heq : probOf P (evAnd W₀ (evCompl Z)) = probOf P (evAnd W₁ (evCompl Z)) :=
        probOf_congr P hEquiv
      exact by
        change probOf P (fun ω => W₀ ω ∧ Z ω) + probOf P (fun ω => W₀ ω ∧ ¬Z ω) = probOf P W₀ at h0
        change probOf P (fun ω => W₁ ω ∧ Z ω) + probOf P (fun ω => W₁ ω ∧ ¬Z ω) = probOf P W₁ at h1
        change probOf P (fun ω => W₀ ω ∧ ¬Z ω) = probOf P (fun ω => W₁ ω ∧ ¬Z ω) at heq
        change probOf P W₀ - probOf P W₁ =
          probOf P (fun ω => W₀ ω ∧ Z ω) - probOf P (fun ω => W₁ ω ∧ Z ω)
        linarith
    }
  We claim hBound₀ : 0 ≤ probOf P (evAnd W₀ Z) ∧ probOf P (evAnd W₀ Z) ≤ probOf P Z by
    by_leaf "Nonnegativity of probability gives $0 \\le P[W_0 \\land Z]$, and monotonicity over the inclusion $W_0 \\land Z \\subseteq Z$ yields $P[W_0 \\land Z] \\le P[Z]$." {
      exact ⟨probOf_nonneg P _, probOf_mono P (fun _ h => h.2)⟩
    }
  We claim hBound₁ : 0 ≤ probOf P (evAnd W₁ Z) ∧ probOf P (evAnd W₁ Z) ≤ probOf P Z by
    by_leaf "Likewise, nonnegativity gives $0 \\le P[W_1 \\land Z]$ and monotonicity over $W_1 \\land Z \\subseteq Z$ yields $P[W_1 \\land Z] \\le P[Z]$." {
      exact ⟨probOf_nonneg P _, probOf_mono P (fun _ h => h.2)⟩
    }
  by_leaf "Since both $P[W_0 \\land Z]$ and $P[W_1 \\land Z]$ lie in $[0, P[Z]]$, subtracting yields $|P[W_0] - P[W_1]| = |P[W_0 \\land Z] - P[W_1 \\land Z]| \\le P[Z]$." {
    rw [hDiff]
    exact abs_le.mpr ⟨by linarith [hBound₀.1, hBound₁.2], by linarith [hBound₀.2, hBound₁.1]⟩
  }

informal_title theorem4_7_difference_lemma
  "The Difference Lemma"

paper_setting_ns Paper.BonehShoupPart1.DiffLemma
  "Fix a probability space $(\\Omega, P)$; for any event $Z$ on $\\Omega$, denote its complement by $\\overline{Z}$."
  (suppress := ["Ω", "P"])
  (anchor := Paper.BonehShoupPart1.DiffLemma.theorem4_7_difference_lemma)
  (title := "Section 4.4.3 — The Difference Lemma")
  (register := gameBased)

paper_motivation Paper.BonehShoupPart1.DiffLemma.theorem4_7_difference_lemma
  "If two game events agree whenever a failure event $Z$ does not occur, their probabilities differ by at most $P[Z]$."

end DiffLemma

end Paper.BonehShoupPart1

-- ============================================================================
-- Axiom Verification & Paper Validation Export
-- ============================================================================

#print axioms Paper.BonehShoupPart1.OneTimePad.theorem2_2_otp_perfect_security
#print axioms Paper.BonehShoupPart1.ParallelPRG.theorem3_2_parallel_prg_composition
#print axioms Paper.BonehShoupPart1.SequentialPRG.theorem3_3_sequential_prg_composition
#print axioms Paper.BonehShoupPart1.StatDist.theorem3_11_statDist_bounds_distAdv
#print axioms Paper.BonehShoupPart1.DiffLemma.theorem4_7_difference_lemma

open Lean in
#eval show Lean.Elab.Term.TermElabM Unit from do
  let decls : Array Name := #[
    `Paper.BonehShoupPart1.OneTimePad.theorem2_2_otp_perfect_security,
    `Paper.BonehShoupPart1.ParallelPRG.theorem3_2_parallel_prg_composition,
    `Paper.BonehShoupPart1.SequentialPRG.theorem3_3_sequential_prg_composition,
    `Paper.BonehShoupPart1.StatDist.theorem3_11_statDist_bounds_distAdv,
    `Paper.BonehShoupPart1.DiffLemma.theorem4_7_difference_lemma
  ]
  let env ← getEnv
  for d in decls do
    let reg := Informalization.Core.Register.effectiveRegister env d
    if reg != .gameBased then
      throwError "Expected gameBased register for {d}, got {repr reg}"
  let doc : Informalization.Core.Explanation.Document ←
    Informalization.Render.Json.buildDocument
      "Boneh–Shoup: Foundations and Pseudorandom Generators"
      (some "Theorems 2.2, 3.2, 3.3, 3.11, and 4.7")
      decls
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  IO.FS.createDirAll outDir
  let jsonStr := Informalization.Render.Json.renderDocumentJson doc
  let htmlStr := Informalization.Render.Html.renderDocumentHtml doc
  IO.FS.writeFile (outDir / "boneh_shoup_part1.json") jsonStr
  IO.FS.writeFile (outDir / "boneh_shoup_part1.html") htmlStr
  let leaks := Informalization.Core.Hygiene.auditZeroLeakage #[jsonStr]
  if !leaks.isEmpty then
    throwError "auditZeroLeakage failed: {leaks}"
  IO.println s!"Paper.BonehShoupPart1: exported {doc.entries.size} entries, auditZeroLeakage = {leaks.size}"

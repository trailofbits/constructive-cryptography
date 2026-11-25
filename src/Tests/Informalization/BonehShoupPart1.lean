/-
Copyright (c) 2026 Research Team. All rights reserved.
Released under Apache 2.0 license.
Authors: Boneh–Shoup Foundations Formalization Team
-/
import Informalization.Verbose
import Informalization.Render.Json
import Informalization.Render.Html
import Informalization.CLI
import Informalization.Core.Hygiene
import Probability.Distribution
import Probability.StatisticalDistance
import Probability.Expectation
import Probability.DependentProduct
import RandomSystems.Distance.Transcript

/-!
# Boneh–Shoup Foundations (Part 1: Perfect Security, PRGs, Statistical Distance, and the Difference Lemma)

Formalizations and structured cryptographic proofs for five foundational theorems from
Boneh & Shoup, *A Graduate Course in Applied Cryptography*:

1. **Theorem 2.2** — *Perfect Security of the One-Time Pad* (§2.1)
2. **Theorem 3.2** — *Parallel Composition of Pseudorandom Generators* (§3.4.1)
3. **Theorem 3.3** — *Sequential Composition of Pseudorandom Generators* (§3.4.2)
4. **Theorem 3.11** — *Statistical Distance Bounds Distinguishing Advantage* (§3.11)
5. **Theorem 4.7** — *The Difference Lemma* (§4.4.3)
-/

namespace Tests.Informalization.BonehShoupPart1

open Probability
open Probability.Distribution
open scoped VerboseCC Probability.CryptoNotation

/-!
## Shared Probability Helpers (Boneh–Shoup Notation Layer)
-/

open Informalization.Core.Presentation Informalization.Core.ContextProfile

section SharedHelpers

@[math_notation "#1\\!\\left[#2\\right]"]
noncomputable def probOf {Ω : Type} (P : ProbDist Ω) (E : Ω → Prop) : ℝ :=
  P.val.mass E

/-- Expectation of `f` under distribution `P`. -/
@[math_notation "\\mathbb{E}_{#1}\\!\\left[#2\\right]"]
noncomputable def expectOf {Ω : Type} (P : ProbDist Ω) (f : Ω → ℝ) : ℝ :=
  P.val.expect f

/-- Pushforward distribution of `f` applied to `P`. -/
noncomputable def pushDist {A B : Type} (P : ProbDist A) (f : A → B) : ProbDist B :=
  ⟨P.val.fTransform f, Distribution.fTransform_isProbDist f P.property⟩

/-- Product probability distribution on finite types `A × B`. -/
noncomputable def pairDist {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (Q : ProbDist B) : ProbDist (A × B) :=
  ⟨Finsupp.onFinset Finset.univ (fun ab : A × B => P.val ab.1 * Q.val ab.2)
    (fun _ _ => Finset.mem_univ _), by
    refine ⟨fun ab => ?_, ?_⟩
    · simp only [Finsupp.onFinset_apply]
      exact mul_nonneg (P.property.1 ab.1) (Q.property.1 ab.2)
    · simp only [Distribution.weight]
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp only [Finsupp.onFinset_apply, Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      have hQ : ∑ b : B, Q.val b = 1 := by
        simpa [Distribution.weight, Finsupp.sum_fintype] using Q.property.2
      simp_rw [hQ, mul_one]
      simpa [Distribution.weight, Finsupp.sum_fintype] using P.property.2⟩

private lemma weight_eq_sum {A : Type} [Fintype A] (X : Distribution A) :
    X.weight = ∑ a : A, X a := by
  simp [Distribution.weight, Finsupp.sum_fintype]

private lemma probDist_sum_eq_one {A : Type} [Fintype A] (P : ProbDist A) :
    ∑ a : A, P.val a = 1 := by
  rw [← weight_eq_sum]
  exact P.property.2

private lemma expectOf_eq_sum {A : Type} [Fintype A] (P : ProbDist A) (f : A → ℝ) :
    expectOf P f = ∑ a : A, P.val a * f a := by
  simp only [expectOf, Distribution.expect]
  exact Finsupp.sum_fintype _ _ (fun _ => by simp)

private lemma pushDist_apply {A B : Type} [Fintype A] (P : ProbDist A) (f : A → B) (b : B) :
    (pushDist P f).val b = ∑ a : A, @ite ℝ (f a = b) (Classical.propDecidable _) (P.val a) 0 := by
  classical
  change (Distribution.fTransform f P.val) b = _
  dsimp only [Distribution.fTransform]
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Finsupp.single_apply]

private lemma pairDist_apply {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (Q : ProbDist B) (a : A) (b : B) :
    (pairDist P Q).val (a, b) = P.val a * Q.val b := by
  simp [pairDist]

private lemma uniform_val_apply {A : Type} [Fintype A] [Nonempty A] (a : A) :
    (ProbDist.uniform A).val a = 1 / (Fintype.card A : ℝ) := by
  change (Distribution.uniform A) a = 1 / (Fintype.card A : ℝ)
  exact Distribution.uniform_apply a

/-- Two-stage sampling distribution (`bind`) on finite types. -/
noncomputable def sampleBind {A B : Type} [Fintype A] [Fintype B]
    (P : ProbDist A) (K : A → ProbDist B) : ProbDist B :=
  ⟨Finsupp.onFinset Finset.univ (fun b => ∑ a : A, P.val a * (K a).val b)
    (fun _ _ => Finset.mem_univ _), by
    refine ⟨fun b => ?_, ?_⟩
    · simp only [Finsupp.onFinset_apply]
      exact Finset.sum_nonneg fun a _ =>
        mul_nonneg (P.property.1 a) ((K a).property.1 b)
    · simp only [Distribution.weight]
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp only [Finsupp.onFinset_apply]
      rw [Finset.sum_comm]
      have hInner : ∀ a : A, ∑ b : B, P.val a * (K a).val b = P.val a := fun a => by
        rw [← Finset.mul_sum, probDist_sum_eq_one (K a), mul_one]
      simp_rw [hInner]
      exact probDist_sum_eq_one P⟩

/-- Point-mass (deterministic) probability distribution concentrated at `x`. -/
noncomputable def pureDist {A : Type} (x : A) : ProbDist A :=
  ⟨Finsupp.single x 1, by
    refine ⟨fun a => ?_, ?_⟩
    · classical
      by_cases h : x = a <;> simp [h]
    · simp [Distribution.weight]⟩

private lemma pureDist_apply {A : Type} (x a : A) :
    (pureDist x).val a = @ite ℝ (x = a) (Classical.propDecidable (x = a)) 1 0 := by
  classical
  simp [pureDist, Finsupp.single_apply]

/-- Independent product distribution over `Fin n → R`. -/
noncomputable def vecDist {n : ℕ} {R : Type} [Fintype R] (μ : Fin n → ProbDist R) :
    ProbDist (Fin n → R) :=
  ⟨Finsupp.onFinset Finset.univ (fun v => ∏ i : Fin n, (μ i).val (v i))
    (fun _ _ => Finset.mem_univ _), by
    refine ⟨fun v => ?_, ?_⟩
    · simp only [Finsupp.onFinset_apply]
      exact Finset.prod_nonneg fun i _ => (μ i).property.1 (v i)
    · simp only [Distribution.weight]
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
      simp only [Finsupp.onFinset_apply]
      rw [← Fintype.prod_sum]
      exact Finset.prod_eq_one fun i _ => probDist_sum_eq_one (μ i)⟩

private lemma vecDist_apply {n : ℕ} {R : Type} [Fintype R]
    (μ : Fin n → ProbDist R) (v : Fin n → R) :
    (vecDist μ).val v = ∏ i : Fin n, (μ i).val (v i) := by
  simp [vecDist]

informal_symbol probOf "\\Pr"
informal_symbol expectOf "\\mathbb{E}"
informal_symbol pushDist "\\mathrm{Map}"
informal_symbol pairDist "\\times"
informal_symbol vecDist "\\bigotimes"

lemma probOf_mono {Ω : Type} (P : ProbDist Ω) {E F : Ω → Prop}
    (h : ∀ ω, E ω → F ω) : probOf P E ≤ probOf P F :=
  Distribution.mass_mono P.property.1 h

lemma probOf_nonneg {Ω : Type} (P : ProbDist Ω) (E : Ω → Prop) : 0 ≤ probOf P E := by
  have hFalse : probOf P (fun _ => False) = 0 := by
    simp [probOf, Distribution.mass]
  have hle : probOf P (fun _ => False) ≤ probOf P E :=
    probOf_mono P (fun _ h => False.elim h)
  linarith

lemma probOf_congr {Ω : Type} (P : ProbDist Ω) {E F : Ω → Prop}
    (h : ∀ ω, E ω ↔ F ω) : probOf P E = probOf P F :=
  Distribution.mass_congr P.val h

lemma probOf_split {Ω : Type} (P : ProbDist Ω) (Z W : Ω → Prop) :
    probOf P (fun ω => W ω ∧ Z ω) + probOf P (fun ω => W ω ∧ ¬ Z ω) = probOf P W := by
  have h1 : probOf P (fun ω => W ω ∧ Z ω) = probOf P (fun ω => Z ω ∧ W ω) :=
    probOf_congr P (fun ω => and_comm)
  have h2 : probOf P (fun ω => W ω ∧ ¬ Z ω) = probOf P (fun ω => ¬ Z ω ∧ W ω) :=
    probOf_congr P (fun ω => and_comm)
  rw [h1, h2]
  exact Distribution.mass_and_add_mass_not_and P.val Z W

informal_title probOf_mono "monotonicity of probability"
informal_opaque probOf_mono
informal_title probOf_nonneg "nonnegativity of probability"
informal_opaque probOf_nonneg
informal_title probOf_congr "extensional equality of event probabilities"
informal_opaque probOf_congr
informal_title probOf_split "law of total probability over an event and its complement"
informal_opaque probOf_split

end SharedHelpers

/-!
## 1. Theorem 2.2 — Perfect Security of the One-Time Pad (Boneh–Shoup §2.1, L1003–1011)
-/

section OneTimePadSection

paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Fixed-length bitstrings `{0,1}^L`. -/
@[paper_describe "bitstring" (plural := "bitstrings") (carrier := false) (qualifier := "of length {L}"),
  math_notation "\\{0, 1\\}^{#1}"]
abbrev BitString (L : ℕ) : Type := Fin L → Bool

informal_symbol BitString "\\mathrm{Bits}"

/-- Bitwise XOR on `{0,1}^L`. -/
@[math_notation "#1 \\oplus #2"]
def xorBits {L : ℕ} (x y : BitString L) : BitString L :=
  fun i => xor (x i) (y i)

informal_symbol xorBits "\\oplus"

private lemma xorBits_comm {L : ℕ} (x y : BitString L) : xorBits x y = xorBits y x := by
  funext i
  exact Bool.xor_comm (x i) (y i)

informal_title xorBits_comm "commutativity of XOR"

private lemma xorBits_self_right {L : ℕ} (x y : BitString L) :
    xorBits (xorBits x y) y = x := by
  funext i
  simp [xorBits]

informal_title xorBits_self_right "XOR self-cancellation"

lemma xorBits_eq_iff {L : ℕ} (k m c : BitString L) :
    xorBits k m = c ↔ k = xorBits m c := by
  constructor
  · intro h
    calc
      k = xorBits (xorBits k m) m := (xorBits_self_right k m).symm
      _ = xorBits c m := by rw [h]
      _ = xorBits m c := xorBits_comm c m
  · intro h
    calc
      xorBits k m = xorBits (xorBits m c) m := by rw [h]
      _ = xorBits (xorBits c m) m := by rw [xorBits_comm m c]
      _ = c := xorBits_self_right c m

informal_title xorBits_eq_iff "XOR key inversion"

/-- A Shannon cipher `(E, D)` over key space `K`, message space `M`, and ciphertext space `C`. -/
@[paper_describe "Shannon cipher" (plural := "Shannon ciphers") (carrier := false)
  (varStyle := .mathcal) (qualifier := "over ({K}, {M}, {C})")]
structure ShannonCipher (K M C : Type) where
  enc : K → M → C
  dec : K → C → M
  correct : ∀ k m, dec k (enc k m) = m

attribute [math_opaque] ShannonCipher.enc ShannonCipher.dec
informal_symbol ShannonCipher.enc "E"
informal_symbol ShannonCipher.dec "D"

/-- The one-time pad over `L`-bit strings (`K = M = C = {0,1}^L`). -/
@[math_notation "\\mathcal{E}_{\\mathrm{OTP}}" (hide := [0])]
def oneTimePad (L : ℕ) : ShannonCipher (BitString L) (BitString L) (BitString L) where
  enc := xorBits
  dec := xorBits
  correct k m := by
    funext i
    simp [xorBits]

informal_symbol oneTimePad "\\mathcal{E}_{\\mathrm{OTP}}"

/-- Ciphertext distribution `E(k, m)` for a uniformly chosen key `k ← 𝒰[K]`. -/
noncomputable def cipherDist {K M C : Type} [Fintype K] [Nonempty K]
    (E : ShannonCipher K M C) (m : M) : ProbDist C :=
  pushDist (ProbDist.uniform K) (fun k => E.enc k m)

/-- A Shannon cipher is perfectly secure if every pair of messages induces the same
    ciphertext distribution under uniform key sampling. -/
@[math_pred "is perfectly secure"]
def PerfectlySecure {K M C : Type} [Fintype K] [Nonempty K]
    (E : ShannonCipher K M C) : Prop :=
  ∀ m₀ m₁ : M, ∀ c : C, (cipherDist E m₀).val c = (cipherDist E m₁).val c

/-- Number of keys `k ∈ K` mapping message `m` to ciphertext `c`: `|{k ∈ K : E(k, m) = c}|`. -/
@[math_notation "\\left|\\{k : #1\\!\\left(k, #2\\right) = #3\\}\\right|"]
noncomputable def keyFiberCount {K M C : Type} [Fintype K] [DecidableEq C]
    (E : ShannonCipher K M C) (m : M) (c : C) : ℕ :=
  (Finset.univ.filter (fun k => E.enc k m = c)).card

informal_symbol keyFiberCount "\\#\\mathrm{Keys}"

private lemma keyFiberCount_eq_one_of_unique {K M C : Type} [Fintype K] [DecidableEq K]
    [DecidableEq C] (E : ShannonCipher K M C) (m : M) (c : C) (k₀ : K)
    (huniq : ∀ k : K, E.enc k m = c ↔ k = k₀) :
    keyFiberCount E m c = 1 := by
  unfold keyFiberCount
  have hset : Finset.univ.filter (fun k => E.enc k m = c) = ({k₀} : Finset K) := by
    ext k
    simp [huniq k]
  rw [hset, Finset.card_singleton]

informal_title keyFiberCount_eq_one_of_unique "unique preimage gives fiber size 1"

private lemma cipherDist_apply_eq_fiber {K M C : Type} [Fintype K] [Nonempty K] [DecidableEq C]
    (E : ShannonCipher K M C) (m : M) (c : C) :
    (cipherDist E m).val c = (keyFiberCount E m c : ℝ) / (Fintype.card K : ℝ) := by
  unfold cipherDist pushDist keyFiberCount
  exact Distribution.fTransform_uniform_apply (fun k => E.enc k m) c

/-- **Theorem 2.1 (Condition (ii), Boneh–Shoup L979–1001):** If for every ciphertext `c`
    there exists a constant `N_c` such that `|{k ∈ K : E(k, m) = c}| = N_c` for all
    messages `m`, then `E` is perfectly secure. -/
@[math_opaque]
theorem theorem2_1_perfect_security_of_const_fiber
    {K M C : Type} [Fintype K] [Nonempty K] [DecidableEq C]
    (E : ShannonCipher K M C)
    (hConst : ∀ c : C, ∃ N_c : ℕ, ∀ m : M, keyFiberCount E m c = N_c) :
    PerfectlySecure E := by
  intro m₀ m₁ c
  obtain ⟨N_c, hNc⟩ := hConst c
  rw [cipherDist_apply_eq_fiber E m₀ c, cipherDist_apply_eq_fiber E m₁ c, hNc m₀, hNc m₁]

informal_title theorem2_1_perfect_security_of_const_fiber "Theorem 2.1 (Condition (ii))"
informal_kind theorem2_1_perfect_security_of_const_fiber "Theorem"

/-- **Theorem 2.2 (Boneh–Shoup §2.1):**
    The one-time pad is a perfectly secure Shannon cipher. -/
theorem theorem2_2_otp_perfect_security (L : ℕ)
    (E : ShannonCipher (BitString L) (BitString L) (BitString L))
    (hOTP : E = oneTimePad L) :
    PerfectlySecure E := by
  We claim hUnique : ∀ m c : BitString L, keyFiberCount E m c = 1
    explaining "since for any fixed message $m$ and ciphertext $c$ in ${BitString L}, the unique key $k$ satisfying $k \\oplus m = c$ under ${oneTimePad L} is $k = m \\oplus c$" by
    subst hOTP
    intro m c
    exact keyFiberCount_eq_one_of_unique (oneTimePad L) m c (xorBits m c)
      (fun k => xorBits_eq_iff k m c)
  We conclude "Therefore ${E} satisfies condition (ii) in Theorem 2.1 with constant key-fiber size $N_c =$ ${(1 : ℕ)} for every ciphertext" by
    exact theorem2_1_perfect_security_of_const_fiber E (fun c => ⟨1, fun m => hUnique m c⟩)

informal_title theorem2_2_otp_perfect_security "Perfect Security of the One-Time Pad"
informal_kind theorem2_2_otp_perfect_security "Theorem"
informal_section theorem2_2_otp_perfect_security
  "Section 2.1 — Perfect Security and the One-Time Pad"
informal_section_prelude theorem2_2_otp_perfect_security
  "definition"
  "Definition 2.1"
  "Shannon Cipher and Perfect Security"
  "A Shannon cipher $\\mathcal{E} = (E, D)$ over key space $\\mathcal{K}$, message space $\\mathcal{M}$, and ciphertext space $\\mathcal{C}$ consists of an encryption map $E : \\mathcal{K} \\times \\mathcal{M} \\to \\mathcal{C}$ and a decryption map $D : \\mathcal{K} \\times \\mathcal{C} \\to \\mathcal{M}$ satisfying correctness $D(k, E(k, m)) = m$ for all $k \\in \\mathcal{K}$ and $m \\in \\mathcal{M}$.\n\nFor finite nonempty $\\mathcal{K}$, $\\mathcal{E}$ is perfectly secure if for all $m_0, m_1 \\in \\mathcal{M}$ and all $c \\in \\mathcal{C}$, uniform key sampling $k \\leftarrow \\mathcal{U}[\\mathcal{K}]$ yields $\\Pr[E(k, m_0) = c] = \\Pr[E(k, m_1) = c]$. By Theorem 2.1 (Condition (ii)), $\\mathcal{E}$ is perfectly secure whenever for every $c \\in \\mathcal{C}$ there exists a constant $N_c \\in \\mathbb{N}$ such that $|\\{k \\in \\mathcal{K} : E(k, m) = c\\}| = N_c$ for all $m \\in \\mathcal{M}$."
informal_section_prelude theorem2_2_otp_perfect_security
  "construction"
  "Construction 2.1"
  "One-Time Pad"
  "For a bit-length parameter $L \\in \\mathbb{N}$, the one-time pad $\\mathcal{E}_{\\mathrm{OTP}} = (E, D)$ is defined over $\\mathcal{K} = \\mathcal{M} = \\mathcal{C} = \\{0, 1\\}^L$ by bitwise exclusive-OR, where $(k \\oplus m) \\oplus m = k$ and $x \\oplus y = y \\oplus x$ ensure $D(k, E(k, m)) = m$:\n> $E(k, m) := k \\oplus m$\n> $D(k, c) := k \\oplus c$"

end OneTimePadSection

/-!
## 2. Theorem 3.2 — Parallel Composition of PRGs (Boneh–Shoup §3.4.1)
-/

section ParallelPRGSection

paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Finite `n`-tuple space `R^n = Fin n → R`. -/
@[paper_describe "tuple" (plural := "tuples") (carrier := false) (qualifier := "of length {n} over {R}"),
  math_notation "{#2}^{#1}"]
abbrev VecSpace (n : ℕ) (R : Type) : Type := Fin n → R

informal_symbol VecSpace "\\mathrm{Tuple}"

/-- A probabilistic adversary attacking a PRG with output space `R` in Attack Game 3.1,
    returning `{0,1}` (`true` or `false`) on any challenge `r ∈ R`. -/
@[paper_describe "PRG adversary" (plural := "PRG adversaries") (carrier := false)
  (varStyle := .mathcal) (qualifier := "against outputs in {R}")]
structure PRGAdversary (R : Type) where
  run : R → ProbDist Bool

attribute [math_notation "#1\\!\\left(#2\\right)"] PRGAdversary.run

/-- Experiment 0 win probability `Pr[W₀] = Pr[A(G(s)) = 1]` for `s ← 𝒰[S]`. -/
@[math_notation "\\Pr_{0}\\!\\left[#1, #2\\right]"]
noncomputable def prgExp0 {S R : Type} [Fintype S] [Nonempty S]
    (A : PRGAdversary R) (G : S → R) : ℝ :=
  expectOf (ProbDist.uniform S) (fun s => (A.run (G s)).val true)

/-- Experiment 1 win probability `Pr[W₁] = Pr[A(r) = 1]` for `r ← 𝒰[R]`. -/
@[math_notation "\\Pr_{1}\\!\\left[#1\\right]"]
noncomputable def prgExp1 {R : Type} [Fintype R] [Nonempty R]
    (A : PRGAdversary R) : ℝ :=
  expectOf (ProbDist.uniform R) (fun r => (A.run r).val true)

/-- Attack Game 3.1 advantage `PRGadv[A, G] = |Pr[W₀] - Pr[W₁]|`. -/
@[math_notation "\\mathrm{PRGadv}\\!\\left[#1, #2\\right]"]
noncomputable def prgAdv {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    (A : PRGAdversary R) (G : S → R) : ℝ :=
  |prgExp0 A G - prgExp1 A|

/-- The `n`-fold parallel composition `G'(s₁, ..., sₙ) = (G(s₁), ..., G(sₙ))`. -/
@[math_notation "#1^{\\parallel #2}"]
def parallelPRG {S R : Type} (G : S → R) (n : ℕ) : VecSpace n S → VecSpace n R :=
  fun s i => G (s i)

/-- Coordinate distribution for `Hybrid j` (`0 ≤ j ≤ n`):
    coordinates `i < j` are uniformly distributed in `R`,
    while coordinates `i ≥ j` are distributed as `G(s)` for `s ← 𝒰[S]`. -/
noncomputable def parallelHybridCoord {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (G : S → R) (j : ℕ) (i : Fin n) : ProbDist R :=
  if i.val < j then ProbDist.uniform R else pushDist (ProbDist.uniform S) G

/-- Joint vector distribution `Hybrid^‖ j` over `R^n`: product over `i ∈ Fin n`
    of `parallelHybridCoord`. -/
@[math_notation "\\mathbf{Hybrid}^{\\parallel}_{#1}" (hide := [0, 1])]
noncomputable def parallelHybridDist {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] (G : S → R) (n j : ℕ) : ProbDist (Fin n → R) :=
  vecDist (fun i : Fin n => parallelHybridCoord G j i)

/-- Winning probability `p^‖_j = Pr[A(x) = 1]` when `x` is drawn from `Hybrid^‖ j`. -/
@[math_notation "p^{\\parallel}_{#1}" (hide := [0, 1])]
noncomputable def parallelHybridProb {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R) (j : ℕ) : ℝ :=
  expectOf (parallelHybridDist G n j) (fun vec => (A.run vec).val true)

/-- Reduction vector assembly in Figure 3.5:
    given index `ω ∈ {0, ..., n-1}`, challenge `r ∈ R`, random prefix/tail `rVec ∈ R^n`,
    and seed vector `sVec ∈ S^n`, form
    `(r₁, ..., r_{ω-1}, r, G(s_{ω+1}), ..., G(sₙ))`. -/
def parallelSplice {S R : Type} (G : S → R) (n : ℕ) (ω : Fin n) (r : R)
    (rVec : Fin n → R) (sVec : Fin n → S) : Fin n → R :=
  fun i =>
    if i.val < ω.val then rVec i
    else if i = ω then r
    else G (sVec i)

/-- Reduction adversary `B` from Boneh–Shoup Figure 3.5:
    given challenge `r ∈ R`, sample `ω ← 𝒰[Fin n]`, `rVec ← 𝒰[R^n]`, `sVec ← 𝒰[S^n]`,
    and run `A` on `parallelSplice G n ω r rVec sVec`. -/
@[math_notation "\\mathrm{Red}_{\\mathrm{par}}\\!\\left(#1, #2\\right)"]
noncomputable def parallelReduction {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R)
    (hn : 0 < n) : PRGAdversary R where
  run r :=
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    sampleBind (ProbDist.uniform (Fin n)) fun ω =>
      sampleBind (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
        fun rs =>
          A.run (parallelSplice G n ω r rs.1 rs.2)

/-! Internal product/coordinate lemmas for Theorem 3.2 (marked opaque for Paper mode). -/

private lemma expect_uniform_push {A B : Type} [Fintype A] [Nonempty A]
    (f : A → B) (φ : B → ℝ) :
    expectOf (pushDist (ProbDist.uniform A) f) φ =
      expectOf (ProbDist.uniform A) (fun a => φ (f a)) := by
  unfold expectOf pushDist
  exact Distribution.expect_fTransform (ProbDist.uniform A).val f φ

private lemma parallelHybridProb_zero {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R) :
    parallelHybridProb A G 0 = prgExp0 A (parallelPRG G n) := by
  classical
  unfold parallelHybridProb prgExp0 expectOf parallelHybridDist
  have hdist :
      vecDist (fun i : Fin n => parallelHybridCoord G (n := n) 0 i) =
        pushDist (ProbDist.uniform (Fin n → S)) (parallelPRG G n) := by
    ext v
    rw [vecDist_apply, pushDist_apply]
    simp only [parallelHybridCoord, Nat.not_lt_zero, ↓reduceIte]
    have hU : ∀ s : Fin n → S,
        (ProbDist.uniform (Fin n → S)).val s =
          ∏ i : Fin n, (ProbDist.uniform S).val (s i) := by
      intro s
      simp [uniform_val_apply]
    have hfactor : ∀ s : Fin n → S,
        (@ite ℝ (parallelPRG G n s = v) (Classical.propDecidable _)
          ((ProbDist.uniform (Fin n → S)).val s) 0) =
          ∏ i : Fin n, if G (s i) = v i then (ProbDist.uniform S).val (s i) else 0 := by
      intro s
      by_cases h : parallelPRG G n s = v
      · have hi : ∀ i : Fin n, G (s i) = v i := fun i => congrFun h i
        simp only [h, ↓reduceIte, hU]
        exact Finset.prod_congr rfl fun i _ => by simp only [hi i, ↓reduceIte]
      · have hex : ∃ i : Fin n, G (s i) ≠ v i := by
          by_contra hall
          push Not at hall
          exact h (funext hall)
        obtain ⟨i₀, hi₀⟩ := hex
        simp only [h, ↓reduceIte]
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp only [hi₀, ↓reduceIte])
    calc
      ∏ i : Fin n, (pushDist (ProbDist.uniform S) G).val (v i)
          = ∏ i : Fin n, ∑ si : S, @ite ℝ (G si = v i) (Classical.propDecidable _)
              ((ProbDist.uniform S).val si) 0 := by
            refine Finset.prod_congr rfl fun i _ => ?_
            rw [pushDist_apply]
      _ = ∑ s : Fin n → S, ∏ i : Fin n,
            @ite ℝ (G (s i) = v i) (Classical.propDecidable _) ((ProbDist.uniform S).val (s i)) 0 := by
            exact Fintype.prod_sum (fun i si =>
              @ite ℝ (G si = v i) (Classical.propDecidable _) ((ProbDist.uniform S).val si) 0)
      _ = ∑ s : Fin n → S, @ite ℝ (parallelPRG G n s = v) (Classical.propDecidable _)
            ((ProbDist.uniform (Fin n → S)).val s) 0 := by
            refine Finset.sum_congr rfl fun s _ => ?_
            symm
            convert hfactor s
  rw [hdist]
  exact expect_uniform_push (parallelPRG G n) (fun vec => (A.run vec).val true)

private lemma parallelHybridProb_n {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R) :
    parallelHybridProb A G n = prgExp1 A := by
  unfold parallelHybridProb prgExp1 expectOf parallelHybridDist
  have hdist :
      vecDist (fun i : Fin n => parallelHybridCoord G (n := n) n i) =
        ProbDist.uniform (Fin n → R) := by
    ext v
    rw [vecDist_apply, uniform_val_apply]
    have hcoord : ∀ i : Fin n,
        (parallelHybridCoord G (n := n) n i).val (v i) = 1 / (Fintype.card R : ℝ) := by
      intro i
      simp [parallelHybridCoord, i.isLt, uniform_val_apply]
    simp [hcoord]
  rw [hdist]

private lemma parallelSplice_expect_eq {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] (G : S → R) (n : ℕ) (ω : Fin n) (r : R)
    (φ : (Fin n → R) → ℝ) :
    expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
        (fun rs => φ (parallelSplice G n ω r rs.1 rs.2)) =
      expectOf (vecDist (Function.update
        (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r))) φ := by
  classical
  let μ : Fin n → ProbDist R := Function.update
    (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)
  have hpush :
      pushDist (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
          (fun rs : (Fin n → R) × (Fin n → S) => parallelSplice G n ω r rs.1 rs.2) =
        vecDist μ := by
    ext v
    rw [pushDist_apply, vecDist_apply]
    have hU : ∀ (rv : Fin n → R) (sv : Fin n → S),
        (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S))).val (rv, sv) =
          (∏ i : Fin n, (ProbDist.uniform R).val (rv i)) *
            (∏ i : Fin n, (ProbDist.uniform S).val (sv i)) := by
      intro rv sv
      simp only [pairDist_apply, uniform_val_apply, Fintype.card_fun,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.cast_pow, one_div]
      ring
    have hfactor : ∀ (rv : Fin n → R) (sv : Fin n → S),
        (if parallelSplice G n ω r rv sv = v then
          (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S))).val (rv, sv)
         else 0) =
        (∏ i : Fin n,
          (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
           else (ProbDist.uniform R).val (rv i))) *
        (∏ i : Fin n,
          (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
           else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
           else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) := by
      intro rv sv
      have hcoordMatch :
          parallelSplice G n ω r rv sv = v ↔
            (∀ i : Fin n,
              (i.val < ω.val → rv i = v i) ∧
              (¬ i.val < ω.val → i = ω → r = v i) ∧
              (¬ i.val < ω.val → i ≠ ω → G (sv i) = v i)) := by
        constructor
        · intro h i
          have hi := congrFun h i
          dsimp [parallelSplice] at hi
          refine ⟨fun hlt => ?_, fun hnot heq => ?_, fun hnot hne => ?_⟩
          · simpa [hlt] using hi
          · simpa [hnot, heq] using hi
          · simpa [hnot, hne] using hi
        · intro h
          funext i
          obtain ⟨h1, h2, h3⟩ := h i
          dsimp [parallelSplice]
          split_ifs with hlt heq
          · exact h1 hlt
          · exact h2 hlt heq
          · exact h3 hlt heq
      by_cases h : parallelSplice G n ω r rv sv = v
      · simp only [h, ↓reduceIte, hU]
        have hm := hcoordMatch.mp h
        have hrProd :
            (∏ i : Fin n,
              (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
               else (ProbDist.uniform R).val (rv i))) =
              ∏ i : Fin n, (ProbDist.uniform R).val (rv i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hlt : i.val < ω.val
          · simp [hlt, (hm i).1 hlt]
          · simp [hlt]
        have hsProd :
            (∏ i : Fin n,
              (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
               else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
               else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) =
              ∏ i : Fin n, (ProbDist.uniform S).val (sv i) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          by_cases hlt : i.val < ω.val
          · simp [hlt]
          · by_cases heq : i = ω
            · simp [heq, (hm i).2.1 hlt heq]
            · simp [hlt, heq, (hm i).2.2 hlt heq]
        rw [hrProd, hsProd]
      · simp only [h, ↓reduceIte]
        have hnot : ∃ i : Fin n, ¬ (
            (i.val < ω.val → rv i = v i) ∧
            (¬ i.val < ω.val → i = ω → r = v i) ∧
            (¬ i.val < ω.val → i ≠ ω → G (sv i) = v i)) := by
          by_contra hall
          push Not at hall
          exact h (hcoordMatch.mpr fun i => by
            obtain ⟨a, b, c⟩ := hall i
            exact ⟨a, fun h' => b (Nat.le_of_not_lt h'), fun h' => c (Nat.le_of_not_lt h')⟩)
        obtain ⟨i₀, hi₀⟩ := hnot
        by_cases hlt : i₀.val < ω.val
        · have hne : rv i₀ ≠ v i₀ := fun he => hi₀ ⟨fun _ => he,
            fun hn => absurd hlt hn, fun hn => absurd hlt hn⟩
          have hz : (∏ i : Fin n,
              (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
               else (ProbDist.uniform R).val (rv i))) = 0 :=
            Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hlt, hne])
          rw [hz, zero_mul]
        · by_cases heq : i₀ = ω
          · have hne : r ≠ v i₀ := fun he => hi₀ ⟨fun hlt' => absurd hlt' hlt,
              fun _ _ => he, fun _ hne' => absurd heq hne'⟩
            subst heq
            have hz : (∏ i : Fin n,
                (if i.val < i₀.val then (ProbDist.uniform S).val (sv i)
                 else if i = i₀ then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
                 else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hne])
            rw [hz, mul_zero]
          · have hne : G (sv i₀) ≠ v i₀ := fun he => hi₀ ⟨fun hlt' => absurd hlt' hlt,
              fun _ heq' => absurd heq' heq, fun _ _ => he⟩
            have hz : (∏ i : Fin n,
                (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
                 else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
                 else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) = 0 :=
              Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hlt, heq, hne])
            rw [hz, mul_zero]
    have hSumFactored :
        (∑ x : Fin n → R, ∑ y : Fin n → S,
          @ite ℝ (parallelSplice G n ω r x y = v) (Classical.propDecidable _)
            ((pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S))).val (x, y)) 0) =
        ∑ rv : Fin n → R, ∑ sv : Fin n → S,
          (∏ i : Fin n,
            (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
             else (ProbDist.uniform R).val (rv i))) *
          (∏ i : Fin n,
            (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
             else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
             else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) :=
      Finset.sum_congr rfl fun rv _ => Finset.sum_congr rfl fun sv _ => by convert hfactor rv sv
    rw [Fintype.sum_prod_type]
    refine hSumFactored.trans ?_
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    have hsumR : (∑ rv : Fin n → R,
        ∏ i : Fin n,
          (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
           else (ProbDist.uniform R).val (rv i))) =
        ∏ i : Fin n,
          if i.val < ω.val then (ProbDist.uniform R).val (v i) else 1 := by
      have hSwapR :
          (∑ rv : Fin n → R, ∏ i : Fin n,
            (if i.val < ω.val then (if rv i = v i then (ProbDist.uniform R).val (rv i) else 0)
             else (ProbDist.uniform R).val (rv i))) =
          ∏ i : Fin n, ∑ ri : R,
            (if i.val < ω.val then (if ri = v i then (ProbDist.uniform R).val ri else 0)
             else (ProbDist.uniform R).val ri) :=
        (Fintype.prod_sum (fun i ri =>
          if i.val < ω.val then (if ri = v i then (ProbDist.uniform R).val ri else 0)
          else (ProbDist.uniform R).val ri)).symm
      rw [hSwapR]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hlt : i.val < ω.val
      · simp [hlt]
      · simp only [hlt, ↓reduceIte]
        exact probDist_sum_eq_one (ProbDist.uniform R)
    have hsumS : (∑ sv : Fin n → S,
        ∏ i : Fin n,
          (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
           else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
           else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) =
        ∏ i : Fin n,
          (if i.val < ω.val then 1
           else if i = ω then (if r = v i then 1 else 0)
           else (pushDist (ProbDist.uniform S) G).val (v i)) := by
      have hSwapS :
          (∑ sv : Fin n → S, ∏ i : Fin n,
            (if i.val < ω.val then (ProbDist.uniform S).val (sv i)
             else if i = ω then (if r = v i then (ProbDist.uniform S).val (sv i) else 0)
             else (if G (sv i) = v i then (ProbDist.uniform S).val (sv i) else 0))) =
          ∏ i : Fin n, ∑ si : S,
            (if i.val < ω.val then (ProbDist.uniform S).val si
             else if i = ω then (if r = v i then (ProbDist.uniform S).val si else 0)
             else (if G si = v i then (ProbDist.uniform S).val si else 0)) :=
        (Fintype.prod_sum (fun i si =>
          if i.val < ω.val then (ProbDist.uniform S).val si
          else if i = ω then (if r = v i then (ProbDist.uniform S).val si else 0)
          else (if G si = v i then (ProbDist.uniform S).val si else 0))).symm
      rw [hSwapS]
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hlt : i.val < ω.val
      · simp only [hlt, ↓reduceIte]
        exact probDist_sum_eq_one (ProbDist.uniform S)
      · by_cases heq : i = ω
        · subst heq
          simp only [Nat.lt_irrefl, ↓reduceIte]
          by_cases hrv : r = v i
          · simp only [hrv, ↓reduceIte]
            exact probDist_sum_eq_one (ProbDist.uniform S)
          · simp [hrv]
        · simp only [hlt, heq, ↓reduceIte]
          rw [pushDist_apply]
    rw [hsumR, hsumS, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases heq : i = ω
    · simp [μ, heq, pureDist_apply]
    · by_cases hlt : i.val < ω.val
      · simp only [μ, Function.update_of_ne heq, parallelHybridCoord, hlt, ↓reduceIte, mul_one]
      · simp only [μ, Function.update_of_ne heq, parallelHybridCoord, hlt, heq, ↓reduceIte, one_mul]
  rw [← hpush]
  unfold expectOf pushDist
  exact (Distribution.expect_fTransform
    (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S))).val
    (fun rs : (Fin n → R) × (Fin n → S) => parallelSplice G n ω r rs.1 rs.2) φ).symm

private lemma vecDist_update_expect {R : Type} [Fintype R] [Nonempty R]
    (n : ℕ) (μ : Fin n → ProbDist R) (ω : Fin n) (P₀ : ProbDist R)
    (φ : (Fin n → R) → ℝ) :
    expectOf P₀ (fun r => expectOf (vecDist (Function.update μ ω (pureDist r))) φ) =
      expectOf (vecDist (Function.update μ ω P₀)) φ := by
  classical
  simp_rw [expectOf_eq_sum]
  have hL :
      (∑ r : R, P₀.val r * ∑ v : Fin n → R,
          (vecDist (Function.update μ ω (pureDist r))).val v * φ v) =
        ∑ v : Fin n → R, (∑ r : R, P₀.val r *
          (vecDist (Function.update μ ω (pureDist r))).val v) * φ v := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hL]
  refine Finset.sum_congr rfl fun v _ => congrArg (· * φ v) ?_
  have hprod : ∀ r : R,
      (vecDist (Function.update μ ω (pureDist r))).val v =
        (if r = v ω then (1 : ℝ) else 0) *
          ∏ i ∈ Finset.univ.erase ω, (μ i).val (v i) := by
    intro r
    rw [vecDist_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ω)]
    simp only [Function.update_self, pureDist_apply]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ ω := (Finset.mem_erase.mp hi).1
    simp [Function.update_of_ne hne]
  simp_rw [hprod]
  have hsum :
      (∑ r : R, P₀.val r * ((if r = v ω then (1 : ℝ) else 0) *
        ∏ i ∈ Finset.univ.erase ω, (μ i).val (v i))) =
      (P₀.val (v ω)) * ∏ i ∈ Finset.univ.erase ω, (μ i).val (v i) := by
    have hassoc : ∀ r : R,
        P₀.val r * ((if r = v ω then (1 : ℝ) else 0) *
          ∏ i ∈ Finset.univ.erase ω, (μ i).val (v i)) =
        (P₀.val r * (if r = v ω then (1 : ℝ) else 0)) *
          ∏ i ∈ Finset.univ.erase ω, (μ i).val (v i) := fun r => by ring
    simp_rw [hassoc, ← Finset.sum_mul]
    congr 1
    simp
  rw [hsum, vecDist_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ω)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  have hne : i ≠ ω := (Finset.mem_erase.mp hi).1
  simp [Function.update_of_ne hne]

private lemma parallelHybridCoord_update_push {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (G : S → R) (ω : Fin n) :
    Function.update (fun i : Fin n => parallelHybridCoord G ω.val i) ω
        (pushDist (ProbDist.uniform S) G) =
      fun i : Fin n => parallelHybridCoord G ω.val i := by
  funext i
  by_cases heq : i = ω
  · subst heq
    simp [parallelHybridCoord]
  · simp [Function.update_of_ne heq]

private lemma parallelHybridCoord_update_uniform {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (G : S → R) (ω : Fin n) :
    Function.update (fun i : Fin n => parallelHybridCoord G ω.val i) ω
        (ProbDist.uniform R) =
      fun i : Fin n => parallelHybridCoord G (ω.val + 1) i := by
  funext i
  by_cases heq : i = ω
  · subst heq
    simp [parallelHybridCoord]
  · have hiff : i.val < ω.val + 1 ↔ i.val < ω.val := by
      have hne : i.val ≠ ω.val := fun h => heq (Fin.ext h)
      omega
    simp [Function.update_of_ne heq, parallelHybridCoord, hiff]

private lemma sampleBind_eval_true {A : Type} [Fintype A]
    (P : ProbDist A) (K : A → ProbDist Bool) :
    (sampleBind P K).val true = expectOf P (fun a => (K a).val true) := by
  rw [expectOf_eq_sum]
  simp [sampleBind]

private lemma parallelReduction_exp0 {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R)
    (hn : 0 < n) :
    prgExp0 (parallelReduction A G hn) G =
      (1 / (n : ℝ)) * ∑ j : Fin n, parallelHybridProb A G j.val := by
  let _hnEmpty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hB : ∀ r : R, ((parallelReduction A G hn).run r).val true =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
          (fun rs => (A.run (parallelSplice G n ω r rs.1 rs.2)).val true)) := by
    intro r
    unfold parallelReduction
    rw [sampleBind_eval_true, expectOf_eq_sum, expectOf_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => congrArg ((ProbDist.uniform (Fin n)).val ω * ·) ?_
    exact sampleBind_eval_true _ _
  have hSplice : ∀ (ω : Fin n) (r : R),
      expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
        (fun rs => (A.run (parallelSplice G n ω r rs.1 rs.2)).val true) =
      expectOf (vecDist (Function.update
        (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
        (fun vec => (A.run vec).val true) :=
    fun ω r => parallelSplice_expect_eq G n ω r (fun vec => (A.run vec).val true)
  unfold prgExp0
  simp_rw [hB, hSplice]
  change expectOf (ProbDist.uniform S) (fun s =>
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (vecDist (Function.update
          (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist (G s))))
          (fun vec => (A.run vec).val true))) =
    (1 / (n : ℝ)) * ∑ j : Fin n, parallelHybridProb A G j.val
  have hSwap :
      expectOf (ProbDist.uniform S) (fun s =>
        expectOf (ProbDist.uniform (Fin n)) (fun ω =>
          expectOf (vecDist (Function.update
            (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist (G s))))
            (fun vec => (A.run vec).val true))) =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (ProbDist.uniform S) (fun s =>
          expectOf (vecDist (Function.update
            (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist (G s))))
            (fun vec => (A.run vec).val true))) := by
    simp_rw [expectOf_eq_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun s _ => ?_
    refine Finset.sum_congr rfl fun vec _ => ?_
    rw [mul_left_comm]
  rw [hSwap]
  have hInner : ∀ ω : Fin n,
      expectOf (ProbDist.uniform S) (fun s =>
        expectOf (vecDist (Function.update
          (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist (G s))))
          (fun vec => (A.run vec).val true)) =
        parallelHybridProb A G ω.val := by
    intro ω
    rw [← expect_uniform_push G (fun r =>
      expectOf (vecDist (Function.update
        (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
        (fun vec => (A.run vec).val true))]
    rw [vecDist_update_expect, parallelHybridCoord_update_push]
    rfl
  simp_rw [hInner, expectOf_eq_sum]
  simp [uniform_val_apply, ← Finset.mul_sum]

private lemma parallelReduction_exp1 {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R)
    (hn : 0 < n) :
    prgExp1 (parallelReduction A G hn) =
      (1 / (n : ℝ)) * ∑ j : Fin n, parallelHybridProb A G (j.val + 1) := by
  let _hnEmpty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hB : ∀ r : R, ((parallelReduction A G hn).run r).val true =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
          (fun rs => (A.run (parallelSplice G n ω r rs.1 rs.2)).val true)) := by
    intro r
    unfold parallelReduction
    rw [sampleBind_eval_true, expectOf_eq_sum, expectOf_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => congrArg ((ProbDist.uniform (Fin n)).val ω * ·) ?_
    exact sampleBind_eval_true _ _
  have hSplice : ∀ (ω : Fin n) (r : R),
      expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform (Fin n → S)))
        (fun rs => (A.run (parallelSplice G n ω r rs.1 rs.2)).val true) =
      expectOf (vecDist (Function.update
        (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
        (fun vec => (A.run vec).val true) :=
    fun ω r => parallelSplice_expect_eq G n ω r (fun vec => (A.run vec).val true)
  unfold prgExp1
  simp_rw [hB, hSplice]
  have hSwap :
      expectOf (ProbDist.uniform R) (fun r =>
        expectOf (ProbDist.uniform (Fin n)) (fun ω =>
          expectOf (vecDist (Function.update
            (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
            (fun vec => (A.run vec).val true))) =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (ProbDist.uniform R) (fun r =>
          expectOf (vecDist (Function.update
            (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
            (fun vec => (A.run vec).val true))) := by
    simp_rw [expectOf_eq_sum]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun r _ => ?_
    refine Finset.sum_congr rfl fun vec _ => ?_
    rw [mul_left_comm]
  rw [hSwap]
  have hInner : ∀ ω : Fin n,
      expectOf (ProbDist.uniform R) (fun r =>
        expectOf (vecDist (Function.update
          (fun i : Fin n => parallelHybridCoord G ω.val i) ω (pureDist r)))
          (fun vec => (A.run vec).val true)) =
        parallelHybridProb A G (ω.val + 1) := by
    intro ω
    rw [vecDist_update_expect, parallelHybridCoord_update_uniform]
    rfl
  simp_rw [hInner, expectOf_eq_sum]
  simp [uniform_val_apply, ← Finset.mul_sum]

private lemma parallelReduction_exp0_range {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R)
    (hn : 0 < n) :
    prgExp0 (parallelReduction A G hn) G =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G j := by
  rw [parallelReduction_exp0 A G hn, Fin.sum_univ_eq_sum_range (fun j => parallelHybridProb A G j)]

private lemma parallelReduction_exp1_range {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] {n : ℕ} (A : PRGAdversary (Fin n → R)) (G : S → R)
    (hn : 0 < n) :
    prgExp1 (parallelReduction A G hn) =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G (j + 1) := by
  rw [parallelReduction_exp1 A G hn,
    Fin.sum_univ_eq_sum_range (fun j => parallelHybridProb A G (j + 1))]

private lemma prgAdv_eq_abs {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    (A : PRGAdversary R) (G : S → R) :
    prgAdv A G = |prgExp0 A G - prgExp1 A| := rfl

informal_title prgAdv_eq_abs "definition of PRG advantage"

private lemma abs_sub_eq_of_eq {a b a' b' : ℝ} (ha : a = a') (hb : b = b') :
    |a - b| = |a' - b'| := by
  rw [ha, hb]

informal_title abs_sub_eq_of_eq "the experiment probability identities"

private lemma mul_abs_sub_eq_mul_prgAdv {S R : Type} [Fintype S] [Nonempty S]
    [Fintype R] [Nonempty R] (c : ℝ) (A : PRGAdversary R) (G : S → R)
    {p0 pn : ℝ} (h0 : p0 = prgExp0 A G) (hnEq : pn = prgExp1 A) :
    c * |p0 - pn| = c * prgAdv A G := by
  rw [h0, hnEq]
  rfl

informal_title mul_abs_sub_eq_mul_prgAdv "the boundary identities and definition of PRG advantage"

lemma scaled_telescoping_abs {n : ℕ} (p : ℕ → ℝ) :
    |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, p j -
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, p (j + 1)| =
    (1 / (n : ℝ)) * |p 0 - p n| := by
  have hInv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  calc
    |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, p j -
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, p (j + 1)|
        = |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, (p j - p (j + 1))| := by
            rw [← mul_sub, ← Finset.sum_sub_distrib]
    _ = (1 / (n : ℝ)) * |∑ j ∈ Finset.range n, (p j - p (j + 1))| := by
            rw [abs_mul, abs_of_nonneg hInv]
    _ = (1 / (n : ℝ)) * |p 0 - p n| := by
            rw [Finset.sum_range_sub' p n]

informal_title scaled_telescoping_abs "summing and cancelling adjacent hybrid differences"

lemma eq_mul_of_div_eq {n : ℕ} (hn : 0 < n) {a b : ℝ}
    (h : a = (1 / (n : ℝ)) * b) : b = (n : ℝ) * a := by
  have hnPos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  rw [h]
  field_simp

informal_title eq_mul_of_div_eq "multiplying both sides by n"

informal_symbol prgExp0 "\\Pr_0"
informal_symbol prgExp1 "\\Pr_1"
informal_symbol prgAdv "\\mathrm{PRGadv}"
informal_symbol parallelPRG "G^{\\parallel}"
informal_symbol parallelHybridDist "\\mathbf{Hybrid}^{\\parallel}"
informal_symbol parallelHybridProb "p^{\\parallel}"
informal_symbol parallelReduction "\\mathrm{Red}_{\\mathrm{par}}"
informal_title parallelHybridProb_zero "Experiment 0 equivalence with Hybrid 0"
informal_title parallelHybridProb_n "Experiment 1 equivalence with Hybrid n"
informal_title parallelReduction_exp0_range "averaging Experiment 0 over uniformly random index"
informal_title parallelReduction_exp1_range "averaging Experiment 1 over uniformly random index"

/-- **Theorem 3.2 (Boneh–Shoup §3.4.1):**
    For any PRG `G : S → R`, any `n ≥ 1`, and any adversary `A` attacking the
    `n`-fold parallel composition `G^‖(s₁, ..., sₙ) = (G(s₁), ..., G(sₙ))`,
    there exists an adversary `B` attacking `G` (where `B` is an elementary wrapper around `A`)
    such that `PRGadv[A, G^‖] = n · PRGadv[B, G]`. -/
theorem theorem3_2_parallel_prg_composition
    {S R : Type} [Fintype S] [Nonempty S] [Fintype R] [Nonempty R]
    (G : S → R) (n : ℕ) (hn : 0 < n) (A : PRGAdversary (VecSpace n R)) :
    ∃ B : PRGAdversary R,
      prgAdv A (parallelPRG G n) = (n : ℝ) * prgAdv B G := by
  Proof overview "We introduce ${n + 1} hybrid games ${parallelHybridDist G n 0} through ${parallelHybridDist G n n} interpolating between ${parallelPRG G n} and uniform ${VecSpace n R}. For each $0 \\le j \\le$ ${n}, let $p^{\\parallel}_j := \\Pr[\\mathcal{A}(\\mathbf{Hybrid}^{\\parallel}_j) = 1]$ denote the probability that ${A} outputs $1$ in Hybrid $j$. We construct a single-query reduction ${parallelReduction A G hn} (an elementary wrapper around ${A}) that embeds its challenge at a uniformly random index, and evaluate the resulting telescoping sum."
  Present pseudocode "hybrid" "Hybrid $j$ ($0 \\le j \\le n$)"
    "For each coordinate $i < j$, sample $r_i$ uniformly from ${R}\nFor each coordinate $i \\ge j$ up to ${n}, sample $s_i$ uniformly from ${S} and set $r_i$ by applying ${G} to $s_i$\nSend $(r_0, \\dots, r_{n-1})$ in ${VecSpace n R} to ${A} and output whatever ${A} outputs"
  We claim h0 : parallelHybridProb A G 0 = prgExp0 A (parallelPRG G n)
    explaining "since ${parallelHybridDist G n 0} draws fresh pseudorandom outputs on all ${n} coordinates and matches Experiment 0 of ${A} against ${parallelPRG G n}" by
    exact parallelHybridProb_zero A G
  We claim hnEq : parallelHybridProb A G n = prgExp1 A
    explaining "since ${parallelHybridDist G n n} draws all ${n} coordinates uniformly from ${R} and matches Experiment 1 of ${A}" by
    exact parallelHybridProb_n A G
  New paragraph
  Consider adversary B : PRGAdversary R := parallelReduction A G hn
    where "an elementary wrapper around ${A} making a single oracle call: given a challenge in ${R}, it samples an index uniformly from ${Fin n}, fills all earlier coordinates uniformly from ${R}, inserts the challenge at that index, generates all later coordinates via ${G} on fresh seeds from ${S}, and outputs whatever ${A} outputs"
  Present pseudocode "reduction" "Reduction $\\mathcal{B}$"
    "Upon receiving challenge $r$ in ${R}, ${B} plays the role of challenger to ${A}:\n  Sample $\\omega$ uniformly from ${Fin n}\n  For $i < \\omega$, sample $r_i$ uniformly from ${R}\n  Set $r_{\\omega} \\leftarrow r$\n  For $i > \\omega$ up to ${n}, sample $s_i$ uniformly from ${S} and set $r_i$ by applying ${G} to $s_i$\n  Send $(r_0, \\dots, r_{n-1})$ in ${VecSpace n R} to ${A} and output whatever ${A} outputs"
  We claim hB0 :
      prgExp0 B G = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G j
    explaining "since in Experiment 0 of ${B} against ${G}, conditioning on the random index places an output of ${G} at that coordinate, matching the corresponding hybrid and averaging ${parallelHybridProb A G 0} through ${parallelHybridProb A G (n - 1)}" by
    exact parallelReduction_exp0_range A G hn
  We claim hB1 :
      prgExp1 B = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G (j + 1)
    explaining "since in Experiment 1 of ${B}, conditioning on the random index places a uniform element of ${R} at that coordinate, shifting the hybrid index by one and averaging ${parallelHybridProb A G 1} through ${parallelHybridProb A G n}" by
    exact parallelReduction_exp1_range A G hn
  New paragraph
  We claim hAdv : prgAdv B G = (1 / (n : ℝ)) * prgAdv A (parallelPRG G n)
    explaining "combining both experiment averages collapses into a telescoping difference between ${parallelHybridProb A G 0} and ${parallelHybridProb A G n}" by
    calc
      prgAdv B G
          = |prgExp0 B G - prgExp1 B| := prgAdv_eq_abs B G
      _ = |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G j -
            (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, parallelHybridProb A G (j + 1)| :=
            abs_sub_eq_of_eq hB0 hB1
      _ = (1 / (n : ℝ)) * |parallelHybridProb A G 0 - parallelHybridProb A G n| :=
            scaled_telescoping_abs (parallelHybridProb A G)
      _ = (1 / (n : ℝ)) * prgAdv A (parallelPRG G n) :=
            mul_abs_sub_eq_mul_prgAdv (1 / (n : ℝ)) A (parallelPRG G n) h0 hnEq
  We conclude "We multiply both sides by ${n} and exhibit ${B}, where ${B} is an elementary wrapper around ${A}, as the reduction adversary" by
    exact ⟨B, eq_mul_of_div_eq hn hAdv⟩

informal_title theorem3_2_parallel_prg_composition
  "Parallel Composition of Pseudorandom Generators"
informal_kind theorem3_2_parallel_prg_composition "Theorem"
informal_section theorem3_2_parallel_prg_composition
  "Section 3.4.1 — Parallel Composition of Pseudorandom Generators"
informal_section_prelude theorem3_2_parallel_prg_composition
  "attackGame"
  "Attack Game 3.1"
  "Pseudorandom Generator Security"
  "For a function $G : \\mathcal{S} \\to \\mathcal{R}$ over finite nonempty sets $\\mathcal{S}, \\mathcal{R}$ and an adversary $\\mathcal{A}$ outputting a bit $\\hat{b} \\in \\{0, 1\\}$, write $\\Pr_0[\\mathcal{A}, G] := \\Pr[W_0]$ and $\\Pr_1[\\mathcal{A}] := \\Pr[W_1]$ for the probabilities that $\\mathcal{A}$ outputs $1$ in Experiments $0$ and $1$ below, and define $\\mathrm{PRGadv}[\\mathcal{A}, G] := \\left|\\Pr_0[\\mathcal{A}, G] - \\Pr_1[\\mathcal{A}]\\right|$.\n> Experiment 0:\n>   $s \\leftarrow \\mathcal{U}[\\mathcal{S}],\\; r \\leftarrow G(s)$\n>   send $r$ to $\\mathcal{A}$ and output $\\hat{b} \\in \\{0, 1\\}$\n> Experiment 1:\n>   $r \\leftarrow \\mathcal{U}[\\mathcal{R}]$\n>   send $r$ to $\\mathcal{A}$ and output $\\hat{b} \\in \\{0, 1\\}$"
informal_section_prelude theorem3_2_parallel_prg_composition
  "construction"
  "Construction 3.1"
  "Parallel Composition of a PRG"
  "Given a PRG $G : \\mathcal{S} \\to \\mathcal{R}$ and an integer $n \\ge 1$, its $n$-wise parallel composition is the function $G^{\\parallel n} : \\mathcal{S}^n \\to \\mathcal{R}^n$ defined on $(s_1, \\dots, s_n) \\in \\mathcal{S}^n$ by $$G^{\\parallel n}(s_1, \\dots, s_n) := (G(s_1), \\dots, G(s_n))$$."

end ParallelPRGSection

/-!
## 3. Theorem 3.3 — Sequential Composition of PRGs (Boneh–Shoup §3.4.2)
-/

section SequentialPRGSection

paper_context GameBasedContext

/-- Iterate a length-extending PRG `G : S → R × S` for `k` remaining steps,
    writing the resulting `R`-blocks into indices `n - k, ..., n - 1` of `buf`. -/
def seqFill {R S : Type} (G : S → R × S) (n : ℕ) :
    ℕ → (Fin n → R) → S → (Fin n → R) × S
  | 0, buf, s => (buf, s)
  | k + 1, buf, s =>
      let p := G s
      seqFill G n k (fun i => if i.val = n - (k + 1) then p.1 else buf i) p.2

set_option linter.paperPresentation true

/-- The `n`-step sequential composition `G'(s) = (r₁, ..., rₙ, sₙ)` starting from `s : S`. -/
@[math_notation "#1^{\\mathrm{seq}\\, #2}"]
noncomputable def seqPRG {R S : Type} [Nonempty R] (G : S → R × S) (n : ℕ) (s : S) :
    VecSpace n R × S :=
  seqFill G n n (fun _ => Classical.arbitrary R) s

/-- Hybrid `j` (`0 ≤ j ≤ n`) in Figure 3.6:
    sample random prefix `buf ← 𝒰[Fin n → R]` and seed `s ← 𝒰[S]`, then run `G`
    for the remaining `n - j` steps starting at position `j`. -/
@[math_notation "\\mathbf{Hybrid}^{\\mathrm{seq}}_{#1}" (hide := [0, 1])]
noncomputable def seqHybridDist {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    (G : S → R × S) (n j : ℕ) : ProbDist ((Fin n → R) × S) :=
  pushDist (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform S))
    (fun bs => seqFill G n (n - j) bs.1 bs.2)

/-- Winning probability `p^seq_j = Pr[A(x) = 1]` on `Hybrid^seq j` of sequential composition. -/
@[math_notation "p^{\\mathrm{seq}}_{#1}" (hide := [0, 1])]
noncomputable def seqHybridProb {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S) (j : ℕ) : ℝ :=
  expectOf (seqHybridDist G n j) (fun out => (A.run out).val true)

/-- Reduction adversary `B` from Boneh–Shoup Figure 3.7:
    given challenge `(r, s') ∈ R × S`, pick `ω ← 𝒰[Fin n]`, draw `buf ← 𝒰[Fin n → R]`,
    place `r` at position `ω`, iterate `G` for the remaining `n - (ω + 1)` steps from `s'`,
    and run `A`. -/
@[math_notation "\\mathrm{Red}_{\\mathrm{seq}}\\!\\left(#1, #2\\right)"]
noncomputable def seqReduction {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S)
    (hn : 0 < n) : PRGAdversary (R × S) where
  run rs :=
    letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    sampleBind (ProbDist.uniform (Fin n)) fun ω =>
      sampleBind (ProbDist.uniform (Fin n → R)) fun buf =>
        A.run (seqFill G n (n - (ω.val + 1))
          (fun i => if i.val = ω.val then rs.1 else buf i) rs.2)

private lemma seqFill_agrees_lt {R S : Type} (G : S → R × S) (n k : ℕ) (hk : k ≤ n)
    (buf₁ buf₂ : Fin n → R) (hagree : ∀ i : Fin n, i.val < n - k → buf₁ i = buf₂ i)
    (s : S) :
    seqFill G n k buf₁ s = seqFill G n k buf₂ s := by
  induction k generalizing buf₁ buf₂ s with
  | zero =>
      simp only [seqFill]
      congr 1
      funext i
      exact hagree i (by simp)
  | succ k ih =>
      simp only [seqFill]
      apply ih (Nat.le_of_succ_le hk)
      intro i hi
      by_cases heq : i.val = n - (k + 1)
      · simp [heq]
      · have hlt : i.val < n - (k + 1) := by omega
        simp [heq, hagree i hlt]

private lemma seqFill_const_full {R S : Type} [Nonempty R] (G : S → R × S) (n : ℕ)
    (buf : Fin n → R) (s : S) :
    seqFill G n n buf s = seqPRG G n s := by
  unfold seqPRG
  exact seqFill_agrees_lt G n n le_rfl buf (fun _ => Classical.arbitrary R)
    (fun i hi => by simp at hi) s

private lemma seqHybridProb_zero {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S) :
    seqHybridProb A G 0 = prgExp0 A (seqPRG G n) := by
  unfold seqHybridProb prgExp0 seqHybridDist expectOf pushDist
  rw [Distribution.expect_fTransform]
  simp only [Nat.sub_zero, Function.comp_def]
  have hfun : ∀ bs : (Fin n → R) × S,
      (A.run (seqFill G n n bs.1 bs.2)).val true = (A.run (seqPRG G n bs.2)).val true := by
    intro bs
    rw [seqFill_const_full G n bs.1 bs.2]
  simp_rw [hfun]
  change expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform S))
      (fun bs => (A.run (seqPRG G n bs.2)).val true) =
    expectOf (ProbDist.uniform S) (fun s => (A.run (seqPRG G n s)).val true)
  simp_rw [expectOf_eq_sum]
  rw [Fintype.sum_prod_type]
  have hfactor : ∀ (buf : Fin n → R) (s : S),
      (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform S)).val (buf, s) *
          (A.run (seqPRG G n s)).val true =
        (ProbDist.uniform (Fin n → R)).val buf *
          ((ProbDist.uniform S).val s * (A.run (seqPRG G n s)).val true) := by
    intro buf s
    simp only [pairDist_apply]
    ring
  simp_rw [hfactor]
  rw [Finset.sum_comm]
  have hinner : ∀ s : S,
      (∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
        ((ProbDist.uniform S).val s * (A.run (seqPRG G n s)).val true)) =
      (ProbDist.uniform S).val s * (A.run (seqPRG G n s)).val true := by
    intro s
    rw [← Finset.sum_mul, probDist_sum_eq_one (ProbDist.uniform (Fin n → R)), one_mul]
  exact Finset.sum_congr rfl fun s _ => hinner s

private lemma seqHybridProb_n {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S) :
    seqHybridProb A G n = prgExp1 A := by
  unfold seqHybridProb prgExp1 seqHybridDist expectOf pushDist
  rw [Distribution.expect_fTransform]
  simp only [Nat.sub_self, seqFill, Function.comp_def]
  change expectOf (pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform S))
      (fun bs => (A.run bs).val true) =
    expectOf (ProbDist.uniform ((Fin n → R) × S)) (fun rs => (A.run rs).val true)
  simp_rw [expectOf_eq_sum]
  refine Finset.sum_congr rfl fun ⟨buf, s⟩ _ => ?_
  simp only [pairDist_apply, uniform_val_apply, Fintype.card_prod]
  rw [Nat.cast_mul]
  ring

private lemma uniform_fin_vec_update_sum {R : Type} [Fintype R] [Nonempty R]
    (n : ℕ) (ω : Fin n) (φ : (Fin n → R) → ℝ) :
    (∑ r : R, (ProbDist.uniform R).val r *
      ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
        φ (fun i => if i.val = ω.val then r else buf i)) =
      ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf * φ buf := by
  let swapFun : R × (Fin n → R) → R × (Fin n → R) :=
    fun p => (p.2 ω, fun i => if i.val = ω.val then p.1 else p.2 i)
  have hSwapInv : Function.Involutive swapFun := by
    intro p
    ext
    · simp [swapFun]
    · dsimp only [swapFun]
      split_ifs with h
      · have hω : _ = ω := Fin.ext h
        subst hω
        rfl
      · rfl
  let swap : (R × (Fin n → R)) ≃ (R × (Fin n → R)) :=
    { toFun := swapFun
      invFun := swapFun
      left_inv := hSwapInv
      right_inv := hSwapInv }
  let c : ℝ := (Fintype.card R : ℝ)⁻¹ * (Fintype.card (Fin n → R) : ℝ)⁻¹
  have hSwapApply : ∀ q : R × (Fin n → R), swap q = swapFun q := fun _ => rfl
  have hRewrite :
      (∑ r : R, (ProbDist.uniform R).val r *
        ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
          φ (fun i => if i.val = ω.val then r else buf i)) =
        ∑ p : R × (Fin n → R), c * φ (swap p).2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun buf _ => ?_
    rw [hSwapApply]
    simp only [uniform_val_apply, one_div]
    dsimp only [swapFun, c]
    ring
  rw [hRewrite]
  have hSwapSum :
      (∑ p : R × (Fin n → R), c * φ (swap p).2) =
        ∑ q : R × (Fin n → R), c * φ q.2 :=
    Equiv.sum_comp swap (fun q : R × (Fin n → R) => c * φ q.2)
  rw [hSwapSum, Fintype.sum_prod_type]
  have hSplit :
      (∑ _r : R, ∑ buf : Fin n → R, c * φ buf) =
      ∑ r : R, (ProbDist.uniform R).val r *
        ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf * φ buf := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun buf _ => ?_
    simp only [uniform_val_apply, c, one_div]
    ring
  rw [hSplit, ← Finset.sum_mul, probDist_sum_eq_one (ProbDist.uniform R), one_mul]

private lemma seqReduction_exp0 {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S) (hn : 0 < n) :
    prgExp0 (seqReduction A G hn) G =
      (1 / (n : ℝ)) * ∑ j : Fin n, seqHybridProb A G j.val := by
  let _hnEmpty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hB : ∀ rs : R × S, ((seqReduction A G hn).run rs).val true =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (ProbDist.uniform (Fin n → R)) (fun buf =>
          (A.run (seqFill G n (n - (ω.val + 1))
            (fun i => if i.val = ω.val then rs.1 else buf i) rs.2)).val true)) := by
    intro rs
    unfold seqReduction
    rw [sampleBind_eval_true, expectOf_eq_sum, expectOf_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => congrArg ((ProbDist.uniform (Fin n)).val ω * ·) ?_
    exact sampleBind_eval_true _ _
  unfold prgExp0
  simp_rw [hB]
  have hStep : ∀ (ω : Fin n) (buf : Fin n → R) (s : S),
      seqFill G n (n - (ω.val + 1))
          (fun i => if i.val = ω.val then (G s).1 else buf i) (G s).2 =
        seqFill G n (n - ω.val) buf s := by
    intro ω buf s
    have hSub : n - ω.val = (n - (ω.val + 1)) + 1 := by omega
    rw [hSub, seqFill]
    have hIdx : n - ((n - (ω.val + 1)) + 1) = ω.val := by omega
    simp [hIdx]
  simp_rw [hStep, expectOf_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hInner : ∀ ω : Fin n,
      (∑ s : S, ∑ buf : Fin n → R,
        (ProbDist.uniform S).val s *
          ((ProbDist.uniform (Fin n)).val ω *
            ((ProbDist.uniform (Fin n → R)).val buf *
              (A.run (seqFill G n (n - ω.val) buf s)).val true))) =
      (1 / (n : ℝ)) * seqHybridProb A G ω.val := by
    intro ω
    have hFactor : ∀ (s : S) (buf : Fin n → R),
        (ProbDist.uniform S).val s *
          ((ProbDist.uniform (Fin n)).val ω *
            ((ProbDist.uniform (Fin n → R)).val buf *
              (A.run (seqFill G n (n - ω.val) buf s)).val true)) =
        (1 / (n : ℝ)) *
          ((pairDist (ProbDist.uniform (Fin n → R)) (ProbDist.uniform S)).val (buf, s) *
            (A.run (seqFill G n (n - ω.val) buf s)).val true) := by
      intro s buf
      simp only [pairDist_apply, uniform_val_apply, Fintype.card_fin]
      ring
    simp_rw [hFactor, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_comm]
    unfold seqHybridProb seqHybridDist expectOf pushDist
    rw [Distribution.expect_fTransform]
    dsimp only [Function.comp_def]
    change (∑ x : Fin n → R, ∑ y : S,
        (pairDist 𝒰[Fin n → R] 𝒰[S]).val (x, y) *
          (A.run (seqFill G n (n - ω.val) x y)).val true) =
      Distribution.expect (pairDist 𝒰[Fin n → R] 𝒰[S]).val
        (fun bs => (A.run (seqFill G n (n - ω.val) bs.1 bs.2)).val true)
    rw [← expectOf, expectOf_eq_sum, Fintype.sum_prod_type]
  simp_rw [hInner]

private lemma seqReduction_exp1 {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    {n : ℕ} (A : PRGAdversary ((Fin n → R) × S)) (G : S → R × S) (hn : 0 < n) :
    prgExp1 (seqReduction A G hn) =
      (1 / (n : ℝ)) * ∑ j : Fin n, seqHybridProb A G (j.val + 1) := by
  let _hnEmpty : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hB : ∀ rs : R × S, ((seqReduction A G hn).run rs).val true =
      expectOf (ProbDist.uniform (Fin n)) (fun ω =>
        expectOf (ProbDist.uniform (Fin n → R)) (fun buf =>
          (A.run (seqFill G n (n - (ω.val + 1))
            (fun i => if i.val = ω.val then rs.1 else buf i) rs.2)).val true)) := by
    intro rs
    unfold seqReduction
    rw [sampleBind_eval_true, expectOf_eq_sum, expectOf_eq_sum]
    refine Finset.sum_congr rfl fun ω _ => congrArg ((ProbDist.uniform (Fin n)).val ω * ·) ?_
    exact sampleBind_eval_true _ _
  unfold prgExp1
  simp_rw [hB, expectOf_eq_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hInner : ∀ ω : Fin n,
      (∑ rs : R × S, ∑ buf : Fin n → R,
        (ProbDist.uniform (R × S)).val rs *
          ((ProbDist.uniform (Fin n)).val ω *
            ((ProbDist.uniform (Fin n → R)).val buf *
              (A.run (seqFill G n (n - (ω.val + 1))
                (fun i => if i.val = ω.val then rs.1 else buf i) rs.2)).val true))) =
      (1 / (n : ℝ)) * seqHybridProb A G (ω.val + 1) := by
    intro ω
    rw [Fintype.sum_prod_type]
    have hFactor : ∀ (r : R) (s : S) (buf : Fin n → R),
        (ProbDist.uniform (R × S)).val (r, s) *
          ((ProbDist.uniform (Fin n)).val ω *
            ((ProbDist.uniform (Fin n → R)).val buf *
              (A.run (seqFill G n (n - (ω.val + 1))
                (fun i => if i.val = ω.val then r else buf i) s)).val true)) =
        (1 / (n : ℝ)) * ((ProbDist.uniform S).val s *
          ((ProbDist.uniform R).val r * ((ProbDist.uniform (Fin n → R)).val buf *
            (A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then r else buf i) s)).val true))) := by
      intro r s buf
      simp only [uniform_val_apply, Fintype.card_prod, Fintype.card_fin]
      rw [Nat.cast_mul]
      ring
    simp_rw [hFactor, ← Finset.mul_sum]
    congr 1
    have hSwap :
        (∑ r : R, ∑ s : S,
          (ProbDist.uniform S).val s *
            ((ProbDist.uniform R).val r *
              ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
                (A.run (seqFill G n (n - (ω.val + 1))
                  (fun i => if i.val = ω.val then r else buf i) s)).val true)) =
        ∑ s : S, (ProbDist.uniform S).val s *
          (∑ r : R, (ProbDist.uniform R).val r *
            ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
              (A.run (seqFill G n (n - (ω.val + 1))
                (fun i => if i.val = ω.val then r else buf i) s)).val true) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
    rw [hSwap]
    have hReidx : ∀ s : S,
        (∑ r : R, (ProbDist.uniform R).val r *
          ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
            (A.run (seqFill G n (n - (ω.val + 1))
              (fun i => if i.val = ω.val then r else buf i) s)).val true) =
        ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
          (A.run (seqFill G n (n - (ω.val + 1)) buf s)).val true := fun s =>
      uniform_fin_vec_update_sum n ω
        (fun v => (A.run (seqFill G n (n - (ω.val + 1)) v s)).val true)
    simp_rw [hReidx]
    unfold seqHybridProb seqHybridDist expectOf pushDist
    rw [Distribution.expect_fTransform]
    change (∑ s : S, (ProbDist.uniform S).val s *
        ∑ buf : Fin n → R, (ProbDist.uniform (Fin n → R)).val buf *
          (A.run (seqFill G n (n - (ω.val + 1)) buf s)).val true) =
      Distribution.expect (pairDist 𝒰[Fin n → R] 𝒰[S]).val
        (fun bs => (A.run (seqFill G n (n - (ω.val + 1)) bs.1 bs.2)).val true)
    rw [← expectOf, expectOf_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun buf _ => ?_
    simp only [pairDist_apply]
    ring
  simp_rw [hInner]

private lemma seqReduction_exp0_range {R S : Type} [Fintype R] [Nonempty R]
    [Fintype S] [Nonempty S] {n : ℕ} (A : PRGAdversary ((Fin n → R) × S))
    (G : S → R × S) (hn : 0 < n) :
    prgExp0 (seqReduction A G hn) G =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G j := by
  rw [seqReduction_exp0 A G hn, Fin.sum_univ_eq_sum_range (fun j => seqHybridProb A G j)]

private lemma seqReduction_exp1_range {R S : Type} [Fintype R] [Nonempty R]
    [Fintype S] [Nonempty S] {n : ℕ} (A : PRGAdversary ((Fin n → R) × S))
    (G : S → R × S) (hn : 0 < n) :
    prgExp1 (seqReduction A G hn) =
      (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G (j + 1) := by
  rw [seqReduction_exp1 A G hn,
    Fin.sum_univ_eq_sum_range (fun j => seqHybridProb A G (j + 1))]

informal_symbol seqPRG "G^{\\mathrm{seq}}"
informal_symbol seqHybridDist "\\mathbf{Hybrid}^{\\mathrm{seq}}"
informal_symbol seqHybridProb "p^{\\mathrm{seq}}"
informal_symbol seqReduction "\\mathrm{Red}_{\\mathrm{seq}}"
informal_title seqHybridProb_zero "Experiment 0 equivalence with Hybrid 0"
informal_title seqHybridProb_n "Experiment 1 equivalence with Hybrid n"
informal_title seqReduction_exp0_range "averaging Experiment 0 over uniformly random step"
informal_title seqReduction_exp1_range "averaging Experiment 1 over uniformly random step"

/-- **Theorem 3.3 (Boneh–Shoup §3.4.2):**
    For any length-extending PRG `G : S → R × S`, any `n ≥ 1`, and any adversary `A`
    attacking the `n`-step sequential composition `G^seq(s) = (r₁, ..., rₙ, sₙ)`,
    there exists an adversary `B` attacking `G` (where `B` is an elementary wrapper around `A`)
    such that `PRGadv[A, G^seq] = n · PRGadv[B, G]`. -/
theorem theorem3_3_sequential_prg_composition
    {R S : Type} [Fintype R] [Nonempty R] [Fintype S] [Nonempty S]
    (G : S → R × S) (n : ℕ) (hn : 0 < n) (A : PRGAdversary (VecSpace n R × S)) :
    ∃ B : PRGAdversary (R × S),
      prgAdv A (seqPRG G n) = (n : ℝ) * prgAdv B G := by
  Proof overview "We define ${n + 1} sequential hybrids ${seqHybridDist G n 0} through ${seqHybridDist G n n} replacing the initial output prefix with uniform blocks in ${R} and resampling the intermediate seed in ${S} before iterating ${G} for the remaining steps. For each $0 \\le j \\le$ ${n}, let $p^{\\mathrm{seq}}_j := \\Pr[\\mathcal{A}(\\mathbf{Hybrid}^{\\mathrm{seq}}_j) = 1]$ denote the probability that ${A} outputs $1$ in Hybrid $j$. We construct a single-query reduction ${seqReduction A G hn} (an elementary wrapper around ${A}) and evaluate the resulting telescoping sum."
  Present pseudocode "hybrid" "Hybrid $j$ ($0 \\le j \\le n$)"
    "For $0 \\le i < j$, sample $r_i$ uniformly from ${R}\nSample a fresh intermediate seed $s$ uniformly from ${S} at step $j$\nIterate ${G} for the remaining $n - j$ steps from $s$ to form $(r_j, \\dots, r_{n-1}, s_n)$\nSend $((r_0, \\dots, r_{n-1}), s_n)$ in ${VecSpace n R × S} to ${A} and output whatever ${A} outputs"
  We claim h0 : seqHybridProb A G 0 = prgExp0 A (seqPRG G n)
    explaining "since ${seqHybridDist G n 0} iterates ${G} for all ${n} steps from a fresh uniform seed in ${S} and matches Experiment 0 of ${A} against ${seqPRG G n}" by
    exact seqHybridProb_zero A G
  We claim hnEq : seqHybridProb A G n = prgExp1 A
    explaining "since ${seqHybridDist G n n} replaces all ${n} output blocks and the final state with uniform samples from ${R} and ${S}, matching Experiment 1 of ${A}" by
    exact seqHybridProb_n A G
  New paragraph
  Consider adversary B : PRGAdversary (R × S) := seqReduction A G hn
    where "an elementary wrapper around ${A} making a single oracle call: given a challenge in ${R × S}, it picks an index uniformly from ${Fin n}, fills preceding blocks uniformly from ${R}, inserts the challenge pair at that index, iterates ${G} for the remaining steps, and outputs whatever ${A} outputs"
  Present pseudocode "reduction" "Reduction $\\mathcal{B}$"
    "Upon receiving challenge $(r, s)$ in ${R × S}, ${B} plays the role of challenger to ${A}:\n  Sample $\\omega$ uniformly from ${Fin n}\n  For $i < \\omega$, sample $r_i$ uniformly from ${R}\n  Set $(r_{\\omega}, s_{\\omega + 1}) \\leftarrow (r, s)$\n  Iterate ${G} for the remaining $n - (\\omega + 1)$ steps from $s_{\\omega + 1}$ to form $(r_{\\omega + 1}, \\dots, r_{n-1}, s_n)$\n  Send $((r_0, \\dots, r_{n-1}), s_n)$ in ${VecSpace n R × S} to ${A} and output whatever ${A} outputs"
  We claim hB0 :
      prgExp0 B G = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G j
    explaining "since in Experiment 0 of ${B} against ${G}, conditioning on the chosen index makes the remaining ${G} iteration one step longer, matching the corresponding hybrid and averaging ${seqHybridProb A G 0} through ${seqHybridProb A G (n - 1)}" by
    exact seqReduction_exp0_range A G hn
  We claim hB1 :
      prgExp1 B = (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G (j + 1)
    explaining "since in Experiment 1 of ${B}, conditioning on the chosen index leaves the inserted prefix block uniform in ${R}, advancing the hybrid index by one and averaging ${seqHybridProb A G 1} through ${seqHybridProb A G n}" by
    exact seqReduction_exp1_range A G hn
  New paragraph
  We claim hAdv : prgAdv B G = (1 / (n : ℝ)) * prgAdv A (seqPRG G n)
    explaining "combining both experiment averages collapses into a telescoping difference between ${seqHybridProb A G 0} and ${seqHybridProb A G n}" by
    calc
      prgAdv B G
          = |prgExp0 B G - prgExp1 B| := prgAdv_eq_abs B G
      _ = |(1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G j -
            (1 / (n : ℝ)) * ∑ j ∈ Finset.range n, seqHybridProb A G (j + 1)| :=
            abs_sub_eq_of_eq hB0 hB1
      _ = (1 / (n : ℝ)) * |seqHybridProb A G 0 - seqHybridProb A G n| :=
            scaled_telescoping_abs (seqHybridProb A G)
      _ = (1 / (n : ℝ)) * prgAdv A (seqPRG G n) :=
            mul_abs_sub_eq_mul_prgAdv (1 / (n : ℝ)) A (seqPRG G n) h0 hnEq
  We conclude "We multiply both sides by ${n} and exhibit ${B}, where ${B} is an elementary wrapper around ${A}, as the reduction adversary" by
    exact ⟨B, eq_mul_of_div_eq hn hAdv⟩

informal_title theorem3_3_sequential_prg_composition
  "Sequential Composition of Pseudorandom Generators"
informal_kind theorem3_3_sequential_prg_composition "Theorem"
informal_section theorem3_3_sequential_prg_composition
  "Section 3.4.2 — Sequential Composition and Length Extension"
informal_section_prelude theorem3_3_sequential_prg_composition
  "construction"
  "Construction 3.2"
  "Sequential Length-Extending PRG"
  "Given a length-extending PRG $G : \\mathcal{S} \\to \\mathcal{R} \\times \\mathcal{S}$ and an integer $n \\ge 1$, its $n$-wise sequential composition $G^{\\mathrm{seq}\\, n} : \\mathcal{S} \\to \\mathcal{R}^n \\times \\mathcal{S}$ iterates $G$ for $n$ steps starting from $s \\in \\mathcal{S}$:\n> $s_0 \\leftarrow s$\n> for $i \\leftarrow 1$ to $n$ do\n>   $(r_i, s_i) \\leftarrow G(s_{i-1})$\n> output $(r_1, \\dots, r_n, s_n)$"

end SequentialPRGSection

/-!
## 4. Theorem 3.11 — Statistical Distance Bounds Distinguishing Advantage (Boneh–Shoup §3.11)
-/

section StatisticalDistanceSection

paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Adversary in Attack Game 3.3 distinguishing two distributions `P₀, P₁` over `R`:
    equipped with finite nonempty coin space `Coins` (a singleton when deterministic)
    and decision predicate `run r t ∈ {0,1}`. -/
@[paper_describe "distinguishing adversary" (plural := "distinguishing adversaries")
  (carrier := false) (varStyle := .mathcal) (qualifier := "over {R}")]
structure DistAdversary (R : Type) where
  Coins : Type
  [coinsFintype : Fintype Coins]
  [coinsNonempty : Nonempty Coins]
  run : R → Coins → Bool

attribute [instance] DistAdversary.coinsFintype DistAdversary.coinsNonempty
attribute [math_notation "\\mathcal{T}_{#1}"] DistAdversary.Coins
attribute [math_notation "#1\\!\\left(#2, #3\\right)"] DistAdversary.run

/-- Predicate expressing that `A` is deterministic (uses a trivial singleton coin space). -/
@[math_pred "is deterministic"]
def DistAdversary.IsDet {R : Type} (A : DistAdversary R) : Prop :=
  Subsingleton A.Coins

/-- Predicate expressing that `A` is probabilistic (not deterministic). -/
@[math_pred "is probabilistic"]
def DistAdversary.IsProb {R : Type} (A : DistAdversary R) : Prop :=
  ¬ A.IsDet

/-- Acceptance event `R'_t = {r ∈ R : A(r, t) = 1}` for fixed coin `t`. -/
@[math_notation "R'_{#1}" (hide := [0])]
def acceptEvent {R : Type} (A : DistAdversary R) (t : A.Coins) : R → Prop :=
  fun r => A.run r t = true

/-- Acceptance probability `Pr[W_b] = E_{t ← 𝒰[T]}[P_b(R'_t)]` in Experiment `b`. -/
@[math_notation "\\Pr\\!\\left[#2\\left(#1\\right) = 1\\right]"]
noncomputable def distWinProb {R : Type} (P : ProbDist R) (A : DistAdversary R) : ℝ :=
  expectOf (ProbDist.uniform A.Coins) (fun t => probOf P (acceptEvent A t))

/-- Distinguishing advantage `Distadv[A, P₀, P₁] = |Pr[W₀] - Pr[W₁]|`. -/
@[math_notation "\\mathrm{Distadv}\\!\\left[#1, #2, #3\\right]"]
noncomputable def distAdv {R : Type} (A : DistAdversary R) (P₀ P₁ : ProbDist R) : ℝ :=
  |distWinProb P₀ A - distWinProb P₁ A|

/-- **Theorem 3.10 (Boneh–Shoup §3.11):**
    For any distributions `P₀, P₁` on `R` and any event `E ⊆ R`,
    `|P₀[E] - P₁[E]| ≤ Δ(P₀, P₁)`. -/
@[math_opaque]
theorem theorem3_10_statDist_bounds_event
    {R : Type} [Fintype R] (P₀ P₁ : ProbDist R) (E : R → Prop) :
    |probOf P₀ E - probOf P₁ E| ≤ Probability.statDist P₀.val P₁.val := by
  exact SystemAlgebra.abs_mass_sub_le_statDist P₀ P₁ E

private lemma distWinProb_det {R : Type} (P : ProbDist R) (A : DistAdversary R)
    (t₀ : A.Coins) (hSub : Subsingleton A.Coins) :
    distWinProb P A = probOf P (acceptEvent A t₀) := by
  let _hUniq : Unique A.Coins := { default := t₀, uniq := fun _ => hSub.elim _ _ }
  rw [distWinProb, expectOf_eq_sum, Fintype.sum_unique]
  have huniq : default = t₀ := rfl
  simp [uniform_val_apply, huniq]

private lemma distAdv_eq_abs {R : Type} (A : DistAdversary R) (P₀ P₁ : ProbDist R) :
    distAdv A P₀ P₁ = |distWinProb P₀ A - distWinProb P₁ A| := rfl

@[informal_expand]
private lemma abs_det_winProb_diff {R : Type} (P₀ P₁ : ProbDist R) (A : DistAdversary R)
    (t₀ : A.Coins) (hDet : Subsingleton A.Coins) :
    |distWinProb P₀ A - distWinProb P₁ A| =
      |probOf P₀ (acceptEvent A t₀) - probOf P₁ (acceptEvent A t₀)| := by
  have h₀ : distWinProb P₀ A = probOf P₀ (acceptEvent A t₀) :=
    distWinProb_det P₀ A t₀ hDet
  have h₁ : distWinProb P₁ A = probOf P₁ (acceptEvent A t₀) :=
    distWinProb_det P₁ A t₀ hDet
  rw [h₀, h₁]

private lemma distAdv_sub_expect {R : Type} (P₀ P₁ : ProbDist R) (A : DistAdversary R) :
    distWinProb P₀ A - distWinProb P₁ A =
      (1 / (Fintype.card A.Coins : ℝ)) *
        ∑ t : A.Coins, (probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t)) := by
  unfold distWinProb
  simp_rw [expectOf_eq_sum, uniform_val_apply, ← Finset.mul_sum]
  rw [← mul_sub, ← Finset.sum_sub_distrib]

private lemma distAdv_sub_expect_abs {R : Type} (P₀ P₁ : ProbDist R) (A : DistAdversary R) :
    |distWinProb P₀ A - distWinProb P₁ A| =
      |(1 / (Fintype.card A.Coins : ℝ)) *
        ∑ t : A.Coins, (probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t))| := by
  rw [distAdv_sub_expect]

private lemma avg_abs_le_avg {T : Type} [Fintype T] [Nonempty T] (f : T → ℝ) :
    |(1 / (Fintype.card T : ℝ)) * ∑ t : T, f t| ≤
      (1 / (Fintype.card T : ℝ)) * ∑ t : T, |f t| := by
  have hInv : (0 : ℝ) ≤ 1 / (Fintype.card T : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hInv]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs f Finset.univ) hInv

set_option linter.unusedVariables false in
private lemma avg_sum_le {T : Type} [Fintype T] [Nonempty T] (f : T → ℝ) (B : ℝ)
    (hf : ∀ t : T, f t ≤ B) :
    (1 / (Fintype.card T : ℝ)) * ∑ t : T, f t ≤
      (1 / (Fintype.card T : ℝ)) * ∑ t : T, B := by
  have hInv : (0 : ℝ) ≤ 1 / (Fintype.card T : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => hf t) hInv

set_option linter.unusedVariables false in
private lemma avg_const_eq {T : Type} [Fintype T] [Nonempty T] (B : ℝ) :
    (1 / (Fintype.card T : ℝ)) * ∑ t : T, B = B := by
  have hPos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  simp [Finset.sum_const, Finset.card_univ]

informal_title theorem3_10_statDist_bounds_event "Theorem 3.10"
informal_kind theorem3_10_statDist_bounds_event "Theorem"
informal_title distWinProb_det "deterministic win probability equals event mass"
informal_opaque distWinProb_det
informal_title distAdv_eq_abs "definition of distinguishing advantage"
informal_title abs_det_winProb_diff "identifying deterministic win probabilities with event mass"
informal_title distAdv_sub_expect_abs "averaging over coin choices"
informal_title avg_abs_le_avg "the triangle inequality"
informal_title avg_sum_le "Theorem 3.10 for each coin choice"
informal_title avg_const_eq "averaging a constant over all coins"
informal_symbol distWinProb "\\Pr_{\\mathrm{dist}}"
informal_symbol distAdv "\\mathrm{Distadv}"
informal_symbol Probability.statDist "\\Delta"
informal_symbol acceptEvent "R'"

/-- **Theorem 3.11 (Boneh–Shoup §3.11):**
    For any two distributions `P₀, P₁` over a finite set `R` and any distinguishing
    adversary `A` (deterministic or probabilistic), `Distadv[A, P₀, P₁] ≤ Δ(P₀, P₁)`. -/
theorem theorem3_11_statDist_bounds_distAdv
    {R : Type} [Fintype R] (P₀ P₁ : ProbDist R) (A : DistAdversary R) :
    distAdv A P₀ P₁ ≤ Probability.statDist P₀.val P₁.val := by
  With notation (distWinProb P₀ A) as "\\Pr[W_0]"
  With notation (distWinProb P₁ A) as "\\Pr[W_1]"
  Proof overview "We treat deterministic and randomized distinguishers separately over coin space ${A.Coins}. For each coin choice $t \\in \\mathcal{T}_{\\mathcal{A}}$, let $R'_t = \\{x : \\mathcal{A}(x; t) = 1\\}$ denote the coin-fixed acceptance event on ${R}, and reduce the bound to Theorem 3.10."
  Present pseudocode "algorithm" "Coin-Fixed Acceptance Events"
    "For each coin $t$ in ${A.Coins}, define $R'_t := \\{x \\in R : \\mathcal{A}(x; t) = 1\\}$ on ${R}\nWhen ${A} is deterministic, ${A.Coins} is a singleton $\\{t_0\\}$, so $R' := R'_{t_0}$ satisfies $\\Pr[W_b] = P_b[R']$\nWhen ${A} is probabilistic, averaging over ${A.Coins} gives $\\Pr[W_b] = \\frac{1}{|\\mathcal{T}_{\\mathcal{A}}|} \\sum_{t \\in \\mathcal{T}_{\\mathcal{A}}} P_b[R'_t]$ for ${P₀} and ${P₁}"
  We claim hDetCase : A.IsDet → distAdv A P₀ P₁ ≤ Probability.statDist P₀.val P₁.val
    explaining "when ${A} is deterministic, fixing its unique coin $t_0$ defines the single acceptance event $R' = R'_{t_0} = \\{x : \\mathcal{A}(x; t_0) = 1\\}$ with $\\Pr[W_0] = P_0[R']$ and $\\Pr[W_1] = P_1[R']$, so Theorem 3.10 yields the bound" by
    intro hDet
    let t₀ : A.Coins := Classical.arbitrary A.Coins
    With notation (probOf P₀ (acceptEvent A t₀)) as "P_0[R']"
    With notation (probOf P₁ (acceptEvent A t₀)) as "P_1[R']"
    calc
      distAdv A P₀ P₁
          = |distWinProb P₀ A - distWinProb P₁ A| := distAdv_eq_abs A P₀ P₁
      _ = |probOf P₀ (acceptEvent A t₀) - probOf P₁ (acceptEvent A t₀)| :=
            abs_det_winProb_diff P₀ P₁ A t₀ hDet
      _ ≤ Probability.statDist P₀.val P₁.val :=
            theorem3_10_statDist_bounds_event P₀ P₁ (acceptEvent A t₀)
  New paragraph
  We claim hProbCase : A.IsProb → distAdv A P₀ P₁ ≤ Probability.statDist P₀.val P₁.val
    explaining "when ${A} is probabilistic, introducing the coin-fixed acceptance event $R'_t = \\{x : \\mathcal{A}(x; t) = 1\\}$ and averaging over ${A.Coins} reduces ${distAdv A P₀ P₁} via the triangle inequality and Theorem 3.10 to ${Probability.statDist P₀.val P₁.val}" by
    intro _
    calc
      distAdv A P₀ P₁
          = |distWinProb P₀ A - distWinProb P₁ A| := distAdv_eq_abs A P₀ P₁
      _ = |(1 / (Fintype.card A.Coins : ℝ)) *
            ∑ t : A.Coins, (probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t))| :=
            distAdv_sub_expect_abs P₀ P₁ A
      _ ≤ (1 / (Fintype.card A.Coins : ℝ)) *
            ∑ t : A.Coins, |probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t)| :=
            avg_abs_le_avg _
      _ ≤ (1 / (Fintype.card A.Coins : ℝ)) *
            ∑ t : A.Coins, Probability.statDist P₀.val P₁.val :=
            avg_sum_le (fun t => |probOf P₀ (acceptEvent A t) - probOf P₁ (acceptEvent A t)|)
              (Probability.statDist P₀.val P₁.val)
              (fun t => theorem3_10_statDist_bounds_event P₀ P₁ (acceptEvent A t))
      _ = Probability.statDist P₀.val P₁.val :=
            avg_const_eq (Probability.statDist P₀.val P₁.val)
  We conclude "We combine both deterministic and randomized cases"
    from hDetCase and hProbCase by
    exact (Classical.em A.IsDet).elim hDetCase hProbCase

informal_title theorem3_11_statDist_bounds_distAdv
  "Statistical Distance Bounds Distinguishing Advantage"
informal_kind theorem3_11_statDist_bounds_distAdv "Theorem"
informal_section theorem3_11_statDist_bounds_distAdv
  "Section 3.11 — Statistical Distance and Distinguishing Advantage"
informal_section_prelude theorem3_11_statDist_bounds_distAdv
  "definition"
  "Definition 3.6"
  "Statistical Distance"
  "For probability distributions $P_0$ and $P_1$ on a finite set $R$, their statistical distance is $$\\Delta(P_0, P_1) = \\frac{1}{2} \\sum_{x \\in R} |P_0(x) - P_1(x)|$$.\n\nOn probability distributions over finite $R$, this equals the one-sided excess $\\sum_{x \\in R} \\max\\{P_0(x) - P_1(x), 0\\}$. By Theorem 3.10, $\\max_{R' \\subseteq R} |P_0[R'] - P_1[R']| = \\Delta(P_0, P_1)$, so $|P_0[R'] - P_1[R']| \\le \\Delta(P_0, P_1)$ for every event $R' \\subseteq R$."
informal_section_prelude theorem3_11_statDist_bounds_distAdv
  "attackGame"
  "Attack Game 3.3"
  "Distinguishing Game"
  "Let $P_0$ and $P_1$ be probability distributions on a finite set $R$, and let $\\mathcal{A}$ be a randomized adversary with finite nonempty coin space $\\mathcal{T}_{\\mathcal{A}}$. For $b \\in \\{0, 1\\}$, write $\\Pr[\\mathcal{A}(P_b) = 1]$ for the acceptance probability in Experiment $b$ below, and define $\\mathrm{Distadv}[\\mathcal{A}, P_0, P_1] := \\left|\\Pr[\\mathcal{A}(P_0) = 1] - \\Pr[\\mathcal{A}(P_1) = 1]\\right|$.\n> Experiment $b$ ($b \\in \\{0, 1\\}$):\n>   sample $x \\leftarrow P_b$ and coins $t \\leftarrow \\mathcal{U}[\\mathcal{T}_{\\mathcal{A}}]$\n>   output $\\hat{b} \\leftarrow \\mathcal{A}(x; t) \\in \\{0, 1\\}$"

end StatisticalDistanceSection

/-!
## 5. Theorem 4.7 — The Difference Lemma (Boneh–Shoup §4.4.3)
-/

section DifferenceLemmaSection

paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Intersection event `E ∧ F` on `Ω`. -/
@[math_notation "#1 \\land #2"]
def evAnd {Ω : Type} (E F : Ω → Prop) : Ω → Prop := fun ω => E ω ∧ F ω

/-- Complement event `¬E` on `Ω`. -/
@[math_notation "\\overline{#1}"]
def evCompl {Ω : Type} (E : Ω → Prop) : Ω → Prop := fun ω => ¬ E ω

informal_symbol evAnd "\\land"
informal_symbol evCompl "\\overline{\\cdot}"

@[informal_expand]
private lemma diffLemma_partition_step {Ω : Type} (P : ProbDist Ω) (W₀ W₁ Z : Ω → Prop) :
    |probOf P W₀ - probOf P W₁| =
      |(probOf P (evAnd W₀ Z) + probOf P (evAnd W₀ (evCompl Z))) -
       (probOf P (evAnd W₁ Z) + probOf P (evAnd W₁ (evCompl Z)))| := by
  have h₀ : probOf P (evAnd W₀ Z) + probOf P (evAnd W₀ (evCompl Z)) = probOf P W₀ :=
    probOf_split P Z W₀
  have h₁ : probOf P (evAnd W₁ Z) + probOf P (evAnd W₁ (evCompl Z)) = probOf P W₁ :=
    probOf_split P Z W₁
  rw [← h₀, ← h₁]

informal_title diffLemma_partition_step "partitioning both events over Z and its complement"

@[informal_expand]
private lemma diffLemma_cancel_step {Ω : Type} (P : ProbDist Ω) (W₀ W₁ Z : Ω → Prop)
    (hEquiv : ∀ ω, W₀ ω ∧ ¬ Z ω ↔ W₁ ω ∧ ¬ Z ω) :
    |(probOf P (evAnd W₀ Z) + probOf P (evAnd W₀ (evCompl Z))) -
     (probOf P (evAnd W₁ Z) + probOf P (evAnd W₁ (evCompl Z)))| =
    |probOf P (evAnd W₀ Z) - probOf P (evAnd W₁ Z)| := by
  have hEq : probOf P (evAnd W₀ (evCompl Z)) = probOf P (evAnd W₁ (evCompl Z)) :=
    probOf_congr P hEquiv
  have hSub :
      (probOf P (evAnd W₀ Z) + probOf P (evAnd W₀ (evCompl Z))) -
        (probOf P (evAnd W₁ Z) + probOf P (evAnd W₁ (evCompl Z))) =
      probOf P (evAnd W₀ Z) - probOf P (evAnd W₁ Z) := by
    rw [hEq]
    ring
  rw [hSub]

informal_title diffLemma_cancel_step "cancelling the identical intersections with the complement of Z"

@[informal_expand]
private lemma diffLemma_interval_bound {Ω : Type} (P : ProbDist Ω) (W₀ W₁ Z : Ω → Prop) :
    |probOf P (evAnd W₀ Z) - probOf P (evAnd W₁ Z)| ≤ probOf P Z := by
  have h₀ : 0 ≤ probOf P (evAnd W₀ Z) ∧ probOf P (evAnd W₀ Z) ≤ probOf P Z :=
    ⟨probOf_nonneg P _, probOf_mono P fun _ h => h.2⟩
  have h₁ : 0 ≤ probOf P (evAnd W₁ Z) ∧ probOf P (evAnd W₁ Z) ≤ probOf P Z :=
    ⟨probOf_nonneg P _, probOf_mono P fun _ h => h.2⟩
  exact abs_le.mpr ⟨by linarith [h₀.1, h₁.2], by linarith [h₀.2, h₁.1]⟩

informal_title diffLemma_interval_bound "each intersection lying in [0, Pr[Z]]"

/-- **Theorem 4.7 (The Difference Lemma, Boneh–Shoup §4.4.3):**
    Let `W₀, W₁, Z` be events defined on the same probability space `P` such that
    `W₀ ∧ ¬ Z ↔ W₁ ∧ ¬ Z`. Then `|Pr[W₀] - Pr[W₁]| ≤ Pr[Z]`. -/
theorem theorem4_7_difference_lemma
    {Ω : Type} (P : ProbDist Ω) (W₀ W₁ Z : Ω → Prop)
    (hEquiv : ∀ ω, W₀ ω ∧ ¬ Z ω ↔ W₁ ω ∧ ¬ Z ω) :
    |probOf P W₀ - probOf P W₁| ≤ probOf P Z := by
  With notation (probOf P W₀) as "\\Pr[W_0]"
  With notation (probOf P W₁) as "\\Pr[W_1]"
  With notation (probOf P Z) as "\\Pr[Z]"
  With notation (probOf P (evAnd W₀ Z)) as "\\Pr[W_0 \\land Z]"
  With notation (probOf P (evAnd W₀ (evCompl Z))) as "\\Pr[W_0 \\land \\overline{Z}]"
  With notation (probOf P (evAnd W₁ Z)) as "\\Pr[W_1 \\land Z]"
  With notation (probOf P (evAnd W₁ (evCompl Z))) as "\\Pr[W_1 \\land \\overline{Z}]"
  Proof overview "We partition ${W₀} and ${W₁} over ${Z} and ${evCompl Z}, cancel the matching terms on ${evCompl Z} using the identical-until-bad equivalence, and bound the remaining difference using $0 \\le$ ${probOf P (evAnd W₀ Z)} $\\le$ ${probOf P Z} and $0 \\le$ ${probOf P (evAnd W₁ Z)} $\\le$ ${probOf P Z}."
  calc
    |probOf P W₀ - probOf P W₁|
        = |(probOf P (evAnd W₀ Z) + probOf P (evAnd W₀ (evCompl Z))) -
            (probOf P (evAnd W₁ Z) + probOf P (evAnd W₁ (evCompl Z)))| :=
          diffLemma_partition_step P W₀ W₁ Z
    _ = |probOf P (evAnd W₀ Z) - probOf P (evAnd W₁ Z)| :=
          diffLemma_cancel_step P W₀ W₁ Z hEquiv
    _ ≤ probOf P Z :=
          diffLemma_interval_bound P W₀ W₁ Z

informal_title theorem4_7_difference_lemma "The Difference Lemma"
informal_kind theorem4_7_difference_lemma "Theorem"
informal_section theorem4_7_difference_lemma "Section 4.4.3 — The Difference Lemma"
informal_section_prelude theorem4_7_difference_lemma
  "definition"
  "Setup 4.1"
  "Identical-Until-Bad Events"
  "Let $W_0$, $W_1$, and $Z$ be events defined on a common probability space $(\\Omega, P)$, where $\\overline{Z}$ denotes the complement of the failure event $Z$. The events $W_0$ and $W_1$ are identical until bad (with respect to $Z$) if $W_0 \\land \\overline{Z} \\iff W_1 \\land \\overline{Z}$.\n\nIn game-playing proofs, two experiments are coupled on the same probability space $(\\Omega, P)$ so that executions avoiding the failure event $Z$ induce identical outcomes for $W_0$ and $W_1$, bounding $|\\Pr[W_0] - \\Pr[W_1]|$ by $\\Pr[Z]$."

end DifferenceLemmaSection

/-!
## Standard Axiom Verification & Self-Contained JSON/HTML Export
-/

#print axioms theorem2_2_otp_perfect_security
#print axioms theorem3_2_parallel_prg_composition
#print axioms theorem3_3_sequential_prg_composition
#print axioms theorem3_11_statDist_bounds_distAdv
#print axioms theorem4_7_difference_lemma

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let targetDecls : Array Name :=
    #[``theorem2_2_otp_perfect_security,
      ``theorem3_2_parallel_prg_composition,
      ``theorem3_3_sequential_prg_composition,
      ``theorem3_11_statDist_bounds_distAdv,
      ``theorem4_7_difference_lemma]
  let doc ← liftTermElabM <| Informalization.Render.Json.buildDocument
    "Boneh–Shoup: Foundations and Pseudorandom Generators"
    "Selected Foundations, Pseudorandom Generators, Statistical Distance, and the Difference Lemma"
    targetDecls
  let texts := Informalization.CLI.collectDocumentTexts doc
  let leaks := Informalization.Core.Hygiene.auditZeroLeakage texts
  unless leaks.isEmpty do
    throwError "BonehShoupPart1 informalization leaked {leaks.size} forbidden string(s): {leaks}"
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "boneh_shoup_part1.json")
    (Informalization.Render.Json.renderDocumentJson doc)
  IO.FS.writeFile (outDir / "boneh_shoup_part1.html")
    (Informalization.Render.Html.renderDocumentHtml doc)
  IO.println s!"BonehShoupPart1: exported {doc.entries.size} entries, auditZeroLeakage = {leaks.size}"

end Tests.Informalization.BonehShoupPart1

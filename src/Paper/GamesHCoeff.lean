/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Paper.Register
import Informalization.Paper.Archetypes
import ConstructiveCryptography.Instances.Game
import Examples.AuthenticatedEncryption.Collision
import Examples.Games
import RandomSystems.Distance.HCoefficient
import RandomSystems.Typed.Functional

/-!
# Benchmarks B5 & B6: Games with Monotone Binary Outputs and the H-Coefficient Technique (Register C: `randomSystems`)

Formalizes:
* **B5 (CR18 Theorems 4.17 & 6.1):**
  - `mbo_reduction_bound`: transporting MBO game-winning bounds and conditional-equivalence
    distinguishing bounds under converter attachment via compatible distinguishers;
  - `aead_collision_mbo_bound`: bounding $\Delta(\mathbf{H}_{\mathsf{coll}}, \mathsf{Ideal}\,\mathbf{E}_{\mathsf{enc}}(\Pi)) \le q(\mathrm{enc})^2 / |\mathcal{M}|$
    via `Bad_event`, conditional equivalence, and an explicit birthday union bound;
* **B6 (Jha §2.2 Lemma 2.2.1 / Corollary 2.2.2 + General-$N$ Tightness Application):**
  - `h_coefficient_method`: the H-coefficient bound with genuine 3-step total-variation partition
    derivation over bad and good transcripts;
  - `point_vs_uniform_tightness`: exact distinguishing advantage
    $\Delta(\mathbf{F}_{x_0}, \mathbf{F}_{\mathrm{rand}}) = 1 - 1/|D|$ over any finite domain $D$
    with $|D| \ge 2$, proved via an explicit one-query distinguisher lower bound and an
    H-coefficient upper bound.
-/

namespace Paper.GamesHCoeff

open CategoryTheory
open Probability SystemAlgebra SystemAlgebra.Interface
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped VerboseCC SystemAlgebra NNReal BigOperators

noncomputable section

/-! ## Clean Paper Accessors & Definitions -/

/-- Compatible distinguisher on typed random-system interface `A` supporting both decision and MBO
winning probabilities. -/
@[paper_describe "compatible distinguisher" (plural := "compatible distinguishers")
  (carrier := false) (qualifier := "with interface {A}")]
def CompatDistinguisher (A : Interface) : Type := TypedSolver A

/-- Decision behavior view of a compatible distinguisher. -/
def CompatDistinguisher.decision {A : Interface} (D : CompatDistinguisher A) :
    TypedDistinguisher A :=
  TypedSolver.decision D

/-- Absorb converter `α` into compatible distinguisher `D`. -/
def CompatDistinguisher.absorb {A B : Interface}
    (D : CompatDistinguisher A) (α : TypedConverter A B) : CompatDistinguisher B :=
  TypedSolver.absorb D α

/-- Extract the underlying probabilistic interaction realizing both views of `D`. -/
lemma CompatDistinguisher.exists_realization {A : Interface} (D : CompatDistinguisher A) :
    ∃ P : A.inputDomain.Distinguisher,
      (∀ R : TypedSystem A, D.decision.1 R = P.probability R.1) ∧
      ∀ G : TypedGame A, TypedSolver.winProbability D G = P.winProbability G.1.1 :=
  TypedSolver.exists_realization D

/-- Decision advantage of a compatible distinguisher `D` between two typed systems `R` and `S`. -/
@[math_notation "\\Delta^{#1}(#2, #3)"]
def distAdv {A : Interface} (D : CompatDistinguisher A) (R S : TypedSystem A) : ℝ :=
  |D.decision.1 R - D.decision.1 S|

/-- Acceptance probability of a compatible distinguisher `obs` on typed system `R`. -/
@[math_notation "\\Pr\\!\\left[#1\\!\\left(#2\\right) = 1\\right]"]
def obsProb {A : Interface} (obs : TypedDistinguisher A) (R : TypedSystem A) : ℝ :=
  obs.1 R

/-- Completed interaction transcript over typed random-system interface `A`. -/
def Transcript (A : Interface) : Type :=
  List ((Σ i, A.X i) × (Σ i, A.Y i))

/-- Subset of completed transcripts over interface `A`. -/
@[paper_describe "subset of transcripts" (plural := "subsets of transcripts")
  (carrier := false) (qualifier := "over {A}")]
def TranscriptSubset (A : Interface) : Type :=
  Transcript A → Prop

instance {A : Interface} : Membership (Transcript A) (TranscriptSubset A) :=
  ⟨fun T τ => T τ⟩

/-- View a `TranscriptSubset A` as its underlying transcript predicate. -/
@[math_notation "#1"]
def TranscriptSubset.toPred {A : Interface} (T : TranscriptSubset A) : Transcript A → Prop :=
  T

/-- Complementary good-transcript set $\overline{B}$ of a bad-transcript subset `B`. -/
@[math_notation "\\overline{#1}"]
def goodSet {A : Interface} (B : Transcript A → Prop) : Transcript A → Prop :=
  fun τ => ¬ B τ

/-- Interpolation probability of transcript `τ` under typed random system `R`. -/
@[math_notation "#1\\!\\left(#2\\right)"]
def sysProb {A : Interface} (R : TypedSystem A) (τ : Transcript A) : ℝ :=
  R.1 τ

/-- Probability that a compatible distinguisher `D` sets the MBO flag of game `G`. -/
@[math_notation "\\Gamma^{#1}(#2)"]
def winProb {A : Interface} (D : CompatDistinguisher A) (G : TypedGame A) : ℝ :=
  TypedSolver.winProbability D G

/-- Induced completed-transcript distribution $\mathcal{L}(R, E, n)$. -/
@[math_notation "\\mathcal{L}(#1, #2, #3)"]
def transcriptLaw {A : Interface} (R : TypedSystem A)
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ) : Distribution (Transcript A) :=
  R.1.sLaw E.1 n

/-- Total-variation distance $\delta(\mu, \nu)$ between transcript distributions. -/
@[math_notation "\\delta(#1, #2)"]
def tvDist {A : Interface} (μ ν : Distribution (Transcript A)) : ℝ :=
  Probability.statDist μ ν

/-- One-sided ideal-over-real excess mass restricted to transcript subset `B`. -/
@[math_notation "\\sum_{\\tau \\in #3} \\max\\!\\left(0, #2(\\tau) - #1(\\tau)\\right)"]
def tvExcessOn {A : Interface} (μ_real μ_id : Distribution (Transcript A))
    (B : Transcript A → Prop) : ℝ :=
  letI : DecidablePred B := Classical.decPred B
  letI : DecidableEq (Transcript A) := Classical.decEq (Transcript A)
  ∑ τ ∈ (μ_id.support ∪ μ_real.support).filter B, max (μ_id τ - μ_real τ) 0

/-- Bad-transcript probability mass under the ideal transcript distribution $\mathcal{L}(S, E, n)$. -/
@[math_notation "\\Pr_{\\mathcal{L}(#1, #2, #3)}\\!\\left[#4\\right]"]
def idealBadProb {A : Interface} (S : TypedSystem A)
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
    (Bad : Transcript A → Prop) : ℝ :=
  Probability.probBad (S.1.sLaw E.1 n) Bad

/-- Good-transcript probability mass under the ideal transcript distribution $\mathcal{L}(S, E, n)$. -/
@[math_notation "\\Pr_{\\mathcal{L}(#1, #2, #3)}\\!\\left[\\overline{#4}\\right]"]
def idealGoodProb {A : Interface} (S : TypedSystem A)
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
    (Bad : Transcript A → Prop) : ℝ :=
  (S.1.sLaw E.1 n).mass (fun τ => ¬ Bad τ)

/-- Single-query interface returning elements of an arbitrary finite domain `D`. -/
abbrev pointInterface (D : Type) [Fintype D] : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => D) 1

/-- Constant single-query system returning fixed value `x : D`. -/
def pointFixed {D : Type} [Fintype D] (x : D) : TypedSystem (pointInterface D) :=
  TypedSystem.ofFunction fun _ _ => x

/-- Uniform single-query system sampling `x ← 𝒰(D)` and behaving like `pointFixed x`. -/
def pointIdeal (D : Type) [Fintype D] [Nonempty D] : TypedSystem (pointInterface D) :=
  TypedSystem.sample (Probability.Distribution.uniform D) (pointFixed (D := D))

/-- Bad single-query transcript predicate: the single reply differs from the target element `x₀`. -/
def BadReply {D : Type} [Fintype D] (x₀ : D)
    (h : List ((Σ i, (pointInterface D).X i) × (Σ i, (pointInterface D).Y i))) : Prop :=
  ∃ y : D, y ≠ x₀ ∧ h = [(⟨(), ()⟩, ⟨(), y⟩)]

/-! ## B5: Game Reductions and Monotone Binary Outputs (CR18 Thms 4.17 & 6.1) -/

/-- **MBO Reduction Bound** (Maurer CR18, Theorem 4.17 & §4.7.2):
if game $\hat{\mathbf{G}}$ on interface $B$ is conditionally equivalent to $\mathbf{T}$ until its
MBO triggers, and every compatible distinguisher on $B$ triggers $\hat{\mathbf{G}}$ with
probability at most $\varepsilon$, then attaching any converter $\alpha : A \to B$ preserves the
distinguishing bound $\Delta^D(\alpha\mathbf{G}^-, \alpha\mathbf{T}) \le \varepsilon$. -/
theorem mbo_reduction_bound
    {A B : Interface} (α : TypedConverter A B)
    (G : TypedGame B) (T : TypedSystem B)
    (hc : G.1.1.ConditionallyEquivalent T.1)
    {ε : ℝ≥0}
    (hWin : ∀ D' : CompatDistinguisher B, winProb D' G ≤ (ε : ℝ))
    (D : CompatDistinguisher A) :
    distAdv D (α • G.visible) (α • T) ≤ (ε : ℝ) := by
  With notation (D.absorb α) as "D \\circ \\alpha"
    explaining "the absorbed compatible distinguisher on interface $B$"
  proof_idea "We absorb the converter $\\alpha$ into the compatible distinguisher $D$, invoke conditional equivalence until the MBO triggers (CR18, Theorem 4.17), and apply the MBO winning bound on interface $B$."
  We claim hAbsorb :
      distAdv D (α • G.visible) (α • T) = distAdv (D.absorb α) G.visible T by
    by_leaf "Running $D$ with outer converter $\\alpha$ on the underlying system $\\hat{\\mathbf{G}}^-$ and $\\mathbf{T}$ has identical decision probabilities to running the absorbed distinguisher $D \\circ \\alpha$ directly on interface $B$." {
      rfl
    }
  We claim hCond :
      distAdv (D.absorb α) G.visible T ≤ winProb (D.absorb α) G by
    by_leaf "Realizing the compatible distinguisher $D \\circ \\alpha$ by a single probabilistic interaction $P$ on $B$, conditional equivalence forces $\\hat{\\mathbf{G}}$'s MBO flag to trigger whenever $P$ separates the underlying system $\\hat{\\mathbf{G}}^-$ from $\\mathbf{T}$, bounding the decision gap by $\\Gamma^{D \\circ \\alpha}(\\hat{\\mathbf{G}})$." {
      obtain ⟨P, hP, hW⟩ := (D.absorb α).exists_realization
      rw [distAdv, hP G.visible, hP T, winProb, hW G]
      exact P.advantage_le_winProbability G.1.2 T.2 G.2 hc
    }
  by_leaf "Applying the assumed MBO winning-probability bound $\\Gamma^{D \\circ \\alpha}(\\hat{\\mathbf{G}}) \\le \\varepsilon$ closes the reduction." {
    exact hAbsorb.trans_le (hCond.trans (hWin (D.absorb α)))
  }

section AEADCollision

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
  [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]

/-- **AEAD Collision MBO Bound** (CR18, Theorem 6.1; Banfi, Lemma 2.3.9):
the doubly filtered hybrid $\mathbf{H}_{\mathsf{coll}}$ and the ideal system
$\mathsf{Ideal}\,\mathbf{E}_{\mathsf{enc}}(\Pi)$ satisfy
$\Delta(\mathbf{H}_{\mathsf{coll}}, \mathsf{Ideal}\,\mathbf{E}_{\mathsf{enc}}(\Pi)) \le q(\mathrm{enc})^2 / |\mathcal{M}|$. -/
theorem aead_collision_mbo_bound
    (scheme : Commons.SymmetricEncryption K M C)
    (q : Commons.AE.Port → ℕ) :
    Δ (AuthenticatedEncryption.Hybrid scheme q)
      (Commons.AE.Ideal.perPort M C (budget := q) •
        Commons.Encryption.system.perPort scheme
          (budget := Commons.AE.Ideal.insideBudget M C q)) ≤
      ((q .enc) ^ 2 / Fintype.card M : ℝ≥0) := by
  With notation (AuthenticatedEncryption.Hybrid scheme q) as "\\mathbf{H}_{\\mathsf{coll}}"
    explaining "the doubly filtered hybrid $\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)$"
  With notation (GameExamples.collision scheme q) as "\\hat{\\mathbf{G}}_{\\mathsf{coll}}"
    explaining "the AEAD collision MBO game whose underlying system is $\\mathbf{H}_{\\mathsf{coll}}$"
  With notation (Commons.AE.Ideal.perPort M C (budget := q) •
    Commons.Encryption.system.perPort scheme
      (budget := Commons.AE.Ideal.insideBudget M C q)) as "\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}(\\Pi)"
    explaining "the ideal AEAD system backed by encryption-only queries"
  proof_idea "We realize $\\mathbf{H}_{\\mathsf{coll}}$ as the underlying system of the collision MBO game $\\hat{\\mathbf{G}}_{\\mathsf{coll}}$, prove conditional equivalence with $\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}(\\Pi)$ until the collision event $E$ triggers the MBO, bound the probability of $E$ via a union bound, and apply the MBO Difference Lemma."
  Bad_event E := (AuthenticatedEncryption.collisionGame scheme q).badProbability
    because "that a plaintext collision occurs across the $q(\\mathrm{enc})$ encryption queries against the outer uniform replacement messages"
  We claim hEquiv :
      DistinctionGames.ConditionallyEquivalent (GameExamples.collision scheme q)
        (Commons.AE.Ideal.perPort M C (budget := q) •
          Commons.Encryption.system.perPort scheme
            (budget := Commons.AE.Ideal.insideBudget M C q)) by
    by_leaf "Whenever the collision event $E$ does not occur—no original encryption plaintext equals any outer replacement plaintext—the doubly filtered hybrid answers encryption queries with fresh random ciphertexts and replay decryption queries identically to $\\mathsf{Ideal}\\,\\mathbf{E}_{\\mathsf{enc}}(\\Pi)$." {
      exact GameExamples.collision_conditionallyEquivalent scheme q
    }
  We claim hWinBound :
      ∀ D' : CompatDistinguisher (Commons.AE.perPort M C q),
        winProb D' (GameExamples.collision scheme q) ≤
          (q .enc : ℝ) ^ 2 / Fintype.card M by
    by_leaf "Every admitted query trace of a compatible distinguisher $D'$ issues at most $q(\\mathrm{enc})$ encryption queries against $q(\\mathrm{enc})$ independent uniform replacement plaintexts in $\\mathcal{M}$; summing $1/|\\mathcal{M}|$ over all $q(\\mathrm{enc})^2$ pairs via a union bound bounds $\\Pr[E]$ by $q(\\mathrm{enc})^2 / |\\mathcal{M}|$, giving $\\Gamma^{D'}(\\hat{\\mathbf{G}}_{\\mathsf{coll}}) \\le q(\\mathrm{enc})^2 / |\\mathcal{M}|$." {
      intro D'
      have hBadTrace := AuthenticatedEncryption.collisionGame_badProbability_le scheme q
      change ∀ xs, xs = [] ∨ (Commons.AE.perPort M C q).domain xs →
        E xs ≤ (q .enc : ℝ) ^ 2 / Fintype.card M at hBadTrace
      have _ := hBadTrace
      exact GameExamples.collision_win_le scheme q ⟨D', rfl⟩
    }
  Conclude_difference_lemma using [hEquiv, hWinBound] by
    exact AuthenticatedEncryption.hybrid_ideal_distance_le scheme q

end AEADCollision

/-! ## B6: The H-Coefficient Method and General-N Tightness (Jha §2.2 Lem 2.2.1 / Cor 2.2.2) -/

private lemma tvDist_eq_tvExcessOn_add {A : Interface} (R S : TypedSystem A)
    (B : Transcript A → Prop) (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
    (hE : A.inputDomain.Compatible E) :
    tvDist (transcriptLaw R E n) (transcriptLaw S E n) =
      tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) B +
        tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) (goodSet B) := by
  classical
  have hRlaw : (transcriptLaw R E n).isProbDist := R.1.sLaw_isProbDist (hE R.1 R.2) n
  have hSlaw : (transcriptLaw S E n).isProbDist := S.1.sLaw_isProbDist (hE S.1 S.2) n
  have hEqW : (transcriptLaw R E n).weight = (transcriptLaw S E n).weight :=
    hRlaw.weight_eq.trans hSlaw.weight_eq.symm
  rw [tvDist, Probability.statDist_symm_of_eq_weight _ _ hEqW,
    Probability.statDist_eq_sum_of_support_subset _ _
      (Finsupp.support_sub :
        (transcriptLaw S E n - transcriptLaw R E n).support ⊆
          (transcriptLaw S E n).support ∪ (transcriptLaw R E n).support)]
  have hSplit := (Finset.sum_filter_add_sum_filter_not
    ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support) B
    (fun τ => max (transcriptLaw S E n τ - transcriptLaw R E n τ) 0)).symm
  refine hSplit.trans ?_
  unfold tvExcessOn goodSet
  exact congrArg₂ (· + ·)
    (Finset.sum_congr (by ext τ; simp) (fun _ _ => rfl))
    (Finset.sum_congr (by ext τ; simp) (fun _ _ => rfl))

private lemma tvExcessOn_bad_le {A : Interface} (R S : TypedSystem A)
    (B : Transcript A → Prop) (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
    (hE : A.inputDomain.Compatible E) :
    tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) B ≤ idealBadProb S E n B := by
  classical
  have hRnn : (transcriptLaw R E n).NonNeg := (R.1.sLaw_isProbDist (hE R.1 R.2) n).1
  have hSnn : (transcriptLaw S E n).NonNeg := (S.1.sLaw_isProbDist (hE S.1 S.2) n).1
  unfold tvExcessOn
  have hLe :
      ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter B,
          max (transcriptLaw S E n τ - transcriptLaw R E n τ) 0 ≤
        ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter B,
          transcriptLaw S E n τ :=
    Finset.sum_le_sum fun τ _ => max_le (sub_le_self _ (hRnn τ)) (hSnn τ)
  refine hLe.trans_eq ?_
  unfold idealBadProb Probability.probBad
  symm
  have hMass :
      (S.1.sLaw E.1 n).mass B =
        ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter B,
          transcriptLaw S E n τ :=
    Probability.Distribution.mass_eq_sum_of_support_subset (transcriptLaw S E n)
      (s := (transcriptLaw S E n).support ∪ (transcriptLaw R E n).support)
      Finset.subset_union_left B
  refine hMass.trans ?_
  exact Finset.sum_congr (by ext τ; simp) (fun _ _ => rfl)

private lemma tvExcessOn_good_le {A : Interface} (R S : TypedSystem A)
    (B : Transcript A → Prop) (ε₂ : ℝ≥0)
    (hRatio : ∀ τ : Transcript A, ¬ B τ → (1 - (ε₂ : ℝ)) * S.1 τ ≤ R.1 τ)
    (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ)
    (hE : A.inputDomain.Compatible E) :
    tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) (goodSet B) ≤
      (ε₂ : ℝ) * idealGoodProb S E n B := by
  classical
  have hSnn : (transcriptLaw S E n).NonNeg := (S.1.sLaw_isProbDist (hE S.1 S.2) n).1
  have hLawRatio : ∀ τ : Transcript A, goodSet B τ →
      (1 - (ε₂ : ℝ)) * transcriptLaw S E n τ ≤ transcriptLaw R E n τ := by
    intro τ hτ
    change (1 - (ε₂ : ℝ)) * S.1.sLaw E.1 n τ ≤ R.1.sLaw E.1 n τ
    rw [RandomSystem.sLaw_apply (R := S.1) (σ := E.1) n τ,
      RandomSystem.sLaw_apply (R := R.1) (σ := E.1) n τ]
    split_ifs
    · exact hRatio τ hτ
    · rw [mul_zero]
  have hPt : ∀ τ : Transcript A, goodSet B τ →
      max (transcriptLaw S E n τ - transcriptLaw R E n τ) 0 ≤
        (ε₂ : ℝ) * transcriptLaw S E n τ := by
    intro τ hτ
    refine max_le ?_ (mul_nonneg ε₂.coe_nonneg (hSnn τ))
    have h := hLawRatio τ hτ
    rw [sub_mul, one_mul] at h
    linarith
  unfold tvExcessOn
  have hLe :
      ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter (goodSet B),
          max (transcriptLaw S E n τ - transcriptLaw R E n τ) 0 ≤
        ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter (goodSet B),
          (ε₂ : ℝ) * transcriptLaw S E n τ :=
    Finset.sum_le_sum fun τ hτ => hPt τ (Finset.mem_filter.mp hτ).2
  refine hLe.trans_eq ?_
  rw [← Finset.mul_sum]
  congr 1
  unfold idealGoodProb
  symm
  have hMass :
      (S.1.sLaw E.1 n).mass (fun τ => ¬ B τ) =
        ∑ τ ∈ ((transcriptLaw S E n).support ∪ (transcriptLaw R E n).support).filter (goodSet B),
          transcriptLaw S E n τ :=
    Probability.Distribution.mass_eq_sum_of_support_subset (transcriptLaw S E n)
      (s := (transcriptLaw S E n).support ∪ (transcriptLaw R E n).support)
      Finset.subset_union_left (goodSet B)
  refine hMass.trans ?_
  exact Finset.sum_congr (by ext τ; simp) (fun _ _ => rfl)

/-- **The H-Coefficient Method** (Jha, §2.2, Lemma 2.2.1 / Corollary 2.2.2):
for any real and ideal systems $\mathbf{R}, \mathbf{S}$ and bad transcript set $\mathcal{T}_{\mathrm{bad}}$,
if (i) under every compatible $n$-query deterministic environment $E$, the ideal transcript falls in
$\mathcal{T}_{\mathrm{bad}}$ with probability at most $\varepsilon_1$, and (ii) every good
transcript $\tau \notin \mathcal{T}_{\mathrm{bad}}$ satisfies the ratio lower bound
$(1 - \varepsilon_2)\mathbf{S}(\tau) \le \mathbf{R}(\tau)$, then
$\Delta(\mathbf{R}, \mathbf{S}) \le \varepsilon_1 + \varepsilon_2$. -/
theorem h_coefficient_method
    {A : Interface} (R S : TypedSystem A)
    (T_bad : TranscriptSubset A)
    (ε₁ ε₂ : ℝ≥0)
    (hBad : ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ),
      QueryBounded n E → A.inputDomain.Compatible E →
      idealBadProb S E n T_bad.toPred ≤ ε₁)
    (hRatio : ∀ τ : Transcript A, τ ∉ T_bad → (1 - (ε₂ : ℝ)) * S.1 τ ≤ R.1 τ) :
    Δ R S ≤ ε₁ + ε₂ := by
  With notation R as "\\mathbf{R}" explaining "the real random system"
  With notation S as "\\mathbf{S}" explaining "the ideal random system"
  With notation T_bad as "\\mathcal{T}_{\\mathrm{bad}}"
    explaining "the set of bad transcripts"
  proof_idea "Fix a compatible $n$-query deterministic environment $E$. We express the total-variation distance $\\delta(\\mathcal{L}(\\mathbf{R}, E, n), \\mathcal{L}(\\mathbf{S}, E, n))$ as a one-sided sum over $\\mathcal{T}(A)$, partition into $\\mathcal{T}_{\\mathrm{bad}}$ and $\\overline{\\mathcal{T}_{\\mathrm{bad}}}$, bound the bad-transcript sum by $\\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\mathcal{T}_{\\mathrm{bad}}] \\le \\varepsilon_1$ and the good-transcript sum by $\\varepsilon_2 \\cdot \\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\overline{\\mathcal{T}_{\\mathrm{bad}}}] \\le \\varepsilon_2$, and take the supremum over $E$."
  By "the definition of $\\Delta(\\mathbf{R}, \\mathbf{S})$ as a supremum over compatible environments" it suffices to show hFixedEnv :
      ∀ (E : DDE (Σ i, A.X i) (Σ i, A.Y i)) (n : ℕ),
        QueryBounded n E → A.inputDomain.Compatible E →
        tvDist (transcriptLaw R E n) (transcriptLaw S E n) ≤ (ε₁ : ℝ) + (ε₂ : ℝ) by {
    by_leaf "Taking the supremum over all such environments $E$ yields $\\Delta(\\mathbf{R}, \\mathbf{S}) \\le \\varepsilon_1 + \\varepsilon_2$." {
      rw [SystemAlgebra.Interface.cc_distance_eq, ← ENNReal.coe_add]
      refine SystemAlgebra.RandomSystem.transcriptDistance_le fun E n hn hE => ?_
      change tvDist (transcriptLaw R E n) (transcriptLaw S E n) ≤ ((ε₁ + ε₂ : ℝ≥0) : ℝ)
      push_cast
      exact hFixedEnv E n hn hE
    }
  }
  intro E n hn hE
  We claim hPartition :
      tvDist (transcriptLaw R E n) (transcriptLaw S E n) =
        tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) T_bad.toPred +
          tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) (goodSet T_bad.toPred) by
    by_leaf "Since $\\mu^{\\mathrm{real}} = \\mathcal{L}(\\mathbf{R}, E, n)$ and $\\mu^{\\mathrm{id}} = \\mathcal{L}(\\mathbf{S}, E, n)$ are normalized probability distributions of weight $1$, symmetry of total-variation distance expresses $\\delta(\\mu^{\\mathrm{real}}, \\mu^{\\mathrm{id}}) = \\sum_{\\tau \\in \\mathcal{T}(A)} \\max(0, \\mu^{\\mathrm{id}}(\\tau) - \\mu^{\\mathrm{real}}(\\tau))$ as a one-sided excess sum, which partitions cleanly into $\\tau \\in \\mathcal{T}_{\\mathrm{bad}}$ and $\\tau \\notin \\mathcal{T}_{\\mathrm{bad}}$." {
      exact tvDist_eq_tvExcessOn_add R S T_bad.toPred E n hE
    }
  We claim hBadSum :
      tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) T_bad.toPred ≤ (ε₁ : ℝ) by
    We note hBadDom :
        tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) T_bad.toPred ≤
          idealBadProb S E n T_bad.toPred by
      by_leaf "On every bad transcript $\\tau \\in \\mathcal{T}_{\\mathrm{bad}}$, nonnegativity of $\\mu^{\\mathrm{real}}(\\tau)$ and $\\mu^{\\mathrm{id}}(\\tau)$ gives $\\max(0, \\mu^{\\mathrm{id}}(\\tau) - \\mu^{\\mathrm{real}}(\\tau)) \\le \\mu^{\\mathrm{id}}(\\tau)$, so summing over $\\tau \\in \\mathcal{T}_{\\mathrm{bad}}$ is at most $\\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\mathcal{T}_{\\mathrm{bad}}]$." {
        exact tvExcessOn_bad_le R S T_bad.toPred E n hE
      }
    by_leaf "Combining with the assumed ideal bad-transcript probability bound $\\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\mathcal{T}_{\\mathrm{bad}}] \\le \\varepsilon_1$ yields at most $\\varepsilon_1$." {
      exact hBadDom.trans (hBad E n hn hE)
    }
  We claim hGoodSum :
      tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) (goodSet T_bad.toPred) ≤ (ε₂ : ℝ) by
    We note hGoodDom :
        tvExcessOn (transcriptLaw R E n) (transcriptLaw S E n) (goodSet T_bad.toPred) ≤
          (ε₂ : ℝ) * idealGoodProb S E n T_bad.toPred by
      by_leaf "On every good transcript $\\tau \\notin \\mathcal{T}_{\\mathrm{bad}}$, the ratio condition $(1 - \\varepsilon_2)\\mu^{\\mathrm{id}}(\\tau) \\le \\mu^{\\mathrm{real}}(\\tau)$ rearranges to $\\max(0, \\mu^{\\mathrm{id}}(\\tau) - \\mu^{\\mathrm{real}}(\\tau)) \\le \\varepsilon_2\\,\\mu^{\\mathrm{id}}(\\tau)$; summing over $\\tau \\notin \\mathcal{T}_{\\mathrm{bad}}$ gives at most $\\varepsilon_2 \\cdot \\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\overline{\\mathcal{T}_{\\mathrm{bad}}}]$." {
        exact tvExcessOn_good_le R S T_bad.toPred ε₂ hRatio E n hE
      }
    by_leaf "Since $\\mathcal{L}(\\mathbf{S}, E, n)$ is a probability distribution, $\\Pr_{\\mathcal{L}(\\mathbf{S}, E, n)}[\\overline{\\mathcal{T}_{\\mathrm{bad}}}] \\le 1$, so the good-transcript excess is at most $\\varepsilon_2$." {
      have hSw := S.1.sLaw_isProbDist (hE S.1 S.2) n
      have hGoodLe1 : idealGoodProb S E n T_bad.toPred ≤ 1 :=
        (Probability.Distribution.mass_le_weight hSw.1 _).trans_eq hSw.2
      exact hGoodDom.trans (by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hGoodLe1 ε₂.coe_nonneg)
    }
  by_leaf "Summing the bad- and good-transcript bounds gives $\\delta(\\mathcal{L}(\\mathbf{R}, E, n), \\mathcal{L}(\\mathbf{S}, E, n)) \\le \\varepsilon_1 + \\varepsilon_2$." {
    rw [hPartition]
    exact add_le_add hBadSum hGoodSum
  }

section PointVsUniform

private def pointQuery (D : Type) [Fintype D] :
    DDE (Σ i, (pointInterface D).X i) (Σ i, (pointInterface D).Y i) :=
  DDE.ofQueries [⟨(), ()⟩]

private def targetTranscript {D : Type} [Fintype D] (x₀ : D) :
    List ((Σ i, (pointInterface D).X i) × (Σ i, (pointInterface D).Y i)) :=
  [(⟨(), ()⟩, ⟨(), x₀⟩)]

private lemma pointQuery_bounded (D : Type) [Fintype D] : QueryBounded 1 (pointQuery D) := by
  intro ys hd
  cases ys with
  | nil => simp
  | cons _ _ =>
      simp only [pointQuery, DDE.ofQueries, SystemAlgebra.fixedQueries, List.length_cons,
        List.getElem?_cons_succ, List.getElem?_nil] at hd
      exact absurd hd (by simp)

private lemma pointQuery_compatible (D : Type) [Fintype D] :
    (pointInterface D).inputDomain.Compatible (pointQuery D) := by
  intro _ _ h x _ _ hx
  have hh : h.length = 0 := by
    have hb := pointQuery_bounded D (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp only [List.length_map] at hb
    omega
  have he : h = [] := List.length_eq_zero_iff.mp hh
  subst h
  simp [pointInterface, Interface.queryBudget, Interface.inputDomain, Domain.ofInputs]

private lemma targetTranscript_good {D : Type} [Fintype D] (x₀ : D) :
    Good (pointQuery D).1 1 (targetTranscript x₀) := by
  constructor
  · apply (FollowsStrategy.snoc_iff (h := [])).mpr
    refine ⟨FollowsStrategy.nil, ?_⟩
    simp [pointQuery, DDE.ofQueries, SystemAlgebra.fixedQueries]
  · exact Or.inl rfl

private noncomputable def pointObserver {D : Type} [Fintype D] (x₀ : D) :
    (pointInterface D).inputDomain.Distinguisher :=
  Distribution.ProbDist.single
    ⟨envProbe (pointQuery D) (fun t => t.1.zip t.2 = targetTranscript x₀),
      envProbe_isDDD (pointQuery_bounded D),
      Domain.envProbe_decisionCompatible (pointQuery_compatible D) _⟩

private noncomputable def pointObserverBehavior {D : Type} [Fintype D] (x₀ : D) :
    TypedDistinguisher (pointInterface D) :=
  (pointObserver x₀).behavior

private lemma pointObserver_fixed_prob {D : Type} [Fintype D] [DecidableEq D] (x₀ x : D) :
    (pointObserverBehavior x₀).1 (pointFixed x) = if x = x₀ then 1 else 0 := by
  change (pointObserver x₀).probability (pointFixed x).1 = if x = x₀ then 1 else 0
  simp only [pointObserver, Distribution.ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul]
  rw [RandomSystem.decisionProbability_envProbe (pointQuery_bounded D) _ (pointFixed x).2]
  have zip_proj (h : List ((Σ i, (pointInterface D).X i) × (Σ i, (pointInterface D).Y i))) :
      (h.map Prod.fst).zip (h.map Prod.snd) = h := (List.zip_of_prod rfl rfl).symm
  simp only [zip_proj]
  rw [Distribution.mass_singleton, RandomSystem.sLaw_apply, ite_eq_left (targetTranscript_good x₀)]
  by_cases hx : x = x₀
  · subst hx
    simp [pointFixed, TypedSystem.ofFunction_mass, pointInterface, Interface.queryBudget,
      targetTranscript]
  · simp [pointFixed, TypedSystem.ofFunction_mass, pointInterface, Interface.queryBudget,
      targetTranscript, hx, Ne.symm hx]

private lemma pointObserver_ideal_prob {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (x₀ : D) :
    (pointObserverBehavior x₀).1 (pointIdeal D) = 1 / (Fintype.card D : ℝ) := by
  change (pointObserver x₀).probability (pointIdeal D).1 = 1 / (Fintype.card D : ℝ)
  rw [pointIdeal, TypedSystem.sample, Domain.Distinguisher.probability_mix]
  have hsingle : ∀ x : D,
      Distribution.uniform D x * (pointObserver x₀).probability (pointFixed x).1 =
        if x = x₀ then 1 / (Fintype.card D : ℝ) else 0 := by
    intro x
    have hp := pointObserver_fixed_prob x₀ x
    change (pointObserver x₀).probability (pointFixed x).1 = if x = x₀ then 1 else 0 at hp
    rw [hp, Distribution.uniform_apply]
    split_ifs <;> simp
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [hsingle, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

private lemma nnreal_one_sub_inv_card_coe {D : Type} [Fintype D] [Nonempty D] :
    (((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ℝ)) = 1 - 1 / (Fintype.card D : ℝ) := by
  have hle : (1 / (Fintype.card D : ℝ≥0)) ≤ 1 := by
    have hc : (1 : ℝ≥0) ≤ Fintype.card D := by exact_mod_cast Fintype.card_pos (α := D)
    exact div_le_one_of_le₀ hc zero_le
  rw [NNReal.coe_sub hle]
  simp

private lemma pointIdeal_badMass_le {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (x₀ : D)
    (E : DDE (Σ i, (pointInterface D).X i) (Σ i, (pointInterface D).Y i)) (n : ℕ)
    (hE : (pointInterface D).inputDomain.Compatible E) :
    idealBadProb (pointIdeal D) E n (BadReply x₀) ≤ ((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ℝ) := by
  have hCardPos : 0 < Fintype.card D := Fintype.card_pos (α := D)
  let badEmb :
      D ↪ List ((Σ i, (pointInterface D).X i) × (Σ i, (pointInterface D).Y i)) :=
    ⟨fun y => [(⟨(), ()⟩, ⟨(), y⟩)], fun y₁ y₂ heq => by cases heq; rfl⟩
  have hLawNN : ((pointIdeal D).1.sLaw E.1 n).NonNeg :=
    ((pointIdeal D).1.sLaw_isProbDist (hE _ (pointIdeal D).2) n).1
  have hSub :
      Probability.probBad ((pointIdeal D).1.sLaw E.1 n) (BadReply x₀) ≤
        ∑ y ∈ Finset.univ.erase x₀,
          ((pointIdeal D).1.sLaw E.1 n) [(⟨(), ()⟩, ⟨(), y⟩)] := by
    let : DecidablePred (BadReply x₀) := Classical.decPred (BadReply x₀)
    rw [Probability.probBad, Probability.Distribution.mass, Finsupp.sum, ← Finset.sum_filter]
    have hMap :
        ∑ h ∈ (Finset.univ.erase x₀).map badEmb, ((pointIdeal D).1.sLaw E.1 n) h =
          ∑ y ∈ Finset.univ.erase x₀,
            ((pointIdeal D).1.sLaw E.1 n) [(⟨(), ()⟩, ⟨(), y⟩)] :=
      Finset.sum_map _ _ _
    rw [← hMap]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hLawNN h)
    intro h hh
    obtain ⟨_, y, hy, rfl⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_map.mpr ⟨y, Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩, rfl⟩
  have hPt : ∀ y : D,
      ((pointIdeal D).1.sLaw E.1 n) [(⟨(), ()⟩, ⟨(), y⟩)] ≤ 1 / (Fintype.card D : ℝ) := by
    intro y
    have hs : ((pointIdeal D).1.sLaw E.1 n) [(⟨(), ()⟩, ⟨(), y⟩)] ≤
        (pointIdeal D).1 [(⟨(), ()⟩, ⟨(), y⟩)] := by
      rw [RandomSystem.sLaw_apply]
      split_ifs
      · exact le_rfl
      · exact (pointIdeal D).1.mass_nonneg _
    have hid : (pointIdeal D).1 [(⟨(), ()⟩, ⟨(), y⟩)] = 1 / (Fintype.card D : ℝ) := by
      rw [pointIdeal, TypedSystem.sample_mass, Finset.sum_eq_single y]
      · have hm : (pointFixed y).1 [(⟨(), ()⟩, ⟨(), y⟩)] = 1 := by
          apply TypedSystem.ofFunction_mass_eq_one
          · right; simp [pointInterface, Interface.queryBudget]
          · simp
        rw [hm, Probability.Distribution.uniform_apply, mul_one]
      · intro c _ hcy
        have hm : (pointFixed c).1 [(⟨(), ()⟩, ⟨(), y⟩)] = 0 := by
          rw [pointFixed, TypedSystem.ofFunction_mass, ite_eq_right]
          intro hc
          exact hcy (congrArg Sigma.snd (hc.2 (⟨(), ()⟩, ⟨(), y⟩) (by simp))).symm
        rw [hm, mul_zero]
      · intro hyNot
        exfalso
        apply hyNot
        rw [Finsupp.mem_support_iff, Probability.Distribution.uniform_apply]
        positivity
    exact hs.trans_eq hid
  have hSumBound :
      ∑ y ∈ Finset.univ.erase x₀,
          ((pointIdeal D).1.sLaw E.1 n) [(⟨(), ()⟩, ⟨(), y⟩)] ≤
        ∑ _ ∈ Finset.univ.erase x₀, (1 / (Fintype.card D : ℝ)) :=
    Finset.sum_le_sum fun y _ => hPt y
  have hEraseCard :
      ((Finset.univ.erase x₀ : Finset D).card : ℝ) = (Fintype.card D : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x₀), Finset.card_univ]
    have hc1 : 1 ≤ Fintype.card D := by omega
    rw [Nat.cast_sub hc1, Nat.cast_one]
  have hFinal :
      ∑ _ ∈ Finset.univ.erase x₀, (1 / (Fintype.card D : ℝ)) =
        1 - 1 / (Fintype.card D : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hEraseCard]
    have hne : (Fintype.card D : ℝ) ≠ 0 := by
      exact_mod_cast (show Fintype.card D ≠ 0 by omega)
    field_simp
  change Probability.probBad ((pointIdeal D).1.sLaw E.1 n) (BadReply x₀) ≤ _
  rw [nnreal_one_sub_inv_card_coe]
  exact hSub.trans (hSumBound.trans_eq hFinal)

/-- **Tightness of Point-vs-Uniform Distinguishing** (Jha §2.2 / Optimal Single-Query Gap):
over any finite domain $D$ with $|D| \ge 2$, the single-query constant system $\mathbf{F}_{x_0}$
and the uniform sampling system $\mathbf{F}_{\mathrm{rand}}$ have exact distinguishing advantage
$\Delta(\mathbf{F}_{x_0}, \mathbf{F}_{\mathrm{rand}}) = 1 - 1/|D|$.
The lower bound is witnessed by an explicit testing distinguisher checking for $x_0$, while the
matching upper bound follows from the H-coefficient method with bad replies $y \ne x_0$. -/
theorem point_vs_uniform_tightness
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    (hCard : 2 ≤ Fintype.card D) (x₀ : D) :
    Δ (pointFixed x₀) (pointIdeal D) =
      ((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ENNReal) := by
  With notation (pointFixed x₀) as "\\mathbf{F}_{x_0}"
    explaining "the constant single-query system outputting $x_0 \\in D$"
  With notation (pointIdeal D) as "\\mathbf{F}_{\\mathrm{rand}}"
    explaining "the uniform single-query system sampling $x \\leftarrow \\mathcal{U}(D)$"
  With notation (pointObserverBehavior x₀) as "\\mathcal{D}_{x_0}"
    explaining "the one-query distinguisher returning $1$ iff the reply equals $x_0$"
  proof_idea "We prove matching lower and upper bounds on $\\Delta(\\mathbf{F}_{x_0}, \\mathbf{F}_{\\mathrm{rand}})$: an explicit one-query distinguisher $\\mathcal{D}_{x_0}$ achieves advantage $1 - 1/|D|$, while the H-coefficient method with bad transcripts $\\{\\tau_y : y \\ne x_0\\}$ matches $1 - 1/|D|$ with zero ratio loss on good transcripts."
  We claim hLower :
      ((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ENNReal) ≤
        Δ (pointFixed x₀) (pointIdeal D) by
    We note hAdv :
        ENNReal.ofReal |obsProb (pointObserverBehavior x₀) (pointFixed x₀) -
            obsProb (pointObserverBehavior x₀) (pointIdeal D)| ≤
          Δ (pointFixed x₀) (pointIdeal D) by
      by_leaf "Since $\\mathcal{D}_{x_0}$ is compatible, its advantage is at most $\\Delta(\\mathbf{F}_{x_0}, \\mathbf{F}_{\\mathrm{rand}})$." {
        rw [SystemAlgebra.Interface.cc_distance_eq]
        exact Domain.DistinguisherBehavior.advantage_le_transcriptDistance
          (pointObserverBehavior x₀) (pointFixed x₀) (pointIdeal D)
      }
    by_leaf "Acceptance is $1$ on $\\mathbf{F}_{x_0}$ and $1/|D|$ on $\\mathbf{F}_{\\mathrm{rand}}$, yielding distinguishing advantage $1 - 1/|D|$." {
      have hFix : obsProb (pointObserverBehavior x₀) (pointFixed x₀) = 1 := by
        simpa only [obsProb, ↓reduceIte] using pointObserver_fixed_prob x₀ x₀
      have hId : obsProb (pointObserverBehavior x₀) (pointIdeal D) = 1 / (Fintype.card D : ℝ) :=
        pointObserver_ideal_prob x₀
      have hNonneg : 0 ≤ 1 - 1 / (Fintype.card D : ℝ) := by
        have hc : (1 : ℝ) ≤ Fintype.card D := by
          exact_mod_cast (show 1 ≤ Fintype.card D by omega)
        linarith [div_le_one_of_le₀ hc (by positivity)]
      have hVal :
          |obsProb (pointObserverBehavior x₀) (pointFixed x₀) -
              obsProb (pointObserverBehavior x₀) (pointIdeal D)| =
            (((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ℝ)) := by
        rw [hFix, hId, nnreal_one_sub_inv_card_coe, abs_of_nonneg hNonneg]
      rw [hVal, ENNReal.ofReal_coe_nnreal] at hAdv
      exact hAdv
    }
  We claim hUpper :
      Δ (pointFixed x₀) (pointIdeal D) ≤
        ((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ENNReal) by
    Split_transcripts Bad : TranscriptSubset (pointInterface D) := BadReply x₀
      because "declaring single-query transcripts $\\tau_y$ with reply $y \\ne x_0$ to be bad"
    We note hBadMass :
        ∀ (E : DDE (Σ i, (pointInterface D).X i) (Σ i, (pointInterface D).Y i)) (n : ℕ),
          QueryBounded n E → (pointInterface D).inputDomain.Compatible E →
          idealBadProb (pointIdeal D) E n Bad.toPred ≤ ((1 - 1 / (Fintype.card D : ℝ≥0) : ℝ≥0) : ℝ) by
      by_leaf "Each of the $|D| - 1$ bad single-query transcripts $\\tau_y$ returning $y \\ne x_0$ has probability mass at most $1/|D|$ under $\\mathcal{L}(\\mathbf{F}_{\\mathrm{rand}}, E, n)$, summing to $1 - 1/|D|$." {
        exact fun E n _ hE => pointIdeal_badMass_le x₀ E n hE
      }
    We note hGoodRatio :
        ∀ τ : Transcript (pointInterface D),
          τ ∉ Bad → sysProb (pointIdeal D) τ ≤ sysProb (pointFixed x₀) τ by
      by_leaf "On the empty transcript $\\tau_{\\emptyset}$, both systems assign mass $1$ ($1 \\le 1$); on the single-query transcript $\\tau_{x_0}$ returning $x_0$, $\\mathbf{F}_{\\mathrm{rand}}(\\tau_{x_0}) = 1/|D| \\le 1 = \\mathbf{F}_{x_0}(\\tau_{x_0})$; and all transcripts exceeding query budget $1$ vanish under both systems." {
          intro τ hGood
          dsimp only [sysProb]
          cases τ with
          | nil =>
              have hFixNil : (pointFixed x₀).1 [] = 1 :=
                RandomSystem.mass_nil (pointFixed x₀).1
              have hIdNil : (pointIdeal D).1 [] = 1 :=
                RandomSystem.mass_nil (pointIdeal D).1
              rw [hFixNil, hIdNil]
          | cons hd tl =>
              cases tl with
              | nil =>
                  rcases hd with ⟨⟨i, x⟩, ⟨j, y⟩⟩
                  cases i; cases x; cases j
                  dsimp only [pointInterface, Interface.queryBudget] at y
                  by_cases hy : y = x₀
                  · subst hy
                    have hFix1 : (pointFixed y).1 [(⟨(), ()⟩, ⟨(), y⟩)] = 1 := by
                      apply TypedSystem.ofFunction_mass_eq_one
                      · right; simp [pointInterface, Interface.queryBudget]
                      · simp
                    have hId1 : (pointIdeal D).1 [(⟨(), ()⟩, ⟨(), y⟩)] =
                        1 / (Fintype.card D : ℝ) := by
                      rw [pointIdeal, TypedSystem.sample_mass, Finset.sum_eq_single y]
                      · rw [hFix1, Probability.Distribution.uniform_apply, mul_one]
                      · intro c _ hcy
                        have hm : (pointFixed c).1 [(⟨(), ()⟩, ⟨(), y⟩)] = 0 := by
                          rw [pointFixed, TypedSystem.ofFunction_mass, ite_eq_right]
                          intro hc
                          exact hcy (congrArg Sigma.snd (hc.2 (⟨(), ()⟩, ⟨(), y⟩) (by simp))).symm
                        rw [hm, mul_zero]
                      · intro hyNot
                        exfalso
                        apply hyNot
                        rw [Finsupp.mem_support_iff, Probability.Distribution.uniform_apply]
                        positivity
                    rw [hFix1, hId1]
                    have hc : (1 : ℝ) ≤ Fintype.card D := by exact_mod_cast (show 1 ≤ Fintype.card D by omega)
                    exact div_le_one_of_le₀ hc (by positivity)
                  · exact (hGood ⟨y, hy, rfl⟩).elim
              | cons hd2 tl2 =>
                  have hzero : ∀ c : D, (pointFixed c).1 (hd :: hd2 :: tl2) = 0 := fun c => by
                    rw [pointFixed, TypedSystem.ofFunction_mass, ite_eq_right]
                    rintro ⟨hnil | hdom, _⟩
                    · simp at hnil
                    · have hlen := (pointInterface D).length_le _ hdom
                      simp only [pointInterface, Interface.queryBudget, List.length_map,
                        List.length_cons] at hlen
                      omega
                  have hId0 : (pointIdeal D).1 (hd :: hd2 :: tl2) = 0 := by
                    rw [pointIdeal, TypedSystem.sample_mass]
                    exact Finset.sum_eq_zero fun c _ => by simp [hzero c]
                  rw [hId0, hzero x₀]
      }
    Conclude_h_coeff using [hBadMass, hGoodRatio] by
      have hRes := h_coefficient_method (pointFixed x₀) (pointIdeal D) Bad
        (1 - 1 / (Fintype.card D : ℝ≥0)) 0 hBadMass (fun τ hτ => by
          simpa only [NNReal.coe_zero, sub_zero, one_mul, sysProb] using hGoodRatio τ hτ)
      simpa only [NNReal.coe_zero, ENNReal.coe_zero, add_zero] using hRes
  by_leaf "Combining the explicit distinguisher lower bound and the H-coefficient upper bound yields exact equality $\\Delta(\\mathbf{F}_{x_0}, \\mathbf{F}_{\\mathrm{rand}}) = 1 - 1/|D|$." {
    exact le_antisymm hUpper hLower
  }

end PointVsUniform

end

paper_register_ns Paper.GamesHCoeff randomSystems

paper_motivation Paper.GamesHCoeff
  "We present two central techniques for random systems in Register C: Maurer's monotone binary output (MBO) game-playing framework (CR18, Theorems 4.17 and 6.1) and Patarin's H-coefficient method (Jha, Lemma 2.2.1 and Corollary 2.2.2) together with an exact general-$N$ tightness application."
  (title := "Games, Monotone Binary Outputs, and the H-Coefficient Technique")

paper_setting_ns Paper.GamesHCoeff
  "Fix typed random-system interfaces $A, B$ with compatible distinguishers $D$ carrying decision advantage $\\Delta^D(\\mathbf{R}, \\mathbf{S})$ and winning probability $\\Gamma^D(\\hat{\\mathbf{G}})$ on games $\\hat{\\mathbf{G}}$ endowed with a monotone binary output (MBO). Say $\\hat{\\mathbf{G}} \\mid\\equiv \\mathbf{T}$ when $\\hat{\\mathbf{G}}$ behaves identically to $\\mathbf{T}$ conditioned on the MBO remaining unset, leaving the underlying system $\\hat{\\mathbf{G}}^{-}$ when the MBO is ignored."
  (suppress := ["A", "B", "K", "M", "C", "scheme", "q", "D"])
  (anchor := mbo_reduction_bound)
  (title := "Game Reductions and Monotone Binary Outputs")
  (register := randomSystems)

paper_construction aead_collision_mbo_bound "Game" "AEAD Collision-Hybrid System and MBO Game"
  "Following Banfi (§2.3.4) and Maurer (CR18, Theorem 6.1), we pair the doubly filtered AEAD hybrid with a monotone collision flag."
  (lines := [
    "Collision hybrid: $\\mathbf{H}_{\\mathsf{coll}} := \\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathsf{PTXT}\\,\\mathsf{CCA}\\,\\mathbf{E}_{\\mathsf{AE}}(\\Pi)$ under budget $q$",
    "Collision game: $\\hat{\\mathbf{G}}_{\\mathsf{coll}}$ has $\\mathbf{H}_{\\mathsf{coll}}$ as its underlying system $\\hat{\\mathbf{G}}_{\\mathsf{coll}}^-$ and sets its MBO to $1$ whenever an original encryption plaintext equals an outer replacement plaintext"
  ])

paper_setting h_coefficient_method
  "Over a typed random-system interface $A$, write $\\mathcal{T}(A)$ for the space of completed query–reply transcripts, $\\mathbf{R}(\\tau)$ and $\\mathbf{S}(\\tau)$ for the interpolation probabilities of $\\tau \\in \\mathcal{T}(A)$ under real and ideal systems $\\mathbf{R}, \\mathbf{S}$, and $\\mathcal{L}(\\mathbf{R}, E, n), \\mathcal{L}(\\mathbf{S}, E, n)$ for their induced transcript distributions under any compatible $n$-query deterministic environment $E$, with total-variation distance $\\delta(\\mu, \\nu) = \\sum_{\\tau \\in \\mathcal{T}(A)} \\max(0, \\nu(\\tau) - \\mu(\\tau))$ when $|\\mu| = |\\nu|$. Let $\\mathcal{T}_{\\mathrm{bad}} \\subseteq \\mathcal{T}(A)$ denote a bad transcript subset with complement $\\overline{\\mathcal{T}_{\\mathrm{bad}}}$; for the single-query tightness example on domain $D$, write $\\tau_{\\emptyset}$ for the empty transcript and $\\tau_y$ for the single-query transcript returning $y \\in D$."
  (suppress := ["A"])
  (title := "The H-Coefficient Method")
  (register := randomSystems)

informal_symbol Paper.GamesHCoeff.Transcript "\\mathcal{T}"
informal_symbol Paper.GamesHCoeff.pointInterface "\\mathcal{I}_{D}"
informal_hide_args Paper.GamesHCoeff.pointInterface 0
informal_symbol Commons.AE.Port "\\mathsf{Port}_{\\mathrm{AE}}"
informal_symbol Commons.AE.perPort "\\mathsf{AE}"
informal_symbol Commons.AE.system.perPort "\\mathbf{E}_{\\mathsf{AE}}"
informal_symbol Commons.Encryption.system.perPort "\\mathbf{E}_{\\mathsf{enc}}"
informal_symbol Commons.AE.PTXT.perPort "\\mathsf{PTXT}"
informal_hide_args Commons.AE.PTXT.perPort 0 1
informal_symbol Commons.AE.CCA.perPort "\\mathsf{CCA}"
informal_hide_args Commons.AE.CCA.perPort 0 1
informal_symbol Commons.AE.Ideal.perPort "\\mathsf{Ideal}"
informal_hide_args Commons.AE.Ideal.perPort 0 1
informal_symbol AuthenticatedEncryption.Hybrid "\\mathbf{H}_{\\mathsf{coll}}"
informal_hide_args AuthenticatedEncryption.Hybrid 0 1

informal_title mbo_reduction_bound "MBO Game-Playing Reduction under Converter Attachment"
informal_kind mbo_reduction_bound "Theorem"
informal_binder mbo_reduction_bound "α" "\\alpha"
informal_binder mbo_reduction_bound "G" "\\hat{\\mathbf{G}}"
informal_binder mbo_reduction_bound "T" "\\mathbf{T}"
informal_binder mbo_reduction_bound "ε" "\\varepsilon"
informal_binder mbo_reduction_bound "D" "D"

informal_title aead_collision_mbo_bound "AEAD Collision Bound via MBO Conditional Equivalence"
informal_kind aead_collision_mbo_bound "Theorem"
informal_binder aead_collision_mbo_bound "M" "\\mathcal{M}"
informal_binder aead_collision_mbo_bound "C" "\\mathcal{C}"
informal_binder aead_collision_mbo_bound "scheme" "\\Pi"
informal_theorem_notation aead_collision_mbo_bound
  (AuthenticatedEncryption.Hybrid scheme q) "\\mathbf{H}_{\\mathsf{coll}}"

informal_title h_coefficient_method "The H-Coefficient Method"
informal_kind h_coefficient_method "Theorem"
informal_binder h_coefficient_method "R" "\\mathbf{R}"
informal_binder h_coefficient_method "S" "\\mathbf{S}"
informal_binder h_coefficient_method "T_bad" "\\mathcal{T}_{\\mathrm{bad}}"
informal_binder h_coefficient_method "ε₁" "\\varepsilon_1"
informal_binder h_coefficient_method "ε₂" "\\varepsilon_2"

informal_title point_vs_uniform_tightness "Exact Advantage of Point-vs-Uniform Single-Query Systems"
informal_kind point_vs_uniform_tightness "Theorem"
informal_binder point_vs_uniform_tightness "x₀" "x_0"

end Paper.GamesHCoeff

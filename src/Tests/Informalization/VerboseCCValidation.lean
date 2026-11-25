/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Verbose
import Informalization.Render.Json
import Informalization.Render.Html
import Informalization.CLI
import Examples.PRGLengthExtension
import Examples.AuthenticatedEncryption.Security
import Examples.Games
import RandomSystems.Distance.RevealedHCoefficient
import RandomSystems.Typed.SamplingDistance
import RandomSystems.Typed.Distinguisher

/-!
# End-to-End Validation of Paper-Grounded Verbose-CC Authoring & Trace Decompilation

Five flagship Constructive Cryptography, Indifferentiability, Game-Playing, H-Coefficient,
and Tightness-Sandwich proofs authored with `open scoped VerboseCC`, with zero `sorry` and
only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`):

1. **PRG Length Extension** (`prgLengthExtension_verbose`): `Write`, `Introduce_hybrid`, `Claim`,
   `By_non_expansion`, `By_CC_routine`, and `By_hybrid_chain` with `because_of` step notes.
2. **Authenticated Encryption Composition** (`aeadComposition_verbose` &
   `aeadHybridReduction_verbose`): `It_suffices_to_show`, `By_context_insensitivity_right`,
   `By_sequential_composition`, `By_CC_routine`.
3. **Indifferentiability Serial Simulator Composition** (`indiffSerialComposition_verbose`):
   `Claim`, `Exhibit_simulator`, `Fact`, `Construct_using`, `Compose_simulators`.
4. **Games & Revealed Extended H-Technique** (`gameCollision_verbose` &
   `extendedHCoefficient_verbose`): `Ignore_MBO_of`, `By_conditional_equivalence`, and
   `By_extended_H_technique` dropping ideal-law, good-ratio, and bad-mass subgoals to Lean.
5. **Tightness Sandwich** (`bitDistinguishingTightness_verbose`): `Tightness_sandwich` splitting
   into matching `lower_bound` (with `Exhibit_distinguisher` and `Lower_bound_advantage_of`)
   and `upper_bound` (with `By_extended_H_technique`).
-/

namespace Tests.Informalization.VerboseCCValidation

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability Commons
open scoped NNReal SystemAlgebra
open scoped VerboseCC

noncomputable section

/-! ## Flagship 1: PRG Length Extension -/

/-- Doubling a PRG from `S → S × S` to `S → S × S × S` via the two-call converter constructions
`𝓡₁` and `𝓡₂` incurs at most `ε + ε` distinguishing distance against a uniform triple. -/
theorem prgLengthExtension_verbose
    {S : Type} [Fintype S] [Nonempty S]
    (G : S → S × S) {q : Commons.Evaluation.Port → ℕ} {ε : ENNReal}
    (hPRG : Δ (Examples.PRGLengthExtension.PRGReal.perPort G
      (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q))
      (Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]) ≤ ε) :
    Δ (Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G)
      (budget := q))
      (Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤ ε + ε := by
  Write U := Commons.MemorylessSource.perPort (S × S) 𝒰[S × S]
    (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q)
  Introduce_hybrid M₁ := Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) • U
  Introduce_hybrid M₂ := Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
    (@id (TypedSystem (Commons.Evaluation.perPort Unit (S × S)
      (Examples.PRGLengthExtension.𝓡₂.insideBudget S q))) U)
  Claim hFirstCall :
      Δ (Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) •
          Examples.PRGLengthExtension.PRGReal.perPort G
            (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q))
        M₁ ≤ ε by
    By_non_expansion
    exact hPRG
  Claim hSecondCall :
      Δ (Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
          Examples.PRGLengthExtension.PRGReal.perPort G
            (budget := Examples.PRGLengthExtension.𝓡₂.insideBudget S q))
        M₂ ≤ ε by
    By_non_expansion
    exact hPRG
  By_hybrid_chain {
    cc_calc statistical
      Examples.PRGLengthExtension.PRGReal.perPort (Examples.PRGLengthExtension.H G) (budget := q)
        = Examples.PRGLengthExtension.𝓡₁.perPort G (budget := q) •
            Examples.PRGLengthExtension.PRGReal.perPort G
              (budget := Examples.PRGLengthExtension.𝓡₁.insideBudget G q) :=
          because_of "by definition of the length-extending construction isolating the first PRG call" =>
            by
              By_CC_routine "rewriting the length extension as a converter attachment" {
                exact Examples.PRGLengthExtension.prgReal_H_eq G q
              }
      _ ≈[ε] M₁ :=
          because_of "by replacing the first PRG instance with a uniform pair via non-expansion" =>
            hFirstCall
      _ = Examples.PRGLengthExtension.𝓡₂.perPort S (budget := q) •
            Examples.PRGLengthExtension.PRGReal.perPort G
              (budget := Examples.PRGLengthExtension.𝓡₂.insideBudget S q) :=
          because_of "by regrouping the uniform prefix into the second-call converter" =>
            Examples.PRGLengthExtension.𝓡₁_smul_prgRand G q
      _ ≈[ε] M₂ :=
          because_of "by replacing the second PRG instance with a uniform pair via non-expansion" =>
            hSecondCall
      _ = Commons.MemorylessSource.perPort (S × S × S) 𝒰[S × S × S] (budget := q) :=
          because_of "by folding the two independent uniform pairs into a uniform triple" =>
            Examples.PRGLengthExtension.𝓡₂_smul_prgRand q
  }

informal_title prgLengthExtension_verbose "PRG Length Extension (Verbose-CC)"
informal_kind prgLengthExtension_verbose "Theorem"

/-! ## Flagship 2: Authenticated Encryption Composition & Reduction -/

/-- Context-insensitive lifting of a symmetric encryption step alongside an authentication key,
composed sequentially with an authenticated-encryption converter step. -/
theorem aeadComposition_verbose
    {A B C K : Interface}
    (encConv : B ⟶ A) (macConv : C ⟶ B ⊗ K)
    (realChannel : TypedSystem A) (cpaChannel : TypedSystem B)
    (macKey : TypedSystem K) (aeIdeal : TypedSystem C)
    {ε₁ ε₂ : ENNReal}
    (hEnc : ({realChannel} : Specification (TypedSystem A)) —[encConv; ε₁]→ {cpaChannel})
    (hMac : ({cpaChannel ∥ macKey} : Specification (TypedSystem (B ⊗ K)))
      —[macConv; ε₂]→ {aeIdeal}) :
    ({realChannel ∥ macKey} : Specification (TypedSystem (A ⊗ K)))
      —[macConv ≫ (encConv ▷ K); ε₁ + ε₂]→ {aeIdeal} := by
  It_suffices_to_show hLifted :
      ({realChannel ∥ macKey} : Specification (TypedSystem (A ⊗ K)))
        —[encConv ▷ K; ε₁]→ {cpaChannel ∥ macKey}
      because "by sequential composability with the outer authentication step" via
    By_sequential_composition hLifted and hMac
  By_context_insensitivity_right {macKey} using hEnc

informal_title aeadComposition_verbose "Authenticated Encryption Composition (Verbose-CC)"
informal_kind aeadComposition_verbose "Theorem"

/-- Concrete authenticated encryption distance decomposition combining the plaintext-integrity
and ciphertext-indistinguishability terms with the collision penalty. -/
theorem aeadHybridReduction_verbose
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : Commons.SymmetricEncryption K M C) (q : Commons.AE.Port → ℕ)
    {ε_p ε_c : ENNReal}
    (hPTXT : Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.PTXT.perPort M C (budget := q) •
        Commons.AE.system.perPort scheme (budget := q)) ≤ ε_p)
    (hCCA : Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.CCA.perPort M C (budget := q) •
        Commons.AE.system.perPort scheme (budget := q)) ≤ ε_c) :
    Δ (Commons.AE.system.perPort scheme (budget := q))
      (Commons.AE.Ideal.perPort M C (budget := q) •
        Commons.Encryption.system.perPort scheme (budget := Commons.AE.Ideal.insideBudget M C q)) ≤
      ε_p + ε_c + ε_p + ε_c +
        (((q Commons.AE.Port.enc : ℝ≥0) ^ 2 / (Fintype.card M : ℝ≥0) : ℝ≥0) : ENNReal) := by
  It_suffices_to_show hBase :
      Δ (Commons.AE.system.perPort scheme (budget := q))
        (Commons.AE.PTXT.perPort M C (budget := q) •
          Commons.AE.system.perPort scheme (budget := q)) +
          Δ (Commons.AE.system.perPort scheme (budget := q))
            (Commons.AE.CCA.perPort M C (budget := q) •
              Commons.AE.system.perPort scheme (budget := q)) +
        Δ (Commons.AE.system.perPort scheme (budget := q))
          (Commons.AE.PTXT.perPort M C (budget := q) •
            Commons.AE.system.perPort scheme (budget := q)) +
      Δ (Commons.AE.system.perPort scheme (budget := q))
        (Commons.AE.CCA.perPort M C (budget := q) •
          Commons.AE.system.perPort scheme (budget := q)) ≤
        ε_p + ε_c + ε_p + ε_c
      because "by the hybrid distance decomposition of authenticated encryption" via {
    By_CC_routine "combining the AEAD hybrid bound with the per-component distance assumptions" {
      exact (AuthenticatedEncryption.real_ideal_distance_le scheme q).trans
        (add_le_add hBase le_rfl)
    }
  }
  Combining {
    By_CC_routine "summing the plaintext-integrity and IND-CCA component bounds" {
      exact add_le_add (add_le_add (add_le_add hPTXT hCCA) hPTXT) hCCA
    }
  }

informal_title aeadHybridReduction_verbose "AEAD Hybrid Distance Decomposition (Verbose-CC)"
informal_kind aeadHybridReduction_verbose "Theorem"

/-! ## Flagship 3: Indifferentiability Serial Simulator Composition -/

/-- Serial composition of an indifferentiable protocol and an ideal-world application via
exhibition of the admitted simulator and composition-order invariance. -/
theorem indiffSerialComposition_verbose
    {H H' P Q B : Interface}
    (protocol : H ⊗ P ⟶ B) (application : H' ⟶ H)
    (simulators : Set (P ⟶ Q)) (simulator : P ⟶ Q) (admitted : simulator ∈ simulators)
    (real : TypedSystem B) (ideal : TypedSystem (H ⊗ Q)) (target : TypedSystem (H' ⊗ Q))
    {ε δ : ENNReal}
    (indifferentiable : Δ (protocol • real) ((H ◁ simulator) • ideal) ≤ ε)
    (idealApplication : Δ ((application ▷ Q) • ideal) target ≤ δ) :
    ({real} : Specification (TypedSystem B)) —[(application ▷ P) ≫ protocol]→
      Commons.Indifferentiability.specification target simulators (ε + δ) := by
  Claim hIndiff :
      ({real} : Specification (TypedSystem B)) —[protocol]→
        Commons.Indifferentiability.specification ideal simulators ε by
    Exhibit_simulator simulator for_interface P
    · exact admitted
    · exact indifferentiable
  Fact hApp :
      ({ideal} : Specification (TypedSystem (H ⊗ Q))) —[application ▷ Q; δ]→ {target} by
    Construct_using idealApplication
  Compose_simulators hIndiff and hApp

informal_title indiffSerialComposition_verbose "Indifferentiability Serial Simulator Composition (Verbose-CC)"
informal_kind indiffSerialComposition_verbose "Theorem"

/-! ## Flagship 4: Games & Revealed Extended H-Technique -/

/-- Any compatible solver's advantage between the AEAD collision-hybrid system and the ideal
AEAD system is bounded by the plaintext-collision game-winning bound. -/
theorem gameCollision_verbose
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : Commons.SymmetricEncryption K M C) (q : Commons.AE.Port → ℕ)
    {s : (TypedSystem (Commons.AE.perPort M C q) → ℝ) ×
      (TypedGame (Commons.AE.perPort M C q) → ℝ)}
    (hs : s ∈ ConstructiveCryptography.DistinctionGames.solvers (Commons.AE.perPort M C q)) :
    |s.1 (AuthenticatedEncryption.Hybrid scheme q) -
        s.1 (Commons.AE.Ideal.perPort M C • Commons.Encryption.system.perPort scheme)| ≤
      ↑(q Commons.AE.Port.enc) ^ 2 / ↑(Fintype.card M) := by
  Ignore_MBO_of (GameExamples.collision scheme q) via (GameExamples.collision_visible scheme q)
  It_suffices_to_show hWin :
      s.2 (GameExamples.collision scheme q) ≤
        ↑(q Commons.AE.Port.enc) ^ 2 / ↑(Fintype.card M)
      because "because the collision game is conditionally equivalent to the ideal system while the MBO remains unset" via {
    have hCond :
        |s.1 (ConstructiveCryptography.DistinctionGames.visible (GameExamples.collision scheme q)) -
            s.1 (Commons.AE.Ideal.perPort M C • Commons.Encryption.system.perPort scheme)| ≤
          s.2 (GameExamples.collision scheme q) := by
      By_conditional_equivalence (GameExamples.collision_conditionallyEquivalent scheme q) using hs
    exact hCond.trans hWin
  }
  By_CC_routine "bounding the probability of provoking a plaintext collision MBO across encryption queries" {
    exact GameExamples.collision_win_le scheme q
      (ConstructiveCryptography.DistinctionGames.solvers_winner hs)
  }

informal_title gameCollision_verbose "AEAD Collision-Hybrid Bound via Conditional Equivalence (Verbose-CC)"
informal_kind gameCollision_verbose "Theorem"

/-- Revealed Extended H-Technique with non-trivial ideal randomness and bad-transcript split,
leaving the ideal reveal law, good-transcript ratio, and bad-mass combinatorics to standard Lean. -/
theorem extendedHCoefficient_verbose (A : Interface) (S : TypedSystem A) :
    Δ S S ≤ ((1 / 2 : ℝ≥0) : ENNReal) := by
  Write P := Probability.Distribution.ProbDist.single ()
  Fact hp : S.1 = SystemAlgebra.RandomSystem.mix P (fun _ => S.1) by
    By_CC_routine "verifying that the trivial one-point mixture reproduces the system" {
      apply SystemAlgebra.RandomSystem.ext
      intro h
      simp only [SystemAlgebra.RandomSystem.mix_mass, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, Finsupp.single_eq_same, one_mul, Finset.sum_const,
        Finset.card_singleton, one_smul, P, Probability.Distribution.ProbDist.single]
    }
  By_extended_H_technique
    mixing_real (fun _ => S.1) over P using hp
    revealing (fun _ _ => false) and (fun _ => Probability.Distribution.uniform Bool)
    with_bad_transcripts (fun τ => τ.2 = true) bound_by (1 / 2)
    with_good_ratio_loss 0
  · exact fun _ => Probability.Distribution.uniform_isProbDist (A := Bool)
  · intro τ hg
    rcases τ with ⟨h, b⟩
    cases b with
    | false =>
        simp only [sub_zero, SystemAlgebra.RandomSystem.kernelMass,
          Probability.Distribution.uniform_apply, Fintype.card_bool, Nat.cast_ofNat, one_div,
          one_mul, SystemAlgebra.RandomSystem.revealMass, Probability.Distribution.ProbDist.single,
          ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same,
          ↓reduceIte, Finset.sum_const, Finset.card_singleton, one_smul, P]
        linarith [S.1.mass_nonneg h]
    | true =>
        exact (hg rfl).elim
  · intro E n _ hE
    rw [SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect]
    have hmass : (Probability.Distribution.uniform Bool).mass (fun b => b = true) = 1 / 2 := by
      rw [Probability.Distribution.mass_singleton]
      norm_num [Probability.Distribution.uniform_apply]
    simp only [hmass, Probability.Distribution.expect_const,
      (S.1.sLaw_isProbDist (hE _ S.2) n).weight_eq, mul_one, le_refl]

informal_title extendedHCoefficient_verbose "Extended H-Technique on Self-Distance (Verbose-CC)"
informal_kind extendedHCoefficient_verbose "Theorem"

/-! ## Flagship 5: Tightness Sandwich (`lower_bound` + `upper_bound`) -/

/-- One-query Boolean bit interface with budget 1. -/
abbrev bitInterface : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Deterministic bit system answering every single-port query with constant bit `c`. -/
def fixedBit (c : Bool) : TypedSystem bitInterface :=
  TypedSystem.ofFunction fun _ _ => c

/-- Randomized bit system drawing `c ← 𝒰(Bool)` and behaving like `fixedBit c`. -/
def sampledBit : TypedSystem bitInterface :=
  TypedSystem.sample (Probability.Distribution.uniform Bool) fixedBit

/-- Single query `()` at port `()`. -/
def bitQuery : DDE (Σ i, bitInterface.X i) (Σ i, bitInterface.Y i) :=
  DDE.ofQueries [⟨(), ()⟩]

/-- Transcript witnessing reply `true`. -/
def trueBitTranscript : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i)) :=
  [(⟨(), ()⟩, ⟨(), true⟩)]

private lemma bitQuery_bounded : QueryBounded 1 bitQuery := by
  intro ys hd
  cases ys with
  | nil => simp
  | cons _ _ =>
      simp only [bitQuery, DDE.ofQueries, SystemAlgebra.fixedQueries, List.length_cons,
        List.getElem?_cons_succ, List.getElem?_nil] at hd
      exact absurd hd (by simp)

private lemma bitQuery_compatible : bitInterface.inputDomain.Compatible bitQuery := by
  intro _ _ h x _ _ hx
  have hh : h.length = 0 := by
    have hb := bitQuery_bounded (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp only [List.length_map] at hb
    omega
  have he : h = [] := List.length_eq_zero_iff.mp hh
  subst h
  simp only [bitInterface, Interface.queryBudget, ne_eq, Interface.inputDomain, Domain.ofInputs,
    List.append_eq_nil_iff, List.map_eq_nil_iff, List.cons_ne_self, and_false, not_false_eq_true,
    List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add,
    add_le_iff_nonpos_left, nonpos_iff_eq_zero, List.length_eq_zero_iff, true_and]

private lemma trueBitTranscript_good : Good bitQuery.1 1 trueBitTranscript := by
  constructor
  · apply (FollowsStrategy.snoc_iff (h := [])).mpr
    refine ⟨FollowsStrategy.nil, ?_⟩
    simp [bitQuery, DDE.ofQueries, SystemAlgebra.fixedQueries]
  · exact Or.inl rfl

/-- Explicit compatible one-query distinguisher checking whether the bit reply equals `true`. -/
def bitObserver : bitInterface.inputDomain.Distinguisher :=
  Distribution.ProbDist.single ⟨envProbe bitQuery (fun t => t.1.zip t.2 = trueBitTranscript),
    envProbe_isDDD bitQuery_bounded,
    Domain.envProbe_decisionCompatible bitQuery_compatible _⟩

/-- Typed behavior of `bitObserver`. -/
def bitObserverBehavior : TypedDistinguisher bitInterface := bitObserver.behavior

informal_symbol bitObserverBehavior "D"

private lemma bitObserver_fixed_prob (b : Bool) :
    bitObserverBehavior.1 (fixedBit b) = if b then 1 else 0 := by
  change bitObserver.probability (fixedBit b).1 = if b then 1 else 0
  simp only [bitObserver, Distribution.ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul]
  rw [RandomSystem.decisionProbability_envProbe bitQuery_bounded _ (fixedBit b).2]
  have zip_proj (h : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i))) :
      (h.map Prod.fst).zip (h.map Prod.snd) = h := (List.zip_of_prod rfl rfl).symm
  simp only [zip_proj]
  rw [Distribution.mass_singleton, RandomSystem.sLaw_apply, ite_eq_left trueBitTranscript_good]
  cases b <;> norm_num [fixedBit, TypedSystem.ofFunction_mass, bitInterface, trueBitTranscript]

private lemma bitObserver_false_prob :
    bitObserverBehavior.1 (fixedBit false) = 0 := by
  simpa using bitObserver_fixed_prob false

private lemma bitObserver_sampled_prob :
    bitObserverBehavior.1 sampledBit = 1 / 2 := by
  change bitObserver.probability sampledBit.1 = 1 / 2
  rw [sampledBit, TypedSystem.sample, Domain.Distinguisher.probability_mix]
  have h0 := bitObserver_fixed_prob false
  have h1 := bitObserver_fixed_prob true
  change bitObserver.probability (fixedBit false).1 = 0 at h0
  change bitObserver.probability (fixedBit true).1 = 1 at h1
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  norm_num [Distribution.uniform_apply, h0, h1]

/-- Exact tightness sandwich `Δ (fixedBit false) sampledBit = 1 / 2`: matching lower bound via an
explicit one-query distinguisher and upper bound via the Extended H-Technique. -/
theorem bitDistinguishingTightness_verbose :
    ((1 / 2 : ℝ≥0) : ENNReal) ≤ Δ (fixedBit false) sampledBit ∧
      Δ (fixedBit false) sampledBit ≤ ((1 / 2 : ℝ≥0) : ENNReal) := by
  Tightness_sandwich
  lower_bound {
    Exhibit_distinguisher bitObserverBehavior
    Lower_bound_advantage_of bitObserverBehavior via bitObserver_false_prob and bitObserver_sampled_prob
  }
  upper_bound {
    Write P₁ := Probability.Distribution.ProbDist.single ()
    Fact hMix : (fixedBit false).1 = SystemAlgebra.RandomSystem.mix P₁ (fun _ => (fixedBit false).1) by
      By_CC_routine "verifying that the trivial one-point mixture reproduces the constant-bit system" {
        apply SystemAlgebra.RandomSystem.ext
        intro h
        simp only [SystemAlgebra.RandomSystem.mix_mass, P₁, Probability.Distribution.ProbDist.single,
          ne_eq, one_ne_zero, not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same,
          one_mul, Finset.sum_const, Finset.card_singleton, one_smul]
      }
    By_extended_H_technique
      mixing_real (fun _ => (fixedBit false).1) over P₁ using hMix
      revealing (fun _ _ => ()) and (fun _ => Finsupp.single () 1)
      with_bad_transcripts (fun τ => τ.1 = trueBitTranscript) bound_by (1 / 2)
      with_good_ratio_loss 0
    · exact fun _ => Probability.Distribution.isProbDist_single ()
    · intro τ hg
      rcases τ with ⟨h, ⟨⟩⟩
      simp only [sub_zero, one_mul, SystemAlgebra.RandomSystem.kernelMass,
        Finsupp.single_eq_same, mul_one, SystemAlgebra.RandomSystem.revealMass,
        Probability.Distribution.ProbDist.single, ne_eq, one_ne_zero, not_false_eq_true,
        Finsupp.support_single, ↓reduceIte, Finset.sum_const, Finset.card_singleton, one_smul, P₁]
      cases h with
      | nil =>
          simp [sampledBit, TypedSystem.sample_mass, fixedBit, TypedSystem.ofFunction_mass,
            bitInterface, Interface.queryBudget, Probability.Distribution.uniform_apply]
          have hc : (Probability.Distribution.uniform Bool).support.card ≤ 2 :=
            (Finset.card_le_univ _).trans_eq Fintype.card_bool
          have hcR : ((Probability.Distribution.uniform Bool).support.card : ℝ) ≤ 2 := by
            exact_mod_cast hc
          linarith
      | cons hd tl =>
          cases tl with
          | nil =>
              rcases hd with ⟨⟨i, x⟩, ⟨j, y⟩⟩
              cases i; cases x; cases j; cases y with
              | false =>
                  simp [sampledBit, TypedSystem.sample_mass, fixedBit,
                    TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget,
                    Probability.Distribution.uniform_apply]
                  norm_num
              | true =>
                  exfalso
                  exact hg rfl
          | cons hd2 tl2 =>
              have hz : ∀ c, (fixedBit c).1 (hd :: hd2 :: tl2) = 0 := fun c => by
                simp [fixedBit, TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget]
              have hs0 : sampledBit.1 (hd :: hd2 :: tl2) = 0 := by
                rw [sampledBit, TypedSystem.sample_mass]
                exact Finset.sum_eq_zero (fun c _ => by simp [hz c])
              simpa [hs0] using (hz false).ge
    · intro E n _ _
      rw [SystemAlgebra.RandomSystem.kernelLaw_mass_eq_expect]
      have hUnitMass (h : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i))) :
          Probability.Distribution.mass (Finsupp.single () (1 : ℝ))
            (fun _ => h = trueBitTranscript) =
            if h = trueBitTranscript then 1 else 0 := by
        simp [Probability.Distribution.mass, Finsupp.sum_single_index]
      simp_rw [hUnitMass]
      have hGoodMass :
          ((sampledBit.1.sLaw (↑E) n).mass (fun h => h = trueBitTranscript)) ≤ 1 / 2 := by
        rw [Probability.Distribution.mass_singleton, SystemAlgebra.RandomSystem.sLaw_apply]
        split_ifs
        · rw [sampledBit, TypedSystem.sample_mass]
          simp [fixedBit, TypedSystem.ofFunction_mass, bitInterface, Interface.queryBudget,
            trueBitTranscript, Probability.Distribution.uniform_apply]
        · norm_num
      have heq :
          (sampledBit.1.sLaw (↑E) n).expect (fun h => if h = trueBitTranscript then (1 : ℝ) else 0) =
            (sampledBit.1.sLaw (↑E) n).mass (fun h => h = trueBitTranscript) := by
        rw [Probability.Distribution.expect, Probability.Distribution.mass]
        simp only [mul_ite, mul_one, mul_zero]
        convert rfl
      linarith
  }

informal_title bitDistinguishingTightness_verbose "One-Query Bit-Distinguishing Tightness Sandwich (Verbose-CC)"
informal_kind bitDistinguishingTightness_verbose "Theorem"

end

/-! ## Axiom Audits (Standard Axioms Only, Zero `sorry`) -/

#print axioms prgLengthExtension_verbose
#print axioms aeadComposition_verbose
#print axioms aeadHybridReduction_verbose
#print axioms indiffSerialComposition_verbose
#print axioms gameCollision_verbose
#print axioms extendedHCoefficient_verbose
#print axioms bitDistinguishingTightness_verbose

/-! ## Export Rendered JSON & HTML + Zero-Leakage Check -/

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let targetDecls : Array Name := #[
    `Tests.Informalization.VerboseCCValidation.prgLengthExtension_verbose,
    `Tests.Informalization.VerboseCCValidation.aeadComposition_verbose,
    `Tests.Informalization.VerboseCCValidation.aeadHybridReduction_verbose,
    `Tests.Informalization.VerboseCCValidation.indiffSerialComposition_verbose,
    `Tests.Informalization.VerboseCCValidation.gameCollision_verbose,
    `Tests.Informalization.VerboseCCValidation.extendedHCoefficient_verbose,
    `Tests.Informalization.VerboseCCValidation.bitDistinguishingTightness_verbose
  ]
  let doc ← liftTermElabM <| Informalization.Render.Json.buildDocument
    "Constructive Cryptography Proofs — Verbose-CC Validation"
    (some "Five flagship theorems authored with Verbose-CC and decompiled from kernel Expr.mdata traces")
    targetDecls
  let texts := Informalization.CLI.collectDocumentTexts doc
  let leaks := Informalization.Core.Hygiene.auditZeroLeakage texts
  unless leaks.isEmpty do
    throwError "Verbose-CC informalization leaked {leaks.size} forbidden string(s): {leaks}"
  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "verbose_cc.json") (Informalization.Render.Json.renderDocumentJson doc)
  IO.FS.writeFile (outDir / "verbose_cc.html") (Informalization.Render.Html.renderDocumentHtml doc)
  IO.println s!"VerboseCCValidation: exported {doc.entries.size} entries, auditZeroLeakage = {leaks.size}"

end Tests.Informalization.VerboseCCValidation

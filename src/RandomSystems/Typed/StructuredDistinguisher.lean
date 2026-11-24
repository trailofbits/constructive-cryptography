module

public import RandomSystems.Distance.SignedObservation
public import RandomSystems.Typed.TranscriptLaw
public import RandomSystems.Typed.Distinguisher
public import RandomSystems.Typed.Functional

/-!
# Structured stopping distinguishers

`StructuredDistinguisher A` is the concrete probabilistic distinguisher
`A.inputDomain.Distinguisher` on interface `A`, without erasing the underlying distribution over
compatible stopping DDDs behind `TypedDistinguisher A`. Keeping the concrete carrier preserves
`transcriptLaw`, `ProbDist.bind` mixing, and nonadaptivity predicates (`IsNonAdaptive`), while
`toTyped` projects onto the behavioral quotient `TypedDistinguisher A` compatibly with converter
absorption.

Signed decision gaps and `ProbDist.bind` averaging are reused directly from
`RandomSystems.Distance.SignedObservation`.

## Main definitions

* `StructuredDistinguisher A`: concrete compatible stopping distinguishers on `A`
* `StructuredDistinguisher.probability`, `signedGap`, `advantage`: evaluation and gaps on
  `TypedSystem A`
* `StructuredDistinguisher.toTyped`: behavioral projection to `TypedDistinguisher A`
* `StructuredDistinguisher.absorb`: concrete converter absorption compatible with
  `TypedDistinguisher.absorb`
* `StructuredDistinguisher.uniformChoice`: sample `i ←$ Fin L` once before interacting
* `StructuredDistinguisher.IsNonAdaptive`: every supported strategy asks a fixed query sequence
* `StructuredDistinguisher.fixedQuery`, `sampleFixedQuery`: nonadaptive test constructors

## Main results

* `StructuredDistinguisher.toTyped_absorb`: `(D.absorb α).toTyped = D.toTyped.absorb α`
* `StructuredDistinguisher.probability_bind`, `signedGap_bind`, `transcriptLaw_bind`:
  linearity of decision probabilities, signed gaps, and transcripts under `ProbDist.bind`
* `StructuredDistinguisher.signedGap_telescoping_uniformChoice`,
  `advantage_telescoping_uniformChoice`, `advantage_telescoping_uniformChoice_le`:
  uniform-index telescoping hybrid theorems for concrete distinguishers
* `StructuredDistinguisher.IsNonAdaptive.bind`, `IsNonAdaptive.uniformChoice`:
  preservation of nonadaptivity under finite mixtures

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. TCC 2020.
   Cryptology ePrint Archive, Paper 2020/1187.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

set_option autoImplicit false

namespace SystemAlgebra

open Probability
open scoped BigOperators NNReal

/-- Compatible stopping distinguishers on interface `A` [1, Definition 9], retaining
`transcriptLaw`, `ProbDist.bind`, and `IsNonAdaptive`. -/
abbrev StructuredDistinguisher (A : Interface) := A.inputDomain.Distinguisher

namespace StructuredDistinguisher

/-! ### Evaluation, signed gap, advantage, and behavioral projection -/

/-- Output-1 probability `Pr[D(R) = 1]` of a concrete distinguisher `D` on `R : TypedSystem A`. -/
noncomputable def probability {A : Interface} (D : StructuredDistinguisher A)
    (R : TypedSystem A) : ℝ :=
  Domain.Distinguisher.probability D R.1

/-- Signed distinguishing gap `Pr[D(R) = 1] - Pr[D(S) = 1]` [2, Definition 4.7, p. 91]. -/
noncomputable def signedGap {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) : ℝ :=
  Domain.Distinguisher.signedGap D R.1 S.1

/-- Absolute distinguishing advantage `|Pr[D(R) = 1] - Pr[D(S) = 1]|` in `ENNReal`. -/
noncomputable def advantage {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) : ENNReal :=
  Domain.Distinguisher.advantage D R.1 S.1

/-- Advantage is the extended nonnegative real magnitude of the signed gap. -/
lemma advantage_eq_ofReal_abs_signedGap {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) :
    D.advantage R S = ENNReal.ofReal |D.signedGap R S| :=
  rfl

/-- Zero advantage on identical typed systems. -/
@[simp]
lemma advantage_self {A : Interface} (D : StructuredDistinguisher A) (R : TypedSystem A) :
    D.advantage R R = 0 :=
  Domain.Distinguisher.advantage_self D R.1

/-- Symmetry of advantage on typed systems. -/
lemma advantage_symm {A : Interface} (D : StructuredDistinguisher A) (R S : TypedSystem A) :
    D.advantage R S = D.advantage S R :=
  Domain.Distinguisher.advantage_symm D R.1 S.1

/-- Triangle inequality for advantage on typed systems. -/
lemma advantage_triangle {A : Interface} (D : StructuredDistinguisher A)
    (R S T : TypedSystem A) :
    D.advantage R T ≤ D.advantage R S + D.advantage S T :=
  Domain.Distinguisher.advantage_triangle D R.1 S.1 T.1

/-- Every concrete distinguisher's advantage is bounded by the transcript distance. -/
lemma advantage_le_transcriptDistance {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) :
    D.advantage R S ≤ R.1.transcriptDistance S.1 :=
  Domain.Distinguisher.advantage_le_transcriptDistance D R.2 S.2

/-- Project a concrete distinguisher onto its behavior `TypedDistinguisher A`. -/
noncomputable def toTyped {A : Interface} (D : StructuredDistinguisher A) :
    TypedDistinguisher A :=
  Domain.Distinguisher.behavior D

/-- The behavioral projection preserves output-1 probability on every typed system. -/
@[simp]
lemma toTyped_probability {A : Interface} (D : StructuredDistinguisher A)
    (R : TypedSystem A) :
    D.toTyped.1 R = D.probability R :=
  rfl

/-- The behavioral projection preserves advantage on every pair of typed systems. -/
@[simp]
lemma toTyped_advantage {A : Interface} (D : StructuredDistinguisher A)
    (R S : TypedSystem A) :
    D.toTyped.advantage R S = D.advantage R S :=
  rfl

/-! ### Concrete converter absorption -/

/-- Absorb converter `α : TypedConverter A B` into `D`, preserving output-1 probabilities
`(D.absorb α).probability R = D.probability (α • R)`. -/
noncomputable def absorb {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) : StructuredDistinguisher B :=
  (Domain.Distinguisher.exists_absorbAll B.nonempty_prefix A.nonempty_prefix α D).choose

/-- Absorbing `α` preserves output-1 probability:
`(D.absorb α).probability R = D.probability (α • R)`. -/
lemma probability_absorb {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) (R : TypedSystem B) :
    (D.absorb α).probability R = D.probability (α • R) :=
  (Domain.Distinguisher.exists_absorbAll B.nonempty_prefix A.nonempty_prefix α D).choose_spec
    R.1 R.2

/-- Absorbing `α` preserves the signed distinguishing gap. -/
lemma signedGap_absorb {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) (R S : TypedSystem B) :
    (D.absorb α).signedGap R S = D.signedGap (α • R) (α • S) := by
  simp only [signedGap, Domain.Distinguisher.signedGap]
  exact congrArg₂ (· - ·) (probability_absorb D α R) (probability_absorb D α S)

/-- Absorbing `α` preserves absolute distinguishing advantage. -/
lemma advantage_absorb {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) (R S : TypedSystem B) :
    (D.absorb α).advantage R S = D.advantage (α • R) (α • S) := by
  simp only [advantage_eq_ofReal_abs_signedGap, signedGap_absorb]

/-- Concrete absorption agrees with `TypedDistinguisher.absorb` under behavioral projection. -/
lemma toTyped_absorb {A B : Interface} (D : StructuredDistinguisher A)
    (α : TypedConverter A B) :
    (D.absorb α).toTyped = D.toTyped.absorb α := by
  apply Subtype.ext
  funext R
  exact probability_absorb D α R

/-! ### Finite mixtures, signed-gap averaging, and uniform-index selection -/

/-- Sampling an index `k ∼ μ` once and running `family k` averages output-1 probabilities. -/
lemma probability_bind {A : Interface} {K : Type*} (μ : Distribution.ProbDist K)
    (family : K → StructuredDistinguisher A) (R : TypedSystem A) :
    probability (μ.bind family) R = μ.1.expect (fun k => (family k).probability R) :=
  Domain.Distinguisher.probability_bind μ family R.1

/-- Sampling an index `k ∼ μ` once averages signed distinguishing gaps. -/
lemma signedGap_bind {A : Interface} {K : Type*} (μ : Distribution.ProbDist K)
    (family : K → StructuredDistinguisher A) (R S : TypedSystem A) :
    signedGap (μ.bind family) R S = μ.1.expect (fun k => (family k).signedGap R S) :=
  Domain.Distinguisher.signedGap_bind μ family R.1 S.1

/-- The transcript law of a mixed distinguisher is the mixture of the component transcript laws. -/
lemma transcriptLaw_bind {A : Interface} {K : Type} (μ : Distribution.ProbDist K)
    (family : K → StructuredDistinguisher A) (R : TypedSystem A) :
    Domain.Distinguisher.transcriptLaw (μ.bind family) R =
      μ.bind (fun k => Domain.Distinguisher.transcriptLaw (family k) R) := by
  apply Subtype.ext
  change Distribution.bindK (Distribution.bindK μ.1 (fun k => (family k).1)) _ =
    Distribution.bindK μ.1 (fun k => Distribution.bindK (family k).1 _)
  exact Distribution.bindK_bindK μ.1 (fun k => (family k).1) _

/-- Sample an index `i ←$ Fin L` uniformly once before interacting, then run `family i`. -/
noncomputable def uniformChoice {A : Interface} {L : ℕ} (hL : 0 < L)
    (family : Fin L → StructuredDistinguisher A) : StructuredDistinguisher A :=
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  𝒰[Fin L].bind family

/-- Output-1 probability of `uniformChoice hL family` is the uniform average over `Fin L`. -/
lemma probability_uniformChoice {A : Interface} {L : ℕ} (hL : 0 < L)
    (family : Fin L → StructuredDistinguisher A) (R : TypedSystem A) :
    (uniformChoice hL family).probability R =
      (1 / (L : ℝ)) * ∑ i : Fin L, (family i).probability R := by
  classical
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [uniformChoice, probability_bind, Distribution.expect_eq_sum]
  simp only [Distribution.ProbDist.uniform, Distribution.uniform_apply, Fintype.card_fin,
    ← Finset.mul_sum]

/-- Signed gap of `uniformChoice hL family` is the uniform average of component signed gaps. -/
lemma signedGap_uniformChoice {A : Interface} {L : ℕ} (hL : 0 < L)
    (family : Fin L → StructuredDistinguisher A) (R S : TypedSystem A) :
    (uniformChoice hL family).signedGap R S =
      (1 / (L : ℝ)) * ∑ i : Fin L, (family i).signedGap R S := by
  classical
  let : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  rw [uniformChoice, signedGap_bind, Distribution.expect_eq_sum]
  simp only [Distribution.ProbDist.uniform, Distribution.uniform_apply, Fintype.card_fin,
    ← Finset.mul_sum]

/-- Scaled uniform-index telescoping signed-gap identity: sampling `i ←$ Fin L` once yields
`Pr[D(H 0)] - Pr[D(H L)] = L * scale * (Pr[B(X₀)] - Pr[B(X₁)])`. -/
theorem signedGap_telescoping_uniformChoice_scaled {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : Fin (L + 1) → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B) (scale : ℝ)
    (hstep : ∀ i : Fin L,
      D.signedGap (H i.castSucc) (H i.succ) = scale * (family i).signedGap X₀ X₁) :
    D.signedGap (H 0) (H (Fin.last L)) =
      (L : ℝ) * scale * (uniformChoice hL family).signedGap X₀ X₁ := by
  let acc : ℕ → ℝ := fun k =>
    if hk : k < L + 1 then D.probability (H ⟨k, hk⟩) else 0
  have htel : ∑ i : Fin L, D.signedGap (H i.castSucc) (H i.succ) =
      D.signedGap (H 0) (H (Fin.last L)) := by
    have hterm (i : Fin L) :
        D.signedGap (H i.castSucc) (H i.succ) = acc i.val - acc (i.val + 1) := by
      have hi1 : i.val < L + 1 := Nat.lt_succ_of_lt i.isLt
      have hi2 : i.val + 1 < L + 1 := Nat.succ_lt_succ i.isLt
      simp only [signedGap, Domain.Distinguisher.signedGap, probability, acc, hi1, hi2, ↓reduceDIte]
      rfl
    have hsum : ∑ i : Fin L, (acc i.val - acc (i.val + 1)) = acc 0 - acc L :=
      (Fin.sum_univ_eq_sum_range (fun k => acc k - acc (k + 1)) L).trans
        (Finset.sum_range_sub' acc L)
    rw [Finset.sum_congr rfl (fun i _ => hterm i), hsum]
    have h0 : 0 < L + 1 := Nat.zero_lt_succ L
    have hL' : L < L + 1 := Nat.lt_succ_self L
    simp only [signedGap, Domain.Distinguisher.signedGap, probability, acc, h0, hL', ↓reduceDIte]
    rfl
  rw [← htel, signedGap_uniformChoice]
  have hne : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hcancel : (L : ℝ) * scale * (1 / (L : ℝ)) = scale := by field_simp
  rw [← mul_assoc, hcancel, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => hstep i)

/-- Uniform-index telescoping signed-gap identity: sampling `i ←$ Fin L` once for the whole
interaction yields `Pr[D(H 0)] - Pr[D(H L)] = L * (Pr[B(X₀)] - Pr[B(X₁)])`. -/
theorem signedGap_telescoping_uniformChoice {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : Fin (L + 1) → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B)
    (hstep : ∀ i : Fin L, D.signedGap (H i.castSucc) (H i.succ) = (family i).signedGap X₀ X₁) :
    D.signedGap (H 0) (H (Fin.last L)) =
      (L : ℝ) * (uniformChoice hL family).signedGap X₀ X₁ := by
  have h := signedGap_telescoping_uniformChoice_scaled hL D H family X₀ X₁ 1
    (fun i => by simpa only [one_mul] using hstep i)
  simpa only [mul_one] using h

/-- `Nat`-indexed uniform-index telescoping signed-gap identity for `H : ℕ → TypedSystem A`. -/
theorem signedGap_telescoping_uniformChoice_nat {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : ℕ → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B) (scale : ℝ)
    (hstep : ∀ i : Fin L,
      D.signedGap (H i.val) (H (i.val + 1)) = scale * (family i).signedGap X₀ X₁) :
    D.signedGap (H 0) (H L) =
      (L : ℝ) * scale * (uniformChoice hL family).signedGap X₀ X₁ :=
  signedGap_telescoping_uniformChoice_scaled hL D (fun i : Fin (L + 1) => H i.val)
    family X₀ X₁ scale hstep

/-- Exact advantage identity for the scaled uniform-index telescoping hybrid. -/
theorem advantage_telescoping_uniformChoice_scaled {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : Fin (L + 1) → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B)
    {scale : ℝ} (hscale : 0 ≤ scale)
    (hstep : ∀ i : Fin L,
      D.signedGap (H i.castSucc) (H i.succ) = scale * (family i).signedGap X₀ X₁) :
    D.advantage (H 0) (H (Fin.last L)) =
      (L : ENNReal) * ENNReal.ofReal scale * (uniformChoice hL family).advantage X₀ X₁ := by
  rw [advantage_eq_ofReal_abs_signedGap, advantage_eq_ofReal_abs_signedGap,
    signedGap_telescoping_uniformChoice_scaled hL D H family X₀ X₁ scale hstep,
    abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg L), abs_of_nonneg hscale,
    ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg L) hscale),
    ENNReal.ofReal_mul (Nat.cast_nonneg L), ENNReal.ofReal_natCast]

/-- Exact advantage identity for the uniform-index telescoping hybrid:
`advantage D (H 0) (H L) = L * advantage (uniformChoice hL family) X₀ X₁`. -/
theorem advantage_telescoping_uniformChoice {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : Fin (L + 1) → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B)
    (hstep : ∀ i : Fin L, D.signedGap (H i.castSucc) (H i.succ) = (family i).signedGap X₀ X₁) :
    D.advantage (H 0) (H (Fin.last L)) =
      (L : ENNReal) * (uniformChoice hL family).advantage X₀ X₁ := by
  have h := advantage_telescoping_uniformChoice_scaled hL D H family X₀ X₁ zero_le_one
    (fun i => by simpa only [one_mul] using hstep i)
  simpa only [ENNReal.ofReal_one, mul_one] using h

/-- Advantage upper bound for the uniform-index telescoping hybrid. -/
theorem advantage_telescoping_uniformChoice_le {A B : Interface} {L : ℕ} (hL : 0 < L)
    (D : StructuredDistinguisher A) (H : Fin (L + 1) → TypedSystem A)
    (family : Fin L → StructuredDistinguisher B) (X₀ X₁ : TypedSystem B)
    (hstep : ∀ i : Fin L, D.signedGap (H i.castSucc) (H i.succ) = (family i).signedGap X₀ X₁) :
    D.advantage (H 0) (H (Fin.last L)) ≤
      (L : ENNReal) * (uniformChoice hL family).advantage X₀ X₁ :=
  (advantage_telescoping_uniformChoice hL D H family X₀ X₁ hstep).le

/-! ### Nonadaptivity predicates and fixed-query distinguishers -/

/-- A concrete distinguisher is nonadaptive when every supported deterministic strategy asks a
fixed query list independent of earlier system replies. -/
def IsNonAdaptive {A : Interface} (D : StructuredDistinguisher A) : Prop :=
  ∀ choice ∈ D.1.support, ∃ inputs : List (Σ i, A.X i), envOf choice.1 = fixedQueries inputs

/-- Mixtures of nonadaptive distinguishers remain nonadaptive. -/
lemma IsNonAdaptive.bind {A : Interface} {K : Type} (μ : Distribution.ProbDist K)
    (family : K → StructuredDistinguisher A) (hfamily : ∀ k, IsNonAdaptive (family k)) :
    IsNonAdaptive (μ.bind family) := by
  intro choice hchoice
  obtain ⟨k, _, hk⟩ := Distribution.mem_support_bindK hchoice
  exact hfamily k choice hk

/-- Uniform-index sampling preserves nonadaptivity. -/
lemma IsNonAdaptive.uniformChoice {A : Interface} {L : ℕ} (hL : 0 < L)
    (family : Fin L → StructuredDistinguisher A) (hfamily : ∀ i, IsNonAdaptive (family i)) :
    IsNonAdaptive (uniformChoice hL family) :=
  IsNonAdaptive.bind _ family hfamily

/-- A prescribed query list asks nothing after its last entry. -/
lemma ofQueries_queryBounded {X Y : Type} (xs : List X) :
    QueryBounded xs.length (DDE.ofQueries (Y := Y) xs) := by
  intro ys defined
  by_contra tooLong
  have absent : xs[ys.length]? = none := List.getElem?_eq_none (Nat.le_of_not_gt tooLong)
  simp only [DDE.ofQueries, fixedQueries, absent] at defined
  exact defined.elim

/-- An admitted query list is domain-compatible independently of replies and the system. -/
lemma ofQueries_compatible (A : Interface) (xs : List (Σ i, A.X i))
    (hd : xs = [] ∨ A.domain xs) : A.inputDomain.Compatible (DDE.ofQueries xs) := by
  intro R _ t x hc _ hx
  obtain ⟨_, hf⟩ := FollowsStrategy.fixedQueries hc
  have hq : xs[t.length]? = some x := by
    simpa only [DDE.ofQueries, fixedQueries, List.length_map,
      Part.mem_ofOption, Option.mem_def] using hx
  have hlt : t.length < xs.length := by
    by_contra hn
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hq
    cases hq
  change A.domain (t.map Prod.fst ++ [x])
  rw [hf]
  have ht : xs.take t.length ++ [x] = xs.take (t.length + 1) := by
    rw [List.take_add_one, hq]
    rfl
  rw [ht]
  rcases hd with rfl | hd
  · simp only [List.length_nil] at hlt
    omega
  · exact A.nonempty_prefix.2 (List.take_prefix _ _)
      (List.ne_nil_of_length_pos (by rw [List.length_take]; omega)) hd

/-- On a single-label interface, a fixed-query probe retains its fixed query list on every reply
history, including histories beyond its stopping point. -/
lemma envOf_envProbe_ofQueries {I : Type} [Subsingleton I] {X Y : I → Type}
    (xs : List (Σ i, X i)) (test : List (Σ i, X i) × List (Σ i, Y i) → Prop) :
    envOf (envProbe (DDE.ofQueries xs) test) = fixedQueries xs := by
  classical
  funext ys
  have hfit (hlen : ys.length ≤ xs.length) : EFits (fixedQueries xs) ys := by
    intro k hk
    have hkx : k < xs.length := hk.trans_le hlen
    refine ⟨xs[k], ?_, Subsingleton.elim _ _⟩
    simp only [fixedQueries, List.length_take, Nat.min_eq_left hk.le,
      List.getElem?_eq_getElem hkx, Part.mem_coe, Option.mem_def]
  by_cases hf : EFits (fixedQueries xs) ys
  · exact envOf_envProbe hf
  · have hn : ¬ ∃ zs, ys.map envIn = zs.map envIn ∧ EFits (fixedQueries xs) zs := by
      rintro ⟨zs, he, hzs⟩
      have he' := List.map_injective_iff.mpr envIn_injective he
      exact hf (he' ▸ hzs)
    have hlen : xs.length ≤ ys.length := (Nat.lt_of_not_ge (fun h => hf (hfit h))).le
    have hprobe : envProbe (DDE.ofQueries xs) test (dHist ys) = Part.none := by
      change dite (∃ zs, ys.map envIn = zs.map envIn ∧ EFits (fixedQueries xs) zs) _ _ = _
      exact dite_eq_right hn
    rw [envOf, hprobe]
    simp only [Part.bind_none, fixedQueries, List.getElem?_eq_none hlen, Part.coe_none]

/-- A deterministic fixed-query decision packaged as a `StructuredDistinguisher A`. -/
noncomputable def fixedQuery (A : Interface) (xs : List (Σ i, A.X i))
    (hd : xs = [] ∨ A.domain xs) (test : List (Σ i, A.Y i) → Bool) :
    StructuredDistinguisher A :=
  ⟨Finsupp.single ⟨envProbe (DDE.ofQueries xs) (fun t => test t.2 = true),
    envProbe_isDDD (ofQueries_queryBounded xs),
    Domain.envProbe_decisionCompatible (ofQueries_compatible A xs hd) _⟩ 1,
    Distribution.isProbDist_single _⟩

/-- Sample a fixed query schedule and decision rule from `μ` before any oracle interaction. -/
noncomputable def sampleFixedQuery (A : Interface) {K : Type} (μ : Distribution.ProbDist K)
    (xs : K → List (Σ i, A.X i)) (hd : ∀ k, xs k = [] ∨ A.domain (xs k))
    (test : K → List (Σ i, A.Y i) → Bool) : StructuredDistinguisher A :=
  Distribution.ProbDist.map (fun k =>
    ⟨envProbe (DDE.ofQueries (xs k)) (fun t => test k t.2 = true),
      envProbe_isDDD (ofQueries_queryBounded (xs k)),
      Domain.envProbe_decisionCompatible (ofQueries_compatible A (xs k) (hd k)) _⟩) μ

/-- Output-1 probability of `sampleFixedQuery` averages the component fixed-query tests. -/
lemma sampleFixedQuery_probability (A : Interface) {K : Type} (μ : Distribution.ProbDist K)
    (xs : K → List (Σ i, A.X i)) (hd : ∀ k, xs k = [] ∨ A.domain (xs k))
    (test : K → List (Σ i, A.Y i) → Bool) (R : TypedSystem A) :
    (sampleFixedQuery A μ xs hd test).probability R =
      μ.1.expect (fun k => (fixedQuery A (xs k) (hd k) (test k)).probability R) := by
  rw [sampleFixedQuery, probability, Domain.Distinguisher.probability,
    Distribution.ProbDist.map_val, Distribution.sum_fTransform_mul]
  simp only [fixedQuery, probability, Domain.Distinguisher.probability, Finsupp.sum_single_index,
    zero_mul, one_mul, Distribution.expect]

/-- On a single-label interface, `fixedQuery` is nonadaptive. -/
lemma fixedQuery_isNonAdaptive (A : Interface) [Subsingleton A.I] (xs : List (Σ i, A.X i))
    (hd : xs = [] ∨ A.domain xs) (test : List (Σ i, A.Y i) → Bool) :
    IsNonAdaptive (fixedQuery A xs hd test) := by
  intro choice hchoice
  have hEq : choice = ⟨envProbe (DDE.ofQueries xs) (fun t => test t.2 = true),
      envProbe_isDDD (ofQueries_queryBounded xs),
      Domain.envProbe_decisionCompatible (ofQueries_compatible A xs hd) _⟩ :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hchoice)
  rw [hEq]
  exact ⟨xs, envOf_envProbe_ofQueries xs _⟩

/-- On a single-label interface, `sampleFixedQuery` is nonadaptive. -/
lemma sampleFixedQuery_isNonAdaptive (A : Interface) [Subsingleton A.I] {K : Type}
    (μ : Distribution.ProbDist K) (xs : K → List (Σ i, A.X i))
    (hd : ∀ k, xs k = [] ∨ A.domain (xs k)) (test : K → List (Σ i, A.Y i) → Bool) :
    IsNonAdaptive (sampleFixedQuery A μ xs hd test) := by
  intro choice hchoice
  obtain ⟨k, _, hk⟩ := Distribution.mem_support_fTransform _ _ hchoice
  rw [← hk]
  exact ⟨xs k, envOf_envProbe_ofQueries (xs k) _⟩

end StructuredDistinguisher

end SystemAlgebra

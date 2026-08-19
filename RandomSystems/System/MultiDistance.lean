/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ClassDistance
import Probability.MultiCoupling

/-!
# The multi-system distance: Lanzenberger Definition 2.27 and Theorem 2.29

The system-level reading of `Probability/MultiCoupling.lean`, which carries the
whole combinatorial content on plain distributions.  Here the tuple of laws is
a tuple of **equivalence classes** of PDS, and the two thesis statements are

* **Definition 2.27** — `Δ(𝒮) := 1 − sup_{representatives} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`
  (`multiSystemDistance`), and
* **Theorem 2.29** — `Δ(Sᵢ,Sⱼ) ≤ Δ(𝒮) ≤ (min(n,ℓ) − 1) · max_{i≠j} δ(Sᵢ,Sⱼ)`
  (`classDistance_le_ofReal_multiSystemDistance` composed with
  `multiSystemDistance_pair_le`, and `exists_pair_multiSystemDistance_le`).

Read visually at printed pp. 18–19 of D. Lanzenberger, *A Theory of Random
Systems, Games, and Hardness Amplification*, DISS ETH No. 29554.

## Two source errata, both kernel-checked

**(a) Definition 2.27/2.28's quantifier over representatives.**  Definition
2.27 prints
`Δ(𝒮) := 1 − inf_{(S₁,…,Sₙ) ∈ 𝐒₁×⋯×𝐒ₙ} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`
and Definition 2.28 prints
`Δ(S,T) := inf_{S∈𝐒,T∈𝐓} δ(S,T) = 1 − inf_{(S,T)∈𝐒×𝐓} sup_ℰ Pr^ℰ(S = T)`.
The `inf` over representatives must be a `sup`: by the coupling lemma
`sup_ℰ Pr^ℰ(S = T) = |S| − δ(S,T)` at each representative pair
(`Probability.supAgreement_pair_eq_weight_sub_statDist`), so the printed second
display of Definition 2.28 computes `sup` of `δ` over representatives, not the
asserted first display's `inf`.  The thesis's own remark below Definition 2.28
— `V₀ ≡ V_{1/2}` at `δ = 1`, "taking the infimum seems to be necessary" —
separates the two.  `multiSystemDistance` is Definition 2.27 with the
corrected `sup`; the verbatim printed display is kept, and used by nothing, as
`printedMultiSystemDistance`, so that the erratum can be *refuted* rather than
argued (`RandomSystems/System/Example216.lean`).

**(b) Theorem 2.29's `min` over pairs in the upper bound** should be a `max`;
the refutation is `Probability.printed_min_form_counterexample` and the
corrected statement is `exists_pair_multiSystemDistance_le`.

## Definition 2.28's identity at a pair, under Ruling R9

The thesis's `Δ(S,T)` is an infimum over *probability* representatives, and
since **Ruling R9** so is `PDS.classDistance`: its infimum ranges over honest
(`Distribution.NonNeg`) representatives, which at a class of weight one are
exactly the probability ones, weight being an invariant of the class.  So the
identity Definition 2.28 asserts between its two displays is a theorem here:

* `multiSystemDistance_le_statDist_of_equivalent` and
  `le_multiSystemDistance` — the two eliminators exhibiting
  `multiSystemDistance` at a pair *as* the infimum over non-negative
  probability representatives, which is Definition 2.28's first display as the
  thesis means it;
* `classDistance_eq_ofReal_multiSystemDistance` — the two displays are one
  number, and
* `classDistance_le_ofReal_multiSystemDistance` — the half of it that Theorem
  2.29's lower bound consumes, kept separate because that is all it needs.

This supersedes the file's earlier delta note.  While `PDS.classDistance` was
an infimum over *all* representatives, signed ones included, only the `≤`
comparison was available and the reverse was an open definitional question;
R9 closed it by fixing the definition's carrier, not by comparing two infima.
Signed representatives remain a proof-technique tool — couplings and bounds —
and `Probability.supAgreement_eq_zero_of_not_nonNeg` is why they were inert on
this side all along: a signed tuple admits no joint at all.

## Provenance

Statement shapes and proof architecture transplanted from the read-only quarry
`RandomSystems/LanzenbergerChain.lean`: `multiSystemDistance` `:350`,
`printedMultiSystemDistance` `:366`, `bddAbove_supAgreement_set` `:388`,
`multiSystemDistance_pair_le` `:415`, the Definition 2.28 identity `:478`,
Theorem 2.29's lower bound `:567`/`:577` and corrected upper bound `:608`.
The quarry rides `PFunPDS X Y` with its own `δ` and `Δ`; every statement here
is restated on `PDS X Y = Distribution (System.DDS X Y)`, `Probability.statDist`
and `PDS.classDistance`.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)
open Probability

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-! ## Definition 2.27, errata-corrected -/

/-- Lanzenberger **Definition 2.27** with erratum (a) corrected: the
multi-system distance of a finite family of random systems,

  `Δ(𝒮) = 1 − sup_{representatives} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`.

The outer supremum ranges over tuples of representatives of the classes, the
inner one (`Probability.supAgreement`) over joint distributions of that tuple.
The thesis prints `inf` for the outer quantifier, which contradicts Definition
2.28's own first display; see the file header and
`RandomSystems/System/Example216.lean` for the kernel-checked refutation.

As with `classDistance` and `advFullyDefined`, the thesis's standing
same-domain and probability assumptions are left to the theorems that need
them rather than baked into the definition.

COINAGE (quarry-continuation of `LanzenbergerChain.lean:350`); the thesis
names the object only by the display `Δ(𝒮)`. -/
def multiSystemDistance {n : ℕ} (S : Fin n → PDS X Y) : ℝ :=
  1 - sSup {a : ℝ | ∃ laws : Fin n → PDS X Y,
    (∀ i, equivalent (S i) (laws i)) ∧ a = supAgreement laws}

/-- Lanzenberger Definition 2.28's **second printed display**, rendered
verbatim: `1 − inf_{representatives} sup_ℰ Pr^ℰ(S₁ = ⋯ = Sₙ)`, i.e.
`multiSystemDistance` with the printed `inf` kept instead of corrected to a
`sup`.

This declaration exists so that erratum (a) is a *theorem* rather than an
argument: Definition 2.28 asserts that this quantity equals its first display
`inf_{S∈𝐒,T∈𝐓} δ(S,T)`, and `RandomSystems/System/Example216.lean` exhibits a
concrete class pair at which the two take the values `1` and `0`.  **Nothing
else in the tree may depend on it.**

COINAGE (quarry-continuation of `LanzenbergerChain.lean:366`). -/
def printedMultiSystemDistance {n : ℕ} (S : Fin n → PDS X Y) : ℝ :=
  1 - sInf {a : ℝ | ∃ laws : Fin n → PDS X Y,
    (∀ i, equivalent (S i) (laws i)) ∧ a = supAgreement laws}

/-- Definition 2.27's outer supremum set, named once so the three `sSup`
lemmas below read as statements about one object. -/
def agreementValues {n : ℕ} (S : Fin n → PDS X Y) : Set ℝ :=
  {a : ℝ | ∃ laws : Fin n → PDS X Y,
    (∀ i, equivalent (S i) (laws i)) ∧ a = supAgreement laws}

theorem multiSystemDistance_eq {n : ℕ} (S : Fin n → PDS X Y) :
    multiSystemDistance S = 1 - sSup (agreementValues S) := rfl

/-- The systems themselves are a representative tuple, so Definition 2.27's
outer set is never empty. -/
theorem agreementValues_nonempty {n : ℕ} (S : Fin n → PDS X Y) :
    (agreementValues S).Nonempty :=
  ⟨supAgreement S, S, fun _ => equivalent_refl _, rfl⟩

/-- Definition 2.27's outer supremum set is bounded above by the weight of any
one class — all representatives of one class share its weight — so the real
`sSup` is well behaved.

`hw` is the signed carrier's cost, at its weakest layer.  It is deliberately
*not* `(S 0).NonNeg`: the representatives are only known to be `equivalent` to
`S`, and equivalence transports weight but not non-negativity, so a pointwise
hypothesis on `S` would buy nothing.  What saves the bound is that a *joint*
is non-negative by `IsJointOf`, so every agreement mass is below the joint's
weight, hence below `(laws 0).weight = (S 0).weight`.  When no joint exists at
all the inner supremum is the empty `sSup = 0`, and `hw` is exactly what
bounds that. -/
theorem bddAbove_agreementValues {n : ℕ} [NeZero n] (S : Fin n → PDS X Y)
    (hw : 0 ≤ (S 0).weight) : BddAbove (agreementValues S) := by
  refine ⟨(S 0).weight, ?_⟩
  rintro a ⟨laws, hlaws, rfl⟩
  refine Real.sSup_le ?_ hw
  rintro b ⟨joint, hjoint, rfl⟩
  exact (Distribution.mass_le_weight hjoint.nonNeg _).trans_eq
    ((weight_eq_of_isJointOf hjoint 0).trans
      (weight_eq_of_equivalent (hlaws 0)).symm)

/-- Definition 2.27's outer supremum is below `1` at a family of probability
classes: a non-negative representative tuple's agreement mass is below its
common weight, and a signed tuple admits no joint at all and contributes `0`
(`Probability.supAgreement_eq_zero_of_not_nonNeg`). -/
theorem sSup_agreementValues_le_one {n : ℕ} [NeZero n] (S : Fin n → PDS X Y)
    (hw : (S 0).weight = 1) : sSup (agreementValues S) ≤ 1 := by
  classical
  refine Real.sSup_le ?_ zero_le_one
  rintro a ⟨laws, hlaws, rfl⟩
  have hw0 : (laws 0).weight = 1 := by
    rw [← weight_eq_of_equivalent (hlaws 0), hw]
  by_cases hnn : ∀ k, (laws k).NonNeg
  · exact (supAgreement_le_weight laws 0 (hnn 0)).trans hw0.le
  · rw [supAgreement_eq_zero_of_not_nonNeg hnn]
    exact zero_le_one

/-- The multi-system distance of a family of probability classes is
non-negative — Definition 2.27's `1 −` never overshoots. -/
theorem multiSystemDistance_nonneg {n : ℕ} [NeZero n] (S : Fin n → PDS X Y)
    (hw : (S 0).weight = 1) : 0 ≤ multiSystemDistance S := by
  have := sSup_agreementValues_le_one S hw
  rw [multiSystemDistance_eq]
  linarith

/-! ## Definition 2.28 at a pair -/

/-- **Definition 2.28's `inf`-eliminator**: every pair of *probability*
representatives bounds the multi-system distance from above.  This is one half
of "at a pair, Definition 2.27 is Definition 2.28's first display".

The `isProbDist` hypotheses are the thesis's own ("`𝐒`, `𝐓` are classes of
PDS") and on the signed carrier they are needed at both conjuncts: `NonNeg`
because the coupling bridge is false for signed laws, and `weight = 1` because
Definition 2.27's `1 −` normalizes the agreement mass. -/
theorem multiSystemDistance_le_statDist_of_equivalent
    {P : Fin 2 → PDS X Y}
    {S' T' : PDS X Y} (hS' : equivalent (P 0) S') (hT' : equivalent (P 1) T')
    (hS'p : S'.isProbDist) (hT'p : T'.isProbDist) :
    multiSystemDistance P ≤ statDist S' T' := by
  classical
  have hw : 0 ≤ (P 0).weight := by
    rw [weight_eq_of_equivalent hS', hS'p.2]; exact zero_le_one
  set laws : Fin 2 → PDS X Y := fun k => if k = 0 then S' else T' with hlaws
  have hlaws0 : laws 0 = S' := rfl
  have hlaws1 : laws 1 = T' := rfl
  have hnn : ∀ k, (laws k).NonNeg := by
    intro k
    fin_cases k
    · exact hS'p.1
    · exact hT'p.1
  have hsup : supAgreement laws = 1 - statDist S' T' := by
    rw [supAgreement_pair_eq_weight_sub_statDist laws hnn
      (by rw [hlaws0, hlaws1, hS'p.2, hT'p.2]), hlaws0, hlaws1, hS'p.2]
  have hmem : supAgreement laws ∈ agreementValues P := by
    refine ⟨laws, fun k => ?_, rfl⟩
    fin_cases k
    · exact hS'
    · exact hT'
  have hle : supAgreement laws ≤ sSup (agreementValues P) :=
    le_csSup (bddAbove_agreementValues P hw) hmem
  rw [multiSystemDistance_eq]
  rw [hsup] at hle
  linarith

/-- **Definition 2.28's `le_inf`-eliminator**: a bound holding at *every* pair
of probability representatives is a bound below the multi-system distance.
Together with `multiSystemDistance_le_statDist_of_equivalent` this exhibits
`multiSystemDistance` at a pair as the infimum of `δ` over probability
representatives — Definition 2.28's first display as the thesis means it.

The signed representative tuples that `classDistance` also ranges over are
inert here: `Probability.supAgreement_eq_zero_of_not_nonNeg` says a signed
tuple admits no joint at all, so it contributes `0` to a supremum of
non-negative numbers. -/
theorem le_multiSystemDistance {P : Fin 2 → PDS X Y} {a : ℝ}
    (hP0 : (P 0).isProbDist) (hP1 : (P 1).isProbDist)
    (h : ∀ S' T' : PDS X Y, equivalent (P 0) S' → equivalent (P 1) T' →
      S'.isProbDist → T'.isProbDist → a ≤ statDist S' T')
    (ha : a ≤ 1) :
    a ≤ multiSystemDistance P := by
  classical
  rw [multiSystemDistance_eq, le_sub_comm]
  refine Real.sSup_le ?_ (by linarith)
  rintro b ⟨laws, hlaws, rfl⟩
  by_cases hnn : ∀ k, (laws k).NonNeg
  · have hw0 : (laws 0).weight = 1 := by
      rw [← weight_eq_of_equivalent (hlaws 0), hP0.2]
    have hw1 : (laws 1).weight = 1 := by
      rw [← weight_eq_of_equivalent (hlaws 1), hP1.2]
    have hkey := h (laws 0) (laws 1) (hlaws 0) (hlaws 1) ⟨hnn 0, hw0⟩ ⟨hnn 1, hw1⟩
    rw [supAgreement_pair_eq_weight_sub_statDist laws hnn (by rw [hw0, hw1]),
      hw0]
    linarith
  · rw [supAgreement_eq_zero_of_not_nonNeg hnn]
    linarith

/-- **The comparison with the class distance**, in the direction that holds
without the probability hypotheses on the representatives: `Δ(S,T) ≤ Δ({S,T})`.
Theorem 2.29's lower bound consumes exactly this direction; the equality is
`classDistance_eq_ofReal_multiSystemDistance`.

The proof is the ε-approximation of the outer supremum: for every `ε > 0`
either some probability representative pair comes within `ε` of Definition
2.27's supremum — and then `classDistance` is below its `δ` — or the supremum
is itself below `ε`, in which case the right-hand side already exceeds `1`,
which bounds every `δ` of probability laws. -/
theorem classDistance_le_ofReal_multiSystemDistance {S T : PDS X Y}
    (hS : S.isProbDist) (hT : T.isProbDist)
    (P : Fin 2 → PDS X Y) (h0 : P 0 = S) (h1 : P 1 = T) :
    classDistance S T ≤ ENNReal.ofReal (multiSystemDistance P) := by
  classical
  have hw : 0 ≤ (P 0).weight := by rw [h0, hS.2]; exact zero_le_one
  have hbdd : BddAbove (agreementValues P) := bddAbove_agreementValues P hw
  have hone : sSup (agreementValues P) ≤ 1 :=
    sSup_agreementValues_le_one P (by rw [h0, hS.2])
  have hm0 : 0 ≤ multiSystemDistance P := by
    rw [multiSystemDistance_eq]; linarith
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨b, hbmem, hb⟩ :=
    exists_lt_of_lt_csSup (agreementValues_nonempty P)
      (show sSup (agreementValues P) - (ε : ℝ) < sSup (agreementValues P) by
        have : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
        linarith)
  obtain ⟨laws, hlaws, rfl⟩ := hbmem
  have hstep : classDistance S T ≤ ENNReal.ofReal (multiSystemDistance P + ε) := by
    by_cases hnn : ∀ k, (laws k).NonNeg
    · have hw0 : (laws 0).weight = 1 := by
        rw [← weight_eq_of_equivalent (hlaws 0), h0, hS.2]
      have hw1 : (laws 1).weight = 1 := by
        rw [← weight_eq_of_equivalent (hlaws 1), h1, hT.2]
      have hsup : supAgreement laws = 1 - statDist (laws 0) (laws 1) := by
        rw [supAgreement_pair_eq_weight_sub_statDist laws hnn (by rw [hw0, hw1]),
          hw0]
      have hδ : statDist (laws 0) (laws 1) ≤ multiSystemDistance P + ε := by
        rw [multiSystemDistance_eq]
        rw [hsup] at hb
        linarith
      refine (classDistance_le_statDist_of_equivalent
        (h0 ▸ hlaws 0) (h1 ▸ hlaws 1) (hnn 0) (hnn 1)).trans
        (ENNReal.ofReal_le_ofReal hδ)
    · rw [supAgreement_eq_zero_of_not_nonNeg hnn] at hb
      have hδ : statDist S T ≤ multiSystemDistance P + ε := by
        rw [multiSystemDistance_eq]
        have h1' : statDist S T ≤ 1 := by
          have := Probability.statDist_le_weight hS.1 hT.1
          rw [hS.2] at this
          exact this
        linarith
      refine (classDistance_le_statDist S T hS.1 hT.1).trans
        (ENNReal.ofReal_le_ofReal hδ)
  refine hstep.trans ?_
  rw [ENNReal.ofReal_add hm0 (by exact_mod_cast hε.le), ENNReal.ofReal_coe_nnreal]

/-- **Definition 2.28's identity at a pair, as an equality** — the Ruling-R9
payoff.  Definition 2.28 asserts that its two displays are one number:

  `Δ(S,T) = inf_{S'∈𝐒, T'∈𝐓} δ(S',T') = 1 − sup_{(S',T')∈𝐒×𝐓} sup_ℰ Pr^ℰ(S'=T')`

(the second display errata-corrected, see the file header).  Under Ruling R9
the left-hand side *is* `PDS.classDistance` — an infimum over honest
representatives, which at a probability class are exactly the thesis's
probability representatives — so the assertion is a theorem here, not the
one-sided comparison it had to be while `Δ` was unrestricted.

`≤` is `classDistance_le_ofReal_multiSystemDistance`.  `≥` is
`le_classDistance` against `multiSystemDistance_le_statDist_of_equivalent`:
weight is an invariant of the class (`weight_eq_of_equivalent`), so an honest
representative of a class of weight one is normalized, and R9's honesty clause
supplies exactly the `isProbDist` hypothesis that eliminator asks for. -/
theorem classDistance_eq_ofReal_multiSystemDistance {S T : PDS X Y}
    (hS : S.isProbDist) (hT : T.isProbDist)
    (P : Fin 2 → PDS X Y) (h0 : P 0 = S) (h1 : P 1 = T) :
    classDistance S T = ENNReal.ofReal (multiSystemDistance P) :=
  le_antisymm (classDistance_le_ofReal_multiSystemDistance hS hT P h0 h1)
    (le_classDistance fun S' T' hS' hT' hS'nn hT'nn =>
      ENNReal.ofReal_le_ofReal
        (multiSystemDistance_le_statDist_of_equivalent (h0 ▸ hS') (h1 ▸ hT')
          ⟨hS'nn, by rw [← weight_eq_of_equivalent hS', hS.2]⟩
          ⟨hT'nn, by rw [← weight_eq_of_equivalent hT', hT.2]⟩))

/-! ## Theorem 2.29 -/

/-- **Theorem 2.29's trivial inequality, per pair** (which implies the
thesis's `min_{i≠j}` display; no distinctness of `i` and `j` is needed): every
pair's multi-system distance is a lower bound for the tuple's.  Every
representative tuple projects to a representative pair, and every tuple joint
projects to a pair joint with at least the tuple's agreement.

`hw` is `bddAbove_agreementValues`'s hypothesis at the projected pair, whose
zeroth entry is `Sᵢ`: without an upper bound on the pair's supremum set the
real `sSup` collapses to its junk value and the comparison is meaningless. -/
theorem multiSystemDistance_pair_le {n : ℕ} [NeZero n] (S : Fin n → PDS X Y)
    (i j : Fin n) (hw : 0 ≤ (S i).weight) :
    multiSystemDistance (selectPair i j S) ≤ multiSystemDistance S := by
  classical
  have hwpair : 0 ≤ ((selectPair i j S) 0).weight := hw
  rw [multiSystemDistance_eq, multiSystemDistance_eq]
  refine sub_le_sub_left ?_ 1
  have hnonneg : 0 ≤ sSup (agreementValues (selectPair i j S)) :=
    (supAgreement_nonneg (selectPair i j S)).trans
      (le_csSup (bddAbove_agreementValues (selectPair i j S) hwpair)
        ⟨selectPair i j S, fun _ => equivalent_refl _, rfl⟩)
  refine Real.sSup_le ?_ hnonneg
  rintro a ⟨laws, hlaws, rfl⟩
  have hequiv : ∀ k, equivalent (selectPair i j S k) (selectPair i j laws k) := by
    intro k
    fin_cases k
    · exact hlaws i
    · exact hlaws j
  exact (supAgreement_le_of_pair_marginals (selectPair i j laws) i j rfl rfl).trans
    (le_csSup (bddAbove_agreementValues (selectPair i j S) hwpair)
      ⟨selectPair i j laws, hequiv, rfl⟩)

/-- **Theorem 2.29, the lower bound**: each pairwise class distance is below
the multi-system distance — per pair, which is the thesis's `min_{i≠j}`
display (`inf'_classDistance_le_multiSystemDistance`).  Composition of
`multiSystemDistance_pair_le` with the Definition 2.28 comparison. -/
theorem classDistance_le_ofReal_multiSystemDistance_of_mem {n : ℕ} [NeZero n]
    {S : Fin n → PDS X Y} (hprob : ∀ i, (S i).isProbDist) (i j : Fin n) :
    classDistance (S i) (S j) ≤ ENNReal.ofReal (multiSystemDistance S) := by
  have hw : 0 ≤ (S i).weight := by rw [(hprob i).2]; exact zero_le_one
  refine (classDistance_le_ofReal_multiSystemDistance (hprob i) (hprob j)
    (selectPair i j S) rfl rfl).trans ?_
  exact ENNReal.ofReal_le_ofReal (multiSystemDistance_pair_le S i j hw)

/-- Theorem 2.29's lower bound in the thesis's own `min_{i,j∈[n], i≠j}`
display, as an `inf'` over the off-diagonal pairs. -/
theorem inf'_classDistance_le_multiSystemDistance {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → PDS X Y} (hprob : ∀ i, (S i).isProbDist) :
    ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)).inf'
        ⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by simp⟩
        (fun p => classDistance (S p.1) (S p.2))
      ≤ ENNReal.ofReal (multiSystemDistance S) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hmem : ((⟨0, by omega⟩, ⟨1, by omega⟩) : Fin n × Fin n) ∈
      ({p : Fin n × Fin n | p.1 ≠ p.2} : Finset (Fin n × Fin n)) := by simp
  exact (Finset.inf'_le _ hmem).trans
    (classDistance_le_ofReal_multiSystemDistance_of_mem hprob _ _)

/-- **Theorem 2.29, the upper bound — in the corrected `max`-over-pairs form**
(attained: some pair `i ≠ j` realizes it).  For a representative tuple of
probability laws, with `ℓ` the number of distinct deterministic systems in
their supports,

  `Δ(𝒮) ≤ (min(n,ℓ) − 1) · δ(lawsᵢ, lawsⱼ)` for some `i ≠ j`,

hence `Δ(𝒮) ≤ (min(n,ℓ) − 1) · max_{i≠j} δ(lawsᵢ, lawsⱼ)`.

Two departures from the printed statement, both forced.  The printed
`min_{i≠j} Δ(Sᵢ,Sⱼ)` on the right is erratum (b): Lemma 2.30 controls the
*largest* pairwise distance, and the `min` form is refuted kernel-checked
(`Probability.printed_min_form_counterexample`).  And the right-hand side
carries the chosen representatives' `δ`, quantified over all representative
tuples, rather than the pairwise class distances: transferring to the pairwise
infima under a `max` would need one tuple attaining all pairwise infima
simultaneously, which the thesis does not provide — its transfer step is sound
only for the `min` form it misstates.  The thesis's `ℓ` counts the union over
*all* representatives; the per-tuple count here is smaller, so this bound is at
least as strong at every tuple. -/
theorem exists_pair_multiSystemDistance_le {n : ℕ} (hn : 2 ≤ n)
    {S : Fin n → PDS X Y} (laws : Fin n → PDS X Y)
    (hlaws : ∀ i, equivalent (S i) (laws i))
    (hprob : ∀ i, (laws i).isProbDist) :
    ∃ i j : Fin n, i ≠ j ∧
      multiSystemDistance S
        ≤ (((min n (supportUnion laws).card : ℕ) : ℝ) - 1)
            * statDist (laws i) (laws j) := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  have hw : ∀ k, (laws k).weight = 1 := fun k => (hprob k).2
  have hnn : ∀ k, (laws k).NonNeg := fun k => (hprob k).1
  obtain ⟨i, j, hij, hbound⟩ := exists_pair_one_sub_supAgreement_le hn laws hprob
  refine ⟨i, j, hij, ?_⟩
  have hmsd : multiSystemDistance S ≤ 1 - supAgreement laws := by
    rw [multiSystemDistance_eq]
    have hwS : 0 ≤ (S 0).weight := by
      rw [weight_eq_of_equivalent (hlaws 0), hw 0]
      exact zero_le_one
    have hle := le_csSup (bddAbove_agreementValues S hwS) ⟨laws, hlaws, rfl⟩
    linarith
  have hpairδ : 1 - supAgreement (selectPair i j laws)
      = statDist (laws i) (laws j) := by
    have hnn' : ∀ k, ((selectPair i j laws) k).NonNeg := by
      intro k
      fin_cases k
      · exact hnn i
      · exact hnn j
    have hsup := supAgreement_pair_eq_weight_sub_statDist (selectPair i j laws)
      hnn' (by simp only [selectPair_zero, selectPair_one, hw i, hw j])
    simp only [selectPair_zero, selectPair_one, hw i] at hsup
    rw [hsup]
    ring
  rw [hpairδ] at hbound
  exact hmsd.trans hbound

end PDS

end

end RandomSystems

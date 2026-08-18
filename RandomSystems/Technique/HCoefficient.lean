/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Environment
import Probability.Counting

/-!
# The H-coefficient technique, layer 3: the transcript factorization

Maurer, *Cryptography Foundations* (ETH Zürich, Spring 2018 — the tree's
`CR18`), §3.6.5 *Computing the Transcript Distribution*, **Lemma 3.2, printed
page 70**, read on the rendered page:

> For a PDS `S` and a PDE `E` we have
> `p^{ES}_{X^k Y^k}(x^k, y^k) = p^E_{X^k|Y^{k-1}}(x^k, y^{k-1}) · p^S_{Y^k|X^k}(y^k, x^k)`.

A transcript's probability is an **environment factor** times a **system
factor**.  That single identity is the whole of the H-coefficient technique's
system-facing half: the environment factor does not mention the system, so it
cancels from any *ratio* of two transcript laws taken at the same transcript,
and a hypothesis about the ratio may therefore be checked with the adversary
deleted — non-adaptively, transcript by transcript.

*Source flag (PHI-SPEC R8).*  CR18 is **fallback-only** under the source
hierarchy (MauRen16 / Jost / LiuMau20 / Lanzenberger); it is used here because
it is also the source this tree already cites for the objects the statement is
about — `System.DDE.Total` is CR18 Definition 3.6 and `PDS.trLawFullyDefined`
is CR18 Definition 3.7 (`RandomSystems/System/Environment.lean`).  The
reference repository additionally cites an unpublished-to-this-tree "thesis
App. A.1" for the same identity; that page is not on disk and is **not**
claimed here.

*Attribution flag.*  The technique itself is attributed in the literature to
Patarin ("coefficients H"), and its partition refinement to Chen–Steinberger.
Following the T0 precedent (`Probability/StatisticalDistance.lean`), those
names are **recorded, not verified**: no bibliography entry, year or page for
either exists in the reference repository, no such paper is on disk, and
neither sits in the source hierarchy.  Upgrading them to page-verified
citations is owed.

## The three layers (PHI-SPEC R10)

1. the partition bounds and 2. the good/bad ratio kernel are landed in
`Probability/StatisticalDistance.lean` (`statDist_sum_of_disjoint_support`,
`hTechnique_ratio`, `hTechnique_partition`, …) and are **consumed**, not
re-proved.  This file is layer 3, the only build item: the factorization on
this tree's transcript observables, and the environment-uniform corollary it
buys.

## What is defined here

Nothing new is carried (PHI-SPEC R11(a)): every object below is a definition
over the landed carrier — `System.DDS`, `System.DDE.Total`,
`System.DDE.Total.transcript`, `PDS`, `PDS.trLawFullyDefined`,
`PDS.advFullyDefined`.

* `System.TranscriptSystemEvent` / `System.TranscriptEnvironmentEvent` — CR18
  Lemma 3.2's two rectangle events, split so that each mentions only one of
  the two parties.  `System.transcript_eq_iff` is the split itself: a run
  produces the transcript `t` exactly when the environment asks `t`'s queries
  and halts on schedule **and** the system gives `t`'s answers.
* `System.transcriptEnvironmentFactor` (`η`) — the environment factor.  On
  the R4 carrier the environment is deterministic, so `η ∈ {0,1}`: it is the
  indicator that `t` is a run of `e` at horizon `n`.
* `PDS.transcriptSystemFactor` (`σ`) — the system factor `p^S_{Y^k|X^k}`, the
  law's mass on the deterministic systems that answer `t`.
* `PDS.trLawFullyDefined_apply` — **Lemma 3.2 on this carrier**:
  `tr(S,e,n)(t) = η(e,n,t) · σ(S,t)`, an exact equality.
* `PDS.h_coefficient_theorem` — the user-facing endpoint, uniform over
  environments and over the interaction length.

## The `⊥`-total carrier (F-2)

Refusal is an observable answer (PHI-SPEC R2), so a transcript entry carries
`Option Y` and a transcript containing refusals factorizes exactly like any
other: the system event constrains `s⊥`, whose value at a refused query *is*
`none`.  No totality hypothesis appears anywhere below.
-/

noncomputable section

open scoped ENNReal NNReal

namespace RandomSystems

open Probability

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-! ### CR18 Lemma 3.2's two rectangle events

Lemma 3.2 factors the transcript probability because the run condition
`tr(s,e,n) = t` is a *conjunction* of a condition on `e` alone and a condition
on `s` alone.  The two definitions below are those conjuncts.  Each is phrased
over the rounds of `t` — a round is a prefix of `t` ending in one entry — so no
index arithmetic enters the statements. -/

/-- **CR18 Lemma 3.2, system conjunct.**  The deterministic system `s` produces
exactly the answers recorded in `t`: at every round, `s⊥` maps the input
history of that round to the answer the round records.  `none` is a genuine
answer (a refusal), so this is a condition on `s⊥`, not on `s`, and it never
demands totality. -/
def TranscriptSystemEvent (s : DDS X Y) (t : List (X × Option Y)) : Prop :=
  ∀ u : List (X × Option Y), ∀ x : X, ∀ y : Option Y, u ++ [(x, y)] <+: t →
    output s⊥ (u↓ₓ ++ [x]) (by simp [fullyDefined, dom]) = y

/-- **CR18 Lemma 3.2, environment conjunct**, at horizon `n`.  The environment
`e` asks exactly the queries recorded in `t`, having seen exactly the answers
recorded before them, and its halting is on schedule for `n` moves: `t` is not
longer than `n`, and if it is shorter then `e` has stopped at `t`.

The horizon is an environment-side index — `PDS.trLawFullyDefined` is indexed
by the number of environment moves — so it belongs to this conjunct.  What
matters for Lemma 3.2 is that nothing here mentions the system. -/
def TranscriptEnvironmentEvent (e : DDE.Total Y X) (n : ℕ)
    (t : List (X × Option Y)) : Prop :=
  (∀ u : List (X × Option Y), ∀ x : X, ∀ y : Option Y, u ++ [(x, y)] <+: t →
      e u↓ᵧ = some x) ∧
    t.length ≤ n ∧ (t.length < n → e t↓ᵧ = none)

namespace DDE.Total

/-- A run of `n` environment moves records at most `n` rounds. -/
theorem length_transcript_le (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ) :
    (transcript s e n).length ≤ n := by
  induction n with
  | zero => simp [transcript]
  | succ n ih =>
      rcases hx : e (transcript s e n)↓ᵧ with _ | x
      · simp only [transcript, hx]
        exact ih.trans (Nat.le_succ n)
      · simp only [transcript, hx, List.length_append, List.length_singleton]
        exact Nat.succ_le_succ ih

/-- Once the environment has stopped, the transcript no longer grows. -/
theorem transcript_add_eq_of_halted {s : DDS X Y} {e : DDE.Total Y X} {m : ℕ}
    (h : e (transcript s e m)↓ᵧ = none) (k : ℕ) :
    transcript s e (m + k) = transcript s e m := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hx : e (transcript s e (m + k))↓ᵧ = none := by rw [ih]; exact h
      show transcript s e (m + k + 1) = transcript s e m
      simp only [transcript, hx]
      exact ih

/-- A run of `n` moves satisfies the environment conjunct at horizon `n`. -/
theorem transcriptEnvironmentEvent_transcript (s : DDS X Y) (e : DDE.Total Y X)
    (n : ℕ) : TranscriptEnvironmentEvent e n (transcript s e n) := by
  induction n with
  | zero =>
      refine ⟨fun u x y hu => ?_, by simp [transcript], by simp⟩
      simp only [transcript] at hu
      exact absurd (List.eq_nil_of_prefix_nil hu) (by simp)
  | succ n ih =>
      obtain ⟨hask, hlen, hstop⟩ := ih
      rcases hx : e (transcript s e n)↓ᵧ with _ | x
      · refine ⟨fun u x' y hu => hask u x' y (by simpa [transcript, hx] using hu),
          by simp only [transcript, hx]; exact hlen.trans (Nat.le_succ n),
          fun _ => by simp only [transcript, hx]⟩
      · refine ⟨fun u x' y hu => ?_, ?_, ?_⟩
        · rw [show transcript s e (n + 1) =
              transcript s e n ++ [(x, output s⊥ ((transcript s e n)↓ₓ ++ [x]) (by simp [fullyDefined, dom]))] by
            simp only [transcript, hx]] at hu
          rcases List.prefix_concat_iff.mp hu with heq | hpre
          · obtain ⟨hu', hlast⟩ := List.append_inj heq (by
              have := congrArg List.length heq
              simp only [List.length_append, List.length_singleton] at this
              omega)
            have hx1 : x' = x := by
              have h := congrArg
                (fun l : List (X × Option Y) => l.head?.map Prod.fst) hlast
              simpa using h
            rw [hu', hx1]
            exact hx
          · exact hask u x' y hpre
        · simp only [transcript, hx, List.length_append, List.length_singleton]
          exact Nat.succ_le_succ hlen
        · intro hlt
          simp only [transcript, hx, List.length_append, List.length_singleton] at hlt
          exact absurd hx (by rw [hstop (by omega)]; simp)

/-- A run of `n` moves satisfies the system conjunct. -/
theorem transcriptSystemEvent_transcript (s : DDS X Y) (e : DDE.Total Y X)
    (n : ℕ) : TranscriptSystemEvent s (transcript s e n) := by
  induction n with
  | zero =>
      intro u x y hu
      simp only [transcript] at hu
      exact absurd (List.eq_nil_of_prefix_nil hu) (by simp)
  | succ n ih =>
      intro u x' y hu
      rcases hx : e (transcript s e n)↓ᵧ with _ | x
      · exact ih u x' y (by simpa [transcript, hx] using hu)
      · rw [show transcript s e (n + 1) =
            transcript s e n ++ [(x, output s⊥ ((transcript s e n)↓ₓ ++ [x]) (by simp [fullyDefined, dom]))] by
          simp only [transcript, hx]] at hu
        rcases List.prefix_concat_iff.mp hu with heq | hpre
        · obtain ⟨hu', hlast⟩ := List.append_inj heq (by
            have := congrArg List.length heq
            simp only [List.length_append, List.length_singleton] at this
            omega)
          have hpair : (x', y) =
              (x, output s⊥ ((transcript s e n)↓ₓ ++ [x])
                (by simp [fullyDefined, dom])) := by
            have h := congrArg (fun l : List (X × Option Y) => l.head?) hlast
            simp only [List.head?_cons, Option.some.injEq] at h
            exact h
          have hx1 : x' = x := congrArg Prod.fst hpair
          have hy1 : y = output s⊥ ((transcript s e n)↓ₓ ++ [x])
              (by simp [fullyDefined, dom]) := congrArg Prod.snd hpair
          subst hx1
          subst hu'
          exact hy1.symm
        · exact ih u x' y hpre

/-- Reading the two conjuncts back: a transcript satisfying both is the run. -/
theorem transcript_length_eq_self {s : DDS X Y} {e : DDE.Total Y X}
    {t : List (X × Option Y)}
    (hE : ∀ u : List (X × Option Y), ∀ x : X, ∀ y : Option Y, u ++ [(x, y)] <+: t →
      e u↓ᵧ = some x)
    (hS : TranscriptSystemEvent s t) :
    transcript s e t.length = t := by
  induction t using List.reverseRecOn with
  | nil => rfl
  | append_singleton t entry ih =>
      obtain ⟨x, y⟩ := entry
      have hpre : ∀ (u : List (X × Option Y)) (x' : X) (y' : Option Y),
          u ++ [(x', y')] <+: t → u ++ [(x', y')] <+: t ++ [(x, y)] :=
        fun u x' y' h => h.trans (List.prefix_append _ _)
      have iht : transcript s e t.length = t :=
        ih (fun u x' y' h => hE u x' y' (hpre u x' y' h))
          (fun u x' y' h => hS u x' y' (hpre u x' y' h))
      have hx : e t↓ᵧ = some x := hE t x y List.prefix_rfl
      have hy : output s⊥ (t↓ₓ ++ [x]) (by simp [fullyDefined, dom]) = y :=
        hS t x y List.prefix_rfl
      simp only [List.length_append, List.length_singleton]
      show transcript s e (t.length + 1) = t ++ [(x, y)]
      simp only [transcript, iht, hx]
      rw [hy]

/-- **CR18 Lemma 3.2, the split.**  A run of `n` environment moves produces the
transcript `t` exactly when `e` asks `t`'s queries and halts on schedule, and
`s` gives `t`'s answers.  The right-hand side is a conjunction of one condition
on `e` and one condition on `s`, which is what makes the transcript law
factorize. -/
theorem transcript_eq_iff (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ)
    (t : List (X × Option Y)) :
    transcript s e n = t ↔
      TranscriptEnvironmentEvent e n t ∧ TranscriptSystemEvent s t := by
  constructor
  · rintro rfl
    exact ⟨transcriptEnvironmentEvent_transcript s e n,
      transcriptSystemEvent_transcript s e n⟩
  · rintro ⟨⟨hask, hlen, hstop⟩, hS⟩
    have hself : transcript s e t.length = t := transcript_length_eq_self hask hS
    rcases Nat.eq_or_lt_of_le hlen with heq | hlt
    · rw [← heq]; exact hself
    · have hhalt : e (transcript s e t.length)↓ᵧ = none := by
        rw [hself]; exact hstop hlt
      have := transcript_add_eq_of_halted hhalt (n - t.length)
      rw [Nat.add_sub_cancel' hlen] at this
      rw [this]; exact hself

end DDE.Total

/-! ### The environment factor `η`

On the R4 carrier the environment is deterministic (`DDE.Total`), so CR18's
`p^E_{X^k|Y^{k-1}}` is `0` or `1`: it is the indicator of the environment
conjunct.  Its only two properties used below are that it is non-negative and
that it does not mention the system. -/

open Classical in
/-- CR18 Lemma 3.2's environment factor `p^E_{X^k|Y^{k-1}}` on this carrier:
the `0/1` indicator that `t` is a run of `e` at horizon `n`.  It is the whole
of the environment's contribution to a transcript's probability — and it
carries no system. -/
def transcriptEnvironmentFactor (e : DDE.Total Y X) (n : ℕ)
    (t : List (X × Option Y)) : ℝ :=
  if TranscriptEnvironmentEvent e n t then 1 else 0

theorem transcriptEnvironmentFactor_eq_one {e : DDE.Total Y X} {n : ℕ}
    {t : List (X × Option Y)} (h : TranscriptEnvironmentEvent e n t) :
    transcriptEnvironmentFactor e n t = 1 := by
  classical
  simp only [transcriptEnvironmentFactor, if_pos h]

theorem transcriptEnvironmentFactor_eq_zero {e : DDE.Total Y X} {n : ℕ}
    {t : List (X × Option Y)} (h : ¬ TranscriptEnvironmentEvent e n t) :
    transcriptEnvironmentFactor e n t = 0 := by
  classical
  simp only [transcriptEnvironmentFactor, if_neg h]

theorem transcriptEnvironmentFactor_nonneg (e : DDE.Total Y X) (n : ℕ)
    (t : List (X × Option Y)) : 0 ≤ transcriptEnvironmentFactor e n t := by
  classical
  simp only [transcriptEnvironmentFactor]
  split <;> norm_num

end System

namespace PDS

/-! ### The system factor `σ` -/

/-- CR18 Lemma 3.2's system factor `p^S_{Y^k|X^k}`: the mass the law `S` puts
on the deterministic systems that answer `t`.  It mentions no environment and
no horizon — that is the content of "the adversary factors out". -/
def transcriptSystemFactor (S : PDS X Y) (t : List (X × Option Y)) : ℝ :=
  S.mass (fun s => System.TranscriptSystemEvent s t)

theorem transcriptSystemFactor_nonneg {S : PDS X Y} (hS : S.NonNeg)
    (t : List (X × Option Y)) : 0 ≤ transcriptSystemFactor S t :=
  hS.mass_nonneg _

/-- **CR18 Lemma 3.2 on this carrier.**  The transcript law of `S` against the
deterministic environment `e` after `n` moves factorizes at every transcript:

  `tr(S, e, n)(t) = η(e, n, t) · σ(S, t)`

with `η` free of `S`.  An exact equality, and it holds at transcripts carrying
refusals just as at fully answered ones (PHI-SPEC R2/F-2). -/
theorem trLawFullyDefined_apply (e : System.DDE.Total Y X) (n : ℕ) (S : PDS X Y)
    (t : List (X × Option Y)) :
    trLawFullyDefined e n S t =
      System.transcriptEnvironmentFactor e n t * transcriptSystemFactor S t := by
  rw [trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
  by_cases h : System.TranscriptEnvironmentEvent e n t
  · rw [System.transcriptEnvironmentFactor_eq_one h, one_mul, transcriptSystemFactor]
    exact Distribution.mass_congr S fun s => by
      rw [System.DDE.Total.transcript_eq_iff]
      exact ⟨fun hc => hc.2, fun hc => ⟨h, hc⟩⟩
  · rw [System.transcriptEnvironmentFactor_eq_zero h, zero_mul]
    exact Distribution.mass_eq_zero_of_forall_not S fun s hs =>
      h ((System.DDE.Total.transcript_eq_iff s e n t).mp hs).1

/-- **The transcript distance with the adversary factored out.**  At a fixed
environment and horizon the distance between the two transcript laws is a sum
of *system-factor* gaps, each gated by the environment's `0/1` factor:

  `δ(tr(S,e,n), tr(T,e,n)) = Σ_t η(e,n,t) · max(σ(S,t) − σ(T,t), 0)`.

Every summand is environment-free; the environment only selects which of them
are counted.  The index set is any finite set carrying the difference's support
(`Distribution` is finitely supported), so no finiteness of the transcript
space is used. -/
theorem statDist_trLawFullyDefined_eq_sum (S T : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) {c : Finset (List (X × Option Y))}
    (hc : (trLawFullyDefined e n S - trLawFullyDefined e n T).support ⊆ c) :
    statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T) =
      ∑ t ∈ c, System.transcriptEnvironmentFactor e n t *
        max (transcriptSystemFactor S t - transcriptSystemFactor T t) 0 := by
  rw [statDist_eq_sum_of_support_subset _ _ hc]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [trLawFullyDefined_apply, trLawFullyDefined_apply, ← mul_sub,
    mul_max_of_nonneg _ _ (System.transcriptEnvironmentFactor_nonneg e n t), mul_zero]

/-- **The ratio transfers, uniformly over environments.**  A pointwise ratio
between the *system factors* — an environment-free, non-adaptive hypothesis —
is inherited by the transcript laws against every deterministic environment and
at every horizon, because the common environment factor is non-negative and
cancels.  This is the sentence "adaptivity is free" in one line. -/
theorem trLawFullyDefined_ratio_of_transcriptSystemFactor_ratio
    {S T : PDS X Y} {eps : ℝ≥0} {Bad : List (X × Option Y) → Prop}
    (h : ∀ t, ¬ Bad t → (1 - eps) * transcriptSystemFactor T t ≤
      transcriptSystemFactor S t)
    (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)) (ht : ¬ Bad t) :
    (1 - eps) * trLawFullyDefined e n T t ≤ trLawFullyDefined e n S t := by
  rw [trLawFullyDefined_apply, trLawFullyDefined_apply, ← mul_assoc, mul_comm (1 - (eps : ℝ)),
    mul_assoc]
  exact mul_le_mul_of_nonneg_left (h t ht)
    (System.transcriptEnvironmentFactor_nonneg e n t)

end PDS

/-! ### The layer-2 kernel at an infinite carrier

**Declared deviation, stated plainly.**  The statement below is
`Probability.hTechnique_ratio` with `[Fintype A]` deleted, and it is proved
again rather than derived — layer 2 cannot supply it, because the `Fintype`
sits in its hypotheses.  The carrier forces this: the transcript space
`List (X × Option Y)` is infinite even for finite alphabets, so **no** endpoint
of this file could be stated through the landed form.

The deletion is the correction the metric already carries one level down.
`Probability.statDist`'s own docstring records it — "*No `Fintype` is needed,
and requiring one was a spurious restriction*" — and
`Probability.statDist_eq_sum_of_support_subset`,
`Probability.Distribution.weight_eq_sum_of_support_subset` and
`Probability.Distribution.mass_eq_sum_of_support_subset` are the support-indexed
companions it is proved from.  `Distribution` is `A →₀ ℝ`: finite support is
already in the carrier, and the H-lemmas were simply never revisited.

**PROPOSED RELOCATION.**  This belongs in `Probability/StatisticalDistance.lean`
*in place of* `hTechnique_ratio`, which is then its `Fintype` instance and needs
no separate proof.  It is kept here only to respect the T5 lane. -/

/-- **Layer 2 without `[Fintype]`.**  If the real/ideal density ratio is at
least `1 - ε` on good points then `δ(real, ideal) ≤ Pr_ideal[Bad] + ε`.  Sums
run over `(ideal - real).support ∪ ideal.support`, so no finiteness of the
carrier is used. -/
theorem statDist_le_probBad_add_of_ratio_on_good {A : Type*}
    (real ideal : Distribution A) (Bad : A → Prop) (eps : ℝ≥0)
    (h_real_nonneg : real.NonNeg) (h_ideal_nonneg : ideal.NonNeg)
    (h_weight : real.weight = ideal.weight)
    (h_ideal_le : ideal.weight ≤ 1)
    (h_ratio : ∀ a, ¬ Bad a → (1 - eps) * ideal a ≤ real a) :
    statDist real ideal ≤ probBad ideal Bad + eps := by
  classical
  set s : Finset A := (ideal - real).support ∪ ideal.support with hs
  have hsub : (ideal - real).support ⊆ s := Finset.subset_union_left
  have hsupp : ideal.support ⊆ s := Finset.subset_union_right
  rw [statDist_symm_of_eq_weight real ideal h_weight,
    statDist_eq_sum_of_support_subset ideal real hsub]
  have hterm : ∀ a ∈ s,
      max (ideal a - real a) 0 ≤ (if Bad a then ideal a else 0) + eps * ideal a := by
    intro a _
    by_cases hbad : Bad a
    · have h0 := h_ideal_nonneg a
      have h1 := h_real_nonneg a
      have h2 : 0 ≤ (eps : ℝ) * ideal a :=
        mul_nonneg eps.coe_nonneg (h_ideal_nonneg a)
      simp only [hbad, if_true]
      exact max_le (by linarith) (by linarith)
    · simp only [hbad, if_false, zero_add]
      exact max_le (sub_le_mul_of_one_sub_mul_le (h_ratio a hbad))
        (mul_nonneg eps.coe_nonneg (h_ideal_nonneg a))
  calc ∑ a ∈ s, max (ideal a - real a) 0
      ≤ ∑ a ∈ s, ((if Bad a then ideal a else 0) + (eps : ℝ) * ideal a) :=
        Finset.sum_le_sum hterm
    _ = (∑ a ∈ s.filter Bad, ideal a) + (eps : ℝ) * ∑ a ∈ s, ideal a := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_filter]
    _ = probBad ideal Bad + (eps : ℝ) * ideal.weight := by
        rw [probBad, Distribution.mass_eq_sum_of_support_subset ideal hsupp,
          Distribution.weight_eq_sum_of_support_subset ideal hsupp]
    _ ≤ probBad ideal Bad + eps := by
        have : (eps : ℝ) * ideal.weight ≤ (eps : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left h_ideal_le eps.coe_nonneg
        linarith

namespace PDS

/-! ### The endpoint -/

/-- **The H-coefficient theorem** (CR18 Lemma 3.2 composed with the layer-2
kernel).

  a ratio on the **system factors** over the good transcripts,
  plus a bound on the ideal law's **bad mass**,
  gives `Adv⊥(S, T) ≤ δ_b + ε`.

Both hypotheses are checked with the adversary deleted in the sense that
matters: the ratio hypothesis mentions no environment and no horizon at all —
it is a statement about `σ`, and the environment factor cancels from it
(`trLawFullyDefined_ratio_of_transcriptSystemFactor_ratio`) — and the bad-mass
hypothesis is the technique's **sole adaptive residue**, a quantity that must
be bounded uniformly over environments.  That division is the integration
contract of the method.

The bound is read in `ℝ≥0∞` through the lossless `ℝ≥0 → ℝ≥0∞` coercion, not
through `ENNReal.ofReal`: `ε` and `δ_b` are non-negative by type. -/
theorem h_coefficient_theorem {S T : PDS X Y} {Bad : List (X × Option Y) → Prop}
    {eps δb : ℝ≥0}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight) (hT1 : T.weight ≤ 1)
    (h_ratio : ∀ t, ¬ Bad t →
      (1 - eps) * transcriptSystemFactor T t ≤ transcriptSystemFactor S t)
    (h_bad : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      probBad (trLawFullyDefined e n T) Bad ≤ δb) :
    advFullyDefined S T ≤ (δb + eps : ℝ≥0) := by
  refine iSup_le fun e => iSup_le fun n => ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  have hker := statDist_le_probBad_add_of_ratio_on_good
    (trLawFullyDefined e n S) (trLawFullyDefined e n T) Bad eps
    (hS.fTransform _) (hT.fTransform _)
    (by rw [weight_trLawFullyDefined, weight_trLawFullyDefined, hw])
    (by rw [weight_trLawFullyDefined]; exact hT1)
    (fun t ht => trLawFullyDefined_ratio_of_transcriptSystemFactor_ratio h_ratio e n t ht)
  have hb := h_bad e n
  push_cast
  linarith

/-- **The equality-on-good form.**  If the two system factors *agree* on the
good transcripts, the distance is the ideal bad mass alone.  This is the
`ε = 0` instance of the theorem: the ratio hypothesis at `ε = 0` is exactly
`σ_T ≤ σ_S`, which equality supplies. -/
theorem h_coefficient_theorem_eq_on_good {S T : PDS X Y}
    {Bad : List (X × Option Y) → Prop} {δb : ℝ≥0}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight) (hT1 : T.weight ≤ 1)
    (h_eq : ∀ t, ¬ Bad t → transcriptSystemFactor T t = transcriptSystemFactor S t)
    (h_bad : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      probBad (trLawFullyDefined e n T) Bad ≤ δb) :
    advFullyDefined S T ≤ (δb : ℝ≥0) := by
  have h := h_coefficient_theorem (eps := 0) hS hT hw hT1
    (fun t ht => by simpa using (h_eq t ht).le) h_bad
  simpa using h

/-- **The perfect form** (`Bad = ∅`): a ratio holding at *every* transcript
gives `Adv⊥(S, T) ≤ ε` with no adaptive residue at all. -/
theorem h_coefficient_theorem_of_forall {S T : PDS X Y} {eps : ℝ≥0}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight) (hT1 : T.weight ≤ 1)
    (h_ratio : ∀ t, (1 - eps) * transcriptSystemFactor T t ≤
      transcriptSystemFactor S t) :
    advFullyDefined S T ≤ (eps : ℝ≥0) := by
  have h := h_coefficient_theorem (Bad := fun _ => False) (δb := 0) hS hT hw hT1
    (fun t _ => h_ratio t)
    (fun e n => by
      rw [probBad]
      exact le_of_eq (Distribution.mass_eq_zero_of_forall_not _ fun _ h => h))
  simpa using h

/-! ### Receipt: the counting layer feeds `ε`

Not an application — no concrete `S`, `T` or alphabet appears.  The receipt
records the *shape* in which `Probability/Counting.lean` is consumed: the
counting layer produces exactly a pointwise inequality between two per-
transcript masses, which is what the ratio hypothesis of the endpoint asks
for, with the birthday defect landing in `ε`. -/

/-- **The switching ratio slots into `ε`.**  If, off the bad set, the ideal
system factor is the uniform-permutation mass `(N−q)!/N!` and the real one is
the uniform-function mass `1/N^q`, then `Probability.Counting.switching_ratio_le`
discharges the endpoint's ratio hypothesis with `ε = q(q−1)/2N`, and the
technique returns

  `Adv⊥(S, T) ≤ δ_b + q(q−1)/2N`.

The two mass hypotheses are exactly what a counting argument delivers; nothing
else about the systems is used. -/
theorem h_coefficient_theorem_switching_ratio {S T : PDS X Y}
    {Bad : List (X × Option Y) → Prop} {δb : ℝ≥0} {N q : ℕ}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight) (hT1 : T.weight ≤ 1)
    (hqN : q ≤ N) (hN : 0 < N)
    (h_eps : ((q * (q - 1) : ℕ) : ℝ≥0) / ((2 * N : ℕ) : ℝ≥0) ≤ 1)
    (h_ideal : ∀ t, ¬ Bad t → transcriptSystemFactor T t =
      ((((N - q).factorial : ℝ≥0) / ((N.factorial : ℝ≥0))) : ℝ))
    (h_real : ∀ t, ¬ Bad t → transcriptSystemFactor S t =
      ((1 / (N : ℝ≥0) ^ q : ℝ≥0) : ℝ))
    (h_bad : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      probBad (trLawFullyDefined e n T) Bad ≤ δb) :
    advFullyDefined S T ≤
      (δb + ((q * (q - 1) : ℕ) : ℝ≥0) / ((2 * N : ℕ) : ℝ≥0) : ℝ≥0) := by
  refine h_coefficient_theorem hS hT hw hT1 (fun t ht => ?_) h_bad
  have h := NNReal.coe_le_coe.mpr (Probability.Counting.switching_ratio_le hqN hN h_eps)
  rw [NNReal.coe_mul, NNReal.coe_sub h_eps, NNReal.coe_one] at h
  rw [h_ideal t ht, h_real t ht]
  exact h

end PDS

end RandomSystems

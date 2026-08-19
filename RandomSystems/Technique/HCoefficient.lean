/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Environment
import Probability.Counting

/-!
# The H-coefficient technique, layer 3: the transcript factorization

**Primary source.**  David Lanzenberger, *Coupling Techniques for Cryptographic
Proofs* (the thesis; `papers/thesis (1).pdf` in the reference repository),
**Appendix A.1, printed pp. 87–88** (PDF leaves 97–98), read on the rendered
page.  §A.1 is headed *"Extra Proofs for Chapter 2"*; printed p. 87 opens
*"Proof (of Theorem 2.18)"* — the result that transcript equivalence under all
compatible **non-adaptive** deterministic environments already gives it under
*"all compatible (𝒴,𝒳)-DDE e (even adaptive ones)"*.  Printed p. 88 carries the
step this file formalizes, verbatim:

> "Observe moreover that for any (𝒳,𝒴)-DDS `s` and any compatible (𝒴,𝒳)-DDE
> `ē`, the transcript `tr(s, ē)` is `t̂` **if and only if** `s(x̂ⁱ) = ŷᵢ` **and**
> `ē(ŷ^{i−1}) = x̂ᵢ` for all `i ∈ [l]`."

and, immediately after, the system factor itself:

> `tr(S, e′)(t̂) = S({s | s ∈ dom(S), ∀i ∈ [l] : s(x̂ⁱ) = ŷᵢ}) = tr(S, e)(t̂)`.

The *iff* is `System.DDE.Total.transcript_eq_iff`; the `S`-mass on its
right-hand side is `PDS.transcriptSystemFactor`; and the fact that the two
environments `e`, `e′` give the *same* value is the environment factor
cancelling.  Lanzenberger is **primary** under PHI-SPEC R8, and the thesis both
states and proves this, so no fallback is invoked for the mathematics.

**Secondary provenance.**  Maurer, *Cryptography Foundations* (ETH Zürich,
Spring 2018 — the tree's `CR18`), §3.6.5 *Computing the Transcript
Distribution*, **Lemma 3.2, printed page 70**, read on the rendered page:

> For a PDS `S` and a PDE `E` we have
> `p^{ES}_{X^k Y^k}(x^k, y^k) = p^E_{X^k|Y^{k-1}}(x^k, y^{k-1}) · p^S_{Y^k|X^k}(y^k, x^k)`.

CR18 generalizes the thesis step to *probabilistic* environments and names the
two factors; it states the lemma **without proof** ("We omit the proof of the
following lemma").  It is recorded here as provenance and as the source of the
`η`/`σ` naming — not as the governing source, and no R8 fallback exception is
claimed: a primary addresses this concept.  (CR18 is separately, and
legitimately, this tree's cited source for the *objects*: `System.DDE.Total` is
CR18 Definition 3.6 and `PDS.trLawFullyDefined` is CR18 Definition 3.7, per
`RandomSystems/System/Environment.lean`.)

A transcript's probability is an **environment factor** times a **system
factor**.  That single identity is the whole of the H-coefficient technique's
system-facing half: the environment factor does not mention the system, so it
cancels from any *ratio* of two transcript laws taken at the same transcript,
and a hypothesis about the ratio may therefore be checked with the adversary
deleted — non-adaptively, transcript by transcript.  That is precisely the use
Appendix A.1 makes of it.

*Attribution flag.*  The *technique* built on top of the identity is attributed
in the literature to Patarin ("coefficients H"), and its partition refinement to
Chen–Steinberger.  Following the T0 precedent
(`Probability/StatisticalDistance.lean`), those names are **recorded, not
verified**: no bibliography entry, year or page for either exists in the
reference repository, no such paper is on disk, and neither sits in the source
hierarchy.  Upgrading them to page-verified citations is owed.  (This flag
concerns layer 2's `δb + ε` shape only; the factorization below is
primary-sourced.)

## Minimal-migration map (PHI-SPEC R11(b))

The reference repository carries this development **twice**: once for
probabilistic environments over fixed-length transcripts
(`RandomSystems/PDS.lean`, `HTechnique/Derivation.lean`), and once for
*deterministic* environments over exactly this carrier — variable-length
`List (X × Option Y)`, `⊥`-total — which is the family that matches here.  The
node-by-node correspondence, so the adaptation is auditable:

| here | reference repository (READ-ONLY) |
|---|---|
| `System.TranscriptEnvironmentEvent` | the `hq` + `hlen` hypotheses of `RandomSystem.lean:750` `transcript_eq_iff_of_consistent` (`hlen` written as a disjunction; here as `≤ n ∧ (< n → halt)`) |
| `System.TranscriptSystemEvent` | that theorem's right-hand side; second conjunct of `RandomSystem.lean:634` `transcript_consistent` |
| `transcriptEnvironmentEvent_transcript` + `transcriptSystemEvent_transcript` | `RandomSystem.lean:634` `transcript_consistent` (both halves in one statement) |
| `transcript_length_eq_self` | `RandomSystem.lean:688` `transcript_eq_of_consistent` |
| `transcript_eq_iff` | `RandomSystem.lean:750` `transcript_eq_iff_of_consistent`; thesis-named alias `LanzenbergerChain.lean:160` `fixed_transcript_event_eq_fixed_query_event` |
| `length_transcript_le` | `Lemma415.lean:113` `transcript_length_le` |
| `transcript_add_eq_of_halted` | `RandomSystem.lean:1270` `transcript_stall_of_length_lt'` and its `transcript_succ_stall` neighbourhood |
| `transcriptSystemFactor` (`σ`) | `Derivation.lean:588` `sysFactor` / `PDS.lean:2390` `transcriptSystemFactor` |
| `transcriptEnvironmentFactor` (`η`) | `Derivation.lean:573` `envFactor` / `PDS.lean:2396` |
| `trLawFullyDefined_apply` | `PDS.lean:2668` `transcriptLaw_eq_systemFactor_mul_environmentFactor`, `Derivation.lean:602` |
| `statDist_trLawFullyDefined_eq_sum` | `Derivation.lean:634` (the (★) identity) |
| `trLawFullyDefined_ratio_of_transcriptSystemFactor_ratio` | `Derivation.lean:212` `transcriptLaw_ratio_of_fixedQuery_ratio_of_good` |
| `h_coefficient_theorem` | `Derivation.lean:398` `adv_le_of_fixedQuery_ratio_of_good` |

The only presentational delta is how a *round* of `t` is addressed: the
reference states its conjuncts index-wise (`∀ k < t.length`, with `t.take k` and
`t[k]`); here they are stated prefix-wise (`∀ u x y, u ++ [(x,y)] <+: t`).  The
two are the same quantifier — each `k < t.length` is the unique decomposition
with `u = t.take k` — and the prefix form was chosen because it matches the
`snoc` shape of the landed `transcript` recurrence, so the inductions are
`List.reverseRecOn` rather than index arithmetic.  Nothing else differs, and no
node here is without a counterpart there.

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
  the thesis's two conjuncts (App. A.1, printed p. 88), each mentioning only
  one of the two parties; CR18 Lemma 3.2 names the corresponding factors.  `System.transcript_eq_iff` is the split itself: a run
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

/-! ### The thesis's two conjuncts

The transcript probability factors because the run condition `tr(s,e,n) = t` is
a *conjunction* of a condition on `e` alone and a condition on `s` alone — the
thesis's "`tr(s, ē)` is `t̂` if and only if `s(x̂ⁱ) = ŷᵢ` and `ē(ŷ^{i−1}) = x̂ᵢ`"
(App. A.1, printed p. 88).  The two definitions below are those conjuncts;
CR18 Lemma 3.2 is the same split read as a product of two *factors*, one per
party.  Each is phrased over the rounds of `t` — a round is a prefix of `t`
ending in one entry — so no index arithmetic enters the statements; the
reference repository states the same two conjuncts index-wise
(`RandomSystem.lean:750`), which is the same quantifier. -/

/-- **The thesis's system conjunct** (App. A.1, printed p. 88: `s(x̂ⁱ) = ŷᵢ`
for all `i ∈ [l]`); CR18 Lemma 3.2's system factor is its mass.  The
deterministic system `s` produces
exactly the answers recorded in `t`: at every round, `s⊥` maps the input
history of that round to the answer the round records.  `none` is a genuine
answer (a refusal), so this is a condition on `s⊥`, not on `s`, and it never
demands totality. -/
def TranscriptSystemEvent (s : DDS X Y) (t : List (X × Option Y)) : Prop :=
  ∀ u : List (X × Option Y), ∀ x : X, ∀ y : Option Y, u ++ [(x, y)] <+: t →
    output s⊥ (u↓ₓ ++ [x]) (by simp [fullyDefined, dom]) = y

/-- **The thesis's environment conjunct** (App. A.1, printed p. 88:
`ē(ŷ^{i−1}) = x̂ᵢ` for all `i ∈ [l]`), at horizon `n`.  The environment
`e` asks exactly the queries recorded in `t`, having seen exactly the answers
recorded before them, and its halting is on schedule for `n` moves: `t` is not
longer than `n`, and if it is shorter then `e` has stopped at `t`.

The horizon is an environment-side index — `PDS.trLawFullyDefined` is indexed
by the number of environment moves — so it belongs to this conjunct.  What
matters for the factorization is that nothing here mentions the system.

The halting clause is **not** a novelty of this tree: the reference repository
carries it on this same carrier as the `hlen` hypothesis of
`RandomSystem.lean:750` `transcript_eq_iff_of_consistent`, written as the
disjunction `|t| = n ∨ (|t| < n ∧ e t↓ᵧ = none)`. -/
def TranscriptEnvironmentEvent (e : DDE.Total Y X) (n : ℕ)
    (t : List (X × Option Y)) : Prop :=
  (∀ u : List (X × Option Y), ∀ x : X, ∀ y : Option Y, u ++ [(x, y)] <+: t →
      e u↓ᵧ = some x) ∧
    t.length ≤ n ∧ (t.length < n → e t↓ᵧ = none)

namespace DDE.Total

/-- A run of `n` environment moves records at most `n` rounds.
Reference-repository counterpart: `Lemma415.lean:113` `transcript_length_le`. -/
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

/-- Once the environment has stopped, the transcript no longer grows.
Reference-repository neighbourhood: `RandomSystem.lean:1270`
`transcript_stall_of_length_lt'` (the converse reading) and
`transcript_succ_stall`. -/
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

/-- A run of `n` moves satisfies the environment conjunct at horizon `n`.
This and the next theorem are the two halves of the reference repository's
`RandomSystem.lean:634` `transcript_consistent`. -/
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

/-- Reading the two conjuncts back: a transcript satisfying both is the run.
Reference-repository counterpart: `RandomSystem.lean:688`
`transcript_eq_of_consistent`. -/
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

/-- **The thesis's split** (App. A.1, printed p. 88, quoted at the head of this
file), read on this carrier.  A run of `n` environment moves produces the
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
/-- The environment factor — CR18 Lemma 3.2's `p^E_{X^k|Y^{k-1}}` — on this
carrier:
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

/-- The system factor: the thesis's `S({s | ∀ i ∈ [l] : s(x̂ⁱ) = ŷᵢ})`
(App. A.1, printed p. 88), CR18 Lemma 3.2's `p^S_{Y^k|X^k}` — the mass the law
`S` puts
on the deterministic systems that answer `t`.  It mentions no environment and
no horizon — that is the content of "the adversary factors out". -/
def transcriptSystemFactor (S : PDS X Y) (t : List (X × Option Y)) : ℝ :=
  S.mass (fun s => System.TranscriptSystemEvent s t)

theorem transcriptSystemFactor_nonneg {S : PDS X Y} (hS : S.NonNeg)
    (t : List (X × Option Y)) : 0 ≤ transcriptSystemFactor S t :=
  hS.mass_nonneg _

/-- **The factorization** — the thesis's App. A.1 identity (printed p. 88),
which CR18 Lemma 3.2 (printed p. 70) states for probabilistic environments with
the two factors named.  The transcript law of `S` against the
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

/-! ### The layer-2 kernel at an infinite carrier

The kernel this file's endpoints consume is
`Probability.statDist_le_probBad_add_of_ratio_on_good` — `hTechnique_ratio`
with `[Fintype A]` deleted, since the transcript space `List (X × Option Y)` is
infinite even for finite alphabets.  It now lives in
`Probability/StatisticalDistance.lean` beside `probBad` and the `[Fintype]`
form, which is its instance; the proposed relocation this file used to carry
has been applied. -/

namespace PDS

/-! ### The endpoint -/

/-- **The H-coefficient theorem** (the factorization composed with the layer-2
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

/-! ### `σ` at the empty transcript, and why a receipt must be length-indexed

The system conjunct is vacuous at `t = []`, so `σ(S, [])` is the whole weight of
`S`.  That single fact decides the shape any counting receipt may take, and it
is why the first version of the receipt below (constant `σ` on both sides) was
**degenerate**: it was true and axiom-clean, but its hypotheses were jointly
satisfiable only where its own `ε` was `0` or where they already forced
`δb ≥ ‖T‖`, in which case the conclusion follows from `statDist_le_weight`
alone and no counting is consumed.  Found by the T5 adversarial audit; the two
lemmas below record the obstruction and its repair so it cannot recur. -/

/-- `σ` at the empty transcript is the law's weight: no round has happened, so
the system conjunct constrains nothing. -/
theorem transcriptSystemFactor_nil (S : PDS X Y) :
    transcriptSystemFactor S ([] : List (X × Option Y)) = S.weight := by
  have hall : ∀ s : System.DDS X Y,
      System.TranscriptSystemEvent s ([] : List (X × Option Y)) := by
    intro s u x y hu
    exact absurd (List.eq_nil_of_prefix_nil hu) (by simp)
  rw [transcriptSystemFactor,
    Distribution.mass_congr S
      (P := fun s => System.TranscriptSystemEvent s ([] : List (X × Option Y)))
      (Q := fun _ => True) (fun s => iff_of_true (hall s) trivial),
    Distribution.mass_true]

/-- **Constant `σ`-hypotheses force the empty transcript to be bad.**  If a
would-be receipt pins `σ(S, ·)` and `σ(T, ·)` off `Bad` to two *constants*, then
— because `σ` at `[]` is the weight and the endpoint already demands
`‖S‖ = ‖T‖` — the two constants must agree wherever `[]` is good.  So as soon
as they differ (the uniform-permutation and uniform-function masses differ at
every `q ≥ 2`), `Bad []` is forced, and then `h_bad` at horizon `0` charges the
whole of `‖T‖` to `δb`, which alone implies the endpoint's conclusion.

This is the precise reason the receipt below indexes its two masses by
`t.length` instead. -/
theorem bad_nil_of_transcriptSystemFactor_const {S T : PDS X Y}
    {Bad : List (X × Option Y) → Prop} {cS cT : ℝ}
    (hw : S.weight = T.weight)
    (h_ideal : ∀ t, ¬ Bad t → transcriptSystemFactor T t = cT)
    (h_real : ∀ t, ¬ Bad t → transcriptSystemFactor S t = cS)
    (hne : cS ≠ cT) :
    Bad ([] : List (X × Option Y)) := by
  by_contra hgood
  refine hne ?_
  rw [← h_real [] hgood, ← h_ideal [] hgood, transcriptSystemFactor_nil,
    transcriptSystemFactor_nil, hw]

/-! ### Receipt: the counting layer feeds `ε`

Not an application — no concrete `S`, `T` or alphabet appears.  The receipt
records the *shape* in which `Probability/Counting.lean` is consumed: the
counting layer produces exactly a pointwise inequality between two per-round
masses, which is what the ratio hypothesis of the endpoint asks for, with the
birthday defect landing in `ε`.

On a variable-length carrier those masses are functions of `t.length`, so the
hypotheses are indexed by it and the query bound enters as "every good
transcript is short" (`h_len`).  `Probability.Counting.switching_ratio_le` then
fires at each good length `k = |t| ≤ q`, and monotonicity of `k(k−1)` in `k`
pulls every one of those defects under the single `ε = q(q−1)/2N`. -/

/-- **The switching ratio slots into `ε`.**  Off the bad set, let the ideal
system factor be the uniform-permutation mass `(N−|t|)!/N!` and the real one the
uniform-function mass `1/N^{|t|}`, with every good transcript of length at most
`q`.  Then `Probability.Counting.switching_ratio_le` discharges the endpoint's
ratio hypothesis with `ε = q(q−1)/2N`, and the technique returns

  `Adv⊥(S, T) ≤ δ_b + q(q−1)/2N`.

The two mass hypotheses are exactly what a counting argument delivers, and they
are **consistent at `[]`** for probability laws
(`transcriptSystemFactor_nil_switching_ratio`), so nothing here forces the
degenerate regime of `bad_nil_of_transcriptSystemFactor_const`.  Nothing else
about the systems is used. -/
theorem h_coefficient_theorem_switching_ratio {S T : PDS X Y}
    {Bad : List (X × Option Y) → Prop} {δb : ℝ≥0} {N q : ℕ}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight) (hT1 : T.weight ≤ 1)
    (hqN : q ≤ N) (hN : 0 < N)
    (h_eps : ((q * (q - 1) : ℕ) : ℝ≥0) / ((2 * N : ℕ) : ℝ≥0) ≤ 1)
    (h_len : ∀ t, ¬ Bad t → t.length ≤ q)
    (h_ideal : ∀ t, ¬ Bad t → transcriptSystemFactor T t =
      (((N - t.length).factorial : ℝ) / (N.factorial : ℝ)))
    (h_real : ∀ t, ¬ Bad t → transcriptSystemFactor S t =
      1 / (N : ℝ) ^ t.length)
    (h_bad : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      probBad (trLawFullyDefined e n T) Bad ≤ δb) :
    advFullyDefined S T ≤
      (δb + ((q * (q - 1) : ℕ) : ℝ≥0) / ((2 * N : ℕ) : ℝ≥0) : ℝ≥0) := by
  refine h_coefficient_theorem hS hT hw hT1 (fun t ht => ?_) h_bad
  rw [h_ideal t ht, h_real t ht]
  exact Probability.Counting.switching_ratio_le_of_query_bound
    (h_len t ht) hqN hN h_eps

/-- **Non-triviality of the receipt.**  At the empty transcript the receipt's
two length-indexed hypotheses read `‖T‖ = 1` and `‖S‖ = 1` — they are satisfied
by any pair of probability laws, so `[]` may be good and the receipt does not
collapse into `bad_nil_of_transcriptSystemFactor_const`'s degenerate regime.
(The constant-`σ` version this replaces could not clear the same test: it
demanded `(N−q)!/N! = 1/N^q`, false for every `q ≥ 2`.) -/
theorem transcriptSystemFactor_nil_switching_ratio {S T : PDS X Y} {N : ℕ}
    (hS1 : S.weight = 1) (hT1 : T.weight = 1) :
    transcriptSystemFactor T ([] : List (X × Option Y)) =
        (((N - ([] : List (X × Option Y)).length).factorial : ℝ) /
          (N.factorial : ℝ)) ∧
      transcriptSystemFactor S ([] : List (X × Option Y)) =
        1 / (N : ℝ) ^ ([] : List (X × Option Y)).length := by
  have hfac : (N.factorial : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  refine ⟨?_, ?_⟩
  · rw [transcriptSystemFactor_nil, hT1]
    simp only [List.length_nil, Nat.sub_zero]
    exact (div_self hfac).symm
  · rw [transcriptSystemFactor_nil, hS1]
    simp

end PDS

end RandomSystems

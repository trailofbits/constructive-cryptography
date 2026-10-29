import RandomSystems.Distance.Decision
import Probability.Coupling

/-!
# Couplings of random systems

The transcript of a deterministic system with a strategy within `n` rounds is the sequence of
query–reply pairs they exchange. For a strategy compatible with the random system of a PDS, the
transcript law of that random system is the transformation of the PDS by the transcript map. A
coupling of two PDSs is a joint distribution of the two; it bounds the statistical distance of
the transcript laws by the probability that the two sampled systems give different transcripts,
and the transcript distance of the two random systems by the probability that the two sampled
systems differ. Sources: Lanzenberger–Maurer, Definitions 4 and 7 (printed pp. 10, 12),
footnote 9 (printed p. 14), Definition 11 and Theorem 2 (printed p. 15).

## Main definitions

* `System.tr s σ n`: the transcript of the deterministic system `s` with `σ` within `n` rounds

## Main results

* `System.tr_eq_iff`: when `s` answers the queries of `σ`, its transcript is the only transcript
  of `σ` within `n` rounds that `s` replies
* `PDS.sLaw_behavior_eq_fTransform`: the transcript law of the random system of a PDS is the
  transformation of the PDS by the transcript map
* `PDS.statDist_sLaw_behavior_le_of_isCoupling`: under a coupling, the transcript laws are at
  statistical distance at most the probability that the transcripts differ
* `PDS.transcriptDistance_behavior_le_of_isCoupling`: under a coupling, the transcript distance is
  at most the probability that the systems differ
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {A B : Type}

/-! ## The transcript of a deterministic system -/

namespace System

open scoped Classical in
/-- **The transcript** of the deterministic system `s` with the strategy `σ` within `n` rounds
(Lanzenberger–Maurer, Definition 7, printed p. 12): "the sequence of pairs (x₁, y₁), (x₂, y₂),
…, (x_l, y_l), defined for i ≥ 1 by xᵢ = e(y₁, …, yᵢ₋₁) and yᵢ = s(x₁, …, xᵢ)", and "If
e(y₁, …, yᵢ₋₁) is undefined (the environment stops), the transcript ends and has length
l = i − 1." It also ends after `n` rounds, and when `s` does not answer the query, which a
compatible strategy never asks. -/
noncomputable def tr (s : System A B) (σ : List B →. A) : ℕ → List (A × B)
  | 0 => []
  | n + 1 =>
    -- The transcript `h` of the first `n` rounds, extended by the query `x` of `σ` and the
    -- reply of `s` to it, if both are defined.
    let h := tr s σ n
    if hx : (σ (h.map Prod.snd)).Dom then
      let x := (σ (h.map Prod.snd)).get hx
      if hy : (s (h.map Prod.fst ++ [x])).Dom then h ++ [(x, (s (h.map Prod.fst ++ [x])).get hy)]
      else h
    else h

variable {s : System A B} {σ : List B →. A}

/-- The queries of the transcript follow `σ`. -/
lemma followsStrategy_tr (n : ℕ) : FollowsStrategy σ (s.tr σ n) := by
  induction n with
  | zero => exact FollowsStrategy.nil
  | succ n ih =>
    rw [tr]
    dsimp only
    split_ifs with hx hy
    -- A new round: its query is the strategy's query after the replies so far.
    · exact FollowsStrategy.snoc_iff.mpr ⟨ih, Part.get_mem hx⟩
    all_goals exact ih

/-- The system gives the replies of its transcript. -/
lemma replies_tr (n : ℕ) :
    Replies s ((s.tr σ n).map Prod.fst) ((s.tr σ n).map Prod.snd) := by
  induction n with
  | zero => exact replies_nil s
  | succ n ih =>
    rw [tr]
    dsimp only
    split_ifs with hx hy
    -- A new round: its reply is the system's answer to the queries so far.
    · simp only [List.map_append, List.map_singleton]
      exact replies_snoc.mpr ⟨ih, Part.get_eq_iff_eq_some.mp rfl⟩
    all_goals exact ih

/-- **The transcript is complete** within `n` rounds when `s` answers every query `σ` asks after
it: it has `n` rounds, or the strategy has stopped. -/
lemma good_tr {n : ℕ}
    (hs : ∀ x ∈ σ ((s.tr σ n).map Prod.snd), (s ((s.tr σ n).map Prod.fst ++ [x])).Dom) :
    Good σ n (s.tr σ n) := by
  -- By induction: the transcript has `n` rounds, or it ended early and `s` does not answer
  -- the next query of `σ` (vacuously so when `σ` has stopped).
  have key : ∀ m, (s.tr σ m).length = m ∨ ((s.tr σ m).length < m ∧
      ∀ x ∈ σ ((s.tr σ m).map Prod.snd), ¬ (s ((s.tr σ m).map Prod.fst ++ [x])).Dom) := by
    intro m
    induction m with
    | zero => exact Or.inl rfl
    | succ m ih =>
      rw [tr]
      dsimp only
      split_ifs with hx hy
      -- A new round: the transcript did not end early, since `s` answered.
      · refine Or.inl ?_
        rcases ih with hl | ⟨-, hn⟩
        · simp [hl]
        · exact absurd hy (hn _ (Part.get_mem hx))
      -- `s` does not answer the query `x` of `σ`, its only query.
      · refine Or.inr ⟨by rcases ih with hl | ⟨hl, -⟩ <;> omega, fun x hx' hd => hy ?_⟩
        rwa [Part.get_eq_of_mem hx' hx]
      -- `σ` has stopped.
      · exact Or.inr ⟨by rcases ih with hl | ⟨hl, -⟩ <;> omega,
          fun x hx' => absurd (Part.dom_iff_mem.mpr ⟨x, hx'⟩) hx⟩
  refine ⟨followsStrategy_tr n, ?_⟩
  rcases key n with hl | ⟨hl, hn⟩
  · exact Or.inl hl
  -- Ended early: as `s` answers every query of `σ`, the strategy must have stopped.
  · exact Or.inr ⟨hl, fun hx => hn _ (Part.get_mem hx) (hs _ (Part.get_mem hx))⟩

/-- **The transcript is the only complete transcript the system replies**: when `s` answers
every query `σ` asks after its transcript, a transcript of `σ` complete within `n` rounds is
replied by `s` exactly when it is the transcript of `s`. -/
lemma tr_eq_iff {n : ℕ}
    (hs : ∀ x ∈ σ ((s.tr σ n).map Prod.snd), (s ((s.tr σ n).map Prod.fst ++ [x])).Dom)
    (h : List (A × B)) :
    s.tr σ n = h ↔ Good σ n h ∧ Replies s (h.map Prod.fst) (h.map Prod.snd) := by
  refine ⟨fun he => he ▸ ⟨good_tr hs, replies_tr n⟩, fun ⟨hg, hr⟩ => ?_⟩
  -- Both `h` and the transcript of `s` are interaction transcripts of `s` with `σ`.
  have hg' := good_tr hs
  have tt := FollowsStrategy.transcript hg'.1 (replies_tr (s := s) n)
  have th := FollowsStrategy.transcript hg.1 hr
  -- Their queries and replies agree: both have `n` rounds, or both end when `σ` stops; one
  -- with `n` rounds and one ending earlier is impossible, since a transcript ending when `σ`
  -- stops is at least as long as any other.
  have he : (s.tr σ n).map Prod.fst = h.map Prod.fst ∧
      (s.tr σ n).map Prod.snd = h.map Prod.snd := by
    rcases hg'.2 with hl | ⟨hl, hd⟩ <;> rcases hg.2 with hl' | ⟨hl', hd'⟩
    · exact tt.eq_of_length_eq th (by simp [hl, hl'])
    · have := th.length_le_of_stopped hd' tt
      simp only [List.length_map] at this
      omega
    · have := tt.length_le_of_stopped hd th
      simp only [List.length_map] at this
      omega
    · exact tt.eq_of_stopped th hd hd'
  -- A list of pairs is determined by its queries and its replies.
  exact (List.zip_of_prod he.1 he.2).trans (List.zip_of_prod rfl rfl).symm

end System

/-! ## The transcript law of a PDS -/

namespace PDS

variable [Fintype A] [Fintype B] {D : Domain A B}

/-- **The transcript law of the random system of a PDS is the transformation of the PDS by the
transcript** (Lanzenberger–Maurer, footnote 9, printed p. 14): "tr(S, e) denotes the
tr(·, e)-transformation of the distribution S (see Definition 4)". For a strategy `σ`
compatible with the random system of `P`, the transcript law within `n` rounds is the
pushforward of `P` by the transcript of the sampled system with `σ` within `n` rounds. -/
theorem sLaw_behavior_eq_fTransform (P : PDS A B D) (hP : P.isProbDist) {σ : List B →. A}
    (hC : (PDS.behavior P hP).Compatible σ) (n : ℕ) :
    (PDS.behavior P hP).sLaw σ n = Distribution.fTransform (fun s => s.1.tr σ n) P := by
  -- 1. A sampled system answers every query of `σ` after its transcript: the transcript has
  --    probability at least the weight of the sample, so the compatible `σ` asks an admitted
  --    query, and the sample has the domain `D`.
  have hans : ∀ s ∈ P.support, ∀ x ∈ σ ((s.1.tr σ n).map Prod.snd),
      (s.1 ((s.1.tr σ n).map Prod.fst ++ [x])).Dom := by
    intro s hs x hx
    have hpos : PDS.behavior P hP (s.1.tr σ n) ≠ 0 := by
      rw [PDS.behavior_mass]
      refine ne_of_gt (lt_of_lt_of_le
        (lt_of_le_of_ne (hP.1 s) (Ne.symm (Finsupp.mem_support_iff.mp hs))) ?_)
      exact Distribution.apply_le_mass hP.1 (P := fun t => Replies t.1 _ _)
        (System.replies_tr n)
    exact (s.2.2 _ x (System.replies_tr n)).mpr (hC _ x (System.followsStrategy_tr n) hpos hx)
  -- 2. Compare the two laws at each transcript `h`: the left side is the mass of the samples
  --    replying `h` if `h` is complete for `σ` within `n` rounds, and zero otherwise; the right
  --    side is the mass of the samples whose transcript is `h`.
  ext h
  rw [RandomSystem.sLaw_apply, PDS.behavior_mass, Distribution.fTransform_apply_eq_mass]
  by_cases hg : Good σ n h
  -- A complete `h`: the samples replying `h` are those whose transcript is `h`.
  · rw [if_pos hg]
    exact Distribution.mass_congr_of_support P fun s hs =>
      ⟨fun hr => (System.tr_eq_iff (hans s hs) h).mpr ⟨hg, hr⟩,
        fun ht => ((System.tr_eq_iff (hans s hs) h).mp ht).2⟩
  -- An incomplete `h` is the transcript of no sample.
  · rw [if_neg hg]
    refine ((Distribution.mass_congr_of_support P (Q := fun _ => False) fun s hs =>
      ⟨fun ht => hg ((System.tr_eq_iff (hans s hs) h).mp ht).1, False.elim⟩).trans
        (Distribution.mass_eq_zero_of_forall_not P fun _ hf => hf)).symm

/-! ## Couplings -/

/-- **A coupling bounds the distance of the transcript laws.** If `J` is a joint distribution
of the PDSs `P` and `Q`, then for a strategy `σ` compatible with both random systems, their
transcript laws within `n` rounds are at statistical distance at most the probability under `J`
that the two sampled systems give different transcripts:

```
            σ ⇄ s   gives  tr(s, σ, n)     s ~ P
  (s, t) ~ J
            σ ⇄ t   gives  tr(t, σ, n)     t ~ Q
```

Both transcript laws are transformations of `J` (`sLaw_behavior_eq_fTransform`), which agree
where the two transcripts agree. -/
lemma statDist_sLaw_behavior_le_of_isCoupling {P Q : PDS A B D} (hP : P.isProbDist)
    (hQ : Q.isProbDist)
    {J : Distribution ({s : System A B // IsDDS s ∧ HasDomain D s} ×
      {s : System A B // IsDDS s ∧ HasDomain D s})}
    (hJ : Distribution.IsCoupling J P Q) (hJ0 : J.NonNeg) {σ : List B →. A}
    (hCP : (PDS.behavior P hP).Compatible σ) (hCQ : (PDS.behavior Q hQ).Compatible σ)
    (n : ℕ) :
    statDist ((PDS.behavior P hP).sLaw σ n) ((PDS.behavior Q hQ).sLaw σ n) ≤
      J.mass fun st => st.1.1.tr σ n ≠ st.2.1.tr σ n := by
  -- The transcript law of `P` is the transformation of `J` by the transcript of the first
  -- system, since `P` is the first marginal of `J`; the same for `Q` and the second.
  rw [sLaw_behavior_eq_fTransform P hP hCP, sLaw_behavior_eq_fTransform Q hQ hCQ, ← hJ.1,
    ← hJ.2, Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  -- Two transformations of one law that agree off an event are within its probability.
  exact statDist_fTransform_le_mass_of_eq_off hJ0 _ _ _ fun _ _ h => not_not.mp h

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- **A coupling bounds the transcript distance** (the inequality of Lanzenberger–Maurer,
Theorem 2, printed p. 15, for an arbitrary coupling): "For any two random systems S and T there
exist PDS S ∈ S and T ∈ T with a joint distribution (or coupling) such that
Adv(S, T) = Pr(S ≠ T)". If `J` is a joint distribution of the PDSs `P` and `Q` and the
probability under `J` that the two sampled systems differ is at most `b`, the transcript
distance of the random systems of `P` and `Q` is at most `b`. The paper obtains Theorem 2 as "an
immediate consequence of Theorem 1 and the classical Coupling Lemma (Lemma 4)"; here, under
every environment the transcript laws are within the probability that the transcripts differ
(`statDist_sLaw_behavior_le_of_isCoupling`), and equal systems give equal transcripts. -/
theorem transcriptDistance_behavior_le_of_isCoupling {P Q : PDS (Σ i, X i) (Σ i, Y i) 𝒟}
    (hP : P.isProbDist) (hQ : Q.isProbDist)
    (hPR : (PDS.behavior P hP).RepliesAtQueriedInterface)
    (hQR : (PDS.behavior Q hQ).RepliesAtQueriedInterface)
    {J : Distribution ({s : System (Σ i, X i) (Σ i, Y i) // IsDDS s ∧ HasDomain 𝒟 s} ×
      {s : System (Σ i, X i) (Σ i, Y i) // IsDDS s ∧ HasDomain 𝒟 s})}
    (hJ : Distribution.IsCoupling J P Q) (hJ0 : J.NonNeg) {b : ℝ≥0}
    (hb : Distribution.offDiagonalMass J ≤ b) :
    (PDS.behavior P hP).transcriptDistance (PDS.behavior Q hQ) ≤ b := by
  -- It suffices to bound the transcript laws under each query-bounded environment `E`
  -- compatible with the domain; such an `E` is compatible with both random systems.
  refine RandomSystem.transcriptDistance_le fun E n _ hc => ?_
  calc statDist ((PDS.behavior P hP).sLaw E.1 n) ((PDS.behavior Q hQ).sLaw E.1 n)
      ≤ J.mass fun st => st.1.1.tr E.1 n ≠ st.2.1.tr E.1 n :=
        statDist_sLaw_behavior_le_of_isCoupling hP hQ hJ hJ0 (hc _ hPR) (hc _ hQR) n
    -- Different transcripts come from different systems.
    _ ≤ Distribution.offDiagonalMass J :=
        Distribution.mass_mono hJ0 fun st hne he => hne (by rw [he])
    _ ≤ b := hb

end PDS

end SystemAlgebra

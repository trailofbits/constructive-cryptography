/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Absorb
import Probability.Coupling

/-!
# System equivalence and the class distance

Lanzenberger presents the distance between two probabilistic discrete systems
**twice**, and both presentations are first class here.

* `PDS.advFullyDefined` (Ruling R4, `Environment.lean`) is the *interactive*
  presentation: a supremum over environments of the statistical distance of the
  transcript laws.  It carries the metric instance on `Phi`.
* `PDS.classDistance` — Lanzenberger **Definition 2.28** — is the *static*
  presentation: an infimum, over pairs of honest equivalent representatives
  (Ruling R9), of the statistical distance of the system laws themselves.

The two are joined by `PDS.equivalent` — Lanzenberger **Definition 2.17** — the
relation that says two systems are indistinguishable outright, and by the
crossing lemmas at the end of this file.  The intended workflow is: prove a
bound in whichever presentation is cheaper (the static one, where a coupling of
*any* convenient pair of representatives is enough), and consume it as `Adv⊥`,
which is what endpoint statements read in.

The file also carries the **coding map** between Lanzenberger's own advantage
(`PDS.Adv`, Definition 2.26 — compatible, stopping environments, stopped
transcript) and Ruling R4's `PDS.advFullyDefined`.  The two index sets are
different and neither contains the other, so the identification is a theorem in
both directions; the machinery that makes it work — the deterministic
factorization behind Lemma 2.18 and the rejection-pruning replay machine — is
the bulk of this file.

## Main definitions

* `PDS.equivalent S T` — Definition 2.17, over the CR18 total presentation.
* `PDS.classDistance S T` — Definition 2.28, `Δ(S, T)`.
* `System.DDE.Total.NonAdaptive`, `System.DDE.Total.playQueries` — Lanzenberger
  fn. 6's environment class and its witness.
* `System.prunedEnv` — the rejection-pruning replay machine, read as a
  Definition-2.11 environment.

## Main results

* `PDS.equivalent_iff_nonAdaptive` — Lanzenberger **Lemma 2.18**: non-adaptive
  environments already decide equivalence.
* `PDS.equivalent_ofTyped_iff` — equivalence transfers through the typed
  inclusion, in both directions.
* `PDS.advFullyDefined_congr`, `PDS.classDistance_congr` — both distances
  transport along equivalence, in both slots.
* `PDS.advFullyDefined_le_classDistance` — `Adv⊥ ≤ Δ`, unconditional.
* `PDS.classDistance_le_offDiagonalMass`,
  `PDS.advFullyDefined_le_offDiagonalMass_of_equivalent` — a coupling of any
  equivalent pair bounds both distances.
* `PDS.Adv_le_advFullyDefined` (unconditional) and
  `PDS.advFullyDefined_eq_Adv_of_dom_eq` (on the shared-domain slice) — the
  coding map.
* `PDS.AdvD_eq_Adv`, `PDS.advFullyDefined_eq_AdvD` — the same coding map at
  Definition 2.26 indexed by the *domain* (`PDS.AdvD`, `Environment.lean`), and
  `PDS.AdvD_congr` — that advantage is a class invariant, with no hypothesis.

## Not to be confused with `PDS.Equivalent`

`PDS.Equivalent` (`ProbabilisticSystem.lean`, capital `E`) is Jost's relation:
equality of the acceptance mass under every strict deterministic distinguisher.
`PDS.equivalent` here is Lanzenberger's Definition 2.17 over the CR18 total
presentation: equality of the *transcript laws* in every total environment, at
every length.  They are relations of the same genre at two presentations of the
interaction, and relating them is the same work as relating `maxEDist` to
`Adv⊥` — not done here, and not needed by anything below.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Lanzenberger Lemma 2.18: the deterministic factorization

Lemma 2.18 says that equivalence is already decided by the environments whose
queries are fixed in advance.  Its content is a *deterministic* fact about one
system at a time, and that is where it is proved here: a transcript prefix `t`
is produced by `s` in `e` after `n` rounds exactly when two independent
conditions hold —

* an **environment-side** condition, that `e` replays the queries of `t` and
  then either fills the round budget or stops (`transcript_consistent`'s first
  component), which does not mention `s` at all; and
* a **system-side** condition, that each entry's answer is the completion's
  answer to that entry's query after the queries before it, which does not
  mention `e` at all.

`transcript_eq_iff_of_consistent` is that factorization.  Once the
environment-side condition holds, the fiber `{s | tr(s, e, n) = t}` is cut out
by the system-side condition alone, and the *non-adaptive* environment
`playQueries t↓ₓ` — play the queries of `t` by position, then stop — cuts out
the same fiber.  So a law that is pinned on every non-adaptive environment is
pinned on every environment. -/

namespace System.DDE.Total

open System

/-- Lanzenberger fn. 6 (the footnote Lemma 2.18 quantifies over): an
environment is **non-adaptive** when the query it makes at step `k` depends
only on `k` — the answers it has received so far do not influence what it asks
next, so its query list is fixed before the interaction starts. -/
def NonAdaptive (e : DDE.Total Y X) : Prop :=
  ∀ l l' : List (Option Y), l.length = l'.length → e l = e l'

/-- The **fixed-query-list environment**: ask the queries of `queries` in
order, by position, and stop when they run out.  This is the witness class of
Lanzenberger fn. 6, and the only non-adaptive environment Lemma 2.18 needs. -/
def playQueries (queries : List X) : DDE.Total Y X :=
  fun l => queries[l.length]?

theorem nonAdaptive_playQueries (queries : List X) :
    NonAdaptive (playQueries (Y := Y) queries) := by
  intro l l' h
  simp only [playQueries, h]

/-- **The factorization, forward half**: the length-`n` transcript satisfies
both consistency conditions.  The environment-side one says each entry replays
`e` on the outputs before it, and that the interaction either used its whole
budget or stopped; the system-side one says each answer is `s⊥`'s answer to
that entry's query after the queries before it. -/
theorem transcript_consistent (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ) :
    ((∀ k, (hk : k < (transcript s e n).length) →
        e ((transcript s e n).take k)↓ᵧ = some (transcript s e n)[k].1) ∧
      ((transcript s e n).length = n ∨
        ((transcript s e n).length < n ∧ e (transcript s e n)↓ᵧ = none))) ∧
    (∀ k, (hk : k < (transcript s e n).length) →
      answer s ((transcript s e n).take k)↓ₓ (transcript s e n)[k].1 =
        (transcript s e n)[k].2) := by
  induction n with
  | zero =>
      refine ⟨⟨fun k hk => absurd hk ?_, Or.inl rfl⟩, fun k hk => absurd hk ?_⟩ <;>
        · show ¬ k < (([] : List (X × Option Y))).length
          simp
  | succ n ih =>
      obtain ⟨⟨hq, hlen⟩, hs⟩ := ih
      rcases he : e (transcript s e n)↓ᵧ with _ | x
      · rw [transcript_succ_of_stop s e he]
        exact ⟨⟨hq, Or.inr ⟨by rcases hlen with h | ⟨h, -⟩ <;> omega, he⟩⟩, hs⟩
      · have hln : (transcript s e n).length = n := by
          rcases hlen with h | ⟨-, hstall⟩
          · exact h
          · rw [hstall] at he; cases he
        rw [transcript_succ_of_query s e he]
        refine ⟨⟨?_, Or.inl (by simp [hln])⟩, ?_⟩
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (transcript s e n).length with hk' | hk'
          · rw [List.take_append_of_le_length (le_of_lt hk'),
              List.getElem_append_left hk']
            exact hq k hk'
          · have hkeq : k = (transcript s e n).length := by omega
            subst hkeq
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            simpa using he
        · intro k hk
          rw [List.length_append, List.length_singleton] at hk
          rcases Nat.lt_or_ge k (transcript s e n).length with hk' | hk'
          · rw [List.take_append_of_le_length (le_of_lt hk'),
              List.getElem_append_left hk']
            exact hs k hk'
          · have hkeq : k = (transcript s e n).length := by omega
            subst hkeq
            rw [List.take_append_of_le_length le_rfl, List.take_length,
              List.getElem_append_right le_rfl]
            simp

/-- **The factorization, backward half**: the two consistency conditions
reconstruct the transcript.  Nothing here is about probability — this is the
deterministic content of Lemma 2.18. -/
theorem transcript_eq_of_consistent (s : DDS X Y) (e : DDE.Total Y X) :
    ∀ (n : ℕ) (t : List (X × Option Y)),
      (∀ k, (hk : k < t.length) → e (t.take k)↓ᵧ = some t[k].1) →
      (t.length = n ∨ (t.length < n ∧ e t↓ᵧ = none)) →
      (∀ k, (hk : k < t.length) → answer s (t.take k)↓ₓ t[k].1 = t[k].2) →
      transcript s e n = t := by
  intro n
  induction n with
  | zero =>
      intro t _ hlen _
      rcases hlen with h | ⟨h, -⟩
      · rw [List.eq_nil_of_length_eq_zero h]
        rfl
      · omega
  | succ n ih =>
      intro t hq hlen hs
      rcases hlen with hl | ⟨hl, hstall⟩
      · have hnlt : n < t.length := by omega
        have h1 : transcript s e n = t.take n := by
          refine ih (t.take n) ?_
            (Or.inl (by rw [List.length_take]; omega)) ?_
          · intro k hk
            rw [List.length_take] at hk
            have hk' : k < t.length := by omega
            rw [List.take_take, min_eq_left (by omega : k ≤ n),
              List.getElem_take]
            exact hq k hk'
          · intro k hk
            rw [List.length_take] at hk
            have hk' : k < t.length := by omega
            rw [List.take_take, min_eq_left (by omega : k ≤ n),
              List.getElem_take]
            exact hs k hk'
        have hfire : e (transcript s e n)↓ᵧ = some t[n].1 := by
          rw [h1]
          exact hq n hnlt
        rw [transcript_succ_of_query s e hfire, h1, hs n hnlt]
        conv_rhs => rw [← List.take_length (l := t), hl]
        rw [List.take_add_one, List.getElem?_eq_getElem hnlt]
        rfl
      · have h1 : transcript s e n = t := by
          refine ih t hq ?_ hs
          rcases Nat.lt_or_ge t.length n with h | h
          · exact Or.inr ⟨h, hstall⟩
          · exact Or.inl (by omega)
        rw [transcript_succ_of_stop s e (by rw [h1]; exact hstall), h1]

/-- **The factorization**: at an environment-consistent prefix value, whether
the transcript equals it is a condition on the *system alone*.  This is the
lemma that lets one environment be exchanged for another — in particular for
the non-adaptive `playQueries`, which is environment-consistent for every
prefix value at its own length. -/
theorem transcript_eq_iff_of_consistent {e : DDE.Total Y X} {n : ℕ}
    {t : List (X × Option Y)}
    (hq : ∀ k, (hk : k < t.length) → e (t.take k)↓ᵧ = some t[k].1)
    (hlen : t.length = n ∨ (t.length < n ∧ e t↓ᵧ = none))
    (s : DDS X Y) :
    transcript s e n = t ↔
      ∀ k, (hk : k < t.length) → answer s (t.take k)↓ₓ t[k].1 = t[k].2 := by
  constructor
  · rintro rfl
    exact (transcript_consistent s e n).2
  · exact transcript_eq_of_consistent s e n t hq hlen

/-- Every prefix value is environment-consistent for its own fixed-query-list
environment, at its own length: `playQueries t↓ₓ` asks exactly the queries of
`t`, in order. -/
theorem consistent_playQueries (t : List (X × Option Y)) :
    ∀ k, (hk : k < t.length) →
      playQueries (Y := Y) t↓ₓ (t.take k)↓ᵧ = some t[k].1 := by
  intro k hk
  have hlen : ((t.take k)↓ᵧ).length = k := by
    simp only [transcriptOutputs, List.length_map, List.length_take]
    omega
  have hk' : k < (t↓ₓ).length := by
    simpa [transcriptInputs] using hk
  simp only [playQueries, hlen, List.getElem?_eq_getElem hk']
  simp [transcriptInputs]

end System.DDE.Total

/-! ## Lanzenberger Definition 2.26 and Ruling R4: reading one interaction as
the other

`PDS.Adv` (Definition 2.26 verbatim) and `PDS.advFullyDefined` (Ruling R4) are
two indexings of the same interaction, and the material below is the bookkeeping
that lets a run of one be read as a run of the other.  Nothing here is
probabilistic: it is the deterministic dictionary — where the length-indexed
run of a total environment stands still, and where the stopped run of a
compatible partial environment has already stabilized. -/

namespace System

/-- The stopped transcript, read at **any** stage the interaction has already
stabilized at.  `tr` is defined at the first such stage (`Nat.find`); this says
the value does not depend on that choice, which is what lets a *uniform* stage
be chosen for a whole finite support. -/
theorem tr_get_eq_trN {e : DDE Y X} {s : DDS X Y} (h : Stops e s) {N : ℕ}
    (hN : trN e s (N + 1) = trN e s N) : (tr e s).get h = trN e s N := by
  classical
  rw [tr_get]
  exact (trN_eq_of_le (Nat.find_spec h) N (Nat.find_le hN)).symm

/-- A round of the length-indexed interaction either appends one entry or
stands still.  Both `trN`'s length bound and its stalling criterion come from
this dichotomy. -/
theorem trStep_eq_or_concat (e : DDE Y X) (s : DDS X Y) (t : Transcript X Y) :
    trStep e s t = t ∨ ∃ p, trStep e s t = t ++ [p] := by
  rw [trStep]
  by_cases hx : (t.map Prod.snd) ∈ e.1.Dom
  · rw [dif_pos hx]
    by_cases hy : (t.map Prod.fst ++ [(e.1 (t.map Prod.snd)).get hx]) ∈ dom s
    · exact Or.inr ⟨_, dif_pos hy⟩
    · exact Or.inl (dif_neg hy)
  · exact Or.inl (dif_neg hx)

theorem trN_length_le (e : DDE Y X) (s : DDS X Y) (n : ℕ) :
    (trN e s n).length ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      show (trStep e s (trN e s n)).length ≤ n + 1
      rcases trStep_eq_or_concat e s (trN e s n) with h | ⟨p, h⟩ <;> rw [h]
      · exact Nat.le_succ_of_le ih
      · simpa using Nat.succ_le_succ ih

/-- A run that has not used its whole budget has stalled — and, by
`trN_succ_eq_iff_of_compatible`, stalled because the environment stopped. -/
theorem trN_stall_of_length_lt (e : DDE Y X) (s : DDS X Y) :
    ∀ {n : ℕ}, (trN e s n).length < n → trN e s (n + 1) = trN e s n := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by simp)
  | succ n ih =>
      intro h
      rcases trStep_eq_or_concat e s (trN e s n) with hstep | ⟨p, hstep⟩
      · have hfix : trN e s (n + 1) = trN e s n := hstep
        show trStep e s (trN e s (n + 1)) = trN e s (n + 1)
        rw [hfix]
        exact hstep
      · exfalso
        have hlen : (trN e s (n + 1)).length = (trN e s n).length + 1 := by
          show (trStep e s (trN e s n)).length = _
          rw [hstep]
          simp
        have hlt : (trN e s n).length < n := by omega
        have := ih hlt
        rw [show trN e s (n + 1) = trStep e s (trN e s n) from rfl, hstep] at this
        simpa using congrArg List.length this

theorem trN_succ_of_stop {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (h : ((trN e s n).map Prod.snd) ∉ e.1.Dom) : trN e s (n + 1) = trN e s n := by
  show trStep e s (trN e s n) = trN e s n
  rw [trStep, dif_neg h]

theorem trN_succ_of_query {e : DDE Y X} {s : DDS X Y} {n : ℕ}
    (hdom : ((trN e s n).map Prod.snd) ∈ e.1.Dom)
    (hy : (trN e s n).map Prod.fst ++
      [(e.1 ((trN e s n).map Prod.snd)).get hdom] ∈ dom s) :
    trN e s (n + 1) = trN e s n ++
      [((e.1 ((trN e s n).map Prod.snd)).get hdom,
        output s ((trN e s n).map Prod.fst ++
          [(e.1 ((trN e s n).map Prod.snd)).get hdom]) hy)] := by
  show trStep e s (trN e s n) = _
  rw [trStep, dif_pos hdom, dif_pos hy]

/-! ### Halting environments stop, against everything

`Stops` is a property of a *pair*; `DDE.Halts` is a property of the environment
alone (Definition 2.12's stopping clause re-cut off the support, see
`Environment.lean`).  The two lemmas below are the implication, and they are
where the re-cut earns its keep: a halting environment stops against every
deterministic system whatsoever, at **one** stage `N` fixed before the system is
seen.  That uniformity is what lets the stopped transcript be read as a
length-`N` transcript of the total presentation. -/

/-- A halting environment's interaction has stabilized by its own round bound:
either the run already stalled — and a short run has stalled — or the
environment has seen `N` answers and asks nothing more. -/
theorem trN_succ_eq_of_halts_bound {e : DDE Y X} {N : ℕ}
    (hN : ∀ l : List Y, N ≤ l.length → l ∉ e.1.Dom) (s : DDS X Y) :
    trN e s (N + 1) = trN e s N := by
  rcases Nat.lt_or_ge (trN e s N).length N with hlt | hge
  · exact trN_stall_of_length_lt e s hlt
  · exact trN_succ_of_stop (hN _ (by simpa using hge))

/-- A halting environment stops against **every** deterministic system: the
round bound is a bound on the interaction, whatever the system answers. -/
theorem stops_of_halts {e : DDE Y X} (h : DDE.Halts e) (s : DDS X Y) :
    Stops e s := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, trN_succ_eq_of_halts_bound hN s⟩

/-! ### The completed transcript's answered part

`answeredEntries` (Definition 3.7's transcript with the `⊥` rounds discarded)
is the bridge between the two presentations: it is a `List (X × Y)`, which is
exactly a Definition 2.12 transcript.  The two append equations below are the
whole calculus the pruning machine needs. -/

@[simp]
theorem answeredEntries_concat_some (t : List (X × Option Y)) (x : X) (y : Y) :
    answeredEntries (t ++ [(x, some y)]) = answeredEntries t ++ [(x, y)] := by
  simp [answeredEntries]

@[simp]
theorem answeredEntries_concat_none (t : List (X × Option Y)) (x : X) :
    answeredEntries (t ++ [(x, none)]) = answeredEntries t := by
  simp [answeredEntries]

theorem length_answeredEntries_le (t : List (X × Option Y)) :
    (answeredEntries t).length ≤ t.length :=
  List.length_filterMap_le _ t

/-- The two presentations' transcripts, side by side: marking every answer of a
Definition 2.12 transcript as present is the Definition 3.7 transcript of an
interaction that refuses nothing. -/
def markAnswers (t : Transcript X Y) : List (X × Option Y) :=
  t.map fun p => (p.1, some p.2)

theorem markAnswers_injective :
    Function.Injective (markAnswers (X := X) (Y := Y)) :=
  List.map_injective_iff.mpr fun p p' h => by
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    exact Prod.ext h.1 h.2

@[simp]
theorem answeredEntries_markAnswers (t : Transcript X Y) :
    answeredEntries (markAnswers t) = t := by
  simpa [markAnswers] using answeredEntries_map_some t

/-! ### The coded interaction, without compatibility

`DDE.Total.transcript_total` (`Environment.lean`) reproduces the Definition-2.12
interaction inside the CR18 engine *verbatim*, and pays for it with the
compatibility hypothesis: the coded environment must never be refused.  The
answered part needs no such hypothesis, and the two lemmas below are why.

A refusal is not silent in either presentation.  On the Definition-2.12 side
the round is not taken at all — `trStep` leaves the transcript alone, and the
interaction is frozen from then on.  On the coded side the round *is* taken,
appending `(x, ⊥)`; but the coded environment reads its own history, that
history now carries a `⊥`, and `DDE.total` is `⊣` on every such history, so the
coded run is frozen from then on as well.  The `⊥` entry is exactly what
`answeredEntries` discards.  So the two presentations agree on the answered part
of *every* pair, compatible or not — which is what lets a Definition-2.12
transcript law be read off the total presentation's transcript law, hence be
pinned by Definition 2.17. -/

/-- Sequencing a history that carries a `⊥` fails: `mapM` in `Option`. -/
theorem mapM_id_eq_none_of_none_mem :
    ∀ {l : List (Option Y)}, none ∈ l → l.mapM id = none := by
  intro l h
  induction l with
  | nil => simp at h
  | cons a l ih =>
      rcases a with _ | y
      · simp [List.mapM_cons]
      · rw [List.mapM_cons]
        rw [ih (by simpa using h)]
        rfl

/-- **The coded environment stops on a refused history.**  `DDE.total` sequences
the history it is given, so a single `⊥` in it makes the whole move `⊣`.  This
is the coding's own doing — the value on `⊥`-carrying histories is junk in the
sense that no *compatible* interaction reaches one — and it is what freezes the
coded run at the first refusal. -/
theorem DDE.total_eq_none_of_none_mem (e : DDE Y X) {l : List (Option Y)}
    (h : none ∈ l) : e.total l = none := by
  rw [DDE.total, mapM_id_eq_none_of_none_mem h]
  rfl

/-- **The two presentations, in lockstep or frozen.**  At every length the coded
transcript either *is* the Definition-2.12 transcript with every answer marked
present, or the interaction has been refused: the coded run is frozen (`⊣`), the
Definition-2.12 run is frozen too, and the answered parts agree.

This is the induction the unconditional agreement
(`DDE.Total.answeredEntries_transcript_total`) rests on; the disjunction is the
invariant that survives a refusal, which the lockstep equation alone does
not. -/
theorem DDE.Total.transcript_total_markAnswers_or_frozen (e : DDE Y X)
    (s : DDS X Y) : ∀ n : ℕ,
      DDE.Total.transcript s e.total n = markAnswers (trN e s n) ∨
        (e.total (DDE.Total.transcript s e.total n)↓ᵧ = none ∧
          answeredEntries (DDE.Total.transcript s e.total n) = trN e s n ∧
          trN e s (n + 1) = trN e s n) := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      rcases ih with hmark | ⟨hstop, hans, hstall⟩
      · have houts : (DDE.Total.transcript s e.total n)↓ᵧ =
            ((trN e s n).map Prod.snd).map some := by
          rw [hmark]
          simp [markAnswers, transcriptOutputs, List.map_map, Function.comp_def]
        have hins : (DDE.Total.transcript s e.total n)↓ₓ =
            (trN e s n).map Prod.fst := by
          rw [hmark]
          simp [markAnswers, transcriptInputs, List.map_map, Function.comp_def]
        have hkept : keptPrefix s ((trN e s n).map Prod.fst) =
            (trN e s n).map Prod.fst := by
          rcases trN_map_fst_mem_dom_or_nil e s n with hnil | hmem
          · simp [hnil, keptPrefix]
          · exact keptPrefix_eq_self_of_mem s hmem
        by_cases hdom : (trN e s n).map Prod.snd ∈ e.1.Dom
        · have hxval : e.total ((DDE.Total.transcript s e.total n)↓ᵧ) =
              some ((e.1 ((trN e s n).map Prod.snd)).get hdom) := by
            rw [houts, DDE.total_map_some, dif_pos hdom]
          have hstep := DDE.Total.transcript_succ_of_query s e.total hxval
          rw [hins] at hstep
          by_cases hy : (trN e s n).map Prod.fst ++
              [(e.1 ((trN e s n).map Prod.snd)).get hdom] ∈ dom s
          · left
            have hanswer : answer s ((trN e s n).map Prod.fst)
                ((e.1 ((trN e s n).map Prod.snd)).get hdom) =
                some (output s _ hy) := by
              rw [answer_eq, dif_pos (by rw [hkept]; exact hy)]
              exact congrArg some (output_congr s (by rw [hkept]) _ hy)
            have htrN : trN e s (n + 1) = trN e s n ++
                [((e.1 ((trN e s n).map Prod.snd)).get hdom, output s _ hy)] :=
              trN_succ_of_query hdom hy
            rw [hstep, hanswer, hmark, htrN]
            simp [markAnswers]
          · right
            have hanswer : answer s ((trN e s n).map Prod.fst)
                ((e.1 ((trN e s n).map Prod.snd)).get hdom) = none := by
              rw [answer_eq, dif_neg (by rw [hkept]; exact hy)]
            have htrN : trN e s (n + 1) = trN e s n := by
              show trStep e s (trN e s n) = trN e s n
              rw [trStep, dif_pos hdom, dif_neg hy]
            rw [hstep, hanswer]
            refine ⟨?_, ?_, ?_⟩
            · refine DDE.total_eq_none_of_none_mem e ?_
              rw [transcriptOutputs_concat]
              simp
            · rw [hmark, answeredEntries_concat_none, answeredEntries_markAnswers,
                htrN]
            · show trStep e s (trN e s (n + 1)) = trN e s (n + 1)
              rw [htrN, trStep, dif_pos hdom, dif_neg hy]
        · left
          have hxval : e.total ((DDE.Total.transcript s e.total n)↓ᵧ) = none := by
            rw [houts, DDE.total_map_some, dif_neg hdom]
          rw [DDE.Total.transcript_succ_of_stop s e.total hxval, hmark,
            trN_succ_of_stop hdom]
      · right
        rw [DDE.Total.transcript_succ_of_stop s e.total hstop]
        refine ⟨hstop, hans.trans hstall.symm, ?_⟩
        show trStep e s (trN e s (n + 1)) = trN e s (n + 1)
        rw [hstall]
        exact hstall

/-- **The two presentations agree on the answered part, with no hypothesis.**
Stripping the coding from the CR18 transcript of the coded environment recovers
the Definition-2.12 transcript — for every pair, not only the compatible ones
(`DDE.Total.answeredEntries_transcript_total` in `Environment.lean` is the
compatible case of this, obtained there from the stronger verbatim agreement). -/
theorem DDE.Total.answeredEntries_transcript_total_of_total (e : DDE Y X)
    (s : DDS X Y) (n : ℕ) :
    answeredEntries (DDE.Total.transcript s e.total n) = trN e s n := by
  rcases DDE.Total.transcript_total_markAnswers_or_frozen e s n with h | ⟨-, h, -⟩
  · rw [h, answeredEntries_markAnswers]
  · exact h

/-- A run that stops stays stopped: once the environment has returned `⊣` the
transcript no longer grows. -/
theorem DDE.Total.transcript_freeze {s : DDS X Y} {e : DDE.Total Y X} {f : ℕ}
    (h : e (DDE.Total.transcript s e f)↓ᵧ = none) :
    ∀ {q : ℕ}, f ≤ q → DDE.Total.transcript s e q = DDE.Total.transcript s e f := by
  intro q hq
  induction q, hq using Nat.le_induction with
  | base => rfl
  | succ q _ ih =>
      rw [DDE.Total.transcript_succ_of_stop s e (by rw [ih]; exact h), ih]

theorem DDE.Total.transcript_length_le (s : DDS X Y) (e : DDE.Total Y X) (n : ℕ) :
    (DDE.Total.transcript s e n).length ≤ n := by
  rcases (DDE.Total.transcript_consistent s e n).1.2 with h | ⟨h, -⟩
  · exact le_of_eq h
  · exact le_of_lt h

theorem DDE.Total.transcript_stall_of_length_lt {s : DDS X Y} {e : DDE.Total Y X}
    {n : ℕ} (h : (DDE.Total.transcript s e n).length < n) :
    e (DDE.Total.transcript s e n)↓ᵧ = none := by
  rcases (DDE.Total.transcript_consistent s e n).1.2 with h' | ⟨-, h'⟩
  · omega
  · exact h'

/-! ### Rejection pruning against a known common domain

Definition 2.26 quantifies over environments that never step outside the
system's domain; Ruling R4's total environments are free to step outside it and
read the refusal.  On the objects Definition 2.14 admits — all deterministic
systems in a support share one domain `D` — that freedom buys nothing, because
*which* queries are refused is then a public function of the query history, not
of the sampled system.  An environment that knows `D` can therefore synthesize
every refusal itself and forward only the queries `D` accepts.

The **replay machine** is that simulation.  Its state is the virtual
Definition-3.7 transcript rebuilt so far together with the real answers not yet
consumed; one step reads the total environment on the virtual transcript, and

* answers a `D`-rejected query `⊥` internally, appending it to the virtual
  transcript and consuming nothing;
* forwards a `D`-accepted query, consuming the next real answer;
* freezes on `⊣`, and freezes when a forwarded query has no answer yet — the
  *blocked* state, which is where the pruned environment makes its move.

Read as a partial function of the real answers, the machine **is** a
Definition-2.11 environment (`prunedEnv`), and it is compatible with every
system whose domain is `D`. -/

section Pruning

open Classical

/-- One step of the rejection-pruning replay. -/
def pruneStep (e : DDE.Total Y X) (D : Set (List X)) :
    List (X × Option Y) × List Y → List (X × Option Y) × List Y :=
  fun state =>
    match e state.1↓ᵧ with
    | none => state
    | some x =>
        if answeredQueries state.1 ++ [x] ∈ D then
          match state.2 with
          | [] => state
          | y :: rest => (state.1 ++ [(x, some y)], rest)
        else (state.1 ++ [(x, none)], state.2)

/-- The state that awaits the next real answer: the environment forwards a
query the common domain accepts, and no answer has arrived. -/
def Blocked (e : DDE.Total Y X) (D : Set (List X))
    (state : List (X × Option Y) × List Y) : Prop :=
  state.2 = [] ∧
    ∃ x, e state.1↓ᵧ = some x ∧ answeredQueries state.1 ++ [x] ∈ D

theorem pruneStep_stall {e : DDE.Total Y X} {D : Set (List X)}
    {t : List (X × Option Y)} {rest : List Y} (h : e t↓ᵧ = none) :
    pruneStep e D (t, rest) = (t, rest) := by
  unfold pruneStep
  dsimp only
  rw [h]

theorem pruneStep_reject {e : DDE.Total Y X} {D : Set (List X)}
    {t : List (X × Option Y)} {rest : List Y} {x : X}
    (h : e t↓ᵧ = some x) (hx : answeredQueries t ++ [x] ∉ D) :
    pruneStep e D (t, rest) = (t ++ [(x, none)], rest) := by
  unfold pruneStep
  dsimp only
  rw [h]
  dsimp only
  rw [if_neg hx]

theorem pruneStep_consume {e : DDE.Total Y X} {D : Set (List X)}
    {t : List (X × Option Y)} {y : Y} {rest : List Y} {x : X}
    (h : e t↓ᵧ = some x) (hx : answeredQueries t ++ [x] ∈ D) :
    pruneStep e D (t, y :: rest) = (t ++ [(x, some y)], rest) := by
  unfold pruneStep
  dsimp only
  rw [h]
  dsimp only
  rw [if_pos hx]

/-- The stalled state is a fixed point, in the unbundled form the iteration
lemmas consume (`pruneStep_stall` at an explicit pair). -/
theorem pruneStep_stall_state {e : DDE.Total Y X} {D : Set (List X)}
    {state : List (X × Option Y) × List Y} (h : e state.1↓ᵧ = none) :
    pruneStep e D state = state := by
  obtain ⟨t, rest⟩ := state
  exact pruneStep_stall h

theorem pruneStep_blocked {e : DDE.Total Y X} {D : Set (List X)}
    {state : List (X × Option Y) × List Y} (h : Blocked e D state) :
    pruneStep e D state = state := by
  obtain ⟨hrest, x, hfire, hacc⟩ := h
  obtain ⟨t, rest⟩ := state
  dsimp only at hrest
  subst hrest
  unfold pruneStep
  dsimp only
  rw [hfire]
  dsimp only
  rw [if_pos hacc]

/-- The pruning replay: from the real answers alone, rebuild the virtual
Definition-3.7 transcript after at most `fuel` virtual steps. -/
def pruneRun (e : DDE.Total Y X) (D : Set (List X)) (fuel : ℕ)
    (answers : List Y) : List (X × Option Y) × List Y :=
  (pruneStep e D)^[fuel] ([], answers)

theorem pruneRun_succ (e : DDE.Total Y X) (D : Set (List X)) (fuel : ℕ)
    (answers : List Y) :
    pruneRun e D (fuel + 1) answers = pruneStep e D (pruneRun e D fuel answers) :=
  Function.iterate_succ_apply' _ _ _

theorem pruneRun_add (e : DDE.Total Y X) (D : Set (List X))
    {small large : ℕ} (hle : small ≤ large) (answers : List Y) :
    pruneRun e D large answers =
      (pruneStep e D)^[large - small] (pruneRun e D small answers) := by
  unfold pruneRun
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hle]

/-- The machine never rebuilds more virtual steps than its fuel. -/
theorem pruneRun_fst_length_le (e : DDE.Total Y X) (D : Set (List X)) :
    ∀ (fuel : ℕ) (answers : List Y),
      (pruneRun e D fuel answers).1.length ≤ fuel := by
  intro fuel
  induction fuel with
  | zero => intro answers; exact Nat.le_refl 0
  | succ fuel ih =>
      intro answers
      rw [pruneRun_succ]
      cases hp : pruneRun e D fuel answers with
      | mk t rest =>
      have hlen : t.length ≤ fuel := by
        have hlen' := ih answers
        rw [hp] at hlen'
        exact hlen'
      rcases he : e t↓ᵧ with _ | x
      · rw [pruneStep_stall he]
        exact Nat.le_succ_of_le hlen
      · by_cases hacc : answeredQueries t ++ [x] ∈ D
        · cases rest with
          | nil =>
              rw [pruneStep_blocked ⟨rfl, x, he, hacc⟩]
              exact Nat.le_succ_of_le hlen
          | cons y rest =>
              rw [pruneStep_consume he hacc]
              simpa using Nat.succ_le_succ hlen
        · rw [pruneStep_reject he hacc]
          simpa using Nat.succ_le_succ hlen

/-- Extending the real answers either commutes with the replay or the shorter
replay froze awaiting an answer strictly before the fuel ran out.  This is what
makes the pruned environment's stop **final**, hence its domain prefix-closed. -/
theorem pruneRun_append (e : DDE.Total Y X) (D : Set (List X)) (extra : List Y) :
    ∀ (fuel : ℕ) (answers : List Y),
      pruneRun e D fuel (answers ++ extra) =
          ((pruneRun e D fuel answers).1,
            (pruneRun e D fuel answers).2 ++ extra) ∨
        ∃ j < fuel, Blocked e D (pruneRun e D j answers) := by
  intro fuel
  induction fuel with
  | zero => intro answers; exact Or.inl rfl
  | succ fuel ih =>
      intro answers
      rcases ih answers with heq | ⟨j, hj, hblocked⟩
      · rw [pruneRun_succ, pruneRun_succ, heq]
        cases hp : pruneRun e D fuel answers with
        | mk t rest =>
        rcases he : e t↓ᵧ with _ | x
        · rw [pruneStep_stall he, pruneStep_stall he]
          exact Or.inl rfl
        · by_cases hacc : answeredQueries t ++ [x] ∈ D
          · cases rest with
            | nil =>
                refine Or.inr ⟨fuel, Nat.lt_succ_self fuel, ?_⟩
                rw [hp]
                exact ⟨rfl, x, he, hacc⟩
            | cons y rest =>
                rw [show (y :: rest) ++ extra = y :: (rest ++ extra) from rfl,
                  pruneStep_consume he hacc, pruneStep_consume he hacc]
                exact Or.inl rfl
          · rw [pruneStep_reject he hacc, pruneStep_reject he hacc]
            exact Or.inl rfl
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hblocked⟩

/-- A blocked replay is frozen: the state never changes again. -/
theorem pruneRun_eq_of_blocked {e : DDE.Total Y X} {D : Set (List X)}
    {answers : List Y} {j : ℕ}
    (hblocked : Blocked e D (pruneRun e D j answers)) {fuel : ℕ} (hle : j ≤ fuel) :
    pruneRun e D fuel answers = pruneRun e D j answers := by
  rw [pruneRun_add e D hle]
  exact Function.iterate_fixed (pruneStep_blocked hblocked) _

/-- A stalled replay is frozen, exactly as a blocked one is
(`pruneRun_eq_of_blocked`): the state never changes again. -/
theorem pruneRun_eq_of_stall {e : DDE.Total Y X} {D : Set (List X)}
    {answers : List Y} {j : ℕ}
    (hstall : e (pruneRun e D j answers).1↓ᵧ = none) {fuel : ℕ} (hle : j ≤ fuel) :
    pruneRun e D fuel answers = pruneRun e D j answers := by
  rw [pruneRun_add e D hle]
  exact Function.iterate_fixed (pruneStep_stall_state hstall) _

/-- **The replay spends its fuel or gets stuck**: after `fuel` steps the virtual
transcript has grown by exactly `fuel` entries, unless the machine stalled or
blocked on the way — the only two states in which a step does nothing.  With
`pruneRun_eq_of_stall`/`pruneRun_eq_of_blocked`, which say those two states are
final, this is what bounds the pruned environment's own number of rounds. -/
theorem pruneRun_length_or_stuck (e : DDE.Total Y X) (D : Set (List X)) :
    ∀ (fuel : ℕ) (answers : List Y),
      (pruneRun e D fuel answers).1.length = fuel ∨
        ∃ j < fuel, (e (pruneRun e D j answers).1↓ᵧ = none ∨
          Blocked e D (pruneRun e D j answers)) := by
  intro fuel
  induction fuel with
  | zero => intro answers; exact Or.inl rfl
  | succ fuel ih =>
      intro answers
      rcases ih answers with hlen | ⟨j, hj, hstuck⟩
      · rw [pruneRun_succ]
        cases hp : pruneRun e D fuel answers with
        | mk t rest =>
        have hlen' : t.length = fuel := by rw [hp] at hlen; exact hlen
        rcases he : e t↓ᵧ with _ | x
        · exact Or.inr ⟨fuel, Nat.lt_succ_self fuel,
            Or.inl (by rw [hp]; exact he)⟩
        · by_cases hacc : answeredQueries t ++ [x] ∈ D
          · cases rest with
            | nil =>
                exact Or.inr ⟨fuel, Nat.lt_succ_self fuel,
                  Or.inr (by rw [hp]; exact ⟨rfl, x, he, hacc⟩)⟩
            | cons y rest =>
                rw [pruneStep_consume he hacc]
                exact Or.inl (by simp [hlen'])
          · rw [pruneStep_reject he hacc]
            exact Or.inl (by simp [hlen'])
      · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hstuck⟩

/-- **The replay's answer budget**: every real answer it has taken is one
answered entry of the virtual transcript, so answered entries and unconsumed
answers together account for the answer list exactly.  A rejected round
synthesizes its `⊥` and consumes nothing, which is why the count is of
`answeredEntries` and not of the transcript. -/
theorem pruneRun_answeredEntries_length_add (e : DDE.Total Y X) (D : Set (List X)) :
    ∀ (fuel : ℕ) (answers : List Y),
      (answeredEntries (pruneRun e D fuel answers).1).length +
        (pruneRun e D fuel answers).2.length = answers.length := by
  intro fuel
  induction fuel with
  | zero => intro answers; simp [pruneRun, answeredEntries]
  | succ fuel ih =>
      intro answers
      have hih := ih answers
      rw [pruneRun_succ]
      cases hp : pruneRun e D fuel answers with
      | mk t rest =>
      rw [hp] at hih
      rcases he : e t↓ᵧ with _ | x
      · rw [pruneStep_stall he]; exact hih
      · by_cases hacc : answeredQueries t ++ [x] ∈ D
        · cases rest with
          | nil => rw [pruneStep_blocked ⟨rfl, x, he, hacc⟩]; exact hih
          | cons y rest =>
              rw [pruneStep_consume he hacc]
              simp only [answeredEntries_concat_some, List.length_append,
                List.length_cons, List.length_nil] at hih ⊢
              omega
        · rw [pruneStep_reject he hacc]
          simpa [answeredEntries_concat_none] using hih

/-! #### The pruned environment -/

/-- The move of the pruned environment: replay the real answers for at most `q`
virtual steps, then forward the environment's next query while virtual budget
remains, and otherwise stop. -/
def prunedNext (e : DDE.Total Y X) (D : Set (List X)) (q : ℕ)
    (answers : List Y) : Option X :=
  match e (pruneRun e D q answers).1↓ᵧ with
  | none => none
  | some x => if (pruneRun e D q answers).1.length < q then some x else none

theorem prunedNext_of_stall {e : DDE.Total Y X} {D : Set (List X)} {q : ℕ}
    {answers : List Y} (h : e (pruneRun e D q answers).1↓ᵧ = none) :
    prunedNext e D q answers = none := by
  unfold prunedNext
  rw [h]

theorem prunedNext_of_fire {e : DDE.Total Y X} {D : Set (List X)} {q : ℕ}
    {answers : List Y} {x : X} (h : e (pruneRun e D q answers).1↓ᵧ = some x) :
    prunedNext e D q answers =
      if (pruneRun e D q answers).1.length < q then some x else none := by
  unfold prunedNext
  rw [h]

/-- The pruned move reads only the rebuilt virtual transcript. -/
theorem prunedNext_congr_fst {e : DDE.Total Y X} {D : Set (List X)} {q : ℕ}
    {answers answers' : List Y}
    (h : (pruneRun e D q answers).1 = (pruneRun e D q answers').1) :
    prunedNext e D q answers = prunedNext e D q answers' := by
  unfold prunedNext
  rw [h]

/-- **The pruned stop is final**: once the machine has stopped on a history it
stops on every extension of it.  Either the extra answers do not reach the
replay at all, or the shorter replay was already blocked — and a blocked replay
is frozen with virtual budget to spare, so it would have forwarded a query
rather than stopped. -/
theorem prunedNext_eq_none_of_append {e : DDE.Total Y X} {D : Set (List X)}
    {q : ℕ} {answers extra : List Y} (h : prunedNext e D q answers = none) :
    prunedNext e D q (answers ++ extra) = none := by
  rcases pruneRun_append e D extra q answers with heq | ⟨j, hj, hblocked⟩
  · have hfst : (pruneRun e D q (answers ++ extra)).1 =
        (pruneRun e D q answers).1 := by rw [heq]
    rw [prunedNext_congr_fst hfst]
    exact h
  · exfalso
    have hfrozen := pruneRun_eq_of_blocked hblocked (Nat.le_of_lt hj)
    obtain ⟨-, x, hfire, -⟩ := hblocked
    have hlen : (pruneRun e D q answers).1.length < q := by
      rw [hfrozen]
      exact Nat.lt_of_le_of_lt (pruneRun_fst_length_le e D j answers) hj
    have hfire' : e (pruneRun e D q answers).1↓ᵧ = some x := by
      rw [hfrozen]; exact hfire
    rw [prunedNext_of_fire hfire', if_pos hlen] at h
    simp at h

/-- **The replay machine, read as a Definition-2.11 environment**: a partial
function of the real answers, undefined exactly where the replay stops.  Its
domain is prefix-closed because the stop is final
(`prunedNext_eq_none_of_append`). -/
def prunedEnv (e : DDE.Total Y X) (D : Set (List X)) (q : ℕ) : DDE Y X :=
  ⟨fun answers => Part.ofOption (prunedNext e D q answers), by
    intro shorter longer hprefix hdom
    obtain ⟨extra, rfl⟩ := hprefix
    rw [PFun.mem_dom] at hdom ⊢
    obtain ⟨x, hx⟩ := hdom
    rw [Part.mem_ofOption] at hx
    rcases hnext : prunedNext e D q shorter with _ | x'
    · rw [prunedNext_eq_none_of_append (extra := extra) hnext] at hx
      simp at hx
    · exact ⟨x', by simp⟩⟩

theorem prunedEnv_apply (e : DDE.Total Y X) (D : Set (List X)) (q : ℕ)
    (answers : List Y) :
    (prunedEnv e D q).1 answers = Part.ofOption (prunedNext e D q answers) :=
  rfl

theorem prunedEnv_notMem_dom {e : DDE.Total Y X} {D : Set (List X)} {q : ℕ}
    {answers : List Y} (h : prunedNext e D q answers = none) :
    answers ∉ (prunedEnv e D q).1.Dom := by
  intro hdom
  rw [PFun.mem_dom] at hdom
  obtain ⟨x, hx⟩ := hdom
  rw [prunedEnv_apply, Part.mem_ofOption, h] at hx
  simp at hx

theorem prunedEnv_mem_dom {e : DDE.Total Y X} {D : Set (List X)} {q : ℕ}
    {answers : List Y} {x : X} (h : prunedNext e D q answers = some x) :
    ∃ hdom : answers ∈ (prunedEnv e D q).1.Dom,
      ((prunedEnv e D q).1 answers).get hdom = x := by
  have hmem : x ∈ (prunedEnv e D q).1 answers := by
    rw [prunedEnv_apply, Part.mem_ofOption, h]
    rfl
  exact ⟨(PFun.mem_dom _ _).2 ⟨x, hmem⟩, Part.get_eq_of_mem hmem _⟩

/-- **The pruned environment stops after `q` answers**, whatever they are.  Its
move is to forward the query the replay is blocked on while virtual budget
remains, so once it has received `q` answers there is no budget left: either the
replay spent its whole fuel — and then the virtual transcript is `q` long — or
it got stuck, and a stall is a stop while a block means every one of the `q`
answers has been consumed, hence recorded as an answered entry of the virtual
transcript. -/
theorem prunedNext_eq_none_of_le_length {e : DDE.Total Y X} {D : Set (List X)}
    {q : ℕ} {answers : List Y} (h : q ≤ answers.length) :
    prunedNext e D q answers = none := by
  rcases he : e (pruneRun e D q answers).1↓ᵧ with _ | x
  · exact prunedNext_of_stall he
  · have hq : q ≤ (pruneRun e D q answers).1.length := by
      rcases pruneRun_length_or_stuck e D q answers with hlen | ⟨j, hj, hstuck⟩
      · exact le_of_eq hlen.symm
      · rcases hstuck with hstall | hblocked
        · exact absurd (by
            rw [pruneRun_eq_of_stall hstall (Nat.le_of_lt hj), hstall] at he
            exact he) (by simp)
        · have hfrozen := pruneRun_eq_of_blocked hblocked (Nat.le_of_lt hj)
          have hmass := pruneRun_answeredEntries_length_add e D q answers
          rw [hfrozen] at hmass ⊢
          rw [hblocked.1, List.length_nil] at hmass
          have hle := length_answeredEntries_le (pruneRun e D j answers).1
          omega
    rw [prunedNext_of_fire he, if_neg (not_lt.mpr hq)]

/-- **The pruned environment halts** (`System.DDE.Halts`), with `q` as its round
bound.  This is what puts it inside the domain-indexed index set of `PDS.AdvD`
— together with `compatible_prunedEnv`, which is `System.CompatibleD` for it by
definition — and it is a property of the environment alone: no system, no
support. -/
theorem halts_prunedEnv (e : DDE.Total Y X) (D : Set (List X)) (q : ℕ) :
    DDE.Halts (prunedEnv e D q) :=
  ⟨q, fun _ hl => prunedEnv_notMem_dom (prunedNext_eq_none_of_le_length hl)⟩

/-! #### Replay fidelity on a shared-domain system

Against a system whose domain is the common `D`, the machine fed the real
answers of a completed transcript rebuilds that transcript exactly: the
rejected rounds are resynthesized from `D`, the accepted ones consume the
forwarded answers verbatim.  This is where the shared-domain hypothesis is
spent, and it is the only place it is needed. -/

variable {D : Set (List X)} {s : DDS X Y}

/-- **Replay fidelity**: `f` machine steps on the real answers of the `f`-round
transcript rebuild that transcript, passing surplus answers through
untouched. -/
theorem pruneRun_answeredEntries (e : DDE.Total Y X) (hdom : dom s = D) :
    ∀ (f : ℕ) (extra : List Y),
      pruneRun e D f
          ((answeredEntries (DDE.Total.transcript s e f)).map Prod.snd ++ extra) =
        (DDE.Total.transcript s e f, extra) := by
  intro f
  induction f with
  | zero => intro extra; rfl
  | succ f ih =>
      intro extra
      rcases he : e (DDE.Total.transcript s e f)↓ᵧ with _ | x
      · rw [DDE.Total.transcript_succ_of_stop s e he, pruneRun_succ, ih extra,
          pruneStep_stall he]
      · have hkept : answeredQueries (DDE.Total.transcript s e f) =
            keptPrefix s (DDE.Total.transcript s e f)↓ₓ :=
          DDE.Total.answeredQueries_transcript s e f
        by_cases hcand :
            keptPrefix s (DDE.Total.transcript s e f)↓ₓ ++ [x] ∈ dom s
        · -- accepted: the machine consumes the forwarded answer verbatim
          have haccD : answeredQueries (DDE.Total.transcript s e f) ++ [x] ∈ D := by
            rw [hkept, ← hdom]
            exact hcand
          have hout : answer s (DDE.Total.transcript s e f)↓ₓ x =
              some (output s _ hcand) := by
            rw [answer_eq]
            exact dif_pos hcand
          rw [DDE.Total.transcript_succ_of_query s e he, hout,
            answeredEntries_concat_some, List.map_append, List.map_singleton,
            List.append_assoc, List.singleton_append, pruneRun_succ,
            ih (output s _ hcand :: extra), pruneStep_consume he haccD]
        · -- rejected: the machine resynthesizes the refusal from `D`
          have hrejD : answeredQueries (DDE.Total.transcript s e f) ++ [x] ∉ D := by
            rw [hkept, ← hdom]
            exact hcand
          have hout : answer s (DDE.Total.transcript s e f)↓ₓ x = none := by
            rw [answer_eq]
            exact dif_neg hcand
          rw [DDE.Total.transcript_succ_of_query s e he, hout,
            answeredEntries_concat_none, pruneRun_succ, ih extra,
            pruneStep_reject he hrejD]

/-- **Run-ahead to a terminal state**: with full fuel the machine passes the
`f`-round transcript and keeps going through rejected rounds only, stopping at
a genuine transcript prefix that is out of budget, stalled, or blocked awaiting
the next forwarded answer.  The rejected rounds it runs through are invisible
to the real interaction, which is why the answered part is unchanged. -/
theorem pruneRun_reaches_terminal (e : DDE.Total Y X) (hdom : dom s = D) :
    ∀ {f q : ℕ}, f ≤ q →
      ∃ f', f ≤ f' ∧ f' ≤ q ∧
        answeredEntries (DDE.Total.transcript s e f') =
          answeredEntries (DDE.Total.transcript s e f) ∧
        pruneRun e D q
            ((answeredEntries (DDE.Total.transcript s e f)).map Prod.snd) =
          (DDE.Total.transcript s e f', []) ∧
        (f' = q ∨ e (DDE.Total.transcript s e f')↓ᵧ = none ∨
          Blocked e D (DDE.Total.transcript s e f', [])) := by
  suffices h : ∀ (gap : ℕ) {f q : ℕ}, q - f = gap → f ≤ q →
      ∃ f', f ≤ f' ∧ f' ≤ q ∧
        answeredEntries (DDE.Total.transcript s e f') =
          answeredEntries (DDE.Total.transcript s e f) ∧
        pruneRun e D q
            ((answeredEntries (DDE.Total.transcript s e f)).map Prod.snd) =
          (DDE.Total.transcript s e f', []) ∧
        (f' = q ∨ e (DDE.Total.transcript s e f')↓ᵧ = none ∨
          Blocked e D (DDE.Total.transcript s e f', [])) by
    intro f q hfq
    exact h (q - f) rfl hfq
  intro gap
  induction gap with
  | zero =>
      intro f q hgap hfq
      obtain rfl : f = q := by omega
      refine ⟨f, Nat.le_refl f, Nat.le_refl f, rfl, ?_, Or.inl rfl⟩
      have hbase := pruneRun_answeredEntries (s := s) e hdom f []
      rwa [List.append_nil] at hbase
  | succ gap ih =>
      intro f q hgap hfq
      have hflt : f < q := by omega
      have hbase := pruneRun_answeredEntries (s := s) e hdom f []
      rw [List.append_nil] at hbase
      have hkept : answeredQueries (DDE.Total.transcript s e f) =
          keptPrefix s (DDE.Total.transcript s e f)↓ₓ :=
        DDE.Total.answeredQueries_transcript s e f
      rcases he : e (DDE.Total.transcript s e f)↓ᵧ with _ | x
      · -- stalled: frozen at the `f`-round transcript
        refine ⟨f, Nat.le_refl f, hfq, rfl, ?_, Or.inr (Or.inl he)⟩
        rw [pruneRun_add e D hfq, hbase]
        exact Function.iterate_fixed (pruneStep_stall he) _
      · by_cases hcand :
            keptPrefix s (DDE.Total.transcript s e f)↓ₓ ++ [x] ∈ dom s
        · -- accepted: blocked awaiting the forwarded answer
          have haccD : answeredQueries (DDE.Total.transcript s e f) ++ [x] ∈ D := by
            rw [hkept, ← hdom]
            exact hcand
          have hblocked : Blocked e D (DDE.Total.transcript s e f, []) :=
            ⟨rfl, x, he, haccD⟩
          refine ⟨f, Nat.le_refl f, hfq, rfl, ?_, Or.inr (Or.inr hblocked)⟩
          rw [pruneRun_add e D hfq, hbase]
          exact Function.iterate_fixed (pruneStep_blocked hblocked) _
        · -- rejected: transcript and machine run ahead in lockstep
          have hout : answer s (DDE.Total.transcript s e f)↓ₓ x = none := by
            rw [answer_eq]
            exact dif_neg hcand
          have hstep : answeredEntries (DDE.Total.transcript s e (f + 1)) =
              answeredEntries (DDE.Total.transcript s e f) := by
            rw [DDE.Total.transcript_succ_of_query s e he, hout,
              answeredEntries_concat_none]
          obtain ⟨f', hff', hf'q, hprop, hrun, hterm⟩ :=
            ih (f := f + 1) (q := q) (by omega) (by omega)
          rw [hstep] at hprop hrun
          exact ⟨f', Nat.le_of_succ_le hff', hf'q, hprop, hrun, hterm⟩

/-- **The pruned interaction is a Definition-2.12 interaction.**  Against a
system whose domain is the common `D`, every round of the pruned environment's
run is the answered part of a genuine Ruling-R4 run of the original
environment, with the replay machine settled on it at a terminal state.

This is the single induction the whole pruning argument rests on: it supplies
compatibility (the forwarded query is always in the domain), stopping (the
budget is finite), and the transcript identity at the budget. -/
theorem trN_prunedEnv (e : DDE.Total Y X) (hdom : dom s = D) (q : ℕ) :
    ∀ j : ℕ, ∃ f', f' ≤ q ∧
      trN (prunedEnv e D q) s j = answeredEntries (DDE.Total.transcript s e f') ∧
      pruneRun e D q ((trN (prunedEnv e D q) s j).map Prod.snd) =
        (DDE.Total.transcript s e f', []) ∧
      (f' = q ∨ e (DDE.Total.transcript s e f')↓ᵧ = none ∨
        Blocked e D (DDE.Total.transcript s e f', [])) := by
  intro j
  induction j with
  | zero =>
      obtain ⟨f', -, hf'q, hprop, hrun, hterm⟩ :=
        pruneRun_reaches_terminal (s := s) e hdom (Nat.zero_le q)
      refine ⟨f', hf'q, ?_, ?_, hterm⟩
      · show ([] : Transcript X Y) = _
        simpa [DDE.Total.transcript, answeredEntries] using hprop.symm
      · show pruneRun e D q (([] : Transcript X Y).map Prod.snd) = _
        simpa [DDE.Total.transcript, answeredEntries] using hrun
  | succ j ihj =>
      obtain ⟨f', hf'q, htranscript, hrun, hterm⟩ := ihj
      rcases he : e (DDE.Total.transcript s e f')↓ᵧ with _ | x
      · -- the original environment stalled: the pruned one stops too
        have hstall : prunedNext e D q
            ((trN (prunedEnv e D q) s j).map Prod.snd) = none :=
          prunedNext_of_stall (by rw [hrun]; exact he)
        rw [trN_succ_of_stop (prunedEnv_notMem_dom hstall)]
        exact ⟨f', hf'q, htranscript, hrun, hterm⟩
      · by_cases hlen : (DDE.Total.transcript s e f').length < q
        · -- budget remains: the pruned environment forwards the query
          have hf'lt : f' < q := by
            rcases Nat.lt_or_ge f' q with h | h
            · exact h
            · exfalso
              obtain rfl : f' = q := Nat.le_antisymm hf'q h
              rw [DDE.Total.transcript_stall_of_length_lt hlen] at he
              simp at he
          have hblocked : Blocked e D (DDE.Total.transcript s e f', []) := by
            rcases hterm with hfq | hstallterm | hb
            · exact absurd hfq (Nat.ne_of_lt hf'lt)
            · rw [hstallterm] at he; simp at he
            · exact hb
          have haccD : answeredQueries (DDE.Total.transcript s e f') ++ [x] ∈ D := by
            obtain ⟨-, x', hfire', haccx'⟩ := hblocked
            have hxx : x = x' := Option.some.inj (he.symm.trans hfire')
            rw [hxx]
            exact haccx'
          have hcand : answeredQueries (DDE.Total.transcript s e f') ++ [x] ∈ dom s := by
            rw [hdom]; exact haccD
          have hkept : keptPrefix s (DDE.Total.transcript s e f')↓ₓ =
              answeredQueries (DDE.Total.transcript s e f') :=
            (DDE.Total.answeredQueries_transcript s e f').symm
          -- the original run's next answered entry
          have hanswered : answeredEntries (DDE.Total.transcript s e (f' + 1)) =
              answeredEntries (DDE.Total.transcript s e f') ++
                [(x, output s (answeredQueries (DDE.Total.transcript s e f') ++ [x])
                  hcand)] := by
            have hout : answer s (DDE.Total.transcript s e f')↓ₓ x =
                some (output s
                  (answeredQueries (DDE.Total.transcript s e f') ++ [x]) hcand) := by
              rw [answer_eq, dif_pos (show
                keptPrefix s (DDE.Total.transcript s e f')↓ₓ ++ [x] ∈ dom s by
                  rw [hkept]; exact hcand)]
              exact congrArg some (output_congr s (by rw [hkept]) _ hcand)
            rw [DDE.Total.transcript_succ_of_query s e he, hout,
              answeredEntries_concat_some]
          -- the pruned environment's own next round
          have hfire : prunedNext e D q
              ((trN (prunedEnv e D q) s j).map Prod.snd) = some x := by
            rw [prunedNext_of_fire (by rw [hrun]; exact he), hrun, if_pos hlen]
          obtain ⟨hdomE, hgetE⟩ := prunedEnv_mem_dom hfire
          have hquery : (trN (prunedEnv e D q) s j).map Prod.fst =
              answeredQueries (DDE.Total.transcript s e f') := by
            rw [htranscript, answeredEntries_map_fst]
          have hy : (trN (prunedEnv e D q) s j).map Prod.fst ++
              [((prunedEnv e D q).1
                ((trN (prunedEnv e D q) s j).map Prod.snd)).get hdomE] ∈ dom s := by
            rw [hgetE, hquery]
            exact hcand
          have hstepEq : trN (prunedEnv e D q) s (j + 1) =
              answeredEntries (DDE.Total.transcript s e (f' + 1)) := by
            rw [trN_succ_of_query hdomE hy, hanswered]
            have hentry :
                (((prunedEnv e D q).1
                    ((trN (prunedEnv e D q) s j).map Prod.snd)).get hdomE,
                  output s ((trN (prunedEnv e D q) s j).map Prod.fst ++
                    [((prunedEnv e D q).1
                      ((trN (prunedEnv e D q) s j).map Prod.snd)).get hdomE]) hy) =
                (x, output s
                  (answeredQueries (DDE.Total.transcript s e f') ++ [x]) hcand) :=
              Prod.ext hgetE (output_congr s (by rw [hquery, hgetE]) hy hcand)
            rw [hentry, htranscript]
          obtain ⟨f'', -, hf''q, hprop, hrun'', hterm''⟩ :=
            pruneRun_reaches_terminal (s := s) e hdom (Nat.succ_le_of_lt hf'lt)
          refine ⟨f'', hf''q, ?_, ?_, hterm''⟩
          · rw [hstepEq]; exact hprop.symm
          · rw [hstepEq]; exact hrun''
        · -- budget exhausted: the pruned environment stops
          have hstall : prunedNext e D q
              ((trN (prunedEnv e D q) s j).map Prod.snd) = none := by
            rw [prunedNext_of_fire (by rw [hrun]; exact he), hrun, if_neg hlen]
          rw [trN_succ_of_stop (prunedEnv_notMem_dom hstall)]
          exact ⟨f', hf'q, htranscript, hrun, hterm⟩

/-- **The pruned environment only forwards queries the system answers** — the
formal content of "it synthesizes the refusals itself".  The forwarded query is
the one the *blocked* replay is waiting on, and a replay blocks only on a query
the common domain accepts. -/
theorem prunedEnv_fire_mem_dom (e : DDE.Total Y X) (hdom : dom s = D) (q j : ℕ)
    {x : X}
    (hfire : prunedNext e D q ((trN (prunedEnv e D q) s j).map Prod.snd) = some x) :
    (trN (prunedEnv e D q) s j).map Prod.fst ++ [x] ∈ dom s := by
  obtain ⟨f', hf'q, htranscript, hrun, hterm⟩ := trN_prunedEnv e hdom q j
  rcases he : e (DDE.Total.transcript s e f')↓ᵧ with _ | x'
  · rw [prunedNext_of_stall (by rw [hrun]; exact he)] at hfire
    simp at hfire
  · rw [prunedNext_of_fire (by rw [hrun]; exact he), hrun] at hfire
    by_cases hlen : (DDE.Total.transcript s e f').length < q
    · rw [if_pos hlen] at hfire
      have hxx : x' = x := Option.some.inj hfire
      have hf'lt : f' < q := by
        rcases Nat.lt_or_ge f' q with h | h
        · exact h
        · exfalso
          obtain rfl : f' = q := Nat.le_antisymm hf'q h
          rw [DDE.Total.transcript_stall_of_length_lt hlen] at he
          simp at he
      have hblocked : Blocked e D (DDE.Total.transcript s e f', []) := by
        rcases hterm with hfq | hstallterm | hb
        · exact absurd hfq (Nat.ne_of_lt hf'lt)
        · rw [hstallterm] at he; simp at he
        · exact hb
      obtain ⟨-, x'', hfire'', hacc''⟩ := hblocked
      have hxx'' : x' = x'' := Option.some.inj (he.symm.trans hfire'')
      rw [htranscript, answeredEntries_map_fst, ← hxx, hxx'', hdom]
      exact hacc''
    · rw [if_neg hlen] at hfire
      simp at hfire

/-- **The pruned environment is compatible** (Definition 2.12) with every
system whose domain is the common `D`. -/
theorem compatible_prunedEnv (e : DDE.Total Y X) (hdom : dom s = D) (q : ℕ) :
    Compatible (prunedEnv e D q) s := by
  intro n x hx
  refine prunedEnv_fire_mem_dom e hdom q n ?_
  rw [prunedEnv_apply, Part.mem_ofOption] at hx
  exact hx

/-- **The pruned environment settles at its budget**, and what it has recorded
there is exactly the answered part of the original `q`-round run.  Both halves
come out of the same case split: either the original environment had already
stopped — and then its run froze, so its answered part never changed again — or
it is still asking, and then the budget is what stops the pruned environment,
which happens exactly at `f' = q`. -/
theorem prunedEnv_settles (e : DDE.Total Y X) (hdom : dom s = D) (q : ℕ) :
    trN (prunedEnv e D q) s (q + 1) = trN (prunedEnv e D q) s q ∧
      trN (prunedEnv e D q) s q = answeredEntries (DDE.Total.transcript s e q) := by
  obtain ⟨f', hf'q, htranscript, hrun, hterm⟩ := trN_prunedEnv e hdom q q
  have hlenle : (trN (prunedEnv e D q) s q).length ≤
      (DDE.Total.transcript s e f').length := by
    rw [htranscript]
    exact length_answeredEntries_le _
  have hstop : prunedNext e D q ((trN (prunedEnv e D q) s q).map Prod.snd) = none ∧
      answeredEntries (DDE.Total.transcript s e f') =
        answeredEntries (DDE.Total.transcript s e q) := by
    rcases he : e (DDE.Total.transcript s e f')↓ᵧ with _ | x
    · exact ⟨prunedNext_of_stall (by rw [hrun]; exact he),
        by rw [DDE.Total.transcript_freeze he hf'q]⟩
    · by_cases hlen : (DDE.Total.transcript s e f').length < q
      · exfalso
        have hfire : prunedNext e D q
            ((trN (prunedEnv e D q) s q).map Prod.snd) = some x := by
          rw [prunedNext_of_fire (by rw [hrun]; exact he), hrun, if_pos hlen]
        obtain ⟨hdomE, -⟩ := prunedEnv_mem_dom hfire
        have hstall : trN (prunedEnv e D q) s (q + 1) = trN (prunedEnv e D q) s q :=
          trN_stall_of_length_lt _ _ (Nat.lt_of_le_of_lt hlenle hlen)
        exact (trN_succ_eq_iff_of_compatible
          (compatible_prunedEnv e hdom q) q).mp hstall hdomE
      · have hq : q ≤ (DDE.Total.transcript s e f').length := Nat.le_of_not_lt hlen
        have hlenf := DDE.Total.transcript_length_le s e f'
        have hf'eq : f' = q := by omega
        exact ⟨by rw [prunedNext_of_fire (by rw [hrun]; exact he), hrun,
          if_neg hlen], by rw [hf'eq]⟩
  exact ⟨trN_succ_of_stop (prunedEnv_notMem_dom hstop.1),
    htranscript.trans hstop.2⟩

theorem stops_prunedEnv (e : DDE.Total Y X) (hdom : dom s = D) (q : ℕ) :
    Stops (prunedEnv e D q) s :=
  ⟨q, (prunedEnv_settles e hdom q).1⟩

/-- **The pruned interaction, at the law-facing index**: the Definition-2.12
transcript of the pruned environment is the answered part of the Ruling-R4
`q`-round transcript of the original one. -/
theorem tr_prunedEnv_get (e : DDE.Total Y X) (hdom : dom s = D) (q : ℕ)
    (h : Stops (prunedEnv e D q) s) :
    (tr (prunedEnv e D q) s).get h = answeredEntries (DDE.Total.transcript s e q) :=
  (tr_get_eq_trN h (prunedEnv_settles e hdom q).1).trans
    (prunedEnv_settles e hdom q).2

end Pruning

end System

namespace PDS

/-! ## Lanzenberger Definition 2.17: equivalence -/

/-- Lanzenberger **Definition 2.17**, taken over the CR18 total presentation
(Definitions 3.6/3.7): two systems are **equivalent** when they produce the same
transcript law in every total environment, at every interaction length.

Definition 2.17 has two clauses — the systems have the same domain, and their
transcript distributions agree in all environments.  On the fully defined
carrier the domain clause is *subsumed* by the second, which is why only one
clause is written here: the completion `s⊥` answers every query, a refusal
being the observable answer `none` (Ruling R2), so the domain is not a side
condition on the interaction but part of what the transcript reports.  That is
the carrier's reading of the definition, recorded here as the modeling delta;
no theorem below depends on it, and none asserts it.

The definition quantifies over all environments, as the source does;
Lemma 2.18 (`equivalent_iff_nonAdaptive`) shows the non-adaptive ones already
decide it. -/
def equivalent (S T : PDS X Y) : Prop :=
  ∀ (e : System.DDE.Total Y X) (n : ℕ),
    trLawFullyDefined e n S = trLawFullyDefined e n T

/-- Equivalence is reflexive. -/
theorem equivalent_refl (S : PDS X Y) : equivalent S S := fun _ _ => rfl

/-- Equivalence is symmetric. -/
theorem equivalent_symm {S T : PDS X Y} (h : equivalent S T) : equivalent T S :=
  fun e n => (h e n).symm

/-- Equivalence is transitive. -/
theorem equivalent_trans {S T U : PDS X Y}
    (h : equivalent S T) (h' : equivalent T U) : equivalent S U :=
  fun e n => (h e n).trans (h' e n)

/-- Equivalent systems have the same weight: the transcript law is a
pushforward, so it carries the system's weight (`weight_trLawFullyDefined`), and
equivalence equates the transcript laws already at the trivial environment and
length `0`.

This is the cheapest receipt for the hypothesis of `statDist`'s symmetry, which
is why the class distance is symmetric exactly where `Adv⊥` is. -/
theorem weight_eq_of_equivalent {S T : PDS X Y} (h : equivalent S T) :
    S.weight = T.weight := by
  have h0 := h (fun _ => none) 0
  rw [← weight_trLawFullyDefined (fun _ => none) 0 S, h0,
    weight_trLawFullyDefined]

open System in
/-- **Lanzenberger Lemma 2.18: non-adaptive environments suffice.**  Two
systems whose transcript laws agree in every environment *whose queries are
fixed in advance* agree in every environment.

Adaptivity buys the environment nothing here because the transcript law is a
pushforward: the mass the law puts on a prefix value `t` is the mass of the
fiber `{s | tr(s, e, n) = t}`, and by the deterministic factorization
(`System.DDE.Total.transcript_eq_iff_of_consistent`) that fiber does not depend
on the environment once the environment can produce `t` at all — it is cut out
by the system-side condition alone.  So the fiber of the adaptive `e` at `t` is
the fiber of the non-adaptive `playQueries t↓ₓ` at `t`, and a value `t` that
`e` cannot produce carries mass zero on both sides.

The environment *is* free to depend on the answers; what the argument uses is
that having seen `t`'s answers, its remaining queries are determined, so the
whole conditional behaviour collapses to one fixed query list — a different one
for each `t`, which is why the hypothesis must range over all of them. -/
theorem equivalent_of_nonAdaptive {S T : PDS X Y}
    (h : ∀ e : System.DDE.Total Y X, System.DDE.Total.NonAdaptive e →
      ∀ n, trLawFullyDefined e n S = trLawFullyDefined e n T) :
    equivalent S T := by
  intro e n
  ext t
  rw [trLawFullyDefined, trLawFullyDefined,
    Distribution.fTransform_apply_eq_mass, Distribution.fTransform_apply_eq_mass]
  by_cases hE : (∀ k, (hk : k < t.length) →
        e (t.take k)↓ᵧ = some t[k].1) ∧
      (t.length = n ∨ (t.length < n ∧ e t↓ᵧ = none))
  · have hkey := h (System.DDE.Total.playQueries t↓ₓ)
      (System.DDE.Total.nonAdaptive_playQueries _) t.length
    have happ := congrArg (fun d => d t) hkey
    simp only [trLawFullyDefined,
      Distribution.fTransform_apply_eq_mass] at happ
    have hred : ∀ R : PDS X Y,
        R.mass (fun s => System.DDE.Total.transcript s e n = t) =
          R.mass (fun s => System.DDE.Total.transcript s
            (System.DDE.Total.playQueries t↓ₓ) t.length = t) := by
      intro R
      refine congrArg R.mass (funext fun s => propext ?_)
      rw [System.DDE.Total.transcript_eq_iff_of_consistent hE.1 hE.2 s,
        System.DDE.Total.transcript_eq_iff_of_consistent
          (System.DDE.Total.consistent_playQueries t) (Or.inl rfl) s]
    rw [hred S, hred T]
    exact happ
  · have hz : ∀ R : PDS X Y,
        R.mass (fun s => System.DDE.Total.transcript s e n = t) = 0 := by
      intro R
      unfold Distribution.mass
      rw [Finsupp.sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg]
      intro hcontra
      subst hcontra
      exact hE ⟨(System.DDE.Total.transcript_consistent s e n).1.1,
        (System.DDE.Total.transcript_consistent s e n).1.2⟩
    rw [hz S, hz T]

/-- **Lemma 2.18 as a characterization.**  The forward direction is the
definition read at the non-adaptive environments; the backward direction is
`equivalent_of_nonAdaptive`. -/
theorem equivalent_iff_nonAdaptive {S T : PDS X Y} :
    equivalent S T ↔
      ∀ e : System.DDE.Total Y X, System.DDE.Total.NonAdaptive e →
        ∀ n, trLawFullyDefined e n S = trLawFullyDefined e n T :=
  ⟨fun h e _ n => h e n, equivalent_of_nonAdaptive⟩

/-- **`Adv⊥` transports along equivalence, in both slots.**  Immediate from the
definition: every index `(e, n)` of the supremum sees the same pair of
transcript laws.  This is the lemma that lets a proof move to a convenient pair
of representatives and come back. -/
theorem advFullyDefined_congr {S S' T T' : PDS X Y}
    (hS : equivalent S S') (hT : equivalent T T') :
    advFullyDefined S T = advFullyDefined S' T' := by
  refine iSup_congr fun e => iSup_congr fun n => ?_
  rw [hS e n, hT e n]

/-! ## Equivalence under absorption

`Absorb.lean`'s pushforward reduction is stated for `Adv⊥`; equivalence needs
the same two hypotheses read at the *law* rather than at the metric.  The two
lemmas below are that reading — same hypothesis, same `key` computation, with
`statDist`'s estimate replaced by equality of the pushed-forward laws.  They
live here rather than beside `PDS.advFullyDefined_fTransform_le` because
`equivalent` is defined in this file. -/

/-- **Equivalence survives a construction the environment absorbs.**  If every
interaction with `g s` is a fixed post-processing of an interaction with `s`
— uniformly in the deterministic system, which is exactly
`Absorb.lean`'s hypothesis — then equivalent systems stay equivalent under
`g`.  The image transcript law is the pushforward of a source transcript law
the hypothesis already equates. -/
theorem equivalent_fTransform {X' : Type*} {Y' : Type*}
    (g : System.DDS X Y → System.DDS X' Y') {RL SL : PDS X Y}
    (h : ∀ (e : System.DDE.Total Y' X') (n : ℕ),
      ∃ (e' : System.DDE.Total Y X) (m : ℕ)
        (p : List (X × Option Y) → List (X' × Option Y')),
        ∀ s : System.DDS X Y,
          System.DDE.Total.transcript (g s) e n =
            p (System.DDE.Total.transcript s e' m))
    (heq : equivalent RL SL) :
    equivalent (Distribution.fTransform g RL) (Distribution.fTransform g SL) := by
  intro e n
  obtain ⟨e', m, p, hp⟩ := h e n
  have key : ∀ L : PDS X Y,
      trLawFullyDefined e n (Distribution.fTransform g L) =
        Distribution.fTransform p (trLawFullyDefined e' m L) := by
    intro L
    show Distribution.fTransform _ (Distribution.fTransform g L) =
      Distribution.fTransform p (Distribution.fTransform _ L)
    rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    exact congrFun (congrArg Distribution.fTransform (funext hp)) L
  rw [key RL, key SL, heq e' m]

/-- **Equivalence descends through a genuine inclusion.**  The mirror
hypothesis — every interaction with `s` is a fixed post-processing of an
interaction with `g s` — is what an inclusion satisfies, and it says the
construction hides nothing: if the images are equivalent so are the
originals. -/
theorem equivalent_of_equivalent_fTransform {X' : Type*} {Y' : Type*}
    (g : System.DDS X Y → System.DDS X' Y') {RL SL : PDS X Y}
    (h : ∀ (e' : System.DDE.Total Y X) (m : ℕ),
      ∃ (e : System.DDE.Total Y' X') (n : ℕ)
        (q : List (X' × Option Y') → List (X × Option Y)),
        ∀ s : System.DDS X Y,
          System.DDE.Total.transcript s e' m =
            q (System.DDE.Total.transcript (g s) e n))
    (heq : equivalent (Distribution.fTransform g RL)
      (Distribution.fTransform g SL)) :
    equivalent RL SL := by
  intro e' m
  obtain ⟨e, n, q, hq⟩ := h e' m
  have key : ∀ L : PDS X Y,
      trLawFullyDefined e' m L =
        Distribution.fTransform q
          (trLawFullyDefined e n (Distribution.fTransform g L)) := by
    intro L
    show Distribution.fTransform _ L =
      Distribution.fTransform q
        (Distribution.fTransform _ (Distribution.fTransform g L))
    rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    exact congrFun (congrArg Distribution.fTransform (funext hq)) L
  rw [key RL, key SL, heq e n]

/-- **Equivalence transfers through the typed inclusion**, in both directions
— the Definition-2.17 companion of the `Adv⊥` isometry
`PDS.advFullyDefined_ofTyped`.

`→` is the inward absorption (`System.exists_absorb_ofTyped_typed`: the outer
environment encodes what the typed environment asks and decodes what it gets),
`←` the outward one (`System.exists_absorb_ofTyped`: an undecodable query is
refused before any inner traffic, a decodable one is relayed).  Including a
typed system into `Φ` therefore neither merges nor separates equivalence
classes, so `[S]` may be read at either signature. -/
theorem equivalent_ofTyped_iff {X Y : Type u} {RL SL : PDS X Y} :
    equivalent (RandomSystems.ofTyped RL) (RandomSystems.ofTyped SL) ↔
      equivalent RL SL :=
  ⟨equivalent_of_equivalent_fTransform System.ofTyped
    fun e' m => System.exists_absorb_ofTyped_typed e' m,
   equivalent_fTransform System.ofTyped
    fun e n => System.exists_absorb_ofTyped e n⟩

/-! ## Lanzenberger Definition 2.28: the class distance -/

/-- Lanzenberger **Definition 2.28**: the distance between two systems measured
on their equivalence *classes* —

  `Δ(S, T) := inf { δ(S', T') | S' ≡ S, T' ≡ T, S' and T' honest }`,

the infimum, over pairs of **honest** equivalent representatives, of the
statistical distance of the system laws themselves.  This is the static
presentation of the distance: no environment appears in it.

**Ruling R9** (PHI-SPEC.md, R9 — THE CLASS DISTANCE FOLLOWS LANZ): the infimum
is taken over honest representatives, which is Definition 2.28's own carrier —
the thesis's `𝐒`, `𝐓` are classes of *probability* systems, and the definition
never sees a signed law.  *Signed representatives are a proof-technique tool
only — couplings and bounds, never the definition.*  A signed law is still free
to appear inside a proof (as the intermediate law of a coupling argument, say);
what R9 forbids is letting one enter the infimum and lower the distance below
what the thesis defines.

`Distribution.NonNeg` is the honesty clause; normalization is not part of it,
for the same reason it is not part of `advFullyDefined`: equivalence transports
weight (`weight_eq_of_equivalent`), so at a probability system every honest
representative is automatically a probability system, and the theorems that
need `weight = 1` say so.

`equivalent` and `NonNeg` are spelled as *binder conditions* rather than as a
subtype, so that a bound at a chosen pair of representatives is six `iInf_le`
steps (`classDistance_le_statDist_of_equivalent`), a bound *of* `Δ` is six
`le_iInf` steps (`le_classDistance`), and transport along `equivalent` in
either slot is an ordinary two-sided estimate (`classDistance_congr`) rather
than a transport along an equivalence of subtypes.  The two eliminators are the
whole interface; nothing below unfolds this definition. -/
def classDistance (S T : PDS X Y) : ℝ≥0∞ :=
  ⨅ (S' : PDS X Y) (_ : equivalent S S') (_ : S'.NonNeg)
    (T' : PDS X Y) (_ : equivalent T T') (_ : T'.NonNeg),
    ENNReal.ofReal (statDist S' T')

/-- Lanzenberger Definition 2.28 notation: `Δ(S, T)` is the class distance,
alongside `Adv(S, T)` (Definition 2.26) and `Adv⊥(S, T)` (Ruling R4). -/
scoped notation "Δ(" S ", " T ")" => PDS.classDistance S T

/-- **Elimination**: any pair of *honest* equivalent representatives bounds the
class distance.  This is `iInf_le` at the chosen pair, and it is how every upper
bound on `Δ` is proved.

The two honesty clauses are Ruling R9's: a signed pair is no longer a witness,
which is exactly what makes `Δ` the thesis's number.  Where a coupling supplies
the pair, they cost nothing — an honest joint has honest marginals
(`Distribution.IsCoupling.nonNeg_left`). -/
theorem classDistance_le_statDist_of_equivalent {S T S' T' : PDS X Y}
    (hS : equivalent S S') (hT : equivalent T T')
    (hS'nn : S'.NonNeg) (hT'nn : T'.NonNeg) :
    classDistance S T ≤ ENNReal.ofReal (statDist S' T') :=
  iInf_le_of_le S' (iInf_le_of_le hS (iInf_le_of_le hS'nn
    (iInf_le_of_le T' (iInf_le_of_le hT (iInf_le _ hT'nn)))))

/-- **Introduction**: a bound holding at *every* pair of honest equivalent
representatives is a bound below the class distance.  This is `le_iInf`, and it
is how every lower bound on `Δ` is proved.

Ruling R9 makes this eliminator *stronger* than its unrestricted predecessor —
there are fewer representatives to check, and the two honesty clauses arrive as
hypotheses. -/
theorem le_classDistance {S T : PDS X Y} {a : ℝ≥0∞}
    (h : ∀ S' T' : PDS X Y, equivalent S S' → equivalent T T' →
      S'.NonNeg → T'.NonNeg → a ≤ ENNReal.ofReal (statDist S' T')) :
    a ≤ classDistance S T :=
  le_iInf fun S' => le_iInf fun hS' => le_iInf fun hS'nn => le_iInf fun T' =>
    le_iInf fun hT' => le_iInf fun hT'nn => h S' T' hS' hT' hS'nn hT'nn

/-- Two honest systems are a pair of representatives of their own classes, so
the class distance never exceeds the statistical distance of the laws one
started with.  Honesty is Ruling R9's admission ticket to the infimum; for a
signed law the statement is false, the infimum then ranging over a set the law
itself is not in. -/
theorem classDistance_le_statDist (S T : PDS X Y) (hS : S.NonNeg) (hT : T.NonNeg) :
    classDistance S T ≤ ENNReal.ofReal (statDist S T) :=
  classDistance_le_statDist_of_equivalent (equivalent_refl S) (equivalent_refl T)
    hS hT

/-- An honest system is at class distance zero from itself.

The honesty hypothesis is Ruling R9's and it cannot be dropped: on a class with
no honest presentation at all the infimum is empty, and `⨅ ∅ = ⊤` in `ℝ≥0∞`.
That is the definition behaving as the thesis intends — Definition 2.28 is
about classes of probability systems — and it is why this fact is not
`@[simp]`: the side condition is not one `simp` can discharge. -/
theorem classDistance_self {S : PDS X Y} (hS : S.NonNeg) : classDistance S S = 0 :=
  le_antisymm
    (by simpa [Probability.statDist_self] using classDistance_le_statDist S S hS hS)
    (zero_le _)

/-- **`Δ` transports along equivalence, in both slots.**  Definitional in
genre: equivalent systems have the same representatives, so the two infima
range over the same set of pairs; the proof is the two eliminators against each
other, once in each direction. -/
theorem classDistance_congr {S S' T T' : PDS X Y}
    (hS : equivalent S S') (hT : equivalent T T') :
    classDistance S T = classDistance S' T' :=
  le_antisymm
    (le_classDistance fun _ _ hU hV hUnn hVnn =>
      classDistance_le_statDist_of_equivalent (equivalent_trans hS hU)
        (equivalent_trans hT hV) hUnn hVnn)
    (le_classDistance fun _ _ hU hV hUnn hVnn =>
      classDistance_le_statDist_of_equivalent
        (equivalent_trans (equivalent_symm hS) hU)
        (equivalent_trans (equivalent_symm hT) hV) hUnn hVnn)

/-- Symmetry of `Δ` for systems of equal weight — in particular for any two
probability laws.  The hypothesis is exactly the one under which Lanzenberger
Definition 2.4 is symmetric, and it passes to the representatives because
equivalence preserves weight (`weight_eq_of_equivalent`); on the signed carrier
`δ` is one-sided and no unconditional symmetry holds.  This is
`advFullyDefined_comm_of_weight_eq` at the static presentation. -/
theorem classDistance_comm_of_weight_eq (S T : PDS X Y)
    (h : S.weight = T.weight) :
    classDistance S T = classDistance T S := by
  refine le_antisymm (le_classDistance fun T' S' hT' hS' hT'nn hS'nn => ?_)
    (le_classDistance fun S' T' hS' hT' hS'nn hT'nn => ?_)
  · rw [Probability.statDist_symm_of_eq_weight T' S' (by
      rw [← weight_eq_of_equivalent hT', ← weight_eq_of_equivalent hS']
      exact h.symm)]
    exact classDistance_le_statDist_of_equivalent hS' hT' hS'nn hT'nn
  · rw [Probability.statDist_symm_of_eq_weight S' T' (by
      rw [← weight_eq_of_equivalent hS', ← weight_eq_of_equivalent hT']
      exact h)]
    exact classDistance_le_statDist_of_equivalent hT' hS' hT'nn hS'nn

/-! ## The crossing lemmas

The point of the layer: a proof runs in whichever presentation is cheaper and
crosses over here.  `Adv⊥` is below `Δ` unconditionally, so every static bound
is an interactive bound; and `Δ` is bounded by *any* coupling of *any* pair of
equivalent representatives, so a static proof is free to move to whatever pair
makes the coupling easy.

None of the three carries `@[simp]`.  The repository's simp discipline —
visible in `MetricFullyDefined.lean`, whose only marked declaration is the
definitional `edist_def` while every receipt (`edist_apply_le_of_mem_…`) is a
plain theorem — reserves the attribute for normalizing rewrites whose
right-hand side is determined by the left.  Here it is not: `advFullyDefined_congr`
and `classDistance_congr` name the target representatives only in their
hypotheses, so simp could neither instantiate them nor discharge the side
conditions, and the two `≤`-bridges are estimates, not rewrites.  Since Ruling
R9 the same holds of `classDistance_self`, whose honesty side condition simp
cannot discharge either, so this file marks nothing at all. -/

/-- **`Adv⊥ ≤ Δ`, unconditional.**  Interaction cannot separate two systems by
more than the *best* pair of representatives already differs.

The proof is the whole reason both presentations are first class: at any pair
of representatives `S' ≡ S`, `T' ≡ T`, the interactive distance is unchanged
(`advFullyDefined_congr`) while the static distance is `δ(S', T')`, and the R4
bridge (`advFullyDefined_le_statDist`, the data processing inequality at every
environment and length) compares them.  Taking the infimum over pairs is the
last step, so the inequality holds against the *infimum*, not merely against
one representative. -/
theorem advFullyDefined_le_classDistance (S T : PDS X Y) :
    advFullyDefined S T ≤ classDistance S T :=
  le_classDistance fun S' T' hS' hT' _ _ => by
    rw [advFullyDefined_congr hS' hT']
    exact advFullyDefined_le_statDist S' T'

/-- **The coupling method, at the class distance**: a coupling of *any* pair of
equivalent representatives bounds `Δ`.

`iInf_le` at that pair, then Lanzenberger Lemma 2.8
(`Probability.statDist_le_offDiagonalMass`).  The freedom to choose the
representatives is what the static presentation buys: the coupling has to be
built for a convenient pair of laws, not for the pair the statement names.

The non-negativity hypothesis is the signed-carrier caveat inherited from
Lemma 2.8; for probability systems it is automatic.  It is also all that Ruling
R9's two honesty clauses cost here: the coupled pair *is* the pair of marginals
of an honest joint, so `Distribution.IsCoupling.nonNeg_left`/`_right` discharge
them from the hypothesis already present. -/
theorem classDistance_le_offDiagonalMass {S T S' T' : PDS X Y}
    (hS : equivalent S S') (hT : equivalent T T')
    {J : Distribution (System.DDS X Y × System.DDS X Y)}
    (hJ : Distribution.IsCoupling J S' T') (hnn : ∀ p, 0 ≤ J p) :
    classDistance S T ≤ ENNReal.ofReal (Distribution.offDiagonalMass J) :=
  (classDistance_le_statDist_of_equivalent hS hT
      (Distribution.IsCoupling.nonNeg_left hJ hnn)
      (Distribution.IsCoupling.nonNeg_right hJ hnn)).trans
    (ENNReal.ofReal_le_ofReal (Probability.statDist_le_offDiagonalMass hJ hnn))

/-- **Prove static, consume as `Adv⊥`** — the composite crossing, and the
workflow this file exists for.

To bound the interactive distance of `S` and `T`: pick *any* systems `S' ≡ S`,
`T' ≡ T` that are convenient, exhibit a joint law under which they are equal
except on a small event, and the mass of that event bounds `Adv⊥(S, T)`.  No
environment appears anywhere in the argument; the interaction was accounted for
once and for all by the R4 bridge inside `advFullyDefined_le_classDistance`.

This generalizes `advFullyDefined_le_offDiagonalMass` (the B8 endpoint), which
is this statement at the identity representatives — there the coupling had to
be a coupling of `S` and `T` themselves. -/
theorem advFullyDefined_le_offDiagonalMass_of_equivalent {S T S' T' : PDS X Y}
    (hS : equivalent S S') (hT : equivalent T T')
    {J : Distribution (System.DDS X Y × System.DDS X Y)}
    (hJ : Distribution.IsCoupling J S' T') (hnn : ∀ p, 0 ≤ J p) :
    advFullyDefined S T ≤ ENNReal.ofReal (Distribution.offDiagonalMass J) :=
  (advFullyDefined_le_classDistance S T).trans
    (classDistance_le_offDiagonalMass hS hT hJ hnn)

/-! ## The coding map: Definition 2.26 meets the fully defined advantage

Lanzenberger's own advantage is `PDS.Adv` — a supremum over the *compatible,
stopping* environments of Definition 2.11, taken at the stopped transcript.
Ruling R4's `PDS.advFullyDefined` is a supremum over *all* total environments
of CR18 Definition 3.6 and all interaction lengths, taken at the length-`n`
transcript of the completion.  The two index sets are different and neither is
a subset of the other, so the identification is a theorem in both directions,
and only one of them is free. -/

/-- **The embedding half of the coding map**, and it costs nothing:
`Adv(S, T) ≤ Adv⊥(S, T)` on the bare carrier, with no domain and no finiteness
hypothesis.

Every Definition-2.26 witness is a Ruling-R4 witness.  Coding the environment
(`System.DDE.total`) makes the CR18 engine reproduce the Definition-2.12
interaction verbatim on a compatible pair — no query is refused, so no `⊥`
appears (`System.DDE.Total.transcript_total`) — and the interaction *length*
that R4 supplies as an index replaces the stabilization stage that Definition
2.26 waits for.  One length serves the whole law because `Distribution` has
finite support: `N` is the supremum of the stabilization stages over the two
supports, and past its own stage a run stands still (`System.tr_get_eq_trN`).

Both readings are then injective pushforwards of one law over Definition-2.12
transcripts — `Option.some` on one side, `System.markAnswers` on the other —
so the two statistical distances are *equal*, not merely comparable, and the
inequality comes only from the last step, where R4's supremum is taken over
strictly more indices. -/
theorem Adv_le_advFullyDefined (S T : PDS X Y) :
    Adv S T ≤ advFullyDefined S T := by
  classical
  refine iSup_le fun e => ?_
  obtain ⟨⟨hcS, hsS⟩, hcT, hsT⟩ := e.2
  set N : ℕ := (S.support ∪ T.support).sup
    (fun s => if h : System.Stops e.1 s then Nat.find h else 0) with hN
  have hstab : ∀ s ∈ S.support ∪ T.support,
      System.trN e.1 s (N + 1) = System.trN e.1 s N := by
    intro s hs
    have hst : System.Stops e.1 s := by
      rcases Finset.mem_union.mp hs with h | h
      · exact hsS s h
      · exact hsT s h
    have hle : Nat.find hst ≤ N := by
      have hsup := Finset.le_sup
        (f := fun s => if h : System.Stops e.1 s then Nat.find h else 0) hs
      simp only [dif_pos hst] at hsup
      exact hsup
    rw [System.trN_eq_of_le (Nat.find_spec hst) (N + 1) (Nat.le_succ_of_le hle),
      System.trN_eq_of_le (Nat.find_spec hst) N hle]
  have key : ∀ L : PDS X Y, L.support ⊆ S.support ∪ T.support →
      (∀ s ∈ L.support, System.Compatible e.1 s) →
      (∀ s ∈ L.support, System.Stops e.1 s) →
      trLaw e.1 L = Distribution.fTransform Option.some
          (Distribution.fTransform (fun s => System.trN e.1 s N) L) ∧
        trLawFullyDefined (System.DDE.total e.1) N L =
          Distribution.fTransform System.markAnswers
            (Distribution.fTransform (fun s => System.trN e.1 s N) L) := by
    intro L hsub hcomp hstop
    rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    constructor
    · refine Distribution.fTransform_congr L fun s hs => ?_
      show (System.tr e.1 s).toOption = some (System.trN e.1 s N)
      rw [Part.toOption_eq_some_iff]
      exact ⟨hstop s hs,
        System.tr_get_eq_trN (hstop s hs) (hstab s (hsub hs))⟩
    · refine Distribution.fTransform_congr L fun s hs => ?_
      simpa [System.markAnswers] using
        System.DDE.Total.transcript_total e.1 s (hcomp s hs) N
  obtain ⟨hS1, hS2⟩ := key S Finset.subset_union_left hcS hsS
  obtain ⟨hT1, hT2⟩ := key T Finset.subset_union_right hcT hsT
  have hval : statDist (trLaw e.1 S) (trLaw e.1 T) =
      statDist (trLawFullyDefined (System.DDE.total e.1) N S)
        (trLawFullyDefined (System.DDE.total e.1) N T) := by
    rw [hS1, hT1, hS2, hT2,
      Probability.statDist_fTransform_injective _ _ _ (Option.some_injective _),
      Probability.statDist_fTransform_injective _ _ _ System.markAnswers_injective]
  rw [hval]
  exact le_iSup_of_le (System.DDE.total e.1) (le_iSup_of_le N le_rfl)

/-! ### The domain-indexed index set

`PDS.AdvD` (`Environment.lean`) is Definition 2.26 indexed by `dom(S)` — the
attribute Definition 2.14 supplies — instead of by the two supports.  Its index
set is admitted by the *domain*, so the two clauses below are all it takes to
enter Definition 2.26's index set from it, once the systems are known to present
that domain. -/

/-- A domain-compatible environment is compatible with every system presenting
the domain.  This is `System.CompatibleD` read at a `PDS.HasDomain` system, and
it is the definition unfolded once. -/
theorem compatible_of_compatibleD {e : System.DDE Y X} {D : Set (List X)}
    {S : PDS X Y} (he : System.CompatibleD e D) (hS : HasDomain S D) :
    Compatible e S :=
  fun s hs => he s (hS s hs)

/-- A halting environment stops on every system, so in particular on the atoms
of any law (`System.stops_of_halts`).  No domain and no support are read. -/
theorem stops_of_halts {e : System.DDE Y X} (he : System.DDE.Halts e)
    (S : PDS X Y) : Stops e S :=
  fun s _ => System.stops_of_halts he s

/-- **The domain-indexed advantage is below Definition 2.26's**, on the systems
Definition 2.14 admits: every environment the domain admits is an environment
the two systems admit.  Nothing but the two clauses above is used, and no
pruning happens here. -/
theorem AdvD_le_Adv {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) : AdvD D S T ≤ Adv S T :=
  iSup_le fun e =>
    le_iSup_of_le
      ⟨e.1, ⟨compatible_of_compatibleD e.2.1 hS, stops_of_halts e.2.2 S⟩,
        ⟨compatible_of_compatibleD e.2.1 hT, stops_of_halts e.2.2 T⟩⟩ le_rfl

/-- **The pruning half of the coding map**, at the domain-indexed advantage.  On
the systems Lanzenberger Definition 2.14 admits — every deterministic system in
either support presents the *same* domain `D` — Ruling R4's supremum is already
attained on the index set `D` itself admits, so `Adv⊥(S, T) ≤ Adv_D(S, T)`.

The hypothesis is exactly Definition 2.26's own shared-domain clause, and it is
what the statement needs rather than bookkeeping: with one common domain,
*which* queries are refused is a public function of the query history, so a
compatible environment can synthesize every refusal itself and forward only the
queries the domain accepts (`System.prunedEnv`).  Without it the `⊥` channel is
genuinely informative — the total environment reads the support's domain
pattern off the refusals, which no compatible environment can — and the
inequality is false.

That the pruned environment lies in the *domain-indexed* index set is the
sharper reading of the same two receipts: `System.compatible_prunedEnv` is
already stated for every system with domain `D` (which is `System.CompatibleD`
verbatim), and `System.halts_prunedEnv` bounds its rounds by the replay budget
without mentioning a system at all.

There is no finiteness hypothesis and no non-negativity hypothesis: both
suprema live in `ℝ≥0∞`, so neither needs to be bounded above, and the estimate
is the data processing inequality, which is signed-carrier safe.

The proof is one deterministic identity plus one data processing step: the
*unpruned* transcript is recovered from the *pruned* one by running the replay
machine forward (`System.pruneRun_answeredEntries`), so `Adv⊥`'s law at every
`(e, n)` is a fixed post-processing of `Adv_D`'s law at the pruned environment,
and post-processing cannot increase `δ`. -/
theorem advFullyDefined_le_AdvD {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) :
    advFullyDefined S T ≤ AdvD D S T := by
  classical
  refine iSup_le fun e => iSup_le fun n => ?_
  have hmem : System.CompatibleD (System.prunedEnv e D n) D ∧
      System.DDE.Halts (System.prunedEnv e D n) :=
    ⟨fun s hdom => System.compatible_prunedEnv e hdom n,
      System.halts_prunedEnv e D n⟩
  have hlaw : ∀ L : PDS X Y, HasDomain L D →
      trLawFullyDefined e n L =
        Distribution.fTransform
          (fun o : Option (System.Transcript X Y) =>
            (System.pruneRun e D n ((o.getD []).map Prod.snd)).1)
          (trLaw (System.prunedEnv e D n) L) := by
    intro L hL
    show Distribution.fTransform _ L =
      Distribution.fTransform _ (Distribution.fTransform _ L)
    rw [Distribution.fTransform_fTransform]
    refine Distribution.fTransform_congr L fun s hs => ?_
    have hst : System.Stops (System.prunedEnv e D n) s :=
      System.stops_prunedEnv e (hL s hs) n
    have htoOption : (System.tr (System.prunedEnv e D n) s).toOption =
        some (System.answeredEntries (System.DDE.Total.transcript s e n)) := by
      rw [Part.toOption_eq_some_iff]
      exact ⟨hst, System.tr_prunedEnv_get e (hL s hs) n hst⟩
    have hreplay := System.pruneRun_answeredEntries (s := s) e (hL s hs) n []
    rw [List.append_nil] at hreplay
    show System.DDE.Total.transcript s e n = _
    rw [Function.comp_apply, htoOption, Option.getD_some, hreplay]
  rw [hlaw S hS, hlaw T hT]
  refine le_trans
    (ENNReal.ofReal_le_ofReal (Probability.statDist_fTransform_le _ _ _)) ?_
  exact le_iSup_of_le ⟨System.prunedEnv e D n, hmem⟩ le_rfl

/-- **The pruning half of the coding map**, at Definition 2.26 itself:
`Adv⊥(S, T) ≤ Adv(S, T)` on the shared-domain slice.  The pruning is
`advFullyDefined_le_AdvD`, which lands in the domain-indexed index set; this
composes it with the inclusion of that set into Definition 2.26's
(`AdvD_le_Adv`). -/
theorem advFullyDefined_le_Adv_of_dom_eq {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) :
    advFullyDefined S T ≤ Adv S T :=
  (advFullyDefined_le_AdvD hS hT).trans (AdvD_le_Adv hS hT)

/-- **The coding map** (the leg's point): on the shared-domain slice
Lanzenberger Definition 2.26's advantage and Ruling R4's fully defined
advantage are the *same number*.

`≤` is `Adv_le_advFullyDefined`, which is free; `≥` is
`advFullyDefined_le_Adv_of_dom_eq`, which is rejection pruning and is where the
shared-domain clause is spent.  With this, every statement the tree proves
about `Adv⊥` is a statement about Definition 2.26 on the objects the thesis
admits — which is what makes Theorem 2.31's queued half, stated about
Definition 2.26, an obligation about the metric this tree actually carries.

The hypothesis bundle is exactly Definition 2.14's common-domain clause, named
at a single `D` for both systems.  `PDS.HasFixedDomain` is the one-system
existential form of the same clause; it cannot be used here, because two
instances of it give two possibly different domains and the theorem is false
across different domains. -/
theorem advFullyDefined_eq_Adv_of_dom_eq {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) :
    advFullyDefined S T = Adv S T :=
  le_antisymm (advFullyDefined_le_Adv_of_dom_eq hS hT) (Adv_le_advFullyDefined S T)

/-- **The coding map at the domain-indexed advantage**: on the shared-domain
slice all three numbers agree, so `AdvD D` is Ruling R4's metric under another
indexing.  `≤` is the pruning half; `≥` runs through Definition 2.26, whose
index set contains the domain's. -/
theorem advFullyDefined_eq_AdvD {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) :
    advFullyDefined S T = AdvD D S T :=
  le_antisymm (advFullyDefined_le_AdvD hS hT)
    ((AdvD_le_Adv hS hT).trans (Adv_le_advFullyDefined S T))

/-- **Definition 2.26 does not notice the re-indexing.**  On the systems
Definition 2.14 admits, indexing the supremum by the domain and indexing it by
the two supports give the same number — which is what licenses reading every
`Adv` statement of the thesis as a statement about `AdvD`, where it descends to
Notation 2.19's classes. -/
theorem AdvD_eq_Adv {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) : AdvD D S T = Adv S T :=
  (advFullyDefined_eq_AdvD hS hT).symm.trans (advFullyDefined_eq_Adv_of_dom_eq hS hT)

/-! ### The descent: Definition 2.26 at the domain is a class invariant

The taxonomy of LEDGER.md's Adv-descent paragraph, discharged.  `Adv` is not
visible as a function of the two behaviours because its index set is cut out by
the *supports*; `AdvD`'s is cut out by the domain, and on it the Definition-2.12
transcript law is a fixed post-processing of a Definition-3.7 transcript law —
which Definition 2.17 equates.  Both halves of that are unconditional, so the
congruence is too, and `PDS.Behaviour.AdvD` (`Behaviour.lean`) is its quotient. -/

/-- **A halting environment's transcript law is a class invariant.**  For an
environment with a round bound, the Definition-2.12 transcript law is the
Definition-3.7 transcript law at that bound, post-processed by a fixed map:
halting supplies one stage at which the interaction with *every* system has
stabilized (`System.stops_of_halts`), and at that stage the stopped transcript
is the answered part of the coded run
(`System.DDE.Total.answeredEntries_transcript_total_of_total`, which needs no
compatibility).  Equivalence equates the latter law, hence the former.

This is Notation 2.19's observation — `tr(𝐒, e)` depends only on the class —
proved where the thesis assumes it, and the hypothesis it needs is the honest
residue of the thesis's global finiteness: the environment must stop. -/
theorem trLaw_congr_of_halts {e : System.DDE Y X} (he : System.DDE.Halts e)
    {S S' : PDS X Y} (h : equivalent S S') : trLaw e S = trLaw e S' := by
  classical
  obtain ⟨N, hN⟩ := he
  have key : ∀ L : PDS X Y,
      trLaw e L =
        Distribution.fTransform
          (fun t : List (X × Option Y) => some (System.answeredEntries t))
          (trLawFullyDefined (System.DDE.total e) N L) := by
    intro L
    show Distribution.fTransform _ L =
      Distribution.fTransform _ (Distribution.fTransform _ L)
    rw [Distribution.fTransform_fTransform]
    refine Distribution.fTransform_congr L fun s _ => ?_
    show (System.tr e s).toOption = _
    rw [Function.comp_apply, Part.toOption_eq_some_iff]
    refine ⟨⟨N, System.trN_succ_eq_of_halts_bound hN s⟩, ?_⟩
    rw [System.tr_get_eq_trN _ (System.trN_succ_eq_of_halts_bound hN s),
      System.DDE.Total.answeredEntries_transcript_total_of_total]
  rw [key S, key S', h (System.DDE.total e) N]

/-- **`Adv_D` transports along equivalence, in both slots** — with no
hypothesis, which is the point.  Every index of the supremum is an environment
the *domain* admits, so the index set is the same for the two pairs, and at each
index the transcript laws agree by `trLaw_congr_of_halts`.  Nothing
presentation-bound is read: not a support, not a sign, not a weight.

Contrast `PDS.Adv`, whose index set names the two systems; there the same
statement is not available, and that difference is the whole content of the
re-indexing. -/
theorem AdvD_congr {S S' T T' : PDS X Y} {D : Set (List X)}
    (hS : equivalent S S') (hT : equivalent T T') :
    AdvD D S T = AdvD D S' T' :=
  iSup_congr fun e => by
    rw [trLaw_congr_of_halts e.2.2 hS, trLaw_congr_of_halts e.2.2 hT]

/-! ### Queued: the finite-slice half (Lanzenberger Theorem 2.31)

`advFullyDefined_le_classDistance` is one half of Theorem 2.31, and it is the
half that holds outright.  The other half —

  `classDistance S T = advFullyDefined S T`,

with attainment, on the finite shared-domain slice — is **supplied** by
`Attainment.lean`
(`PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded` and its
attainment half), which is where the query induction, Lemma 2.33 and Notation
2.34's successor calculus live.  What this file owes it is exactly the coding
map above: the equality is stated about Ruling R4's metric, and
`advFullyDefined_eq_Adv_of_dom_eq` is what makes it a statement about Definition
2.26, the form the thesis states
(`PDS.classDistance_eq_Adv_of_commonDomain_bounded`).

Theorem 2.32, the coupling theorem for random systems, is Theorem 2.31 composed
with Lemma 2.8; its second half is already in the tree
(`Probability.exists_coupling_offDiagonalMass_eq`), and the inequality direction
a proof actually consumes is `advFullyDefined_le_offDiagonalMass_of_equivalent`
above. -/

end PDS

end

end RandomSystems

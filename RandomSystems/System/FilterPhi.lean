/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.AttachEngineFully

/-!
# CR18 Definition 3.10's filter `[q]` at Φ

The query-limit filter is a DDS operation (`System.filterQueries`, CR18
Definition 3.10: "`[q]s` is the system `s` restricted to `q` queries and is
undefined as of the `(q+1)`-st query").  This module lifts it to Φ by the
pushforward, exactly as `block` lifts `System.blockSet`, and discharges the
receipt the lift owes.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v

variable {X : Type u} {Y : Type v}

/-! ## The deletion pass through the filter -/

/-- The deletion pass of a query-limited system is the unlimited system's pass,
truncated at the budget: the two passes accept the same queries until `q` of
them have been accepted, after which the filter refuses everything and refusals
are deleted (CR18 Definition 3.3), so the kept prefix stops growing. -/
theorem keptPrefix_filterQueries (q : ℕ) (S : DDS X Y) (l : List X) :
    keptPrefix (filterQueries q S) l = (keptPrefix S l).take q := by
  induction l using List.reverseRecOn with
  | nil => simp [keptPrefix]
  | append_singleton l x ih =>
      rw [keptPrefix_append_singleton, keptPrefix_append_singleton, ih]
      by_cases hlt : (keptPrefix S l).length < q
      · have htake : (keptPrefix S l).take q = keptPrefix S l :=
          List.take_of_length_le (le_of_lt hlt)
        rw [htake]
        by_cases hd : keptPrefix S l ++ [x] ∈ dom S
        · rw [if_pos hd, if_pos (show keptPrefix S l ++ [x] ∈ dom (filterQueries q S) from
            ⟨hd, by simp; omega⟩)]
          exact (List.take_of_length_le (by simp; omega)).symm
        · rw [if_neg hd, if_neg (fun hc => hd hc.1), htake]
      · have hlt := Nat.not_lt.mp hlt
        have hlen : ((keptPrefix S l).take q).length = q := by
          simp [List.length_take, min_eq_left hlt]
        rw [if_neg (fun hc => by
          have := (mem_dom_filterQueries q S _).mp hc |>.2
          simp only [List.length_append, List.length_cons, List.length_nil, hlen] at this
          omega)]
        by_cases hd : keptPrefix S l ++ [x] ∈ dom S
        · rw [if_pos hd, List.take_append_of_le_length hlt]
        · rw [if_neg hd]

/-- **The filter's answer**: the query-limited system answers as the system
does while the budget is unspent, and refuses afterwards.  The budget is
measured by the kept prefix — refused attempts are deleted and do not count
(CR18 Definition 3.3), which is the sense in which `[q]` restricts the number
of *answered* queries. -/
theorem answer_filterQueries (q : ℕ) (S : DDS X Y) (l : List X) (x : X) :
    answer (filterQueries q S) l x =
      if (keptPrefix S l).length < q then answer S l x else none := by
  rw [answer_eq, answer_eq, keptPrefix_filterQueries]
  by_cases hlt : (keptPrefix S l).length < q
  · have htake : (keptPrefix S l).take q = keptPrefix S l :=
      List.take_of_length_le (le_of_lt hlt)
    rw [if_pos hlt, htake]
    by_cases hd : keptPrefix S l ++ [x] ∈ dom S
    · rw [dif_pos (show keptPrefix S l ++ [x] ∈ dom (filterQueries q S) from
        ⟨hd, by simp; omega⟩), dif_pos hd]
      rfl
    · rw [dif_neg (fun hc => hd hc.1), dif_neg hd]
  · have hlt := Nat.not_lt.mp hlt
    have hlen : ((keptPrefix S l).take q).length = q := by
      simp [List.length_take, min_eq_left hlt]
    rw [if_neg (by omega), dif_neg (fun hc => by
      have := (mem_dom_filterQueries q S _).mp hc |>.2
      simp only [List.length_append, List.length_cons, List.length_nil, hlen] at this
      omega)]

/-! ## The answers seen through the filter -/

/-- The answer stream of a query-limited interaction: the first `q` answers
pass, and every later query is refused.  Refusals do not consume the budget —
CR18 Definition 3.3 deletes them — so the count is over answers, matching
`keptPrefix`.

This is the post-processing through which an interaction with `[q]s` is an
interaction with `s`: it is the only data the reduction below needs, and it is
computed from the answer list alone, never from the system. -/
def refuseAfter : ℕ → List (Option Y) → List (Option Y)
  | _, [] => []
  | q, none :: t => none :: refuseAfter q t
  | 0, some _ :: t => none :: refuseAfter 0 t
  | q + 1, some y :: t => some y :: refuseAfter q t

@[simp] theorem refuseAfter_nil (q : ℕ) : refuseAfter q ([] : List (Option Y)) = [] := rfl

@[simp] theorem refuseAfter_length (q : ℕ) (ys : List (Option Y)) :
    (refuseAfter q ys).length = ys.length := by
  induction ys generalizing q with
  | nil => rfl
  | cons o t ih =>
      cases o with
      | none => simp [refuseAfter, ih]
      | some y => cases q with
        | zero => simp [refuseAfter, ih]
        | succ q => simp [refuseAfter, ih]

/-- One more round of a query-limited interaction: the answer passes while the
budget is unspent and is refused afterwards.  The budget is counted by the
answers already given, which is what `Option.isSome` counts. -/
theorem refuseAfter_append_singleton (q : ℕ) (ys : List (Option Y)) (o : Option Y) :
    refuseAfter q (ys ++ [o]) =
      refuseAfter q ys ++ [if ys.countP Option.isSome < q then o else none] := by
  induction ys generalizing q with
  | nil =>
      cases o with
      | none => cases q <;> simp [refuseAfter]
      | some y => cases q <;> simp [refuseAfter]
  | cons a t ih =>
      cases a with
      | none => simp [refuseAfter, ih]
      | some y => cases q with
        | zero => simp [refuseAfter, ih]
        | succ q =>
            simp only [List.cons_append, refuseAfter, ih, List.countP_cons,
              Option.isSome_some, List.cons_append]
            simp

/-- The answered queries of a transcript are counted by its answer stream. -/
theorem length_answeredQueries (t : List (X × Option Y)) :
    (answeredQueries t).length = (t↓ᵧ).countP Option.isSome := by
  induction t with
  | nil => rfl
  | cons p t ih =>
      rcases p with ⟨x, _ | y⟩ <;>
        simpa [answeredQueries, transcriptOutputs, List.countP_cons] using ih

/-! ## The filter absorbs into the environment -/

/-- **The query-limited interaction, computed.**  An interaction with `[q]s` is
the interaction of the *same* environment with `s`, read through `refuseAfter q`:
the environment's queries are unchanged and its answers are the system's until
the budget is spent, refusals afterwards.

The absorbing environment is `fun ys => e (refuseAfter q ys)` — `e` fed the
view it would have had behind the filter.  It depends on `e` and `q` only, never
on the system, which is what makes the reduction below a reduction. -/
theorem transcript_filterQueries (q : ℕ) (s : DDS X Y) (e e' : DDE.Total Y X)
    (he' : ∀ ys, e' ys = e (refuseAfter q ys)) (n : ℕ) :
    DDE.Total.transcript (filterQueries q s) e n =
      List.zip (DDE.Total.transcript s e' n)↓ₓ
        (refuseAfter q (DDE.Total.transcript s e' n)↓ᵧ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlen : ((DDE.Total.transcript s e' n)↓ₓ).length =
          (refuseAfter q (DDE.Total.transcript s e' n)↓ᵧ).length := by
        simp [transcriptInputs, transcriptOutputs]
      have hx : (DDE.Total.transcript (filterQueries q s) e n)↓ₓ =
          (DDE.Total.transcript s e' n)↓ₓ := by
        rw [ih]; exact List.map_fst_zip (le_of_eq hlen)
      have hy : (DDE.Total.transcript (filterQueries q s) e n)↓ᵧ =
          refuseAfter q (DDE.Total.transcript s e' n)↓ᵧ := by
        rw [ih]; exact List.map_snd_zip (le_of_eq hlen.symm)
      have henv : e' ((DDE.Total.transcript s e' n)↓ᵧ) =
          e ((DDE.Total.transcript (filterQueries q s) e n)↓ᵧ) := by
        rw [he', hy]
      rcases hstop : e ((DDE.Total.transcript (filterQueries q s) e n)↓ᵧ) with _ | x
      · rw [DDE.Total.transcript_succ_of_stop _ _ hstop,
          DDE.Total.transcript_succ_of_stop _ _ (henv.trans hstop)]
        exact ih
      · rw [DDE.Total.transcript_succ_of_query _ _ hstop,
          DDE.Total.transcript_succ_of_query _ _ (henv.trans hstop),
          transcriptInputs_concat, transcriptOutputs_concat,
          refuseAfter_append_singleton, List.zip_append hlen, ← ih]
        refine congrArg (_ ++ ·) ?_
        have hcount : (keptPrefix s (DDE.Total.transcript (filterQueries q s) e n)↓ₓ).length =
            ((DDE.Total.transcript s e' n)↓ᵧ).countP Option.isSome := by
          rw [hx, ← DDE.Total.answeredQueries_transcript, length_answeredQueries]
        rw [List.zip_cons_cons, List.zip_nil_right, answer_filterQueries, hcount, hx]

/-- **The filter absorbs**: every interaction with a query-limited system is a
fixed post-processing of an interaction with the bare system, uniformly in the
system.  This is the receipt the `[q]` row of the ledger owed
(`filterDom, filterQueries | PENDING`), in the shape
`PDS.advFullyDefined_fTransform_le` consumes.

The filter refuses *before* any inner traffic — the budget test reads the
answers already given, not the system's next answer — which is the criterion the
B4 counterexample turns on, and it is why the receipt exists at all. -/
theorem exists_absorb_filterQueries (q : ℕ) (e : DDE.Total Y X) (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (X × Option Y)),
      ∀ s : DDS X Y,
        DDE.Total.transcript (filterQueries q s) e n =
          p (DDE.Total.transcript s e' m) :=
  ⟨fun ys => e (refuseAfter q ys), n,
    fun T => List.zip T↓ₓ (refuseAfter q T↓ᵧ),
    fun s => transcript_filterQueries q s e _ (fun _ => rfl) n⟩

/-- The empty budget is the total block: `[0]s` answers nothing, and so does
`s` with every query silenced.  (`[]` is out of every system's domain, so both
sides are the nowhere-defined system.) -/
theorem filterQueries_zero (S : DDS X Y) :
    filterQueries 0 S = blockSet (Set.univ : Set X) S := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨hdom, hlen⟩
    exact ⟨hdom, fun x hx => absurd (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen) ▸ hx)
      (by simp)⟩
  · rintro ⟨hdom, hno⟩
    refine ⟨hdom, ?_⟩
    rcases l with _ | ⟨x, t⟩
    · simp
    · exact absurd (hno x (by simp)) (by simp)

/-- Consecutive query limits merge into the smaller one. -/
theorem filterQueries_filterQueries (q q' : ℕ) (S : DDS X Y) :
    filterQueries q (filterQueries q' S) = filterQueries (min q q') S := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨⟨hdom, h'⟩, h⟩
    exact ⟨hdom, le_min h h'⟩
  · rintro ⟨hdom, h⟩
    exact ⟨⟨hdom, h.trans (min_le_right q q')⟩, h.trans (min_le_left q q')⟩

end

end System

/-! ## The filter at Φ

The Φ-level lift, in the `block` idiom: a DDS operation pushed forward along
`Distribution.fTransform`.  CR18 §3.4.3 makes `[q]` a converter, and §5.5's
parameterized resources are cut from an unbounded resource by a family of such
filters (Definition 5.11, Example 5.2: "`[r]` is the special case of a filter
restricting access to `r` queries").  The abstract statement form those
instantiate is `AbstractCryptography.ParameterizedConstruction`. -/

noncomputable section

universe u

/-- **CR18 Definition 3.10's filter `[q]` at Φ**: the query limit applied to
the resource, pushed forward along the distribution.  The Φ-level counterpart
of `System.filterQueries`, exactly as `block` is the Φ-level counterpart of
`System.blockSet`. -/
def filterQueries (q : ℕ) : Function.End Phi.{u} :=
  Probability.Distribution.fTransform (System.filterQueries q)

/-- Query limits merge into the smaller one: Σ-composition of `[q]`s is one
`[q]`.  The filters therefore form a commutative family of Φ-endomorphisms,
which is what CR18 Definition 5.11's `{φ_r}_{r∈𝒵}` asks of a parameterized
family. -/
theorem filterQueries_filterQueries (q q' : ℕ) :
    filterQueries.{u} q * filterQueries.{u} q' = filterQueries.{u} (min q q') := by
  funext R
  show Probability.Distribution.fTransform (System.filterQueries q)
    (Probability.Distribution.fTransform (System.filterQueries q') R) = _
  rw [Probability.Distribution.fTransform_fTransform]
  exact congrFun (congrArg _
    (funext fun S => System.filterQueries_filterQueries q q' S)) R

/-- Query limits always commute. -/
theorem filterQueries_actCommute (q q' : ℕ) :
    AbstractCryptography.ActCommute Phi.{u} (filterQueries.{u} q) (filterQueries.{u} q') := by
  intro S
  show (filterQueries.{u} q * filterQueries.{u} q') S
    = (filterQueries.{u} q' * filterQueries.{u} q) S
  rw [filterQueries_filterQueries, filterQueries_filterQueries, min_comm]

/-- The empty budget is the total block, at Φ: `[0]` is the `⊣` of MauRen16
§3.4 at the whole query set, hence a generator of the metric-facing Σ
(`block_mem_converterMonoidAt`).  This is the only budget the register's
routed precedent covers.

**What is argued below, and what is not.**  The route the register proposed for
`q ≥ 1` — "membership in `converterMonoidAt`, with the `block Q` generator as
the precedent" — does not go through at the generator level, and the argument
against it is this prose, not a theorem in this file.

*Argued* — the **attachment family at an owned query**.  Take `q ≥ 1` and an
attachment `attachAt i E` with the family's own side conditions
(`InnerTotal E`, `AnswersWithinUniformBudget E`).  At the empty history
(`reachedAt_nil`) and for `q ∈ i`, `attachEngineFully_refusal_first` reads the
composite's first-query domain as `[Sum.inl q] ∈ dom E`: **free of the
resource**, so the composite answers or refuses by the engine alone.  The
filter does the opposite — `answer_filterQueries` at `l = []` and `q ≥ 1` gives
`answer ([q]S) [] x = answer S [] x`, i.e. it inherits the resource's own
refusal at the very first query.  Point masses separate the two
Φ-endomorphisms, so no owned attachment is `[q]`.

*Not argued anywhere in this tree* — the other three generator families of
`converterMonoidAt` (`AttachEngineFully.lean`): `block Q` (which refuses by the
*query*, not by a count), `fun RL => par c RL TL` and its mirror, and the
attachment at `i = ∅` (every query foreign, where the governing lemma is
`attachEngineFully_transparent`, not `_refusal_first`).  Each looks
straightforwardly excluded; none is excluded here.

*Status* — **closure-level membership is OPEN**: `converterMonoidAt` is a
`Submonoid.closure`, and nothing above or below speaks about products of
generators.  Neither membership nor non-membership of `filterQueries q`,
`q ≥ 1`, is claimed.

**Why the open residue is not cosmetic.**  The landed nonexpansion
(`filterQueries_mem_nonexpandingConverters`) puts every `[q]` in
`nonexpandingConverters`, which carries `IsNonexpandingSMul` and contains
`converterMonoidAt`, so the ε-relaxation calculus (CR18 Definition 5.11 /
eq. (5.6)) is statable with `φ_r := [r]` at that Σ.  It does **not** restore
the construction and interface layers: `converterMonoidWithin` is a
`Submonoid ↥converterMonoidAt` (`StarFullyDefined.lean`), and `Relaxation.star`,
`Φ_E`, MauRen16 Lemma 3, `Constructs`, `blockConverterAt`,
`Par ↥converterMonoidAt` and the interface-role algebra (`Interface.lean`) are
typed at `↥converterMonoidAt` and at nothing else.  A filter outside that
monoid cannot be a `π` in any of them.  Since CR18 §5.5's `ψ_r` is exactly a
filter restricting a *distinguisher's* access, the residue is live, and
nonexpansion alone does not close it. -/
theorem filterQueries_zero : filterQueries.{u} 0 = block.{u} Set.univ := by
  funext R
  exact congrFun (congrArg _ (funext fun S => System.filterQueries_zero S)) R

theorem filterQueries_zero_mem_converterMonoidAt :
    filterQueries.{u} 0 ∈ converterMonoidAt.{u} :=
  filterQueries_zero ▸ block_mem_converterMonoidAt Set.univ

/-- **The filter never helps a distinguisher.**  Whatever an environment learns
from a query-limited resource it learns from the resource itself: it runs the
budget test on the answers it has already received and refuses on its own
behalf (`System.exists_absorb_filterQueries`), through the pushforward
reduction.

This is the metric receipt CR18 §3.4.3's filter row owed, and it is what makes
`[q]` admissible wherever `MauRen16` Definition 2 is what is being asked for. -/
theorem filterQueries_mem_nonexpandingConverters (q : ℕ) :
    filterQueries.{u} q ∈ nonexpandingConverters.{u} := fun RL SL =>
  PDS.advFullyDefined_fTransform_le (System.filterQueries q) RL SL
    fun e n => System.exists_absorb_filterQueries q e n

end

end RandomSystems

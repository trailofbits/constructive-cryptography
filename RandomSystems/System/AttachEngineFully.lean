/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ConnectFullyDefined

/-!
# Interface-local attachment by ownership dispatch (MauRen16 §3.3's `αⁱ`)

MauRen16 §3.3's attachment primitive is *interface-indexed*: `αⁱ : Φ → Φ`
attaches the converter `α` at the interface `i` and leaves the rest of the
object alone.  `System.connectFully` — the migrated whole-face application of
CR18 Definition 3.9 — is the special case where the converter owns everything,
and every Φ-level object above it inherited that whole face.  This module
supplies the interface-indexed primitive directly.

## Why the dispatch is in the definition and not in a wrapper engine

The obvious repair is to keep whole-face application and wrap the engine: a
relay engine that serves the queries of `i` through `E` and forwards every
other outer query as its own single request.  That design is **refuted** — the
closing section of `ConnectFullyDefined.lean` records both witnesses.  A relayed
round has already issued its request when the completion answers `⊥`, so it
cannot refuse; it must *render* `⊥` as some designated token, and the rendering
is observable on both faces: the inner face of one attachment sees the other's
rendering rather than the raw completion, and a refusal that the composite
would delete (CR18 Definition 3.3) becomes a defined answer that it keeps.

`attachEngineFully` does not render anything, because a query outside `i` is
never relayed *through an engine* at all — the definition dispatches on
ownership and hands the query to the resource, so the composite's value at that
query **is** the resource's value, refusals included.  That is
`attachEngineFully_transparent`, and it is exactly where the two G1 witnesses
die: there is no token to disagree about, and a refusal outside `i` stays a
refusal.

## The two genres in one definition

* a query outside `i` is the *relay* genre — one resource query per outer
  query, its answer returned verbatim, its refusal preserved;
* a query inside `i` is the *engine* genre — a CR18 Definition 3.9 round
  resolved against the completion `R⊥`, whose requests are appended to the same
  resource history (`Converter.DDC.resolve`, reused verbatim).

Both genres write into one resource history, kept in the raw form
`connectFully` uses: every query the resource is *asked* is recorded, and CR18
Definition 3.3's deletion pass (`keptPrefix`) is applied when the resource is
read.  That is what makes the two faces agree — an `i`-round's request and a
foreign query are the same kind of event for the resource.

## Presentation: a resolved-round relation, not a scan

The reached state is a **relation** (`ReachedAt`), read off the interpreter's
own partial drive, rather than a `foldl` scan in the style of `keptPrefix`.
The reason is forced by the mathematics: an `i`-round is a least fixed point
and may fail to resolve, so no total function on histories computes the state
the composite has reached.  Uniqueness — the only property a scan would have
bought — is free from partiality (`ReachedAt.unique`).
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical
open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve driveFrom)

universe u

/-! ## The engine class owed by an interface-local attachment -/

/-- **The engine's inside face connects to `i`** (coinage, flagged): every
request the engine can emit carries an address in `i`.

This is the clause MauRen16 §3.3 needs and CR18 Definition 3.8 does not state:
`InnerTotal`, `AnswersWithinBudget` and `AnswersWithinUniformBudget` are
conditions on how the engine *reacts*, and are orthogonal to this one, which
says where it *reaches*.  It is what confines two attachments at disjoint
interfaces to disjoint parts of the resource history, and so what the
commutation `(αR)β = α(Rβ)` will consume. -/
def RequestsWithin (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) : Prop :=
  ∀ (l : List (Uni.{u} ⊕ Option Uni.{u})) (x : Uni.{u}), Sum.inr x ∈ E.1 l → x ∈ i

/-! ## One composite round — the ownership dispatch itself -/

/-- **One round of the interface-local composite**, dispatched on ownership.

* `q ∈ i`: the converter owns the query, so the round is CR18 Definition 3.9's
  inner resolution of `E` against the completion `R⊥`, started at the reached
  converter conversation and resource history.
* `q ∉ i`: the resource owns the query, so the round *is* the resource's own
  step — undefined exactly where the resource declines, which is how refusal
  preservation gets into the definition rather than into a hypothesis.  The
  resource is read at its kept prefix (CR18 Definition 3.3), because the
  history threaded here is the raw list of everything it was asked. -/
def attachEngineFullyRound (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u})
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) (q : Uni.{u}) :
    Part (Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u})) :=
  if q ∈ i then
    resolve (ofEngine E) R (st.1 ++ [Sum.inl (InLabel.outside, q)], st.2)
  else
    (R.1 (keptPrefix R st.2 ++ [q])).map fun y => (y, (st.1, st.2 ++ [q]))

/-- The owned branch: the round is the engine's, against `R⊥`. -/
theorem attachEngineFullyRound_mem {i : Set Uni.{u}}
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u})
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) {q : Uni.{u}} (hq : q ∈ i) :
    attachEngineFullyRound i E R st q =
      resolve (ofEngine E) R (st.1 ++ [Sum.inl (InLabel.outside, q)], st.2) :=
  if_pos hq

/-- The foreign branch: the round is the resource's own step. -/
theorem attachEngineFullyRound_not_mem {i : Set Uni.{u}}
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u})
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) {q : Uni.{u}} (hq : q ∉ i) :
    attachEngineFullyRound i E R st q =
      (R.1 (keptPrefix R st.2 ++ [q])).map fun y => (y, (st.1, st.2 ++ [q])) :=
  if_neg hq

/-! ## The outer iteration -/

/-- The outer iteration of the interface-local composite: feed the outer
queries one after another, threading the converter conversation and the
resource history through `attachEngineFullyRound`, and collect the outer
answers.  Structural recursion on the outer history; the only fixed point is
the one inside an owned round. -/
def attachEngineFullyDrive (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    (List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) → List Uni.{u} →.
      (List Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u}))
  | st, [] => Part.some ([], st)
  | st, q :: rest =>
      (attachEngineFullyRound i E R st q).bind fun r =>
        (attachEngineFullyDrive i E R r.2 rest).map fun rr => (r.1 :: rr.1, rr.2)

variable {i : Set Uni.{u}} {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
  {R : DDS Uni.{u} Uni.{u}}

/-- Each completed round produces exactly one outer answer. -/
theorem attachEngineFullyDrive_length (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u})
    (us : List Uni.{u}) {r : List Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u})}
    (h : r ∈ attachEngineFullyDrive i E R st us) : r.1.length = us.length := by
  induction us generalizing st r with
  | nil =>
      simp only [attachEngineFullyDrive, Part.mem_some_iff] at h
      subst h; simp
  | cons q rest ih =>
      simp only [attachEngineFullyDrive, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r', _hr', rr, hrr, rfl⟩ := h
      simp [ih r'.2 hrr]

/-- The outer iteration splits over a concatenation: drive the prefix, then
drive the suffix from the state it reaches. -/
theorem attachEngineFullyDrive_append (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u})
    (a b : List Uni.{u}) :
    attachEngineFullyDrive i E R st (a ++ b) =
      (attachEngineFullyDrive i E R st a).bind fun ra =>
        (attachEngineFullyDrive i E R ra.2 b).map fun rb => (ra.1 ++ rb.1, rb.2) := by
  induction a generalizing st with
  | nil =>
      simp only [List.nil_append, attachEngineFullyDrive, Part.bind_some]
      refine (Part.map_id' ?_ _).symm
      intro rb; rfl
  | cons q rest ih =>
      simp only [List.cons_append, attachEngineFullyDrive, ih, Part.bind_assoc,
        Part.bind_map, Part.map_bind, Part.map_map, Function.comp_def, List.cons_append]

/-! ## The composite -/

/-- The interface-local composite as a raw partial function: replay the outer
history from empty state and return the last round's outer answer. -/
def attachEngineFullyRaw (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    Raw Uni.{u} Uni.{u} :=
  fun us => (attachEngineFullyDrive i E R ([], []) us).bind fun r =>
    match r.1.getLast? with
    | some v => Part.some v
    | none => Part.none

/-- **`attachEngineFully`** — MauRen16 §3.3's `αⁱ` on the fully defined
carrier: attach the engine `E` at the interface `i` of the resource `R`, by
ownership dispatch.

A query outside `i` reaches `R` verbatim — the composite is defined there
exactly when `R` is, with `R`'s own answer, so nothing outside `i` is rendered,
delayed or intercepted (`attachEngineFully_transparent`).  A query inside `i`
runs one CR18 Definition 3.9 round of `E` against `R⊥`, so the resource can
never kill a round and the composite's refusals inside `i` are the engine's own
(`attachEngineFully_refusal_first`).

Whole-face application (`connectFully`) is the special case `i = Set.univ`. -/
def attachEngineFully (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    DDS Uni.{u} Uni.{u} :=
  ⟨attachEngineFullyRaw i E R, by
    refine ⟨?_, ?_⟩
    · rw [PFun.mem_dom]
      rintro ⟨v, hv⟩
      simp [attachEngineFullyRaw, attachEngineFullyDrive] at hv
    · intro l₁ l₂ hpre hne hdom
      obtain ⟨suf, rfl⟩ := hpre
      rw [PFun.mem_dom] at hdom
      obtain ⟨v, hv⟩ := hdom
      simp only [attachEngineFullyRaw, Part.mem_bind_iff] at hv
      obtain ⟨r, hr, -⟩ := hv
      rw [attachEngineFullyDrive_append, Part.mem_bind_iff] at hr
      obtain ⟨ra, hra, -⟩ := hr
      have hlen : ra.1.length = l₁.length := attachEngineFullyDrive_length ([], []) l₁ hra
      have hne1 : ra.1 ≠ [] := by
        intro hnil
        exact hne (List.eq_nil_of_length_eq_zero (by rw [← hlen, hnil, List.length_nil]))
      rw [PFun.mem_dom]
      refine ⟨ra.1.getLast hne1, ?_⟩
      simp only [attachEngineFullyRaw, Part.mem_bind_iff]
      refine ⟨ra, hra, ?_⟩
      rw [List.getLast?_eq_some_getLast hne1]
      exact Part.mem_some _⟩

@[simp]
theorem attachEngineFully_toPFun (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    (attachEngineFully i E R).1 = attachEngineFullyRaw i E R := rfl

/-- Membership in the composite: the outer history replays to an answer list
ending in `v`. -/
theorem mem_attachEngineFullyRaw_iff (us : List Uni.{u}) (v : Uni.{u}) :
    v ∈ attachEngineFullyRaw i E R us ↔
      ∃ r ∈ attachEngineFullyDrive i E R ([], []) us, r.1.getLast? = some v := by
  simp only [attachEngineFullyRaw, Part.mem_bind_iff]
  refine exists_congr fun r => and_congr_right fun _ => ?_
  cases r.1.getLast? with
  | none => simp
  | some w => simp [Part.mem_some_iff, eq_comm]

/-! ## The reached state -/

/-- The interpreter state the composite has reached on an outer history: the
converter conversation and the resource history after those rounds.

A relation rather than a scan, because an owned round is a least fixed point
and may fail to resolve; see the module docstring. -/
def ReachedAt (i : Set Uni.{u}) (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}))
    (R : DDS Uni.{u} Uni.{u}) (us : List Uni.{u})
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) : Prop :=
  ∃ vs, (vs, st) ∈ attachEngineFullyDrive i E R ([], []) us

theorem reachedAt_nil (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    ReachedAt i E R [] ([], []) :=
  ⟨[], Part.mem_some _⟩

/-- Reached states are unique: the interpreter is a partial function. -/
theorem ReachedAt.unique {us : List Uni.{u}}
    {st st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (h : ReachedAt i E R us st) (h' : ReachedAt i E R us st') : st = st' := by
  obtain ⟨vs, hvs⟩ := h
  obtain ⟨vs', hvs'⟩ := h'
  exact congrArg Prod.snd (Part.mem_unique hvs hvs')

/-- An accepted outer history has reached a state. -/
theorem exists_reachedAt_of_mem_dom {us : List Uni.{u}}
    (h : us ∈ dom (attachEngineFully i E R)) : ∃ st, ReachedAt i E R us st := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
  obtain ⟨r, hr, -⟩ := (mem_attachEngineFullyRaw_iff us v).mp hv
  exact ⟨r.2, r.1, hr⟩

/-- **The frontier drive**, forward: a resolved round from the reached state is
a resolved run of the extended outer history. -/
theorem mem_attachEngineFullyDrive_concat {us : List Uni.{u}}
    {st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}} (hst : ReachedAt i E R us st)
    {q v : Uni.{u}} {st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (hround : (v, st') ∈ attachEngineFullyRound i E R st q) :
    ∃ vs, (vs ++ [v], st') ∈ attachEngineFullyDrive i E R ([], []) (us ++ [q]) := by
  obtain ⟨vs, hvs⟩ := hst
  refine ⟨vs, ?_⟩
  rw [attachEngineFullyDrive_append, Part.mem_bind_iff]
  refine ⟨(vs, st), hvs, ?_⟩
  rw [Part.mem_map_iff]
  refine ⟨([v], st'), ?_, rfl⟩
  simp only [attachEngineFullyDrive, Part.mem_bind_iff, Part.mem_map_iff]
  exact ⟨(v, st'), hround, ([], st'), Part.mem_some _, rfl⟩

/-- **The frontier state**: a resolved round advances the reached state. -/
theorem attachEngineFully_reached_concat {us : List Uni.{u}}
    {st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}} (hst : ReachedAt i E R us st)
    {q v : Uni.{u}} {st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (hround : (v, st') ∈ attachEngineFullyRound i E R st q) :
    ReachedAt i E R (us ++ [q]) st' :=
  let ⟨vs, hvs⟩ := mem_attachEngineFullyDrive_concat hst hround
  ⟨vs ++ [v], hvs⟩

/-- **The frontier state, foreign query**: an accepted query outside `i` leaves
the converter conversation alone and extends the resource history by itself —
CR18 Definition 3.3's "kept when accepted", read on the raw history the
completion deletes from. -/
theorem attachEngineFully_reached_concat_not_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∉ i)
    (hR : keptPrefix R xs ++ [q] ∈ dom R) :
    ReachedAt i E R (us ++ [q]) (c, xs ++ [q]) := by
  refine attachEngineFully_reached_concat hst
    (v := output R (keptPrefix R xs ++ [q]) hR) ?_
  rw [attachEngineFullyRound_not_mem E R (c, xs) hq, Part.mem_map_iff]
  exact ⟨_, Part.get_mem hR, rfl⟩

/-- **The frontier state, owned query**: a query inside `i` advances the state
to whatever its engine round resolves to. -/
theorem attachEngineFully_reached_concat_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∈ i) {v : Uni.{u}}
    {st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (hres : (v, st') ∈ resolve (ofEngine E) R (c ++ [Sum.inl (InLabel.outside, q)], xs)) :
    ReachedAt i E R (us ++ [q]) st' :=
  attachEngineFully_reached_concat hst
    (by rw [attachEngineFullyRound_mem E R (c, xs) hq]; exact hres)

/-! ## The frontier

Everything the composite does at an extended outer history is one round from
the reached state.  The two faces are then read off the dispatch, and neither
mentions the other: the foreign face never consults the engine, and the owned
face never consults the resource before the engine has moved. -/

/-- A one-query drive is one round. -/
theorem mem_attachEngineFullyDrive_singleton
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) (q : Uni.{u})
    {r : List Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u})} :
    r ∈ attachEngineFullyDrive i E R st [q] ↔
      ∃ w ∈ attachEngineFullyRound i E R st q, r = ([w.1], w.2) := by
  simp only [attachEngineFullyDrive, Part.mem_bind_iff, Part.mem_map_iff,
    Part.mem_some_iff]
  constructor
  · rintro ⟨w, hw, rr, rfl, rfl⟩
    exact ⟨w, hw, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, ([], w.2), rfl, rfl⟩

/-- **The frontier value**: at an extended outer history the composite is
exactly the round its dispatch selects, read at the reached state.  Domain and
output of both faces come from this one equation. -/
theorem attachEngineFully_concat_round {us : List Uni.{u}}
    {st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}} (hst : ReachedAt i E R us st)
    (q : Uni.{u}) :
    (attachEngineFully i E R).1 (us ++ [q]) =
      (attachEngineFullyRound i E R st q).map Prod.fst := by
  obtain ⟨vs, hvs⟩ := hst
  refine Part.ext fun v => ?_
  rw [attachEngineFully_toPFun, mem_attachEngineFullyRaw_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨r, hr, hlast⟩
    rw [attachEngineFullyDrive_append, Part.mem_bind_iff] at hr
    obtain ⟨ra, hra, hrb⟩ := hr
    have hra2 : ra = (vs, st) := Part.mem_unique hra hvs
    subst hra2
    rw [Part.mem_map_iff] at hrb
    obtain ⟨rb, hrb, rfl⟩ := hrb
    obtain ⟨w, hw, rfl⟩ := (mem_attachEngineFullyDrive_singleton _ _).mp hrb
    refine ⟨w, hw, ?_⟩
    simpa using hlast
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨vs', hvs'⟩ := mem_attachEngineFullyDrive_concat ⟨vs, hvs⟩
      (v := w.1) (st' := w.2) (by rw [← Prod.mk.eta (p := w)] at hw; exact hw)
    exact ⟨_, hvs', by simp⟩

/-! ### The foreign face — transparency

The clause that has no analogue at whole-face application, and the reason the
refuted relay design is not needed. -/

/-- **Transparency — the headline of the repair.**  At a query the converter
does not own, the composite *is* the resource: one and the same partial value,
so the same domain and the same answer, and in particular the resource's
refusals are the composite's refusals.

This is where the two G1 witnesses die (`ConnectFullyDefined.lean`, closing
section).  Both turn on a relay round having to *render* the completion's `⊥`
as a designated token — on the inner face, because one attachment then feeds
the other a rendered answer instead of the raw completion; on the outer face,
because a rendered `⊥` is a defined answer, so a query CR18 Definition 3.3
would delete is kept instead.  Here a foreign query is not relayed through an
engine at all: the dispatch hands it to the resource, so there is no token to
disagree about, and a refusal outside `i` stays a refusal. -/
theorem attachEngineFully_transparent {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∉ i) :
    (attachEngineFully i E R).1 (us ++ [q]) = R.1 (keptPrefix R xs ++ [q]) := by
  rw [attachEngineFully_concat_round hst q, attachEngineFullyRound_not_mem E R (c, xs) hq]
  refine Part.ext fun v => ?_
  simp [Part.mem_map_iff]

/-- **The frontier receipt, foreign query**: the composite accepts exactly when
the resource does — refusal preservation, by construction. -/
theorem mem_dom_attachEngineFully_concat_not_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∉ i) :
    us ++ [q] ∈ dom (attachEngineFully i E R) ↔ keptPrefix R xs ++ [q] ∈ dom R := by
  show ((attachEngineFully i E R).1 (us ++ [q])).Dom ↔ _
  rw [attachEngineFully_transparent hst hq]
  exact Iff.rfl

/-- **The frontier output, foreign query**: the answer is the resource's own,
computed on the resource's own kept history. -/
theorem output_attachEngineFully_concat_not_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∉ i)
    (h : us ++ [q] ∈ dom (attachEngineFully i E R))
    (hR : keptPrefix R xs ++ [q] ∈ dom R) :
    output (attachEngineFully i E R) (us ++ [q]) h =
      output R (keptPrefix R xs ++ [q]) hR := by
  have hmem : output R (keptPrefix R xs ++ [q]) hR ∈
      (attachEngineFully i E R).1 (us ++ [q]) := by
    rw [attachEngineFully_transparent hst hq]
    exact Part.get_mem hR
  exact Part.get_eq_of_mem hmem h

/-! ### The owned face — the engine's round -/

/-- **The frontier receipt, owned query**: the composite accepts exactly when
the engine's round, started at the reached conversation and resolved against
`R⊥`, resolves. -/
theorem mem_dom_attachEngineFully_concat_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∈ i) :
    us ++ [q] ∈ dom (attachEngineFully i E R) ↔
      (resolve (ofEngine E) R (c ++ [Sum.inl (InLabel.outside, q)], xs)).Dom := by
  show ((attachEngineFully i E R).1 (us ++ [q])).Dom ↔ _
  rw [attachEngineFully_concat_round hst q, attachEngineFullyRound_mem E R (c, xs) hq]
  exact Iff.rfl

/-- **The frontier output, owned query**: the answer is the round's own outer
answer. -/
theorem output_attachEngineFully_concat_mem {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∈ i) {v : Uni.{u}}
    {st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (hres : (v, st') ∈ resolve (ofEngine E) R (c ++ [Sum.inl (InLabel.outside, q)], xs))
    (h : us ++ [q] ∈ dom (attachEngineFully i E R)) :
    output (attachEngineFully i E R) (us ++ [q]) h = v := by
  have hmem : v ∈ (attachEngineFully i E R).1 (us ++ [q]) := by
    rw [attachEngineFully_concat_round hst q, attachEngineFullyRound_mem E R (c, xs) hq,
      Part.mem_map_iff]
    exact ⟨(v, st'), hres, rfl⟩
  exact Part.get_eq_of_mem hmem h

/-- **Refusal precedes inner traffic, at the owned face** — the interface-local
form of `connectFully_refusal_first`, and it is the same statement one face
narrower: whether the composite answers a query of `i` is decided by the
*engine* at the conversation already reached, the resource entering only
through the answers the engine has already seen.

The foreign face needs no such receipt: outside `i` the composite's refusals
are the resource's own, which is `attachEngineFully_transparent`.  Together the
two say that no history is refused after its round issued a request. -/
theorem attachEngineFully_refusal_first {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ}
    (hIT : InnerTotal E) (hβ : AnswersWithinBudget E β) {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {q : Uni.{u}} (hq : q ∈ i) :
    us ++ [q] ∈ dom (attachEngineFully i E R) ↔
      c.map unlabel ++ [Sum.inl q] ∈ dom E := by
  have hmap : (c ++ [Sum.inl (InLabel.outside, q)]).map unlabel =
      c.map unlabel ++ [Sum.inl q] := by simp
  rw [mem_dom_attachEngineFully_concat_mem hst hq]
  constructor
  · intro h
    rw [← hmap]
    exact mem_dom_of_resolve_dom E R _ xs h
  · intro h
    exact resolve_dom_of_mem_dom hIT hβ R (β (c.map unlabel ++ [Sum.inl q]))
      _ xs (by rw [hmap]) (by rw [hmap]; exact h)

/-! ## The whole face is the special case `i = Set.univ`

The demotion bridge.  When the converter owns every query the dispatch never
takes its foreign branch, and what is left is CR18 Definition 3.9's own
iteration — so `connectFully` is not a second primitive but this one at the
full interface. -/

/-- At `i = Set.univ` the outer iteration is CR18 Definition 3.9's own. -/
theorem attachEngineFullyDrive_univ (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}))
    (R : DDS Uni.{u} Uni.{u}) (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u})
    (us : List Uni.{u}) :
    attachEngineFullyDrive Set.univ E R st us = driveFrom (ofEngine E) R st us := by
  induction us generalizing st with
  | nil => rfl
  | cons q rest ih =>
      simp only [attachEngineFullyDrive, Converter.DDC.driveFrom,
        attachEngineFullyRound_mem E R st (Set.mem_univ q), ih]

/-- **The demotion bridge**: whole-face application is the interface-local
attachment at the full interface.  Everything `connectFully` proves is
therefore this primitive's `i = Set.univ` instance, and nothing about it has to
be re-proved. -/
theorem attachEngineFully_univ (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}))
    (R : DDS Uni.{u} Uni.{u}) :
    attachEngineFully Set.univ E R = connectFully E R := by
  apply Subtype.ext
  funext us
  show attachEngineFullyRaw Set.univ E R us = Converter.DDC.applyRaw (ofEngine E) R us
  simp only [attachEngineFullyRaw, Converter.DDC.applyRaw, attachEngineFullyDrive_univ]
  congr 1
  funext r
  cases r.1.getLast? <;> rfl

/-! ## The first query

Before any round has run the reached state is empty, so both faces read off
their own component of the composite with no history in between.  Inside `i`
the answer is the resource-independent one the B4 criterion asks for; outside
`i` it is the resource's, which is transparency at length one and is exactly
the clause whole-face application cannot state. -/

/-- The first query, owned: accepted exactly when the engine accepts it, and no
resource has been consulted. -/
theorem mem_dom_attachEngineFully_of_nil_mem {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ}
    (hIT : InnerTotal E) (hβ : AnswersWithinBudget E β) {q : Uni.{u}} (hq : q ∈ i) :
    [q] ∈ dom (attachEngineFully i E R) ↔ [Sum.inl q] ∈ dom E := by
  have h := attachEngineFully_refusal_first hIT hβ (reachedAt_nil i E R) hq
  simpa using h

/-- The first query, foreign: accepted exactly when the *resource* accepts it —
transparency at length one. -/
theorem mem_dom_attachEngineFully_of_nil_not_mem {q : Uni.{u}} (hq : q ∉ i) :
    [q] ∈ dom (attachEngineFully i E R) ↔ [q] ∈ dom R := by
  have h := mem_dom_attachEngineFully_concat_not_mem (reachedAt_nil i E R) hq
  simpa [keptPrefix] using h

/-- **The B4 criterion, at the interface it applies to**: whether the composite
answers a first *owned* query does not depend on the resource.

Outside `i` the corresponding statement is false, and deliberately so — there
`attachEngineFully` is the resource (`mem_dom_attachEngineFully_of_nil_not_mem`).
Whole-face application could not tell the two apart. -/
theorem mem_dom_attachEngineFully_of_nil_congr {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ}
    (hIT : InnerTotal E) (hβ : AnswersWithinBudget E β) (R R' : DDS Uni.{u} Uni.{u})
    {q : Uni.{u}} (hq : q ∈ i) :
    [q] ∈ dom (attachEngineFully i E R) ↔ [q] ∈ dom (attachEngineFully i E R') :=
  (mem_dom_attachEngineFully_of_nil_mem (R := R) hIT hβ hq).trans
    (mem_dom_attachEngineFully_of_nil_mem (R := R') hIT hβ hq).symm

/-! ## Absorption — the deletion pass is invisible to a round

The re-simulating environment of the absorption receipt below must *ask* the
resource every foreign query the composite is given, because it cannot know
which of them the resource will refuse without asking.  The composite's own
resource history keeps only the accepted ones (`attachEngineFullyRound`'s
foreign branch is `Part.none` at a refusal), so the two histories differ by
exactly the queries CR18 Definition 3.3 deletes — they have the same *kept*
prefix, and nothing else in the mechanism can tell them apart.

That is the content of this section: a round reads the resource only through
the completion, the completion reads only the kept prefix, so a round started
at either history resolves to the same answer and the same converter history,
with the untouched part of the resource history relocated.  Both lemmas are
about `resolve` and would sit equally well with CR18 Definition 3.9's own rules
in `ConnectFullyDefined.lean`; they are stated here because leg (b) is their
only consumer. -/

universe u₁ u₂ u₃ u₄

/-- The deletion pass commutes with a common extension: histories with the same
kept prefix keep the same kept prefix after the same queries. -/
theorem keptPrefix_append_congr {X : Type u₃} {Y : Type u₄} (S : DDS X Y)
    {a b : List X} (w : List X) (h : keptPrefix S a = keptPrefix S b) :
    keptPrefix S (a ++ w) = keptPrefix S (b ++ w) := by
  rw [keptPrefix_append_foldl, keptPrefix_append_foldl, h]

/-- The completion's answer depends on the history only through its kept
prefix — CR18 Definition 3.3 read at a single query. -/
theorem answer_congr_keptPrefix {X : Type u₃} {Y : Type u₄} (S : DDS X Y)
    {a b : List X} (x : X) (h : keptPrefix S a = keptPrefix S b) :
    answer S a x = answer S b x := by
  rw [answer_eq, answer_eq, h]

/-- One connection step, characterized: CR18 Definition 3.9's two rules and
nothing else.  The junk labels are unreachable, which is what makes the
dichotomy exhaustive. -/
theorem mem_connStep_iff {U : Type u₁} {V : Type u₂} {X : Type u₃} {Y : Type u₄}
    (α : Converter.DDC U V X Y) (S : DDS X Y)
    (st : List (CIn U Y) × List X)
    (z : (V × (List (CIn U Y) × List X)) ⊕ (List (CIn U Y) × List X)) :
    z ∈ Converter.DDC.connStep α S st ↔
      (∃ v : V, Sum.inl (InLabel.outside, v) ∈ α.1 st.1 ∧ z = Sum.inl (v, st)) ∨
      (∃ x : X, Sum.inr (InLabel.inside, x) ∈ α.1 st.1 ∧
        z = Sum.inr (st.1 ++ [Sum.inr (InLabel.inside, answer S st.2 x)],
          st.2 ++ [x])) := by
  rw [Converter.DDC.connStep, Part.mem_bind_iff]
  constructor
  · rintro ⟨o, ho, hz⟩
    rcases o with ⟨lbl, v⟩ | ⟨lbl, x⟩ <;> cases lbl
    · simp at hz
    · exact Or.inl ⟨v, ho, Part.mem_some_iff.mp hz⟩
    · exact Or.inr ⟨x, ho, Part.mem_some_iff.mp hz⟩
    · simp at hz
  · rintro (⟨v, hv, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨_, hv, Part.mem_some _⟩
    · exact ⟨_, hx, Part.mem_some _⟩

/-- **A deleted query is invisible to a round.**  A round started at two
resource histories with the same kept prefix resolves to the same outer answer
and the same converter history, and appends the same requests to each — so the
composite's own history and the history an absorbing environment has built are
interchangeable inside a round.

The proof is `PFun.fix_bisim` at the state relation "same converter history,
and resource histories that are the two given ones extended alike". -/
theorem exists_mem_resolve_of_keptPrefix_eq {U : Type u₁} {V : Type u₂}
    {X : Type u₃} {Y : Type u₄} (α : Converter.DDC U V X Y) (S : DDS X Y)
    (c : List (CIn U Y)) {xs ys : List X}
    (h : keptPrefix S xs = keptPrefix S ys) {v : V} {c' : List (CIn U Y)}
    {zs : List X} (hr : (v, (c', zs)) ∈ resolve α S (c, xs)) :
    ∃ w, zs = xs ++ w ∧ (v, (c', ys ++ w)) ∈ resolve α S (c, ys) := by
  have hstop : ∀ a a' : List (CIn U Y) × List X,
      (a.1 = a'.1 ∧ ∃ w, a.2 = xs ++ w ∧ a'.2 = ys ++ w) →
      ∀ b : V × (List (CIn U Y) × List X),
        Sum.inl b ∈ Converter.DDC.connStep α S a →
        ∃ b' : V × (List (CIn U Y) × List X),
          Sum.inl b' ∈ Converter.DDC.connStep α S a' ∧
            (b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧
              ∃ w, b.2.2 = xs ++ w ∧ b'.2.2 = ys ++ w) := by
    rintro ⟨ca, la⟩ ⟨ca', la'⟩ ⟨hc, w, rfl, rfl⟩ b hb
    simp only at hc
    subst hc
    rw [mem_connStep_iff] at hb
    rcases hb with ⟨v', hv', hb⟩ | ⟨x, -, hb⟩
    · obtain rfl : b = (v', (ca, xs ++ w)) := by simpa using hb
      exact ⟨(v', (ca, ys ++ w)),
        (mem_connStep_iff α S (ca, ys ++ w) _).mpr (Or.inl ⟨v', hv', rfl⟩),
        rfl, rfl, w, rfl, rfl⟩
    · simp at hb
  have hstep : ∀ a a' : List (CIn U Y) × List X,
      (a.1 = a'.1 ∧ ∃ w, a.2 = xs ++ w ∧ a'.2 = ys ++ w) →
      ∀ a₁ : List (CIn U Y) × List X,
        Sum.inr a₁ ∈ Converter.DDC.connStep α S a →
        ∃ a₁' : List (CIn U Y) × List X,
          Sum.inr a₁' ∈ Converter.DDC.connStep α S a' ∧
            (a₁.1 = a₁'.1 ∧ ∃ w, a₁.2 = xs ++ w ∧ a₁'.2 = ys ++ w) := by
    rintro ⟨ca, la⟩ ⟨ca', la'⟩ ⟨hc, w, rfl, rfl⟩ a₁ ha
    simp only at hc
    subst hc
    rw [mem_connStep_iff] at ha
    rcases ha with ⟨v', -, ha⟩ | ⟨x, hx, ha⟩
    · simp at ha
    · have hans : answer S (xs ++ w) x = answer S (ys ++ w) x :=
        answer_congr_keptPrefix S x (keptPrefix_append_congr S w h)
      obtain rfl : a₁ =
          (ca ++ [Sum.inr (InLabel.inside, answer S (xs ++ w) x)],
            xs ++ w ++ [x]) := by simpa only [Sum.inr.injEq] using ha
      refine ⟨(ca ++ [Sum.inr (InLabel.inside, answer S (ys ++ w) x)],
          ys ++ w ++ [x]),
        (mem_connStep_iff α S (ca, ys ++ w) _).mpr (Or.inr ⟨x, hx, rfl⟩), ?_⟩
      exact ⟨by rw [hans], w ++ [x], by simp, by simp⟩
  obtain ⟨⟨v', c'', zs'⟩, hb', hv, hc'', w, hw, hw'⟩ :=
    PFun.fix_bisim hstop hstep hr (c, ys) ⟨rfl, [], by simp, by simp⟩
  simp only at hv hc'' hw hw'
  subst hv; subst hc''; subst hw'
  exact ⟨w, hw, hb'⟩

/-! ## Absorption — the replay, by the same dispatch

The decomposition is B4-RESUME's (`fullyReplayStep`, `fullyNeed`,
`fullyReplay`, `absorbFully`, the invariant, the receipt) with the ownership
dispatch carried into the step and the need: an owned outer query delegates to
the *same* round replay `roundReplay` — an owned round is the same engine round
— while a foreign outer query is the relay genre of `Absorb.lean`, one inner
query whose answer is the outer answer verbatim.  The inner induction
`exists_roundReplay_absorb` is parametric in the environment and is reused as
it stands. -/

/-- One round of the replay of an outer interaction with
`attachEngineFully i E ·`, dispatched on ownership exactly as the composite is.

* the outer environment stops: nothing moves;
* an owned query the engine refuses is answered `⊥` on the spot, with no inner
  traffic (`attachEngineFully_refusal_first`);
* an owned query the engine accepts runs the round replay, which either closes
  the round or stalls for want of an inner answer;
* a foreign query consumes the next inner answer and returns it unchanged —
  transparency (`attachEngineFully_transparent`) makes the resource's answer
  the composite's answer, refusals included — or stalls when there is none. -/
def attachEngineFullyReplayStep (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    (st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})) :
    List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u}) :=
  match e st.1↓ᵧ with
  | none => st
  | some u =>
      if u ∈ i then
        if st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E then
          match roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)])
              st.2.2 with
          | ((c', ys'), some v, _) => (st.1 ++ [(u, some v)], c', ys')
          | (_, none, _) => st
        else (st.1 ++ [(u, none)], st.2)
      else
        match st.2.2 with
        | [] => st
        | y :: ys => (st.1 ++ [(u, y)], st.2.1, ys)

/-- The query the replay is waiting for: the round replay's own report at an
owned query, the foreign query itself at a foreign one. -/
def attachEngineFullyNeed (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    (st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})) : Option Uni.{u} :=
  match e st.1↓ᵧ with
  | none => none
  | some u =>
      if u ∈ i then
        if st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E then
          (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2).2.2
        else none
      else
        match st.2.2 with
        | [] => some u
        | _ :: _ => none

theorem attachEngineFullyReplayStep_stop (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})}
    (h : e st.1↓ᵧ = none) : attachEngineFullyReplayStep i E F e st = st := by
  simp [attachEngineFullyReplayStep, h]

theorem attachEngineFullyReplayStep_refuse (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})} {u : Uni.{u}}
    (h : e st.1↓ᵧ = some u) (hu : u ∈ i)
    (hno : st.2.1.map unlabel ++ [Sum.inl u] ∉ dom E) :
    attachEngineFullyReplayStep i E F e st = (st.1 ++ [(u, none)], st.2) := by
  simp only [attachEngineFullyReplayStep, h]
  rw [if_pos hu, if_neg hno]

theorem attachEngineFullyReplayStep_round (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})} {u : Uni.{u}}
    {c' : List (CIn Uni.{u} Uni.{u})} {ys' : List (Option Uni.{u})}
    {v : Uni.{u}} {o : Option Uni.{u}}
    (h : e st.1↓ᵧ = some u) (hu : u ∈ i)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E)
    (hr : roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2 =
      ((c', ys'), some v, o)) :
    attachEngineFullyReplayStep i E F e st = (st.1 ++ [(u, some v)], c', ys') := by
  simp only [attachEngineFullyReplayStep, h]
  rw [if_pos hu, if_pos hd, hr]

theorem attachEngineFullyReplayStep_stall (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})} {u : Uni.{u}}
    (h : e st.1↓ᵧ = some u) (hu : u ∈ i)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E)
    (hr : (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)])
      st.2.2).2.1 = none) :
    attachEngineFullyReplayStep i E F e st = st := by
  simp only [attachEngineFullyReplayStep, h]
  rw [if_pos hu, if_pos hd]
  rcases hrr : roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2
    with ⟨⟨c', ys'⟩, o₁, o₂⟩
  rw [hrr] at hr
  cases hr
  rfl

/-- **The foreign face of the replay**: one inner answer, returned unchanged. -/
theorem attachEngineFullyReplayStep_foreign (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (t : List (Uni.{u} × Option Uni.{u}))
    (c : List (CIn Uni.{u} Uni.{u})) (y : Option Uni.{u})
    (ys : List (Option Uni.{u})) {u : Uni.{u}} (h : e t↓ᵧ = some u) (hu : u ∉ i) :
    attachEngineFullyReplayStep i E F e (t, c, y :: ys) =
      (t ++ [(u, y)], c, ys) := by
  simp [attachEngineFullyReplayStep, h, hu]

theorem attachEngineFullyReplayStep_foreign_stall (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})} {u : Uni.{u}}
    (h : e st.1↓ᵧ = some u) (hu : u ∉ i) (hst : st.2.2 = []) :
    attachEngineFullyReplayStep i E F e st = st := by
  rcases st with ⟨t, c, ys⟩
  simp only at hst
  subst hst
  simp [attachEngineFullyReplayStep, h, hu]

theorem attachEngineFullyNeed_round (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u})
    {st : List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})} {u : Uni.{u}}
    (h : e st.1↓ᵧ = some u) (hu : u ∈ i)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E) :
    attachEngineFullyNeed i E F e st =
      (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2).2.2 := by
  simp only [attachEngineFullyNeed, h]
  rw [if_pos hu, if_pos hd]

/-- At a foreign query with no inner answer left, the replay asks that very
query — the relay face of the dispatch. -/
theorem attachEngineFullyNeed_foreign (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (t : List (Uni.{u} × Option Uni.{u}))
    (c : List (CIn Uni.{u} Uni.{u})) {u : Uni.{u}} (h : e t↓ᵧ = some u)
    (hu : u ∉ i) :
    attachEngineFullyNeed i E F e (t, c, ([] : List (Option Uni.{u}))) = some u := by
  simp [attachEngineFullyNeed, h, hu]

/-- The replay of the first `k` outer rounds against a given list of inner
answers. -/
def attachEngineFullyReplay (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (ys : List (Option Uni.{u})) :
    ℕ → List (Uni.{u} × Option Uni.{u}) ×
      List (CIn Uni.{u} Uni.{u}) × List (Option Uni.{u})
  | 0 => ([], [], ys)
  | k + 1 => attachEngineFullyReplayStep i E F e (attachEngineFullyReplay i E F e ys k)

@[simp]
theorem attachEngineFullyReplay_zero (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (ys : List (Option Uni.{u})) :
    attachEngineFullyReplay i E F e ys 0 = ([], [], ys) :=
  rfl

theorem attachEngineFullyReplay_succ (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (ys : List (Option Uni.{u})) (k : ℕ) :
    attachEngineFullyReplay i E F e ys (k + 1) =
      attachEngineFullyReplayStep i E F e (attachEngineFullyReplay i E F e ys k) :=
  rfl

/-- A stalled replay stays stalled. -/
theorem attachEngineFullyReplay_of_fixed (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (ys : List (Option Uni.{u})) {k : ℕ}
    (hfix : attachEngineFullyReplayStep i E F e (attachEngineFullyReplay i E F e ys k) =
      attachEngineFullyReplay i E F e ys k) :
    ∀ l, k ≤ l → attachEngineFullyReplay i E F e ys l =
      attachEngineFullyReplay i E F e ys k := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => rfl
  | succ l _ ih => rw [attachEngineFullyReplay_succ, ih, hfix]

/-- **The absorbed environment**: the inner environment that replays the outer
interaction with `attachEngineFully i E ·` for `n` rounds and asks exactly the
query the replay is waiting for.  It depends on the outer environment, the
length, the interface, the engine and the budget — never on the resource, which
is what makes the reduction a reduction. -/
def absorbAttachEngineFully (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (F : ℕ)
    (e : DDE.Total Uni.{u} Uni.{u}) (n : ℕ) : DDE.Total Uni.{u} Uni.{u} :=
  fun ys => attachEngineFullyNeed i E F e (attachEngineFullyReplay i E F e ys n)

/-! ### The composite's answer at the frontier

`answer (attachEngineFully i E R)` decided at the reached state: inside `i` a
refusal is the engine's own (and costs no inner traffic) and an answer is the
round's; outside `i` the answer is the resource's, verbatim. -/

/-- An owned query the engine refuses is refused by the composite — **before**
any inner traffic of its round.  This is `attachEngineFully_refusal_first` read
at the completion's answer, which is the form the replay consumes. -/
theorem answer_attachEngineFully_refuse {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ}
    (hIT : InnerTotal E) (hβ : AnswersWithinBudget E β) {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {L : List Uni.{u}}
    (hus : keptPrefix (attachEngineFully i E R) L = us) {u : Uni.{u}} (hu : u ∈ i)
    (hno : c.map unlabel ++ [Sum.inl u] ∉ dom E) :
    answer (attachEngineFully i E R) L u = none := by
  rw [answer_eq]
  refine dif_neg fun hc => hno ?_
  rw [hus] at hc
  exact (attachEngineFully_refusal_first hIT hβ hst hu).mp hc

/-- An owned query the engine accepts is answered by the round it starts. -/
theorem answer_attachEngineFully_round {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {L : List Uni.{u}}
    (hus : keptPrefix (attachEngineFully i E R) L = us) {u : Uni.{u}} (hu : u ∈ i)
    {v : Uni.{u}} {st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (hres : (v, st') ∈ resolve (ofEngine E) R
      (c ++ [Sum.inl (InLabel.outside, u)], xs)) :
    answer (attachEngineFully i E R) L u = some v := by
  have hd : us ++ [u] ∈ dom (attachEngineFully i E R) :=
    (mem_dom_attachEngineFully_concat_mem hst hu).mpr
      (Part.dom_iff_mem.mpr ⟨(v, st'), hres⟩)
  have hd' : keptPrefix (attachEngineFully i E R) L ++ [u] ∈
      dom (attachEngineFully i E R) := by
    rw [hus]; exact hd
  rw [answer_eq, dif_pos hd']
  exact congrArg some
    ((output_congr (attachEngineFully i E R) (by rw [hus]) hd' hd).trans
      (output_attachEngineFully_concat_mem hst hu hres hd))

/-- **The foreign face at the completion's answer**: outside `i` the composite's
answer *is* the resource's, refusal included — `attachEngineFully_transparent`
in the form the replay consumes.  There is no analogue of this clause at
whole-face application, and it is what makes a foreign round a relay round. -/
theorem answer_attachEngineFully_foreign {us : List Uni.{u}}
    {c : List (CIn Uni.{u} Uni.{u})} {xs : List Uni.{u}}
    (hst : ReachedAt i E R us (c, xs)) {L : List Uni.{u}}
    (hus : keptPrefix (attachEngineFully i E R) L = us) {u : Uni.{u}} (hu : u ∉ i) :
    answer (attachEngineFully i E R) L u = answer R xs u := by
  rw [answer_eq, answer_eq]
  by_cases hd : keptPrefix R xs ++ [u] ∈ dom R
  · have hdc : us ++ [u] ∈ dom (attachEngineFully i E R) :=
      (mem_dom_attachEngineFully_concat_not_mem hst hu).mpr hd
    have hdc' : keptPrefix (attachEngineFully i E R) L ++ [u] ∈
        dom (attachEngineFully i E R) := by
      rw [hus]; exact hdc
    rw [dif_pos hdc', dif_pos hd]
    exact congrArg some
      ((output_congr (attachEngineFully i E R) (by rw [hus]) hdc' hdc).trans
        (output_attachEngineFully_concat_not_mem hst hu hdc hd))
  · have hdc' : keptPrefix (attachEngineFully i E R) L ++ [u] ∉
        dom (attachEngineFully i E R) := by
      rw [hus]
      exact fun hc => hd ((mem_dom_attachEngineFully_concat_not_mem hst hu).mp hc)
    rw [dif_neg hdc', dif_neg hd]

/-! ### The outer invariant, and the receipt -/

/-- **The replay invariant.**  After `k` outer rounds the replay has rebuilt the
outer transcript exactly, sits at the converter conversation the composite has
reached, and has consumed exactly the answers of the first `j` inner rounds —
at most `max K 1` per outer round, since an owned round costs at most `K` inner
queries and a foreign one costs exactly one.

The resource histories are the mixed-history clause of the repair.  The
composite's own resource history keeps only what it was *given*: a foreign
query the resource refuses never enters it, because the round is undefined
there.  The absorbing environment has to ask that query all the same — it
cannot know the refusal without asking — so its history carries it.  The two
therefore agree only up to CR18 Definition 3.3's deletion, and the invariant
says exactly that (`keptPrefix R xs = keptPrefix R (…)↓ₓ`); a round cannot tell
them apart (`exists_mem_resolve_of_keptPrefix_eq`), and neither can the
completion (`answer_congr_keptPrefix`). -/
theorem attachEngineFullyReplay_invariant
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K)
    (e : DDE.Total Uni.{u} Uni.{u}) (n : ℕ) (R : DDS Uni.{u} Uni.{u}) :
    ∀ k ≤ n, ∃ (j : ℕ) (c : List (CIn Uni.{u} Uni.{u})) (xs : List Uni.{u}),
      j ≤ k * max K 1 ∧
      ReachedAt i E R
          (answeredQueries (DDE.Total.transcript (attachEngineFully i E R) e k))
          (c, xs) ∧
      keptPrefix R xs =
        keptPrefix R
          (DDE.Total.transcript R
            (absorbAttachEngineFully i E (K + 1) e n) j)↓ₓ ∧
      ∀ zs : List (Option Uni.{u}),
        attachEngineFullyReplay i E (K + 1) e
            ((DDE.Total.transcript R
              (absorbAttachEngineFully i E (K + 1) e n) j)↓ᵧ ++ zs) k =
          (DDE.Total.transcript (attachEngineFully i E R) e k, c, zs) := by
  intro k
  induction k with
  | zero =>
      exact fun _ => ⟨0, [], [], by simp, reachedAt_nil i E R, rfl, fun _ => rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨j, c, xs, hjk, hst, hkp, hrep⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t, ht⟩ :
          ∃ t, DDE.Total.transcript (attachEngineFully i E R) e k = t := ⟨_, rfl⟩
      obtain ⟨T, hT⟩ :
          ∃ T, DDE.Total.transcript R
            (absorbAttachEngineFully i E (K + 1) e n) j = T := ⟨_, rfl⟩
      rw [ht] at hst hrep
      rw [hT] at hkp hrep
      have hone : 1 ≤ max K 1 := le_max_right _ _
      have hKle : K ≤ max K 1 := le_max_left _ _
      have hjk' : j ≤ (k + 1) * max K 1 :=
        le_trans hjk (by rw [Nat.succ_mul]; omega)
      have hus : keptPrefix (attachEngineFully i E R) t↓ₓ = answeredQueries t := by
        rw [← ht]
        exact (DDE.Total.answeredQueries_transcript
          (attachEngineFully i E R) e k).symm
      rcases hx : e t↓ᵧ with _ | u
      · -- the outer environment stops: nothing moves on either side
        have houter : DDE.Total.transcript (attachEngineFully i E R) e (k + 1) = t := by
          rw [DDE.Total.transcript_succ_of_stop (attachEngineFully i E R) e (n := k)
            (by rw [ht]; exact hx), ht]
        exact ⟨j, c, xs, hjk', by rw [houter]; exact hst, by rw [hT]; exact hkp,
          fun zs => by
            rw [hT, attachEngineFullyReplay_succ, hrep zs,
              attachEngineFullyReplayStep_stop i E (K + 1) e (st := (t, c, zs)) hx,
              houter]⟩
      · by_cases hui : u ∈ i
        · by_cases hdE : c.map unlabel ++ [Sum.inl u] ∈ dom E
          · -- an owned query the engine accepts: the round runs, and the
            -- environment asks exactly the requests it issues
            have hwait : ∀ ws : List (Option Uni.{u}),
                (roundReplay E (K + 1) (c ++ [Sum.inl (InLabel.outside, u)])
                  ws).2.1 = none →
                absorbAttachEngineFully i E (K + 1) e n (T↓ᵧ ++ ws) =
                  (roundReplay E (K + 1) (c ++ [Sum.inl (InLabel.outside, u)])
                    ws).2.2 := by
              intro ws hns
              have h1 : attachEngineFullyReplay i E (K + 1) e (T↓ᵧ ++ ws) k =
                  (t, c, ws) := hrep ws
              have hfix : attachEngineFullyReplayStep i E (K + 1) e
                  (attachEngineFullyReplay i E (K + 1) e (T↓ᵧ ++ ws) k) =
                    attachEngineFullyReplay i E (K + 1) e (T↓ᵧ ++ ws) k := by
                rw [h1]
                exact attachEngineFullyReplayStep_stall i E (K + 1) e
                  (st := (t, c, ws)) hx hui hdE hns
              show attachEngineFullyNeed i E (K + 1) e
                (attachEngineFullyReplay i E (K + 1) e (T↓ᵧ ++ ws) n) = _
              rw [attachEngineFullyReplay_of_fixed i E (K + 1) e _ hfix n
                (Nat.le_of_succ_le hk), h1]
              exact attachEngineFullyNeed_round i E (K + 1) e (st := (t, c, ws))
                hx hui hdE
            obtain ⟨r, v, c'', ws', hjr, hrK, hout', hres', hround⟩ :=
              exists_roundReplay_absorb hIT hβ R
                (absorbAttachEngineFully i E (K + 1) e n)
                (K + 1) (c ++ [Sum.inl (InLabel.outside, u)]) T↓ₓ T hwait K
                (c ++ [Sum.inl (InLabel.outside, u)]) j [] (hK _)
                (by simpa using hdE) (by rw [hT, List.append_nil]) (by rw [hT])
                (fun _ => rfl)
            obtain ⟨w, hw, hres⟩ :=
              exists_mem_resolve_of_keptPrefix_eq (ofEngine E) R
                (c ++ [Sum.inl (InLabel.outside, u)]) hkp.symm hres'
            have houter : DDE.Total.transcript (attachEngineFully i E R) e (k + 1) =
                t ++ [(u, some v)] := by
              rw [DDE.Total.transcript_succ_of_query (attachEngineFully i E R) e
                (n := k) (x := u) (by rw [ht]; exact hx), ht,
                answer_attachEngineFully_round hst hus hui hres]
            refine ⟨r, c'', xs ++ w, ?_, ?_, ?_, fun zs => ?_⟩
            · calc r ≤ j + K := hrK
                _ ≤ k * max K 1 + max K 1 := by omega
                _ = (k + 1) * max K 1 := by rw [Nat.succ_mul]
            · rw [houter, answeredQueries_concat_some]
              exact attachEngineFully_reached_concat_mem hst hui hres
            · rw [hw]
              exact keptPrefix_append_congr R w hkp
            · rw [hout', List.append_assoc, attachEngineFullyReplay_succ,
                hrep (ws' ++ zs),
                attachEngineFullyReplayStep_round i E (K + 1) e
                  (st := (t, c, ws' ++ zs)) hx hui hdE (hround zs), houter]
          · -- an owned query the engine refuses: refusal precedes inner
            -- traffic, so the resource is untouched and the composite deletes
            -- the query
            have houter : DDE.Total.transcript (attachEngineFully i E R) e (k + 1) =
                t ++ [(u, none)] := by
              rw [DDE.Total.transcript_succ_of_query (attachEngineFully i E R) e
                (n := k) (x := u) (by rw [ht]; exact hx), ht,
                answer_attachEngineFully_refuse hIT hβ hst hus hui hdE]
            refine ⟨j, c, xs, hjk', ?_, by rw [hT]; exact hkp, fun zs => ?_⟩
            · rw [houter, answeredQueries_concat_none]
              exact hst
            · rw [hT, attachEngineFullyReplay_succ, hrep zs,
                attachEngineFullyReplayStep_refuse i E (K + 1) e
                  (st := (t, c, zs)) hx hui hdE, houter]
        · -- a foreign query: one inner round answers it, and the answer is the
          -- outer answer verbatim
          have hstuck : attachEngineFullyReplay i E (K + 1) e T↓ᵧ n = (t, c, []) := by
            have hk0 : attachEngineFullyReplay i E (K + 1) e T↓ᵧ k = (t, c, []) := by
              have := hrep []
              rwa [List.append_nil] at this
            have hfix : attachEngineFullyReplayStep i E (K + 1) e
                (attachEngineFullyReplay i E (K + 1) e T↓ᵧ k) =
                  attachEngineFullyReplay i E (K + 1) e T↓ᵧ k := by
              rw [hk0]
              exact attachEngineFullyReplayStep_foreign_stall i E (K + 1) e
                (st := (t, c, [])) hx hui rfl
            rw [attachEngineFullyReplay_of_fixed i E (K + 1) e T↓ᵧ hfix n
              (le_trans (Nat.le_succ k) hk), hk0]
          have hneed : absorbAttachEngineFully i E (K + 1) e n T↓ᵧ = some u := by
            show attachEngineFullyNeed i E (K + 1) e
              (attachEngineFullyReplay i E (K + 1) e T↓ᵧ n) = some u
            rw [hstuck]
            exact attachEngineFullyNeed_foreign i E (K + 1) e t c hx hui
          have hinner : DDE.Total.transcript R
              (absorbAttachEngineFully i E (K + 1) e n) (j + 1) =
                T ++ [(u, answer R T↓ₓ u)] := by
            rw [DDE.Total.transcript_succ_of_query R
              (absorbAttachEngineFully i E (K + 1) e n) (n := j) (x := u)
              (by rw [hT]; exact hneed), hT]
          have hans : answer (attachEngineFully i E R) t↓ₓ u = answer R T↓ₓ u := by
            rw [answer_attachEngineFully_foreign hst hus hui]
            exact answer_congr_keptPrefix R u hkp
          have houter : DDE.Total.transcript (attachEngineFully i E R) e (k + 1) =
              t ++ [(u, answer R T↓ₓ u)] := by
            rw [DDE.Total.transcript_succ_of_query (attachEngineFully i E R) e
              (n := k) (x := u) (by rw [ht]; exact hx), ht, hans]
          have hjk'' : j + 1 ≤ (k + 1) * max K 1 := by
            rw [Nat.succ_mul]; omega
          have hreplay' : ∀ zs : List (Option Uni.{u}),
              attachEngineFullyReplay i E (K + 1) e
                  ((DDE.Total.transcript R
                    (absorbAttachEngineFully i E (K + 1) e n) (j + 1))↓ᵧ ++ zs)
                  (k + 1) =
                (DDE.Total.transcript (attachEngineFully i E R) e (k + 1), c, zs) := by
            intro zs
            rw [hinner, transcriptOutputs_concat, List.append_assoc,
              List.singleton_append, attachEngineFullyReplay_succ, hrep _,
              attachEngineFullyReplayStep_foreign i E (K + 1) e t c _ zs hx hui,
              houter]
          by_cases hd : keptPrefix R T↓ₓ ++ [u] ∈ dom R
          · have hval : answer R T↓ₓ u =
                some (output R (keptPrefix R T↓ₓ ++ [u]) hd) := by
              rw [answer_eq, dif_pos hd]
            refine ⟨j + 1, c, xs ++ [u], hjk'', ?_, ?_, hreplay'⟩
            · rw [houter, hval, answeredQueries_concat_some]
              exact attachEngineFully_reached_concat_not_mem hst hui (by rw [hkp]; exact hd)
            · rw [hinner, transcriptInputs_concat]
              exact keptPrefix_append_congr R [u] hkp
          · have hval : answer R T↓ₓ u = none := by
              rw [answer_eq, dif_neg hd]
            refine ⟨j + 1, c, xs, hjk'', ?_, ?_, hreplay'⟩
            · rw [houter, hval, answeredQueries_concat_none]
              exact hst
            · rw [hinner, transcriptInputs_concat, keptPrefix_append_singleton,
                if_neg hd]
              exact hkp

/-- **The interface-local attachment absorbs** (DRIFT-REPAIR leg b): every
interaction with `attachEngineFully i E s` is a fixed post-processing of an
interaction with `s`, uniformly in `s`.  This is the hypothesis of
`PDS.advFullyDefined_fTransform_le` for the interface-indexed family, and with
it MauRen16 §3.3's `αⁱ` is nonexpanding.

The re-simulating environment runs the engine itself and relays everything
else.  Both faces of the dispatch are what make it possible, and each for its
own reason:

* inside `i` it holds the converter conversation, so by
  `attachEngineFully_refusal_first` it decides refusals without consulting the
  resource — a refused owned query costs no inner traffic and is deleted on
  both sides — and by `resolve_of_request` every request it relays is answered
  by `System.answer s`;
* outside `i` it asks the query itself and copies the answer, because by
  `attachEngineFully_transparent` the resource's value *is* the composite's,
  refusal included.  Nothing is rendered, so nothing has to be undone.

The hypotheses are the engine class of `exists_absorb_connectFully`, unchanged:
inner-facing totality, Definition 3.8's finite-bound clause, and that bound
uniform over converter histories.  `RequestsWithin i E` is **not** needed —
absorption never asks where the engine's requests point, only how many there
are; it is the commutation of two attachments that will consume it.

`m := n * max K 1`: an owned round costs at most `K` inner queries, by the
budget; a foreign round costs exactly one, since it is a single relayed query.
The count is the only place the two genres have to be reconciled, and `max K 1`
is what reconciles them — `n * K` is wrong at `K = 0`, where an engine that
never requests still has to let foreign queries through. -/
theorem exists_absorb_attachEngineFully
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K)
    (e : DDE.Total Uni.{u} Uni.{u}) (n : ℕ) :
    ∃ (e' : DDE.Total Uni.{u} Uni.{u}) (m : ℕ)
      (p : List (Uni.{u} × Option Uni.{u}) → List (Uni.{u} × Option Uni.{u})),
      ∀ s : DDS Uni.{u} Uni.{u},
        DDE.Total.transcript (attachEngineFully i E s) e n =
          p (DDE.Total.transcript s e' m) := by
  refine ⟨absorbAttachEngineFully i E (K + 1) e n, n * max K 1,
    fun T => (attachEngineFullyReplay i E (K + 1) e T↓ᵧ n).1, fun s => ?_⟩
  obtain ⟨j, c, xs, hjn, -, -, hrep⟩ :=
    attachEngineFullyReplay_invariant hIT hβ hK e n s n le_rfl
  obtain ⟨zs, hzs⟩ :
      ∃ zs, (DDE.Total.transcript s
            (absorbAttachEngineFully i E (K + 1) e n) j)↓ᵧ ++ zs =
        (DDE.Total.transcript s
          (absorbAttachEngineFully i E (K + 1) e n) (n * max K 1))↓ᵧ := by
    obtain ⟨w, hw⟩ :=
      DDE.Total.transcript_prefix s (absorbAttachEngineFully i E (K + 1) e n) hjn
    exact ⟨w↓ᵧ, by simp only [transcriptOutputs, ← List.map_append, hw]⟩
  show DDE.Total.transcript (attachEngineFully i E s) e n =
    (attachEngineFullyReplay i E (K + 1) e
      (DDE.Total.transcript s
        (absorbAttachEngineFully i E (K + 1) e n) (n * max K 1))↓ᵧ n).1
  rw [← hzs, hrep zs]

/-! ## An owned round stays inside its interface

`RequestsWithin i E` — the clause leg (a) introduced and nothing has yet
consumed — says the engine's requests carry addresses in `i`.  Read against
CR18 Definition 3.9's round it says the round *cannot look outside `i`*: the
only resource queries a round issues are the engine's own requests, so two
systems that answer alike inside `i` are indistinguishable to it.

That is `exists_mem_resolve_of_requestsWithin`, and it is the whole content of
the commutation: a round of `E` runs identically against `R` and against any
`R` with a converter attached at an interface disjoint from `i`.  The named
receipt `resolve_requests_within` — the round's resource-history extension is a
list of addresses of `i` — is its `S' = S` instance. -/

/-- An `ofEngine` converter requests exactly what its engine requests: the
converse of `Converter.DDC.mem_ofEngine_in`, which is what turns
`RequestsWithin` (a clause about the *engine*) into a statement about the
round.  Junk labels are impossible by construction, so the equivalence is
exact. -/
theorem mem_ofEngine_in_iff {U V X Y : Type u}
    (E : DDS (U ⊕ Option Y) (V ⊕ X)) (c : List (CIn U Y)) (x : X) :
    Sum.inr (InLabel.inside, x) ∈ (ofEngine E).1 c ↔
      Sum.inr x ∈ E.1 (c.map unlabel) := by
  constructor
  · intro h
    have h' : Sum.inr (InLabel.inside, x) ∈
        (E.1 (c.map unlabel)).map (fun m : V ⊕ X => Converter.DDC.moveOf m.swap) := h
    obtain ⟨m, hm, heq⟩ := (Part.mem_map_iff _).mp h'
    rcases m with v | x'
    · simp [Converter.DDC.moveOf] at heq
    · have hx : x' = x := by simpa [Converter.DDC.moveOf] using heq
      exact hx ▸ hm
  · exact Converter.DDC.mem_ofEngine_in

/-- **A round confined to `i` cannot see outside `i`** (DRIFT-REPAIR leg d, the
clause `RequestsWithin` was introduced for).  Let `P` be any correspondence
between resource histories of `S` and of `S'` that

* makes the two systems answer alike at every address of `i`, and
* survives extending both histories by the same address of `i`;

then a round of `E` against `S` from `P`-corresponding histories is the *same*
round against `S'` — same outer answer, same converter conversation — and the
histories it leaves still correspond.

The proof is `PFun.fix_bisim` at "same conversation, `P`-corresponding resource
histories".  The engine's move is read off the shared conversation, so it is
literally the same move on both sides; the only place the systems could differ
is the answer to a request, and `RequestsWithin i E` puts every request in `i`,
where `P` says they agree.  Nothing about `S`, `S'` or `P` beyond those two
clauses is used — in particular no engine class, no budget and no totality: a
round that diverges on one side diverges on the other. -/
theorem exists_mem_resolve_of_requestsWithin {i : Set Uni.{u}}
    {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hReq : RequestsWithin i E) {S S' : DDS Uni.{u} Uni.{u}}
    (P : List Uni.{u} → List Uni.{u} → Prop)
    (hans : ∀ ls ls', P ls ls' → ∀ x ∈ i, answer S ls x = answer S' ls' x)
    (hext : ∀ ls ls', P ls ls' → ∀ x ∈ i, P (ls ++ [x]) (ls' ++ [x]))
    {c c' : List (CIn Uni.{u} Uni.{u})} {ls ls' ms : List Uni.{u}} {v : Uni.{u}}
    (hP : P ls ls') (hres : (v, (c', ms)) ∈ resolve (ofEngine E) S (c, ls)) :
    ∃ ms', (v, (c', ms')) ∈ resolve (ofEngine E) S' (c, ls') ∧ P ms ms' := by
  have hstop : ∀ a a' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
      (a.1 = a'.1 ∧ P a.2 a'.2) →
      ∀ b : Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u}),
        Sum.inl b ∈ Converter.DDC.connStep (ofEngine E) S a →
        ∃ b' : Uni.{u} × (List (CIn Uni.{u} Uni.{u}) × List Uni.{u}),
          Sum.inl b' ∈ Converter.DDC.connStep (ofEngine E) S' a' ∧
            (b.1 = b'.1 ∧ b.2.1 = b'.2.1 ∧ P b.2.2 b'.2.2) := by
    rintro ⟨ca, la⟩ ⟨ca', la'⟩ ⟨hc, hPa⟩ b hb
    simp only at hc hPa
    subst hc
    rw [mem_connStep_iff] at hb
    rcases hb with ⟨v', hv', hbeq⟩ | ⟨x, -, hbeq⟩
    · obtain rfl : b = (v', (ca, la)) := by simpa using hbeq
      exact ⟨(v', (ca, la')),
        (mem_connStep_iff _ _ _ _).mpr (Or.inl ⟨v', hv', rfl⟩), rfl, rfl, hPa⟩
    · simp at hbeq
  have hstep : ∀ a a' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
      (a.1 = a'.1 ∧ P a.2 a'.2) →
      ∀ a₁ : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
        Sum.inr a₁ ∈ Converter.DDC.connStep (ofEngine E) S a →
        ∃ a₁' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
          Sum.inr a₁' ∈ Converter.DDC.connStep (ofEngine E) S' a' ∧
            (a₁.1 = a₁'.1 ∧ P a₁.2 a₁'.2) := by
    rintro ⟨ca, la⟩ ⟨ca', la'⟩ ⟨hc, hPa⟩ a₁ ha
    simp only at hc hPa
    subst hc
    rw [mem_connStep_iff] at ha
    rcases ha with ⟨v', -, haeq⟩ | ⟨x, hx, haeq⟩
    · simp at haeq
    · have hxi : x ∈ i := hReq _ _ ((mem_ofEngine_in_iff E ca x).mp hx)
      obtain rfl : a₁ =
          (ca ++ [Sum.inr (InLabel.inside, answer S la x)], la ++ [x]) := by
        simpa only [Sum.inr.injEq] using haeq
      refine ⟨(ca ++ [Sum.inr (InLabel.inside, answer S' la' x)], la' ++ [x]),
        (mem_connStep_iff _ _ _ _).mpr (Or.inr ⟨x, hx, rfl⟩), ?_, hext _ _ hPa x hxi⟩
      rw [hans _ _ hPa x hxi]
  obtain ⟨⟨v', c'', ms'⟩, hb', hv, hc'', hP'⟩ :=
    PFun.fix_bisim hstop hstep hres (c, ls') ⟨rfl, hP⟩
  simp only at hv hc'' hP'
  subst hv; subst hc''
  exact ⟨ms', hb', hP'⟩

/-- **An owned round stays inside its interface**: a resolving round of
`ofEngine E` extends the resource history it started from by addresses of `i`
only.

This is the statement leg (a) predicted `RequestsWithin` would earn its keep
by, and it is `exists_mem_resolve_of_requestsWithin` read at the trivial
correspondence "the same history, extended inside `i`". -/
theorem resolve_requests_within {i : Set Uni.{u}}
    {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hReq : RequestsWithin i E) (S : DDS Uni.{u} Uni.{u})
    {c c' : List (CIn Uni.{u} Uni.{u})} {xs xs' : List Uni.{u}} {v : Uni.{u}}
    (h : (v, (c', xs')) ∈ resolve (ofEngine E) S (c, xs)) :
    ∃ w : List Uni.{u}, xs' = xs ++ w ∧ ∀ x ∈ w, x ∈ i := by
  obtain ⟨ms', -, hms, w, hw, hwi⟩ :=
    exists_mem_resolve_of_requestsWithin hReq
      (S := S) (S' := S)
      (fun ls ls' => ls = ls' ∧ ∃ w : List Uni.{u}, ls' = xs ++ w ∧ ∀ x ∈ w, x ∈ i)
      (by rintro ls ls' ⟨rfl, -⟩ x -; rfl)
      (by
        rintro ls ls' ⟨rfl, w, rfl, hw⟩ x hx
        refine ⟨rfl, w ++ [x], by simp, ?_⟩
        intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hw y hy
        · exact (List.mem_singleton.mp hy) ▸ hx)
      ⟨rfl, [], by simp, by simp⟩ h
  exact ⟨w, by rw [hms, hw], hwi⟩

/-! ## The frontier, read backwards

The frontier section above says what the composite *does* at an extended outer
history, given the state it has reached.  The commutation induction needs the
converses: that the extended history reached a state only if the shorter one
did, and that the round its dispatch selects is the one that produced it.  Both
are the same `attachEngineFullyDrive_append` equation read from right to left,
and neither has an analogue in the whole-face layer, where the fold is
`driveFrom`. -/

/-- The empty outer history is refused, as it is by every DDS. -/
theorem attachEngineFully_nil (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    (attachEngineFully i E R).1 [] = Part.none :=
  Part.eq_none_iff.mpr fun v hv => by
    simp [attachEngineFullyRaw, attachEngineFullyDrive] at hv

/-- On a nonempty outer history, having reached a state and being accepted are
the same thing: the drive produces one answer per query, so a resolved drive of
a nonempty history has a last answer. -/
theorem exists_reachedAt_iff_mem_dom {us : List Uni.{u}} (hne : us ≠ []) :
    (∃ st, ReachedAt i E R us st) ↔ us ∈ dom (attachEngineFully i E R) := by
  constructor
  · rintro ⟨st, vs, hvs⟩
    have hlen : vs.length = us.length := attachEngineFullyDrive_length ([], []) us hvs
    have hvne : vs ≠ [] := fun h =>
      hne (List.eq_nil_of_length_eq_zero (by rw [← hlen, h, List.length_nil]))
    refine Part.dom_iff_mem.mpr ⟨vs.getLast hvne, ?_⟩
    rw [attachEngineFully_toPFun, mem_attachEngineFullyRaw_iff]
    exact ⟨(vs, st), hvs, List.getLast?_eq_some_getLast hvne⟩
  · exact exists_reachedAt_of_mem_dom

/-- A state reached on an extended history was reached on the prefix first. -/
theorem exists_reachedAt_of_reachedAt_append {us vs : List Uni.{u}}
    {st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (h : ReachedAt i E R (us ++ vs) st) : ∃ st', ReachedAt i E R us st' := by
  obtain ⟨ws, hws⟩ := h
  rw [attachEngineFullyDrive_append, Part.mem_bind_iff] at hws
  obtain ⟨ra, hra, -⟩ := hws
  exact ⟨ra.2, ra.1, hra⟩

/-- **The frontier drive, backwards**: the state reached on an extended outer
history is the state its round left — the converse of
`mem_attachEngineFullyDrive_concat`, and what lets an induction read the round
off the states it is carrying. -/
theorem exists_mem_attachEngineFullyRound_of_reachedAt {us : List Uni.{u}}
    {st₀ st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}} {q : Uni.{u}}
    (hst₀ : ReachedAt i E R us st₀) (h : ReachedAt i E R (us ++ [q]) st) :
    ∃ v, (v, st) ∈ attachEngineFullyRound i E R st₀ q := by
  obtain ⟨ws, hws⟩ := h
  rw [attachEngineFullyDrive_append, Part.mem_bind_iff] at hws
  obtain ⟨ra, hra, hrb⟩ := hws
  obtain ⟨vs₀, hvs₀⟩ := hst₀
  obtain rfl : ra = (vs₀, st₀) := Part.mem_unique hra hvs₀
  rw [Part.mem_map_iff] at hrb
  obtain ⟨rb, hrb, heq⟩ := hrb
  obtain ⟨wd, hwd, rfl⟩ := (mem_attachEngineFullyDrive_singleton _ _).mp hrb
  have hst2 : wd.2 = st := congrArg Prod.snd heq
  exact ⟨wd.1, hst2 ▸ hwd⟩

/-- Nothing happens after a history that reached no state. -/
theorem attachEngineFully_concat_eq_none {us : List Uni.{u}}
    (h : ¬ ∃ st, ReachedAt i E R us st) (q : Uni.{u}) :
    (attachEngineFully i E R).1 (us ++ [q]) = Part.none :=
  Part.eq_none_iff.mpr fun v hv =>
    h (exists_reachedAt_of_reachedAt_append
      (Exists.choose_spec
        (exists_reachedAt_of_mem_dom (Part.dom_iff_mem.mpr ⟨v, hv⟩))))

/-! ## A foreign attachment, watched from outside its interface

`attachEngineFully_transparent` says the composite *is* the resource at one
query outside `j`.  Watched over a whole interaction, that becomes a simulation
invariant, and it is the invariant leg (d) runs on:

> the composite's raw history `ys` and the resource's own history `xs` are
> related when the composite has reached `(cF, w)` on `ys` and `w` agrees with
> `xs` up to CR18 Definition 3.3 deletion.

The two lemmas below are the invariant's two obligations — the answers agree,
and the relation survives one more query outside `j`.  The deletion is
essential and is exactly leg (b)'s mixed-history phenomenon seen from the other
side: the composite's inner history keeps only what the resource accepted,
while the history reached inside it keeps what the composite was asked, so the
two lists are different and their kept prefixes are not. -/

/-- The invariant's first obligation: outside `j` the composite answers exactly
as the resource does — `attachEngineFully_transparent` at the completion's
answer, carried across the deletion by `answer_congr_keptPrefix`. -/
theorem answer_attachEngineFully_congr {j : Set Uni.{u}}
    {F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {cF : List (CIn Uni.{u} Uni.{u})} {ys xs w : List Uni.{u}}
    (hst : ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys) (cF, w))
    (hkp : keptPrefix R w = keptPrefix R xs) {x : Uni.{u}} (hx : x ∉ j) :
    answer (attachEngineFully j F R) ys x = answer R xs x := by
  rw [answer_attachEngineFully_foreign hst rfl hx]
  exact answer_congr_keptPrefix R x hkp

/-- The invariant's second obligation: one more query outside `j` leaves the
correspondence standing.  Both cases are deletion bookkeeping — an accepted
query is appended on both sides, a refused one is appended on neither, and
which of the two happens is the *same* event on both sides because the
composite accepts outside `j` exactly when the resource does. -/
theorem exists_reachedAt_attachEngineFully_concat {j : Set Uni.{u}}
    {F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {cF : List (CIn Uni.{u} Uni.{u})} {ys xs w : List Uni.{u}}
    (hst : ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys) (cF, w))
    (hkp : keptPrefix R w = keptPrefix R xs) {x : Uni.{u}} (hx : x ∉ j) :
    ∃ w' : List Uni.{u},
      ReachedAt j F R (keptPrefix (attachEngineFully j F R) (ys ++ [x])) (cF, w') ∧
        keptPrefix R w' = keptPrefix R (xs ++ [x]) := by
  by_cases hd : keptPrefix R w ++ [x] ∈ dom R
  · have hT : keptPrefix (attachEngineFully j F R) ys ++ [x] ∈
        dom (attachEngineFully j F R) :=
      (mem_dom_attachEngineFully_concat_not_mem hst hx).mpr hd
    refine ⟨w ++ [x], ?_, ?_⟩
    · rw [keptPrefix_append_singleton (attachEngineFully j F R) ys x, if_pos hT]
      exact attachEngineFully_reached_concat_not_mem hst hx hd
    · rw [keptPrefix_append_singleton R w x, if_pos hd,
        keptPrefix_append_singleton R xs x, if_pos (hkp ▸ hd), hkp]
  · have hT : keptPrefix (attachEngineFully j F R) ys ++ [x] ∉
        dom (attachEngineFully j F R) :=
      fun hc => hd ((mem_dom_attachEngineFully_concat_not_mem hst hx).mp hc)
    refine ⟨w, ?_, ?_⟩
    · rw [keptPrefix_append_singleton (attachEngineFully j F R) ys x, if_neg hT]
      exact hst
    · rw [keptPrefix_append_singleton R xs x, if_neg (hkp ▸ hd), hkp]

/-! ### The round transfer

The two obligations plugged into `exists_mem_resolve_of_requestsWithin`: an
owned round of `E` runs the same against the resource and against the resource
with a converter attached at an interface disjoint from `i`.  Both directions
are needed, because the commutation is an equation of *partial* values and
neither round is known to resolve in advance. -/

/-- **A foreign attachment is invisible to an owned round**, forwards: a round
against `attachEngineFully j F R` is the same round against `R`, and the
correspondence stands afterwards. -/
theorem exists_mem_resolve_of_mem_resolve_attachEngineFully {i j : Set Uni.{u}}
    {E F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})} (hij : Disjoint i j)
    (hE : RequestsWithin i E) {c c' cF : List (CIn Uni.{u} Uni.{u})}
    {ys xs w ys' : List Uni.{u}} {v : Uni.{u}}
    (hst : ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys) (cF, w))
    (hkp : keptPrefix R w = keptPrefix R xs)
    (hres : (v, (c', ys')) ∈ resolve (ofEngine E) (attachEngineFully j F R) (c, ys)) :
    ∃ xs' w' : List Uni.{u},
      (v, (c', xs')) ∈ resolve (ofEngine E) R (c, xs) ∧
        ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys') (cF, w') ∧
        keptPrefix R w' = keptPrefix R xs' := by
  obtain ⟨xs', hxs', w', hw', hkp'⟩ :=
    exists_mem_resolve_of_requestsWithin hE
      (S := attachEngineFully j F R) (S' := R)
      (fun ls ls' => ∃ w' : List Uni.{u},
        ReachedAt j F R (keptPrefix (attachEngineFully j F R) ls) (cF, w') ∧
          keptPrefix R w' = keptPrefix R ls')
      (by
        rintro ls ls' ⟨w', hw', hkp'⟩ x hx
        exact answer_attachEngineFully_congr hw' hkp' (Set.disjoint_left.mp hij hx))
      (by
        rintro ls ls' ⟨w', hw', hkp'⟩ x hx
        exact exists_reachedAt_attachEngineFully_concat hw' hkp'
          (Set.disjoint_left.mp hij hx))
      ⟨w, hst, hkp⟩ hres
  exact ⟨xs', w', hxs', hw', hkp'⟩

/-- **A foreign attachment is invisible to an owned round**, backwards.  Only
existence is claimed: the value is then forced by
`exists_mem_resolve_of_mem_resolve_attachEngineFully` and the uniqueness of
partial values. -/
theorem exists_mem_resolve_attachEngineFully_of_mem_resolve {i j : Set Uni.{u}}
    {E F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})} (hij : Disjoint i j)
    (hE : RequestsWithin i E) {c c' cF : List (CIn Uni.{u} Uni.{u})}
    {ys xs w xs' : List Uni.{u}} {v : Uni.{u}}
    (hst : ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys) (cF, w))
    (hkp : keptPrefix R w = keptPrefix R xs)
    (hres : (v, (c', xs')) ∈ resolve (ofEngine E) R (c, xs)) :
    ∃ ys' : List Uni.{u},
      (v, (c', ys')) ∈ resolve (ofEngine E) (attachEngineFully j F R) (c, ys) := by
  obtain ⟨ys', hys', -⟩ :=
    exists_mem_resolve_of_requestsWithin hE
      (S := R) (S' := attachEngineFully j F R)
      (fun ls ls' => ∃ w' : List Uni.{u},
        ReachedAt j F R (keptPrefix (attachEngineFully j F R) ls') (cF, w') ∧
          keptPrefix R w' = keptPrefix R ls)
      (by
        rintro ls ls' ⟨w', hw', hkp'⟩ x hx
        exact (answer_attachEngineFully_congr hw' hkp'
          (Set.disjoint_left.mp hij hx)).symm)
      (by
        rintro ls ls' ⟨w', hw', hkp'⟩ x hx
        exact exists_reachedAt_attachEngineFully_concat hw' hkp'
          (Set.disjoint_left.mp hij hx))
      ⟨w, hst, hkp⟩ hres
  exact ⟨ys', hys'⟩

/-! ## The commutation — MauRen16 §3.3's `(αR)β = α(Rβ)`

MauRen16 §3.3 postulates that converters attached at distinct interfaces
commute; on this carrier it is a theorem, and the only clauses it costs are
`Disjoint i j` and the two confinement clauses `RequestsWithin i E`,
`RequestsWithin j F`.

The induction is the one the old carrier's `System.attachEngine_comm` runs
(`Connect.lean`), transplanted: a snoc induction on the outer history carrying
the reached states of both nestings together with their cross-identifications.
Three things are different here, and all three are the repair's doing.

* The states are `ReachedAt`, so the two composites' *own* histories are the
  raw lists of everything they were asked, and the layer below each of them is
  read at its kept prefix.  The cross-identification of the two bottom
  histories is therefore `keptPrefix R xL = keptPrefix R xR`, not `xL = xR`:
  the two nestings ask `R` genuinely different query lists — a request the
  resource refuses never enters one composite's history and does enter the
  other's — and CR18 Definition 3.3 deletes exactly the difference.
* The converter conversations are identified *on the nose* (`cE`, `cF` are
  shared between the two sides), where the old proof identified projections
  `eProj i ehL = eProj i ehER`.  There is nothing to project: an engine here is
  attached to a query set, not lifted through a tagging, so its conversation is
  the same list on both sides.
* Transparency replaces the old `serve_transparent`.  On the old carrier a
  foreign round was two `serve` steps that had to be shown to pass through; on
  this one a foreign query is not a round at all, and
  `attachEngineFully_transparent` is an equation of partial values.

The three query cases are then exactly MauRen16's own case split: `q ∈ i` runs
`E`'s round on the left and, on the right, reaches `E` through the `j`-layer's
transparency — the same round by `exists_mem_resolve_…_attachEngineFully`;
`q ∈ j` is the mirror; `q ∉ i ∪ j` is transparent twice on both sides and
reduces to the bottom histories' agreement. -/

/-- The commutation induction: both nestings agree at every outer history, and
the states they have reached correspond — the two converter conversations are
shared, and the two bottom resource histories agree up to CR18 Definition 3.3
deletion. -/
theorem attachEngineFully_comm_aux {i j : Set Uni.{u}} (hij : Disjoint i j)
    {E F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hE : RequestsWithin i E) (hF : RequestsWithin j F) (R : DDS Uni.{u} Uni.{u}) :
    ∀ us : List Uni.{u},
      (attachEngineFully i E (attachEngineFully j F R)).1 us =
          (attachEngineFully j F (attachEngineFully i E R)).1 us ∧
        ∀ (cE : List (CIn Uni.{u} Uni.{u})) (ys : List Uni.{u})
          (cF : List (CIn Uni.{u} Uni.{u})) (zs : List Uni.{u}),
          ReachedAt i E (attachEngineFully j F R) us (cE, ys) →
          ReachedAt j F (attachEngineFully i E R) us (cF, zs) →
          ∃ xL xR : List Uni.{u},
            ReachedAt j F R (keptPrefix (attachEngineFully j F R) ys) (cF, xL) ∧
            ReachedAt i E R (keptPrefix (attachEngineFully i E R) zs) (cE, xR) ∧
            keptPrefix R xL = keptPrefix R xR := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨by rw [attachEngineFully_nil, attachEngineFully_nil], ?_⟩
      intro cE ys cF zs h1 h2
      have e1 := ReachedAt.unique h1 (reachedAt_nil i E (attachEngineFully j F R))
      have e2 := ReachedAt.unique h2 (reachedAt_nil j F (attachEngineFully i E R))
      simp only [Prod.mk.injEq] at e1 e2
      obtain ⟨rfl, rfl⟩ := e1
      obtain ⟨rfl, rfl⟩ := e2
      exact ⟨[], [], reachedAt_nil j F R, reachedAt_nil i E R, rfl⟩
  | append_singleton us q ih =>
      obtain ⟨ihval, ihst⟩ := ih
      have hexiff : (∃ st, ReachedAt i E (attachEngineFully j F R) us st) ↔
          (∃ st, ReachedAt j F (attachEngineFully i E R) us st) := by
        by_cases hne : us = []
        · subst hne
          exact iff_of_true ⟨_, reachedAt_nil _ _ _⟩ ⟨_, reachedAt_nil _ _ _⟩
        · rw [exists_reachedAt_iff_mem_dom hne, exists_reachedAt_iff_mem_dom hne]
          show ((attachEngineFully i E (attachEngineFully j F R)).1 us).Dom ↔
            ((attachEngineFully j F (attachEngineFully i E R)).1 us).Dom
          rw [ihval]
      by_cases hex : ∃ st, ReachedAt i E (attachEngineFully j F R) us st
      · obtain ⟨⟨cE, ys⟩, hstL⟩ := hex
        obtain ⟨⟨cF, zs⟩, hstR⟩ := hexiff.mp ⟨_, hstL⟩
        obtain ⟨xL, xR, hA, hB, hkp⟩ := ihst cE ys cF zs hstL hstR
        by_cases hqi : q ∈ i
        · -- the outer converter owns the query; on the right the `j`-layer is
          -- transparent at it, so both sides run one round of `E`
          have hqj : q ∉ j := Set.disjoint_left.mp hij hqi
          have hLv : (attachEngineFully i E (attachEngineFully j F R)).1 (us ++ [q]) =
              (resolve (ofEngine E) (attachEngineFully j F R)
                (cE ++ [Sum.inl (InLabel.outside, q)], ys)).map Prod.fst := by
            rw [attachEngineFully_concat_round hstL q,
              attachEngineFullyRound_mem E (attachEngineFully j F R) (cE, ys) hqi]
          have hRv : (attachEngineFully j F (attachEngineFully i E R)).1 (us ++ [q]) =
              (resolve (ofEngine E) R
                (cE ++ [Sum.inl (InLabel.outside, q)], xR)).map Prod.fst := by
            rw [attachEngineFully_transparent hstR hqj,
              attachEngineFully_concat_round hB q,
              attachEngineFullyRound_mem E R (cE, xR) hqi]
          refine ⟨?_, ?_⟩
          · rw [hLv, hRv]
            refine Part.ext fun v => ?_
            simp only [Part.mem_map_iff]
            constructor
            · rintro ⟨⟨v', c'', ys'⟩, hmem, rfl⟩
              obtain ⟨xs', -, hR, -, -⟩ :=
                exists_mem_resolve_of_mem_resolve_attachEngineFully hij hE hA hkp hmem
              exact ⟨(v', (c'', xs')), hR, rfl⟩
            · rintro ⟨⟨v', c'', xs'⟩, hmem, rfl⟩
              obtain ⟨ys', hT⟩ :=
                exists_mem_resolve_attachEngineFully_of_mem_resolve hij hE hA hkp hmem
              exact ⟨(v', (c'', ys')), hT, rfl⟩
          · intro cE₁ ys₁ cF₁ zs₁ h1 h2
            obtain ⟨v, hv⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstL h1
            rw [attachEngineFullyRound_mem E (attachEngineFully j F R) (cE, ys) hqi] at hv
            obtain ⟨xs', w', hresR, hA₁, hkp₁⟩ :=
              exists_mem_resolve_of_mem_resolve_attachEngineFully hij hE hA hkp hv
            obtain ⟨y, hy⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstR h2
            rw [attachEngineFullyRound_not_mem F (attachEngineFully i E R) (cF, zs) hqj,
              Part.mem_map_iff] at hy
            obtain ⟨y₀, hy₀, heq⟩ := hy
            simp only [Prod.mk.injEq] at heq
            obtain ⟨-, rfl, rfl⟩ := heq
            have hdom : keptPrefix (attachEngineFully i E R) zs ++ [q] ∈
                dom (attachEngineFully i E R) := Part.dom_iff_mem.mpr ⟨y₀, hy₀⟩
            refine ⟨w', xs', hA₁, ?_, hkp₁⟩
            rw [keptPrefix_append_singleton (attachEngineFully i E R) zs q,
              if_pos hdom]
            exact attachEngineFully_reached_concat_mem hB hqi hresR
        · by_cases hqj : q ∈ j
          · -- the mirror case: the inner converter owns the query
            have hLv : (attachEngineFully i E (attachEngineFully j F R)).1 (us ++ [q]) =
                (resolve (ofEngine F) R
                  (cF ++ [Sum.inl (InLabel.outside, q)], xL)).map Prod.fst := by
              rw [attachEngineFully_transparent hstL hqi,
                attachEngineFully_concat_round hA q,
                attachEngineFullyRound_mem F R (cF, xL) hqj]
            have hRv : (attachEngineFully j F (attachEngineFully i E R)).1 (us ++ [q]) =
                (resolve (ofEngine F) (attachEngineFully i E R)
                  (cF ++ [Sum.inl (InLabel.outside, q)], zs)).map Prod.fst := by
              rw [attachEngineFully_concat_round hstR q,
                attachEngineFullyRound_mem F (attachEngineFully i E R) (cF, zs) hqj]
            refine ⟨?_, ?_⟩
            · rw [hLv, hRv]
              refine Part.ext fun v => ?_
              simp only [Part.mem_map_iff]
              constructor
              · rintro ⟨⟨v', c'', xs'⟩, hmem, rfl⟩
                obtain ⟨zs', hT⟩ :=
                  exists_mem_resolve_attachEngineFully_of_mem_resolve hij.symm hF hB
                    hkp.symm hmem
                exact ⟨(v', (c'', zs')), hT, rfl⟩
              · rintro ⟨⟨v', c'', zs'⟩, hmem, rfl⟩
                obtain ⟨xs', -, hR, -, -⟩ :=
                  exists_mem_resolve_of_mem_resolve_attachEngineFully hij.symm hF hB
                    hkp.symm hmem
                exact ⟨(v', (c'', xs')), hR, rfl⟩
            · intro cE₁ ys₁ cF₁ zs₁ h1 h2
              obtain ⟨y, hy⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstR h2
              rw [attachEngineFullyRound_mem F (attachEngineFully i E R) (cF, zs) hqj] at hy
              obtain ⟨xs', w', hresR, hB₁, hkp₁⟩ :=
                exists_mem_resolve_of_mem_resolve_attachEngineFully hij.symm hF hB
                  hkp.symm hy
              obtain ⟨v, hv⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstL h1
              rw [attachEngineFullyRound_not_mem E (attachEngineFully j F R) (cE, ys) hqi,
                Part.mem_map_iff] at hv
              obtain ⟨v₀, hv₀, heq⟩ := hv
              simp only [Prod.mk.injEq] at heq
              obtain ⟨-, rfl, rfl⟩ := heq
              have hdom : keptPrefix (attachEngineFully j F R) ys ++ [q] ∈
                  dom (attachEngineFully j F R) := Part.dom_iff_mem.mpr ⟨v₀, hv₀⟩
              refine ⟨xs', w', ?_, hB₁, hkp₁.symm⟩
              rw [keptPrefix_append_singleton (attachEngineFully j F R) ys q,
                if_pos hdom]
              exact attachEngineFully_reached_concat_mem hA hqj hresR
          · -- neither converter owns the query: transparency twice on each
            -- side, and the two bottom histories agree
            have hLv : (attachEngineFully i E (attachEngineFully j F R)).1 (us ++ [q]) =
                R.1 (keptPrefix R xL ++ [q]) := by
              rw [attachEngineFully_transparent hstL hqi,
                attachEngineFully_transparent hA hqj]
            have hRv : (attachEngineFully j F (attachEngineFully i E R)).1 (us ++ [q]) =
                R.1 (keptPrefix R xR ++ [q]) := by
              rw [attachEngineFully_transparent hstR hqj,
                attachEngineFully_transparent hB hqi]
            refine ⟨by rw [hLv, hRv, hkp], ?_⟩
            intro cE₁ ys₁ cF₁ zs₁ h1 h2
            obtain ⟨v, hv⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstL h1
            rw [attachEngineFullyRound_not_mem E (attachEngineFully j F R) (cE, ys) hqi,
              Part.mem_map_iff] at hv
            obtain ⟨v₀, -, heqL⟩ := hv
            simp only [Prod.mk.injEq] at heqL
            obtain ⟨-, rfl, rfl⟩ := heqL
            obtain ⟨y, hy⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hstR h2
            rw [attachEngineFullyRound_not_mem F (attachEngineFully i E R) (cF, zs) hqj,
              Part.mem_map_iff] at hy
            obtain ⟨y₀, -, heqR⟩ := hy
            simp only [Prod.mk.injEq] at heqR
            obtain ⟨-, rfl, rfl⟩ := heqR
            obtain ⟨xL', hL', hkpL'⟩ :=
              exists_reachedAt_attachEngineFully_concat hA rfl hqj
            obtain ⟨xR', hR', hkpR'⟩ :=
              exists_reachedAt_attachEngineFully_concat hB rfl hqi
            exact ⟨xL', xR', hL', hR',
              hkpL'.trans ((keptPrefix_append_congr R [q] hkp).trans hkpR'.symm)⟩
      · have hexR : ¬ ∃ st, ReachedAt j F (attachEngineFully i E R) us st :=
          fun hc => hex (hexiff.mpr hc)
        refine ⟨by rw [attachEngineFully_concat_eq_none hex,
          attachEngineFully_concat_eq_none hexR], ?_⟩
        intro cE₁ ys₁ cF₁ zs₁ h1 h2
        exact absurd (exists_reachedAt_of_reachedAt_append h1) hex

/-- **Composition-order independence** (MauRen16 §3.3's `(αR)β = α(Rβ)`, matrix
row 22): engines attached at disjoint interfaces commute, as an equation of
systems.

The paper takes this as an axiom of the cryptographic algebra; here it is a
theorem, and its price is exactly three clauses.  `Disjoint i j` is the
statement's own hypothesis.  `RequestsWithin i E` and `RequestsWithin j F` say
each engine reaches only its own interface, and they are not bookkeeping: an
engine that requests inside the *other* converter's interface would be served
by that converter in one nesting and by the resource in the other, and the
equation is false.  Nothing about the engines' *reactions* is needed — not
`InnerTotal`, not CR18 Definition 3.8's budget, not the uniform bound —
because commutation is an equation of partial values, and a round that
diverges on one side diverges on the other. -/
theorem attachEngineFully_comm {i j : Set Uni.{u}} (hij : Disjoint i j)
    {E F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hE : RequestsWithin i E) (hF : RequestsWithin j F) (R : DDS Uni.{u} Uni.{u}) :
    attachEngineFully i E (attachEngineFully j F R) =
      attachEngineFully j F (attachEngineFully i E R) :=
  Subtype.ext (funext fun us => (attachEngineFully_comm_aux hij hE hF R us).1)

/-! ## Transparency over a whole history, and `⊣` as an attachment

`attachEngineFully_transparent` is the *one-round* statement: at a single query
outside `i` the composite is the resource.  Over an outer history that never
enters `i` at all it becomes an equation of partial values at that history, and
then an equation of **systems** once the history is also blocked.

That equation is what identifies MauRen16 §3.4's blocking converter `⊣` with an
interface-local attachment — of the engine that never moves — and it is what
makes every law of the carrier right-outbound.  Both are §3.4's obligations, and
neither has an analogue at whole-face application, where there is no foreign
face to be transparent at. -/

/-- A blocked system is the unblocked one at every history the block admits. -/
theorem blockSet_apply_of_forall_not_mem {X : Type u₃} {Y : Type u₄} {A : Set X}
    (S : DDS X Y) {l : List X} (hl : ∀ q ∈ l, q ∉ A) :
    (blockSet A S).1 l = S.1 l :=
  Part.ext' (and_iff_left hl) fun _ _ => rfl

/-- **The state reached on a history that never enters `i`**: every round is
foreign, so the converter conversation stays empty and the resource history is
the outer history itself — CR18 Definition 3.3's deletion never fires, because
a refused query would have ended the drive. -/
theorem reachedAt_of_forall_not_mem :
    ∀ {us : List Uni.{u}}, (∀ q ∈ us, q ∉ i) → (us ∈ dom R ∨ us = []) →
      ReachedAt i E R us ([], us) := by
  intro us
  induction us using List.reverseRecOn with
  | nil => exact fun _ _ => reachedAt_nil i E R
  | append_singleton ws q ih =>
      intro hus hd
      have hq : q ∉ i := hus q (by simp)
      have hdom : ws ++ [q] ∈ dom R := by
        rcases hd with hd | hd
        · exact hd
        · exact absurd hd (by simp)
      have hws : ws ∈ dom R ∨ ws = [] := by
        by_cases hnil : ws = []
        · exact Or.inr hnil
        · exact Or.inl (prefix_closed R ⟨[q], rfl⟩ hnil hdom)
      exact attachEngineFully_reached_concat_not_mem
        (ih (fun x hx => hus x (by simp [hx])) hws) hq
        (by rw [keptPrefix_eq_self_of_mem_or_empty R hws]; exact hdom)

/-- **Transparency over a whole history**: at an outer history that never enters
`i`, the composite and the resource are one and the same partial value — same
domain, same answer, same refusal.

The two cases are the two ways a history can end.  If the resource accepted the
prefix, the reached state is the prefix itself and `attachEngineFully_transparent`
applies with nothing to delete; if it did not, both sides died there and stay
dead, because both domains are prefix-closed. -/
theorem attachEngineFully_of_forall_not_mem :
    ∀ {us : List Uni.{u}}, (∀ q ∈ us, q ∉ i) →
      (attachEngineFully i E R).1 us = R.1 us := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      intro _
      rw [attachEngineFully_nil]
      exact (Part.eq_none_iff'.mpr (empty_not_mem R)).symm
  | append_singleton ws q ih =>
      intro hus
      have hq : q ∉ i := hus q (by simp)
      have hws : ∀ x ∈ ws, x ∉ i := fun x hx => hus x (by simp [hx])
      by_cases hd : ws ∈ dom R ∨ ws = []
      · rw [attachEngineFully_transparent (reachedAt_of_forall_not_mem hws hd) hq,
          keptPrefix_eq_self_of_mem_or_empty R hd]
      · have hnil : ws ≠ [] := fun h => hd (Or.inr h)
        have hRdom : ws ∉ dom R := fun h => hd (Or.inl h)
        have hRq : ws ++ [q] ∉ dom R := fun h => hRdom (prefix_closed R ⟨[q], rfl⟩ hnil h)
        have hCdom : ws ∉ dom (attachEngineFully i E R) := fun h => by
          have h' : ((attachEngineFully i E R).1 ws).Dom := h
          rw [ih hws] at h'
          exact hRdom h'
        have hCq : ws ++ [q] ∉ dom (attachEngineFully i E R) := fun h =>
          hCdom (prefix_closed _ ⟨[q], rfl⟩ hnil h)
        rw [Part.eq_none_iff'.mpr hCq, Part.eq_none_iff'.mpr hRq]

/-- **MauRen16 §3.4's `⊣` is an interface-local attachment.**  Blocking the
query set `A` *is* `αᴬ` for the engine `Z` that never moves: outside `A` the
dispatch hands the query to the resource verbatim, and inside `A` the round
cannot resolve, because a resolved round certifies the engine's own first move
(`mem_dom_of_resolve_dom`) and `Z` has none.

This is what buys `⊣`'s commutation with a foreign attachment: `block` inherits
`attachAt_comm` instead of needing a second commutation induction of its own.
The hypothesis is on the engine alone and is the sharpest form of "the
converter never answers"; no engine class is consumed, and in particular `Z` is
not `InnerTotal`. -/
theorem attachEngineFully_eq_blockSet_of_dom_eq_empty {A : Set Uni.{u}}
    {Z : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hZ : ∀ c, c ∉ dom Z) (S : DDS Uni.{u} Uni.{u}) :
    attachEngineFully A Z S = blockSet A S := by
  refine Subtype.ext (funext fun us => ?_)
  show (attachEngineFully A Z S).1 us = (blockSet A S).1 us
  by_cases hus : ∀ q ∈ us, q ∉ A
  · exact (attachEngineFully_of_forall_not_mem (i := A) (E := Z) (R := S) hus).trans
      (blockSet_apply_of_forall_not_mem S hus).symm
  · have hex : ∃ q ∈ us, q ∈ A := by
      by_contra hc
      exact hus fun q hq hqA => hc ⟨q, hq, hqA⟩
    obtain ⟨q, hqus, hqA⟩ := hex
    obtain ⟨ws, rest, rfl⟩ := List.append_of_mem hqus
    have hCq : ws ++ [q] ∉ dom (attachEngineFully A Z S) := by
      intro hc
      by_cases hex : ∃ st, ReachedAt A Z S ws st
      · obtain ⟨⟨c, xs⟩, hst⟩ := hex
        exact hZ _ (mem_dom_of_resolve_dom Z S _ xs
          ((mem_dom_attachEngineFully_concat_mem hst hqA).mp hc))
      · exact (Part.eq_none_iff'.mp (attachEngineFully_concat_eq_none hex q)) hc
    have hpre : ws ++ [q] <+: ws ++ q :: rest := ⟨rest, by simp⟩
    have hne : ws ++ [q] ≠ [] := by simp
    have h₁ : (attachEngineFully A Z S).1 (ws ++ q :: rest) = Part.none :=
      Part.eq_none_iff'.mpr fun hc => hCq (prefix_closed _ hpre hne hc)
    have h₂ : (blockSet A S).1 (ws ++ q :: rest) = Part.none :=
      Part.eq_none_iff'.mpr fun hc =>
        ((mem_dom_blockSet A S _).mp hc).2 q (by simp) hqA
    rw [h₁, h₂]

/-- **MauRen16 §3.4's right-outboundness, on the carrier**: a converter attached
*inside* the blocked query set has no effect once the set is blocked.

There is nothing to compute: `A` is blocked, `j ⊆ A`, so no query of a surviving
history ever reaches the converter's interface and the whole interaction is
transparent.  This is the system-level content of "no signalling from the right
interface to the left", and it needs neither an engine class nor
`RequestsWithin` — an engine that is never activated cannot request
anything. -/
theorem blockSet_attachEngineFully_of_subset {A j : Set Uni.{u}} (hjA : j ⊆ A)
    (F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (S : DDS Uni.{u} Uni.{u}) :
    blockSet A (attachEngineFully j F S) = blockSet A S := by
  refine Subtype.ext (funext fun us => ?_)
  show (blockSet A (attachEngineFully j F S)).1 us = (blockSet A S).1 us
  by_cases hus : ∀ q ∈ us, q ∉ A
  · rw [blockSet_apply_of_forall_not_mem _ hus, blockSet_apply_of_forall_not_mem S hus]
    exact attachEngineFully_of_forall_not_mem (i := j) (E := F) (R := S)
      fun x hx hxj => hus x hx (hjA hxj)
  · have h₁ : (blockSet A (attachEngineFully j F S)).1 us = Part.none :=
      Part.eq_none_iff'.mpr fun hc =>
        hus fun q hq => ((mem_dom_blockSet A _ _).mp hc).2 q hq
    have h₂ : (blockSet A S).1 us = Part.none :=
      Part.eq_none_iff'.mpr fun hc =>
        hus fun q hq => ((mem_dom_blockSet A S _).mp hc).2 q hq
    rw [h₁, h₂]


/-! ## Attachment is local in the resource

UPSTREAM-CANDIDATE (the attachment surface itself; every construction whose
argument is "what the resource does outside the region the protocol queries is
irrelevant" needs this and nothing weaker).

MauRen16 §3.3's `αⁱ` reads the resource only through the requests its own
engine emits, so the composite depends on the resource only at the request
histories those requests build.  Two resources that answer alike there give
*equal* composites — not merely indistinguishable ones.

**The reach is a sum, not a bound.**  CR18 Definition 3.8's clause (printed
p. 62) bounds the requests of *one round*; an interaction has as many rounds as
it has outer queries, so the request history an interaction can build is the
running total of the rounds' budgets and nothing smaller.  The accounting is
therefore carried by a function `cost` on outer histories, with the single
hypothesis `hpay` that opening a round for one more outer query buys at least
that round's budget.  A statement with `β` in place of `cost` — "the composite
depends on the resource only at histories of length `≤ β`" — is **false** for
every engine that answers more than one outer query.

The interface is `Set.univ`: a query outside `i` reaches the resource verbatim
(`attachEngineFully_transparent`) and is not accounted for by the engine's
budget, so the interface-local statement would need `cost` to pay for foreign
queries as well.  Nothing below needs it and it is not claimed.
-/

section Locality

variable {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {cost : List Uni.{u} → ℕ}
  {R' : DDS Uni.{u} Uni.{u}}

/-- A cost that pays for every round only grows: the budget it must cover is a
natural number, so extending the outer history cannot lower the total.  This is
what lets the accounting be discharged once, at the end of the outer history,
instead of at every prefix. -/
theorem cost_le_append_of_budget
    (hpay : ∀ (done : List Uni.{u}) (q : Uni.{u}) (c : List (CIn Uni.{u} Uni.{u})),
      β ((c ++ [Sum.inl (InLabel.outside, q)]).map unlabel) + cost done ≤ cost (done ++ [q]))
    (a b : List Uni.{u}) : cost a ≤ cost (a ++ b) := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b q ih =>
      have := hpay (a ++ b) q []
      rw [← List.append_assoc]
      omega

/-- **The driven interaction is local in the resource**: over an outer history
of total cost `cost (done ++ rest)`, the drive consults the resource only after
request histories shorter than that, so two resources agreeing there drive
alike.

The invariant is that the request history reached is no longer than the cost of
the outer queries already driven; it is maintained by
`length_le_of_mem_resolve`, which bounds one round's requests by that round's
budget, while `hpay` says the new outer query's cost covers that budget. -/
theorem attachEngineFullyDrive_congr_of_answer_eq (hβ : AnswersWithinBudget E β)
    (hpay : ∀ (done : List Uni.{u}) (q : Uni.{u}) (c : List (CIn Uni.{u} Uni.{u})),
      β ((c ++ [Sum.inl (InLabel.outside, q)]).map unlabel) + cost done ≤ cost (done ++ [q])) :
    ∀ (rest done : List Uni.{u}) (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}),
      (∀ (zs : List Uni.{u}) (x : Uni.{u}), zs.length < cost (done ++ rest) →
        answer R zs x = answer R' zs x) →
      st.2.length ≤ cost done →
        attachEngineFullyDrive (Set.univ : Set Uni.{u}) E R st rest
          = attachEngineFullyDrive (Set.univ : Set Uni.{u}) E R' st rest := by
  intro rest
  induction rest with
  | nil => intro done st _ _; rfl
  | cons q rest ih =>
      intro done st hagree hlen
      have hcons : done ++ q :: rest = (done ++ [q]) ++ rest := by simp
      have hmono : cost (done ++ [q]) ≤ cost (done ++ q :: rest) := by
        rw [hcons]; exact cost_le_append_of_budget hpay _ _
      have hstep := hpay done q st.1
      have hrd : attachEngineFullyRound (Set.univ : Set Uni.{u}) E R st q
          = attachEngineFullyRound (Set.univ : Set Uni.{u}) E R' st q := by
        rw [attachEngineFullyRound_mem _ _ _ (Set.mem_univ q),
          attachEngineFullyRound_mem _ _ _ (Set.mem_univ q)]
        refine resolve_congr_of_answer_eq hβ
          (β ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)) _ st.2 le_rfl ?_
        intro zs x hzs
        exact hagree zs x (by omega)
      show (attachEngineFullyRound (Set.univ : Set Uni.{u}) E R st q).bind _
        = (attachEngineFullyRound (Set.univ : Set Uni.{u}) E R' st q).bind _
      rw [hrd]
      refine Part.ext fun z => ?_
      simp only [Part.mem_bind_iff]
      refine exists_congr fun a => and_congr_right fun ha => ?_
      obtain ⟨v, c₂, xs₂⟩ := a
      have hmem : (v, (c₂, xs₂)) ∈ resolve (ofEngine E) R'
          (st.1 ++ [Sum.inl (InLabel.outside, q)], st.2) := by
        rw [attachEngineFullyRound_mem _ _ _ (Set.mem_univ q)] at ha
        exact ha
      have hA := length_le_of_mem_resolve hβ R'
        (β ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)) _ st.2 le_rfl hmem
      rw [ih (done ++ [q]) (c₂, xs₂) (by rw [← hcons]; exact hagree)
        (by simpa using (by omega : xs₂.length ≤ cost (done ++ [q])))]

/-- **Attachment is local in the resource**, at one outer history: the
composite's answer to `l` is determined by the resource's answers after request
histories shorter than `cost l`. -/
theorem attachEngineFully_congr_of_answer_eq (hβ : AnswersWithinBudget E β)
    (hpay : ∀ (done : List Uni.{u}) (q : Uni.{u}) (c : List (CIn Uni.{u} Uni.{u})),
      β ((c ++ [Sum.inl (InLabel.outside, q)]).map unlabel) + cost done ≤ cost (done ++ [q]))
    (l : List Uni.{u})
    (hagree : ∀ (zs : List Uni.{u}) (x : Uni.{u}), zs.length < cost l →
      answer R zs x = answer R' zs x) :
    (attachEngineFully (Set.univ : Set Uni.{u}) E R).1 l
      = (attachEngineFully (Set.univ : Set Uni.{u}) E R').1 l := by
  simp only [attachEngineFully_toPFun, attachEngineFullyRaw]
  rw [attachEngineFullyDrive_congr_of_answer_eq hβ hpay l [] ([], [])
    (by simpa using hagree) (by simp)]

/-- **Attachment under a domain filter is local in the resource**: if CR18
§3.4.3's filter (unnumbered prose, printed p. 62) admits only outer histories
of cost at most `N`, the filtered composite is determined by the resource's
answers after request histories shorter than `N`, and two such resources give
equal filtered composites.

This is the form an application uses: the outer restriction is what caps the
reach, so the resource is pinned down only on a bounded region. -/
theorem filterDom_attachEngineFully_congr_of_answer_eq (hβ : AnswersWithinBudget E β)
    (hpay : ∀ (done : List Uni.{u}) (q : Uni.{u}) (c : List (CIn Uni.{u} Uni.{u})),
      β ((c ++ [Sum.inl (InLabel.outside, q)]).map unlabel) + cost done ≤ cost (done ++ [q]))
    (P : List Uni.{u} → Prop) (hP : PrefixClosed P) (N : ℕ) (hadm : ∀ l, P l → cost l ≤ N)
    (hagree : ∀ (zs : List Uni.{u}) (x : Uni.{u}), zs.length < N →
      answer R zs x = answer R' zs x) :
    filterDom P hP (attachEngineFully (Set.univ : Set Uni.{u}) E R)
      = filterDom P hP (attachEngineFully (Set.univ : Set Uni.{u}) E R') := by
  apply Subtype.ext
  funext l
  have hmem : ∀ (S : DDS Uni.{u} Uni.{u}) (v : Uni.{u}),
      v ∈ (filterDom P hP S).1 l ↔ (v ∈ S.1 l ∧ P l) := by
    intro S v
    constructor
    · rintro ⟨⟨hd, hp⟩, hv⟩; exact ⟨⟨hd, hv⟩, hp⟩
    · rintro ⟨⟨hd, hv⟩, hp⟩; exact ⟨⟨hd, hp⟩, hv⟩
  refine Part.ext fun v => ?_
  by_cases hPl : P l
  · rw [hmem, hmem, attachEngineFully_congr_of_answer_eq hβ hpay l
      (fun zs x hzs => hagree zs x (lt_of_lt_of_le hzs (hadm l hPl)))]
  · rw [hmem, hmem]
    simp [hPl]

end Locality
end

end System

/-! ## The repaired attachment is nonexpanding

The metric consequence of the absorption receipt, through the pushforward
reduction — MauRen16 §4.3's "absorbed by the distinguisher" at the
interface-indexed `αⁱ`.  The Σ-level re-basing (the generator family, the
budgeted monoid and the S4 receipts over it) is leg (c); this is the single
membership those will be assembled from, and it is stated at the raw
pushforward so that leg (c) can name the generator as it pleases. -/

noncomputable section

open Probability (Distribution)

universe u

/-- **The interface-local attachment never helps a distinguisher.**  Whatever
an environment learns from the converted resource it learns from the resource
itself, by running the engine on the queries of `i` and relaying the rest —
`System.exists_absorb_attachEngineFully` through the pushforward reduction.

`System.RequestsWithin i E` is deliberately absent: absorption is indifferent
to where the engine's requests point.  It is the commutation of attachments at
disjoint interfaces (leg d) that needs that clause, not this. -/
theorem attachEngineFully_mem_nonexpandingConverters {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinBudget E β)
    (hK : ∀ l, β l ≤ K) :
    (fun L => Distribution.fTransform (System.attachEngineFully i E) L) ∈
      nonexpandingConverters.{u} := fun RL SL =>
  PDS.advFullyDefined_fTransform_le (System.attachEngineFully i E) RL SL
    fun e n => System.exists_absorb_attachEngineFully hIT hβ hK e n

/-! ## The interface-indexed Σ

The Φ-level re-basing.  `attachFully` takes the whole face because
`connectFully` does; the generator here carries the interface `i` it acts at —
MauRen16 §3.3's `αⁱ` — and whole-face application is recovered as
`i = Set.univ` (`attachAt_univ`).

The two parallel frames at a subprobability partner are **the same sets**,
spelled exactly as in `converterMonoidFully` / `converterMonoidFullyBudgeted`.
The block family is **widened** (Marc, 2026-08-19) to CR18 §3.4.3's domain
filters (unnumbered prose, printed p. 62 — Definition 3.10 is only the `[q]`
notation) at an arbitrary prefix-closed predicate: `block Q` is the
instance at "avoid `Q`" (`block_eq_filterPhi`) and `filterQueries q` the
instance at "at most `q` answered queries", so every statement proved over the
old family stands and the query limit is now a converter of the Σ rather than
merely a nonexpanding endomorphism.  The receipt the widening costs is
`filterPhi_mem_nonexpandingConverters` (`Absorb.lean`).

The old monoids are **superseded, not deleted**.  They keep their statements,
their proofs and their receipts, and the demotion bridge places them inside the
re-based ones: `converterMonoidFullyBudgeted_le_converterMonoidAt` and
`converterMonoidFully_le_converterMonoidAtWeakBudget`.  Nothing that cites them
breaks; new statements name the interface-indexed monoid. -/

/-- **The interface-indexed attachment endomorphism of Φ** — MauRen16 §3.3's
`αⁱ` at the Φ level: the deterministic engine `E`, attached at the interface
`i` of the completion of the resource.  Queries outside `i` reach the resource
verbatim, refusals included; queries inside `i` run one CR18 Definition 3.9
round of `E` against `R⊥`.

The Φ-level counterpart of `System.attachEngineFully`, and the re-based
generator of the metric-facing Σ.  `attachFully` is its `i = Set.univ` case
(`attachAt_univ`); `attach` stays as it is and stays refuted (B4). -/
def attachAt (i : Set Uni.{u})
    (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) :
    Function.End Phi.{u} :=
  fun L => Distribution.fTransform (System.attachEngineFully i E) L

/-- **The demotion bridge at the Φ level**: the migrated whole-face attachment
is the interface-indexed one at the full interface.  This is what makes the
supersession of `converterMonoidFully(Budgeted)` a one-line containment rather
than a re-proof — `System.attachEngineFully_univ` pushed forward. -/
theorem attachAt_univ
    (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) :
    attachAt Set.univ E = attachFully E := by
  have h : System.attachEngineFully (Set.univ : Set Uni.{u}) E
      = System.connectFully E :=
    funext fun R => System.attachEngineFully_univ E R
  exact congrArg Distribution.fTransform h

/-- **The interface-indexed attachment never helps a distinguisher**, at the
named generator: `attachEngineFully_mem_nonexpandingConverters` read through
`attachAt`.  The re-based counterpart of
`attachFully_mem_nonexpandingConverters`.

`System.RequestsWithin i E` is deliberately absent: absorption is indifferent
to where the engine's requests point. -/
theorem attachAt_mem_nonexpandingConverters {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinBudget E β)
    (hK : ∀ l, β l ≤ K) :
    attachAt i E ∈ nonexpandingConverters.{u} :=
  attachEngineFully_mem_nonexpandingConverters hIT hβ hK

/-- **The interface-indexed converter monoid at A6's budget** — the re-based
counterpart of `converterMonoidFully`: interface-indexed attachments of engines
that are inner-total and budgeted *history by history*, CR18 §3.4.3's domain
filters (unnumbered prose, printed p. 62), and the parallel frames at a
subprobability partner.

As with `converterMonoidFully`, no nonexpansion is claimed here: absorption
needs CR18 Definition 3.8's request bound uniformly over converter histories,
which is what `converterMonoidAt` asks for.  The two are related by
`converterMonoidAt_le_converterMonoidAtWeakBudget`, and that inclusion is the
honest statement of the delta. -/
def converterMonoidAtWeakBudget : Submonoid (Function.End Phi.{u}) :=
  Submonoid.closure
    ({π | ∃ (i : Set Uni.{u})
        (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})),
        System.InnerTotal E ∧ (∃ β, System.AnswersWithinBudget E β) ∧
          π = attachAt i E} ∪
      {π | ∃ (P : List Uni.{u} → Prop) (hP : PrefixClosed P),
        π = filterPhi P hP} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c RL TL} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c TL RL})

theorem attachAt_mem_converterMonoidAtWeakBudget (i : Set Uni.{u})
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : ∃ β, System.AnswersWithinBudget E β) :
    attachAt i E ∈ converterMonoidAtWeakBudget.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inl ⟨i, E, hIT, hβ, rfl⟩)))

theorem filterPhi_mem_converterMonoidAtWeakBudget (P : List Uni.{u} → Prop)
    (hP : PrefixClosed P) : filterPhi P hP ∈ converterMonoidAtWeakBudget.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨P, hP, rfl⟩)))

theorem block_mem_converterMonoidAtWeakBudget (Q : Set Uni.{u}) :
    block Q ∈ converterMonoidAtWeakBudget.{u} :=
  block_eq_filterPhi Q ▸ filterPhi_mem_converterMonoidAtWeakBudget _ _

theorem parRight_mem_converterMonoidAtWeakBudget (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c RL TL) ∈ converterMonoidAtWeakBudget.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨c, TL, h0, h1, rfl⟩))

theorem parLeft_mem_converterMonoidAtWeakBudget (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c TL RL) ∈ converterMonoidAtWeakBudget.{u} :=
  Submonoid.subset_closure (Or.inr ⟨c, TL, h0, h1, rfl⟩)

/-- The unit is there, as in every `Submonoid.closure` — recorded because
`converterMonoidFully` records it too. -/
example : (1 : Function.End Phi.{u}) ∈ converterMonoidAtWeakBudget.{u} :=
  one_mem _

/-- **The metric-facing Σ, interface-indexed** — the re-based counterpart of
`converterMonoidFullyBudgeted`: the parallel frames unchanged, the block
family widened to CR18 §3.4.3's domain filters (unnumbered prose, printed
p. 62) at a prefix-closed predicate (Marc's re-ruling, 2026-08-19 — `block Q`
and `filterQueries q` are both instances of it, and Definition 3.10 is only the
`[q]` notation), and the attachment family carrying MauRen16 §3.3's interface
index *and* CR18 Definition 3.8's *uniform* request bound.  This is the Σ over which the fully
defined metric layer's Definition 2 and Lemma 1∘2 receipts hold
(`MetricFullyDefined.lean`).

The name is a coinage, flagged: "the converter monoid of interface-indexed
attachments".  The object it re-bases is not — it is MauRen16 §3.3's Σ, and
`converterMonoidFullyBudgeted` is its `i = Set.univ` sub-closure
(`converterMonoidFullyBudgeted_le_converterMonoidAt`). -/
def converterMonoidAt : Submonoid (Function.End Phi.{u}) :=
  Submonoid.closure
    ({π | ∃ (i : Set Uni.{u})
        (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})),
        System.InnerTotal E ∧ System.AnswersWithinUniformBudget E ∧
          π = attachAt i E} ∪
      {π | ∃ (P : List Uni.{u} → Prop) (hP : PrefixClosed P),
        π = filterPhi P hP} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c RL TL} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c TL RL})

theorem attachAt_mem_converterMonoidAt (i : Set Uni.{u})
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinUniformBudget E) :
    attachAt i E ∈ converterMonoidAt.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inl ⟨i, E, hIT, hβ, rfl⟩)))

/-- **CR18 §3.4.3's filter is a generator of the metric-facing Σ** (unnumbered
prose, printed p. 62).  The family is every domain filter at a prefix-closed
predicate, which is what `block Q` and `filterQueries q` both are. -/
theorem filterPhi_mem_converterMonoidAt (P : List Uni.{u} → Prop)
    (hP : PrefixClosed P) : filterPhi P hP ∈ converterMonoidAt.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨P, hP, rfl⟩)))

/-- MauRen16 §3.4's `⊣` at the widened family: blocking is the filter at the
query-avoiding predicate (`block_eq_filterPhi`).  The statement is unchanged —
only its proof moved from a generator of its own to an instance of one. -/
theorem block_mem_converterMonoidAt (Q : Set Uni.{u}) :
    block Q ∈ converterMonoidAt.{u} :=
  block_eq_filterPhi Q ▸ filterPhi_mem_converterMonoidAt _ _

theorem parRight_mem_converterMonoidAt (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c RL TL) ∈ converterMonoidAt.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨c, TL, h0, h1, rfl⟩))

theorem parLeft_mem_converterMonoidAt (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c TL RL) ∈ converterMonoidAt.{u} :=
  Submonoid.subset_closure (Or.inr ⟨c, TL, h0, h1, rfl⟩)

/-- The unit is there, as in every `Submonoid.closure`. -/
example : (1 : Function.End Phi.{u}) ∈ converterMonoidAt.{u} :=
  one_mem _

/-- The budgeted monoid sits inside the A6-budgeted one: a uniform bound is a
bound.  The re-based counterpart of
`converterMonoidFullyBudgeted_le_converterMonoidFully`; the converse is not
claimed, and `converterMonoidAtWeakBudget` carries no nonexpansion receipt. -/
theorem converterMonoidAt_le_converterMonoidAtWeakBudget :
    converterMonoidAt.{u} ≤ converterMonoidAtWeakBudget.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨i, E, hIT, ⟨β, _, hβ, _⟩, rfl⟩) | ⟨P, hP, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact attachAt_mem_converterMonoidAtWeakBudget i hIT ⟨β, hβ⟩
  · exact filterPhi_mem_converterMonoidAtWeakBudget P hP
  · exact parRight_mem_converterMonoidAtWeakBudget c h0 h1
  · exact parLeft_mem_converterMonoidAtWeakBudget c h0 h1

/-- **The interface-indexed converter monoid is nonexpanding** — the closure
step, re-based.  Every generator absorbs into the environment: interface-indexed
attachments by `System.exists_absorb_attachEngineFully` (through
`attachAt_mem_nonexpandingConverters`), domain filters by
`System.exists_absorb_filterDom` (through
`filterPhi_mem_nonexpandingConverters`), parallel frames by
`exists_absorb_par` — and `nonexpandingConverters` is a
submonoid, so the whole closure does.

This is the re-based counterpart of
`converterMonoidFullyBudgeted_le_nonexpandingConverters`, and it is what makes
the S4 receipts hold at the interface-indexed Σ.  It is *not* available for
`converterMonoid` (the B4 witness lives inside it) and not claimed for
`converterMonoidAtWeakBudget`. -/
theorem converterMonoidAt_le_nonexpandingConverters :
    converterMonoidAt.{u} ≤ nonexpandingConverters.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨i, E, hIT, ⟨β, K, hβ, hK⟩, rfl⟩) | ⟨P, hP, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact attachAt_mem_nonexpandingConverters hIT hβ hK
  · exact filterPhi_mem_nonexpandingConverters P hP
  · exact parRight_mem_nonexpandingConverters h0 h1
  · exact parLeft_mem_nonexpandingConverters h0 h1

/-! ### Supersession, not deletion

The whole-face monoids are contained in the interface-indexed ones, generator
by generator: the parallel frames are literally the same sets, the old block
generator is the filter at the query-avoiding predicate, and a whole-face
attachment is `attachAt Set.univ` by the demotion bridge.  So
every statement already proved over `converterMonoidFully(Budgeted)` is a
statement about a sub-family of the re-based Σ, and nothing has to be
re-derived to keep it. -/

/-- **The supersession bridge, budgeted side**: the whole-face metric-facing Σ
is a sub-closure of the interface-indexed one, through `attachAt_univ`. -/
theorem converterMonoidFullyBudgeted_le_converterMonoidAt :
    converterMonoidFullyBudgeted.{u} ≤ converterMonoidAt.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨E, hIT, hβ, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact (attachAt_univ E) ▸ attachAt_mem_converterMonoidAt Set.univ hIT hβ
  · exact block_mem_converterMonoidAt Q
  · exact parRight_mem_converterMonoidAt c h0 h1
  · exact parLeft_mem_converterMonoidAt c h0 h1

/-- **The supersession bridge, A6 side**: the same containment at the weaker
budget. -/
theorem converterMonoidFully_le_converterMonoidAtWeakBudget :
    converterMonoidFully.{u} ≤ converterMonoidAtWeakBudget.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨E, hIT, hβ, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact (attachAt_univ E) ▸
      attachAt_mem_converterMonoidAtWeakBudget Set.univ hIT hβ
  · exact block_mem_converterMonoidAtWeakBudget Q
  · exact parRight_mem_converterMonoidAtWeakBudget c h0 h1
  · exact parLeft_mem_converterMonoidAtWeakBudget c h0 h1

/-! ## Commutation, and MauRen16 §7's grouping

`System.attachEngineFully_comm` pushed to Φ, and then handed to the abstract
grouping layer.  This is the receipt gap **G1** asked for: the metric-facing Σ
is `converterMonoidAt`, its attachment generators are `attachAt i E`, and what
was missing was any `ActCommute` / `PairwiseOrderInvariant` /
`OrderInvariant` statement about them.

The abstract layer's `PairwiseOrderInvariant Φ (e : ι → SigmaI → Sigma)` asks
that `e i α` and `e j β` commute whenever `i ≠ j`, with the converter argument
drawn from *one* type for every interface.  Two things have to be arranged for
that to be the statement this carrier can discharge.

* An interface here is a `Set Uni`, and distinct sets need not be disjoint, so
  the index type is not `Set Uni` itself: it is an abstract `ι` together with a
  pairwise disjoint interface assignment `w : ι → Set Uni`.  That is MauRen16
  §7's own indexing — one sub-interface per party — and it is what makes
  `i ≠ j` the right hypothesis.
* The confinement clause `System.RequestsWithin (w k) (φ k)` mentions the
  interface, so it cannot sit in a converter type that is uniform in `k`.  It
  sits in a *tuple*: the converter argument is a whole protocol, one engine per
  index, each confined to its own interface — MauRen16 §7's "protocol = tuple
  of converters, one per potentially honest party" — and `e k` attaches its
  `k`-th component.  The generators of `attachedWithin e Z` are then exactly
  the admissible interface-local attachments at the interfaces of `Z`, which is
  the grouping §7 means. -/

/-- **A protocol confined to an interface assignment** (coinage, flagged):
MauRen16 §7's tuple of converters, one per party, made precise on this carrier
— one engine per index `k`, confined to that index's interface `w k`
(`System.RequestsWithin`, the clause the commutation consumes) and in the
converter class the metric-facing Σ admits (`System.InnerTotal` and CR18
Definition 3.8's uniform request bound, the clauses nonexpansion consumes).

An `abbrev` rather than a `def` so the subtype's projections stay available at
the use sites; it introduces no new mathematics, only the packaging the
abstract grouping layer's `e : ι → SigmaI → Sigma` requires. -/
abbrev ProtocolWithin {ι : Type*} (w : ι → Set Uni.{u}) : Type _ :=
  {φ : ι → System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) //
    ∀ k, System.RequestsWithin (w k) (φ k) ∧ System.InnerTotal (φ k) ∧
      System.AnswersWithinUniformBudget (φ k)}

/-- **MauRen16 §3.3's `(αR)β = α(Rβ)` at the Φ level**: interface-local
attachments at disjoint interfaces commute as endomorphisms of Φ.
`System.attachEngineFully_comm` under the pushforward, which is a
`fTransform_fTransform` on each side and then one `congrArg`.

The hypotheses are the carrier theorem's, unchanged: disjointness and the two
confinement clauses.  No engine class is consumed — that is what
`attachAt_mem_nonexpandingConverters` needs, not this. -/
theorem attachAt_comm {i j : Set Uni.{u}} (hij : Disjoint i j)
    {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hE : System.RequestsWithin i E) (hF : System.RequestsWithin j F) :
    attachAt i E * attachAt j F = attachAt j F * attachAt i E := by
  funext L
  show Distribution.fTransform (System.attachEngineFully i E)
      (Distribution.fTransform (System.attachEngineFully j F) L) =
    Distribution.fTransform (System.attachEngineFully j F)
      (Distribution.fTransform (System.attachEngineFully i E) L)
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  exact congrFun (congrArg _
    (funext fun R => System.attachEngineFully_comm hij hE hF R)) L

/-- The `ActCommute` receipt over the metric-facing Σ's attachment generators —
the form the abstract grouping layer consumes, and the one gap G1 named as
missing. -/
theorem attachAt_actCommute {i j : Set Uni.{u}} (hij : Disjoint i j)
    {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hE : System.RequestsWithin i E) (hF : System.RequestsWithin j F) :
    AbstractCryptography.ActCommute Phi.{u} (attachAt i E) (attachAt j F) := by
  intro L
  show (attachAt i E * attachAt j F) L = (attachAt j F * attachAt i E) L
  rw [attachAt_comm hij hE hF]

/-- **The abstract grouping axiom, discharged**: the interface-local attachment
family over a pairwise disjoint interface assignment satisfies
`PairwiseOrderInvariant`.  Distinct indices carry disjoint interfaces, and a
protocol's components are confined to their own, so `attachAt_actCommute`
applies with nothing left to check. -/
theorem pairwiseOrderInvariant_attachAt {ι : Type*} {w : ι → Set Uni.{u}}
    (hw : ∀ k l : ι, k ≠ l → Disjoint (w k) (w l)) :
    AbstractCryptography.PairwiseOrderInvariant Phi.{u}
      (fun (k : ι) (φ : ProtocolWithin w) => attachAt (w k) (φ.val k)) :=
  fun k l hkl φ ψ => attachAt_actCommute (hw k l hkl) (φ.2 k).1 (ψ.2 l).1

/-- **MauRen16 §7's grouping receipt on the metric-facing carrier**: converters
attached within disjoint interface sets are order invariant as groups — the
honest and dishonest sides of any corruption split.  The closure induction is
the abstract layer's `orderInvariant_attachedWithin`, consumed with no new
induction code; **G1 closes here**. -/
theorem orderInvariant_attachAt {ι : Type*} {w : ι → Set Uni.{u}}
    (hw : ∀ k l : ι, k ≠ l → Disjoint (w k) (w l)) {Z₁ Z₂ : Set ι}
    (h : Disjoint Z₁ Z₂) :
    AbstractCryptography.OrderInvariant Phi.{u}
      (AbstractCryptography.attachedWithin
        (fun (k : ι) (φ : ProtocolWithin w) => attachAt (w k) (φ.val k)) Z₁).subtype
      (AbstractCryptography.attachedWithin
        (fun (k : ι) (φ : ProtocolWithin w) => attachAt (w k) (φ.val k)) Z₂).subtype :=
  AbstractCryptography.orderInvariant_attachedWithin _
    (pairwiseOrderInvariant_attachAt hw) h

/-- The grouping happens **inside the metric-facing Σ**: every converter
attached within an interface set is an element of `converterMonoidAt`, because
a protocol's components carry `System.InnerTotal` and CR18 Definition 3.8's
uniform request bound.  Without this the order-invariance receipt would live
beside the Σ the metric consumes rather than in it, which is precisely the
defect gap G1 recorded. -/
theorem attachedWithin_attachAt_le_converterMonoidAt {ι : Type*}
    {w : ι → Set Uni.{u}} (Z : Set ι) :
    AbstractCryptography.attachedWithin
        (fun (k : ι) (φ : ProtocolWithin w) => attachAt (w k) (φ.val k)) Z ≤
      converterMonoidAt.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π hπ
  simp only [Set.mem_iUnion] at hπ
  obtain ⟨k, -, φ, rfl⟩ := hπ
  exact attachAt_mem_converterMonoidAt (w k) (φ.2 k).2.1 (φ.2 k).2.2

end

end RandomSystems

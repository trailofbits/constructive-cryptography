/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Absorb

/-!
# The migrated converter application — the converter observes the completion

Ruling R2 says a refusal is observable and non-fatal.  `Connect.connect` makes
it fatal *to the round*: `Connect.serve` is `Part.none` as soon as the resource
declines a request, so a composite can refuse an outer query **after** inner
traffic, CR18 deletion rewinds the composite but not the resource, and the B4
witness turns that mismatch into a rewind oracle.  This module is the migrated
attachment: the converter is attached to `R⊥`, so the resource answers every
request — with `none` where it used to decline — and the converter reacts to
the refusal instead of dying on it.

Nothing here modifies the old layer.  `connect`/`serve`/`lift` stay exactly as
they are, classified PARTIAL-ONLY in `LEDGER.md`; the migrated generators live
beside them under the `Fully` names and are what the Φ-level metric work
consumes.

## A6-M0 — the Cascade audit (2026-08-17).  VERDICT: REUSE

The audit was to decide whether `RandomSystems/Converter/Cascade.lean` already
implements "the converter observes the Option-answers of the completion, and
rounds never refuse after inner traffic".  It does implement the first half —
and, better, so does the object one level down, which is what this module
builds on.

*Decisive fact 1 (the object exists, and it is not in `Cascade`).*
`Converter.DDC U V X Y` **is** the engine signature of this task,

```
DDC U V X Y = DDS ((InLabel × U) ⊕ (InLabel × Option Y))
                  ((InLabel × V) ⊕ (InLabel × X))
```

— CR18 Def 3.8, i.e. `DDS (U ⊕ Option Y) (V ⊕ X)` with the face labels written
out — and `DDC.connStep` answers every request with
`System.output (S⊥) (xs ++ [x])`, the *total* completion answer, feeding it
back to the converter as `Sum.inr (inside, o)`.  So the resource can never kill
a round: `DDC.resolve = (connStep α S).fix` is undefined only where `α` itself
is undefined, or where the inner loop never stops.  `Cascade.drive` is the same
discipline at the `ProtocolFn` presentation (`List U × List (Option Y) →. X ⊕ V`),
and `Cascade.apply_toDDC` proves the two presentations agree.  `Cascade`'s own
`apply` is therefore *not* the reusable object — it consumes a pair-indexed
partial function, from which an engine history `List (U ⊕ Option Y)` cannot be
recovered (the round interleaving is not a function of the pair) — while
`DDC.apply`, which it is defined against, is.

*Decisive fact 2 (what is missing, and it is not plumbing).*  CR18's own
Def 3.8 class goes the wrong way.  Its input-alphabet clause, in tree as
`Converter.AnswersInY`, reads "after an output `(in, x)` the input alphabet is
`Y`" — the converter is *silent once it has seen a `⊥`*.  `IsDDC` bakes that
in.  A converter in CR18's own class therefore refuses after inner traffic
exactly when the resource declines, which is the B4 pathology, and no
absorption receipt can hold for the class as CR18 states it.  The migration is
consequently a genuine strengthening of the converter class, not a re-plumbing
of the driver: `InnerTotal` below is the repository's replacement for
`AnswersInY`, and it is flagged as such.  Nothing in the tree states it, nothing
states refusal-first, and no Φ-level endomorphism is built on `DDC.apply` —
`attach`, `connectPhi` and `converterMonoid` are all built on the refuted
`Connect.connect`.

So A6 reuses `DDC.apply` verbatim as the interpreter and supplies what is
missing: the engine at the mission's unlabelled signature (`DDC.ofEngine`,
which also removes CR18's junk labels by construction), inner-facing totality,
the refusal-first receipt, the identity receipt, and the Φ-level re-basing.
-/

namespace RandomSystems

namespace Converter

namespace DDC

noncomputable section

open Classical
open scoped System

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ## The engine, and its labelling

CR18 Def 3.8 writes the converter's faces as labels on the alphabets; the
engine presentation writes them as the sum injections.  `ofEngine` is the
translation, and it is the reason no junk-output hypothesis is needed below:
a relabelled engine's move is a `moveOf` image by construction. -/

/-- Strip the face labels off a converter input: an outer query, or an inner
answer of the completion. -/
def unlabel : CIn U Y → U ⊕ Option Y :=
  Sum.elim (fun p => Sum.inl p.2) (fun p => Sum.inr p.2)

@[simp] theorem unlabel_query (lbl : InLabel) (u : U) :
    unlabel (Sum.inl (lbl, u) : CIn U Y) = Sum.inl u := rfl

@[simp] theorem unlabel_answer (lbl : InLabel) (o : Option Y) :
    unlabel (Sum.inr (lbl, o) : CIn U Y) = Sum.inr o := rfl

/-- **An engine as a CR18 Def 3.8 converter** (coinage, flagged): the engine
reads the labelled history with its labels dropped, and its move is labelled
canonically.  Junk output labels — `(in, v)` and `(out, x)`, which CR18's
output alphabet excludes and which `connStep` would refuse — are impossible
for an `ofEngine` converter. -/
def ofEngine (E : System.DDS (U ⊕ Option Y) (V ⊕ X)) : DDC U V X Y :=
  System.relabel unlabel (fun m : V ⊕ X => moveOf m.swap) E

@[simp] theorem mem_dom_ofEngine (E : System.DDS (U ⊕ Option Y) (V ⊕ X))
    (c : List (CIn U Y)) :
    c ∈ System.dom (ofEngine E) ↔ c.map unlabel ∈ System.dom E :=
  Iff.rfl

theorem output_ofEngine (E : System.DDS (U ⊕ Option Y) (V ⊕ X))
    (c : List (CIn U Y)) (h : c ∈ System.dom (ofEngine E))
    (hE : c.map unlabel ∈ System.dom E) :
    System.output (ofEngine E) c h =
      moveOf (System.output E (c.map unlabel) hE).swap :=
  rfl

theorem mem_ofEngine_of_mem {E : System.DDS (U ⊕ Option Y) (V ⊕ X)}
    {c : List (CIn U Y)} {m : V ⊕ X} (h : m ∈ E.1 (c.map unlabel)) :
    moveOf m.swap ∈ (ofEngine E).1 c :=
  Part.mem_map _ h

theorem mem_ofEngine_out {E : System.DDS (U ⊕ Option Y) (V ⊕ X)}
    {c : List (CIn U Y)} {v : V} (h : Sum.inl v ∈ E.1 (c.map unlabel)) :
    Sum.inl (InLabel.outside, v) ∈ (ofEngine E).1 c :=
  mem_ofEngine_of_mem h

theorem mem_ofEngine_in {E : System.DDS (U ⊕ Option Y) (V ⊕ X)}
    {c : List (CIn U Y)} {x : X} (h : Sum.inr x ∈ E.1 (c.map unlabel)) :
    Sum.inr (InLabel.inside, x) ∈ (ofEngine E).1 c :=
  mem_ofEngine_of_mem h

/-- The move of an engine converter at a history its engine accepts: an outer
answer, or a request.  The dichotomy every round argument splits on. -/
theorem exists_move_ofEngine {E : System.DDS (U ⊕ Option Y) (V ⊕ X)}
    {c : List (CIn U Y)} (hE : c.map unlabel ∈ System.dom E) :
    (∃ v : V, Sum.inl (InLabel.outside, v) ∈ (ofEngine E).1 c) ∨
      ∃ x : X, Sum.inr (InLabel.inside, x) ∈ (ofEngine E).1 c := by
  have hm : System.output E (c.map unlabel) hE ∈ E.1 (c.map unlabel) :=
    Part.get_mem hE
  rcases hout : System.output E (c.map unlabel) hE with v | x
  · exact Or.inl ⟨v, mem_ofEngine_out (hout ▸ hm)⟩
  · exact Or.inr ⟨x, mem_ofEngine_in (hout ▸ hm)⟩

/-! ## One round of the outer fold -/

/-- A one-query fold is one inner resolution. -/
theorem mem_driveFrom_singleton (α : DDC U V X Y) (R : System.DDS X Y)
    (st : List (CIn U Y) × List X) (u : U)
    {r : List V × (List (CIn U Y) × List X)} :
    r ∈ driveFrom α R st [u] ↔
      ∃ q ∈ resolve α R (st.1 ++ [Sum.inl (InLabel.outside, u)], st.2),
        r = ([q.1], q.2) := by
  simp only [driveFrom, Part.mem_bind_iff, Part.mem_map_iff, Part.mem_some_iff]
  constructor
  · rintro ⟨q, hq, rr, rfl, rfl⟩
    exact ⟨q, hq, rfl⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, ([], q.2), rfl, rfl⟩

end

end DDC

end Converter

namespace System

noncomputable section

open Classical
open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve driveFrom)

universe u v w z

variable {U : Type u} {V : Type w} {X : Type z} {Y : Type v}

/-! ## The migrated attachment -/

/-- **`connectFully`** — the migrated trace: interpret the engine's requests
against the *completion* `R⊥`.  Every request is answered (`none` where the
resource declines), so a round can only fail on the converter's own move;
`Connect.connect`, which dies on a declined request, is untouched and stays
PARTIAL-ONLY. -/
def connectFully (E : DDS (U ⊕ Option Y) (V ⊕ X)) (R : DDS X Y) : DDS U V :=
  Converter.DDC.apply (ofEngine E) R

/-- The interpreter state reached on an outer history: the converter history
and the resource history after those rounds. -/
def ReachedState (E : DDS (U ⊕ Option Y) (V ⊕ X)) (R : DDS X Y) (us : List U)
    (st : List (CIn U Y) × List X) : Prop :=
  ∃ vs, (vs, st) ∈ driveFrom (ofEngine E) R ([], []) us

theorem reachedState_nil (E : DDS (U ⊕ Option Y) (V ⊕ X)) (R : DDS X Y) :
    ReachedState E R [] ([], []) :=
  ⟨[], Part.mem_some _⟩

/-- Reached states are unique: the interpreter is a partial function. -/
theorem ReachedState.unique {E : DDS (U ⊕ Option Y) (V ⊕ X)} {R : DDS X Y}
    {us : List U} {st st' : List (CIn U Y) × List X}
    (h : ReachedState E R us st) (h' : ReachedState E R us st') : st = st' := by
  obtain ⟨vs, hvs⟩ := h
  obtain ⟨vs', hvs'⟩ := h'
  exact congrArg Prod.snd (Part.mem_unique hvs hvs')

/-- The frontier round, forward: a resolved round from the reached state is a
resolved run of the extended outer history. -/
theorem mem_driveFrom_concat {E : DDS (U ⊕ Option Y) (V ⊕ X)} {R : DDS X Y}
    {us : List U} {c : List (CIn U Y)} {xs : List X}
    (hst : ReachedState E R us (c, xs)) {u : U} {v : V}
    {st' : List (CIn U Y) × List X}
    (hres : (v, st') ∈ resolve (ofEngine E) R
      (c ++ [Sum.inl (InLabel.outside, u)], xs)) :
    ∃ vs, (vs ++ [v], st') ∈ driveFrom (ofEngine E) R ([], []) (us ++ [u]) := by
  obtain ⟨vs, hvs⟩ := hst
  refine ⟨vs, ?_⟩
  rw [Converter.DDC.driveFrom_append, Part.mem_bind_iff]
  refine ⟨(vs, (c, xs)), hvs, ?_⟩
  rw [Part.mem_map_iff]
  exact ⟨([v], st'),
    (Converter.DDC.mem_driveFrom_singleton _ _ _ _).mpr ⟨(v, st'), hres, rfl⟩,
    rfl⟩

/-- **The frontier receipt**: the migrated composite accepts an extended outer
history exactly when the round from the reached state resolves. -/
theorem mem_dom_connectFully_concat {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {us : List U} {c : List (CIn U Y)} {xs : List X}
    (hst : ReachedState E R us (c, xs)) (u : U) :
    us ++ [u] ∈ dom (connectFully E R) ↔
      (resolve (ofEngine E) R (c ++ [Sum.inl (InLabel.outside, u)], xs)).Dom := by
  constructor
  · intro h
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
    obtain ⟨r, hr, -⟩ := (Converter.DDC.mem_apply_iff _ _ _ _).mp hv
    rw [Converter.DDC.driveFrom_append, Part.mem_bind_iff] at hr
    obtain ⟨ra, hra, hrb⟩ := hr
    obtain ⟨vs, hvs⟩ := hst
    have hra2 : ra.2 = (c, xs) := congrArg Prod.snd (Part.mem_unique hra hvs)
    rw [Part.mem_map_iff] at hrb
    obtain ⟨rb, hrb, -⟩ := hrb
    rw [hra2, Converter.DDC.mem_driveFrom_singleton] at hrb
    obtain ⟨q, hq, -⟩ := hrb
    exact Part.dom_iff_mem.mpr ⟨q, hq⟩
  · intro h
    obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp h
    obtain ⟨vs, hvs⟩ := mem_driveFrom_concat hst (v := q.1) (st' := q.2) hq
    refine Part.dom_iff_mem.mpr ⟨q.1, ?_⟩
    refine (Converter.DDC.mem_apply_iff _ _ _ _).mpr ⟨(vs ++ [q.1], q.2), hvs, ?_⟩
    simp

/-- **The frontier output**: the composite's answer to the extended outer
history is the round's outer answer. -/
theorem output_connectFully_concat {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {us : List U} {c : List (CIn U Y)} {xs : List X}
    (hst : ReachedState E R us (c, xs)) {u : U} {v : V}
    {st' : List (CIn U Y) × List X}
    (hres : (v, st') ∈ resolve (ofEngine E) R
      (c ++ [Sum.inl (InLabel.outside, u)], xs))
    (h : us ++ [u] ∈ dom (connectFully E R)) :
    output (connectFully E R) (us ++ [u]) h = v := by
  obtain ⟨vs, hvs⟩ := mem_driveFrom_concat hst hres
  have hmem : v ∈ (connectFully E R).1 (us ++ [u]) := by
    refine (Converter.DDC.mem_apply_iff _ _ _ _).mpr ⟨(vs ++ [v], st'), hvs, ?_⟩
    simp
  exact Part.get_eq_of_mem hmem h

/-- **The frontier state**: a resolved round advances the reached state. -/
theorem reachedState_concat {E : DDS (U ⊕ Option Y) (V ⊕ X)} {R : DDS X Y}
    {us : List U} {c : List (CIn U Y)} {xs : List X}
    (hst : ReachedState E R us (c, xs)) {u : U} {v : V}
    {st' : List (CIn U Y) × List X}
    (hres : (v, st') ∈ resolve (ofEngine E) R
      (c ++ [Sum.inl (InLabel.outside, u)], xs)) :
    ReachedState E R (us ++ [u]) st' := by
  obtain ⟨vs, hvs⟩ := mem_driveFrom_concat hst hres
  exact ⟨vs ++ [v], hvs⟩

/-! ## The round equations, in the engine's own vocabulary

CR18 Def 3.9's two connection rules, read off `resolve_out`/`resolve_in`
through the labelling, with the inner answer named by `System.answer` — the
form the absorption work consumes. -/

/-- The output rule: an engine answer closes the round, histories unchanged. -/
theorem mem_resolve_of_answer {E : DDS (U ⊕ Option Y) (V ⊕ X)} {R : DDS X Y}
    {c : List (CIn U Y)} {xs : List X} {v : V}
    (h : Sum.inl v ∈ E.1 (c.map unlabel)) :
    (v, (c, xs)) ∈ resolve (ofEngine E) R (c, xs) :=
  Converter.DDC.resolve_out _ _ (Converter.DDC.mem_ofEngine_out h)

/-- The query rule: an engine request continues the round from the completion's
answer — which exists for every request, and is `none` exactly where the
resource declines. -/
theorem resolve_of_request {E : DDS (U ⊕ Option Y) (V ⊕ X)} {R : DDS X Y}
    {c : List (CIn U Y)} {xs : List X} {x : X}
    (h : Sum.inr x ∈ E.1 (c.map unlabel)) :
    resolve (ofEngine E) R (c, xs) =
      resolve (ofEngine E) R
        (c ++ [Sum.inr (InLabel.inside, answer R xs x)], xs ++ [x]) :=
  Converter.DDC.resolve_in _ _ (Converter.DDC.mem_ofEngine_in h)

/-- A resolved round certifies the converter's own first move. -/
theorem mem_dom_of_resolve_dom (E : DDS (U ⊕ Option Y) (V ⊕ X)) (R : DDS X Y)
    (c : List (CIn U Y)) (xs : List X)
    (h : (resolve (ofEngine E) R (c, xs)).Dom) : c.map unlabel ∈ dom E := by
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
  exact (Part.bind_dom.mp (PFun.dom_of_mem_fix hv)).fst

/-! ## Refusal precedes inner traffic

The criterion that killed B4, now a theorem.  Two hypotheses on the engine,
both flagged as repository extensions of CR18 Def 3.8:

* `InnerTotal` — the engine reacts to whatever the completion returns.  This
  is the *replacement* for Def 3.8's input-alphabet clause (in tree as
  `Converter.AnswersInY`), which demands the opposite — silence after a `⊥` —
  and is exactly what makes CR18's own converter class refuse after inner
  traffic.  Ruling R2 forces the replacement.
* `AnswersWithinBudget` — Def 3.8's finite-bound clause on consecutive
  requests, in the well-founded form the round induction consumes: a measure
  on engine histories that strictly drops at every request step.  It is needed:
  without it a round can request forever, and a diverging round is undefined
  after inner traffic. -/

/-- **Inner-facing totality**: once the engine has emitted a request, it is
defined at that history extended by *any* answer of the completion, `none`
included.  CR18 Def 3.8's shape, with its input-alphabet clause replaced by
its negation (ruling R2). -/
def InnerTotal (E : DDS (U ⊕ Option Y) (V ⊕ X)) : Prop :=
  ∀ (l : List (U ⊕ Option Y)) (x : X), Sum.inr x ∈ E.1 l →
    ∀ o : Option Y, l ++ [Sum.inr o] ∈ dom E

/-- **The finite-bound clause, well-founded form** (coinage, flagged; the
engine-side `AnswersWithinDepth`): `β` bounds the requests still to come, and
strictly drops at every request step. -/
def AnswersWithinBudget (E : DDS (U ⊕ Option Y) (V ⊕ X))
    (β : List (U ⊕ Option Y) → ℕ) : Prop :=
  ∀ (l : List (U ⊕ Option Y)) (x : X), Sum.inr x ∈ E.1 l →
    ∀ o : Option Y, β (l ++ [Sum.inr o]) < β l

/-- **CR18 Definition 3.8's request bound, verbatim** (coinage, flagged): a
well-founded budget that is bounded *uniformly over converter histories* — one
bound for the converter, which is how Definition 3.8 states it ("a finite upper
bound on the number of consecutive requests").  This, not `AnswersWithinBudget`
alone, is what absorption needs: see `exists_absorb_connectFully`. -/
def AnswersWithinUniformBudget (E : DDS (U ⊕ Option Y) (V ⊕ X)) : Prop :=
  ∃ (β : List (U ⊕ Option Y) → ℕ) (K : ℕ),
    AnswersWithinBudget E β ∧ ∀ l, β l ≤ K

/-- **A started round always ends**: from any converter history the engine
accepts, the round resolves — whatever the resource answers.  The resource
therefore has no way to make a round fail. -/
theorem resolve_dom_of_mem_dom {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (R : DDS X Y) :
    ∀ (n : ℕ) (c : List (CIn U Y)) (xs : List X), β (c.map unlabel) ≤ n →
      c.map unlabel ∈ dom E → (resolve (ofEngine E) R (c, xs)).Dom := by
  intro n
  induction n with
  | zero =>
      intro c xs hle hE
      have hm : output E (c.map unlabel) hE ∈ E.1 (c.map unlabel) :=
        Part.get_mem hE
      rcases hout : output E (c.map unlabel) hE with v | x
      · exact Part.dom_iff_mem.mpr
          ⟨(v, (c, xs)), mem_resolve_of_answer (hout ▸ hm)⟩
      · exact absurd (lt_of_lt_of_le
          (hβ _ x (hout ▸ hm) (answer R xs x)) hle)
          (Nat.not_lt_zero _)
  | succ n ih =>
      intro c xs hle hE
      have hm : output E (c.map unlabel) hE ∈ E.1 (c.map unlabel) :=
        Part.get_mem hE
      rcases hout : output E (c.map unlabel) hE with v | x
      · exact Part.dom_iff_mem.mpr
          ⟨(v, (c, xs)), mem_resolve_of_answer (hout ▸ hm)⟩
      · have hreq : Sum.inr x ∈ E.1 (c.map unlabel) := hout ▸ hm
        have hmap : (c ++ [Sum.inr (InLabel.inside, answer R xs x)]).map unlabel =
            c.map unlabel ++ [Sum.inr (answer R xs x)] := by simp
        rw [resolve_of_request hreq]
        refine ih _ (xs ++ [x]) ?_ ?_
        · rw [hmap]
          exact Nat.lt_succ_iff.mp
            (lt_of_lt_of_le (hβ _ x hreq (answer R xs x)) hle)
        · rw [hmap]
          exact hIT _ x hreq (answer R xs x)

/-- **Refusal precedes inner traffic** — by construction.  The migrated
composite accepts an outer query exactly when the *engine* accepts it at the
converter history already reached; the resource enters only through the
answers the engine has already seen, never through a refusal.  So no history
is refused after its round issued a request: a round that starts, ends.

This is the shape B4-resume consumes.  The blunter reading — that the domain
is independent of the resource outright — is **false** under these hypotheses
and is not what absorption needs: an engine may perfectly well refuse a *new*
outer query on the strength of an earlier round's answer (nothing constrains
its outer face), and that refusal costs the environment nothing, because it
precedes all traffic of its own round and the re-simulating environment knows
the engine history exactly.  The resource-independent form does hold literally
before any answer has been seen (`mem_dom_connectFully_of_nil`). -/
theorem connectFully_refusal_first {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) {us : List U} {c : List (CIn U Y)}
    {xs : List X} (hst : ReachedState E R us (c, xs)) (u : U) :
    us ++ [u] ∈ dom (connectFully E R) ↔
      c.map unlabel ++ [Sum.inl u] ∈ dom E := by
  have hmap : (c ++ [Sum.inl (InLabel.outside, u)]).map unlabel =
      c.map unlabel ++ [Sum.inl u] := by simp
  rw [mem_dom_connectFully_concat hst u]
  constructor
  · intro h
    rw [← hmap]
    exact mem_dom_of_resolve_dom E R _ xs h
  · intro h
    exact resolve_dom_of_mem_dom hIT hβ R (β (c.map unlabel ++ [Sum.inl u]))
      _ xs (by rw [hmap]) (by rw [hmap]; exact h)

/-- The resource-independent form, where it is true: the first outer query is
accepted by the composite exactly when the engine accepts it, and no resource
has been consulted yet. -/
theorem mem_dom_connectFully_of_nil {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (u : U) :
    [u] ∈ dom (connectFully E R) ↔ [Sum.inl u] ∈ dom E := by
  have h := connectFully_refusal_first hIT hβ (reachedState_nil E R) u
  simpa using h

/-- **The B4 criterion, at the frontier it is stated for**: whether the
migrated composite answers a first query does not depend on the resource. -/
theorem mem_dom_connectFully_of_nil_congr {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (R R' : DDS X Y) (u : U) :
    [u] ∈ dom (connectFully E R) ↔ [u] ∈ dom (connectFully E R') :=
  (mem_dom_connectFully_of_nil hIT hβ u).trans
    (mem_dom_connectFully_of_nil hIT hβ u).symm

/-! ## The identity of the migrated monoid

MauRen16 §3.3's `id ∈ Σ`, migrated.  The relay engine forwards the outer query
as its single request and forwards the completion's answer as its outer answer,
so its outer answer alphabet is `Option Y` and the composite is `R⊥`, not `R`.
That is the honest migrated identity: on the fully defined carrier the object
the identity converter exposes IS the completion.  The consequence for the Φ
layer is recorded at `attachFully`: the relay is not a member of that family,
it is the metric layer's `R ↦ R⊥`. -/

/-- **The migrated relay engine**: swap the faces — an outer query becomes the
request, an answer of the completion becomes the outer answer. -/
def idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X) :=
  functionEvaluator Sum.swap

theorem innerTotal_idEngineFully : InnerTotal (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X)) :=
  fun l x _ o => by
    show l ++ [Sum.inr o] ≠ []
    simp

theorem answersWithinBudget_idEngineFully :
    AnswersWithinBudget (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X))
      (fun l => match l.getLast? with | some (Sum.inl _) => 1 | _ => 0) := by
  intro l x hx o
  have hne : l ≠ [] := hx.1
  have hswap : Sum.inr x = Sum.swap (l.getLast hne) :=
    Part.mem_unique hx ⟨hne, rfl⟩
  have hlast : l.getLast hne = Sum.inl x := by
    rcases hl : l.getLast hne with u | o' <;> rw [hl] at hswap <;> simp at hswap
    rw [hswap]
  have h1 : l.getLast? = some (Sum.inl x) := by
    rw [List.getLast?_eq_some_getLast hne, hlast]
  have h2 : (l ++ [Sum.inr o]).getLast? = some (Sum.inr o) := by simp
  simp [h1, h2]

/-- One relay round: request the outer query, deliver the completion's answer.
The round is computed, not merely resolvable — the relay never stalls. -/
theorem mem_resolve_idEngineFully (R : DDS X Y) (c : List (CIn X Y))
    (xs : List X) (x : X) :
    (answer R xs x,
        ((c ++ [Sum.inl (InLabel.outside, x)]) ++
            [Sum.inr (InLabel.inside, answer R xs x)], xs ++ [x])) ∈
      resolve (ofEngine idEngineFully) R (c ++ [Sum.inl (InLabel.outside, x)], xs) := by
  have hE : (c ++ [Sum.inl (InLabel.outside, x)]).map unlabel ∈
      dom (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X)) := by
    show _ ≠ []
    simp
  have hout : output idEngineFully _ hE = Sum.inr x := by
    have : (c ++ [Sum.inl (InLabel.outside, x)]).map unlabel =
        c.map unlabel ++ [Sum.inl x] := by simp
    simp [idEngineFully, this]
  have hm : output idEngineFully _ hE ∈
      (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X)).1 _ := Part.get_mem hE
  rw [resolve_of_request (hout ▸ hm)]
  have hE' : ((c ++ [Sum.inl (InLabel.outside, x)]) ++
      [Sum.inr (InLabel.inside, answer R xs x)]).map unlabel ∈
      dom (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X)) := by
    show _ ≠ []
    simp
  have hout' : output idEngineFully _ hE' = Sum.inl (answer R xs x) := by
    simp [idEngineFully]
  have hm' : output idEngineFully _ hE' ∈
      (idEngineFully : DDS (X ⊕ Option Y) (Option Y ⊕ X)).1 _ := Part.get_mem hE'
  exact mem_resolve_of_answer (hout' ▸ hm')

/-- The relay's reached state on an outer history: the resource has seen
exactly the outer queries. -/
theorem exists_reachedState_idEngineFully (R : DDS X Y) (us : List X) :
    ∃ c, ReachedState idEngineFully R us (c, us) := by
  induction us using List.reverseRecOn with
  | nil => exact ⟨[], reachedState_nil _ _⟩
  | append_singleton us x ih =>
      obtain ⟨c, hst⟩ := ih
      exact ⟨_, reachedState_concat hst (mem_resolve_idEngineFully R c us x)⟩

/-- **The migrated identity receipt**: attaching the relay to a resource is the
resource's own completion.  Not `= R`: on the fully defined carrier the relay
exposes `R⊥`, which is the identity's honest image (MauRen16 §3.3's `id ∈ Σ`
read through CR18 Def 3.3). -/
theorem connectFully_idEngineFully (R : DDS X Y) :
    connectFully idEngineFully R = R⊥ := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ ?_
  · constructor
    · intro h
      have hne : l ≠ [] := by
        rintro rfl
        exact empty_not_mem (connectFully idEngineFully R) h
      show l ∈ dom R⊥
      rw [dom_fullyDefined]
      exact hne
    · intro h
      have hne : l ≠ [] := by
        have h' : l ∈ dom R⊥ := h
        rw [dom_fullyDefined] at h'
        exact h'
      obtain ⟨m, x, rfl⟩ : ∃ m q, l = m ++ [q] := by
        rcases l.eq_nil_or_concat with rfl | ⟨m, q, rfl⟩
        · exact absurd rfl hne
        · exact ⟨m, q, by simp⟩
      obtain ⟨c, hst⟩ := exists_reachedState_idEngineFully R m
      exact (mem_dom_connectFully_concat hst x).mpr
        (Part.dom_iff_mem.mpr ⟨_, mem_resolve_idEngineFully R c m x⟩)
  · intro h₁ h₂
    have hne : l ≠ [] := by
      rintro rfl
      exact empty_not_mem (connectFully idEngineFully R) h₁
    obtain ⟨m, x, rfl⟩ : ∃ m q, l = m ++ [q] := by
      rcases l.eq_nil_or_concat with rfl | ⟨m, q, rfl⟩
      · exact absurd rfl hne
      · exact ⟨m, q, by simp⟩
    obtain ⟨c, hst⟩ := exists_reachedState_idEngineFully R m
    show output (connectFully idEngineFully R) (m ++ [x]) h₁ =
      output R⊥ (m ++ [x]) h₂
    rw [output_connectFully_concat hst (mem_resolve_idEngineFully R c m x) h₁]
    rfl

/-! ## Serial composition — the receipt that is NOT delivered here

The composite of two migrated attachments is `connectFully E₂ (connectFully E₁ R)`,
and the alphabets nest: with `E₁ : DDS (U ⊕ Option Y) (V ⊕ X)` the inner
composite is a `DDS U V`, so the outer engine must read the *completion of the
inner composite*, `E₂ : DDS (W ⊕ Option V) (Z ⊕ U)`, and a cascade engine would
have to live at `DDS (W ⊕ Option Y) (Z ⊕ X)` with

    connectFully (cascadeFully E₂ E₁) R = connectFully E₂ (connectFully E₁ R).

What blocks it, precisely.  A cascade engine's history `List (W ⊕ Option Y)`
records only the *outer* queries and the *real resource's* answers; both
engines' own histories have to be replayed from it, and the replay must
reproduce `answer (connectFully E₁ R)`, i.e. the *kept prefix* of the inner
composite: when `E₁` refuses an outer query the inner composite deletes it, so
the replay must roll `E₁`'s history back to the start of that round (a no-op
exactly where `connectFully_refusal_first` applies, and unfaithful where it
does not).  That is a genuine two-engine state machine with rollback, and it is
`Cascade.compGo`'s job — which is why the honest route is not to hand-roll it
but to go through the ν layer, where `Cascade.comp` and its receipt
`apply_comp` already exist: the missing link is a bridge
`DDC.apply α S = Cascade.apply (toNu α) S` for a junk-free `α` (the round trip
`toNu_toDDC` is proven in the other direction only).  Recorded as the blocked
statement; B4-resume does not consume it, and `converterMonoidFully` below is a
`Submonoid.closure`, which needs no closed generator set. -/

/-! ## B4-RESUME — the migrated attachment absorbs into the environment

The keystone of the fully defined metric pipeline: everything an environment
learns from `connectFully E s` it can learn from `s` alone, by *running the
engine itself*.  The re-simulating environment holds the converter history, so

* it decides refusals without consulting the resource
  (`connectFully_refusal_first`: the composite accepts an outer query exactly
  when the engine accepts it at the reached converter history), and
* every request it relays is answered by `System.answer s` — the inner
  transcript's own answer (`resolve_of_request`).

The decomposition is the one `exists_absorb_blockSet` / `exists_absorb_par`
use — replay step, replay, need, absorbed environment, invariant — with one
new layer: a round of `connectFully` issues *several* inner queries, not at
most one, so the outer replay step delegates to a round replay (`roundReplay`)
and the invariant's inner-round counter advances by a whole round at a time.

The budget is what makes the round replay a total function and what turns the
outer length `n` into an inner length `m`: CR18 Definition 3.8 asks for "a
finite upper bound on the number of consecutive requests", and that bound —
uniform over converter histories, as CR18 states it — is the hypothesis
`hF : ∀ l, β l < F` below.  It is a genuine hypothesis, not an artefact of the
proof: `AnswersWithinBudget` alone bounds the requests of a round by `β` *at
that round's history*, and nothing stops `β` from growing with what the engine
has been told, so without a uniform bound no single `m` serves every `s`. -/

section Absorb

/-- **The engine's move**, as a total function: `none` exactly where the engine
is undefined.  General infrastructure (coinage, flagged), stated here at the
point of use as `System.answer` is; it removes the dependent domain proof that
would otherwise make the round recursion unrewritable. -/
def move {A : Type*} {B : Type*} (E : DDS A B) (l : List A) : Option B :=
  if h : l ∈ dom E then some (output E l h) else none

theorem move_eq_some_iff {A : Type*} {B : Type*} {E : DDS A B} {l : List A}
    {b : B} : move E l = some b ↔ b ∈ E.1 l := by
  by_cases h : l ∈ dom E
  · rw [move, dif_pos h, Option.some_inj]
    exact ⟨fun hb => hb ▸ Part.get_mem h,
      fun hb => Part.mem_unique (Part.get_mem h) hb⟩
  · rw [move, dif_neg h]
    exact ⟨fun hc => absurd hc (by simp),
      fun hb => absurd (Part.dom_iff_mem.mpr ⟨b, hb⟩) h⟩

/-- **One round of the composite, replayed** from the converter history and a
list of inner answers.  The engine either answers the outer query (the round
closes, `Option V` component), or requests — consuming the next inner answer,
or reporting the request it is waiting for when there is none (`Option X`
component).  The fuel is CR18 Definition 3.8's request bound; a round that
would exceed it returns neither, which is a state the hypotheses exclude. -/
def roundReplay (E : DDS (U ⊕ Option Y) (V ⊕ X)) :
    ℕ → List (CIn U Y) → List (Option Y) →
      (List (CIn U Y) × List (Option Y)) × Option V × Option X
  | 0, c, ys => ((c, ys), none, none)
  | d + 1, c, ys =>
      match move E (c.map unlabel) with
      | none => ((c, ys), none, none)
      | some (Sum.inl v) => ((c, ys), some v, none)
      | some (Sum.inr x) =>
          match ys with
          | [] => ((c, ys), none, some x)
          | y :: ys' => roundReplay E d (c ++ [Sum.inr (InLabel.inside, y)]) ys'

theorem roundReplay_answer {E : DDS (U ⊕ Option Y) (V ⊕ X)} {d : ℕ}
    {c : List (CIn U Y)} (ys : List (Option Y)) {v : V}
    (h : Sum.inl v ∈ E.1 (c.map unlabel)) :
    roundReplay E (d + 1) c ys = ((c, ys), some v, none) := by
  simp [roundReplay, move_eq_some_iff.mpr h]

theorem roundReplay_stuck {E : DDS (U ⊕ Option Y) (V ⊕ X)} {d : ℕ}
    {c : List (CIn U Y)} {x : X} (h : Sum.inr x ∈ E.1 (c.map unlabel)) :
    roundReplay E (d + 1) c [] = ((c, []), none, some x) := by
  simp [roundReplay, move_eq_some_iff.mpr h]

theorem roundReplay_request {E : DDS (U ⊕ Option Y) (V ⊕ X)} {d : ℕ}
    {c : List (CIn U Y)} {x : X} (y : Option Y) (ys : List (Option Y))
    (h : Sum.inr x ∈ E.1 (c.map unlabel)) :
    roundReplay E (d + 1) c (y :: ys) =
      roundReplay E d (c ++ [Sum.inr (InLabel.inside, y)]) ys := by
  simp [roundReplay, move_eq_some_iff.mpr h]

/-- One round of the replay of an outer interaction with `connectFully E ·`:
the outer environment moves on the outer transcript built so far; a query the
engine refuses is answered `⊥` on the spot — *with no inner traffic*, which is
`connectFully_refusal_first` — and a query it accepts runs the round replay,
which either closes the round or stalls for want of an inner answer. -/
def fullyReplayStep (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    (st : List (U × Option V) × List (CIn U Y) × List (Option Y)) :
    List (U × Option V) × List (CIn U Y) × List (Option Y) :=
  match e st.1↓ᵧ with
  | none => st
  | some u =>
      if st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E then
        match roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2 with
        | ((c', ys'), some v, _) => (st.1 ++ [(u, some v)], c', ys')
        | (_, none, _) => st
      else (st.1 ++ [(u, none)], st.2)

/-- The request the replay is waiting for: the round replay's own report. -/
def fullyNeed (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ) (e : DDE.Total V U)
    (st : List (U × Option V) × List (CIn U Y) × List (Option Y)) : Option X :=
  match e st.1↓ᵧ with
  | none => none
  | some u =>
      if st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E then
        (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2).2.2
      else none

theorem fullyReplayStep_stop (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    {st : List (U × Option V) × List (CIn U Y) × List (Option Y)}
    (h : e st.1↓ᵧ = none) : fullyReplayStep E F e st = st := by
  simp [fullyReplayStep, h]

theorem fullyReplayStep_refuse (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    {st : List (U × Option V) × List (CIn U Y) × List (Option Y)} {u : U}
    (h : e st.1↓ᵧ = some u)
    (hno : st.2.1.map unlabel ++ [Sum.inl u] ∉ dom E) :
    fullyReplayStep E F e st = (st.1 ++ [(u, none)], st.2) := by
  simp only [fullyReplayStep, h]
  rw [if_neg hno]

theorem fullyReplayStep_round (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    {st : List (U × Option V) × List (CIn U Y) × List (Option Y)} {u : U}
    {c' : List (CIn U Y)} {ys' : List (Option Y)} {v : V} {o : Option X}
    (h : e st.1↓ᵧ = some u)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E)
    (hr : roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2 =
      ((c', ys'), some v, o)) :
    fullyReplayStep E F e st = (st.1 ++ [(u, some v)], c', ys') := by
  simp only [fullyReplayStep, h]
  rw [if_pos hd, hr]

theorem fullyReplayStep_stall (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    {st : List (U × Option V) × List (CIn U Y) × List (Option Y)} {u : U}
    (h : e st.1↓ᵧ = some u)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E)
    (hr : (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)])
      st.2.2).2.1 = none) :
    fullyReplayStep E F e st = st := by
  simp only [fullyReplayStep, h]
  rw [if_pos hd]
  rcases hrr : roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2
    with ⟨⟨c', ys'⟩, o₁, o₂⟩
  rw [hrr] at hr
  cases hr
  rfl

/-- The request the replay reports is the round replay's, at the state the
outer environment's move puts it in. -/
theorem fullyNeed_round (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U)
    {st : List (U × Option V) × List (CIn U Y) × List (Option Y)} {u : U}
    (h : e st.1↓ᵧ = some u)
    (hd : st.2.1.map unlabel ++ [Sum.inl u] ∈ dom E) :
    fullyNeed E F e st =
      (roundReplay E F (st.2.1 ++ [Sum.inl (InLabel.outside, u)]) st.2.2).2.2 := by
  simp only [fullyNeed, h]
  rw [if_pos hd]

/-- The replay of the first `k` outer rounds against a given list of inner
answers. -/
def fullyReplay (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ) (e : DDE.Total V U)
    (ys : List (Option Y)) :
    ℕ → List (U × Option V) × List (CIn U Y) × List (Option Y)
  | 0 => ([], [], ys)
  | k + 1 => fullyReplayStep E F e (fullyReplay E F e ys k)

@[simp]
theorem fullyReplay_zero (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U) (ys : List (Option Y)) :
    fullyReplay E F e ys 0 = ([], [], ys) :=
  rfl

theorem fullyReplay_succ (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U) (ys : List (Option Y)) (k : ℕ) :
    fullyReplay E F e ys (k + 1) =
      fullyReplayStep E F e (fullyReplay E F e ys k) :=
  rfl

/-- A stalled replay stays stalled. -/
theorem fullyReplay_of_fixed (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ)
    (e : DDE.Total V U) (ys : List (Option Y)) {k : ℕ}
    (hfix : fullyReplayStep E F e (fullyReplay E F e ys k) =
      fullyReplay E F e ys k) :
    ∀ i, k ≤ i → fullyReplay E F e ys i = fullyReplay E F e ys k := by
  intro i hi
  induction i, hi using Nat.le_induction with
  | base => rfl
  | succ i _ ih => rw [fullyReplay_succ, ih, hfix]

/-- **The absorbed environment**: the inner environment that replays the outer
interaction with `connectFully E ·` for `n` rounds and asks exactly the request
the replay is waiting for.  It depends on the outer environment, the length,
the engine and the budget — never on the resource, which is what makes the
reduction a reduction. -/
def absorbFully (E : DDS (U ⊕ Option Y) (V ⊕ X)) (F : ℕ) (e : DDE.Total V U)
    (n : ℕ) : DDE.Total Y X :=
  fun ys => fullyNeed E F e (fullyReplay E F e ys n)

/-! ### The composite's answer at the frontier

`answer (connectFully E R)` decided at the reached converter history: a refusal
is the engine's own (and costs no inner traffic), an answer is the round's. -/

/-- A query the engine refuses is refused by the composite — **before** any
inner traffic of its round.  This is `connectFully_refusal_first` read at the
completion's answer, which is the form the replay consumes. -/
theorem answer_connectFully_refuse {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) {us : List U} {c : List (CIn U Y)}
    {xs : List X} (hst : ReachedState E R us (c, xs)) {L : List U}
    (hus : keptPrefix (connectFully E R) L = us) {u : U}
    (hno : c.map unlabel ++ [Sum.inl u] ∉ dom E) :
    answer (connectFully E R) L u = none := by
  rw [answer_eq]
  refine dif_neg fun hc => hno ?_
  rw [hus] at hc
  exact (connectFully_refusal_first hIT hβ hst u).mp hc

/-- A query the engine accepts is answered by the round it starts. -/
theorem answer_connectFully_round {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {R : DDS X Y} {us : List U} {c : List (CIn U Y)} {xs : List X}
    (hst : ReachedState E R us (c, xs)) {L : List U}
    (hus : keptPrefix (connectFully E R) L = us) {u : U} {v : V}
    {st' : List (CIn U Y) × List X}
    (hres : (v, st') ∈ resolve (ofEngine E) R
      (c ++ [Sum.inl (InLabel.outside, u)], xs)) :
    answer (connectFully E R) L u = some v := by
  have hd : us ++ [u] ∈ dom (connectFully E R) :=
    (mem_dom_connectFully_concat hst u).mpr
      (Part.dom_iff_mem.mpr ⟨(v, st'), hres⟩)
  have hd' : keptPrefix (connectFully E R) L ++ [u] ∈ dom (connectFully E R) := by
    rw [hus]; exact hd
  rw [answer_eq, dif_pos hd']
  exact congrArg some
    ((output_congr (connectFully E R) (by rw [hus]) hd' hd).trans
      (output_connectFully_concat hst hres hd))

/-! ### The round, absorbed

The inner induction of the milestone: a round issues its requests one at a
time, the re-simulating environment asks each of them, and the round replay
follows the engine step for step.  The induction is on the budget — CR18
Definition 3.8's finite bound on consecutive requests — which is also what
bounds the inner rounds a single outer round costs. -/

/-- **A round of the composite is a run of the round replay**, and the requests
it issues are exactly the queries the absorbed environment asks.  The budget
`d` bounds both the recursion and the number of inner rounds the round costs
(`r ≤ j + d`). -/
theorem exists_roundReplay_absorb {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {β : List (U ⊕ Option Y) → ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (R : DDS X Y) (A : DDE.Total Y X) (F : ℕ)
    (c₀ : List (CIn U Y)) (xs₀ : List X) (T₀ : List (X × Option Y))
    (hwait : ∀ ws : List (Option Y), (roundReplay E F c₀ ws).2.1 = none →
      A (T₀↓ᵧ ++ ws) = (roundReplay E F c₀ ws).2.2) :
    ∀ (d : ℕ) (c' : List (CIn U Y)) (j : ℕ) (ws : List (Option Y)),
      β (c'.map unlabel) ≤ d →
      c'.map unlabel ∈ dom E →
      (DDE.Total.transcript R A j)↓ᵧ = T₀↓ᵧ ++ ws →
      resolve (ofEngine E) R (c₀, xs₀) =
        resolve (ofEngine E) R (c', (DDE.Total.transcript R A j)↓ₓ) →
      (∀ zs, roundReplay E F c₀ (ws ++ zs) = roundReplay E (d + 1) c' zs) →
      ∃ (r : ℕ) (v : V) (c'' : List (CIn U Y)) (ws' : List (Option Y)),
        j ≤ r ∧ r ≤ j + d ∧
        (DDE.Total.transcript R A r)↓ᵧ = T₀↓ᵧ ++ ws' ∧
        (v, (c'', (DDE.Total.transcript R A r)↓ₓ)) ∈
          resolve (ofEngine E) R (c₀, xs₀) ∧
        ∀ zs, roundReplay E F c₀ (ws' ++ zs) = ((c'', zs), some v, none) := by
  intro d
  induction d with
  | zero =>
      intro c' j ws hle hE hout hres hrep
      have hm : output E (c'.map unlabel) hE ∈ E.1 (c'.map unlabel) :=
        Part.get_mem hE
      rcases hmove : output E (c'.map unlabel) hE with v | x
      · refine ⟨j, v, c', ws, le_rfl, by omega, hout, ?_, fun zs => ?_⟩
        · rw [hres]
          exact mem_resolve_of_answer (hmove ▸ hm)
        · rw [hrep zs]
          exact roundReplay_answer zs (hmove ▸ hm)
      · exact absurd (lt_of_lt_of_le (hβ _ x (hmove ▸ hm) none) hle)
          (Nat.not_lt_zero _)
  | succ d ih =>
      intro c' j ws hle hE hout hres hrep
      have hm : output E (c'.map unlabel) hE ∈ E.1 (c'.map unlabel) :=
        Part.get_mem hE
      rcases hmove : output E (c'.map unlabel) hE with v | x
      · refine ⟨j, v, c', ws, le_rfl, by omega, hout, ?_, fun zs => ?_⟩
        · rw [hres]
          exact mem_resolve_of_answer (hmove ▸ hm)
        · rw [hrep zs]
          exact roundReplay_answer zs (hmove ▸ hm)
      · have hreq : Sum.inr x ∈ E.1 (c'.map unlabel) := hmove ▸ hm
        have hstall : roundReplay E F c₀ ws = ((c', []), none, some x) := by
          have := hrep []
          rw [List.append_nil] at this
          rw [this]
          exact roundReplay_stuck hreq
        have hneed : A (DDE.Total.transcript R A j)↓ᵧ = some x := by
          rw [hout, hwait ws (by rw [hstall]), hstall]
        have hinner : DDE.Total.transcript R A (j + 1) =
            DDE.Total.transcript R A j ++
              [(x, answer R (DDE.Total.transcript R A j)↓ₓ x)] :=
          DDE.Total.transcript_succ_of_query R A hneed
        have hmap : (c' ++ [Sum.inr (InLabel.inside,
              answer R (DDE.Total.transcript R A j)↓ₓ x)]).map unlabel =
            c'.map unlabel ++
              [Sum.inr (answer R (DDE.Total.transcript R A j)↓ₓ x)] := by simp
        obtain ⟨r, v, c'', ws', h1, h2, h3, h4, h5⟩ :=
          ih (c' ++ [Sum.inr (InLabel.inside,
                answer R (DDE.Total.transcript R A j)↓ₓ x)])
            (j + 1) (ws ++ [answer R (DDE.Total.transcript R A j)↓ₓ x])
            (by
              rw [hmap]
              exact Nat.lt_succ_iff.mp
                (lt_of_lt_of_le (hβ _ x hreq _) hle))
            (by
              rw [hmap]
              exact hIT _ x hreq _)
            (by
              rw [hinner, transcriptOutputs_concat, hout, List.append_assoc])
            (by
              rw [hres, resolve_of_request hreq, hinner,
                transcriptInputs_concat])
            (fun zs => by
              rw [List.append_assoc, List.singleton_append, hrep,
                roundReplay_request _ zs hreq])
        exact ⟨r, v, c'', ws', by omega, by omega, h3, h4, h5⟩

/-! ### The outer invariant, and the receipt -/

/-- **The replay invariant.**  After `k` outer rounds the replay has rebuilt
the outer transcript exactly, sits at the converter history the composite has
reached (`ReachedState` at the *kept* outer history, which is
`answeredQueries` of the transcript), and has consumed exactly the answers of
the first `j` inner rounds — at most `K` per outer round, which is what turns
an outer length into an inner one.  The quantifier over the unconsumed tail
`zs` is what makes the invariant usable both at the truncated answer list (what
the inner environment sees when asked for its next query) and at the full one
(what the reconstruction map sees). -/
theorem fullyReplay_invariant {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {β : List (U ⊕ Option Y) → ℕ} {K : ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) (e : DDE.Total V U)
    (n : ℕ) (R : DDS X Y) :
    ∀ k ≤ n, ∃ (j : ℕ) (c : List (CIn U Y)), j ≤ k * K ∧
      ReachedState E R
          (answeredQueries (DDE.Total.transcript (connectFully E R) e k))
          (c, (DDE.Total.transcript R (absorbFully E (K + 1) e n) j)↓ₓ) ∧
      ∀ zs : List (Option Y),
        fullyReplay E (K + 1) e
            ((DDE.Total.transcript R (absorbFully E (K + 1) e n) j)↓ᵧ ++ zs) k =
          (DDE.Total.transcript (connectFully E R) e k, c, zs) := by
  intro k
  induction k with
  | zero => exact fun _ => ⟨0, [], by simp, reachedState_nil E R, fun _ => rfl⟩
  | succ k ih =>
      intro hk
      obtain ⟨j, c, hjk, hst, hrep⟩ := ih (Nat.le_of_succ_le hk)
      obtain ⟨t, ht⟩ :
          ∃ t, DDE.Total.transcript (connectFully E R) e k = t := ⟨_, rfl⟩
      obtain ⟨T, hT⟩ :
          ∃ T, DDE.Total.transcript R (absorbFully E (K + 1) e n) j = T :=
        ⟨_, rfl⟩
      rw [ht] at hst hrep
      rw [hT] at hst hrep
      have hjk' : j ≤ (k + 1) * K :=
        le_trans hjk (by rw [Nat.succ_mul]; omega)
      have hus : keptPrefix (connectFully E R) t↓ₓ = answeredQueries t := by
        rw [← ht]
        exact (DDE.Total.answeredQueries_transcript (connectFully E R) e k).symm
      rcases hx : e t↓ᵧ with _ | u
      · -- the outer environment stops: nothing moves on either side
        have houter : DDE.Total.transcript (connectFully E R) e (k + 1) = t := by
          rw [DDE.Total.transcript_succ_of_stop (connectFully E R) e (n := k)
            (by rw [ht]; exact hx), ht]
        exact ⟨j, c, hjk', by rw [hT, houter]; exact hst, fun zs => by
          rw [hT, fullyReplay_succ, hrep zs,
            fullyReplayStep_stop E (K + 1) e (st := (t, c, zs)) hx, houter]⟩
      · by_cases hdE : c.map unlabel ++ [Sum.inl u] ∈ dom E
        · -- the engine accepts the query: the round runs, and the environment
          -- asks exactly the requests it issues
          have hwait : ∀ ws : List (Option Y),
              (roundReplay E (K + 1) (c ++ [Sum.inl (InLabel.outside, u)])
                ws).2.1 = none →
              absorbFully E (K + 1) e n (T↓ᵧ ++ ws) =
                (roundReplay E (K + 1) (c ++ [Sum.inl (InLabel.outside, u)])
                  ws).2.2 := by
            intro ws hns
            have h1 : fullyReplay E (K + 1) e (T↓ᵧ ++ ws) k = (t, c, ws) :=
              hrep ws
            have hfix : fullyReplayStep E (K + 1) e
                (fullyReplay E (K + 1) e (T↓ᵧ ++ ws) k) =
                  fullyReplay E (K + 1) e (T↓ᵧ ++ ws) k := by
              rw [h1]
              exact fullyReplayStep_stall E (K + 1) e (st := (t, c, ws)) hx
                hdE hns
            show fullyNeed E (K + 1) e
              (fullyReplay E (K + 1) e (T↓ᵧ ++ ws) n) = _
            rw [fullyReplay_of_fixed E (K + 1) e _ hfix n
              (Nat.le_of_succ_le hk), h1]
            exact fullyNeed_round E (K + 1) e (st := (t, c, ws)) hx hdE
          obtain ⟨r, v, c'', ws', hjr, hrK, hout', hres', hround⟩ :=
            exists_roundReplay_absorb hIT hβ R (absorbFully E (K + 1) e n)
              (K + 1) (c ++ [Sum.inl (InLabel.outside, u)]) T↓ₓ T hwait K
              (c ++ [Sum.inl (InLabel.outside, u)]) j [] (hK _)
              (by simpa using hdE) (by rw [hT, List.append_nil]) (by rw [hT])
              (fun _ => rfl)
          have houter : DDE.Total.transcript (connectFully E R) e (k + 1) =
              t ++ [(u, some v)] := by
            rw [DDE.Total.transcript_succ_of_query (connectFully E R) e
              (n := k) (x := u) (by rw [ht]; exact hx), ht,
              answer_connectFully_round hst hus hres']
          refine ⟨r, c'', ?_, ?_, fun zs => ?_⟩
          · calc r ≤ j + K := hrK
              _ ≤ k * K + K := by omega
              _ = (k + 1) * K := by rw [Nat.succ_mul]
          · rw [houter, answeredQueries_concat_some]
            exact reachedState_concat hst hres'
          · rw [hout', List.append_assoc, fullyReplay_succ, hrep (ws' ++ zs),
              fullyReplayStep_round E (K + 1) e (st := (t, c, ws' ++ zs)) hx
                hdE (hround zs), houter]
        · -- the engine refuses the query: refusal precedes inner traffic, so
          -- the resource is untouched and the composite deletes the query
          have houter : DDE.Total.transcript (connectFully E R) e (k + 1) =
              t ++ [(u, none)] := by
            rw [DDE.Total.transcript_succ_of_query (connectFully E R) e
              (n := k) (x := u) (by rw [ht]; exact hx), ht,
              answer_connectFully_refuse hIT hβ hst hus hdE]
          refine ⟨j, c, hjk', ?_, fun zs => ?_⟩
          · rw [hT, houter, answeredQueries_concat_none]
            exact hst
          · rw [hT, fullyReplay_succ, hrep zs,
              fullyReplayStep_refuse E (K + 1) e (st := (t, c, zs)) hx hdE,
              houter]

/-- **The migrated attachment absorbs** (B4-RESUME): every interaction with
`connectFully E s` is a fixed post-processing of an interaction with `s`,
uniformly in `s`.  This is the hypothesis of `PDS.advFullyDefined_fTransform_le`
for the engine family, and with it the migrated converters are nonexpanding.

The re-simulating environment runs the engine itself.  It holds the converter
history, so by `connectFully_refusal_first` it decides refusals without
consulting the resource — a refused outer query costs no inner traffic and is
deleted on both sides — and by `resolve_of_request` every request it relays is
answered by `System.answer s`, i.e. by the inner transcript's own answer.

The hypotheses are CR18 Definition 3.8's converter class with its input
alphabet clause replaced by its negation (ruling R2):

* `hIT` — inner-facing totality (`InnerTotal`), the replacement for
  `Converter.AnswersInY`, which is the B4 pathology in the definition;
* `hβ` — Definition 3.8's finite-bound clause in well-founded form;
* `hK` — that bound **uniform over converter histories**, which is how CR18
  states it ("a finite upper bound on the number of consecutive requests").
  It is a genuine hypothesis and not a proof artefact: `hβ` alone bounds a
  round's requests by `β` at that round's own history, and nothing stops `β`
  from growing with what the engine has been told, so an engine can be made to
  ask arbitrarily many questions in its second round depending on the answer
  to its first — and then no single `m` serves every `s`.

`m := n * K`: at most `K` inner rounds per outer round, by the budget. -/
theorem exists_absorb_connectFully {E : DDS (U ⊕ Option Y) (V ⊕ X)}
    {β : List (U ⊕ Option Y) → ℕ} {K : ℕ} (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) (e : DDE.Total V U)
    (n : ℕ) :
    ∃ (e' : DDE.Total Y X) (m : ℕ)
      (p : List (X × Option Y) → List (U × Option V)),
      ∀ s : DDS X Y,
        DDE.Total.transcript (connectFully E s) e n =
          p (DDE.Total.transcript s e' m) := by
  refine ⟨absorbFully E (K + 1) e n, n * K,
    fun T => (fullyReplay E (K + 1) e T↓ᵧ n).1, fun s => ?_⟩
  obtain ⟨j, c, hjn, -, hrep⟩ :=
    fullyReplay_invariant hIT hβ hK e n s n le_rfl
  obtain ⟨zs, hzs⟩ :
      ∃ zs, (DDE.Total.transcript s (absorbFully E (K + 1) e n) j)↓ᵧ ++ zs =
        (DDE.Total.transcript s (absorbFully E (K + 1) e n) (n * K))↓ᵧ := by
    obtain ⟨w, hw⟩ :=
      DDE.Total.transcript_prefix s (absorbFully E (K + 1) e n) hjn
    exact ⟨w↓ᵧ, by simp only [transcriptOutputs, ← List.map_append, hw]⟩
  show DDE.Total.transcript (connectFully E s) e n =
    (fullyReplay E (K + 1) e
      (DDE.Total.transcript s (absorbFully E (K + 1) e n) (n * K))↓ᵧ n).1
  rw [← hzs, hrep zs]

end Absorb

end

end System

/-! ## Φ-level re-basing

`connectFully E` is a map `DDS X Y → DDS U V`; it is an endomorphism of Φ
exactly for the engines whose outer face is `Uni` on both sides, i.e.

    E : DDS (Uni ⊕ Option Uni) (Uni ⊕ Uni)

— `Uni`-valued outer answers, `Option Uni`-valued inner answers.  The Option
lives at the *interaction*, never on the object: the composite is an ordinary
`DDS Uni Uni` and `attachFully E` is an honest `Function.End Phi`.

The relay `idEngineFully` is deliberately **not** in this family: its outer
answers land in `Option Y`, and its composite is `R⊥`.  The identity of the
migrated attachment therefore lives at the metric layer, as `R ↦ R⊥`, where
ruling R4's `Adv⊥` completes both sides before comparing them — not as a member
of `converterMonoidFully`. -/

noncomputable section

open Probability (Distribution)

universe u

/-- **The migrated attachment endomorphism of Φ**: the deterministic engine,
attached to the completion of the resource.  The Φ-level counterpart of
`attach`, which stays as it is and stays refuted (B4). -/
def attachFully
    (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) :
    Function.End Phi.{u} :=
  Distribution.fTransform (System.connectFully E)

/-- **The metric-facing converter monoid** — the Σ the fully defined metric
layer may consume: migrated attachments of engines that satisfy the A6
hypotheses (inner totality and a request budget, so that refusal precedes inner
traffic), blocks, and the parallel frames at a subprobability partner.

`converterMonoid` is untouched: it is generated by `connectPhi`/`attach`/
`block` over the refuted `connect`, and the B4 witness lives inside it.

**B4-RESUME delta (2026-08-17).**  Nonexpansion is proved for the *budgeted*
sub-closure `converterMonoidFullyBudgeted`, not for this monoid: absorption
needs CR18 Definition 3.8's request bound *uniformly over converter histories*,
while the generating condition here is only `∃ β, AnswersWithinBudget E β`,
which bounds a round's requests by `β` at that round's own history.  The gap is
real, not a proof artefact — see `System.exists_absorb_connectFully`. -/
def converterMonoidFully : Submonoid (Function.End Phi.{u}) :=
  Submonoid.closure
    ({π | ∃ E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}),
        System.InnerTotal E ∧ (∃ β, System.AnswersWithinBudget E β) ∧
          π = attachFully E} ∪
      {π | ∃ Q : Set Uni.{u}, π = block Q} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c RL TL} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c TL RL})

theorem attachFully_mem_converterMonoidFully
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : ∃ β, System.AnswersWithinBudget E β) :
    attachFully E ∈ converterMonoidFully.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inl ⟨E, hIT, hβ, rfl⟩)))

theorem block_mem_converterMonoidFully (Q : Set Uni.{u}) :
    block Q ∈ converterMonoidFully.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨Q, rfl⟩)))

theorem parRight_mem_converterMonoidFully (c : Set Uni.{u}) {TL : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c RL TL) ∈ converterMonoidFully.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨c, TL, h0, h1, rfl⟩))

theorem parLeft_mem_converterMonoidFully (c : Set Uni.{u}) {TL : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c TL RL) ∈ converterMonoidFully.{u} :=
  Submonoid.subset_closure (Or.inr ⟨c, TL, h0, h1, rfl⟩)

/-- The unit is there, as in every `Submonoid.closure` — recorded because
`converterMonoid` records it too. -/
example : (1 : Function.End Phi.{u}) ∈ converterMonoidFully.{u} :=
  one_mem _

/-! ## B4-RESUME — the budgeted monoid, and its nonexpansion

CR18 Definition 3.8 asks a converter for "a finite upper bound on the number of
consecutive requests": one bound for the converter, not one per history.  A6's
`AnswersWithinBudget` is the well-founded reading of that clause and is weaker;
absorption needs the uniform one (`System.exists_absorb_connectFully`), so the
monoid the metric layer may consume is the sub-closure generated by the
uniformly budgeted attachments.  The two are related by
`converterMonoidFullyBudgeted_le_converterMonoidFully`, and the delta is
recorded there, in `converterMonoidFully` and in `LEDGER.md`. -/

/-- **The migrated attachment never helps a distinguisher.**  Whatever an
environment learns from the converted resource it learns from the resource
itself, by running the engine — `System.exists_absorb_connectFully` through the
pushforward reduction. -/
theorem attachFully_mem_nonexpandingConverters
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinBudget E β)
    (hK : ∀ l, β l ≤ K) :
    attachFully E ∈ nonexpandingConverters.{u} := fun RL SL =>
  PDS.advFullyDefined_fTransform_le (System.connectFully E) RL SL
    fun e n => System.exists_absorb_connectFully hIT hβ hK e n

/-- **The budgeted converter monoid**: the same three families as
`converterMonoidFully`, with the attachment family carrying CR18 Definition
3.8's *uniform* request bound.  This is the Σ over which the fully defined
metric layer's Lemma 2 and Lemma 5 receipts hold. -/
def converterMonoidFullyBudgeted : Submonoid (Function.End Phi.{u}) :=
  Submonoid.closure
    ({π | ∃ E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}),
        System.InnerTotal E ∧ System.AnswersWithinUniformBudget E ∧
          π = attachFully E} ∪
      {π | ∃ Q : Set Uni.{u}, π = block Q} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c RL TL} ∪
      {π | ∃ (c : Set Uni.{u}) (TL : Phi.{u}), (∀ t, 0 ≤ ofPhi TL t) ∧
        (ofPhi TL).weight ≤ 1 ∧ π = fun RL => par c TL RL})

theorem attachFully_mem_converterMonoidFullyBudgeted
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinUniformBudget E) :
    attachFully E ∈ converterMonoidFullyBudgeted.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inl ⟨E, hIT, hβ, rfl⟩)))

theorem block_mem_converterMonoidFullyBudgeted (Q : Set Uni.{u}) :
    block Q ∈ converterMonoidFullyBudgeted.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inl (Or.inr ⟨Q, rfl⟩)))

theorem parRight_mem_converterMonoidFullyBudgeted (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c RL TL) ∈ converterMonoidFullyBudgeted.{u} :=
  Submonoid.subset_closure (Or.inl (Or.inr ⟨c, TL, h0, h1, rfl⟩))

theorem parLeft_mem_converterMonoidFullyBudgeted (c : Set Uni.{u})
    {TL : Phi.{u}} (h0 : ∀ t, 0 ≤ ofPhi TL t) (h1 : (ofPhi TL).weight ≤ 1) :
    (fun RL => par c TL RL) ∈ converterMonoidFullyBudgeted.{u} :=
  Submonoid.subset_closure (Or.inr ⟨c, TL, h0, h1, rfl⟩)

/-- The budgeted monoid sits inside the A6 monoid: a uniform bound is a
bound.  The inclusion is the honest statement of the delta — the converse is
not claimed, and `converterMonoidFully` carries no nonexpansion receipt. -/
theorem converterMonoidFullyBudgeted_le_converterMonoidFully :
    converterMonoidFullyBudgeted.{u} ≤ converterMonoidFully.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨E, hIT, ⟨β, _, hβ, _⟩, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact attachFully_mem_converterMonoidFully hIT ⟨β, hβ⟩
  · exact block_mem_converterMonoidFully Q
  · exact parRight_mem_converterMonoidFully c h0 h1
  · exact parLeft_mem_converterMonoidFully c h0 h1

/-- **The migrated converter monoid is nonexpanding** (B4-RESUME, the closure
step): every generator absorbs into the environment — migrated attachments by
`System.exists_absorb_connectFully`, blocks by `exists_absorb_blockSet`,
parallel frames by `exists_absorb_par` — and `nonexpandingConverters` is a
submonoid, so the whole closure does.

This is the statement B5 left open.  It is *not* available for
`converterMonoid` (the B4 witness lives inside it) and not claimed for
`converterMonoidFully` (whose attachment family is not uniformly budgeted). -/
theorem converterMonoidFullyBudgeted_le_nonexpandingConverters :
    converterMonoidFullyBudgeted.{u} ≤ nonexpandingConverters.{u} := by
  refine Submonoid.closure_le.mpr ?_
  rintro π ((((⟨E, hIT, ⟨β, K, hβ, hK⟩, rfl⟩) | ⟨Q, rfl⟩) |
    ⟨c, TL, h0, h1, rfl⟩) | ⟨c, TL, h0, h1, rfl⟩)
  · exact attachFully_mem_nonexpandingConverters hIT hβ hK
  · exact block_mem_nonexpandingConverters Q
  · exact parRight_mem_nonexpandingConverters h0 h1
  · exact parLeft_mem_nonexpandingConverters h0 h1

/-! ## Interface-local attachment — RETIRED RECORD (G1 closed by DRIFT-REPAIR leg (d))

The receipt this note said could not be delivered on the relay design WAS
delivered on the ownership-dispatch design: `System.attachEngineFully_comm`
(AttachEngineFully.lean).  This section is retained verbatim below as the
record of WHY the relay design fails; see LEDGER "G1 — CLOSED".


MauRen16 §3.3's commutation `(αR)β = α(Rβ)` asks for an *interface-local*
attachment family on this Σ: for a query set `i ⊆ Uni`, an engine
`relayExcept i E : DDS (Uni ⊕ Option Uni) (Uni ⊕ Uni)` that serves outer
queries in `i` through `E` and relays every other outer query verbatim, with
`attachFullyAt i E := attachFully (relayExcept i E)`, so that

    attachFullyAt i E * attachFullyAt j F = attachFullyAt j F * attachFullyAt i E

for disjoint `i`, `j` (LEDGER.md gap G1, matrix row 22).  Nothing of the kind
is defined here, and the reason is a design obstruction that has to be ruled
on before any such definition is written down.  Recorded so the next attempt
does not rediscover it.

**The obstruction.**  A relayed round must turn the completion's answer
`o : Option Uni` into an outer answer in `Uni`; the round has already issued
its request, so it cannot refuse (that is the B4 pathology, and it would cost
`InnerTotal` and with it `exists_absorb_connectFully`).  So the relay must
*render* `⊥` as some designated `botToken : Uni` — and rendering is exactly
what makes the two attachment orders disagree, because on one side the
engine's inner face sees the other attachment's rendering while on the other
side it sees the raw completion.  Two independent witnesses, both at
`i = {a}`, `j = {b}`, `a ≠ b`:

* *inner face.*  Let `E` request `a` and answer `c₁` on `some _`, `c₀` on
  `none` (inner-total, budget 1, requests inside `i`); let `F` answer at once
  on any query of `j`; let `s` refuse `a`.  Left to right,
  `E` is driven against `connectFully (relayExcept j F) s`, whose relay round
  at `a ∉ j` answers `botToken` and never refuses, so `E` sees
  `some botToken` and the composite answers `c₁`.  Right to left, `a ∉ j` is
  relayed to `connectFully (relayExcept i E) s`, where `E` queries `s`
  directly, sees `none`, and the composite answers `c₀`.

* *outer face.*  Let `E` refuse the outer query `a`.  Left to right the
  composite refuses `a` — an observable `⊥`, and the query is deleted from its
  history by CR18 Definition 3.3.  Right to left that refusal is read by a
  relay round of `relayExcept j F`, which renders it `botToken`: a *defined*
  answer, and the query is kept.

Both survive every choice of `botToken`, and neither is repairable by a
hypothesis on `E` and `F` alone: the first turns on whether `s` refuses, and
the equation is an equation of endomorphisms, so it must hold at every `s`.

**What the definition must therefore do.**  The `⊥` of the composite and the
`⊥` relayed out of the resource have to be *identified*, not merely rendered
on one side:

1. the engine feeds `E` the rendered answer `some (ρ o)` rather than `o`,
   where `ρ (some v) = v` and `ρ none = botToken` — forced, since
   transparency needs `ρ (some (ρ o)) = ρ o`, which no injective rendering
   satisfies, so some identification is unavoidable and this is the smallest
   one (`botToken` becomes indistinguishable from a resource answering
   `botToken`, and from nothing else); and
2. either the engine is made total on outer queries, answering `botToken`
   where `E` refuses (unconditional commutation, at the price that
   `attachFullyAt i E` never refuses and its image lies in the total
   subcarrier), or refusals are kept and the commutation carries the
   hypothesis that `E` and `F` never refuse an outer query (a converter class
   restriction — the paper's converters always respond).

Both are semantic rulings about what an attachment *is* on this carrier, which
is why the family is not defined here on either reading. -/

end

end RandomSystems

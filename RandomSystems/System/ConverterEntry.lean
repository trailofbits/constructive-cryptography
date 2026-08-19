/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.AttachEngineFully

/-!
# The entry point: a typed converter as a member of the metric-facing `Σ`

PAPER-FAITHFUL

Cachin–Renner(–Maurer), *Lecture Notes on Cryptography*, **Definition 3.8,
printed p. 62** (read on the rendered page): "a deterministic discrete
converter converting an `(X,Y)`-DDS into a `(U,V)`-DDS is just a DDS over the
converter alphabets", together with its finite-bound clause, "a finite upper
bound on the number of consecutive requests".

An application names exactly one converter notion — the element of
`converterMonoidAt` acting on `Phi`.  What an application *writes down*,
though, is a history function at its own alphabets: given the outer messages
so far and the inner answers of the round, either ask the resource one more
question or answer outward.  This module is the crossing between the two, done
once: `converterEngine` builds the attachment engine, the three receipts are
discharged from two conditions on the history function, and
`converterEngine_mem_converterMonoidAt` is the membership.

Membership is only half of what an application needs.  The other half — that
the converter it wrote down *computes* what it was written to compute — is the
closing section: `ConverterRunsTo` is one round of the history function against
`R⊥`, `mem_resolve_converterEngine` turns such a run into CR18 Definition 3.9's
resolved round (printed p. 62), and `attachEngineFully_converterEngine_univ` is
the realization equation an application instantiates.

## The two conditions, and why they are the right two

They are exactly the hypotheses `attachAt_mem_converterMonoidAt` consumes,
read back through the crossing:

* `ConverterInnerTotal` — Ruling R2's inner-facing totality: having asked, the
  converter reacts to whatever comes back, a refusal included.  CR18 Definition
  3.8's own input-alphabet clause demands the opposite; the replacement is the
  standing repository extension (`System.InnerTotal`, `ConnectFullyDefined.lean`).
* `ConverterRequestsBounded ν K` — Definition 3.8's finite-bound clause,
  printed p. 62, at the round: at most `K` inner queries per outer query.  It
  is *not* bookkeeping.  Absorption needs the bound to be uniform over
  converter histories, so a converter whose round length grows without bound
  fails this condition, and with it the *sufficient* condition
  `attachAt_mem_converterMonoidAt` that the entry point below runs through.
  That is the whole of it: `converterMonoidAt` is a `Submonoid.closure`, and
  failing one sufficient condition is not non-membership — denying that would
  need a separating invariant on the closure, and this tree has none.  What a
  bounded round length buys is the constant `K`.

## The round-local reading of the history function

The two lists are the outer queries *of the whole interaction* and the inner
answers *of the current round*.  Round-local is a **convenience, not a
necessity**.  `Converter.ProtocolFn U V X Y` is an `abbrev` for the very type
spelled out here, so both readings apply to one and the same object, and the
landed `Converter.AnswersWithin` already states Definition 3.8's clause
verbatim — "a finite upper bound on the number of consecutive outputs of the
form `(in, x)`", printed p. 62 — on that cumulative presentation: a bound on
query streaks, stated at cumulative answers.  What round-local buys is only
that the bound reads `ys.length < K`, which is `AnswersWithinUniformBudget`'s
`β` with no streak reasoning at all.

The two readings are therefore related, and related here rather than left to
coexist: `ConverterRequestsBounded.answersWithin` shows the round-local
condition implies the cumulative one (at `K + 1`, and the offset is sharp),
and `exists_answersWithin_not_converterRequestsBounded` shows the converse
fails, so the streak reading may never be cited for the round-local one.  The
round boundary itself is read off the engine history by `roundAnswers`, which
resets at each outer query — the same boundary CR18 Definition 3.9 draws
(printed p. 62).

## What the engine does with a query it cannot read

Outer queries are decoded at `U`; a history that does not decode leaves the
engine undefined, and the composite therefore refuses.  Inner answers are
decoded at `Y` *totally*, an undecodable answer arriving as `⊥`: the converter
cannot read it, and Ruling R2 makes a refusal observable and non-fatal, so
this is the faithful rendering rather than a stall.  Against a resource
included by `System.ofTyped` the case does not arise.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u

variable {U V X Y : Type u}

/-! ## Reading an engine history -/

/-- The outer queries an engine history records. -/
def outerQueries (l : List (Uni.{u} ⊕ Option Uni.{u})) : List Uni.{u} :=
  l.filterMap fun a => match a with | Sum.inl q => some q | Sum.inr _ => none

/-- The inner answers received since the last outer query — the current round
of CR18 Definition 3.9's application (printed p. 62). -/
def roundAnswers (l : List (Uni.{u} ⊕ Option Uni.{u})) : List (Option Uni.{u}) :=
  l.foldl (fun acc a => match a with | Sum.inl _ => [] | Sum.inr o => acc ++ [o]) []

@[simp] theorem outerQueries_nil :
    outerQueries ([] : List (Uni.{u} ⊕ Option Uni.{u})) = [] := rfl

@[simp] theorem roundAnswers_nil :
    roundAnswers ([] : List (Uni.{u} ⊕ Option Uni.{u})) = [] := rfl

@[simp] theorem outerQueries_concat_inl (l : List (Uni.{u} ⊕ Option Uni.{u}))
    (q : Uni.{u}) : outerQueries (l ++ [Sum.inl q]) = outerQueries l ++ [q] := by
  simp [outerQueries]

@[simp] theorem outerQueries_concat_inr (l : List (Uni.{u} ⊕ Option Uni.{u}))
    (o : Option Uni.{u}) : outerQueries (l ++ [Sum.inr o]) = outerQueries l := by
  simp [outerQueries]

@[simp] theorem roundAnswers_concat_inl (l : List (Uni.{u} ⊕ Option Uni.{u}))
    (q : Uni.{u}) : roundAnswers (l ++ [Sum.inl q]) = [] := by
  simp [roundAnswers]

@[simp] theorem roundAnswers_concat_inr (l : List (Uni.{u} ⊕ Option Uni.{u}))
    (o : Option Uni.{u}) :
    roundAnswers (l ++ [Sum.inr o]) = roundAnswers l ++ [o] := by
  simp [roundAnswers]

/-! ## The two conditions on the history function -/

/-- **Ruling R2's inner-facing totality**, at the history-function
presentation: having asked, the converter is defined at the round extended by
*any* answer, a refusal included. -/
def ConverterInnerTotal (ν : List U × List (Option Y) →. X ⊕ V) : Prop :=
  ∀ (us : List U) (ys : List (Option Y)) (x : X), Sum.inl x ∈ ν (us, ys) →
    ∀ o : Option Y, (ν (us, ys ++ [o])).Dom

/-- **CR18 Definition 3.8's finite request bound** (printed p. 62), at the
history-function presentation: a round asks at most `K` questions. -/
def ConverterRequestsBounded (ν : List U × List (Option Y) →. X ⊕ V) (K : ℕ) :
    Prop :=
  ∀ (us : List U) (ys : List (Option Y)) (x : X), Sum.inl x ∈ ν (us, ys) →
    ys.length < K

/-! ### The two readings of Definition 3.8's bound, related

`ConverterRequestsBounded` and the landed `Converter.AnswersWithin` are two
readings of one clause on one type (`Converter.ProtocolFn` is an `abbrev` for
the type used here).  Leaving them unbridged would let a future application
prove one and cite the other, so both directions are settled here.
-/

/-- **The round-local bound implies Definition 3.8's streak bound** (printed
p. 62), at every pair — reachability is not used.  If a query is only ever
issued at fewer than `K` answers, then no `K + 1` consecutive queries open
anywhere: the `K`-th extension already carries `K` answers. -/
theorem ConverterRequestsBounded.answersWithinAt
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ConverterRequestsBounded ν K) (p : List U × List (Option Y)) :
    Converter.AnswersWithinAt ν p (K + 1) := by
  intro ext hlen hall
  obtain ⟨x, hx⟩ := hall K (by omega)
  have := hK p.1 _ x hx
  rw [List.length_append, List.length_take] at this
  omega

/-- **The bridge**: the entry point's round-local receipt discharges the
landed converter surface's uniform reading of CR18 Definition 3.8's clause
(printed p. 62), at `K + 1`.

The offset is sharp, not slack: `ConverterRequestsBounded ν K` admits a round
of exactly `K` queries — issued at `0, …, K-1` answers — and `([u], [])` is
reachable, so `Converter.AnswersWithin ν K` genuinely fails for such a `ν`.
(That sharpness is argued, not landed: no witness for it is in the tree.  The
non-interchangeability below *is* landed.) -/
theorem ConverterRequestsBounded.answersWithin
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ConverterRequestsBounded ν K) : Converter.AnswersWithin ν (K + 1) :=
  fun p _ => hK.answersWithinAt p

/-- **The converse fails, so the two readings are not interchangeable.**  The
streak bound constrains how many queries run *back to back*; the round-local
bound constrains *where in the answer list* a query may be issued at all.  A
history function that queries exactly once, but only after five answers, has
no streak of two and no round-local bound below six. -/
theorem exists_answersWithin_not_converterRequestsBounded :
    ∃ ν : List Unit × List (Option Unit) →. Unit ⊕ Unit,
      Converter.AnswersWithin ν 2 ∧ ¬ ConverterRequestsBounded ν 2 := by
  refine ⟨fun p => Part.some (if p.2.length = 5 then Sum.inl () else Sum.inr ()), ?_, ?_⟩
  · intro p _ ext hlen hall
    obtain ⟨x, hx⟩ := hall 0 (by omega)
    obtain ⟨x', hx'⟩ := hall 1 (by omega)
    simp only [Part.mem_some_iff, List.take_zero, List.append_nil] at hx
    simp only [Part.mem_some_iff, List.length_append, List.length_take] at hx'
    have h5 : p.2.length = 5 := by
      by_contra h
      rw [if_neg h] at hx
      exact absurd hx (by simp)
    rw [h5] at hx'
    rw [if_neg (by omega)] at hx'
    exact absurd hx' (by simp)
  · intro h
    have := h [()] [none, none, none, none, none] () (by simp)
    simp at this

/-! ## The engine -/

/-- Addressing a move of the history function: an inner query carries the
inner alphabet's tag, an outer answer the outer one.  CR18 Definition 3.8's
two output labels (printed p. 62) at the universal alphabet. -/
def converterAddress (X V : Type u) : X ⊕ V → Uni.{u} ⊕ Uni.{u}
  | Sum.inl x => Sum.inr (encode X x)
  | Sum.inr v => Sum.inl (encode V v)

@[simp] theorem converterAddress_inl (x : X) :
    converterAddress X V (Sum.inl x) = Sum.inr (encode X x) := rfl

@[simp] theorem converterAddress_inr (v : V) :
    converterAddress X V (Sum.inr v) = Sum.inl (encode V v) := rfl

/-- The engine's move: decode the outer history at `U`, read the round's
answers at `Y`, consult the history function, and address the move. -/
def converterMove (X V : Type u) (ν : List U × List (Option Y) →. X ⊕ V)
    (l : List (Uni.{u} ⊕ Option Uni.{u})) : Part (Uni.{u} ⊕ Uni.{u}) :=
  (decodeList U (outerQueries l)).bind fun us =>
    (ν (us, (roundAnswers l).map fun o => o.bind decodeOption)).map
      (converterAddress X V)

/-- **The typed converter as an attachment engine.**  CR18 Definition 3.8's
object (printed p. 62) at the universal alphabet, cut down to the histories all
of whose prefixes the converter accepts (`System.validate`, as `ofTyped`
does). -/
def converterEngine (X V : Type u) (ν : List U × List (Option Y) →. X ⊕ V) :
    DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) :=
  validate (converterMove X V ν)

theorem mem_converterMove_of_mem_converterEngine
    {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}}
    (h : m ∈ (converterEngine X V ν).1 l) : m ∈ converterMove X V ν l := by
  obtain ⟨hd, hm⟩ := h
  exact ⟨hd.2 l (List.prefix_refl l) hd.1, hm⟩

theorem mem_dom_converterEngine {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} (h : l ∈ dom (converterEngine X V ν)) :
    l ≠ [] ∧ ∀ l', l' <+: l → l' ≠ [] → (converterMove X V ν l').Dom := h

/-- A move the engine makes comes from a move of the history function. -/
theorem exists_mem_of_mem_converterMove {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}}
    (h : m ∈ converterMove X V ν l) :
    ∃ us ∈ decodeList U (outerQueries l),
      ∃ n ∈ ν (us, (roundAnswers l).map fun o => o.bind decodeOption),
        m = converterAddress X V n := by
  obtain ⟨us, hus, hrest⟩ := Part.mem_bind_iff.mp h
  obtain ⟨n, hn, hm⟩ := (Part.mem_map_iff _).mp hrest
  exact ⟨us, hus, n, hn, hm.symm⟩

/-! ## The three receipts -/

/-- **The engine reaches only into `i`**: every request it emits is a query
addressed at the inner alphabet, so an interface containing that alphabet's
copy contains every request. -/
theorem requestsWithin_converterEngine {ν : List U × List (Option Y) →. X ⊕ V}
    (i : Set Uni.{u}) (hi : ∀ x : X, encode X x ∈ i) :
    RequestsWithin i (converterEngine X V ν) := by
  intro l x hx
  obtain ⟨us, -, n, -, hm⟩ :=
    exists_mem_of_mem_converterMove (mem_converterMove_of_mem_converterEngine hx)
  rcases n with x' | v
  · have : x = encode X x' := by simpa using hm
    exact this ▸ hi x'
  · exact absurd hm (by simp)

/-- **Inner-facing totality transports** (Ruling R2): the engine reacts to
whatever the completion returns because the history function does. -/
theorem innerTotal_converterEngine {ν : List U × List (Option Y) →. X ⊕ V}
    (hIT : ConverterInnerTotal ν) : InnerTotal (converterEngine X V ν) := by
  intro l x hx o
  obtain ⟨hne, hpre⟩ := hx.1
  obtain ⟨us, hus, n, hn, hm⟩ :=
    exists_mem_of_mem_converterMove (mem_converterMove_of_mem_converterEngine hx)
  have hreq : ∃ x' : X, n = Sum.inl x' := by
    rcases n with x' | v
    · exact ⟨x', rfl⟩
    · exact absurd hm (by simp)
  obtain ⟨x', rfl⟩ := hreq
  refine ⟨by simp, fun l' hl' hne' => ?_⟩
  rcases List.prefix_concat_iff.mp hl' with rfl | hl''
  · refine Part.dom_iff_mem.mpr ?_
    rw [converterMove]
    have hdom : (ν (us, ((roundAnswers l).map fun o' => o'.bind decodeOption)
        ++ [o.bind decodeOption])).Dom :=
      hIT us _ x' hn (o.bind decodeOption)
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hdom
    refine ⟨converterAddress X V w, ?_⟩
    rw [Part.mem_bind_iff]
    refine ⟨us, by rwa [outerQueries_concat_inr], ?_⟩
    rw [Part.mem_map_iff]
    exact ⟨w, by rwa [roundAnswers_concat_inr, List.map_append], rfl⟩
  · exact hpre l' hl'' hne'

/-- The round budget as a measure on engine histories: the requests a round
may still make. -/
def converterBudget (K : ℕ) (l : List (Uni.{u} ⊕ Option Uni.{u})) : ℕ :=
  K - (roundAnswers l).length

/-- **CR18 Definition 3.8's request bound transports** (printed p. 62), and it
is *uniform*: the measure is bounded by `K` at every engine history because it
counts within one round. -/
theorem answersWithinUniformBudget_converterEngine
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ConverterRequestsBounded ν K) :
    AnswersWithinUniformBudget (converterEngine X V ν) := by
  refine ⟨converterBudget K, K, ?_, fun l => Nat.sub_le _ _⟩
  intro l x hx o
  obtain ⟨us, -, n, hn, hm⟩ :=
    exists_mem_of_mem_converterMove (mem_converterMove_of_mem_converterEngine hx)
  have hreq : ∃ x' : X, n = Sum.inl x' := by
    rcases n with x' | v
    · exact ⟨x', rfl⟩
    · exact absurd hm (by simp)
  obtain ⟨x', rfl⟩ := hreq
  have hlt : ((roundAnswers l).map fun o' => o'.bind (decodeOption (X := Y))).length < K :=
    hK us _ x' hn
  rw [List.length_map] at hlt
  simp only [converterBudget, roundAnswers_concat_inr, List.length_append,
    List.length_singleton]
  omega

/-! ## The round, computed

The receipts above place the engine in `Σ`; they say nothing about what it
*answers*.  An application needs the second half — that the converter it wrote
down actually computes what it was written to compute — and that is one
statement, proved once here rather than per application: driving
`converterEngine` through **one** outer query with `k` inner requests yields the
history function's own outer answer, with the resource's answers threaded back
into the round.

`ConverterRunsTo` is that run, as a relation: from the round state `(us, ys)`
and resource history `xs`, the history function either answers outward, or asks
one question and continues from the answer `R⊥` gives it.  It is CR18
Definition 3.9's inner resolution (printed p. 62) read on the history-function
side, and it is what an application supplies; the round lemma turns it into a
resolved round and the drive lemma iterates it. -/

open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve)

/-- The outer queries of a concatenation are the concatenation of the outer
queries. -/
theorem outerQueries_append (l₁ l₂ : List (Uni.{u} ⊕ Option Uni.{u})) :
    outerQueries (l₁ ++ l₂) = outerQueries l₁ ++ outerQueries l₂ := by
  simp [outerQueries, List.filterMap_append]

/-- Inner answers carry no outer query. -/
theorem outerQueries_map_inr (as : List (Option Uni.{u})) :
    outerQueries (as.map Sum.inr) = [] := by
  induction as with
  | nil => rfl
  | cons a t ih => simp [outerQueries]

/-- A history all of whose entries carry `U`'s address decodes. -/
theorem decodeList_dom_of_forall_tag :
    ∀ {l : List Uni.{u}}, (∀ q ∈ l, q.1 = U) → (decodeList U l).Dom := by
  intro l
  induction l with
  | nil => intro _; exact ⟨⟩
  | cons q t ih =>
      intro h
      refine Part.bind_dom.mpr ⟨h q (by simp), ?_⟩
      exact Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (Part.get_mem
        (ih fun q' hq' => h q' (List.mem_cons_of_mem _ hq')))⟩

/-- An accepted move of the validated engine is the underlying move. -/
theorem mem_converterEngine_of_mem_converterMove {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}}
    (hdom : l ∈ dom (converterEngine X V ν)) (hm : m ∈ converterMove X V ν l) :
    m ∈ (converterEngine X V ν).1 l :=
  ⟨hdom, Part.get_eq_of_mem hm (hdom.2 l (List.prefix_refl l) hdom.1)⟩

/-- **A round of the history function against `R⊥`** — CR18 Definition 3.9's
inner resolution (printed p. 62) on the history-function side.  From the outer
history `us`, the round answers `ys` received so far and the resource history
`xs`, either the history function answers `v` outward, or it asks `x` and the
run continues at the answer `R⊥` returns — `none` where the resource declines,
which Ruling R2 makes an ordinary inner answer rather than a stall. -/
inductive ConverterRunsTo (ν : List U × List (Option Y) →. X ⊕ V) (R : DDS Uni.{u} Uni.{u})
    (us : List U) : List (Option Y) → List Uni.{u} → V → Prop
  | stop {ys xs v} (h : Sum.inr v ∈ ν (us, ys)) : ConverterRunsTo ν R us ys xs v
  | ask {ys xs x v} (h : Sum.inl x ∈ ν (us, ys))
      (ih : ConverterRunsTo ν R us
        (ys ++ [(answer R xs (encode X x)).bind decodeOption]) (xs ++ [encode X x]) v) :
      ConverterRunsTo ν R us ys xs v

/-- A run makes a first move, so the history function is defined where it
starts. -/
theorem ConverterRunsTo.dom {ν : List U × List (Option Y) →. X ⊕ V} {R : DDS Uni.{u} Uni.{u}}
    {us : List U} {ys : List (Option Y)} {xs : List Uni.{u}} {v : V}
    (h : ConverterRunsTo ν R us ys xs v) : (ν (us, ys)).Dom := by
  cases h with
  | stop h => exact Part.dom_iff_mem.mpr ⟨_, h⟩
  | ask h _ => exact Part.dom_iff_mem.mpr ⟨_, h⟩

/-- **The round lemma**: a run of the history function *is* a resolved round of
its engine.  The requests are appended to the resource history and the answers
to the converter conversation, so the engine's conversation grows by inner
answers only — which is why the outer answer arrives at all and why the next
round starts from the same outer queries.

This is the reusable half of a realization equation: an application supplies
`ConverterRunsTo` for its own history function and gets CR18 Definition 3.9's
round (printed p. 62) without touching `PFun.fix`. -/
theorem mem_resolve_converterEngine {ν : List U × List (Option Y) →. X ⊕ V}
    {R : DDS Uni.{u} Uni.{u}} {us : List U} {ys : List (Option Y)}
    {xs : List Uni.{u}} {v : V}
    (hrun : ConverterRunsTo ν R us ys xs v) :
    ∀ c : List (CIn Uni.{u} Uni.{u}),
      c.map unlabel ∈ dom (converterEngine X V ν) →
      us ∈ decodeList U (outerQueries (c.map unlabel)) →
      (roundAnswers (c.map unlabel)).map (fun o => o.bind decodeOption) = ys →
      ∃ as : List (Option Uni.{u}), ∃ bs : List Uni.{u},
        (encode V v, (c ++ as.map (fun o => Sum.inr (InLabel.inside, o)), xs ++ bs))
            ∈ resolve (ofEngine (converterEngine X V ν)) R (c, xs) ∧
          (c ++ as.map (fun o => Sum.inr (InLabel.inside, o))).map unlabel
            ∈ dom (converterEngine X V ν) := by
  induction hrun with
  | @stop ys xs v h =>
      intro c hval hus hy
      refine ⟨[], [], ?_, ?_⟩
      · simp only [List.map_nil, List.append_nil]
        refine mem_resolve_of_answer ?_
        refine mem_converterEngine_of_mem_converterMove hval ?_
        rw [converterMove, Part.mem_bind_iff]
        refine ⟨us, hus, ?_⟩
        rw [Part.mem_map_iff]
        exact ⟨Sum.inr v, by rw [hy]; exact h, rfl⟩
      · simpa using hval
  | @ask ys xs x v h hrest ih =>
      intro c hval hus hy
      have hreq : Sum.inr (encode X x) ∈ (converterEngine X V ν).1 (c.map unlabel) := by
        refine mem_converterEngine_of_mem_converterMove hval ?_
        rw [converterMove, Part.mem_bind_iff]
        refine ⟨us, hus, ?_⟩
        rw [Part.mem_map_iff]
        exact ⟨Sum.inl x, by rw [hy]; exact h, rfl⟩
      rw [resolve_of_request (R := R) hreq]
      set o : Option Uni.{u} := answer R xs (encode X x) with ho
      have hmap : (c ++ [(Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u})]).map unlabel
          = c.map unlabel ++ [Sum.inr o] := by simp
      have hus' : us ∈ decodeList U (outerQueries
          ((c ++ [(Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u})]).map unlabel)) := by
        rw [hmap, outerQueries_concat_inr]; exact hus
      have hy' : (roundAnswers
            ((c ++ [(Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u})]).map unlabel)).map
            (fun w => w.bind decodeOption) = ys ++ [o.bind decodeOption] := by
        rw [hmap, roundAnswers_concat_inr, List.map_append, hy]
        rfl
      have hval' : (c ++ [(Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u})]).map unlabel
          ∈ dom (converterEngine X V ν) := by
        rw [hmap]
        refine (mem_dom_validate_concat (Or.inr hval) _).mpr ?_
        obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hrest.dom
        refine Part.dom_iff_mem.mpr ⟨converterAddress X V n, ?_⟩
        rw [converterMove, Part.mem_bind_iff]
        refine ⟨us, by rw [← hmap]; exact hus', ?_⟩
        rw [Part.mem_map_iff]
        refine ⟨n, ?_, rfl⟩
        rw [show (roundAnswers (c.map unlabel ++ [Sum.inr o])).map
            (fun w => w.bind (decodeOption (X := Y))) = ys ++ [o.bind decodeOption] from
          by rw [← hmap]; exact hy']
        exact hn
      obtain ⟨as, bs, hmem, hdom'⟩ := ih _ hval' hus' hy'
      refine ⟨o :: as, encode X x :: bs, ?_, ?_⟩
      · simpa using hmem
      · simpa using hdom'

/-- **One composite round**: an owned outer query `encode U u` is answered by
`encode V v` for the `v` the run reaches, and the state it leaves records that
one more outer query has been asked. -/
theorem mem_attachEngineFullyRound_converterEngine {i : Set Uni.{u}}
    {ν : List U × List (Option Y) →. X ⊕ V} {R : DDS Uni.{u} Uni.{u}}
    {st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}} {us₀ : List U} {u : U} {v : V}
    (hu : encode U u ∈ i)
    (hval : st.1.map unlabel = [] ∨ st.1.map unlabel ∈ dom (converterEngine X V ν))
    (hq : outerQueries (st.1.map unlabel) = us₀.map (encode U))
    (hrun : ConverterRunsTo ν R (us₀ ++ [u]) [] st.2 v) :
    ∃ st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
      (encode V v, st') ∈ attachEngineFullyRound i (converterEngine X V ν) R st (encode U u) ∧
        st'.1.map unlabel ∈ dom (converterEngine X V ν) ∧
        outerQueries (st'.1.map unlabel) = (us₀ ++ [u]).map (encode U) := by
  rw [attachEngineFullyRound_mem _ _ _ hu]
  set c : List (CIn Uni.{u} Uni.{u}) := st.1 ++ [Sum.inl (InLabel.outside, encode U u)] with hc
  have hcmap : c.map unlabel = st.1.map unlabel ++ [Sum.inl (encode U u)] := by simp [hc]
  have houter : outerQueries (c.map unlabel) = (us₀ ++ [u]).map (encode U) := by
    rw [hcmap, outerQueries_concat_inl, hq, List.map_append]
    rfl
  have hus : (us₀ ++ [u]) ∈ decodeList U (outerQueries (c.map unlabel)) := by
    rw [houter, decodeList_encode]
    exact Part.mem_some _
  have hy : (roundAnswers (c.map unlabel)).map
      (fun w => w.bind (decodeOption (X := Y))) = [] := by
    rw [hcmap, roundAnswers_concat_inl]
    rfl
  have hvalc : c.map unlabel ∈ dom (converterEngine X V ν) := by
    rw [hcmap]
    refine (mem_dom_validate_concat hval _).mpr ?_
    obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp hrun.dom
    refine Part.dom_iff_mem.mpr ⟨converterAddress X V n, ?_⟩
    rw [converterMove, Part.mem_bind_iff]
    refine ⟨us₀ ++ [u], by rw [← hcmap]; exact hus, ?_⟩
    rw [Part.mem_map_iff]
    refine ⟨n, ?_, rfl⟩
    rw [show (roundAnswers (st.1.map unlabel ++ [Sum.inl (encode U u)])).map
        (fun w => w.bind (decodeOption (X := Y))) = [] from by rw [← hcmap]; exact hy]
    exact hn
  obtain ⟨as, bs, hmem, hdom'⟩ := mem_resolve_converterEngine hrun c hvalc hus hy
  refine ⟨_, hmem, hdom', ?_⟩
  have hun : (c ++ as.map (fun o => (Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u}))).map
      unlabel = c.map unlabel ++ as.map Sum.inr := by simp
  rw [show ((c ++ as.map (fun o => (Sum.inr (InLabel.inside, o) : CIn Uni.{u} Uni.{u})),
      st.2 ++ bs) : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}).1 = _ from rfl, hun,
    outerQueries_append, outerQueries_map_inr, houter, List.append_nil]

/-- **The outer iteration**: a history function whose every round runs to
`g u`, whatever the resource history it starts from, drives the composite
through a whole outer interaction. -/
theorem mem_attachEngineFullyDrive_converterEngine {i : Set Uni.{u}}
    {ν : List U × List (Option Y) →. X ⊕ V} {R : DDS Uni.{u} Uni.{u}} {g : U → V}
    (hi : ∀ u : U, encode U u ∈ i)
    (hrun : ∀ (us : List U) (u : U) (xs : List Uni.{u}),
      ConverterRunsTo ν R (us ++ [u]) [] xs (g u)) (us : List U) :
    ∀ (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) (us₀ : List U),
      (st.1.map unlabel = [] ∨ st.1.map unlabel ∈ dom (converterEngine X V ν)) →
      outerQueries (st.1.map unlabel) = us₀.map (encode U) →
      ∃ st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u},
        (us.map (fun w => encode V (g w)), st') ∈
            attachEngineFullyDrive i (converterEngine X V ν) R st (us.map (encode U)) ∧
          (st'.1.map unlabel = [] ∨ st'.1.map unlabel ∈ dom (converterEngine X V ν)) ∧
          outerQueries (st'.1.map unlabel) = (us₀ ++ us).map (encode U) := by
  induction us with
  | nil =>
      intro st us₀ hval hq
      exact ⟨st, by simp [attachEngineFullyDrive], hval, by simpa using hq⟩
  | cons u rest ih =>
      intro st us₀ hval hq
      obtain ⟨st₁, hst₁, hdom₁, houter₁⟩ :=
        mem_attachEngineFullyRound_converterEngine (i := i) (hi u) hval hq (hrun us₀ u st.2)
      obtain ⟨st₂, hst₂, hval₂, houter₂⟩ := ih st₁ (us₀ ++ [u]) (Or.inr hdom₁) houter₁
      refine ⟨st₂, ?_, hval₂, by simpa using houter₂⟩
      rw [List.map_cons, attachEngineFullyDrive, Part.mem_bind_iff]
      exact ⟨(encode V (g u), st₁), hst₁,
        (Part.mem_map_iff _).mpr ⟨(rest.map (fun w => encode V (g w)), st₂), hst₂, rfl⟩⟩

/-- **A round adds no outer query**: the conversation a resolved round leaves
carries the outer queries it started with.  Proved by `PFun.fixInduction` on
CR18 Definition 3.9's inner resolution (printed p. 62): the stopping rule leaves
the conversation alone and the query rule appends an inner answer. -/
theorem outerQueries_resolve {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {R : DDS Uni.{u} Uni.{u}} {c c' : List (CIn Uni.{u} Uni.{u})}
    {xs xs' : List Uni.{u}} {v : Uni.{u}}
    (h : (v, (c', xs')) ∈ resolve (ofEngine E) R (c, xs)) :
    outerQueries (c'.map unlabel) = outerQueries (c.map unlabel) := by
  refine PFun.fixInduction
    (C := fun st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u} =>
      outerQueries (c'.map unlabel) = outerQueries (st.1.map unlabel)) h ?_
  rintro ⟨ca, la⟩ hb ih
  rcases PFun.mem_fix_iff.mp hb with hstop | ⟨a'', hstep, -⟩
  · rw [mem_connStep_iff] at hstop
    rcases hstop with ⟨w, -, heq⟩ | ⟨x, -, heq⟩
    · have hc : c' = ca := congrArg (fun p => p.2.1) (Sum.inl_injective heq)
      rw [hc]
    · exact absurd heq (by simp)
  · rw [mem_connStep_iff] at hstep
    rcases hstep with ⟨w, -, heq⟩ | ⟨x, hx, heq⟩
    · exact absurd heq (by simp)
    · have hmem : Sum.inr a'' ∈ Converter.DDC.connStep (ofEngine E) R (ca, la) := by
        rw [mem_connStep_iff]; exact Or.inr ⟨x, hx, heq⟩
      have ha : a''.1 = ca ++ [Sum.inr (InLabel.inside, answer R la x)] :=
        congrArg (fun p => p.1) (Sum.inr_injective heq)
      rw [ih a'' hmem, ha]
      simp [outerQueries]

/-- **Whole-face queries are read at `U`**: every outer query a driven
interaction accepts carries the outer alphabet's address, because the round it
opened had to decode the outer history to move at all.  The converse half of
the realization equation's domain. -/
theorem tag_of_mem_attachEngineFullyDrive_converterEngine
    {ν : List U × List (Option Y) →. X ⊕ V} {R : DDS Uni.{u} Uni.{u}} :
    ∀ (qs : List Uni.{u}) (st st' : List (CIn Uni.{u} Uni.{u}) × List Uni.{u})
      (vs : List Uni.{u}),
      (vs, st') ∈ attachEngineFullyDrive (Set.univ : Set Uni.{u})
        (converterEngine X V ν) R st qs → ∀ q ∈ qs, q.1 = U := by
  intro qs
  induction qs with
  | nil => intro _ _ _ _ q hq; exact absurd hq (by simp)
  | cons q rest ih =>
      intro st st' vs hdrive q' hq'
      rw [attachEngineFullyDrive, Part.mem_bind_iff] at hdrive
      obtain ⟨r, hr, hrest⟩ := hdrive
      rw [attachEngineFullyRound_mem _ _ _ (Set.mem_univ q)] at hr
      have hdom : ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)
          ∈ dom (converterEngine X V ν) :=
        mem_dom_of_resolve_dom _ _ _ _ (Part.dom_iff_mem.mpr ⟨r, hr⟩)
      have hmv : (converterMove X V ν (st.1.map unlabel ++ [Sum.inl q])).Dom := by
        have := hdom.2 _ (List.prefix_refl _) hdom.1
        simpa using this
      have hdec : (decodeList U (outerQueries (st.1.map unlabel) ++ [q])).Dom := by
        have := (Part.bind_dom.mp hmv).fst
        rwa [outerQueries_append, outerQueries] at this
      rcases List.mem_cons.mp hq' with rfl | hq''
      · exact decodeList_dom_mem hdec q' (by simp)
      · rw [Part.mem_map_iff] at hrest
        obtain ⟨rr, hrr, -⟩ := hrest
        exact ih r.2 rr.2 rr.1 hrr q' hq''

/-- **The realization equation, once and for all.**  A history function whose
every round runs to `g u` — whatever the resource history the round starts from
— attached at the whole face, *is* the on-ramped stateless system `g`.

This is what an application needs before any indistinguishability statement
about its converter can mean anything: it says the converter computes what it
was written to compute, against the resource it was written for.  The two
directions are exactly the two halves above: the drive lemma builds the run for
a decodable outer history, and `tag_of_mem_attachEngineFullyDrive_converterEngine`
shows nothing else is accepted, because the engine has to decode the outer
history before it can move (CR18 Definition 3.9's round, printed p. 62).

Whole-face is the scope, and it is CR18 Definition 3.9's own application: at a
*proper* interface a query outside it reaches the resource verbatim
(`attachEngineFullyRound_not_mem`), so the resource's own alphabet stays
visible and the composite is not the on-ramp of anything. -/
theorem attachEngineFully_converterEngine_univ {ν : List U × List (Option Y) →. X ⊕ V}
    {R : DDS Uni.{u} Uni.{u}} {g : U → V}
    (hrun : ∀ (us : List U) (u : U) (xs : List Uni.{u}),
      ConverterRunsTo ν R (us ++ [u]) [] xs (g u)) :
    attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X V ν) R
      = ofTyped (functionEvaluator g) := by
  have hval : ∀ (ws : List U) (hne : ws ≠ []),
      encode V (g (ws.getLast hne)) ∈
        (attachEngineFully (Set.univ : Set Uni.{u}) (converterEngine X V ν) R).1
          (ws.map (encode U)) := by
    intro ws hne
    obtain ⟨st', hst', -, -⟩ :=
      mem_attachEngineFullyDrive_converterEngine (i := Set.univ)
        (fun _ => Set.mem_univ _) hrun ws ([], []) [] (Or.inl rfl) rfl
    refine (mem_attachEngineFullyRaw_iff _ _).mpr ⟨_, hst', ?_⟩
    rw [List.getLast?_map, List.getLast?_eq_some_getLast hne]
    rfl
  have hshape : ∀ us : List Uni.{u},
      ((ofTyped (functionEvaluator g)).1 us).Dom →
      ∃ ws : List U, ∃ hne : ws ≠ [], us = ws.map (encode U) := by
    intro us hdom
    have hne : us ≠ [] := hdom.1
    have hraw : (ofTypedRaw (functionEvaluator g) us).Dom :=
      hdom.2 us (List.prefix_refl _) hdom.1
    have hdec : (decodeList U us).Dom := (Part.bind_dom.mp (Part.dom_iff_mem.mpr
      (by obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hraw
          obtain ⟨w, hw, -⟩ := (Part.mem_map_iff _).mp hy
          exact ⟨w, hw⟩))).fst
    refine ⟨(decodeList U us).get hdec, ?_, decodeList_mem_eq (Part.get_mem hdec)⟩
    intro hnil
    exact hne (by rw [decodeList_mem_eq (Part.get_mem hdec), hnil]; rfl)
  refine Subtype.ext (funext fun us => Part.ext' ?_ ?_)
  · constructor
    · intro hdom
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp hdom
      obtain ⟨r, hr, hlast⟩ := (mem_attachEngineFullyRaw_iff us v).mp hv
      have htag : ∀ q ∈ us, q.1 = U :=
        tag_of_mem_attachEngineFullyDrive_converterEngine us ([], []) r.2 r.1 (by simpa using hr)
      have hdec : (decodeList U us).Dom := decodeList_dom_of_forall_tag htag
      have hus : us = ((decodeList U us).get hdec).map (encode U) :=
        decodeList_mem_eq (Part.get_mem hdec)
      have hne : us ≠ [] := by
        intro hnil
        have hlen : r.1.length = us.length := attachEngineFullyDrive_length ([], []) us hr
        rw [hnil] at hlen
        rw [List.eq_nil_of_length_eq_zero hlen] at hlast
        exact absurd hlast (by simp)
      have hwne : (decodeList U us).get hdec ≠ [] := by
        intro hnil; exact hne (by rw [hus, hnil]; rfl)
      show us ∈ dom (ofTyped (functionEvaluator g))
      rw [hus]
      exact (mem_dom_ofTyped_encode hwne).mpr (by rw [dom_functionEvaluator]; exact hwne)
    · intro hdom
      obtain ⟨ws, hne, rfl⟩ := hshape us hdom
      exact Part.dom_iff_mem.mpr ⟨_, hval ws hne⟩
  · intro h₁ h₂
    obtain ⟨ws, hne, rfl⟩ := hshape us h₂
    have hS : ws ∈ dom (functionEvaluator g) := by rw [dom_functionEvaluator]; exact hne
    rw [Part.get_eq_of_mem (hval ws hne) h₁]
    show _ = output (ofTyped (functionEvaluator g)) (ws.map (encode U)) h₂
    rw [output_ofTyped_encode hS h₂, output_functionEvaluator]

/-! ## The membership -/

end

end System

noncomputable section

universe u

/-- **The entry point.**  A history function that always reacts and whose
rounds are boundedly long is a member of the metric-facing `Σ`, attached at any
interface: `attachAt` of `converterEngine`, through
`attachAt_mem_converterMonoidAt` (PRIMITIVE REGISTRY, ATTACHMENT).  No new
primitive, no widening; the whole content is that the two conditions on the
history function *are* `System.InnerTotal` and
`System.AnswersWithinUniformBudget` read through the crossing.

This is the only converter notion an application *reasons with*: the element
of `Σ` is what every endpoint speaks about.  The history function is how the
application writes its converter down, and it is named in statements only by
the receipts this entry point consumes — in the CBC-MAC lane exactly
`cbcRound_innerTotal`, `cbcRound_requestsBounded_of_length_le` and
`cbcRound_requestsBounded`, with the engine named once more in
`cbcConverter_requestsWithin`.  No endpoint mentions either. -/
theorem converterEngine_mem_converterMonoidAt {U V X Y : Type u}
    (i : Set Uni.{u}) (ν : List U × List (Option Y) →. X ⊕ V) {K : ℕ}
    (hIT : System.ConverterInnerTotal ν)
    (hK : System.ConverterRequestsBounded ν K) :
    attachAt i (System.converterEngine X V ν) ∈ converterMonoidAt.{u} :=
  attachAt_mem_converterMonoidAt i (System.innerTotal_converterEngine hIT)
    (System.answersWithinUniformBudget_converterEngine hK)

end

end RandomSystems

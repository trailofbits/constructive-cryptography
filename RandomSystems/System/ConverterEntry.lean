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
once: `protocolEngine` builds the attachment engine, the three receipts are
discharged from two conditions on the history function, and
`protocolEngine_mem_converterMonoidAt` is the membership.

## The two conditions, and why they are the right two

They are exactly the hypotheses `attachAt_mem_converterMonoidAt` consumes,
read back through the crossing:

* `ProtocolInnerTotal` — Ruling R2's inner-facing totality: having asked, the
  converter reacts to whatever comes back, a refusal included.  CR18 Definition
  3.8's own input-alphabet clause demands the opposite; the replacement is the
  standing repository extension (`System.InnerTotal`, `ConnectFullyDefined.lean`).
* `ProtocolRequestsBounded ν K` — Definition 3.8's finite-bound clause,
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
coexist: `ProtocolRequestsBounded.answersWithin` shows the round-local
condition implies the cumulative one (at `K + 1`, and the offset is sharp),
and `exists_answersWithin_not_protocolRequestsBounded` shows the converse
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
def ProtocolInnerTotal (ν : List U × List (Option Y) →. X ⊕ V) : Prop :=
  ∀ (us : List U) (ys : List (Option Y)) (x : X), Sum.inl x ∈ ν (us, ys) →
    ∀ o : Option Y, (ν (us, ys ++ [o])).Dom

/-- **CR18 Definition 3.8's finite request bound** (printed p. 62), at the
history-function presentation: a round asks at most `K` questions. -/
def ProtocolRequestsBounded (ν : List U × List (Option Y) →. X ⊕ V) (K : ℕ) :
    Prop :=
  ∀ (us : List U) (ys : List (Option Y)) (x : X), Sum.inl x ∈ ν (us, ys) →
    ys.length < K

/-! ### The two readings of Definition 3.8's bound, related

`ProtocolRequestsBounded` and the landed `Converter.AnswersWithin` are two
readings of one clause on one type (`Converter.ProtocolFn` is an `abbrev` for
the type used here).  Leaving them unbridged would let a future application
prove one and cite the other, so both directions are settled here.
-/

/-- **The round-local bound implies Definition 3.8's streak bound** (printed
p. 62), at every pair — reachability is not used.  If a query is only ever
issued at fewer than `K` answers, then no `K + 1` consecutive queries open
anywhere: the `K`-th extension already carries `K` answers. -/
theorem ProtocolRequestsBounded.answersWithinAt
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ProtocolRequestsBounded ν K) (p : List U × List (Option Y)) :
    Converter.AnswersWithinAt ν p (K + 1) := by
  intro ext hlen hall
  obtain ⟨x, hx⟩ := hall K (by omega)
  have := hK p.1 _ x hx
  rw [List.length_append, List.length_take] at this
  omega

/-- **The bridge**: the entry point's round-local receipt discharges the
landed converter surface's uniform reading of CR18 Definition 3.8's clause
(printed p. 62), at `K + 1`.

The offset is sharp, not slack: `ProtocolRequestsBounded ν K` admits a round
of exactly `K` queries — issued at `0, …, K-1` answers — and `([u], [])` is
reachable, so `Converter.AnswersWithin ν K` genuinely fails for such a `ν`.
(That sharpness is argued, not landed: no witness for it is in the tree.  The
non-interchangeability below *is* landed.) -/
theorem ProtocolRequestsBounded.answersWithin
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ProtocolRequestsBounded ν K) : Converter.AnswersWithin ν (K + 1) :=
  fun p _ => hK.answersWithinAt p

/-- **The converse fails, so the two readings are not interchangeable.**  The
streak bound constrains how many queries run *back to back*; the round-local
bound constrains *where in the answer list* a query may be issued at all.  A
history function that queries exactly once, but only after five answers, has
no streak of two and no round-local bound below six. -/
theorem exists_answersWithin_not_protocolRequestsBounded :
    ∃ ν : List Unit × List (Option Unit) →. Unit ⊕ Unit,
      Converter.AnswersWithin ν 2 ∧ ¬ ProtocolRequestsBounded ν 2 := by
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
def protocolAddress (X V : Type u) : X ⊕ V → Uni.{u} ⊕ Uni.{u}
  | Sum.inl x => Sum.inr (encode X x)
  | Sum.inr v => Sum.inl (encode V v)

@[simp] theorem protocolAddress_inl (x : X) :
    protocolAddress X V (Sum.inl x) = Sum.inr (encode X x) := rfl

@[simp] theorem protocolAddress_inr (v : V) :
    protocolAddress X V (Sum.inr v) = Sum.inl (encode V v) := rfl

/-- The engine's move: decode the outer history at `U`, read the round's
answers at `Y`, consult the history function, and address the move. -/
def protocolMove (X V : Type u) (ν : List U × List (Option Y) →. X ⊕ V)
    (l : List (Uni.{u} ⊕ Option Uni.{u})) : Part (Uni.{u} ⊕ Uni.{u}) :=
  (decodeList U (outerQueries l)).bind fun us =>
    (ν (us, (roundAnswers l).map fun o => o.bind decodeOption)).map
      (protocolAddress X V)

/-- **The typed converter as an attachment engine.**  CR18 Definition 3.8's
object (printed p. 62) at the universal alphabet, cut down to the histories all
of whose prefixes the converter accepts (`System.validate`, as `ofTyped`
does). -/
def protocolEngine (X V : Type u) (ν : List U × List (Option Y) →. X ⊕ V) :
    DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) :=
  validate (protocolMove X V ν)

theorem mem_protocolMove_of_mem_protocolEngine
    {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}}
    (h : m ∈ (protocolEngine X V ν).1 l) : m ∈ protocolMove X V ν l := by
  obtain ⟨hd, hm⟩ := h
  exact ⟨hd.2 l (List.prefix_refl l) hd.1, hm⟩

theorem mem_dom_protocolEngine {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} (h : l ∈ dom (protocolEngine X V ν)) :
    l ≠ [] ∧ ∀ l', l' <+: l → l' ≠ [] → (protocolMove X V ν l').Dom := h

/-- A move the engine makes comes from a move of the history function. -/
theorem exists_mem_of_mem_protocolMove {ν : List U × List (Option Y) →. X ⊕ V}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}}
    (h : m ∈ protocolMove X V ν l) :
    ∃ us ∈ decodeList U (outerQueries l),
      ∃ n ∈ ν (us, (roundAnswers l).map fun o => o.bind decodeOption),
        m = protocolAddress X V n := by
  obtain ⟨us, hus, hrest⟩ := Part.mem_bind_iff.mp h
  obtain ⟨n, hn, hm⟩ := (Part.mem_map_iff _).mp hrest
  exact ⟨us, hus, n, hn, hm.symm⟩

/-! ## The three receipts -/

/-- **The engine reaches only into `i`**: every request it emits is a query
addressed at the inner alphabet, so an interface containing that alphabet's
copy contains every request. -/
theorem requestsWithin_protocolEngine {ν : List U × List (Option Y) →. X ⊕ V}
    (i : Set Uni.{u}) (hi : ∀ x : X, encode X x ∈ i) :
    RequestsWithin i (protocolEngine X V ν) := by
  intro l x hx
  obtain ⟨us, -, n, -, hm⟩ :=
    exists_mem_of_mem_protocolMove (mem_protocolMove_of_mem_protocolEngine hx)
  rcases n with x' | v
  · have : x = encode X x' := by simpa using hm
    exact this ▸ hi x'
  · exact absurd hm (by simp)

/-- **Inner-facing totality transports** (Ruling R2): the engine reacts to
whatever the completion returns because the history function does. -/
theorem innerTotal_protocolEngine {ν : List U × List (Option Y) →. X ⊕ V}
    (hIT : ProtocolInnerTotal ν) : InnerTotal (protocolEngine X V ν) := by
  intro l x hx o
  obtain ⟨hne, hpre⟩ := hx.1
  obtain ⟨us, hus, n, hn, hm⟩ :=
    exists_mem_of_mem_protocolMove (mem_protocolMove_of_mem_protocolEngine hx)
  have hreq : ∃ x' : X, n = Sum.inl x' := by
    rcases n with x' | v
    · exact ⟨x', rfl⟩
    · exact absurd hm (by simp)
  obtain ⟨x', rfl⟩ := hreq
  refine ⟨by simp, fun l' hl' hne' => ?_⟩
  rcases List.prefix_concat_iff.mp hl' with rfl | hl''
  · refine Part.dom_iff_mem.mpr ?_
    rw [protocolMove]
    have hdom : (ν (us, ((roundAnswers l).map fun o' => o'.bind decodeOption)
        ++ [o.bind decodeOption])).Dom :=
      hIT us _ x' hn (o.bind decodeOption)
    obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hdom
    refine ⟨protocolAddress X V w, ?_⟩
    rw [Part.mem_bind_iff]
    refine ⟨us, by rwa [outerQueries_concat_inr], ?_⟩
    rw [Part.mem_map_iff]
    exact ⟨w, by rwa [roundAnswers_concat_inr, List.map_append], rfl⟩
  · exact hpre l' hl'' hne'

/-- The round budget as a measure on engine histories: the requests a round
may still make. -/
def protocolBudget (K : ℕ) (l : List (Uni.{u} ⊕ Option Uni.{u})) : ℕ :=
  K - (roundAnswers l).length

/-- **CR18 Definition 3.8's request bound transports** (printed p. 62), and it
is *uniform*: the measure is bounded by `K` at every engine history because it
counts within one round. -/
theorem answersWithinUniformBudget_protocolEngine
    {ν : List U × List (Option Y) →. X ⊕ V} {K : ℕ}
    (hK : ProtocolRequestsBounded ν K) :
    AnswersWithinUniformBudget (protocolEngine X V ν) := by
  refine ⟨protocolBudget K, K, ?_, fun l => Nat.sub_le _ _⟩
  intro l x hx o
  obtain ⟨us, -, n, hn, hm⟩ :=
    exists_mem_of_mem_protocolMove (mem_protocolMove_of_mem_protocolEngine hx)
  have hreq : ∃ x' : X, n = Sum.inl x' := by
    rcases n with x' | v
    · exact ⟨x', rfl⟩
    · exact absurd hm (by simp)
  obtain ⟨x', rfl⟩ := hreq
  have hlt : ((roundAnswers l).map fun o' => o'.bind (decodeOption (X := Y))).length < K :=
    hK us _ x' hn
  rw [List.length_map] at hlt
  simp only [protocolBudget, roundAnswers_concat_inr, List.length_append,
    List.length_singleton]
  omega

/-! ## The membership -/

end

end System

noncomputable section

universe u

/-- **The entry point.**  A history function that always reacts and whose
rounds are boundedly long is a member of the metric-facing `Σ`, attached at any
interface: `attachAt` of `protocolEngine`, through
`attachAt_mem_converterMonoidAt` (PRIMITIVE REGISTRY, ATTACHMENT).  No new
primitive, no widening; the whole content is that the two conditions on the
history function *are* `System.InnerTotal` and
`System.AnswersWithinUniformBudget` read through the crossing.

This is the only converter notion an application *reasons with*: the element
of `Σ` is what every endpoint speaks about.  The history function is how the
application writes its protocol down, and it is named in statements only by
the receipts this entry point consumes — in the CBC-MAC lane exactly
`cbcRound_innerTotal`, `cbcRound_requestsBounded_of_length_le` and
`cbcRound_requestsBounded`, with the engine named once more in
`cbcProtocol_requestsWithin`.  No endpoint mentions either. -/
theorem protocolEngine_mem_converterMonoidAt {U V X Y : Type u}
    (i : Set Uni.{u}) (ν : List U × List (Option Y) →. X ⊕ V) {K : ℕ}
    (hIT : System.ProtocolInnerTotal ν)
    (hK : System.ProtocolRequestsBounded ν K) :
    attachAt i (System.protocolEngine X V ν) ∈ converterMonoidAt.{u} :=
  attachAt_mem_converterMonoidAt i (System.innerTotal_protocolEngine hIT)
    (System.answersWithinUniformBudget_protocolEngine hK)

end

end RandomSystems

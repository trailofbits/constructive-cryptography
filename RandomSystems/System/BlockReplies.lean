/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import RandomSystems.System.AttachEngineFully

/-!
# CR18 Definition 4.20's reply-blocking converter, as an attachment engine

PAPER-FAITHFUL

Cachin–Renner(–Maurer), *Lecture Notes on Cryptography*, **Definition 4.20,
printed p. 109** (read on the rendered page): "For a game `S` we define `bS` as
the game system `S` for which the outputs `Yᵢ` are blocked, i.e., `b` is the
simple converter that is transparent for the queries `Xᵢ` but blocks the
replies `Yᵢ`."

## `b` is reply-side; the landed `block`/`filterPhi` family is query-side

The two are different converters and neither is the other.  A *domain filter*
(`filterPhi`, CR18 **§3.4.3, unnumbered prose, printed p. 62** — the widened
generator family of `converterMonoidAt`; Definition 3.10 is only the `[q]`
notation) decides on the query: a filtered query never reaches the
resource, and the composite refuses.  Definition 4.20's `b` forwards **every**
query verbatim — it is "transparent for the queries" — and interferes only on
the way back, where it discards whatever the resource returned and answers a
fixed symbol.  Reading `b` as a query-side block is what made the blind form
look unavailable; it is an ordinary member of the ratified attachment family.

Concretely, `b` is an engine (`System.DDS (Uni ⊕ Option Uni) (Uni ⊕ Uni)`) with
a two-move round:

* it has just been handed an outer query `q` (the history ends in `Sum.inl q`):
  emit the request `Sum.inr q` — forward it inward, unchanged;
* it has just been handed an inner answer (the history ends in `Sum.inr o`,
  `o : Option Uni`, `none` included): emit `Sum.inl c` — answer the fixed
  constant outward, whatever came back.

That engine is `System.InnerTotal` (it reacts to every inner answer, refusal
included — Ruling R2) and answers within a *uniform* budget of one request per
round (CR18 Definition 3.8's finite-bound clause), so
`attachAt i (blockReplies i c)` is a member of the metric-facing `Σ`
(`blockReplies_mem_converterMonoidAt`) — no new primitive, no new object stack
(PHI-SPEC R11(a)).  Because the engine always answers, the composite never
refuses: nothing about the resource, not even its refusal pattern, reaches the
environment.

## What the composite is

`attachEngineFully_blockReplies_univ` computes it: at the whole face the
reply-erased resource is the *constant system* `functionEvaluator (fun _ => c)`
— the resource has been erased completely, uniformly in `R`.  That equation is
the formal content of Definition 4.20's own gloss, "to win game `bS` means to
win game `S` blindly, without seeing the outputs" (printed p. 109), and it is
what `Technique/BlindWinning.lean` turns into the identification of the two
renderings of "blind".

The interface-local statement `attachEngineFullyRound_blockReplies` is the same
round equation at a general `i`, kept because `attachAt i` is the primitive and
`Set.univ` is a case of it (PRIMITIVE REGISTRY, ATTACHMENT).

## SCOPE: the erasure is a whole-face fact

Everything above is stated at `i = Set.univ`, and that is where it holds.  At a
**proper** interface `i` the composite is *not* the constant system: a query
outside `i` never reaches the engine at all — it is passed to the resource
verbatim (`attachEngineFullyRound_not_mem`), refusal included — so outside `i`
the resource's domain, and with it its refusal pattern, remains observable to
the environment.  What `attachEngineFully_blockReplies_univ` says is that
erasure at the **whole face** leaves nothing; it does not say that attaching
`b` at some sub-interface blinds an environment.  CR18 Definition 4.20's `bS`
is the whole-game object, so the whole-face statement is the one the source
needs, but any downstream reading of "blocking replies blinds" must carry the
`Set.univ` scope with it.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical
open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve)

universe u

/-! ## The engine -/

/-- The move CR18 Definition 4.20's `b` (printed p. 109) makes at a converter
history: forward
an outer query of the interface inward, and answer the constant outward to
anything else — in particular to *any* inner reply, `⊥` included, which is
"blocks the replies `Yᵢ`".

A query outside `i` is answered outright rather than forwarded, which is what
makes the engine's requests all land in `i` (`requestsWithin_blockReplies`).
The composite never consults the engine there (`attachEngineFullyRound`
dispatches on ownership), so the branch is unobservable; it is written this way
so that the engine is a legal citizen of the interface-indexed family. -/
def blockRepliesMove (i : Set Uni.{u}) (c : Uni.{u})
    (l : List (Uni.{u} ⊕ Option Uni.{u})) : Uni.{u} ⊕ Uni.{u} :=
  match l.getLast? with
  | some (Sum.inl q) => if q ∈ i then Sum.inr q else Sum.inl c
  | _ => Sum.inl c

/-- **CR18 Definition 4.20's `b`** (printed p. 109), as an attachment engine at
the interface `i`: transparent for the queries, blocking for the replies.  The
constant `c` is the fixed symbol the blocked reply is replaced by; Definition
4.20 leaves it unnamed because a blocked output carries no information, and
every statement below is uniform in it. -/
def blockReplies (i : Set Uni.{u}) (c : Uni.{u}) :
    DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}) :=
  ⟨fun l => (⟨l ≠ [], fun _ => blockRepliesMove i c l⟩ : Part (Uni.{u} ⊕ Uni.{u})),
    ⟨by simp, by
      intro _ _ _ hne _
      exact hne⟩⟩

@[simp] theorem dom_blockReplies (i : Set Uni.{u}) (c : Uni.{u}) :
    dom (blockReplies i c) = {l : List (Uni.{u} ⊕ Option Uni.{u}) | l ≠ []} := by
  ext l
  rfl

theorem mem_blockReplies_iff {i : Set Uni.{u}} {c : Uni.{u}}
    {l : List (Uni.{u} ⊕ Option Uni.{u})} {m : Uni.{u} ⊕ Uni.{u}} :
    m ∈ (blockReplies i c).1 l ↔ l ≠ [] ∧ m = blockRepliesMove i c l := by
  constructor
  · rintro ⟨hne, hm⟩
    exact ⟨hne, hm.symm⟩
  · rintro ⟨hne, rfl⟩
    exact ⟨hne, rfl⟩

/-- The forwarding move, spelled: after an outer query of the interface the
engine emits that same query inward. -/
theorem blockRepliesMove_query {i : Set Uni.{u}} {c q : Uni.{u}}
    (l : List (Uni.{u} ⊕ Option Uni.{u})) (hq : q ∈ i) :
    blockRepliesMove i c (l ++ [Sum.inl q]) = Sum.inr q := by
  simp [blockRepliesMove, hq]

/-- The blocking move, spelled: after **any** inner reply — an answer or a
refusal — the engine emits the constant outward. -/
theorem blockRepliesMove_reply (i : Set Uni.{u}) (c : Uni.{u})
    (l : List (Uni.{u} ⊕ Option Uni.{u})) (o : Option Uni.{u}) :
    blockRepliesMove i c (l ++ [Sum.inr o]) = Sum.inl c := by
  simp [blockRepliesMove]

/-! ## The three engine-class receipts -/

/-- The engine reaches only into `i`: its single request is the outer query it
was handed, and it forwards only queries of `i`. -/
theorem requestsWithin_blockReplies (i : Set Uni.{u}) (c : Uni.{u}) :
    RequestsWithin i (blockReplies i c) := by
  intro l x hx
  obtain ⟨-, hx⟩ := mem_blockReplies_iff.mp hx
  unfold blockRepliesMove at hx
  rcases hl : l.getLast? with _ | (q | o) <;> rw [hl] at hx <;> simp at hx
  by_cases hq : q ∈ i
  · rw [if_pos hq] at hx
    have : x = q := by simpa using hx
    exact this ▸ hq
  · rw [if_neg hq] at hx
    exact absurd hx (by simp)

/-- **Inner-facing totality** (Ruling R2): the blocked reply is answered
outward whatever came back, refusal included.  This is the clause that makes
`b` erase the resource rather than expose its domain. -/
theorem innerTotal_blockReplies (i : Set Uni.{u}) (c : Uni.{u}) :
    InnerTotal (blockReplies i c) := by
  intro l x _ o
  rw [dom_blockReplies]
  exact List.append_ne_nil_of_right_ne_nil l (by simp)

/-- The budget: at most one request stands between the engine and its outer
answer, uniformly over converter histories — CR18 Definition 3.8's finite-bound
clause (printed p. 62) at `K = 1`. -/
def blockRepliesBudget (l : List (Uni.{u} ⊕ Option Uni.{u})) : ℕ :=
  match l.getLast? with
  | some (Sum.inl _) => 1
  | _ => 0

theorem answersWithinUniformBudget_blockReplies (i : Set Uni.{u}) (c : Uni.{u}) :
    AnswersWithinUniformBudget (blockReplies i c) := by
  refine ⟨blockRepliesBudget, 1, ?_, ?_⟩
  · intro l x hx o
    obtain ⟨-, hx⟩ := mem_blockReplies_iff.mp hx
    have hlast : ∃ q, l.getLast? = some (Sum.inl q) := by
      unfold blockRepliesMove at hx
      rcases hl : l.getLast? with _ | (q | o') <;> rw [hl] at hx <;> simp at hx
      exact ⟨q, rfl⟩
    obtain ⟨q, hq⟩ := hlast
    have h1 : blockRepliesBudget l = 1 := by simp [blockRepliesBudget, hq]
    have h2 : blockRepliesBudget (l ++ [Sum.inr o]) = 0 := by
      simp [blockRepliesBudget]
    rw [h1, h2]
    exact Nat.zero_lt_one
  · intro l
    unfold blockRepliesBudget
    rcases l.getLast? with _ | (q | o) <;> simp

/-! ## The round, and the erasure -/

variable {i : Set Uni.{u}} {c : Uni.{u}} {R : DDS Uni.{u} Uni.{u}}

/-- **One reply-erased round**: an owned query is forwarded inward, the
resource's reply (or refusal) is read and discarded, and the constant is
answered outward.  The state advances by the two engine moves and the one
resource query, so nothing is lost for later rounds — the erasure is of the
*outer* view only. -/
theorem attachEngineFullyRound_blockReplies
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) {q : Uni.{u}} (hq : q ∈ i) :
    attachEngineFullyRound i (blockReplies i c) R st q =
      Part.some (c,
        (st.1 ++ [Sum.inl (InLabel.outside, q)]
            ++ [Sum.inr (InLabel.inside, answer R st.2 q)], st.2 ++ [q])) := by
  rw [attachEngineFullyRound_mem _ _ _ hq]
  have hreq : Sum.inr q ∈ (blockReplies i c).1
      ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel) := by
    refine mem_blockReplies_iff.mpr ⟨by simp, ?_⟩
    rw [List.map_append]
    exact (blockRepliesMove_query _ hq).symm
  rw [resolve_of_request (R := R) hreq]
  refine Part.eq_some_iff.mpr ?_
  refine mem_resolve_of_answer (R := R) ?_
  refine mem_blockReplies_iff.mpr ⟨by simp, ?_⟩
  rw [List.map_append]
  exact (blockRepliesMove_reply i c _ (answer R st.2 q)).symm

/-- The outer iteration of the reply-erased composite is total, and every round
returns the same constant. -/
theorem attachEngineFullyDrive_blockReplies_univ
    (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}) (us : List Uni.{u}) :
    ∃ st', (List.replicate us.length c, st') ∈
      attachEngineFullyDrive (Set.univ : Set Uni.{u}) (blockReplies Set.univ c) R st us := by
  induction us generalizing st with
  | nil => exact ⟨st, by simp [attachEngineFullyDrive]⟩
  | cons q rest ih =>
      obtain ⟨st', hst'⟩ := ih
        (st.1 ++ [Sum.inl (InLabel.outside, q)]
            ++ [Sum.inr (InLabel.inside, answer R st.2 q)], st.2 ++ [q])
      refine ⟨st', ?_⟩
      rw [attachEngineFullyDrive, Part.mem_bind_iff]
      refine ⟨(c, (st.1 ++ [Sum.inl (InLabel.outside, q)]
            ++ [Sum.inr (InLabel.inside, answer R st.2 q)], st.2 ++ [q])), ?_, ?_⟩
      · rw [attachEngineFullyRound_blockReplies (R := R) st (Set.mem_univ q)]
        exact Part.mem_some _
      · refine (Part.mem_map_iff _).mpr
          ⟨(List.replicate rest.length c, st'), hst', ?_⟩
        simp [List.replicate_succ]

/-- **The reply-eraser erases the resource** — CR18 Definition 4.20 at the
whole face, computed.

`b` applied to *any* resource is the constant system: the outer view of
`attachEngineFully Set.univ (blockReplies Set.univ c) R` does not depend on `R`
at all.  This is the precise sense of Definition 4.20's gloss "to win game `bS`
means to win game `S` blindly, without seeing the outputs" (printed p. 109) —
and, on this carrier, it says more than the source needs to: since the engine
answers even a refusal, not even `R`'s *domain* survives the erasure, so the
Ruling R2 observability of `⊥` costs nothing here. -/
theorem attachEngineFully_blockReplies_univ (c : Uni.{u}) (R : DDS Uni.{u} Uni.{u}) :
    attachEngineFully (Set.univ : Set Uni.{u}) (blockReplies Set.univ c) R
      = functionEvaluator (fun _ : Uni.{u} => c) := by
  have hlast : ∀ n : ℕ, n ≠ 0 →
      (List.replicate n c).getLast? = some c := by
    intro n hn
    cases n with
    | zero => exact absurd rfl hn
    | succ m =>
        induction m with
        | zero => simp
        | succ k _ => rw [List.replicate_succ']; simp
  have hval : ∀ us : List Uni.{u}, us ≠ [] →
      c ∈ (attachEngineFully (Set.univ : Set Uni.{u}) (blockReplies Set.univ c) R).1 us := by
    intro us hne
    obtain ⟨st', hst'⟩ :=
      attachEngineFullyDrive_blockReplies_univ (R := R) (c := c) ([], []) us
    exact (mem_attachEngineFullyRaw_iff us c).mpr
      ⟨_, hst', hlast us.length (by simpa using hne)⟩
  refine Subtype.ext (funext fun us => Part.ext' ?_ ?_)
  · constructor
    · intro hmem
      rcases eq_or_ne us [] with rfl | hne
      · exact absurd hmem (by
          simp [attachEngineFully, attachEngineFullyRaw, attachEngineFullyDrive])
      · exact hne
    · intro hne
      exact Part.dom_iff_mem.mpr ⟨c, hval us hne⟩
  · intro _ h₂
    have hne : us ≠ [] := h₂
    have hval' : c ∈ (functionEvaluator (fun _ : Uni.{u} => c)).1 us := ⟨hne, rfl⟩
    rw [Part.get_eq_of_mem (hval us hne), Part.get_eq_of_mem hval']

end

end System

/-! ## The reply-eraser at the Φ level -/

noncomputable section

open Probability (Distribution)

universe u

/-- **CR18 Definition 4.20's `b` is a member of the metric-facing `Σ`**
(printed p. 109).  It is an attachment of an inner-total engine with CR18
Definition 3.8's *uniform* request bound (printed p. 62), which is exactly the
first generator family of
`converterMonoidAt` (PRIMITIVE REGISTRY, ATTACHMENT).  Nothing had to be
widened, and no new primitive enters: the reply-eraser is an ordinary
converter, and the F-8 escalation rested on reading it as a query-side block. -/
theorem blockReplies_mem_converterMonoidAt (i : Set Uni.{u}) (c : Uni.{u}) :
    attachAt i (System.blockReplies i c) ∈ converterMonoidAt.{u} :=
  attachAt_mem_converterMonoidAt i (System.innerTotal_blockReplies i c)
    (System.answersWithinUniformBudget_blockReplies i c)

/-- The same membership in the weaker-budget monoid, for callers that live
there (`converterMonoidAt_le_converterMonoidAtWeakBudget` also gives it). -/
theorem blockReplies_mem_converterMonoidAtWeakBudget (i : Set Uni.{u}) (c : Uni.{u}) :
    attachAt i (System.blockReplies i c) ∈ converterMonoidAtWeakBudget.{u} :=
  converterMonoidAt_le_converterMonoidAtWeakBudget
    (blockReplies_mem_converterMonoidAt i c)

/-- **The reply-eraser at the Φ level, computed**: `attachAt Set.univ (b)`
sends every resource law to the point mass at the constant system.  The
pushforward of `attachEngineFully_blockReplies_univ`. -/
theorem attachAt_blockReplies_univ (c : Uni.{u}) (L : Phi.{u}) :
    attachAt Set.univ (System.blockReplies Set.univ c) L
      = Distribution.fTransform
          (fun _ : System.DDS Uni.{u} Uni.{u} =>
            System.functionEvaluator (fun _ : Uni.{u} => c)) L := by
  show Distribution.fTransform
      (System.attachEngineFully Set.univ (System.blockReplies Set.univ c)) L = _
  exact congrArg (fun f => Distribution.fTransform f L)
    (funext fun R => System.attachEngineFully_blockReplies_univ c R)

end

end RandomSystems

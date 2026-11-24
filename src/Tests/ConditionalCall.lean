module

public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution
public import RandomSystems.Typed.ConditionalCall
public import RandomSystems.Typed.Filter

/-!
# Conditional oracle-call converter regression

Checks `conditionalCall`, `conditionalCallConverter`, and `TypedConverter.conditionalCall`:

* pure-branch inputs emit `0` inside requests and return `pureReply`;
* oracle-branch inputs emit `1` inside request, counted as soon as it is sent (before any inside
  reply arrives), and return `answer u (j, y)` on completion;
* fixed-oracle attachment satisfies `C • [H] = [g_H]` on both branches;
* the caller's outside domain is preserved verbatim, including all-pure outside histories whose
  oracle-branch request sequence is empty and outside domains larger than the inside budget;
* serial composition reuses the `#39` accounting laws
  (`IsDDCFrom.comp_callConverter_query_count_le`);
* CC composite notation (`•`, `∥`, `⊗ₘ`, `𝟙`) and `cc_normalize` work directly.
-/

@[expose] public section

namespace SystemAlgebra.Tests.ConditionalCall

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped SystemAlgebra

/-- Outside interface: one port `⋆`, queries `(flag, x) ∈ Bool²`, Boolean replies, up to 2 calls. -/
abbrev outside : Interface :=
  Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Bool) 2

/-- Inside interface: one port `⋆`, Boolean queries and replies, up to 2 calls. -/
abbrev inside : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

/-- Pure branch predicate: `flag = true` is answered locally without querying the oracle. -/
def isPure (u : Σ o, outside.X o) : Prop := u.2.1 = true

instance : DecidablePred isPure := fun u => inferInstanceAs (Decidable (u.2.1 = true))

/-- Pure reply: negate the payload `x`. -/
def pureReply (u : Σ o, outside.X o) : outside.Y u.1 := !u.2.2

/-- Oracle request: forward the payload `x` to the single inside port. -/
def request (u : Σ o, outside.X o) : Σ j, inside.X j := ⟨(), u.2.2⟩

/-- Oracle reply handler: combine the retained payload and oracle reply via XOR (`bne`). -/
def answer (u : Σ o, outside.X o) (r : Σ j, inside.Y j) : outside.Y u.1 :=
  bne u.2.2 r.2

/-- Nonempty oracle-branch request sequences stay within the 2-query inside budget. -/
lemma request_domain (us : List (Σ o, outside.X o)) (hu : outside.domain us)
    (hne : conditionalRequests isPure request us ≠ []) :
    inside.domain (conditionalRequests isPure request us) :=
  ⟨hne, (conditionalRequests_length_le isPure request us).trans hu.2⟩

/-- Certified conditional converter on `outside` and `inside`. -/
noncomputable def condConv : TypedConverter outside inside :=
  TypedConverter.conditionalCall isPure pureReply request answer request_domain

/-- Raw DDC certificate for the conditional converter. -/
lemma condConv_certified : IsDDCFrom inside.domain outside.domain 1
    (conditionalCallConverter isPure pureReply request answer outside.domain) :=
  conditionalCallConverter_isDDCFrom isPure pureReply request answer
    outside.nonempty_prefix.2 request_domain

/-- Pure-branch single input `(true, x)`: valid converter transcript emitting `0` inside
requests and returning `!x` immediately. -/
example (x : Bool) :
    let T : List ((Σ l : Two outside.I inside.I, twoFam outside.X inside.Y l) ×
        (Σ l : Two outside.I inside.I, twoFam outside.Y inside.X l)) :=
      [(⟨⟨none, ()⟩, (true, x)⟩, ⟨⟨none, ()⟩, !x⟩)]
    Replies (conditionalCallConverter isPure pureReply request answer outside.domain)
      (T.map Prod.fst) (T.map Prod.snd) ∧
    insideQueries (T.map Prod.snd) = [] ∧
    (insideQueries (T.map Prod.snd)).length = 0 := by
  intro T
  have hrep : Replies (conditionalCallConverter isPure pureReply request answer outside.domain)
      (T.map Prod.fst) (T.map Prod.snd) := by
    have hsched := replies_conditionalCallConverter_ofFunction
      isPure pureReply request answer outside.nonempty_prefix.2
      (fun _ b => b) [⟨(), (true, x)⟩] (by
        exact ⟨List.cons_ne_nil _ _, by simp only [List.length_singleton]; omega⟩)
    simpa only [T, List.flatMap_cons, List.flatMap_nil, List.append_nil, isPure, ↓reduceIte,
      List.map_nil, callTranscript, callSteps, pureReply, List.map_cons] using hsched
  refine ⟨hrep, ?_, ?_⟩
  · rw [conditionalCallConverter_queries isPure pureReply request answer hrep]
    simp only [T, List.map_cons, List.map_nil, outsideInputs_outside,
      conditionalRequests_singleton, isPure, ↓reduceIte]
  · rw [conditionalCallConverter_query_count isPure pureReply request answer hrep]
    simp only [T, List.map_cons, List.map_nil, outsideInputs_outside, conditionalCost, isPure,
      ↓reduceIte, List.sum_singleton]

/-- Oracle-branch single input `(false, x)`, stopped immediately after sending the inside
request (pending invocation, before any inside reply arrives): valid converter transcript
emitting `1` inside request, counted as soon as it is sent. -/
example (x : Bool) :
    let T : List ((Σ l : Two outside.I inside.I, twoFam outside.X inside.Y l) ×
        (Σ l : Two outside.I inside.I, twoFam outside.Y inside.X l)) :=
      [(⟨⟨none, ()⟩, (false, x)⟩, ⟨⟨some (), ()⟩, x⟩)]
    Replies (conditionalCallConverter isPure pureReply request answer outside.domain)
      (T.map Prod.fst) (T.map Prod.snd) ∧
    insideQueries (T.map Prod.snd) = [⟨(), x⟩] ∧
    (insideQueries (T.map Prod.snd)).length = 1 := by
  intro T
  have hrep : Replies (conditionalCallConverter isPure pureReply request answer outside.domain)
      (T.map Prod.fst) (T.map Prod.snd) := by
    have hsched := replies_conditionalCallConverter_ofFunction
      isPure pureReply request answer outside.nonempty_prefix.2
      (fun _ b => b) [⟨(), (false, x)⟩] (by
        exact ⟨List.cons_ne_nil _ _, by simp only [List.length_singleton]; omega⟩)
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, isPure, Bool.false_eq_true,
      ↓reduceIte, callTranscript, callSteps, request, answer, List.map_cons,
      List.map_nil] at hsched
    change Replies _ ([_] ++ [_]) ([_] ++ [_]) at hsched
    exact (replies_snoc.mp hsched).1
  refine ⟨hrep, ?_, ?_⟩
  · rw [conditionalCallConverter_queries isPure pureReply request answer hrep]
    simp only [T, List.map_cons, List.map_nil, outsideInputs_outside,
      conditionalRequests_singleton, isPure, Bool.false_eq_true, ↓reduceIte, request]
  · rw [conditionalCallConverter_query_count isPure pureReply request answer hrep]
    simp only [T, List.map_cons, List.map_nil, outsideInputs_outside, conditionalCost, isPure,
      Bool.false_eq_true, ↓reduceIte, List.sum_singleton]

/-- Completed calls emit `0` inside requests on the pure branch and `1` on the oracle branch,
via `conditionalCall_completed_exact_length` (reusing `callRule_completed_exact_length`). -/
example (x y : Bool) :
    (insideQueries ((callTranscript (O := outside.I) (J := inside.I)
      (U := outside.X) (V := outside.Y) (X := inside.X) (Y := inside.Y)
      ⟨(), (true, x)⟩ [] ⟨(), !x⟩).map Prod.snd)).length = 0 ∧
    (insideQueries ((callTranscript (O := outside.I) (J := inside.I)
      (U := outside.X) (V := outside.Y) (X := inside.X) (Y := inside.Y)
      ⟨(), (false, x)⟩ [(⟨(), x⟩, ⟨(), y⟩)] ⟨(), bne x y⟩).map Prod.snd)).length = 1 := by
  constructor
  · simpa only [conditionalCost, isPure, ↓reduceIte] using
      conditionalCall_completed_exact_length isPure pureReply request answer
        ⟨(), (true, x)⟩ [] (!x)
        (fun _ hn => (Nat.not_lt_zero _ hn).elim)
        (by simp only [conditionalCall, isPure, ↓reduceIte, pureReply])
  · simpa only [conditionalCost, isPure, Bool.false_eq_true, ↓reduceIte] using
      conditionalCall_completed_exact_length isPure pureReply request answer
        ⟨(), (false, x)⟩ [(⟨(), x⟩, ⟨(), y⟩)] (bne x y)
        (fun n hn => by
          have hn0 : n = 0 := by simp only [List.length_singleton] at hn; omega
          subst n
          simp only [List.take_zero, List.map_nil, conditionalCall, isPure, Bool.false_eq_true,
            ↓reduceIte, List.getElem_cons_zero, request])
        (by simp only [List.map_singleton, conditionalCall, isPure, Bool.false_eq_true,
          ↓reduceIte, answer])

/-- Fixed-oracle realization: attaching `condConv` to any fixed oracle `H` yields `g_H`,
evaluating `!x` on the pure branch and `bne x (H () x)` on the oracle branch. -/
example (H : ∀ j, inside.X j → inside.Y j) :
    condConv • TypedSystem.ofFunction H =
      TypedSystem.ofFunction (A := outside) (fun _ u =>
        if u.1 = true then !u.2 else bne u.2 (H () u.2)) := by
  rw [condConv, TypedConverter.conditionalCall_smul_ofFunction]
  congr 1

/-- Outside domain with budget `2` restricting to at most `1` oracle-branch query, paired with an
inside domain of budget `1`: preserves the larger outside domain and certifies all-pure histories
whose inside request sequence is empty (not in `inside1.domain`). -/
abbrev tightOutside : Interface :=
  outside.restrict
    (fun us => (us.map (conditionalCost isPure)).sum ≤ 1)
    (fun p h hp hh => by
      obtain ⟨t, rfl⟩ := hp
      simp only [List.map_append, List.sum_append] at hh
      omega)

/-- Inside interface with strict 1-query budget. -/
abbrev inside1 : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1

/-- Request map into `inside1` (same payload, tighter budget). -/
def request1 (u : Σ o, tightOutside.X o) : Σ j, inside1.X j := ⟨(), u.2.2⟩

/-- Oracle-branch requests from `tightOutside` satisfy `inside1.domain` whenever nonempty. -/
lemma request1_domain (us : List (Σ o, tightOutside.X o)) (hu : tightOutside.domain us)
    (hne : conditionalRequests isPure request1 us ≠ []) :
    inside1.domain (conditionalRequests isPure request1 us) := by
  refine ⟨hne, ?_⟩
  rw [conditionalRequests_length]
  exact hu.2

/-- An all-pure 2-query history is admitted by `tightOutside` even though its inside request
sequence is empty and rejected by `inside1.domain`. -/
example :
    tightOutside.domain [⟨(), (true, false)⟩, ⟨(), (true, true)⟩] ∧
    conditionalRequests isPure request1 [⟨(), (true, false)⟩, ⟨(), (true, true)⟩] = [] ∧
    ¬ inside1.domain [] := by
  refine ⟨⟨⟨List.cons_ne_nil _ _, le_refl _⟩, ?_⟩, ?_, fun h => h.1 rfl⟩
  · simp only [List.map_cons, List.map_nil, conditionalCost, isPure, ↓reduceIte, List.sum_cons,
      List.sum_nil, add_zero, Nat.zero_le]
  · simp only [conditionalRequests, List.filterMap_cons, List.filterMap_nil, isPure, ↓reduceIte]

/-- Certified converter with outside budget `2` over inside budget `1`, plus fixed-oracle law. -/
example (H : ∀ j, inside1.X j → inside1.Y j) :
    TypedConverter.conditionalCall (A := tightOutside) (B := inside1)
        isPure (fun u => !u.2.2) request1 (fun u r => bne u.2.2 r.2) request1_domain •
      TypedSystem.ofFunction H =
        TypedSystem.ofFunction (A := tightOutside) (fun _ u =>
          if u.1 = true then !u.2 else bne u.2 (H () u.2)) := by
  rw [TypedConverter.conditionalCall_smul_ofFunction]
  congr 1

/-- Serial composition accounting with an inner `conditionalCallConverter` reuses
`IsDDCFrom.comp_callConverter_query_count_le`. -/
example {O : Type} {U V : O → Type} {G : List (Σ o, U o) → Prop} {bβ : ℕ}
    {β : InsideOutsideSystem O outside.I U V outside.X outside.Y}
    (hβ : IsDDCFrom outside.domain G bβ β)
    {T : List ((Σ l, twoFam U inside.Y l) × (Σ l, twoFam V inside.X l))}
    (hr : Replies
      (trim (serialM β (conditionalCallConverter isPure pureReply request answer outside.domain)))
      (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ Tb : List ((Σ l, twoFam U outside.Y l) × (Σ l, twoFam V outside.X l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      (insideQueries (T.map Prod.snd)).length ≤
        ((insideQueries (Tb.map Prod.snd)).map (conditionalCost isPure)).sum :=
  hβ.comp_conditionalCallConverter_query_count_le isPure pureReply request answer
    condConv_certified hr

/-- CC composite notation (`•`, `∥`, `⊗ₘ`, `𝟙`) and `cc_normalize` work directly with
`TypedConverter.conditionalCall_smul_ofFunction`. -/
example {C : Interface} (H : ∀ j, inside.X j → inside.Y j) (S : TypedSystem C) :
    (condConv ⊗ₘ 𝟙 C) • (TypedSystem.ofFunction H ∥ S) =
      TypedSystem.ofFunction (A := outside) (fun _ u =>
        if u.1 = true then !u.2 else bne u.2 (H () u.2)) ∥ S := by
  cc_normalize
  congr 1
  rw [condConv, TypedConverter.conditionalCall_smul_ofFunction]
  congr 1

#print axioms conditionalCallConverter_isDDCFrom
#print axioms conditionalCallConverter_queries
#print axioms conditionalCallConverter_query_count
#print axioms conditionalCall_completed_exact_length
#print axioms IsDDCFrom.comp_conditionalCallConverter_query_count_le
#print axioms TypedConverter.ofDDC_conditionalCallConverter_smul_ofFunction
#print axioms TypedConverter.conditionalCall_smul_ofFunction

end SystemAlgebra.Tests.ConditionalCall

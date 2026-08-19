/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.AttachEngineFully

/-!
# The framing law: an attachment inside one leg of a parallel composite

MauRen11 §6.2 defines parallel converter composition by
`(α∣β)ⁱ(R‖S) := αⁱR ‖ βⁱS`, and `AbstractCryptography.SMulParClass` renders
that equation as a class field, `(α ∥ β) • (R ∥ S) = (α • R) ∥ (β • S)`.  This
module proves the equation on this carrier, for the attachment generators of
the metric-facing `Σ`.

## The statement, and the three clauses it costs

  `attachEngineFully i E (par c R S) = par c (attachEngineFully i E R) S`
    for `i ⊆ c` and `RequestsWithin i E`.

`i ⊆ c` says the interface the converter acts at lies on the left leg's side of
the splitting; `RequestsWithin i E` says the engine reaches only that
interface.  These are the same two clauses `attachEngineFully_comm` pays, for
the same reason: a converter that could be served by the *other* component in
one nesting and by its own in the other makes the equation false.  Nothing
about the engine's reactions is used — no `InnerTotal`, no budget — because
this, like the commutation, is an equation of partial values, and a round that
diverges on one side diverges on the other.

## Why it is not bookkeeping

The two sides thread *different* resource histories.  On the left the engine's
requests and the foreign outer queries are written into one raw history of the
composite `par c R S`, and CR18 Definition 3.3's deletion is applied to *that*
list when the composite is read; on the right the splitting first filters the
outer history by `c`, and the deletion is applied to `R`'s own list.  The two
agree because deletion commutes with the filter — `keptPrefix_par_proj`, which
the tree already had — and because the frame's side of the history is frozen
during an owned round, `RequestsWithin i E` putting every request inside
`i ⊆ c`.

The round itself transfers with no new induction: `answer_par_mem` is exactly
the hypothesis `exists_mem_resolve_of_requestsWithin` asks for at the
correspondence "the resource history is the composite history filtered by `c`",
so `PFun.fix_bisim` is spent once, in leg (d), and reused here.

## What the abstract class gets

`SMulParClass` is unconditional and this equation is not: `parF` is parallel
composition only on separated faces (`parF_absorb`), and an attachment is
confined only by hypothesis.  So the class stays uninstantiable at `Φ` for the
same reason `IsNonexpandingPar` does, and the conditional theorem is the
deliverable.  The `Φ`-level readings — at a fixed splitting here, at `parF`
through canonicity in `ParFace.lean` — are what the consumers use.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical
open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve driveFrom)

universe u v

/-! ## Two partial-value forms of `par` at the frontier

`mem_dom_par` and `output_par_mem` split the composite's domain and its answer;
what an induction over a *drive* needs is the single partial value, since a
round is a `Part` and the equation being proved is an equation of `Part`s.  The
side condition is the other component's clause, which the frontier receipts
`mem_dom_par_concat_mem`/`_not_mem` carry as a coherence certificate about the
past; here it is stated directly about the sub-history, because at the call
sites it is discharged by `keptPrefix_mem_or` and not by an induction. -/

variable {X : Type u} {Y : Type v}

/-- The composite's whole partial value at a query the **left** component owns:
that component's own value at its own extended sub-history, provided the right
component's sub-history is coherent. -/
theorem par_concat_eq_left (c : Set X) (R S : DDS X Y) {l : List X} {q : X}
    (hq : q ∈ c) (hS : historyAt cᶜ l = [] ∨ historyAt cᶜ l ∈ dom S) :
    (par c R S).1 (l ++ [q]) = R.1 (historyAt c l ++ [q]) := by
  have hqc : q ∉ cᶜ := by simpa using hq
  have hdom : (l ++ [q] ∈ dom (par c R S)) ↔ (historyAt c l ++ [q] ∈ dom R) := by
    rw [mem_dom_par, historyAt_append_mem c l q hq, historyAt_append_not_mem cᶜ l q hqc]
    constructor
    · rintro ⟨-, hR, -⟩
      rcases hR with h | h
      · simp at h
      · exact h
    · intro h
      exact ⟨by simp, Or.inr h, hS⟩
  refine Part.ext' hdom fun h₁ h₂ => ?_
  exact output_par_mem c R S l q hq h₁ h₂

/-- The composite's whole partial value at a query the **right** component
owns. -/
theorem par_concat_eq_right (c : Set X) (R S : DDS X Y) {l : List X} {q : X}
    (hq : q ∉ c) (hR : historyAt c l = [] ∨ historyAt c l ∈ dom R) :
    (par c R S).1 (l ++ [q]) = S.1 (historyAt cᶜ l ++ [q]) := by
  have hqc : q ∈ cᶜ := by simpa using hq
  have hdom : (l ++ [q] ∈ dom (par c R S)) ↔ (historyAt cᶜ l ++ [q] ∈ dom S) := by
    rw [mem_dom_par, historyAt_append_mem cᶜ l q hqc, historyAt_append_not_mem c l q hq]
    constructor
    · rintro ⟨-, -, hS⟩
      rcases hS with h | h
      · simp at h
      · exact h
    · intro h
      exact ⟨by simp, hR, Or.inr h⟩
  refine Part.ext' hdom fun h₁ h₂ => ?_
  exact output_par_not_mem c R S l q hq h₁ h₂

/-- A history accepted with one more query was accepted (or empty) before it —
prefix-closure, in the shape the parallel domain clauses are written in. -/
theorem mem_dom_or_nil_of_concat {T : DDS X Y} {l : List X} {q : X}
    (h : l ++ [q] ∈ dom T) : l = [] ∨ l ∈ dom T := by
  rcases eq_or_ne l [] with rfl | hne
  · exact Or.inl rfl
  · exact Or.inr (prefix_closed T ⟨[q], rfl⟩ hne h)

/-! ## The round transfer across a parallel frame

Both directions are `exists_mem_resolve_of_requestsWithin` at the
correspondence `ls' = historyAt c ls`.  Its two obligations are discharged by
theorems that were already in the tree: the answers agree by `answer_par_mem`
(a request lies in `i ⊆ c`, so the left component owns it), and the
correspondence survives one more request by `historyAt_append_mem`.  No engine
class and no budget are consumed — a round that diverges on one side diverges
on the other. -/

section Rounds

variable {i c : Set Uni.{u}} {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
  {R S : DDS Uni.{u} Uni.{u}}

/-- **Forwards**: a round against the framed resource is the same round against
the resource alone, run on the resource's own sub-history. -/
theorem exists_mem_resolve_of_mem_resolve_par (hic : i ⊆ c) (hReq : RequestsWithin i E)
    {cE cE' : List (CIn Uni.{u} Uni.{u})} {ys ys' : List Uni.{u}} {v : Uni.{u}}
    (h : (v, (cE', ys')) ∈ resolve (ofEngine E) (par c R S) (cE, ys)) :
    (v, (cE', historyAt c ys')) ∈ resolve (ofEngine E) R (cE, historyAt c ys) := by
  obtain ⟨ms', hms', hP⟩ :=
    exists_mem_resolve_of_requestsWithin hReq (S := par c R S) (S' := R)
      (fun ls ls' => ls' = historyAt c ls)
      (by
        rintro ls ls' rfl x hx
        exact answer_par_mem c R S ls x (hic hx))
      (by
        rintro ls ls' rfl x hx
        exact (historyAt_append_mem c ls x (hic hx)).symm)
      rfl h
  exact hP ▸ hms'

/-- **Backwards**: a round against the resource alone lifts to a round against
the framed resource, leaving the same conversation. -/
theorem exists_mem_resolve_par_of_mem_resolve (hic : i ⊆ c) (hReq : RequestsWithin i E)
    {cE cE' : List (CIn Uni.{u} Uni.{u})} {ys ms' : List Uni.{u}} {v : Uni.{u}}
    (h : (v, (cE', ms')) ∈ resolve (ofEngine E) R (cE, historyAt c ys)) :
    ∃ ys', (v, (cE', ys')) ∈ resolve (ofEngine E) (par c R S) (cE, ys) ∧
      historyAt c ys' = ms' := by
  obtain ⟨ys', hys', hP⟩ :=
    exists_mem_resolve_of_requestsWithin hReq (S := R) (S' := par c R S)
      (fun ls ls' => ls = historyAt c ls')
      (by
        rintro ls ls' rfl x hx
        exact (answer_par_mem c R S ls' x (hic hx)).symm)
      (by
        rintro ls ls' rfl x hx
        exact (historyAt_append_mem c ls' x (hic hx)).symm)
      rfl h
  exact ⟨ys', hys', hP.symm⟩

/-- **The frame's side of the history is frozen during a round**: every address
a round appends belongs to `i`, hence to `c`.  This is what makes the frame's
component unable to notice that a round happened, and it is
`resolve_requests_within` read through the splitting. -/
theorem historyAt_compl_resolve (hic : i ⊆ c) (hReq : RequestsWithin i E)
    {T : DDS Uni.{u} Uni.{u}} {cE cE' : List (CIn Uni.{u} Uni.{u})}
    {ys ys' : List Uni.{u}} {v : Uni.{u}}
    (h : (v, (cE', ys')) ∈ resolve (ofEngine E) T (cE, ys)) :
    historyAt cᶜ ys' = historyAt cᶜ ys := by
  obtain ⟨w, rfl, hw⟩ := resolve_requests_within hReq T h
  rw [historyAt_append]
  refine (congrArg (historyAt cᶜ ys ++ ·) ?_).trans (List.append_nil _)
  refine List.filter_eq_nil_iff.mpr fun x hx => ?_
  simpa using hic (hw x hx)

end Rounds

/-! ## The framing law -/

section Framing

variable {i c : Set Uni.{u}} {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}

/-- **The simulation invariant**, and the equation it carries.  One induction
over the outer history, proving three things at once because they feed each
other:

* the two composites are the same partial value at that history;
* forwards, a state reached by `αⁱ` *inside* the frame projects to the state
  `αⁱ` reaches on the resource's own sub-history, the frame's side of the raw
  history being exactly the frame's side of the outer history, and the frame's
  component having accepted it;
* backwards, a state reached on the resource's own sub-history — together with
  the frame's component having accepted its side — lifts to a state inside the
  frame.

Both directions are needed because the equation is an equation of *partial*
values and neither side is known to be defined in advance; that is the same
reason `attachEngineFully_comm_aux` carries its own converse.

The three cases of the step are the three kinds of query: owned (`q ∈ i`),
foreign but on the left leg (`q ∈ c \ i`), and on the right leg (`q ∉ c`).  The
first transfers by the round lemmas above; the second and third are the two
halves of `keptPrefix_par_proj` plus `attachEngineFully_transparent`. -/
theorem attachEngineFully_par_aux (hic : i ⊆ c) (hReq : RequestsWithin i E)
    (R S : DDS Uni.{u} Uni.{u}) :
    ∀ us : List Uni.{u},
      ((attachEngineFully i E (par c R S)).1 us
          = (par c (attachEngineFully i E R) S).1 us)
      ∧ (∀ cE ys, ReachedAt i E (par c R S) us (cE, ys) →
          ReachedAt i E R (historyAt c us) (cE, historyAt c ys)
            ∧ historyAt cᶜ ys = historyAt cᶜ us
            ∧ (historyAt cᶜ us = [] ∨ historyAt cᶜ us ∈ dom S))
      ∧ (∀ cE ms, ReachedAt i E R (historyAt c us) (cE, ms) →
          (historyAt cᶜ us = [] ∨ historyAt cᶜ us ∈ dom S) →
          ∃ ys, ReachedAt i E (par c R S) us (cE, ys) ∧ historyAt c ys = ms
                ∧ historyAt cᶜ ys = historyAt cᶜ us) := by
  have hreach : ∀ l : List Uni.{u},
      (∃ st, ReachedAt i E R l st) ↔
        (l = [] ∨ l ∈ dom (attachEngineFully i E R)) := by
    intro l
    rcases eq_or_ne l [] with rfl | hne
    · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨_, reachedAt_nil i E R⟩⟩
    · rw [exists_reachedAt_iff_mem_dom hne]
      exact ⟨Or.inr, fun h => h.resolve_left hne⟩
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨?_, ?_, ?_⟩
      · rw [attachEngineFully_nil]
        refine (Part.eq_none_iff'.mpr fun hd => ?_).symm
        exact ((mem_dom_par c (attachEngineFully i E R) S []).mp hd).1 rfl
      · intro cE ys hst
        obtain ⟨rfl, rfl⟩ : cE = [] ∧ ys = [] := by
          have := hst.unique (reachedAt_nil i E (par c R S))
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        exact ⟨reachedAt_nil i E R, rfl, Or.inl rfl⟩
      · intro cE ms hst _
        obtain ⟨rfl, rfl⟩ : cE = [] ∧ ms = [] := by
          have := hst.unique (reachedAt_nil i E R)
          exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
        exact ⟨[], reachedAt_nil i E (par c R S), rfl, rfl⟩
  | append_singleton us q ih =>
      obtain ⟨ihv, ihf, ihb⟩ := ih
      refine ⟨?_, ?_, ?_⟩
      · -- the values agree
        by_cases hex : ∃ st, ReachedAt i E (par c R S) us st
        · obtain ⟨⟨cE, ys⟩, hst⟩ := hex
          obtain ⟨hR, hcc, hgood⟩ := ihf cE ys hst
          obtain ⟨hkpR, hkpS⟩ := keptPrefix_par_proj c R S ys
          by_cases hqi : q ∈ i
          · have hqc : q ∈ c := hic hqi
            rw [attachEngineFully_concat_round hst q,
              attachEngineFullyRound_mem E (par c R S) (cE, ys) hqi,
              par_concat_eq_left c (attachEngineFully i E R) S hqc hgood,
              attachEngineFully_concat_round hR q,
              attachEngineFullyRound_mem E R (cE, historyAt c ys) hqi]
            refine Part.ext fun v => ?_
            simp only [Part.mem_map_iff]
            constructor
            · rintro ⟨⟨v', cE', ys'⟩, hmem, rfl⟩
              exact ⟨(v', (cE', historyAt c ys')),
                exists_mem_resolve_of_mem_resolve_par hic hReq hmem, rfl⟩
            · rintro ⟨⟨v', cE', ms'⟩, hmem, rfl⟩
              obtain ⟨ys', hys', -⟩ := exists_mem_resolve_par_of_mem_resolve
                (S := S) hic hReq hmem
              exact ⟨(v', (cE', ys')), hys', rfl⟩
          · rw [attachEngineFully_transparent hst hqi]
            by_cases hqc : q ∈ c
            · rw [par_concat_eq_left c R S hqc
                  (by rw [hkpS]; exact (keptPrefix_mem_or S _).symm),
                hkpR, par_concat_eq_left c (attachEngineFully i E R) S hqc hgood,
                attachEngineFully_transparent hR hqi]
            · rw [par_concat_eq_right c R S hqc
                  (by rw [hkpR]; exact (keptPrefix_mem_or R _).symm),
                hkpS, hcc,
                par_concat_eq_right c (attachEngineFully i E R) S hqc
                  ((hreach (historyAt c us)).mp ⟨_, hR⟩),
                keptPrefix_eq_self_of_mem_or_empty S hgood.symm]
        · rw [attachEngineFully_concat_eq_none hex q]
          refine (Part.eq_none_iff'.mpr fun hd => hex ?_).symm
          obtain ⟨-, hA, hS⟩ := (mem_dom_par c (attachEngineFully i E R) S (us ++ [q])).mp hd
          have hgood : historyAt cᶜ us = [] ∨ historyAt cᶜ us ∈ dom S := by
            by_cases hqc : q ∈ c
            · rwa [historyAt_append_not_mem cᶜ us q (by simpa using hqc)] at hS
            · rw [historyAt_append_mem cᶜ us q (by simpa using hqc)] at hS
              exact mem_dom_or_nil_of_concat (hS.resolve_left (by simp))
          have hAus : historyAt c us = [] ∨ historyAt c us ∈ dom (attachEngineFully i E R) := by
            by_cases hqc : q ∈ c
            · rw [historyAt_append_mem c us q hqc] at hA
              exact mem_dom_or_nil_of_concat (hA.resolve_left (by simp))
            · rwa [historyAt_append_not_mem c us q hqc] at hA
          obtain ⟨⟨cE, ms⟩, hst⟩ := (hreach (historyAt c us)).mpr hAus
          obtain ⟨ys, hys, -, -⟩ := ihb cE ms hst hgood
          exact ⟨_, hys⟩
      · -- forwards
        intro cE₁ ys₁ hst₁
        obtain ⟨⟨cE, ys⟩, hst⟩ := exists_reachedAt_of_reachedAt_append hst₁
        obtain ⟨hR, hcc, hgood⟩ := ihf cE ys hst
        obtain ⟨hkpR, hkpS⟩ := keptPrefix_par_proj c R S ys
        obtain ⟨v, hround⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hst hst₁
        by_cases hqi : q ∈ i
        · have hqc : q ∈ c := hic hqi
          have hqcc : q ∉ cᶜ := by simpa using hqc
          rw [attachEngineFullyRound_mem E (par c R S) (cE, ys) hqi] at hround
          refine ⟨?_, ?_, ?_⟩
          · rw [historyAt_append_mem c us q hqc]
            exact attachEngineFully_reached_concat_mem hR hqi
              (exists_mem_resolve_of_mem_resolve_par hic hReq hround)
          · rw [historyAt_append_not_mem cᶜ us q hqcc,
              historyAt_compl_resolve hic hReq hround]
            exact hcc
          · rw [historyAt_append_not_mem cᶜ us q hqcc]
            exact hgood
        · rw [attachEngineFullyRound_not_mem E (par c R S) (cE, ys) hqi,
            Part.mem_map_iff] at hround
          obtain ⟨y, hy, heq⟩ := hround
          have hcE : cE₁ = cE := (congrArg (Prod.fst ∘ Prod.snd) heq).symm
          have hys : ys₁ = ys ++ [q] := (congrArg (Prod.snd ∘ Prod.snd) heq).symm
          subst hcE; subst hys
          have hdomP : keptPrefix (par c R S) ys ++ [q] ∈ dom (par c R S) :=
            Part.dom_iff_mem.mpr ⟨y, hy⟩
          by_cases hqc : q ∈ c
          · have hqcc : q ∉ cᶜ := by simpa using hqc
            have hdomR : keptPrefix R (historyAt c ys) ++ [q] ∈ dom R := by
              rw [← hkpR]
              exact mem_dom_left_of_mem_dom_par c R S _ q hqc hdomP
            refine ⟨?_, ?_, ?_⟩
            · rw [historyAt_append_mem c us q hqc, historyAt_append_mem c ys q hqc]
              exact attachEngineFully_reached_concat_not_mem hR hqi hdomR
            · rw [historyAt_append_not_mem cᶜ us q hqcc,
                historyAt_append_not_mem cᶜ ys q hqcc]
              exact hcc
            · rw [historyAt_append_not_mem cᶜ us q hqcc]
              exact hgood
          · have hqcc : q ∈ cᶜ := by simpa using hqc
            have hdomS : historyAt cᶜ us ++ [q] ∈ dom S := by
              have h0 := mem_dom_right_of_mem_dom_par c R S _ q hqc hdomP
              rw [hkpS, hcc, keptPrefix_eq_self_of_mem_or_empty S hgood.symm] at h0
              exact h0
            refine ⟨?_, ?_, ?_⟩
            · rw [historyAt_append_not_mem c us q hqc,
                historyAt_append_not_mem c ys q hqc]
              exact hR
            · rw [historyAt_append_mem cᶜ us q hqcc, historyAt_append_mem cᶜ ys q hqcc,
                hcc]
            · rw [historyAt_append_mem cᶜ us q hqcc]
              exact Or.inr hdomS
      · -- backwards
        intro cE₁ ms₁ hst₁ hgood₁
        by_cases hqc : q ∈ c
        · have hqcc : q ∉ cᶜ := by simpa using hqc
          rw [historyAt_append_mem c us q hqc] at hst₁
          rw [historyAt_append_not_mem cᶜ us q hqcc] at hgood₁ ⊢
          obtain ⟨⟨cE, ms⟩, hst⟩ := exists_reachedAt_of_reachedAt_append hst₁
          obtain ⟨ys, hys, hysc, hyscc⟩ := ihb cE ms hst hgood₁
          obtain ⟨hkpR, hkpS⟩ := keptPrefix_par_proj c R S ys
          obtain ⟨v, hround⟩ := exists_mem_attachEngineFullyRound_of_reachedAt hst hst₁
          by_cases hqi : q ∈ i
          · rw [attachEngineFullyRound_mem E R (cE, ms) hqi, ← hysc] at hround
            obtain ⟨ys₁, hys₁, hys₁c⟩ :=
              exists_mem_resolve_par_of_mem_resolve (S := S) hic hReq hround
            refine ⟨ys₁, attachEngineFully_reached_concat_mem hys hqi hys₁, hys₁c, ?_⟩
            rw [historyAt_compl_resolve hic hReq hys₁]
            exact hyscc
          · rw [attachEngineFullyRound_not_mem E R (cE, ms) hqi, Part.mem_map_iff] at hround
            obtain ⟨y, hy, heq⟩ := hround
            have hcE : cE₁ = cE := (congrArg (Prod.fst ∘ Prod.snd) heq).symm
            have hms : ms₁ = ms ++ [q] := (congrArg (Prod.snd ∘ Prod.snd) heq).symm
            subst hcE; subst hms
            have hdomR : keptPrefix R ms ++ [q] ∈ dom R := Part.dom_iff_mem.mpr ⟨y, hy⟩
            have hdomP : keptPrefix (par c R S) ys ++ [q] ∈ dom (par c R S) := by
              rw [mem_dom_par]
              refine ⟨by simp, ?_, ?_⟩
              · rw [historyAt_append_mem c _ q hqc, hkpR, hysc]
                exact Or.inr hdomR
              · rw [historyAt_append_not_mem cᶜ _ q hqcc, hkpS]
                exact (keptPrefix_mem_or S _).symm
            refine ⟨ys ++ [q], attachEngineFully_reached_concat_not_mem hys hqi hdomP, ?_, ?_⟩
            · rw [historyAt_append_mem c ys q hqc, hysc]
            · rw [historyAt_append_not_mem cᶜ ys q hqcc]
              exact hyscc
        · have hqcc : q ∈ cᶜ := by simpa using hqc
          have hqi : q ∉ i := fun h => hqc (hic h)
          rw [historyAt_append_not_mem c us q hqc] at hst₁
          rw [historyAt_append_mem cᶜ us q hqcc] at hgood₁ ⊢
          have hdomS : historyAt cᶜ us ++ [q] ∈ dom S := hgood₁.resolve_left (by simp)
          have hgood : historyAt cᶜ us = [] ∨ historyAt cᶜ us ∈ dom S :=
            mem_dom_or_nil_of_concat hdomS
          obtain ⟨ys, hys, hysc, hyscc⟩ := ihb cE₁ ms₁ hst₁ hgood
          obtain ⟨hkpR, hkpS⟩ := keptPrefix_par_proj c R S ys
          have hdomP : keptPrefix (par c R S) ys ++ [q] ∈ dom (par c R S) := by
            rw [mem_dom_par]
            refine ⟨by simp, ?_, ?_⟩
            · rw [historyAt_append_not_mem c _ q hqc, hkpR]
              exact (keptPrefix_mem_or R _).symm
            · rw [historyAt_append_mem cᶜ _ q hqcc, hkpS, hyscc,
                keptPrefix_eq_self_of_mem_or_empty S hgood.symm]
              exact Or.inr hdomS
          refine ⟨ys ++ [q], attachEngineFully_reached_concat_not_mem hys hqi hdomP, ?_, ?_⟩
          · rw [historyAt_append_not_mem c ys q hqc]
            exact hysc
          · rw [historyAt_append_mem cᶜ ys q hqcc, hyscc]

/-- **The framing law at the deterministic core** — MauRen11 §6.2's
`(α∣1)ⁱ(R‖S) = αⁱR ‖ S`, at this carrier's attachment primitive.

The price is the two clauses `attachEngineFully_comm` pays: the interface is on
the left leg's side of the splitting, and the engine reaches only its own
interface.  No engine class is consumed. -/
theorem attachEngineFully_par (hic : i ⊆ c) (hReq : RequestsWithin i E)
    (R S : DDS Uni.{u} Uni.{u}) :
    attachEngineFully i E (par c R S) = par c (attachEngineFully i E R) S :=
  Subtype.ext (funext fun us => (attachEngineFully_par_aux hic hReq R S us).1)

/-- **The mirror**, `(1∣β)ⁱ(R‖S) = R ‖ βⁱS`, by `par_comm`: complementing the
splitting exchanges the two legs, and `j ⊆ cᶜ` becomes the left-leg
hypothesis. -/
theorem attachEngineFully_par_right {j : Set Uni.{u}}
    {F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hjc : j ⊆ cᶜ) (hReq : RequestsWithin j F) (R S : DDS Uni.{u} Uni.{u}) :
    attachEngineFully j F (par c R S) = par c R (attachEngineFully j F S) := by
  rw [par_comm c R S, attachEngineFully_par hjc hReq S R,
    par_comm cᶜ (attachEngineFully j F S) R, compl_compl]

/-! ### The face of an attachment

The bookkeeping the `parF` readings need: attaching at `i` can only add
addresses of `i` to the interface set.  Outside `i` the composite is the
resource (`attachEngineFully_transparent`), so an accepted foreign query is an
accepted resource query; inside `i` there is nothing to prove. -/

/-- **An attachment moves the face by at most its own interface.** -/
theorem support_attachEngineFully_subset (i : Set Uni.{u})
    (E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (R : DDS Uni.{u} Uni.{u}) :
    System.support (attachEngineFully i E R) ⊆ System.support R ∪ i := by
  rintro q ⟨l, hl, hq⟩
  by_cases hqi : q ∈ i
  · exact Or.inr hqi
  refine Or.inl ?_
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hq
  have hpre : pre ++ [q] ∈ dom (attachEngineFully i E R) :=
    prefix_closed _ (l₂ := pre ++ q :: post) ⟨post, by simp⟩ (by simp) hl
  obtain ⟨⟨cE, xs⟩, hst⟩ :=
    exists_reachedAt_of_reachedAt_append (us := pre) (vs := [q])
      (Exists.choose_spec (exists_reachedAt_of_mem_dom hpre))
  exact ⟨keptPrefix R xs ++ [q],
    (mem_dom_attachEngineFully_concat_not_mem hst hqi).mp hpre, by simp⟩

end Framing

end

end System

/-! ## The framing law at `Φ`

Both sides are pushforwards of the same independent product, so the law lifts
atom by atom: `fTransform_prod_left` moves the attachment inside the product
and `fTransform_fTransform` collapses the two pushforwards, leaving one
`congrArg` on the deterministic equation. -/

noncomputable section

open Probability (Distribution)

universe u

variable {i c : Set Uni.{u}}
  {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}

/-- **The framing law at `Φ`, at a fixed splitting**: an attachment inside the
left leg's side of the splitting passes through the frame. -/
theorem attachAt_par (hic : i ⊆ c) (hReq : System.RequestsWithin i E) (L M : Phi.{u}) :
    attachAt i E (RandomSystems.par c L M) = RandomSystems.par c (attachAt i E L) M := by
  show Distribution.fTransform (System.attachEngineFully i E)
      (Distribution.fTransform (fun p => System.par c p.1 p.2) (Distribution.prod L M)) =
    Distribution.fTransform (fun p => System.par c p.1 p.2)
      (Distribution.prod (Distribution.fTransform (System.attachEngineFully i E) L) M)
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_prod_left,
    Distribution.fTransform_fTransform]
  exact congrArg (fun f => Distribution.fTransform f (Distribution.prod L M))
    (funext fun p => System.attachEngineFully_par hic hReq p.1 p.2)

/-- **The framing law at `Φ`, right leg**. -/
theorem attachAt_par_right {j : Set Uni.{u}}
    {F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hjc : j ⊆ cᶜ) (hReq : System.RequestsWithin j F) (L M : Phi.{u}) :
    attachAt j F (RandomSystems.par c L M) = RandomSystems.par c L (attachAt j F M) := by
  rw [RandomSystems.par_comm c L M, attachAt_par hjc hReq M L,
    RandomSystems.par_comm cᶜ (attachAt j F M) L, compl_compl]

/-- **The face of an attachment at `Φ`** — `System.support_attachEngineFully_subset`
through the pushforward.  This is what lets the `parF` readings discharge their
separation hypotheses for the *converted* resource instead of assuming them
again. -/
theorem support_attachAt_subset (i : Set Uni.{u})
    (E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})) (L : Phi.{u}) :
    RandomSystems.support (attachAt i E L) ⊆ RandomSystems.support L ∪ i := by
  intro q hq
  obtain ⟨T, hT, hqT⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨T₀, hT₀, rfl⟩ := Distribution.mem_support_fTransform _ _ hT
  rcases System.support_attachEngineFully_subset i E T₀ hqT with h | h
  · exact Or.inl (Set.mem_iUnion₂.mpr ⟨T₀, hT₀, h⟩)
  · exact Or.inr h

end

end RandomSystems

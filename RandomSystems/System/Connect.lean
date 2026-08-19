/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Relabel

/-!
# `connect` — the trace: closing the loop between an engine and a resource

The one interactive generator of the converter monoid.  An **engine** is an
ordinary deterministic system at the request-coded signature

* inputs  `U ⊕ Y` — an outer query `u`, or a resource reply `y`;
* answers `V ⊕ X` — an outer answer `v`, or a resource request `x`,

with the outer/inner distinction absorbed in the sum types (no face labels,
no `⊥` symbol: partiality is undefinedness, as everywhere in this
development).  `connect E R` interprets the engine's requests against the
resource `R : DDS X Y`: every interaction is initiated by an outer query;
on `inr x` the resource is consulted and its answer fed back; on `inl v`
the round closes.  Resources never talk to each other — a plain resource's
answers carry no request constructor, so the loop is typable only against
an engine.

Termination is by stabilization, the same discipline as the transcript
(`tr`): the interpreter is staged by fuel, and a history is in the domain
exactly when some fuel resolves it.  On budgeted engines (bounded
consecutive requests) the fuel is computable from the history; that class
and its totality theorem arrive with the converter-monoid assembly.

The probabilistic level (`PDS.connectLaw`) is the independent product
pushed along the deterministic interpreter, exactly as `Resource.parLaw`.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v w z

variable {U : Type u} {V : Type v} {X : Type w} {Y : Type z}

/-- The identity converter's engine — MauRen16 §3.3's `id ∈ Σ` at the
interpreter: relay every outer query as a request, every reply as the
answer.  `Sum.swap`, evaluated statelessly. -/
def idEngine : DDS (X ⊕ Y) (Y ⊕ X) :=
  functionEvaluator Sum.swap

namespace Connect

/-- One round of the interpreter, staged by fuel: resolve the engine's
pending move at the state `(engine history, resource history)` into an
outer answer, servicing `inr`-requests against the resource on the way.
`Part.none` = the engine or resource has no move, or the fuel is spent. -/
def serve (E : DDS (U ⊕ Y) (V ⊕ X)) (R : DDS X Y) :
    ℕ → List (U ⊕ Y) × List X → Part (V × (List (U ⊕ Y) × List X))
  | 0, _ => Part.none
  | n + 1, st =>
      if hE : st.1 ∈ dom E then
        Sum.elim
          (fun v => Part.some (v, st))
          (fun x =>
            if hR : st.2 ++ [x] ∈ dom R then
              serve E R n
                (st.1 ++ [Sum.inr (output R (st.2 ++ [x]) hR)], st.2 ++ [x])
            else Part.none)
          (output E st.1 hE)
      else Part.none

variable {E : DDS (U ⊕ Y) (V ⊕ X)} {R : DDS X Y}

/-- Process an outer history from a state: each query opens a round,
resolved by `serve`; the value is the last round's outer answer together
with the final state. -/
def runAux (E : DDS (U ⊕ Y) (V ⊕ X)) (R : DDS X Y) (n : ℕ) :
    List U → List (U ⊕ Y) × List X → Part (V × (List (U ⊕ Y) × List X))
  | [], _ => Part.none
  | [u], st => serve E R n (st.1 ++ [Sum.inl u], st.2)
  | u :: u' :: us, st =>
      (serve E R n (st.1 ++ [Sum.inl u], st.2)).bind fun p =>
        runAux E R n (u' :: us) p.2

@[simp]
theorem runAux_nil (n : ℕ) (st : List (U ⊕ Y) × List X) :
    runAux E R n [] st = Part.none :=
  rfl

theorem runAux_singleton (n : ℕ) (u : U) (st : List (U ⊕ Y) × List X) :
    runAux E R n [u] st = serve E R n (st.1 ++ [Sum.inl u], st.2) :=
  rfl

theorem runAux_cons_cons (n : ℕ) (u u' : U) (us : List U)
    (st : List (U ⊕ Y) × List X) :
    runAux E R n (u :: u' :: us) st =
      (serve E R n (st.1 ++ [Sum.inl u], st.2)).bind fun p =>
        runAux E R n (u' :: us) p.2 :=
  rfl

/-- Processing an extension succeeds only if processing the (nonempty)
prefix does, from the same state and fuel: the interpreter reads the outer
history left to right. -/
theorem runAux_dom_prefix {n : ℕ} :
    ∀ {us₁ us₂ : List U} {st : List (U ⊕ Y) × List X},
      us₁ <+: us₂ → us₁ ≠ [] →
      (runAux E R n us₂ st).Dom → (runAux E R n us₁ st).Dom := by
  intro us₁
  induction us₁ with
  | nil => exact fun hpre hne _ => absurd rfl hne
  | cons u us₁ ih =>
      intro us₂ st hpre _ hdom
      cases us₂ with
      | nil => simp at hpre
      | cons v us₂' =>
          rw [List.cons_prefix_cons] at hpre
          obtain ⟨rfl, hpre'⟩ := hpre
          cases us₁ with
          | nil =>
              cases us₂' with
              | nil => exact hdom
              | cons v' us₂'' =>
                  rw [runAux_cons_cons] at hdom
                  rw [runAux_singleton]
                  exact (Part.bind_dom.mp hdom).fst
          | cons u' us₁' =>
              cases us₂' with
              | nil => simp at hpre'
              | cons v' us₂'' =>
                  rw [List.cons_prefix_cons] at hpre'
                  obtain ⟨rfl, hpre''⟩ := hpre'
                  rw [runAux_cons_cons] at hdom ⊢
                  obtain ⟨hserve, hrest⟩ := Part.bind_dom.mp hdom
                  exact Part.bind_dom.mpr
                    ⟨hserve, ih (List.cons_prefix_cons.mpr ⟨rfl, hpre''⟩)
                      (by simp) hrest⟩

/-! ### Fuel monotonicity

A resolved round is stable under more fuel: the interpreter is
deterministic, and extra fuel is never consumed. -/

/-- The one-step unfolding of `serve`, as an equation. -/
theorem serve_succ (E : DDS (U ⊕ Y) (V ⊕ X)) (R : DDS X Y) (n : ℕ)
    (st : List (U ⊕ Y) × List X) :
    serve E R (n + 1) st =
      if hE : st.1 ∈ dom E then
        Sum.elim
          (fun v => Part.some (v, st))
          (fun x =>
            if hR : st.2 ++ [x] ∈ dom R then
              serve E R n
                (st.1 ++ [Sum.inr (output R (st.2 ++ [x]) hR)], st.2 ++ [x])
            else Part.none)
          (output E st.1 hE)
      else Part.none :=
  rfl

theorem serve_succ_of_dom :
    ∀ {n : ℕ} {st}, (serve E R n st).Dom →
      serve E R (n + 1) st = serve E R n st := by
  intro n
  induction n with
  | zero => exact fun h => h.elim
  | succ n ih =>
      intro st h
      rw [serve_succ] at h
      conv_lhs => rw [serve_succ]
      conv_rhs => rw [serve_succ]
      by_cases hE : st.1 ∈ dom E
      · simp only [dif_pos hE] at h ⊢
        rcases hout : output E st.1 hE with v | x
        · simp only [Sum.elim_inl]
        · simp only [hout, Sum.elim_inr] at h ⊢
          by_cases hR : st.2 ++ [x] ∈ dom R
          · simp only [dif_pos hR] at h ⊢
            exact ih h
          · simp only [dif_neg hR]
      · simp only [dif_neg hE]

theorem serve_mono {n m : ℕ} (hnm : n ≤ m) {st}
    (h : (serve E R n st).Dom) : serve E R m st = serve E R n st := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
      have hd : (serve E R m st).Dom := by rw [ih]; exact h
      rw [serve_succ_of_dom hd, ih]

theorem runAux_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {us : List U} {st}, (runAux E R n us st).Dom →
      runAux E R m us st = runAux E R n us st := by
  intro us
  induction us with
  | nil => exact fun h => h.elim
  | cons u us ih =>
      intro st h
      cases us with
      | nil =>
          rw [runAux_singleton] at h ⊢
          rw [runAux_singleton]
          exact serve_mono hnm h
      | cons u' us' =>
          rw [runAux_cons_cons] at h ⊢
          rw [runAux_cons_cons]
          obtain ⟨hserve, hrest⟩ := Part.bind_dom.mp h
          rw [serve_mono hnm hserve]
          refine Part.ext fun b => ?_
          rw [Part.mem_bind_iff, Part.mem_bind_iff]
          constructor
          · rintro ⟨a, ha, hb⟩
            have hget := Part.get_eq_of_mem ha hserve
            have hda : (runAux E R n (u' :: us') a.2).Dom := by
              rw [← hget]; exact hrest
            exact ⟨a, ha, by rwa [ih hda] at hb⟩
          · rintro ⟨a, ha, hb⟩
            have hget := Part.get_eq_of_mem ha hserve
            have hda : (runAux E R n (u' :: us') a.2).Dom := by
              rw [← hget]; exact hrest
            exact ⟨a, ha, by rwa [ih hda]⟩

/-- Splitting a run at its last query: process the prefix, then one more
round from the reached state. -/
theorem runAux_append (n : ℕ) :
    ∀ {us : List U} (u : U) {st : List (U ⊕ Y) × List X}, us ≠ [] →
      runAux E R n (us ++ [u]) st =
        (runAux E R n us st).bind fun p =>
          serve E R n (p.2.1 ++ [Sum.inl u], p.2.2) := by
  intro us
  induction us with
  | nil => exact fun u st h => absurd rfl h
  | cons v vs ih =>
      intro u st _
      cases vs with
      | nil =>
          rw [List.cons_append, List.nil_append, runAux_cons_cons,
            runAux_singleton]
          exact congrArg _ (funext fun p => runAux_singleton n u p.2)
      | cons w ws =>
          rw [List.cons_append, List.cons_append, runAux_cons_cons,
            runAux_cons_cons, Part.bind_assoc]
          refine congrArg _ (funext fun p => ?_)
          rw [← List.cons_append]
          exact ih u (by simp)

/-- A resolved round leaves the engine history in the engine's domain: the
final answer was the engine's own `inl` move at that history. -/
theorem serve_final_dom :
    ∀ {n : ℕ} {st : List (U ⊕ Y) × List X} {v : V}
      {st' : List (U ⊕ Y) × List X},
      (v, st') ∈ serve E R n st → st'.1 ∈ dom E := by
  intro n
  induction n with
  | zero =>
      intro st v st' h
      exact absurd h (Part.notMem_none _)
  | succ n ih =>
      intro st v st' h
      rw [serve_succ] at h
      by_cases hE : st.1 ∈ dom E
      · rw [dif_pos hE] at h
        rcases hout : output E st.1 hE with w | x
        · rw [hout] at h
          simp only [Sum.elim_inl] at h
          have hst : st' = st := congrArg Prod.snd (Part.mem_some_iff.mp h)
          rw [hst]
          exact hE
        · rw [hout] at h
          simp only [Sum.elim_inr] at h
          by_cases hR : st.2 ++ [x] ∈ dom R
          · rw [dif_pos hR] at h
            exact ih h
          · rw [dif_neg hR] at h
            exact absurd h (Part.notMem_none _)
      · rw [dif_neg hE] at h
        exact absurd h (Part.notMem_none _)

/-- The resource history only grows across a round. -/
theorem serve_rh_prefix :
    ∀ {n : ℕ} {st : List (U ⊕ Y) × List X} {v : V}
      {st' : List (U ⊕ Y) × List X},
      (v, st') ∈ serve E R n st → st.2 <+: st'.2 := by
  intro n
  induction n with
  | zero =>
      intro st v st' h
      exact absurd h (Part.notMem_none _)
  | succ n ih =>
      intro st v st' h
      rw [serve_succ] at h
      by_cases hE : st.1 ∈ dom E
      · rw [dif_pos hE] at h
        rcases hout : output E st.1 hE with w | x
        · rw [hout] at h
          simp only [Sum.elim_inl] at h
          have hst : st' = st := congrArg Prod.snd (Part.mem_some_iff.mp h)
          rw [hst]
        · rw [hout] at h
          simp only [Sum.elim_inr] at h
          by_cases hR : st.2 ++ [x] ∈ dom R
          · rw [dif_pos hR] at h
            exact (List.prefix_append _ _).trans (ih h)
          · rw [dif_neg hR] at h
            exact absurd h (Part.notMem_none _)
      · rw [dif_neg hE] at h
        exact absurd h (Part.notMem_none _)

/-- The final resource history is the original or the last accepted
extension. -/
theorem serve_rh_dom :
    ∀ {n : ℕ} {st : List (U ⊕ Y) × List X} {v : V}
      {st' : List (U ⊕ Y) × List X},
      (v, st') ∈ serve E R n st → st'.2 = st.2 ∨ st'.2 ∈ dom R := by
  intro n
  induction n with
  | zero =>
      intro st v st' h
      exact absurd h (Part.notMem_none _)
  | succ n ih =>
      intro st v st' h
      rw [serve_succ] at h
      by_cases hE : st.1 ∈ dom E
      · rw [dif_pos hE] at h
        rcases hout : output E st.1 hE with w | x
        · rw [hout] at h
          simp only [Sum.elim_inl] at h
          have hst : st' = st := congrArg Prod.snd (Part.mem_some_iff.mp h)
          rw [hst]
          exact Or.inl rfl
        · rw [hout] at h
          simp only [Sum.elim_inr] at h
          by_cases hR : st.2 ++ [x] ∈ dom R
          · rw [dif_pos hR] at h
            rcases ih h with heq | hmem
            · rw [heq]
              exact Or.inr hR
            · exact Or.inr hmem
          · rw [dif_neg hR] at h
            exact absurd h (Part.notMem_none _)
      · rw [dif_neg hE] at h
        exact absurd h (Part.notMem_none _)

/-- A resolved run leaves the engine history in the engine's domain. -/
theorem runAux_final_dom {n : ℕ} :
    ∀ {us : List U} {st : List (U ⊕ Y) × List X} {v : V}
      {st' : List (U ⊕ Y) × List X},
      (v, st') ∈ runAux E R n us st → st'.1 ∈ dom E := by
  intro us
  induction us with
  | nil =>
      intro st v st' h
      exact absurd h (Part.notMem_none _)
  | cons u vs ih =>
      intro st v st' h
      cases vs with
      | nil =>
          rw [runAux_singleton] at h
          exact serve_final_dom h
      | cons w ws =>
          rw [runAux_cons_cons] at h
          obtain ⟨p, _, hmem⟩ := Part.mem_bind_iff.mp h
          exact ih hmem

/-! ### The interpreter on the identity engine

`idEngine` resolves every round in exactly two inner steps: relay the
query, relay the reply. -/

theorem serve_idEngine {R : DDS X Y} (n : ℕ) (eh : List (X ⊕ Y))
    (rh : List X) (x : X) :
    serve idEngine R (n + 2) (eh ++ [Sum.inl x], rh) =
      if hR : rh ++ [x] ∈ dom R then
        Part.some (output R (rh ++ [x]) hR,
          (eh ++ [Sum.inl x, Sum.inr (output R (rh ++ [x]) hR)], rh ++ [x]))
      else Part.none := by
  have hE : eh ++ [Sum.inl x] ∈ dom idEngine := by
    show eh ++ [Sum.inl x] ≠ []
    simp
  rw [serve_succ, dif_pos hE]
  have hout : output idEngine (eh ++ [Sum.inl x]) hE = Sum.inr x := by
    simp [idEngine]
  rw [hout]
  simp only [Sum.elim_inr]
  by_cases hR : rh ++ [x] ∈ dom R
  · rw [dif_pos hR, dif_pos hR]
    have hE' : (eh ++ [Sum.inl x]) ++
        [Sum.inr (output R (rh ++ [x]) hR)] ∈ dom idEngine := by
      show (eh ++ [Sum.inl x]) ++ [Sum.inr (output R (rh ++ [x]) hR)] ≠ []
      simp
    rw [serve_succ, dif_pos hE']
    have hout' : output idEngine ((eh ++ [Sum.inl x]) ++
        [Sum.inr (output R (rh ++ [x]) hR)]) hE' =
        Sum.inl (output R (rh ++ [x]) hR) := by
      simp [idEngine]
    rw [hout']
    simp [List.append_assoc]
  · rw [dif_neg hR, dif_neg hR]

/-- The interpreter's rounds on the identity engine, characterized from a
mere domain fact: the resource answered, and the state advanced by one
query. -/
theorem serve_idEngine_dom {R : DDS X Y} :
    ∀ {n : ℕ} {eh : List (X ⊕ Y)} {rh : List X} {x : X},
      (serve idEngine R n (eh ++ [Sum.inl x], rh)).Dom →
      ∃ hR : rh ++ [x] ∈ dom R,
        serve idEngine R n (eh ++ [Sum.inl x], rh) =
          Part.some (output R (rh ++ [x]) hR,
            (eh ++ [Sum.inl x, Sum.inr (output R (rh ++ [x]) hR)],
              rh ++ [x])) := by
  intro n
  match n with
  | 0 => intro eh rh x h; exact h.elim
  | 1 =>
      intro eh rh x h
      exfalso
      have hE : eh ++ [Sum.inl x] ∈ dom idEngine := by
        show eh ++ [Sum.inl x] ≠ []
        simp
      rw [serve_succ, dif_pos hE] at h
      have hout : output idEngine (eh ++ [Sum.inl x]) hE = Sum.inr x := by
        simp [idEngine]
      rw [hout] at h
      simp only [Sum.elim_inr] at h
      by_cases hR : rh ++ [x] ∈ dom R
      · rw [dif_pos hR] at h
        exact h.elim
      · rw [dif_neg hR] at h
        exact h.elim
  | n + 2 =>
      intro eh rh x h
      rw [serve_idEngine] at h ⊢
      by_cases hR : rh ++ [x] ∈ dom R
      · exact ⟨hR, by rw [dif_pos hR]⟩
      · rw [dif_neg hR] at h
        exact h.elim

/-- Fuel `2` resolves any in-domain outer history against the identity
engine, producing the resource's own answer. -/
theorem runAux_idEngine {R : DDS X Y} :
    ∀ (us : List X), us ≠ [] → ∀ (eh : List (X ⊕ Y)) (rh : List X)
      (h : rh ++ us ∈ dom R),
      ∃ eh', runAux idEngine R 2 us (eh, rh) =
        Part.some (output R (rh ++ us) h, (eh', rh ++ us)) := by
  intro us
  induction us with
  | nil => exact fun h => absurd rfl h
  | cons u us ih =>
      intro _ eh rh h
      cases us with
      | nil =>
          exact ⟨_, by rw [runAux_singleton, serve_idEngine 0 eh rh u,
            dif_pos h]⟩
      | cons u' us' =>
          have hpre : rh ++ [u] ∈ dom R :=
            prefix_closed R ⟨u' :: us', by simp⟩ (by simp) h
          have hh' : (rh ++ [u]) ++ (u' :: us') ∈ dom R := by
            simpa [List.append_assoc] using h
          obtain ⟨eh', heq⟩ := ih (by simp)
            (eh ++ [Sum.inl u, Sum.inr (output R (rh ++ [u]) hpre)])
            (rh ++ [u]) hh'
          refine ⟨eh', ?_⟩
          rw [runAux_cons_cons, serve_idEngine 0 eh rh u, dif_pos hpre,
            Part.bind_some, heq]
          simp [List.append_assoc]

/-- Conversely, any resolved run against the identity engine certifies the
outer history in the resource's domain. -/
theorem runAux_idEngine_dom {R : DDS X Y} {n : ℕ} :
    ∀ (us : List X) {eh : List (X ⊕ Y)} {rh : List X},
      (runAux idEngine R n us (eh, rh)).Dom → rh ++ us ∈ dom R := by
  intro us
  induction us with
  | nil => exact fun h => h.elim
  | cons u us ih =>
      intro eh rh h
      cases us with
      | nil =>
          rw [runAux_singleton] at h
          obtain ⟨hR, _⟩ := serve_idEngine_dom h
          exact hR
      | cons u' us' =>
          rw [runAux_cons_cons] at h
          obtain ⟨hserve, hrest⟩ := Part.bind_dom.mp h
          obtain ⟨hR, heq⟩ := serve_idEngine_dom hserve
          rw [Part.get_eq_of_mem (by rw [heq]; exact Part.mem_some _) hserve]
            at hrest
          have := ih hrest
          simpa [List.append_assoc] using this

end Connect

/-- Close a raw system to a valid one: defined exactly where every
nonempty prefix of the history is defined.  The general combinator behind
engine constructions whose local rule is not automatically prefix-closed. -/
def validate (S : Raw X Y) : DDS X Y :=
  ⟨fun l =>
    ⟨l ≠ [] ∧ ∀ l', l' <+: l → l' ≠ [] → (S l').Dom,
     fun h => (S l).get (h.2 l (List.prefix_refl l) h.1)⟩, by
    constructor
    · exact fun h => h.1 rfl
    · intro l₁ l₂ hpre hne hdom
      exact ⟨hne, fun l' hl' hne' => hdom.2 l' (hl'.trans hpre) hne'⟩⟩

theorem mem_dom_validate (S : Raw X Y) (l : List X) :
    l ∈ dom (validate S) ↔
      l ≠ [] ∧ ∀ l', l' <+: l → l' ≠ [] → (S l').Dom :=
  Iff.rfl

theorem output_validate (S : Raw X Y) (l : List X)
    (h : l ∈ dom (validate S)) :
    output (validate S) l h = (S l).get (h.2 l (List.prefix_refl l) h.1) :=
  rfl

theorem output_validate_of_eq_some {S : Raw X Y} {l : List X}
    (h : l ∈ dom (validate S)) {y : Y} (hy : S l = Part.some y) :
    output (validate S) l h = y := by
  rw [output_validate]
  exact Part.get_eq_of_mem (by rw [hy]; exact Part.mem_some _) _

/-- Extending a validated history at the frontier: the old history's
certificates carry over, so only the new entry is tested. -/
theorem mem_dom_validate_concat {S : Raw X Y} {l : List X}
    (hl : l = [] ∨ l ∈ dom (validate S)) (e : X) :
    l ++ [e] ∈ dom (validate S) ↔ (S (l ++ [e])).Dom := by
  rw [mem_dom_validate]
  constructor
  · exact fun h => h.2 _ (List.prefix_refl _) h.1
  · intro hS
    refine ⟨by simp, fun l' hl' hne => ?_⟩
    rcases List.prefix_concat_iff.mp hl' with rfl | hl'
    · exact hS
    · rcases hl with rfl | hdom
      · exact absurd (List.prefix_nil.mp hl') hne
      · exact hdom.2 l' hl' hne

/-- **`connect`** — the trace/feedback generator: interpret the engine's
requests against the resource, exposing only the outer face.  A history is
in the domain exactly when some fuel resolves every round (stabilization,
as for `tr`); the output is the last round's outer answer. -/
def connect (E : DDS (U ⊕ Y) (V ⊕ X)) (R : DDS X Y) : DDS U V :=
  ⟨fun us =>
    ⟨∃ n, (Connect.runAux E R n us ([], [])).Dom,
     fun h =>
       ((Connect.runAux E R (Nat.find h) us ([], [])).get
         (Nat.find_spec h)).1⟩, by
    constructor
    · rintro ⟨n, h⟩
      exact h
    · intro us₁ us₂ hpre hne hdom
      obtain ⟨n, hn⟩ := hdom
      exact ⟨n, Connect.runAux_dom_prefix hpre hne hn⟩⟩

/-- The domain of `connect`, by construction: some fuel resolves the
history from the empty state. -/
theorem mem_dom_connect_iff (E : DDS (U ⊕ Y) (V ⊕ X)) (R : DDS X Y)
    (us : List U) :
    us ∈ dom (connect E R) ↔
      ∃ n, (Connect.runAux E R n us ([], [])).Dom :=
  Iff.rfl

/-- **The identity receipt** — MauRen16 §3.3's `id ∈ Σ`, computed: closing
the loop with the relay engine changes nothing.  The sanity gate for the
interpreter: `connect` computes exactly the interaction it claims to. -/
theorem connect_idEngine (R : DDS X Y) :
    connect idEngine R = R := by
  apply Subtype.ext
  funext us
  refine Part.ext' ?_ ?_
  · constructor
    · rintro ⟨n, hn⟩
      cases us with
      | nil => exact hn.elim
      | cons u us' => exact Connect.runAux_idEngine_dom (u :: us') hn
    · intro h
      have hne : us ≠ [] := fun hnil => empty_not_mem R (hnil ▸ h)
      obtain ⟨eh', heq⟩ := Connect.runAux_idEngine us hne [] [] h
      exact ⟨2, by rw [heq]; trivial⟩
  · intro h₁ h₂
    have hne : us ≠ [] := fun hnil => empty_not_mem R (hnil ▸ h₂)
    obtain ⟨eh', heq⟩ := Connect.runAux_idEngine us hne [] [] h₂
    have h2dom : (Connect.runAux idEngine R 2 us ([], [])).Dom := by
      rw [heq]; trivial
    have hd₀ : (Connect.runAux idEngine R (Nat.find h₁) us ([], [])).Dom :=
      Nat.find_spec h₁
    have hmax : Connect.runAux idEngine R (Nat.find h₁) us ([], []) =
        Connect.runAux idEngine R 2 us ([], []) := by
      rw [← Connect.runAux_mono (le_max_left (Nat.find h₁) 2) hd₀,
        Connect.runAux_mono (le_max_right (Nat.find h₁) 2) h2dom]
    have hmem : (output R us h₂, (eh', us)) ∈
        Connect.runAux idEngine R (Nat.find h₁) us ([], []) := by
      rw [hmax, heq]
      exact Part.mem_some _
    show ((Connect.runAux idEngine R (Nat.find h₁) us ([], [])).get
      (Nat.find_spec h₁)).1 = (R.1 us).get h₂
    rw [Part.get_eq_of_mem hmem (Nat.find_spec h₁)]
    rfl

end

/-! ## Interface-local attachment

Attaching an engine at **one** interface of a tagged resource: the
"identity elsewhere" lift (Jost's `α^i = π^γ` factorization) followed by
`connect`.  The lifted engine relays foreign traffic verbatim and defers
`i`-traffic to `E`, evaluated on the `i`-projection of its history; reply
attribution is by the tag of the last outer query, which is exact on every
history the interpreter builds and junk elsewhere. -/

noncomputable section

open Classical

universe u v w

variable {P : Type u} {A : Type v} {B : Type w}

/-- The interface owning the pending conversation: the tag of the last
outer query in a lifted-engine history. -/
def lastTag : List ((P × A) ⊕ B) → Option P :=
  List.foldl
    (fun acc e => match e with
      | Sum.inl (p, _) => some p
      | Sum.inr _ => acc)
    none

@[simp]
theorem lastTag_append_inl (h : List ((P × A) ⊕ B)) (p : P) (a : A) :
    lastTag (h ++ [Sum.inl (p, a)]) = some p := by
  simp [lastTag, List.foldl_append]

@[simp]
theorem lastTag_append_inr (h : List ((P × A) ⊕ B)) (b : B) :
    lastTag (h ++ [Sum.inr b]) = lastTag h := by
  simp [lastTag, List.foldl_append]

/-- One step of the `i`-projection: keep `i`-queries (detagged) and the
replies of `i`-mode segments. -/
def eProjStep (i : P) (acc : List (A ⊕ B) × Option P) :
    ((P × A) ⊕ B) → List (A ⊕ B) × Option P
  | Sum.inl (p, a) => (if p = i then acc.1 ++ [Sum.inl a] else acc.1, some p)
  | Sum.inr b => (if acc.2 = some i then acc.1 ++ [Sum.inr b] else acc.1, acc.2)

/-- The `i`-projection of a lifted-engine history: what the engine at
interface `i` has seen. -/
def eProj (i : P) (h : List ((P × A) ⊕ B)) : List (A ⊕ B) :=
  (h.foldl (eProjStep i) ([], none)).1

theorem eProj_state_snd (i : P) (h : List ((P × A) ⊕ B)) :
    (h.foldl (eProjStep i) ([], none)).2 = lastTag h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h e ih =>
      cases e with
      | inl pa => simp [List.foldl_append, eProjStep, lastTag]
      | inr b => simp [List.foldl_append, eProjStep, ih]

@[simp]
theorem eProj_append_inl (i : P) (h : List ((P × A) ⊕ B)) (p : P) (a : A) :
    eProj i (h ++ [Sum.inl (p, a)]) =
      if p = i then eProj i h ++ [Sum.inl a] else eProj i h := by
  simp [eProj, List.foldl_append, eProjStep]

@[simp]
theorem eProj_append_inr (i : P) (h : List ((P × A) ⊕ B)) (b : B) :
    eProj i (h ++ [Sum.inr b]) =
      if lastTag h = some i then eProj i h ++ [Sum.inr b] else eProj i h := by
  simp [eProj, List.foldl_append, eProjStep, eProj_state_snd]

/-- The local rule of the lifted engine: relay foreign queries down and
foreign replies out; defer `i`-traffic to `E` on the `i`-projection,
tagging `E`'s requests with `i`.  Not prefix-closed on junk histories —
`liftAt` closes it. -/
def liftAtRaw (i : P) (E : DDS (A ⊕ B) (B ⊕ A)) :
    Raw ((P × A) ⊕ B) (B ⊕ (P × A)) := fun h =>
  match h.getLast? with
  | none => Part.none
  | some (Sum.inl (p, a)) =>
      if p = i then (E.1 (eProj i h)).map (Sum.map id fun a' => (i, a'))
      else Part.some (Sum.inr (p, a))
  | some (Sum.inr b) =>
      if lastTag h = some i then
        (E.1 (eProj i h)).map (Sum.map id fun a' => (i, a'))
      else Part.some (Sum.inl b)

/-- The "identity elsewhere" lift of a single-interface engine to the full
tagged alphabet. -/
def liftAt (i : P) (E : DDS (A ⊕ B) (B ⊕ A)) :
    DDS ((P × A) ⊕ B) (B ⊕ (P × A)) :=
  validate (liftAtRaw i E)

/-- **The third generator family**: attach an engine at one interface —
the lift, then the trace. -/
def attachEngine (i : P) (E : DDS (A ⊕ B) (B ⊕ A)) (R : Resource P A B) :
    Resource P A B :=
  connect (liftAt i E) R

/-! ### The local rule at the frontier

`liftAtRaw` dispatches on the last entry of its history; on frontier
extensions the dispatch computes, and in `i`-mode it is `E` on the
projection whatever the frontier entry is. -/

/-- Foreign queries relay down unconditionally. -/
theorem liftAtRaw_concat_foreign {i p : P} (hp : p ≠ i)
    (E : DDS (A ⊕ B) (B ⊕ A)) (h : List ((P × A) ⊕ B)) (a : A) :
    liftAtRaw i E (h ++ [Sum.inl (p, a)]) = Part.some (Sum.inr (p, a)) := by
  simp [liftAtRaw, hp]

/-- Queries at `i` go to the engine, on the extended projection. -/
theorem liftAtRaw_concat_i (i : P) (E : DDS (A ⊕ B) (B ⊕ A))
    (h : List ((P × A) ⊕ B)) (a : A) :
    liftAtRaw i E (h ++ [Sum.inl (i, a)]) =
      (E.1 (eProj i h ++ [Sum.inl a])).map
        (Sum.map id fun a' => (i, a')) := by
  simp [liftAtRaw]

/-- Replies in `i`-mode go to the engine, on the extended projection. -/
theorem liftAtRaw_concat_reply_i {i : P} {h : List ((P × A) ⊕ B)}
    (htag : lastTag h = some i) (E : DDS (A ⊕ B) (B ⊕ A)) (b : B) :
    liftAtRaw i E (h ++ [Sum.inr b]) =
      (E.1 (eProj i h ++ [Sum.inr b])).map
        (Sum.map id fun a' => (i, a')) := by
  simp [liftAtRaw, htag]

/-- Replies out of `i`-mode relay out unconditionally. -/
theorem liftAtRaw_concat_reply_off {i : P} {h : List ((P × A) ⊕ B)}
    (htag : lastTag h ≠ some i) (E : DDS (A ⊕ B) (B ⊕ A)) (b : B) :
    liftAtRaw i E (h ++ [Sum.inr b]) = Part.some (Sum.inl b) := by
  simp [liftAtRaw, htag]

/-- In `i`-mode — the last outer query was at `i` — the lifted engine is
`E` on the projection, whatever the frontier entry. -/
theorem liftAtRaw_of_lastTag (i : P) (E : DDS (A ⊕ B) (B ⊕ A))
    {h : List ((P × A) ⊕ B)} (hne : h ≠ []) (htag : lastTag h = some i) :
    liftAtRaw i E h =
      (E.1 (eProj i h)).map (Sum.map id fun a' => (i, a')) := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, e, rfl⟩
  · exact absurd rfl hne
  · rw [List.concat_eq_append] at htag ⊢
    rcases e with ⟨p, a⟩ | b
    · have hpi : p = i := by simpa using htag
      subst hpi
      rw [liftAtRaw_concat_i]
      simp
    · have htag₀ : lastTag h₀ = some i := by simpa using htag
      rw [liftAtRaw_concat_reply_i htag₀]
      simp [htag₀]

/-- The lifted engine's domain at a frontier extension, given a coherent
past: only the frontier entry is tested. -/
theorem mem_dom_liftAt_concat {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {eh : List ((P × A) ⊕ B)} (hok : eh = [] ∨ eh ∈ dom (liftAt i E))
    (e : (P × A) ⊕ B) :
    eh ++ [e] ∈ dom (liftAt i E) ↔ (liftAtRaw i E (eh ++ [e])).Dom :=
  mem_dom_validate_concat hok e

/-! ### The tagged engine

The `i`-mode of the lifted engine, extracted: `E` with its requests
pre-tagged at `i`, runnable directly against the resource. -/

/-- The engine with its requests pre-tagged at `i`. -/
def tagAt (i : P) (E : DDS (A ⊕ B) (B ⊕ A)) : DDS (A ⊕ B) (B ⊕ (P × A)) :=
  relabel id (Sum.map id fun a' => (i, a')) E

@[simp]
theorem mem_dom_tagAt (i : P) (E : DDS (A ⊕ B) (B ⊕ A))
    (l : List (A ⊕ B)) : l ∈ dom (tagAt i E) ↔ l ∈ dom E := by
  simp only [tagAt]
  rw [mem_dom_relabel, List.map_id]

theorem output_tagAt (i : P) (E : DDS (A ⊕ B) (B ⊕ A))
    {l : List (A ⊕ B)} (h : l ∈ dom (tagAt i E)) (hE : l ∈ dom E) :
    output (tagAt i E) l h =
      Sum.map id (fun a' => (i, a')) (output E l hE) := by
  simp only [tagAt]
  rw [output_relabel]
  exact congrArg _ (output_congr E (List.map_id l) _ hE)

/-! ### The round receipts

The interpreter on the lifted engine, characterized round by round: a
foreign query resolves in two steps against the resource (the
`serve_idEngine` shape); an `i`-mode round is the tagged engine's round on
the projection, transported by one `Part.map` equation. -/

/-- The foreign round: a query at `p ≠ i` passes through the lifted engine
in two steps — relay the query, relay the reply. -/
theorem serve_liftAt_foreign {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} (n : ℕ) {eh : List ((P × A) ⊕ B)}
    (hok : eh = [] ∨ eh ∈ dom (liftAt i E)) {p : P} (hp : p ≠ i) (a : A)
    (rh : List (P × A)) :
    Connect.serve (liftAt i E) T (n + 2) (eh ++ [Sum.inl (p, a)], rh) =
      if hT : rh ++ [(p, a)] ∈ dom T then
        Part.some (output T (rh ++ [(p, a)]) hT,
          (eh ++ [Sum.inl (p, a),
            Sum.inr (output T (rh ++ [(p, a)]) hT)],
            rh ++ [(p, a)]))
      else Part.none := by
  have hE : eh ++ [Sum.inl (p, a)] ∈ dom (liftAt i E) :=
    (mem_dom_liftAt_concat hok _).mpr
      (by rw [liftAtRaw_concat_foreign hp]; trivial)
  rw [Connect.serve_succ, dif_pos hE]
  have hout : output (liftAt i E) (eh ++ [Sum.inl (p, a)]) hE =
      Sum.inr (p, a) :=
    output_validate_of_eq_some hE (liftAtRaw_concat_foreign hp E eh a)
  rw [hout]
  simp only [Sum.elim_inr]
  by_cases hT : rh ++ [(p, a)] ∈ dom T
  · rw [dif_pos hT, dif_pos hT]
    have htag : lastTag (eh ++ [Sum.inl (p, a)]) ≠ some i := by
      simp [hp]
    have hraw := liftAtRaw_concat_reply_off htag E
      (output T (rh ++ [(p, a)]) hT)
    have hE' : (eh ++ [Sum.inl (p, a)]) ++
        [Sum.inr (output T (rh ++ [(p, a)]) hT)] ∈ dom (liftAt i E) :=
      (mem_dom_liftAt_concat (Or.inr hE) _).mpr (by rw [hraw]; trivial)
    rw [Connect.serve_succ, dif_pos hE']
    have hout' : output (liftAt i E) _ hE' =
        Sum.inl (output T (rh ++ [(p, a)]) hT) :=
      output_validate_of_eq_some hE' hraw
    rw [hout']
    simp [List.append_assoc]
  · rw [dif_neg hT, dif_neg hT]

/-- A resolved foreign round, characterized from a mere domain fact. -/
theorem serve_liftAt_foreign_dom {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} :
    ∀ {n : ℕ} {eh : List ((P × A) ⊕ B)},
      (eh = [] ∨ eh ∈ dom (liftAt i E)) → ∀ {p : P}, p ≠ i → ∀ {a : A}
      {rh : List (P × A)},
      (Connect.serve (liftAt i E) T n (eh ++ [Sum.inl (p, a)], rh)).Dom →
      ∃ hT : rh ++ [(p, a)] ∈ dom T,
        Connect.serve (liftAt i E) T n (eh ++ [Sum.inl (p, a)], rh) =
          Part.some (output T (rh ++ [(p, a)]) hT,
            (eh ++ [Sum.inl (p, a),
              Sum.inr (output T (rh ++ [(p, a)]) hT)],
              rh ++ [(p, a)])) := by
  intro n
  match n with
  | 0 =>
      intro eh hok p hp a rh h
      exact h.elim
  | 1 =>
      intro eh hok p hp a rh h
      exfalso
      have hE : eh ++ [Sum.inl (p, a)] ∈ dom (liftAt i E) :=
        (mem_dom_liftAt_concat hok _).mpr
          (by rw [liftAtRaw_concat_foreign hp]; trivial)
      rw [Connect.serve_succ, dif_pos hE] at h
      have hout : output (liftAt i E) (eh ++ [Sum.inl (p, a)]) hE =
          Sum.inr (p, a) :=
        output_validate_of_eq_some hE (liftAtRaw_concat_foreign hp E eh a)
      rw [hout] at h
      simp only [Sum.elim_inr] at h
      by_cases hT : rh ++ [(p, a)] ∈ dom T
      · rw [dif_pos hT] at h
        exact h.elim
      · rw [dif_neg hT] at h
        exact h.elim
  | n + 2 =>
      intro eh hok p hp a rh h
      rw [serve_liftAt_foreign n hok hp a rh] at h ⊢
      by_cases hT : rh ++ [(p, a)] ∈ dom T
      · exact ⟨hT, by rw [dif_pos hT]⟩
      · rw [dif_neg hT] at h
        exact h.elim

/-- **The `i`-mode receipt**: from any `i`-mode state, the lifted engine's
round is the tagged engine's round on the projection, transported by one
`Part.map` equation. -/
theorem serve_liftAt_i {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} :
    ∀ (n : ℕ) {eh₀ : List ((P × A) ⊕ B)} {e : (P × A) ⊕ B}
      {rh : List (P × A)},
      (eh₀ = [] ∨ eh₀ ∈ dom (liftAt i E)) →
      lastTag (eh₀ ++ [e]) = some i →
      Connect.serve (tagAt i E) T n (eProj i (eh₀ ++ [e]), rh) =
        (Connect.serve (liftAt i E) T n (eh₀ ++ [e], rh)).map
          (fun q => (q.1, (eProj i q.2.1, q.2.2))) := by
  intro n
  induction n with
  | zero =>
      intro eh₀ e rh hok htag
      show Part.none = Part.map _ Part.none
      simp
  | succ n ih =>
      intro eh₀ e rh hok htag
      have hne : eh₀ ++ [e] ≠ [] := by simp
      have hraw : liftAtRaw i E (eh₀ ++ [e]) =
          (E.1 (eProj i (eh₀ ++ [e]))).map (Sum.map id fun a' => (i, a')) :=
        liftAtRaw_of_lastTag i E hne htag
      have hdomiff : eh₀ ++ [e] ∈ dom (liftAt i E) ↔
          eProj i (eh₀ ++ [e]) ∈ dom E := by
        rw [mem_dom_liftAt_concat hok e, hraw]
        exact Iff.rfl
      rw [Connect.serve_succ, Connect.serve_succ]
      by_cases hE : eProj i (eh₀ ++ [e]) ∈ dom E
      · have hEl : eh₀ ++ [e] ∈ dom (liftAt i E) := hdomiff.mpr hE
        have hEt : eProj i (eh₀ ++ [e]) ∈ dom (tagAt i E) :=
          (mem_dom_tagAt i E _).mpr hE
        rw [dif_pos hEt, dif_pos hEl]
        have houtL : output (liftAt i E) (eh₀ ++ [e]) hEl =
            Sum.map id (fun a' => (i, a'))
              (output E (eProj i (eh₀ ++ [e])) hE) := by
          apply output_validate_of_eq_some
          rw [hraw]
          exact Part.eq_some_iff.mpr (Part.mem_map _ (Part.get_mem hE))
        have houtT : output (tagAt i E) (eProj i (eh₀ ++ [e])) hEt =
            Sum.map id (fun a' => (i, a'))
              (output E (eProj i (eh₀ ++ [e])) hE) :=
          output_tagAt i E hEt hE
        rw [houtL, houtT]
        rcases hout : output E (eProj i (eh₀ ++ [e])) hE with b | a'
        · simp
        · simp only [Sum.map_inr, Sum.elim_inr]
          by_cases hR : rh ++ [(i, a')] ∈ dom T
          · rw [dif_pos hR, dif_pos hR]
            have hstep := ih (eh₀ := eh₀ ++ [e])
              (e := Sum.inr (output T (rh ++ [(i, a')]) hR))
              (rh := rh ++ [(i, a')]) (Or.inr hEl)
              (by rw [lastTag_append_inr]; exact htag)
            rw [eProj_append_inr, if_pos htag] at hstep
            exact hstep
          · rw [dif_neg hR, dif_neg hR]
            show Part.none = Part.map _ Part.none
            simp
      · rw [dif_neg (fun hc => hE ((mem_dom_tagAt i E _).mp hc)),
          dif_neg (fun hc => hE (hdomiff.mp hc))]
        show Part.none = Part.map _ Part.none
        simp

/-! ### Reached states and the step recurrences

The interpreter state an attachment has reached on an outer history —
fuel-independent by `runAux_mono` — and the attachment's two step
recurrences against it: a foreign extension consults the resource once and
passes through; an own-interface extension is the tagged engine's round on
the projection. -/

/-- The interpreter state reached on an outer history: nothing yet, or the
final state of a resolved run. -/
def AttachState (W : DDS ((P × A) ⊕ B) (B ⊕ (P × A))) (T : Resource P A B)
    (us : List (P × A)) (st : List ((P × A) ⊕ B) × List (P × A)) : Prop :=
  (us = [] ∧ st = ([], [])) ∨
    ∃ n b, (b, st) ∈ Connect.runAux W T n us ([], [])

theorem attachState_nil (W : DDS ((P × A) ⊕ B) (B ⊕ (P × A)))
    (T : Resource P A B) : AttachState W T [] ([], []) :=
  Or.inl ⟨rfl, rfl⟩

/-- Reached engine histories are coherent: the last round ended on the
engine's own move. -/
theorem AttachState.engine_dom {W : DDS ((P × A) ⊕ B) (B ⊕ (P × A))}
    {T : Resource P A B} {us : List (P × A)}
    {st : List ((P × A) ⊕ B) × List (P × A)}
    (h : AttachState W T us st) : st.1 = [] ∨ st.1 ∈ dom W := by
  rcases h with ⟨_, rfl⟩ | ⟨n, b, hmem⟩
  · exact Or.inl rfl
  · exact Or.inr (Connect.runAux_final_dom hmem)

/-- Any resolved run computes the connected system's output. -/
theorem output_connect_eq {W : DDS ((P × A) ⊕ B) (B ⊕ (P × A))}
    {T : Resource P A B} {us : List (P × A)} {n : ℕ} {b : B}
    {st : List ((P × A) ⊕ B) × List (P × A)}
    (hmem : (b, st) ∈ Connect.runAux W T n us ([], []))
    (h : us ∈ dom (connect W T)) : output (connect W T) us h = b := by
  have hd : (Connect.runAux W T n us ([], [])).Dom :=
    Part.dom_iff_mem.mpr ⟨_, hmem⟩
  have hmem' : (b, st) ∈ Connect.runAux W T (Nat.find h) us ([], []) := by
    rw [← Connect.runAux_mono (le_max_left (Nat.find h) n) (Nat.find_spec h),
      Connect.runAux_mono (le_max_right (Nat.find h) n) hd]
    exact hmem
  show ((Connect.runAux W T (Nat.find h) us ([], [])).get
    (Nat.find_spec h)).1 = b
  rw [Part.get_eq_of_mem hmem' (Nat.find_spec h)]

/-- From a resolved extended run, the last round's `serve` resolves from
the reached state. -/
theorem attachState_serve_dom {W : DDS ((P × A) ⊕ B) (B ⊕ (P × A))}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)} (hst : AttachState W T us (eh, rh)) {x : P × A}
    {N : ℕ} (hN : (Connect.runAux W T N (us ++ [x]) ([], [])).Dom) :
    ∃ M, (Connect.serve W T M (eh ++ [Sum.inl x], rh)).Dom := by
  rcases hst with ⟨rfl, heq₀⟩ | ⟨n₀, b₀, hmem⟩
  · simp only [Prod.mk.injEq] at heq₀
    obtain ⟨rfl, rfl⟩ := heq₀
    rw [List.nil_append, Connect.runAux_singleton] at hN
    exact ⟨N, hN⟩
  · have hus : us ≠ [] := by
      rintro rfl
      exact absurd hmem (Part.notMem_none _)
    rw [Connect.runAux_append N _ hus] at hN
    obtain ⟨hd₁, hd₂⟩ := Part.bind_dom.mp hN
    have hd : (Connect.runAux W T n₀ us ([], [])).Dom :=
      Part.dom_iff_mem.mpr ⟨_, hmem⟩
    have hmemN : (b₀, (eh, rh)) ∈ Connect.runAux W T N us ([], []) := by
      rw [← Connect.runAux_mono (le_max_left N n₀) hd₁,
        Connect.runAux_mono (le_max_right N n₀) hd]
      exact hmem
    have hval : (Connect.runAux W T N us ([], [])).get hd₁ = (b₀, (eh, rh)) :=
      Part.get_eq_of_mem hmemN hd₁
    rw [hval] at hd₂
    exact ⟨N, hd₂⟩

/-- The foreign step, forward: from a reached state, a foreign extension
resolves to the resource's answer. -/
theorem attachState_foreign_mem {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) {p : P} (hp : p ≠ i)
    {a : A} (hT : rh ++ [(p, a)] ∈ dom T) :
    ∃ n, (output T (rh ++ [(p, a)]) hT,
        (eh ++ [Sum.inl (p, a), Sum.inr (output T (rh ++ [(p, a)]) hT)],
          rh ++ [(p, a)])) ∈
      Connect.runAux (liftAt i E) T n (us ++ [(p, a)]) ([], []) := by
  have hok : eh = [] ∨ eh ∈ dom (liftAt i E) := hst.engine_dom
  rcases hst with ⟨rfl, heq₀⟩ | ⟨n, b, hmem⟩
  · simp only [Prod.mk.injEq] at heq₀
    obtain ⟨rfl, rfl⟩ := heq₀
    refine ⟨2, ?_⟩
    show (output T ([] ++ [(p, a)]) hT,
        ([] ++ [Sum.inl (p, a), Sum.inr (output T ([] ++ [(p, a)]) hT)],
          [] ++ [(p, a)])) ∈
      Connect.serve (liftAt i E) T 2
        (([] : List ((P × A) ⊕ B)) ++ [Sum.inl (p, a)], ([] : List (P × A)))
    rw [serve_liftAt_foreign 0 (Or.inl rfl) hp a [], dif_pos hT]
    exact Part.mem_some _
  · have hus : us ≠ [] := by
      rintro rfl
      exact absurd hmem (Part.notMem_none _)
    have hd : (Connect.runAux (liftAt i E) T n us ([], [])).Dom :=
      Part.dom_iff_mem.mpr ⟨_, hmem⟩
    refine ⟨n + 2, ?_⟩
    rw [Connect.runAux_append (n + 2) _ hus,
      Connect.runAux_mono (Nat.le_add_right n 2) hd]
    refine Part.mem_bind_iff.mpr ⟨(b, (eh, rh)), hmem, ?_⟩
    show _ ∈ Connect.serve (liftAt i E) T (n + 2) (eh ++ [Sum.inl (p, a)], rh)
    rw [serve_liftAt_foreign n hok hp a rh, dif_pos hT]
    exact Part.mem_some _

/-- The foreign step, backward: if the extension resolves, the resource
accepted the query. -/
theorem attachState_foreign_dom {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) {p : P} (hp : p ≠ i)
    {a : A} (h : us ++ [(p, a)] ∈ dom (connect (liftAt i E) T)) :
    rh ++ [(p, a)] ∈ dom T := by
  have hok : eh = [] ∨ eh ∈ dom (liftAt i E) := hst.engine_dom
  obtain ⟨N, hN⟩ := (mem_dom_connect_iff _ _ _).mp h
  obtain ⟨M, hM⟩ := attachState_serve_dom hst hN
  obtain ⟨hT, -⟩ := serve_liftAt_foreign_dom hok hp hM
  exact hT

theorem attachState_foreign_dom_iff {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) {p : P} (hp : p ≠ i)
    (a : A) :
    us ++ [(p, a)] ∈ dom (connect (liftAt i E) T) ↔
      rh ++ [(p, a)] ∈ dom T := by
  constructor
  · exact attachState_foreign_dom hst hp
  · intro hT
    obtain ⟨n, hmem⟩ := attachState_foreign_mem hst hp hT
    exact (mem_dom_connect_iff _ _ _).mpr ⟨n, Part.dom_iff_mem.mpr ⟨_, hmem⟩⟩

theorem attachState_foreign_output {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) {p : P} (hp : p ≠ i)
    {a : A} (hT : rh ++ [(p, a)] ∈ dom T)
    (h : us ++ [(p, a)] ∈ dom (connect (liftAt i E) T)) :
    output (connect (liftAt i E) T) (us ++ [(p, a)]) h =
      output T (rh ++ [(p, a)]) hT := by
  obtain ⟨n, hmem⟩ := attachState_foreign_mem hst hp hT
  exact output_connect_eq hmem h

theorem attachState_foreign_state {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) {p : P} (hp : p ≠ i)
    {a : A} (hT : rh ++ [(p, a)] ∈ dom T) :
    AttachState (liftAt i E) T (us ++ [(p, a)])
      (eh ++ [Sum.inl (p, a), Sum.inr (output T (rh ++ [(p, a)]) hT)],
        rh ++ [(p, a)]) := by
  obtain ⟨n, hmem⟩ := attachState_foreign_mem hst hp hT
  exact Or.inr ⟨n, _, hmem⟩

/-- The own-interface step, forward: a resolved tagged-engine round
transports to a resolved run of the attachment. -/
theorem attachState_own_mem {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) (a : A) {n : ℕ} {b : B}
    {conv' : List (A ⊕ B)} {rh' : List (P × A)}
    (hserve : (b, (conv', rh')) ∈
      Connect.serve (tagAt i E) T n (eProj i eh ++ [Sum.inl a], rh)) :
    ∃ eh' m, (b, (eh', rh')) ∈
        Connect.runAux (liftAt i E) T m (us ++ [(i, a)]) ([], []) ∧
      eProj i eh' = conv' := by
  have hok : eh = [] ∨ eh ∈ dom (liftAt i E) := hst.engine_dom
  have hmap := serve_liftAt_i (i := i) (E := E) (T := T) n
    (eh₀ := eh) (e := Sum.inl (i, a)) (rh := rh) hok (by simp)
  rw [show eProj i (eh ++ [Sum.inl (i, a)]) = eProj i eh ++ [Sum.inl a]
    by simp] at hmap
  rw [hmap] at hserve
  obtain ⟨⟨b₂, eh', rh₂⟩, hq, heq⟩ := (Part.mem_map_iff _).mp hserve
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, hconv, rfl⟩ := heq
  rcases hst with ⟨rfl, heq₀⟩ | ⟨n₀, b₀, hmem⟩
  · simp only [Prod.mk.injEq] at heq₀
    obtain ⟨rfl, rfl⟩ := heq₀
    refine ⟨eh', n, ?_, hconv⟩
    rw [List.nil_append, Connect.runAux_singleton]
    show _ ∈ Connect.serve (liftAt i E) T n
      (([] : List ((P × A) ⊕ B)) ++ [Sum.inl (i, a)], ([] : List (P × A)))
    exact hq
  · have hus : us ≠ [] := by
      rintro rfl
      exact absurd hmem (Part.notMem_none _)
    have hd : (Connect.runAux (liftAt i E) T n₀ us ([], [])).Dom :=
      Part.dom_iff_mem.mpr ⟨_, hmem⟩
    refine ⟨eh', max n₀ n, ?_, hconv⟩
    rw [Connect.runAux_append _ _ hus,
      Connect.runAux_mono (le_max_left n₀ n) hd]
    refine Part.mem_bind_iff.mpr ⟨(b₀, (eh, rh)), hmem, ?_⟩
    show _ ∈ Connect.serve (liftAt i E) T (max n₀ n)
      (eh ++ [Sum.inl (i, a)], rh)
    rw [Connect.serve_mono (le_max_right n₀ n)
      (Part.dom_iff_mem.mpr ⟨_, hq⟩)]
    exact hq

theorem attachState_own_dom_iff {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) (a : A) :
    us ++ [(i, a)] ∈ dom (connect (liftAt i E) T) ↔
      ∃ n, (Connect.serve (tagAt i E) T n
        (eProj i eh ++ [Sum.inl a], rh)).Dom := by
  have hok : eh = [] ∨ eh ∈ dom (liftAt i E) := hst.engine_dom
  have hmapAll : ∀ n, Connect.serve (tagAt i E) T n
      (eProj i eh ++ [Sum.inl a], rh) =
      (Connect.serve (liftAt i E) T n (eh ++ [Sum.inl (i, a)], rh)).map
        (fun q => (q.1, (eProj i q.2.1, q.2.2))) := fun n => by
    have hmap := serve_liftAt_i (i := i) (E := E) (T := T) n
      (eh₀ := eh) (e := Sum.inl (i, a)) (rh := rh) hok (by simp)
    rwa [show eProj i (eh ++ [Sum.inl (i, a)]) = eProj i eh ++ [Sum.inl a]
      by simp] at hmap
  constructor
  · intro h
    obtain ⟨N, hN⟩ := (mem_dom_connect_iff _ _ _).mp h
    obtain ⟨M, hM⟩ := attachState_serve_dom hst hN
    refine ⟨M, ?_⟩
    rw [hmapAll M]
    exact hM
  · rintro ⟨n, hn⟩
    have hn' : (Connect.serve (liftAt i E) T n
        (eh ++ [Sum.inl (i, a)], rh)).Dom := by
      rw [hmapAll n] at hn
      exact hn
    obtain ⟨q, hq⟩ := Part.dom_iff_mem.mp hn'
    have hq' : ((q.1, (eProj i q.2.1, q.2.2)) : B × _) ∈
        Connect.serve (tagAt i E) T n (eProj i eh ++ [Sum.inl a], rh) := by
      rw [hmapAll n]
      exact (Part.mem_map_iff _).mpr ⟨q, hq, rfl⟩
    obtain ⟨eh', m, hmem, -⟩ := attachState_own_mem hst a hq'
    exact (mem_dom_connect_iff _ _ _).mpr ⟨m, Part.dom_iff_mem.mpr ⟨_, hmem⟩⟩

theorem attachState_own_output {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) (a : A) {n : ℕ} {b : B}
    {conv' : List (A ⊕ B)} {rh' : List (P × A)}
    (hserve : (b, (conv', rh')) ∈
      Connect.serve (tagAt i E) T n (eProj i eh ++ [Sum.inl a], rh))
    (h : us ++ [(i, a)] ∈ dom (connect (liftAt i E) T)) :
    output (connect (liftAt i E) T) (us ++ [(i, a)]) h = b := by
  obtain ⟨eh', m, hmem, -⟩ := attachState_own_mem hst a hserve
  exact output_connect_eq hmem h

theorem attachState_own_state {i : P} {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} {us : List (P × A)} {eh : List ((P × A) ⊕ B)}
    {rh : List (P × A)}
    (hst : AttachState (liftAt i E) T us (eh, rh)) (a : A) {n : ℕ} {b : B}
    {conv' : List (A ⊕ B)} {rh' : List (P × A)}
    (hserve : (b, (conv', rh')) ∈
      Connect.serve (tagAt i E) T n (eProj i eh ++ [Sum.inl a], rh)) :
    ∃ eh', AttachState (liftAt i E) T (us ++ [(i, a)]) (eh', rh') ∧
      eProj i eh' = conv' := by
  obtain ⟨eh', m, hmem, hconv⟩ := attachState_own_mem hst a hserve
  exact ⟨eh', Or.inr ⟨m, b, hmem⟩, hconv⟩

/-! ### Transparency of a foreign attachment

A tag-`i` engine served against a `j`-attachment (`i ≠ j`) runs exactly as
against the bare resource: every request is foreign to `j` and passes
through by the foreign recurrence.  The final outer history is the final
resource history re-based over the starting point, and the foreign
engine's conversation is untouched. -/

theorem serve_transparent {i j : P} (hij : i ≠ j)
    {E F : DDS (A ⊕ B) (B ⊕ A)} {R : Resource P A B} :
    ∀ (n : ℕ) {conv : List (A ⊕ B)} {us : List (P × A)}
      {eh : List ((P × A) ⊕ B)} {rh : List (P × A)},
      AttachState (liftAt j F) R us (eh, rh) →
      (Connect.serve (tagAt i E) (connect (liftAt j F) R) n (conv, us) =
        (Connect.serve (tagAt i E) R n (conv, rh)).map
          (fun q => (q.1, (q.2.1, us ++ q.2.2.drop rh.length)))) ∧
      ∀ {b : B} {conv' : List (A ⊕ B)} {rh' : List (P × A)},
        (b, (conv', rh')) ∈ Connect.serve (tagAt i E) R n (conv, rh) →
        ∃ eh', AttachState (liftAt j F) R (us ++ rh'.drop rh.length)
            (eh', rh') ∧ eProj j eh' = eProj j eh := by
  intro n
  induction n with
  | zero =>
      intro conv us eh rh hst
      constructor
      · show Part.none = Part.map _ Part.none
        simp
      · intro b conv' rh' hmem
        exact absurd hmem (Part.notMem_none _)
  | succ n ih =>
      intro conv us eh rh hst
      constructor
      · rw [Connect.serve_succ, Connect.serve_succ]
        by_cases hE : conv ∈ dom (tagAt i E)
        · rw [dif_pos hE, dif_pos hE]
          have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
          rw [output_tagAt i E hE hE']
          rcases hout : output E conv hE' with b | a'
          · simp only [Sum.map_inl, id_eq, Sum.elim_inl, Part.map_some,
              List.drop_length, List.append_nil]
          · simp only [Sum.map_inr, Sum.elim_inr]
            have hdomiff := attachState_foreign_dom_iff hst hij a'
            by_cases hR : rh ++ [(i, a')] ∈ dom R
            · rw [dif_pos (hdomiff.mpr hR), dif_pos hR]
              have houteq := attachState_foreign_output hst hij hR
                (hdomiff.mpr hR)
              rw [houteq]
              have hst' := attachState_foreign_state hst hij hR
              have hstep := (ih (conv := conv ++
                [Sum.inr (output R (rh ++ [(i, a')]) hR)]) hst').1
              rw [hstep]
              have hidx : ∀ {rh₂ : List (P × A)}, rh ++ [(i, a')] <+: rh₂ →
                  (us ++ [(i, a')]) ++
                      rh₂.drop (rh ++ [(i, a')]).length =
                    us ++ rh₂.drop rh.length := by
                rintro rh₂ ⟨t, rfl⟩
                rw [List.drop_left, List.append_assoc rh, List.drop_left]
                simp
              refine Part.ext fun z => ?_
              rw [Part.mem_map_iff, Part.mem_map_iff]
              constructor
              · rintro ⟨q, hq, rfl⟩
                exact ⟨q, hq, by rw [hidx (Connect.serve_rh_prefix hq)]⟩
              · rintro ⟨q, hq, rfl⟩
                exact ⟨q, hq, by rw [hidx (Connect.serve_rh_prefix hq)]⟩
            · rw [dif_neg (fun hc => hR (hdomiff.mp hc)), dif_neg hR]
              show Part.none = Part.map _ Part.none
              simp
        · rw [dif_neg hE, dif_neg hE]
          show Part.none = Part.map _ Part.none
          simp
      · intro b conv' rh' hmem
        rw [Connect.serve_succ] at hmem
        by_cases hE : conv ∈ dom (tagAt i E)
        · rw [dif_pos hE] at hmem
          have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
          rw [output_tagAt i E hE hE'] at hmem
          rcases hout : output E conv hE' with b₀ | a'
          · rw [hout] at hmem
            simp only [Sum.map_inl, id_eq, Sum.elim_inl] at hmem
            simp only [Part.mem_some_iff, Prod.mk.injEq] at hmem
            obtain ⟨rfl, rfl, rfl⟩ := hmem
            refine ⟨eh, ?_, rfl⟩
            rw [List.drop_length, List.append_nil]
            exact hst
          · rw [hout] at hmem
            simp only [Sum.map_inr, Sum.elim_inr] at hmem
            by_cases hR : rh ++ [(i, a')] ∈ dom R
            · rw [dif_pos hR] at hmem
              have hst' := attachState_foreign_state hst hij hR
              obtain ⟨eh', hstate, hproj⟩ := (ih hst').2 hmem
              have heproj : eProj j (eh ++ [Sum.inl (i, a'),
                  Sum.inr (output R (rh ++ [(i, a')]) hR)]) =
                  eProj j eh := by
                rw [show eh ++ [Sum.inl (i, a'),
                    Sum.inr (output R (rh ++ [(i, a')]) hR)] =
                    (eh ++ [Sum.inl (i, a')]) ++
                      [Sum.inr (output R (rh ++ [(i, a')]) hR)] by simp,
                  eProj_append_inr, if_neg (by simp [hij]),
                  eProj_append_inl, if_neg hij]
              have hidx : (us ++ [(i, a')]) ++
                  rh'.drop (rh ++ [(i, a')]).length =
                  us ++ rh'.drop rh.length := by
                obtain ⟨t, ht⟩ := Connect.serve_rh_prefix hmem
                have ht' : (rh ++ [(i, a')]) ++ t = rh' := ht
                rw [← ht', List.drop_left, List.append_assoc rh,
                  List.drop_left]
                simp
              rw [hidx] at hstate
              exact ⟨eh', hstate, hproj.trans heproj⟩
            · rw [dif_neg hR] at hmem
              exact absurd hmem (Part.notMem_none _)
        · rw [dif_neg hE] at hmem
          exact absurd hmem (Part.notMem_none _)

/-! ### Composition-order independence

MauRen16 §3.3 postulates `α^i β^j R = β^j α^i R` for `i ≠ j` as an axiom of
the cryptographic algebra; on this carrier it is a theorem.  The induction
carries, for both nesting orders, the reached states of both layers
together with their cross-identifications: the two `E`-conversations agree,
the two `F`-conversations agree, and the bottom resource histories agree. -/

/-- A foreign round leaves a projection untouched. -/
theorem eProj_append_foreign {i p : P} (hp : p ≠ i)
    (h : List ((P × A) ⊕ B)) (a : A) (b : B) :
    eProj i (h ++ [Sum.inl (p, a), Sum.inr b]) = eProj i h := by
  rw [show h ++ [Sum.inl (p, a), Sum.inr b] =
      (h ++ [Sum.inl (p, a)]) ++ [Sum.inr b] by simp,
    eProj_append_inr, if_neg (by simp [hp]), eProj_append_inl, if_neg hp]

theorem attachEngine_comm_aux {i j : P} (hij : i ≠ j)
    (E F : DDS (A ⊕ B) (B ⊕ A)) (R : Resource P A B) :
    ∀ us : List (P × A),
      (us ∈ dom (connect (liftAt i E) (connect (liftAt j F) R)) ↔
        us ∈ dom (connect (liftAt j F) (connect (liftAt i E) R))) ∧
      (∀ (hL : us ∈ dom (connect (liftAt i E) (connect (liftAt j F) R)))
        (hRt : us ∈ dom (connect (liftAt j F) (connect (liftAt i E) R))),
        output (connect (liftAt i E) (connect (liftAt j F) R)) us hL =
          output (connect (liftAt j F) (connect (liftAt i E) R)) us hRt) ∧
      (us = [] ∨ us ∈ dom (connect (liftAt i E) (connect (liftAt j F) R)) →
        ∃ ehL usL ehFL rhL ehR usR ehER rhR,
          AttachState (liftAt i E) (connect (liftAt j F) R) us (ehL, usL) ∧
          AttachState (liftAt j F) R usL (ehFL, rhL) ∧
          AttachState (liftAt j F) (connect (liftAt i E) R) us (ehR, usR) ∧
          AttachState (liftAt i E) R usR (ehER, rhR) ∧
          eProj i ehL = eProj i ehER ∧
          eProj j ehR = eProj j ehFL ∧
          rhL = rhR) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨iff_of_false (empty_not_mem _) (empty_not_mem _),
        fun hL _ => absurd hL (empty_not_mem _), fun _ => ?_⟩
      exact ⟨[], [], [], [], [], [], [], [],
        attachState_nil _ _, attachState_nil _ _, attachState_nil _ _,
        attachState_nil _ _, rfl, rfl, rfl⟩
  | append_singleton us x ihus =>
      obtain ⟨p, a⟩ := x
      by_cases hus : us = [] ∨
        us ∈ dom (connect (liftAt i E) (connect (liftAt j F) R))
      · obtain ⟨ehL, usL, ehFL, rhL, ehR, usR, ehER, rhR,
          h1, h2, h3, h4, h5, h6, h7⟩ := ihus.2.2 hus
        by_cases hpi : p = i
        · subst hpi
          have hL₂ : us ++ [(p, a)] ∈
              dom (connect (liftAt p E) (connect (liftAt j F) R)) ↔
              ∃ n, (Connect.serve (tagAt p E) R n
                (eProj p ehL ++ [Sum.inl a], rhL)).Dom := by
            rw [attachState_own_dom_iff h1 a]
            constructor
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [(serve_transparent hij n h2).1] at hn
              exact hn
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [(serve_transparent hij n h2).1]
              exact hn
          have hR₂ : us ++ [(p, a)] ∈
              dom (connect (liftAt j F) (connect (liftAt p E) R)) ↔
              ∃ n, (Connect.serve (tagAt p E) R n
                (eProj p ehER ++ [Sum.inl a], rhR)).Dom := by
            rw [attachState_foreign_dom_iff h3 hij a]
            exact attachState_own_dom_iff h4 a
          refine ⟨by rw [hL₂, hR₂, h5, h7], ?_, ?_⟩
          · intro hL hRt
            obtain ⟨n, hn⟩ := hL₂.mp hL
            obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
            have hqT : (b, (conv', usL ++ rh'.drop rhL.length)) ∈
                Connect.serve (tagAt p E) (connect (liftAt j F) R) n
                  (eProj p ehL ++ [Sum.inl a], usL) := by
              rw [(serve_transparent hij n h2).1]
              exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
            have hq' : (b, (conv', rh')) ∈ Connect.serve (tagAt p E) R n
                (eProj p ehER ++ [Sum.inl a], rhR) := by
              rw [← h5, ← h7]
              exact hq
            have hTin : usR ++ [(p, a)] ∈ dom (connect (liftAt p E) R) :=
              (attachState_own_dom_iff h4 a).mpr
                ⟨n, Part.dom_iff_mem.mpr ⟨_, hq'⟩⟩
            rw [attachState_own_output h1 a hqT hL,
              attachState_foreign_output h3 hij hTin hRt,
              attachState_own_output h4 a hq' hTin]
          · rintro (hcon | hL)
            · exact absurd hcon (by simp)
            · obtain ⟨n, hn⟩ := hL₂.mp hL
              obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
              have hqT : (b, (conv', usL ++ rh'.drop rhL.length)) ∈
                  Connect.serve (tagAt p E) (connect (liftAt j F) R) n
                    (eProj p ehL ++ [Sum.inl a], usL) := by
                rw [(serve_transparent hij n h2).1]
                exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
              have hq' : (b, (conv', rh')) ∈ Connect.serve (tagAt p E) R n
                  (eProj p ehER ++ [Sum.inl a], rhR) := by
                rw [← h5, ← h7]
                exact hq
              have hTin : usR ++ [(p, a)] ∈ dom (connect (liftAt p E) R) :=
                (attachState_own_dom_iff h4 a).mpr
                  ⟨n, Part.dom_iff_mem.mpr ⟨_, hq'⟩⟩
              obtain ⟨ehL', hstL', hconvL'⟩ :=
                attachState_own_state h1 a hqT
              obtain ⟨ehFL', hstFL', hprojFL'⟩ :=
                (serve_transparent hij n
                  (conv := eProj p ehL ++ [Sum.inl a]) h2).2 hq
              have hstR' := attachState_foreign_state h3 hij hTin
              obtain ⟨ehER', hstER', hconvER'⟩ :=
                attachState_own_state h4 a hq'
              refine ⟨ehL', usL ++ rh'.drop rhL.length, ehFL', rh',
                ehR ++ [Sum.inl (p, a), Sum.inr
                  (output (connect (liftAt p E) R) (usR ++ [(p, a)]) hTin)],
                usR ++ [(p, a)], ehER', rh',
                hstL', hstFL', hstR', hstER', ?_, ?_, rfl⟩
              · rw [hconvL', hconvER']
              · rw [eProj_append_foreign hij, h6, hprojFL']
        · by_cases hpj : p = j
          · subst hpj
            have hL₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt i E) (connect (liftAt p F) R)) ↔
                ∃ n, (Connect.serve (tagAt p F) R n
                  (eProj p ehFL ++ [Sum.inl a], rhL)).Dom := by
              rw [attachState_foreign_dom_iff h1 (Ne.symm hij) a]
              exact attachState_own_dom_iff h2 a
            have hR₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt p F) (connect (liftAt i E) R)) ↔
                ∃ n, (Connect.serve (tagAt p F) R n
                  (eProj p ehR ++ [Sum.inl a], rhR)).Dom := by
              rw [attachState_own_dom_iff h3 a]
              constructor
              · rintro ⟨n, hn⟩
                refine ⟨n, ?_⟩
                rw [(serve_transparent (Ne.symm hij) n h4).1] at hn
                exact hn
              · rintro ⟨n, hn⟩
                refine ⟨n, ?_⟩
                rw [(serve_transparent (Ne.symm hij) n h4).1]
                exact hn
            refine ⟨by rw [hL₂, hR₂, h6, h7], ?_, ?_⟩
            · intro hL hRt
              obtain ⟨n, hn⟩ := hR₂.mp hRt
              obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
              have hqT : (b, (conv', usR ++ rh'.drop rhR.length)) ∈
                  Connect.serve (tagAt p F) (connect (liftAt i E) R) n
                    (eProj p ehR ++ [Sum.inl a], usR) := by
                rw [(serve_transparent (Ne.symm hij) n h4).1]
                exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
              have hq' : (b, (conv', rh')) ∈ Connect.serve (tagAt p F) R n
                  (eProj p ehFL ++ [Sum.inl a], rhL) := by
                rw [← h6, h7]
                exact hq
              have hTin : usL ++ [(p, a)] ∈ dom (connect (liftAt p F) R) :=
                (attachState_own_dom_iff h2 a).mpr
                  ⟨n, Part.dom_iff_mem.mpr ⟨_, hq'⟩⟩
              rw [attachState_foreign_output h1 (Ne.symm hij) hTin hL,
                attachState_own_output h2 a hq' hTin,
                attachState_own_output h3 a hqT hRt]
            · rintro (hcon | hL)
              · exact absurd hcon (by simp)
              · obtain ⟨n, hn⟩ := hL₂.mp hL
                obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
                have hq' : (b, (conv', rh')) ∈ Connect.serve (tagAt p F) R n
                    (eProj p ehR ++ [Sum.inl a], rhR) := by
                  rw [h6, ← h7]
                  exact hq
                have hqT : (b, (conv', usR ++ rh'.drop rhR.length)) ∈
                    Connect.serve (tagAt p F) (connect (liftAt i E) R) n
                      (eProj p ehR ++ [Sum.inl a], usR) := by
                  rw [(serve_transparent (Ne.symm hij) n h4).1]
                  exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq', rfl⟩
                have hTin : usL ++ [(p, a)] ∈ dom (connect (liftAt p F) R) :=
                  (attachState_own_dom_iff h2 a).mpr
                    ⟨n, Part.dom_iff_mem.mpr ⟨_, hq⟩⟩
                obtain ⟨ehR', hstR', hconvR'⟩ :=
                  attachState_own_state h3 a hqT
                obtain ⟨ehER', hstER', hprojER'⟩ :=
                  (serve_transparent (Ne.symm hij) n
                    (conv := eProj p ehR ++ [Sum.inl a]) h4).2 hq'
                have hstL' := attachState_foreign_state h1 (Ne.symm hij) hTin
                obtain ⟨ehFL', hstFL', hconvFL'⟩ :=
                  attachState_own_state h2 a hq
                refine ⟨ehL ++ [Sum.inl (p, a), Sum.inr
                    (output (connect (liftAt p F) R) (usL ++ [(p, a)]) hTin)],
                  usL ++ [(p, a)], ehFL', rh',
                  ehR', usR ++ rh'.drop rhR.length, ehER', rh',
                  hstL', hstFL', hstR', hstER', ?_, ?_, rfl⟩
                · rw [eProj_append_foreign (Ne.symm hij), h5, hprojER']
                · rw [hconvR', hconvFL']
          · have hL₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt i E) (connect (liftAt j F) R)) ↔
                rhL ++ [(p, a)] ∈ dom R := by
              rw [attachState_foreign_dom_iff h1 hpi a]
              exact attachState_foreign_dom_iff h2 hpj a
            have hR₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt j F) (connect (liftAt i E) R)) ↔
                rhR ++ [(p, a)] ∈ dom R := by
              rw [attachState_foreign_dom_iff h3 hpj a]
              exact attachState_foreign_dom_iff h4 hpi a
            refine ⟨by rw [hL₂, hR₂, h7], ?_, ?_⟩
            · intro hL hRt
              have hRdom : rhL ++ [(p, a)] ∈ dom R := hL₂.mp hL
              have hTL : usL ++ [(p, a)] ∈ dom (connect (liftAt j F) R) :=
                (attachState_foreign_dom_iff h2 hpj a).mpr hRdom
              have hRdom' : rhR ++ [(p, a)] ∈ dom R := h7 ▸ hRdom
              have hTR : usR ++ [(p, a)] ∈ dom (connect (liftAt i E) R) :=
                (attachState_foreign_dom_iff h4 hpi a).mpr hRdom'
              rw [attachState_foreign_output h1 hpi hTL hL,
                attachState_foreign_output h2 hpj hRdom hTL,
                attachState_foreign_output h3 hpj hTR hRt,
                attachState_foreign_output h4 hpi hRdom' hTR]
              exact output_congr R (by rw [h7]) hRdom hRdom'
            · rintro (hcon | hL)
              · exact absurd hcon (by simp)
              · have hRdom : rhL ++ [(p, a)] ∈ dom R := hL₂.mp hL
                have hTL : usL ++ [(p, a)] ∈ dom (connect (liftAt j F) R) :=
                  (attachState_foreign_dom_iff h2 hpj a).mpr hRdom
                have hRdom' : rhR ++ [(p, a)] ∈ dom R := h7 ▸ hRdom
                have hTR : usR ++ [(p, a)] ∈ dom (connect (liftAt i E) R) :=
                  (attachState_foreign_dom_iff h4 hpi a).mpr hRdom'
                refine ⟨ehL ++ [Sum.inl (p, a), Sum.inr
                    (output (connect (liftAt j F) R) (usL ++ [(p, a)]) hTL)],
                  usL ++ [(p, a)],
                  ehFL ++ [Sum.inl (p, a),
                    Sum.inr (output R (rhL ++ [(p, a)]) hRdom)],
                  rhL ++ [(p, a)],
                  ehR ++ [Sum.inl (p, a), Sum.inr
                    (output (connect (liftAt i E) R) (usR ++ [(p, a)]) hTR)],
                  usR ++ [(p, a)],
                  ehER ++ [Sum.inl (p, a),
                    Sum.inr (output R (rhR ++ [(p, a)]) hRdom')],
                  rhR ++ [(p, a)],
                  attachState_foreign_state h1 hpi hTL,
                  attachState_foreign_state h2 hpj hRdom,
                  attachState_foreign_state h3 hpj hTR,
                  attachState_foreign_state h4 hpi hRdom',
                  ?_, ?_, by rw [h7]⟩
                · rw [eProj_append_foreign hpi, eProj_append_foreign hpi]
                  exact h5
                · rw [eProj_append_foreign hpj, eProj_append_foreign hpj]
                  exact h6
      · push Not at hus
        obtain ⟨hne, hnd⟩ := hus
        have hL' : us ++ [(p, a)] ∉
            dom (connect (liftAt i E) (connect (liftAt j F) R)) :=
          fun h => hnd (prefix_closed _ (List.prefix_append _ _) hne h)
        have hR' : us ++ [(p, a)] ∉
            dom (connect (liftAt j F) (connect (liftAt i E) R)) :=
          fun h => hnd (ihus.1.mpr
            (prefix_closed _ (List.prefix_append _ _) hne h))
        refine ⟨iff_of_false hL' hR', fun hL _ => absurd hL hL',
          fun hcon => ?_⟩
        rcases hcon with hcon | hcon
        · exact absurd hcon (by simp)
        · exact absurd hcon hL'

/-- **Composition-order independence** (MauRen16 §3.3): engines attached at
distinct interfaces commute.  The axiom of the abstract cryptographic
algebra, discharged on the carrier. -/
theorem attachEngine_comm {i j : P} (hij : i ≠ j)
    (E F : DDS (A ⊕ B) (B ⊕ A)) (R : Resource P A B) :
    attachEngine i E (attachEngine j F R) =
      attachEngine j F (attachEngine i E R) := by
  apply Subtype.ext
  funext us
  refine Part.ext' (attachEngine_comm_aux hij E F R us).1
    fun h₁ h₂ => (attachEngine_comm_aux hij E F R us).2.1 h₁ h₂

/-! ### Attachment against the trivial converters

The two mixed commutation cases.  The tagged engine only ever places
`(i,·)`-requests, which a relabelling fixing interface `i` leaves alone
and a block of a foreign interface set permits — so the attachment cannot
see either trivial converter, and they commute past it. -/

section Mixed

variable {i : P} {σ : P × A → P × A}

/-- `lastTag` reads only tags, which a tag-preserving map fixes. -/
theorem lastTag_map (hσ : ∀ p, (σ p).1 = p.1) (eh : List ((P × A) ⊕ B)) :
    lastTag (eh.map (Sum.map σ id)) = lastTag eh := by
  induction eh using List.reverseRecOn with
  | nil => rfl
  | append_singleton eh e ih =>
      rcases e with ⟨p, a⟩ | b
      · have htag := hσ (p, a)
        rcases hσpa : σ (p, a) with ⟨p', a'⟩
        rw [hσpa] at htag
        have htag' : p' = p := htag
        subst htag'
        simp only [List.map_append, List.map_cons, List.map_nil,
          Sum.map_inl, hσpa, lastTag_append_inl]
      · simp only [List.map_append, List.map_cons, List.map_nil,
          Sum.map_inr, id_eq, lastTag_append_inr]
        exact ih

/-- The `i`-projection cannot see a tag-preserving map fixing `i`. -/
theorem eProj_map (hσ : ∀ p, (σ p).1 = p.1)
    (hσi : ∀ p : P × A, p.1 = i → σ p = p) (eh : List ((P × A) ⊕ B)) :
    eProj i (eh.map (Sum.map σ id)) = eProj i eh := by
  induction eh using List.reverseRecOn with
  | nil => rfl
  | append_singleton eh e ih =>
      rcases e with ⟨p, a⟩ | b
      · by_cases hpi : p = i
        · subst hpi
          simp only [List.map_append, List.map_cons, List.map_nil,
            Sum.map_inl, hσi (p, a) rfl, eProj_append_inl, ih]
        · have htag := hσ (p, a)
          rcases hσpa : σ (p, a) with ⟨p', a'⟩
          rw [hσpa] at htag
          have htag' : p' = p := htag
          subst htag'
          simp only [List.map_append, List.map_cons, List.map_nil,
            Sum.map_inl, hσpa, eProj_append_inl, if_neg hpi, ih]
      · simp only [List.map_append, List.map_cons, List.map_nil,
          Sum.map_inr, id_eq, eProj_append_inr, lastTag_map hσ, ih]

/-- The tagged engine cannot see a relabelling that fixes its interface:
serving against `relabel σ id R` is serving against `R` on the mapped
history. -/
theorem serve_tagAt_relabel {E : DDS (A ⊕ B) (B ⊕ A)}
    {R : Resource P A B} (hσi : ∀ p : P × A, p.1 = i → σ p = p) :
    ∀ (n : ℕ) (conv : List (A ⊕ B)) (rh : List (P × A)),
      Connect.serve (tagAt i E) R n (conv, rh.map σ) =
        (Connect.serve (tagAt i E) (relabel σ id R) n (conv, rh)).map
          (fun q => (q.1, (q.2.1, q.2.2.map σ))) := by
  intro n
  induction n with
  | zero =>
      intro conv rh
      show Part.none = Part.map _ Part.none
      simp
  | succ n ih =>
      intro conv rh
      rw [Connect.serve_succ, Connect.serve_succ]
      by_cases hE : conv ∈ dom (tagAt i E)
      · rw [dif_pos hE, dif_pos hE]
        have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
        rw [output_tagAt i E hE hE']
        rcases hout : output E conv hE' with b | a'
        · simp
        · simp only [Sum.map_inr, Sum.elim_inr]
          have hfix : σ (i, a') = (i, a') := hσi (i, a') rfl
          have hmapped : (rh ++ [(i, a')]).map σ = rh.map σ ++ [(i, a')] := by
            simp [hfix]
          have hdomiff : rh ++ [(i, a')] ∈ dom (relabel σ id R) ↔
              rh.map σ ++ [(i, a')] ∈ dom R := by
            rw [mem_dom_relabel, hmapped]
          by_cases hR : rh ++ [(i, a')] ∈ dom (relabel σ id R)
          · rw [dif_pos (hdomiff.mp hR), dif_pos hR]
            have hout' : output (relabel σ id R) (rh ++ [(i, a')]) hR =
                output R (rh.map σ ++ [(i, a')]) (hdomiff.mp hR) := by
              rw [output_relabel]
              exact output_congr R hmapped _ _
            rw [hout']
            have hstep := ih (conv ++ [Sum.inr
              (output R (rh.map σ ++ [(i, a')]) (hdomiff.mp hR))])
              (rh ++ [(i, a')])
            rw [hmapped] at hstep
            exact hstep
          · rw [dif_neg (fun hc => hR (hdomiff.mpr hc)), dif_neg hR]
            show Part.none = Part.map _ Part.none
            simp
      · rw [dif_neg hE, dif_neg hE]
        show Part.none = Part.map _ Part.none
        simp

theorem attachEngine_relabel_aux {E : DDS (A ⊕ B) (B ⊕ A)}
    {R : Resource P A B} (hσ : ∀ p, (σ p).1 = p.1)
    (hσi : ∀ p : P × A, p.1 = i → σ p = p) :
    ∀ us : List (P × A),
      (us ∈ dom (connect (liftAt i E) (relabel σ id R)) ↔
        us.map σ ∈ dom (connect (liftAt i E) R)) ∧
      (∀ (h₁ : us ∈ dom (connect (liftAt i E) (relabel σ id R)))
        (h₂ : us.map σ ∈ dom (connect (liftAt i E) R)),
        output (connect (liftAt i E) (relabel σ id R)) us h₁ =
          output (connect (liftAt i E) R) (us.map σ) h₂) ∧
      (us = [] ∨ us ∈ dom (connect (liftAt i E) (relabel σ id R)) →
        ∃ ehA rhA ehB,
          AttachState (liftAt i E) (relabel σ id R) us (ehA, rhA) ∧
          AttachState (liftAt i E) R (us.map σ) (ehB, rhA.map σ) ∧
          eProj i ehB = eProj i ehA) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨iff_of_false (empty_not_mem _) (empty_not_mem _),
        fun h₁ _ => absurd h₁ (empty_not_mem _), fun _ => ?_⟩
      exact ⟨[], [], [], attachState_nil _ _, attachState_nil _ _, rfl⟩
  | append_singleton us x ihus =>
      obtain ⟨p, a⟩ := x
      have hmap : (us ++ [(p, a)]).map σ = us.map σ ++ [σ (p, a)] := by
        simp
      by_cases hus : us = [] ∨
        us ∈ dom (connect (liftAt i E) (relabel σ id R))
      · obtain ⟨ehA, rhA, ehB, hA, hB, hproj⟩ := ihus.2.2 hus
        by_cases hpi : p = i
        · subst hpi
          have hfix : σ (p, a) = (p, a) := hσi (p, a) rfl
          rw [hfix] at hmap
          have hL₂ : us ++ [(p, a)] ∈
              dom (connect (liftAt p E) (relabel σ id R)) ↔
              ∃ n, (Connect.serve (tagAt p E) R n
                (eProj p ehA ++ [Sum.inl a], rhA.map σ)).Dom := by
            rw [attachState_own_dom_iff hA a]
            constructor
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [serve_tagAt_relabel hσi n]
              exact hn
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [serve_tagAt_relabel hσi n] at hn
              exact hn
          have hR₂ : (us ++ [(p, a)]).map σ ∈
              dom (connect (liftAt p E) R) ↔
              ∃ n, (Connect.serve (tagAt p E) R n
                (eProj p ehB ++ [Sum.inl a], rhA.map σ)).Dom := by
            rw [hmap]
            exact attachState_own_dom_iff hB a
          refine ⟨by rw [hL₂, hR₂, hproj], ?_, ?_⟩
          · intro h₁ h₂
            obtain ⟨n, hn⟩ := (attachState_own_dom_iff hA a).mp h₁
            obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
            have hqB : (b, (conv', rh'.map σ)) ∈
                Connect.serve (tagAt p E) R n
                  (eProj p ehB ++ [Sum.inl a], rhA.map σ) := by
              rw [hproj, serve_tagAt_relabel hσi n]
              exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
            have h₂' : us.map σ ++ [(p, a)] ∈
                dom (connect (liftAt p E) R) := by
              rw [← hmap]
              exact h₂
            rw [attachState_own_output hA a hq h₁]
            have := attachState_own_output hB a hqB h₂'
            rw [output_congr _ hmap h₂ h₂', this]
          · rintro (hcon | h₁)
            · exact absurd hcon (by simp)
            · obtain ⟨n, hn⟩ := (attachState_own_dom_iff hA a).mp h₁
              obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
              have hqB : (b, (conv', rh'.map σ)) ∈
                  Connect.serve (tagAt p E) R n
                    (eProj p ehB ++ [Sum.inl a], rhA.map σ) := by
                rw [hproj, serve_tagAt_relabel hσi n]
                exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
              obtain ⟨ehA', hstA', hconvA'⟩ := attachState_own_state hA a hq
              obtain ⟨ehB', hstB', hconvB'⟩ := attachState_own_state hB a hqB
              refine ⟨ehA', rh', ehB', hstA', ?_, ?_⟩
              · rw [hmap]
                exact hstB'
              · rw [hconvA', hconvB']
        · have htag := hσ (p, a)
          rcases hσpa : σ (p, a) with ⟨p', a₂⟩
          rw [hσpa] at htag
          have htag' : p = p' := htag.symm
          subst htag'
          rw [hσpa] at hmap
          have hdomrel : rhA ++ [(p, a)] ∈ dom (relabel σ id R) ↔
              rhA.map σ ++ [(p, a₂)] ∈ dom R := by
            rw [mem_dom_relabel]
            simp [hσpa]
          have hL₂ : us ++ [(p, a)] ∈
              dom (connect (liftAt i E) (relabel σ id R)) ↔
              rhA.map σ ++ [(p, a₂)] ∈ dom R := by
            rw [attachState_foreign_dom_iff hA hpi a]
            exact hdomrel
          have hR₂ : (us ++ [(p, a)]).map σ ∈
              dom (connect (liftAt i E) R) ↔
              rhA.map σ ++ [(p, a₂)] ∈ dom R := by
            rw [hmap]
            exact attachState_foreign_dom_iff hB hpi a₂
          refine ⟨by rw [hL₂, hR₂], ?_, ?_⟩
          · intro h₁ h₂
            have hRd : rhA.map σ ++ [(p, a₂)] ∈ dom R := hL₂.mp h₁
            have hTrel : rhA ++ [(p, a)] ∈ dom (relabel σ id R) :=
              hdomrel.mpr hRd
            have h₂' : us.map σ ++ [(p, a₂)] ∈
                dom (connect (liftAt i E) R) := by
              rw [← hmap]
              exact h₂
            rw [attachState_foreign_output hA hpi hTrel h₁,
              output_congr _ hmap h₂ h₂',
              attachState_foreign_output hB hpi hRd h₂']
            rw [output_relabel]
            exact output_congr R (by simp [hσpa]) _ _
          · rintro (hcon | h₁)
            · exact absurd hcon (by simp)
            · have hRd : rhA.map σ ++ [(p, a₂)] ∈ dom R := hL₂.mp h₁
              have hTrel : rhA ++ [(p, a)] ∈ dom (relabel σ id R) :=
                hdomrel.mpr hRd
              have houts : output (relabel σ id R) (rhA ++ [(p, a)]) hTrel =
                  output R (rhA.map σ ++ [(p, a₂)]) hRd := by
                rw [output_relabel]
                exact output_congr R (by simp [hσpa]) _ _
              refine ⟨ehA ++ [Sum.inl (p, a), Sum.inr
                  (output (relabel σ id R) (rhA ++ [(p, a)]) hTrel)],
                rhA ++ [(p, a)],
                ehB ++ [Sum.inl (p, a₂), Sum.inr
                  (output R (rhA.map σ ++ [(p, a₂)]) hRd)],
                attachState_foreign_state hA hpi hTrel, ?_, ?_⟩
              · rw [hmap, show (rhA ++ [(p, a)]).map σ =
                    rhA.map σ ++ [(p, a₂)] by simp [hσpa]]
                exact attachState_foreign_state hB hpi hRd
              · rw [eProj_append_foreign hpi, eProj_append_foreign hpi]
                exact hproj
      · push Not at hus
        obtain ⟨hne, hnd⟩ := hus
        have hL' : us ++ [(p, a)] ∉
            dom (connect (liftAt i E) (relabel σ id R)) :=
          fun h => hnd (prefix_closed _ (List.prefix_append _ _) hne h)
        have hR' : (us ++ [(p, a)]).map σ ∉
            dom (connect (liftAt i E) R) := by
          intro h
          rw [hmap] at h
          exact hnd (ihus.1.mpr (prefix_closed _ (List.prefix_append _ _)
            (fun hc => hne (List.map_eq_nil_iff.mp hc)) h))
        refine ⟨iff_of_false hL' hR', fun h₁ _ => absurd h₁ hL',
          fun hcon => ?_⟩
        rcases hcon with hcon | hcon
        · exact absurd hcon (by simp)
        · exact absurd hcon hL'

/-- Attachment commutes with a tag-preserving relabelling that fixes its
interface — the mixed base case behind `attachEngineAt` vs `relabelAt`. -/
theorem attachEngine_relabel {E : DDS (A ⊕ B) (B ⊕ A)}
    {R : Resource P A B} (hσ : ∀ p, (σ p).1 = p.1)
    (hσi : ∀ p : P × A, p.1 = i → σ p = p) :
    attachEngine i E (relabel σ id R) =
      relabel σ id (attachEngine i E R) := by
  apply Subtype.ext
  funext us
  refine Part.ext' (attachEngine_relabel_aux hσ hσi us).1
    fun h₁ h₂ => (attachEngine_relabel_aux hσ hσi us).2.1 h₁ h₂

/-- The tagged engine cannot see a block of a foreign interface set: its
requests carry tag `i ∉ Z`, and a `Z`-clean history stays `Z`-clean. -/
theorem serve_tagAt_block {E : DDS (A ⊕ B) (B ⊕ A)} {R : Resource P A B}
    {Z : Set P} (hiZ : i ∉ Z) :
    ∀ (n : ℕ) (conv : List (A ⊕ B)) {rh : List (P × A)},
      (∀ p ∈ rh, p.1 ∉ Z) →
      Connect.serve (tagAt i E) (block Z R) n (conv, rh) =
        Connect.serve (tagAt i E) R n (conv, rh) := by
  intro n
  induction n with
  | zero =>
      intro conv rh _
      rfl
  | succ n ih =>
      intro conv rh hclean
      rw [Connect.serve_succ, Connect.serve_succ]
      by_cases hE : conv ∈ dom (tagAt i E)
      · rw [dif_pos hE, dif_pos hE]
        have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
        rw [output_tagAt i E hE hE']
        rcases hout : output E conv hE' with b | a'
        · simp
        · simp only [Sum.map_inr, Sum.elim_inr]
          have hclean' : ∀ p ∈ rh ++ [(i, a')], p.1 ∉ Z := by
            intro p hp
            rcases List.mem_append.mp hp with hp | hp
            · exact hclean p hp
            · rcases List.mem_singleton.mp hp with rfl
              exact hiZ
          by_cases hR : rh ++ [(i, a')] ∈ dom R
          · rw [dif_pos ((mem_dom_block Z R _).mpr ⟨hR, hclean'⟩),
              dif_pos hR]
            have houtb : output (block Z R) (rh ++ [(i, a')])
                ((mem_dom_block Z R _).mpr ⟨hR, hclean'⟩) =
                output R (rh ++ [(i, a')]) hR :=
              output_block Z R _ _
            rw [houtb]
            exact ih _ hclean'
          · rw [dif_neg (fun hc => hR ((mem_dom_block Z R _).mp hc).1),
              dif_neg hR]
      · rw [dif_neg hE, dif_neg hE]

/-- Tag support: the tagged engine's rounds extend the resource history by
`(i,·)`-entries only. -/
theorem serve_tagAt_rh_mem {E : DDS (A ⊕ B) (B ⊕ A)}
    {T : Resource P A B} :
    ∀ {n : ℕ} {conv : List (A ⊕ B)} {rh : List (P × A)} {b : B}
      {conv' : List (A ⊕ B)} {rh' : List (P × A)},
      (b, (conv', rh')) ∈ Connect.serve (tagAt i E) T n (conv, rh) →
      ∀ p ∈ rh', p ∈ rh ∨ p.1 = i := by
  intro n
  induction n with
  | zero =>
      intro conv rh b conv' rh' h
      exact absurd h (Part.notMem_none _)
  | succ n ih =>
      intro conv rh b conv' rh' h
      rw [Connect.serve_succ] at h
      by_cases hE : conv ∈ dom (tagAt i E)
      · rw [dif_pos hE] at h
        have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
        rw [output_tagAt i E hE hE'] at h
        rcases hout : output E conv hE' with b₀ | a'
        · rw [hout] at h
          simp only [Sum.map_inl, id_eq, Sum.elim_inl] at h
          have hrh : rh' = rh :=
            congrArg (fun z => z.2.2) (Part.mem_some_iff.mp h)
          rw [hrh]
          exact fun p hp => Or.inl hp
        · rw [hout] at h
          simp only [Sum.map_inr, Sum.elim_inr] at h
          by_cases hR : rh ++ [(i, a')] ∈ dom T
          · rw [dif_pos hR] at h
            intro p hp
            rcases ih h p hp with hmem | hmem
            · rcases List.mem_append.mp hmem with hmem | hmem
              · exact Or.inl hmem
              · rcases List.mem_singleton.mp hmem with rfl
                exact Or.inr rfl
            · exact Or.inr hmem
          · rw [dif_neg hR] at h
            exact absurd h (Part.notMem_none _)
      · rw [dif_neg hE] at h
        exact absurd h (Part.notMem_none _)

theorem attachEngine_block_aux {E : DDS (A ⊕ B) (B ⊕ A)}
    {R : Resource P A B} {Z : Set P} (hiZ : i ∉ Z) :
    ∀ us : List (P × A),
      (us ∈ dom (connect (liftAt i E) (block Z R)) ↔
        us ∈ dom (connect (liftAt i E) R) ∧ ∀ p ∈ us, p.1 ∉ Z) ∧
      (∀ (h₁ : us ∈ dom (connect (liftAt i E) (block Z R)))
        (h₂ : us ∈ dom (connect (liftAt i E) R)),
        output (connect (liftAt i E) (block Z R)) us h₁ =
          output (connect (liftAt i E) R) us h₂) ∧
      (us = [] ∨ us ∈ dom (connect (liftAt i E) (block Z R)) →
        (∀ p ∈ us, p.1 ∉ Z) ∧
        ∃ ehA rh ehB,
          AttachState (liftAt i E) (block Z R) us (ehA, rh) ∧
          AttachState (liftAt i E) R us (ehB, rh) ∧
          eProj i ehB = eProj i ehA ∧ ∀ p ∈ rh, p.1 ∉ Z) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨iff_of_false (empty_not_mem _)
          (fun h => empty_not_mem _ h.1),
        fun h₁ _ => absurd h₁ (empty_not_mem _), fun _ => ?_⟩
      exact ⟨by simp, [], [], [], attachState_nil _ _, attachState_nil _ _,
        rfl, by simp⟩
  | append_singleton us x ihus =>
      obtain ⟨p, a⟩ := x
      by_cases hus : us = [] ∨ us ∈ dom (connect (liftAt i E) (block Z R))
      · obtain ⟨husclean, ehA, rh, ehB, hA, hB, hproj, hrhclean⟩ :=
          ihus.2.2 hus
        by_cases hpZ : p ∈ Z
        · have hpi : p ≠ i := fun hc => hiZ (hc ▸ hpZ)
          have hL' : us ++ [(p, a)] ∉
              dom (connect (liftAt i E) (block Z R)) := by
            intro h
            exact ((mem_dom_block Z R _).mp
                (attachState_foreign_dom hA hpi h)).2 (p, a)
              (List.mem_append_right _ (List.mem_singleton_self _)) hpZ
          refine ⟨iff_of_false hL'
              (fun h => h.2 (p, a)
                (List.mem_append_right _ (List.mem_singleton_self _)) hpZ),
            fun h₁ _ => absurd h₁ hL', fun hcon => ?_⟩
          rcases hcon with hcon | hcon
          · exact absurd hcon (by simp)
          · exact absurd hcon hL'
        · have hextclean : ∀ q ∈ us ++ [(p, a)], q.1 ∉ Z := by
            intro q hq
            rcases List.mem_append.mp hq with hq | hq
            · exact husclean q hq
            · rcases List.mem_singleton.mp hq with rfl
              exact hpZ
          by_cases hpi : p = i
          · subst hpi
            have hL₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt p E) (block Z R)) ↔
                ∃ n, (Connect.serve (tagAt p E) R n
                  (eProj p ehA ++ [Sum.inl a], rh)).Dom := by
              rw [attachState_own_dom_iff hA a]
              constructor
              · rintro ⟨n, hn⟩
                refine ⟨n, ?_⟩
                rw [← serve_tagAt_block hpZ n _ hrhclean]
                exact hn
              · rintro ⟨n, hn⟩
                refine ⟨n, ?_⟩
                rw [serve_tagAt_block hpZ n _ hrhclean]
                exact hn
            have hR₂ : us ++ [(p, a)] ∈ dom (connect (liftAt p E) R) ↔
                ∃ n, (Connect.serve (tagAt p E) R n
                  (eProj p ehB ++ [Sum.inl a], rh)).Dom :=
              attachState_own_dom_iff hB a
            refine ⟨?_, ?_, ?_⟩
            · rw [hL₂]
              constructor
              · intro h
                exact ⟨hR₂.mpr (by rwa [hproj]), hextclean⟩
              · rintro ⟨h, -⟩
                rw [← hproj]
                exact hR₂.mp h
            · intro h₁ h₂
              obtain ⟨n, hn⟩ := (attachState_own_dom_iff hA a).mp h₁
              have hn' : (Connect.serve (tagAt p E) R n
                  (eProj p ehA ++ [Sum.inl a], rh)).Dom := by
                rwa [serve_tagAt_block hpZ n _ hrhclean] at hn
              obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn'
              have hqblk : (b, (conv', rh')) ∈
                  Connect.serve (tagAt p E) (block Z R) n
                    (eProj p ehA ++ [Sum.inl a], rh) := by
                rw [serve_tagAt_block hpZ n _ hrhclean]
                exact hq
              have hqB : (b, (conv', rh')) ∈
                  Connect.serve (tagAt p E) R n
                    (eProj p ehB ++ [Sum.inl a], rh) := by
                rw [hproj]
                exact hq
              rw [attachState_own_output hA a hqblk h₁,
                attachState_own_output hB a hqB h₂]
            · rintro (hcon | h₁)
              · exact absurd hcon (by simp)
              · obtain ⟨n, hn⟩ := (attachState_own_dom_iff hA a).mp h₁
                have hn' : (Connect.serve (tagAt p E) R n
                    (eProj p ehA ++ [Sum.inl a], rh)).Dom := by
                  rwa [serve_tagAt_block hpZ n _ hrhclean] at hn
                obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn'
                have hqblk : (b, (conv', rh')) ∈
                    Connect.serve (tagAt p E) (block Z R) n
                      (eProj p ehA ++ [Sum.inl a], rh) := by
                  rw [serve_tagAt_block hpZ n _ hrhclean]
                  exact hq
                have hqB : (b, (conv', rh')) ∈
                    Connect.serve (tagAt p E) R n
                      (eProj p ehB ++ [Sum.inl a], rh) := by
                  rw [hproj]
                  exact hq
                obtain ⟨ehA', hstA', hconvA'⟩ :=
                  attachState_own_state hA a hqblk
                obtain ⟨ehB', hstB', hconvB'⟩ :=
                  attachState_own_state hB a hqB
                refine ⟨hextclean, ehA', rh', ehB', hstA', hstB', ?_, ?_⟩
                · rw [hconvA', hconvB']
                · intro q hq'
                  rcases serve_tagAt_rh_mem hq q hq' with hmem | hmem
                  · exact hrhclean q hmem
                  · rw [hmem]
                    exact hpZ
          · have hdomblk : rh ++ [(p, a)] ∈ dom (block Z R) ↔
                rh ++ [(p, a)] ∈ dom R := by
              rw [mem_dom_block]
              refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
              intro q hq
              rcases List.mem_append.mp hq with hq | hq
              · exact hrhclean q hq
              · rcases List.mem_singleton.mp hq with rfl
                exact hpZ
            refine ⟨?_, ?_, ?_⟩
            · rw [attachState_foreign_dom_iff hA hpi a, hdomblk,
                ← attachState_foreign_dom_iff hB hpi a]
              exact ⟨fun h => ⟨h, hextclean⟩, fun h => h.1⟩
            · intro h₁ h₂
              have hTblk : rh ++ [(p, a)] ∈ dom (block Z R) :=
                attachState_foreign_dom hA hpi h₁
              have hTR : rh ++ [(p, a)] ∈ dom R := hdomblk.mp hTblk
              rw [attachState_foreign_output hA hpi hTblk h₁,
                attachState_foreign_output hB hpi hTR h₂]
              exact output_block Z R _ _
            · rintro (hcon | h₁)
              · exact absurd hcon (by simp)
              · have hTblk : rh ++ [(p, a)] ∈ dom (block Z R) :=
                  attachState_foreign_dom hA hpi h₁
                have hTR : rh ++ [(p, a)] ∈ dom R := hdomblk.mp hTblk
                have hbeq : output (block Z R) (rh ++ [(p, a)]) hTblk =
                    output R (rh ++ [(p, a)]) hTR :=
                  output_block Z R _ _
                refine ⟨hextclean,
                  ehA ++ [Sum.inl (p, a),
                    Sum.inr (output (block Z R) (rh ++ [(p, a)]) hTblk)],
                  rh ++ [(p, a)],
                  ehB ++ [Sum.inl (p, a),
                    Sum.inr (output R (rh ++ [(p, a)]) hTR)],
                  attachState_foreign_state hA hpi hTblk, ?_, ?_, ?_⟩
                · exact attachState_foreign_state hB hpi hTR
                · rw [eProj_append_foreign hpi, eProj_append_foreign hpi]
                  exact hproj
                · intro q hq
                  rcases List.mem_append.mp hq with hq | hq
                  · exact hrhclean q hq
                  · rcases List.mem_singleton.mp hq with rfl
                    exact hpZ
      · push Not at hus
        obtain ⟨hne, hnd⟩ := hus
        have hL' : us ++ [(p, a)] ∉
            dom (connect (liftAt i E) (block Z R)) :=
          fun h => hnd (prefix_closed _ (List.prefix_append _ _) hne h)
        refine ⟨iff_of_false hL' ?_, fun h₁ _ => absurd h₁ hL',
          fun hcon => ?_⟩
        · rintro ⟨hdom, hclean⟩
          refine hnd (ihus.1.mpr ⟨prefix_closed _ (List.prefix_append _ _)
            hne hdom, fun q hq => hclean q (List.mem_append_left _ hq)⟩)
        · rcases hcon with hcon | hcon
          · exact absurd hcon (by simp)
          · exact absurd hcon hL'

/-- Attachment commutes with blocking a foreign interface set — the mixed
base case behind `attachEngineAt` vs `blockAt`. -/
theorem attachEngine_block {E : DDS (A ⊕ B) (B ⊕ A)}
    {R : Resource P A B} {Z : Set P} (hiZ : i ∉ Z) :
    attachEngine i E (block Z R) = block Z (attachEngine i E R) := by
  apply Subtype.ext
  funext us
  refine Part.ext' (attachEngine_block_aux hiZ us).1
    fun h₁ h₂ => (attachEngine_block_aux hiZ us).2.1 h₁ h₂.1

end Mixed

/-- Lifting the relay is the relay: the identity engine is
interface-blind. -/
theorem liftAt_idEngine (i : P) :
    liftAt i (idEngine (X := A) (Y := B)) = idEngine := by
  have hdom : ∀ l : List ((P × A) ⊕ B), l ≠ [] →
      (liftAtRaw i idEngine l).Dom := by
    intro l hl
    rcases List.eq_nil_or_concat l with rfl | ⟨h₀, e, rfl⟩
    · exact absurd rfl hl
    · rcases e with ⟨p, a⟩ | b
      · by_cases hpi : p = i
        · subst hpi
          simp [liftAtRaw, idEngine, functionEvaluator]
        · simp [liftAtRaw, hpi]
      · by_cases htag : lastTag h₀ = some i
        · simp [liftAtRaw, htag, idEngine, functionEvaluator]
        · simp [liftAtRaw, htag]
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ ?_
  · constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun l' _ hne' => hdom l' hne'⟩
  · intro h₁ h₂
    rcases List.eq_nil_or_concat l with rfl | ⟨h₀, e, rfl⟩
    · exact absurd rfl h₂
    · rcases e with ⟨p, a⟩ | b
      · by_cases hpi : p = i
        · subst hpi
          simp [liftAt, validate, liftAtRaw, idEngine, functionEvaluator]
        · simp [liftAt, validate, liftAtRaw, hpi, idEngine,
            functionEvaluator]
      · by_cases htag : lastTag h₀ = some i
        · simp [liftAt, validate, liftAtRaw, htag, idEngine,
            functionEvaluator]
        · simp [liftAt, validate, liftAtRaw, htag, idEngine,
            functionEvaluator]

/-- MauRen16 §3.3's `id ∈ Σ` at every interface: attaching the identity
engine anywhere changes nothing. -/
theorem attachEngine_idEngine (i : P) (R : Resource P A B) :
    attachEngine i idEngine R = R := by
  rw [attachEngine, liftAt_idEngine, connect_idEngine]

end

end System

namespace PDS

noncomputable section

open Probability (Distribution)

universe u v w z

variable {U : Type u} {V : Type v} {X : Type w} {Y : Type z}

/-- The law of the connected system: engine law and resource law sampled
independently, pushed along the deterministic interpreter — the same shape
as `Resource.parLaw`. -/
def connectLaw (EL : PDS (U ⊕ Y) (V ⊕ X)) (RL : PDS X Y) : PDS U V :=
  Distribution.fTransform
    (fun p : System.DDS (U ⊕ Y) (V ⊕ X) × System.DDS X Y =>
      System.connect p.1 p.2)
    (Distribution.prod EL RL)

variable {P : Type u} {A : Type v} {B : Type w}

/-- Engine attachment at one interface, lifted to probabilistic resources
by pushforward along the deterministic interpreter. -/
def attachEngineLaw (i : P) (E : System.DDS (A ⊕ B) (B ⊕ A)) :
    PDS (P × A) B → PDS (P × A) B :=
  Distribution.fTransform (System.attachEngine i E)

/-- Composition-order independence, on laws. -/
theorem attachEngineLaw_attachEngineLaw {i j : P} (hij : i ≠ j)
    (E F : System.DDS (A ⊕ B) (B ⊕ A)) (S : PDS (P × A) B) :
    attachEngineLaw i E (attachEngineLaw j F S) =
      attachEngineLaw j F (attachEngineLaw i E S) := by
  rw [attachEngineLaw, attachEngineLaw, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  exact congrFun (congrArg _
    (funext fun R => System.attachEngine_comm hij E F R)) S

end

end PDS

end RandomSystems

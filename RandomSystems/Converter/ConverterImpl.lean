/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Connect

/-!
# Converter implementations

A converter is a system (its history function, an engine
`DDS (U ⊕ Y) (V ⊕ X)`); a `ConverterImpl` is one *implementation* of such
a system: initial state, a reaction to an outer query, a reaction to a
resource reply.  Reactions are partial — partiality by undefinedness, the
discipline of the whole development — so implementations cover relays that
must decode as well as total programs.  The implementation never appears
in a theory statement: `ConverterImpl.engine` is its history function, and
two implementations with the same engine are the same converter.

`serve_step` is the generic round theorem: one interpreter round of an
authored converter is `run`, a recursion over the implementation's own
transitions.  Behavior proofs about concrete converters unfold by
computation; the interpreter is never unfolded against a concrete
converter again.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe s u v w x

variable {σ : Type s} {U : Type u} {Y : Type v} {V : Type w} {X : Type x}

/-- A converter implementation: one partial reaction per event, state
across the whole interaction. -/
structure ConverterImpl (σ : Type s) (U : Type u) (Y : Type v) (V : Type w)
    (X : Type x) where
  /-- The initial state. -/
  init : σ
  /-- React to an outer query: new state, and an answer or a request. -/
  onQuery : σ → U → Part (σ × (V ⊕ X))
  /-- React to a resource reply: new state, and an answer or a request. -/
  onReply : σ → Y → Part (σ × (V ⊕ X))

namespace ConverterImpl

/-- One step, on either event kind. -/
def step (P : ConverterImpl σ U Y V X) (s : σ) :
    (U ⊕ Y) → Part (σ × (V ⊕ X))
  | .inl u => P.onQuery s u
  | .inr y => P.onReply s y

/-- The state after a history: the partial fold of the reactions. -/
def state (P : ConverterImpl σ U Y V X) (l : List (U ⊕ Y)) : Part σ :=
  l.foldl (fun ps e => ps.bind fun s => (P.step s e).map Prod.fst)
    (Part.some P.init)

@[simp] theorem state_nil (P : ConverterImpl σ U Y V X) :
    P.state [] = Part.some P.init := rfl

@[simp] theorem state_append (P : ConverterImpl σ U Y V X)
    (l : List (U ⊕ Y)) (e : U ⊕ Y) :
    P.state (l ++ [e]) =
      (P.state l).bind fun s => (P.step s e).map Prod.fst := by
  simp [state, List.foldl_append]

/-- The engine's local rule: resolve the state before the frontier, react
to the frontier event. -/
def engineRaw (P : ConverterImpl σ U Y V X) : Raw (U ⊕ Y) (V ⊕ X) :=
  fun l =>
    match l.getLast? with
    | none => Part.none
    | some e => (P.state l.dropLast).bind fun s => (P.step s e).map Prod.snd

/-- The implementation's engine: its history function, an ordinary system
on the sum alphabet.  This is the converter; the implementation is
presentation. -/
def engine (P : ConverterImpl σ U Y V X) : DDS (U ⊕ Y) (V ⊕ X) :=
  validate (engineRaw P)

@[simp] theorem engineRaw_concat (P : ConverterImpl σ U Y V X)
    (l : List (U ⊕ Y)) (e : U ⊕ Y) :
    engineRaw P (l ++ [e]) =
      (P.state l).bind fun s => (P.step s e).map Prod.snd := by
  simp [engineRaw]

/-- Total implementations have defined state everywhere. -/
theorem state_dom_of_total (P : ConverterImpl σ U Y V X)
    (htot : ∀ s e, (P.step s e).Dom) (l : List (U ⊕ Y)) :
    (P.state l).Dom := by
  induction l using List.reverseRecOn with
  | nil => trivial
  | append_singleton l e ih =>
      rw [state_append]
      exact ⟨ih, htot _ _⟩

/-- A total implementation's engine accepts every nonempty history. -/
theorem mem_dom_engine_of_total (P : ConverterImpl σ U Y V X)
    (htot : ∀ s e, (P.step s e).Dom) {l : List (U ⊕ Y)} (hne : l ≠ []) :
    l ∈ dom P.engine := by
  refine ⟨hne, fun l' hl' hne' => ?_⟩
  rcases List.eq_nil_or_concat l' with rfl | ⟨l₀, e, rfl⟩
  · exact absurd rfl hne'
  · rw [List.concat_eq_append, engineRaw_concat]
    exact ⟨state_dom_of_total P htot l₀, htot _ _⟩

/-! ### The generic round interpreter -/

/-- Resolve a pending move `(state, answer-or-request)` against a
resource, carrying the engine and resource histories. -/
def run (P : ConverterImpl σ U Y V X) (R : DDS X Y) :
    ℕ → σ × (V ⊕ X) → List (U ⊕ Y) → List X →
      Part (V × σ × List (U ⊕ Y) × List X)
  | _, (s, .inl v), eh, rh => Part.some (v, s, eh, rh)
  | 0, (_, .inr _), _, _ => Part.none
  | n + 1, (s, .inr x), eh, rh =>
      if hR : rh ++ [x] ∈ dom R then
        (P.onReply s (output R (rh ++ [x]) hR)).bind fun p =>
          run P R n p (eh ++ [Sum.inr (output R (rh ++ [x]) hR)])
            (rh ++ [x])
      else Part.none

@[simp] theorem run_answer (P : ConverterImpl σ U Y V X) (R : DDS X Y)
    (n : ℕ) (s : σ) (v : V) (eh : List (U ⊕ Y)) (rh : List X) :
    P.run R n (s, Sum.inl v) eh rh = Part.some (v, s, eh, rh) := by
  cases n <;> rfl

theorem run_request (P : ConverterImpl σ U Y V X) (R : DDS X Y) (n : ℕ)
    (s : σ) (x : X) (eh : List (U ⊕ Y)) (rh : List X)
    (hR : rh ++ [x] ∈ dom R) :
    P.run R (n + 1) (s, Sum.inr x) eh rh =
      (P.onReply s (output R (rh ++ [x]) hR)).bind fun p =>
        P.run R n p (eh ++ [Sum.inr (output R (rh ++ [x]) hR)])
          (rh ++ [x]) := by
  show (if hR' : rh ++ [x] ∈ dom R then
      (P.onReply s (output R (rh ++ [x]) hR')).bind fun p =>
        P.run R n p (eh ++ [Sum.inr (output R (rh ++ [x]) hR')])
          (rh ++ [x])
    else Part.none) = _
  rw [dif_pos hR]

theorem run_request_none (P : ConverterImpl σ U Y V X) (R : DDS X Y)
    (n : ℕ) (s : σ) (x : X) (eh : List (U ⊕ Y)) (rh : List X)
    (hR : rh ++ [x] ∉ dom R) :
    P.run R (n + 1) (s, Sum.inr x) eh rh = Part.none := by
  show (if hR' : rh ++ [x] ∈ dom R then
      (P.onReply s (output R (rh ++ [x]) hR')).bind fun p =>
        P.run R n p (eh ++ [Sum.inr (output R (rh ++ [x]) hR')])
          (rh ++ [x])
    else Part.none) = _
  rw [dif_neg hR]

/-- Against a stateless total resource, a request step computes
outright. -/
@[simp] theorem run_functionEvaluator_request (P : ConverterImpl σ U Y V X)
    (f : X → Y) (n : ℕ) (s : σ) (x : X) (eh : List (U ⊕ Y))
    (rh : List X) :
    P.run (functionEvaluator f) (n + 1) (s, Sum.inr x) eh rh =
      (P.onReply s (f x)).bind fun p =>
        P.run (functionEvaluator f) n p (eh ++ [Sum.inr (f x)])
          (rh ++ [x]) := by
  have hR : rh ++ [x] ∈ dom (functionEvaluator f) := by
    show _ ≠ []
    simp
  rw [run_request _ _ _ _ _ _ _ hR]
  have hout : output (functionEvaluator f) (rh ++ [x]) hR = f x := by
    simp
  rw [hout]

/-! ### The generic round theorem -/

/-- **The round theorem, general form**: from any frontier event, one
interpreter round of an authored converter is `run` on the
implementation's own transition, given a coherent past.  The interpreter
is never unfolded against a concrete converter again. -/
theorem serve_step (P : ConverterImpl σ U Y V X) (R : DDS X Y) :
    ∀ (n : ℕ) (eh₀ : List (U ⊕ Y)) (e : U ⊕ Y) (rh : List X),
      (eh₀ = [] ∨ eh₀ ∈ dom P.engine) →
      Connect.serve P.engine R (n + 1) (eh₀ ++ [e], rh) =
        (((P.state eh₀).bind fun s => P.step s e).bind fun p =>
          P.run R n p (eh₀ ++ [e]) rh).map
            (fun q => (q.1, (q.2.2.1, q.2.2.2))) := by
  intro n
  induction n with
  | zero =>
      intro eh₀ e rh hok
      rw [Connect.serve_succ]
      by_cases hE : eh₀ ++ [e] ∈ dom P.engine
      · rw [dif_pos hE]
        have hraw : (engineRaw P (eh₀ ++ [e])).Dom :=
          (mem_dom_validate_concat hok e).mp hE
        rw [engineRaw_concat] at hraw
        obtain ⟨out, houtmem⟩ := Part.dom_iff_mem.mp hraw
        obtain ⟨s₀, hs₀, hmap⟩ := Part.mem_bind_iff.mp houtmem
        obtain ⟨q, hq, hq2⟩ := (Part.mem_map_iff _).mp hmap
        have hstate : P.state eh₀ = Part.some s₀ :=
          Part.eq_some_iff.mpr hs₀
        have hpstep : P.step s₀ e = Part.some q :=
          Part.eq_some_iff.mpr hq
        have hout : output P.engine (eh₀ ++ [e]) hE = out := by
          apply output_validate_of_eq_some
          rw [engineRaw_concat, hstate, Part.bind_some, hpstep,
            Part.map_some, hq2]
        rw [hout, hstate, Part.bind_some, hpstep, Part.bind_some]
        rcases q with ⟨s', out'⟩
        rw [show out = out' from hq2 ▸ rfl]
        rcases out' with v | x
        · rw [Sum.elim_inl, run_answer]
          rfl
        · rw [Sum.elim_inr]
          by_cases hR : rh ++ [x] ∈ dom R
          · rw [dif_pos hR]
            show Part.none = Part.map _ Part.none
            simp
          · rw [dif_neg hR]
            show Part.none = Part.map _ Part.none
            simp
      · rw [dif_neg hE]
        have hraw : ¬(engineRaw P (eh₀ ++ [e])).Dom :=
          fun h => hE ((mem_dom_validate_concat hok e).mpr h)
        rw [engineRaw_concat] at hraw
        have hnone : ((P.state eh₀).bind fun s => P.step s e) =
            Part.none := by
          refine Part.eq_none_iff'.mpr fun h => hraw ?_
          obtain ⟨hs, hp⟩ := h
          exact ⟨hs, hp⟩
        rw [hnone]
        simp
  | succ n ih =>
      intro eh₀ e rh hok
      rw [Connect.serve_succ]
      by_cases hE : eh₀ ++ [e] ∈ dom P.engine
      · rw [dif_pos hE]
        have hraw : (engineRaw P (eh₀ ++ [e])).Dom :=
          (mem_dom_validate_concat hok e).mp hE
        rw [engineRaw_concat] at hraw
        obtain ⟨out, houtmem⟩ := Part.dom_iff_mem.mp hraw
        obtain ⟨s₀, hs₀, hmap⟩ := Part.mem_bind_iff.mp houtmem
        obtain ⟨q, hq, hq2⟩ := (Part.mem_map_iff _).mp hmap
        have hstate : P.state eh₀ = Part.some s₀ :=
          Part.eq_some_iff.mpr hs₀
        have hpstep : P.step s₀ e = Part.some q :=
          Part.eq_some_iff.mpr hq
        have hout : output P.engine (eh₀ ++ [e]) hE = out := by
          apply output_validate_of_eq_some
          rw [engineRaw_concat, hstate, Part.bind_some, hpstep,
            Part.map_some, hq2]
        rw [hout, hstate, Part.bind_some, hpstep, Part.bind_some]
        rcases q with ⟨s', out'⟩
        rw [show out = out' from hq2 ▸ rfl]
        rcases out' with v | x
        · rw [Sum.elim_inl, run_answer]
          rfl
        · rw [Sum.elim_inr]
          by_cases hR : rh ++ [x] ∈ dom R
          · rw [dif_pos hR, run_request _ _ _ _ _ _ _ hR]
            have hstate' : P.state (eh₀ ++ [e]) = Part.some s' := by
              rw [state_append, hstate, Part.bind_some, hpstep,
                Part.map_some]
            have := ih (eh₀ ++ [e])
              (Sum.inr (output R (rh ++ [x]) hR)) (rh ++ [x])
              (Or.inr hE)
            rw [this, hstate', Part.bind_some]
            rfl
          · rw [dif_neg hR, run_request_none _ _ _ _ _ _ _ hR]
            show Part.none = Part.map _ Part.none
            simp
      · rw [dif_neg hE]
        have hraw : ¬(engineRaw P (eh₀ ++ [e])).Dom :=
          fun h => hE ((mem_dom_validate_concat hok e).mpr h)
        rw [engineRaw_concat] at hraw
        have hnone : ((P.state eh₀).bind fun s => P.step s e) =
            Part.none := by
          refine Part.eq_none_iff'.mpr fun h => hraw ?_
          obtain ⟨hs, hp⟩ := h
          exact ⟨hs, hp⟩
        rw [hnone]
        simp

/-- **The round theorem, opening form**: a round on outer query `u`. -/
theorem serve_engine (P : ConverterImpl σ U Y V X) (R : DDS X Y) (n : ℕ)
    (eh : List (U ⊕ Y)) (rh : List X) (u : U)
    (hok : eh = [] ∨ eh ∈ dom P.engine) :
    Connect.serve P.engine R (n + 1) (eh ++ [Sum.inl u], rh) =
      (((P.state eh).bind fun s => P.onQuery s u).bind fun p =>
        P.run R n p (eh ++ [Sum.inl u]) rh).map
          (fun q => (q.1, (q.2.2.1, q.2.2.2))) :=
  serve_step P R n eh (Sum.inl u) rh hok

end ConverterImpl

end

end System

end RandomSystems

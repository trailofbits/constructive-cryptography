/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Cascade

/-!
# The honest cascade equation (CR18 Definition 3.11 via Definition 3.9)

`cascadeViaConverter_eq_cascade` (`Converter.lean`) is `rfl` because its left
side is *defined* as the native cascade.  This module proves the honest
statement: the cascade converter, presented as a protocol function, applied by
Definition 3.9 to the paired-access system, **equals** the native DDS-level
cascade `System.cascade`:

* `apply_cascadeFn` — the transcript-equation form
  `apply cascadeFn (cascadeAccess S T) = S ⊲ₚ T`;
* `apply_toDDC_cascadeFn` — Definition 3.9 applied to the canonical Definition
  3.8 object, `DDC.apply (toDDC cascadeFn) (cascadeAccess S T) = S ⊲ₚ T`,
  by `apply_toDDC`.

Per round the converter forwards the outer input to the left system, feeds the
answer to the right system, and answers the right system's reply outside — a
fixed inner arity of 2, so the round boundary is read off the two history
*lengths* (the `queryLimitFn` idiom) and the proof is a `drive`/`driveOuter`
computation against `cascadeAccess`, not a transcript argument.

Per Definition 3.9 the inner queries are answered by the Definition 3.3
completion `(cascadeAccess S T)⊥`, so a refusal of the paired-access system
arrives as `none` and stalls the converter: `cascadeFn` has no move on an
improper answer, which is exactly where the native cascade is undefined.

## Transport record, against the read-only reference repository

The reference's proven cascade DAG transports **node for node**, with one
forced route delta: this tree has no `CausalApply`, no `DDC.ofStep` and no
`apply_ofStep`, so the converter enters as a `ProtocolFn` and the realization
runs through the ν-level `apply_toDDC` (`Converter/Cascade.lean`).  That
driver answers inner queries with the Definition 3.3 completion and threads a
*cumulative* answer history, so the round boundary `ofStep` read off a reset
inner history is read here off the two history lengths.  Nothing on the cascade
side is dropped or gained by the recast; the combine side's five-node saving
(`CombineRealization.lean`) is proof engineering and is **not** a carrier
consequence — see that header.
-/

namespace RandomSystems

namespace Converter

open scoped System

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}

/-! ### `cascadeMiddle` bookkeeping -/

theorem cascadeMiddle_singleton (S : System.DDS X Y) (x : X)
    (h : [x] ∈ System.dom S) :
    System.cascadeMiddle S [x] h = [System.output S [x] h] := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    have hj : j = 0 := by
      simp only [System.cascadeMiddle_length, List.length_singleton] at hj₁
      omega
    subst hj
    rw [System.cascadeMiddle_getElem]
    simp only [List.getElem_cons_zero]
    exact System.output_congr S (by simp) _ h

theorem cascadeMiddle_snoc (S : System.DDS X Y) {l : List X} {x : X}
    (hl : l ∈ System.dom S) (h : l ++ [x] ∈ System.dom S) :
    System.cascadeMiddle S (l ++ [x]) h
      = System.cascadeMiddle S l hl ++ [System.output S (l ++ [x]) h] := by
  apply List.ext_getElem
  · simp
  · intro j hj₁ hj₂
    rw [System.cascadeMiddle_getElem, List.getElem_append]
    split
    · rename_i hjl
      rw [System.cascadeMiddle_getElem]
      refine System.output_congr S ?_ _ _
      refine List.take_append_of_le_length ?_
      simp only [System.cascadeMiddle_length] at hjl
      omega
    · rename_i hjl
      have hj : j = l.length := by
        simp only [System.cascadeMiddle_length] at hjl
        simp only [System.cascadeMiddle_length, List.length_append,
          List.length_singleton] at hj₁
        omega
      subst hj
      simp only [System.cascadeMiddle_length, Nat.sub_self,
        List.getElem_cons_zero]
      refine System.output_congr S ?_ _ _
      exact List.take_of_length_le (by simp)

/-- Snoc for `cascadeMiddle`, absorbing the empty-prefix case. -/
theorem cascadeMiddle_snoc' (S : System.DDS X Y) {l : List X} {x : X}
    (hl : l ∈ System.dom S ∨ l = []) (h : l ++ [x] ∈ System.dom S)
    (prev : List Y)
    (hprev : ∀ hd : l ∈ System.dom S, prev = System.cascadeMiddle S l hd)
    (hprevnil : l = [] → prev = []) :
    System.cascadeMiddle S (l ++ [x]) h
      = prev ++ [System.output S (l ++ [x]) h] := by
  rcases hl with hd | hnil
  · rw [hprev hd, ← cascadeMiddle_snoc S hd h]
  · subst hnil
    rw [hprevnil rfl]
    simp only [List.nil_append] at h ⊢
    exact cascadeMiddle_singleton S x h

/-! ### Projections of the paired-access history -/

theorem cascadeLeftHistory_snoc_inl (p : List (X ∪ₜ Y)) (x : X) :
    cascadeLeftHistory (p ++ [Sum.inl x]) = cascadeLeftHistory p ++ [x] := by
  rw [cascadeLeftHistory_append]
  rfl

theorem cascadeLeftHistory_snoc_inr (p : List (X ∪ₜ Y)) (y : Y) :
    cascadeLeftHistory (p ++ [Sum.inr y]) = cascadeLeftHistory p := by
  rw [cascadeLeftHistory_append]
  simp [cascadeLeftHistory]

theorem cascadeRightHistory_snoc_inl (p : List (X ∪ₜ Y)) (x : X) :
    cascadeRightHistory (p ++ [Sum.inl x]) = cascadeRightHistory p := by
  rw [cascadeRightHistory_append]
  simp [cascadeRightHistory]

theorem cascadeRightHistory_snoc_inr (p : List (X ∪ₜ Y)) (y : Y) :
    cascadeRightHistory (p ++ [Sum.inr y]) = cascadeRightHistory p ++ [y] := by
  rw [cascadeRightHistory_append]
  rfl

/-! ### Evaluating the paired-access system -/

/-- A left query extends the accepted access history whenever the left system
accepts it. -/
theorem cascadeAccess_dom_snoc_inl (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {x : X}
    (hp : p = [] ∨ p ∈ System.dom (cascadeAccess S T))
    (hL : cascadeLeftHistory p ++ [x] ∈ System.dom S) :
    p ++ [Sum.inl x] ∈ System.dom (cascadeAccess S T) := by
  refine cascadeAccess_dom_snoc S T hp ?_
  have hlast : (p ++ [Sum.inl x]).getLast? = some (Sum.inl x) := by simp
  simp only [cascadeAccessStep, hlast]
  rw [cascadeLeftHistory_snoc_inl]
  exact hL

/-- A right query extends the accepted access history whenever the right system
accepts it. -/
theorem cascadeAccess_dom_snoc_inr (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {y : Y}
    (hp : p = [] ∨ p ∈ System.dom (cascadeAccess S T))
    (hR : cascadeRightHistory p ++ [y] ∈ System.dom T) :
    p ++ [Sum.inr y] ∈ System.dom (cascadeAccess S T) := by
  refine cascadeAccess_dom_snoc S T hp ?_
  have hlast : (p ++ [Sum.inr y]).getLast? = some (Sum.inr y) := by simp
  simp only [cascadeAccessStep, hlast]
  rw [cascadeRightHistory_snoc_inr]
  exact hR

/-- The paired-access system's value on a left query, as an equation. -/
theorem cascadeAccess_eval_inl (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {x : X}
    (hp : p = [] ∨ p ∈ System.dom (cascadeAccess S T))
    (hL : cascadeLeftHistory p ++ [x] ∈ System.dom S) :
    (cascadeAccess S T).1 (p ++ [Sum.inl x])
      = Part.some (Sum.inl
          (System.output S (cascadeLeftHistory p ++ [x]) hL)) := by
  have hlast : (p ++ [Sum.inl x]).getLast? = some (Sum.inl x) := by simp
  have hLfull : cascadeLeftHistory (p ++ [Sum.inl x]) ∈ System.dom S := by
    rw [cascadeLeftHistory_snoc_inl]
    exact hL
  have hdom : p ++ [Sum.inl x] ∈ System.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc_inl S T hp hL
  have hout := cascadeAccess_output_inl S T hdom hlast hLfull
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans (congrArg Sum.inl ?_)
  exact System.output_congr S (cascadeLeftHistory_snoc_inl p x) hLfull hL

/-- The paired-access system's value on a right query, as an equation. -/
theorem cascadeAccess_eval_inr (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {y : Y}
    (hp : p = [] ∨ p ∈ System.dom (cascadeAccess S T))
    (hR : cascadeRightHistory p ++ [y] ∈ System.dom T) :
    (cascadeAccess S T).1 (p ++ [Sum.inr y])
      = Part.some (Sum.inr
          (System.output T (cascadeRightHistory p ++ [y]) hR)) := by
  have hlast : (p ++ [Sum.inr y]).getLast? = some (Sum.inr y) := by simp
  have hRfull : cascadeRightHistory (p ++ [Sum.inr y]) ∈ System.dom T := by
    rw [cascadeRightHistory_snoc_inr]
    exact hR
  have hdom : p ++ [Sum.inr y] ∈ System.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc_inr S T hp hR
  have hout := cascadeAccess_output_inr S T hdom hlast hRfull
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans (congrArg Sum.inr ?_)
  exact System.output_congr T (cascadeRightHistory_snoc_inr p y) hRfull hR

/-- Prefix witness for a concatenated access history. -/
theorem cascadeAccess_dom_or_nil (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {a : X ∪ₜ Y}
    (hdom : p ++ [a] ∈ System.dom (cascadeAccess S T)) :
    p = [] ∨ p ∈ System.dom (cascadeAccess S T) := by
  rcases List.eq_nil_or_concat p with rfl | ⟨p', a', rfl⟩
  · exact Or.inl rfl
  · right
    refine ⟨by simp, ?_⟩
    intro q hqne hq
    exact hdom.2 q hqne (hq.trans (List.prefix_append _ _))

/-- Membership destructor for a left query. -/
theorem cascadeAccess_mem_inl_elim (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {x : X} {a : Y ∪ₜ Z}
    (ha : a ∈ (cascadeAccess S T).1 (p ++ [Sum.inl x])) :
    ∃ hL : cascadeLeftHistory p ++ [x] ∈ System.dom S,
      a = Sum.inl (System.output S (cascadeLeftHistory p ++ [x]) hL) := by
  have hdom : p ++ [Sum.inl x] ∈ System.dom (cascadeAccess S T) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hlast : (p ++ [Sum.inl x]).getLast? = some (Sum.inl x) := by simp
  have hstep : cascadeAccessStep S T (p ++ [Sum.inl x]) :=
    hdom.2 (p ++ [Sum.inl x]) (by simp) (List.prefix_refl _)
  have hLfull : cascadeLeftHistory (p ++ [Sum.inl x]) ∈ System.dom S := by
    simpa only [cascadeAccessStep, hlast] using hstep
  have hL : cascadeLeftHistory p ++ [x] ∈ System.dom S := by
    rw [← cascadeLeftHistory_snoc_inl]
    exact hLfull
  refine ⟨hL, ?_⟩
  have hval := cascadeAccess_eval_inl S T
    (cascadeAccess_dom_or_nil S T hdom) hL
  rw [hval, Part.mem_some_iff] at ha
  exact ha

/-- Membership destructor for a right query. -/
theorem cascadeAccess_mem_inr_elim (S : System.DDS X Y) (T : System.DDS Y Z)
    {p : List (X ∪ₜ Y)} {y : Y} {a : Y ∪ₜ Z}
    (ha : a ∈ (cascadeAccess S T).1 (p ++ [Sum.inr y])) :
    ∃ hR : cascadeRightHistory p ++ [y] ∈ System.dom T,
      a = Sum.inr (System.output T (cascadeRightHistory p ++ [y]) hR) := by
  have hdom : p ++ [Sum.inr y] ∈ System.dom (cascadeAccess S T) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hlast : (p ++ [Sum.inr y]).getLast? = some (Sum.inr y) := by simp
  have hstep : cascadeAccessStep S T (p ++ [Sum.inr y]) :=
    hdom.2 (p ++ [Sum.inr y]) (by simp) (List.prefix_refl _)
  have hRfull : cascadeRightHistory (p ++ [Sum.inr y]) ∈ System.dom T := by
    simpa only [cascadeAccessStep, hlast] using hstep
  have hR : cascadeRightHistory p ++ [y] ∈ System.dom T := by
    rw [← cascadeRightHistory_snoc_inr]
    exact hRfull
  refine ⟨hR, ?_⟩
  have hval := cascadeAccess_eval_inr S T
    (cascadeAccess_dom_or_nil S T hdom) hR
  rw [hval, Part.mem_some_iff] at ha
  exact ha

/-! ### The cascade converter as a protocol function -/

/-- **The cascade converter** (CR18 Definition 3.11's `casc`) as a protocol
function: forward the outer input to the left system, feed its answer to the
right system, answer the right system's reply outside.

The round boundary is read off the history lengths — two inner queries per
outer input — in the `queryLimitFn` idiom.  As everywhere under the
`Y ∪ {⊥}` alphabet, the two answer branches fire only on a proper answer of
the expected side, so a refusal of the paired-access system leaves the
converter with no move. -/
def cascadeFn : ProtocolFn X Z (X ∪ₜ Y) (Y ∪ₜ Z) := fun p =>
  if p.2.length + 2 = 2 * p.1.length then
    match p.1.getLast? with
    | some u => Part.some (Sum.inl (Sum.inl u))
    | none => Part.none
  else if p.2.length + 1 = 2 * p.1.length then
    match p.2.getLast? with
    | some (some (Sum.inl y)) => Part.some (Sum.inl (Sum.inr y))
    | _ => Part.none
  else if p.2.length = 2 * p.1.length ∧ 0 < p.2.length then
    match p.2.getLast? with
    | some (some (Sum.inr z)) => Part.some (Sum.inr z)
    | _ => Part.none
  else Part.none

/-- Move constructor, left query: at a round boundary the converter forwards
the last outer input to the left system. -/
theorem cascadeFn_left_mem {us : List X} {ys : List (Option (Y ∪ₜ Z))} {u : X}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u) :
    Sum.inl (Sum.inl u) ∈ cascadeFn (X := X) (Y := Y) (Z := Z) (us, ys) := by
  simp only [cascadeFn, if_pos hlen, hu]
  exact Part.mem_some _

/-- Move constructor, right query: after a proper left answer the converter
forwards it to the right system. -/
theorem cascadeFn_right_mem {us : List X} {ys : List (Option (Y ∪ₜ Z))} {y : Y}
    (hlen : ys.length + 1 = 2 * us.length)
    (hy : ys.getLast? = some (some (Sum.inl y))) :
    Sum.inl (Sum.inr y) ∈ cascadeFn (X := X) (Y := Y) (Z := Z) (us, ys) := by
  have hne : ¬ (ys.length + 2 = 2 * us.length) := by omega
  simp only [cascadeFn, if_neg hne, if_pos hlen, hy]
  exact Part.mem_some _

/-- Move constructor, outer answer: after a proper right answer the converter
delivers it outside. -/
theorem cascadeFn_answer_mem {us : List X} {ys : List (Option (Y ∪ₜ Z))} {z : Z}
    (hlen : ys.length = 2 * us.length) (h0 : 0 < ys.length)
    (hz : ys.getLast? = some (some (Sum.inr z))) :
    Sum.inr z ∈ cascadeFn (X := X) (Y := Y) (Z := Z) (us, ys) := by
  have hneA : ¬ (ys.length + 2 = 2 * us.length) := by omega
  have hneB : ¬ (ys.length + 1 = 2 * us.length) := by omega
  simp only [cascadeFn, if_neg hneA, if_neg hneB,
    if_pos (And.intro hlen h0), hz]
  exact Part.mem_some _

/-- Move inversion, query branch: an inner query is either the last outer
input (round boundary) or the forwarded proper left answer. -/
theorem cascadeFn_inl_inv {us : List X} {ys : List (Option (Y ∪ₜ Z))}
    {q : X ∪ₜ Y}
    (h : Sum.inl q ∈ cascadeFn (X := X) (Y := Y) (Z := Z) (us, ys)) :
    (ys.length + 2 = 2 * us.length ∧
        ∃ u, q = Sum.inl u ∧ us.getLast? = some u) ∨
      (ys.length + 1 = 2 * us.length ∧
        ∃ y, q = Sum.inr y ∧ ys.getLast? = some (some (Sum.inl y))) := by
  simp only [cascadeFn] at h
  split_ifs at h with h1 h2 h3
  · rcases hu : us.getLast? with _ | u
    · rw [hu] at h; simp at h
    · rw [hu] at h
      simp only [Part.mem_some_iff, Sum.inl.injEq] at h
      subst h
      exact Or.inl ⟨h1, u, rfl, rfl⟩
  · rcases hy : ys.getLast? with _ | oy
    · rw [hy] at h; simp at h
    · rcases oy with _ | a
      · rw [hy] at h; simp at h
      · rcases a with y | z
        · rw [hy] at h
          simp only [Part.mem_some_iff, Sum.inl.injEq] at h
          subst h
          exact Or.inr ⟨h2, y, rfl, rfl⟩
        · rw [hy] at h; simp at h
  · rcases hy : ys.getLast? with _ | oy
    · rw [hy] at h; simp at h
    · rcases oy with _ | a
      · rw [hy] at h; simp at h
      · rcases a with y | z
        · rw [hy] at h; simp at h
        · rw [hy] at h; simp at h
  · simp at h

/-- Move inversion, outer-answer branch. -/
theorem cascadeFn_inr_inv {us : List X} {ys : List (Option (Y ∪ₜ Z))}
    {v : Z} (h : Sum.inr v ∈ cascadeFn (X := X) (Y := Y) (Z := Z) (us, ys)) :
    ys.length = 2 * us.length ∧ 0 < ys.length ∧
      ys.getLast? = some (some (Sum.inr v)) := by
  simp only [cascadeFn] at h
  split_ifs at h with h1 h2 h3
  · rcases hu : us.getLast? with _ | u
    · rw [hu] at h; simp at h
    · rw [hu] at h; simp at h
  · rcases hy : ys.getLast? with _ | oy
    · rw [hy] at h; simp at h
    · rcases oy with _ | a
      · rw [hy] at h; simp at h
      · rcases a with y | z
        · rw [hy] at h; simp at h
        · rw [hy] at h; simp at h
  · rcases hy : ys.getLast? with _ | oy
    · rw [hy] at h; simp at h
    · rcases oy with _ | a
      · rw [hy] at h; simp at h
      · rcases a with y | z
        · rw [hy] at h; simp at h
        · rw [hy] at h
          simp only [Part.mem_some_iff, Sum.inr.injEq] at h
          subst h
          exact ⟨h3.1, h3.2, rfl⟩
  · simp at h

/-! ### One cascade round -/

/-- One cascade round, computed: query the left system with the outer input,
feed its answer to the right system, and deliver the right system's answer
outside.  The access history grows by the woven pair. -/
theorem drive_cascadeFn_round_mem (S : System.DDS X Y) (T : System.DDS Y Z)
    {us : List X} {ys : List (Option (Y ∪ₜ Z))} {xs : List (X ∪ₜ Y)} {u : X}
    {y₁ : Y} {z₁ : Z}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u)
    (hxs : xs ∈ System.dom (cascadeAccess S T) ∨ xs = [])
    (hL : cascadeLeftHistory xs ++ [u] ∈ System.dom S)
    (hy₁ : System.output S (cascadeLeftHistory xs ++ [u]) hL = y₁)
    (hT : cascadeRightHistory xs ++ [y₁] ∈ System.dom T)
    (hz₁ : System.output T (cascadeRightHistory xs ++ [y₁]) hT = z₁) :
    (z₁, xs ++ [Sum.inl u] ++ [Sum.inr y₁],
        ys ++ [some (Sum.inl y₁)] ++ [some (Sum.inr z₁)])
      ∈ drive cascadeFn (cascadeAccess S T) 3 us xs ys := by
  have hlastL : (xs ++ [Sum.inl u]).getLast? = some (Sum.inl u) := by simp
  have hLfull : cascadeLeftHistory (xs ++ [Sum.inl u]) ∈ System.dom S := by
    rw [cascadeLeftHistory_snoc_inl]; exact hL
  have hdom₁ : xs ++ [Sum.inl u] ∈ System.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc_inl S T hxs.symm hL
  have hout₁ : System.output (cascadeAccess S T) (xs ++ [Sum.inl u]) hdom₁
      = Sum.inl y₁ := by
    refine (cascadeAccess_output_inl S T hdom₁ hlastL hLfull).trans ?_
    exact congrArg Sum.inl
      ((System.output_congr S (cascadeLeftHistory_snoc_inl xs u) hLfull hL).trans hy₁)
  have hans₁ : System.output ((cascadeAccess S T)⊥) (xs ++ [Sum.inl u])
      (by rw [System.dom_fullyDefined]; simp) = some (Sum.inl y₁) := by
    rw [System.output_fullyDefined_append_of_mem (cascadeAccess S T) xs
      (Sum.inl u) hxs hdom₁, hout₁]
  refine drive_mem_query cascadeFn (cascadeAccess S T)
    (cascadeFn_left_mem hlen hu) ?_
  rw [hans₁]
  have hlen₂ : (ys ++ [some (Sum.inl y₁)]).length + 1 = 2 * us.length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hy₂ : (ys ++ [some (Sum.inl y₁)]).getLast?
      = some (some (Sum.inl y₁)) := by simp
  have hR₁ : cascadeRightHistory (xs ++ [Sum.inl u]) ++ [y₁] ∈ System.dom T := by
    rw [cascadeRightHistory_snoc_inl]; exact hT
  have hlastR : ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁]).getLast?
      = some (Sum.inr y₁) := by simp
  have hRfull : cascadeRightHistory ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁])
      ∈ System.dom T := by
    rw [cascadeRightHistory_snoc_inr]; exact hR₁
  have hdom₂ : (xs ++ [Sum.inl u]) ++ [Sum.inr y₁]
      ∈ System.dom (cascadeAccess S T) :=
    cascadeAccess_dom_snoc_inr S T (Or.inr hdom₁) hR₁
  have hout₂ : System.output (cascadeAccess S T)
      ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁]) hdom₂ = Sum.inr z₁ := by
    refine (cascadeAccess_output_inr S T hdom₂ hlastR hRfull).trans ?_
    refine congrArg Sum.inr ?_
    refine (System.output_congr T ?_ hRfull hT).trans hz₁
    rw [cascadeRightHistory_snoc_inr, cascadeRightHistory_snoc_inl]
  have hans₂ : System.output ((cascadeAccess S T)⊥)
      ((xs ++ [Sum.inl u]) ++ [Sum.inr y₁])
      (by rw [System.dom_fullyDefined]; simp) = some (Sum.inr z₁) := by
    rw [System.output_fullyDefined_append_of_mem (cascadeAccess S T)
      (xs ++ [Sum.inl u]) (Sum.inr y₁) (Or.inl hdom₁) hdom₂, hout₂]
  refine drive_mem_query cascadeFn (cascadeAccess S T)
    (cascadeFn_right_mem hlen₂ hy₂) ?_
  rw [hans₂]
  exact drive_mem_answer cascadeFn (cascadeAccess S T)
    (cascadeFn_answer_mem
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp) (by simp)) 0

/-- One cascade round, destructed: a successful round certifies both system
domains and pins the whole round. -/
theorem drive_cascadeFn_round_elim (S : System.DDS X Y) (T : System.DDS Y Z)
    {us : List X} {ys : List (Option (Y ∪ₜ Z))} {xs : List (X ∪ₜ Y)} {u : X}
    {fuel : ℕ} {p : Z × List (X ∪ₜ Y) × List (Option (Y ∪ₜ Z))}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u)
    (hxs : xs ∈ System.dom (cascadeAccess S T) ∨ xs = [])
    (hp : p ∈ drive cascadeFn (cascadeAccess S T) fuel us xs ys) :
    ∃ (hL : cascadeLeftHistory xs ++ [u] ∈ System.dom S)
      (hT : cascadeRightHistory xs ++
          [System.output S (cascadeLeftHistory xs ++ [u]) hL] ∈ System.dom T),
      p = (System.output T (cascadeRightHistory xs ++
              [System.output S (cascadeLeftHistory xs ++ [u]) hL]) hT,
        xs ++ [Sum.inl u] ++
          [Sum.inr (System.output S (cascadeLeftHistory xs ++ [u]) hL)],
        ys ++ [some (Sum.inl (System.output S (cascadeLeftHistory xs ++ [u]) hL))]
          ++ [some (Sum.inr (System.output T (cascadeRightHistory xs ++
              [System.output S (cascadeLeftHistory xs ++ [u]) hL]) hT))]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
  swap
  · exact absurd (cascadeFn_inr_inv hm).1 (by omega)
  rcases cascadeFn_inl_inv hm with ⟨-, u', rfl, hu'⟩ | ⟨hbad, -⟩
  swap
  · exact absurd hbad (by omega)
  obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
  rcases fuel with _ | fuel
  · simp [drive] at hp'
  rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
  swap
  · exact absurd (cascadeFn_inr_inv hm₂).1
      (by simp only [List.length_append, List.length_singleton]; omega)
  rcases cascadeFn_inl_inv hm₂ with ⟨hbad, -⟩ | ⟨-, y₁, rfl, hy₁⟩
  · exact absurd hbad
      (by simp only [List.length_append, List.length_singleton]; omega)
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hy₁
  obtain ⟨hdom₁, hout₁⟩ :=
    System.mem_of_output_fullyDefined_append_eq_some (cascadeAccess S T) xs
      (Sum.inl u) hxs hy₁
  have hmem₁ : Sum.inl y₁ ∈ (cascadeAccess S T).1 (xs ++ [Sum.inl u]) := by
    rw [← hout₁]; exact Part.get_mem hdom₁
  obtain ⟨hL, hEq₁⟩ := cascadeAccess_mem_inl_elim S T hmem₁
  obtain rfl : y₁ = System.output S (cascadeLeftHistory xs ++ [u]) hL :=
    Sum.inl.inj hEq₁
  rw [hy₁] at hp''
  rcases fuel with _ | fuel
  · simp [drive] at hp''
  rcases drive_succ_elim hp'' with ⟨x₃, hm₃, -⟩ | ⟨v₃, hm₃, rfl⟩
  · rcases cascadeFn_inl_inv hm₃ with ⟨hbad, -⟩ | ⟨hbad, -⟩ <;>
      exact absurd hbad
        (by simp only [List.length_append, List.length_singleton]; omega)
  obtain ⟨-, -, hy₂⟩ := cascadeFn_inr_inv hm₃
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at hy₂
  obtain ⟨hdom₂, hout₂⟩ :=
    System.mem_of_output_fullyDefined_append_eq_some (cascadeAccess S T)
      (xs ++ [Sum.inl u]) (Sum.inr _) (Or.inl hdom₁) hy₂
  have hmem₂ : Sum.inr v₃ ∈ (cascadeAccess S T).1
      ((xs ++ [Sum.inl u]) ++ [Sum.inr
        (System.output S (cascadeLeftHistory xs ++ [u]) hL)]) := by
    rw [← hout₂]; exact Part.get_mem hdom₂
  obtain ⟨hR, hEq₂⟩ := cascadeAccess_mem_inr_elim S T hmem₂
  have hmid : cascadeRightHistory (xs ++ [Sum.inl u]) ++
      [System.output S (cascadeLeftHistory xs ++ [u]) hL]
        = cascadeRightHistory xs ++
          [System.output S (cascadeLeftHistory xs ++ [u]) hL] := by
    rw [cascadeRightHistory_snoc_inl]
  have hT : cascadeRightHistory xs ++
      [System.output S (cascadeLeftHistory xs ++ [u]) hL] ∈ System.dom T := by
    rw [← hmid]; exact hR
  have hval : v₃ = System.output T (cascadeRightHistory xs ++
      [System.output S (cascadeLeftHistory xs ++ [u]) hL]) hT :=
    (Sum.inr.inj hEq₂).trans (System.output_congr T hmid hR hT)
  exact ⟨hL, hT, by rw [hy₂, hval]⟩

/-! ### The outer fold -/

/-- Forward run of the cascade converter over a whole outer history.

The threaded invariant is the reference's: the access history is accepted, its
left projection is a left-system history, and its right projection is the
`cascadeMiddle` of that left history — plus the ν-level round-boundary
invariant `ys.length = 2 * usPre.length`. -/
theorem driveOuter_cascadeFn_of_dom (S : System.DDS X Y) (T : System.DDS Y Z) :
    ∀ (rest usPre : List X) (xs : List (X ∪ₜ Y))
      (ys : List (Option (Y ∪ₜ Z))),
      ys.length = 2 * usPre.length →
      (xs ∈ System.dom (cascadeAccess S T) ∨ xs = []) →
      (cascadeLeftHistory xs ∈ System.dom S ∨ cascadeLeftHistory xs = []) →
      (∀ h : cascadeLeftHistory xs ∈ System.dom S,
        cascadeRightHistory xs
          = System.cascadeMiddle S (cascadeLeftHistory xs) h) →
      (cascadeLeftHistory xs = [] → cascadeRightHistory xs = []) →
      ((∃ hS : cascadeLeftHistory xs ++ rest ∈ System.dom S,
          System.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
            ∈ System.dom T) ∨ rest = []) →
      ∃ vs xs' ys',
        (vs, xs', ys') ∈
          driveOuter cascadeFn (cascadeAccess S T) 3 usPre xs ys rest ∧
        ∀ (hS : cascadeLeftHistory xs ++ rest ∈ System.dom S)
          (hT : System.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
            ∈ System.dom T),
          rest ≠ [] →
            vs.getLast? = some (System.output T
              (System.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS) hT) := by
  intro rest
  induction rest with
  | nil =>
      intro usPre xs ys _ _ _ _ _ _
      exact ⟨[], xs, ys, by simp [driveOuter],
        fun _ _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro usPre xs ys hlen hxs hSpre hRinv hRnil hfull
      obtain ⟨hSfull, hTfull⟩ :
          ∃ hS : cascadeLeftHistory xs ++ u :: rest ∈ System.dom S,
            System.cascadeMiddle S (cascadeLeftHistory xs ++ u :: rest) hS
              ∈ System.dom T := by
        rcases hfull with h | h
        · exact h
        · exact absurd h (by simp)
      have hS₁ : cascadeLeftHistory xs ++ [u] ∈ System.dom S :=
        System.prefix_closed S ⟨rest, by simp⟩ (by simp) hSfull
      have hT₁ : System.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          ∈ System.dom T :=
        System.prefix_closed T
          (System.cascadeMiddle_prefix S hS₁ hSfull ⟨rest, by simp⟩)
          (System.cascadeMiddle_ne_nil S _ hS₁) hTfull
      set y₁ := System.output S (cascadeLeftHistory xs ++ [u]) hS₁ with hy₁def
      have hmid : System.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          = cascadeRightHistory xs ++ [y₁] :=
        cascadeMiddle_snoc' S hSpre hS₁ _ hRinv hRnil
      have hTround : cascadeRightHistory xs ++ [y₁] ∈ System.dom T := by
        rw [← hmid]; exact hT₁
      set z₁ := System.output T (cascadeRightHistory xs ++ [y₁]) hTround
        with hz₁def
      have hround := drive_cascadeFn_round_mem S T
        (us := usPre ++ [u]) (ys := ys) (xs := xs) (u := u)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp) hxs hS₁ rfl hTround rfl
      have hdom₁ : xs ++ [Sum.inl u] ∈ System.dom (cascadeAccess S T) :=
        cascadeAccess_dom_snoc_inl S T hxs.symm hS₁
      have hR₁ : cascadeRightHistory (xs ++ [Sum.inl u]) ++ [y₁]
          ∈ System.dom T := by
        rw [cascadeRightHistory_snoc_inl]; exact hTround
      have hdomxs' : xs ++ [Sum.inl u] ++ [Sum.inr y₁]
          ∈ System.dom (cascadeAccess S T) :=
        cascadeAccess_dom_snoc_inr S T (Or.inr hdom₁) hR₁
      have hLxs' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          = cascadeLeftHistory xs ++ [u] := by
        rw [cascadeLeftHistory_snoc_inr, cascadeLeftHistory_snoc_inl]
      have hRxs' : cascadeRightHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          = cascadeRightHistory xs ++ [y₁] := by
        rw [cascadeRightHistory_snoc_inr, cascadeRightHistory_snoc_inl]
      have hSpre' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          ∈ System.dom S
          ∨ cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) = [] := by
        rw [hLxs']; exact Or.inl hS₁
      have hRinv' : ∀ h : cascadeLeftHistory
            (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ∈ System.dom S,
          cascadeRightHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
            = System.cascadeMiddle S
                (cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])) h := by
        intro h
        rw [hRxs', ← hmid]
        exact System.cascadeMiddle_congr S hLxs'.symm hS₁ h
      have hRnil' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) = []
          → cascadeRightHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) = [] := by
        intro h
        rw [hLxs'] at h
        exact absurd h (by simp)
      have hlist : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ++ rest
          = cascadeLeftHistory xs ++ u :: rest := by
        rw [hLxs', List.append_assoc]
        rfl
      have hSfull' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          ++ rest ∈ System.dom S := by
        rw [hlist]; exact hSfull
      have hfull' : (∃ hS : cascadeLeftHistory
            (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ++ rest ∈ System.dom S,
          System.cascadeMiddle S
              (cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ++ rest) hS
            ∈ System.dom T) ∨ rest = [] := by
        refine Or.inl ⟨hSfull', ?_⟩
        rw [System.cascadeMiddle_congr S hlist hSfull' hSfull]
        exact hTfull
      obtain ⟨vs', xs'', ys'', hmem', hlast'⟩ :=
        ih (usPre ++ [u]) (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          (ys ++ [some (Sum.inl y₁)] ++ [some (Sum.inr z₁)])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (Or.inl hdomxs') hSpre' hRinv' hRnil' hfull'
      refine ⟨z₁ :: vs', xs'', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(z₁, xs ++ [Sum.inl u] ++ [Sum.inr y₁],
          ys ++ [some (Sum.inl y₁)] ++ [some (Sum.inr z₁)]), hround,
          (vs', xs'', ys''), hmem', rfl⟩
      · intro hS hT hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length cascadeFn (cascadeAccess S T) 3 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
            refine congrArg some ?_
            refine System.output_congr T ?_ hTround hT
            rw [← hmid]
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length cascadeFn (cascadeAccess S T) 3 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have hT' : System.cascadeMiddle S
                (cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ++ rest)
                hSfull' ∈ System.dom T := by
              rw [System.cascadeMiddle_congr S hlist hSfull' hSfull]
              exact hTfull
            have hlast'' := hlast' hSfull' hT' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            refine congrArg some ?_
            refine System.output_congr T ?_ hT' hT
            exact System.cascadeMiddle_congr S hlist hSfull' hS

/-- Backward run analysis of the cascade converter: every defined nonempty run
certifies both system domains and pins the delivered answer. -/
theorem driveOuter_cascadeFn_mem_imp (S : System.DDS X Y) (T : System.DDS Y Z) :
    ∀ (rest usPre : List X) (xs : List (X ∪ₜ Y))
      (ys : List (Option (Y ∪ₜ Z))) {fuel : ℕ}
      {r : List Z × List (X ∪ₜ Y) × List (Option (Y ∪ₜ Z))},
      ys.length = 2 * usPre.length →
      (xs ∈ System.dom (cascadeAccess S T) ∨ xs = []) →
      (cascadeLeftHistory xs ∈ System.dom S ∨ cascadeLeftHistory xs = []) →
      (∀ h : cascadeLeftHistory xs ∈ System.dom S,
        cascadeRightHistory xs
          = System.cascadeMiddle S (cascadeLeftHistory xs) h) →
      (cascadeLeftHistory xs = [] → cascadeRightHistory xs = []) →
      r ∈ driveOuter cascadeFn (cascadeAccess S T) fuel usPre xs ys rest →
      rest ≠ [] →
      ∃ (hS : cascadeLeftHistory xs ++ rest ∈ System.dom S)
        (hT : System.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS
          ∈ System.dom T),
        r.1.getLast? = some (System.output T
          (System.cascadeMiddle S (cascadeLeftHistory xs ++ rest) hS) hT) := by
  intro rest
  induction rest with
  | nil =>
      intro usPre xs ys fuel r _ _ _ _ _ _ hne
      exact absurd rfl hne
  | cons u rest ih =>
      intro usPre xs ys fuel r hlen hxs hSpre hRinv hRnil hr _
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hS₁, hTround, rfl⟩ := drive_cascadeFn_round_elim S T
        (us := usPre ++ [u]) (u := u)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp) hxs hr₁
      set y₁ := System.output S (cascadeLeftHistory xs ++ [u]) hS₁ with hy₁def
      set z₁ := System.output T (cascadeRightHistory xs ++ [y₁]) hTround
        with hz₁def
      have hmid : System.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          = cascadeRightHistory xs ++ [y₁] :=
        cascadeMiddle_snoc' S hSpre hS₁ _ hRinv hRnil
      have hT₁ : System.cascadeMiddle S (cascadeLeftHistory xs ++ [u]) hS₁
          ∈ System.dom T := by
        rw [hmid]; exact hTround
      have hdom₁ : xs ++ [Sum.inl u] ∈ System.dom (cascadeAccess S T) :=
        cascadeAccess_dom_snoc_inl S T hxs.symm hS₁
      have hR₁ : cascadeRightHistory (xs ++ [Sum.inl u]) ++ [y₁]
          ∈ System.dom T := by
        rw [cascadeRightHistory_snoc_inl]; exact hTround
      have hdomxs' : xs ++ [Sum.inl u] ++ [Sum.inr y₁]
          ∈ System.dom (cascadeAccess S T) :=
        cascadeAccess_dom_snoc_inr S T (Or.inr hdom₁) hR₁
      have hLxs' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          = cascadeLeftHistory xs ++ [u] := by
        rw [cascadeLeftHistory_snoc_inr, cascadeLeftHistory_snoc_inl]
      have hRxs' : cascadeRightHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
          = cascadeRightHistory xs ++ [y₁] := by
        rw [cascadeRightHistory_snoc_inr, cascadeRightHistory_snoc_inl]
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨hS₁, hT₁, ?_⟩
          rw [List.getLast?_singleton]
          exact congrArg some (System.output_congr T hmid.symm hTround hT₁)
      | cons r0 rs0 =>
          have hSpre' : cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
              ∈ System.dom S
              ∨ cascadeLeftHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
                = [] := by
            rw [hLxs']; exact Or.inl hS₁
          have hRinv' : ∀ h : cascadeLeftHistory
                (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ∈ System.dom S,
              cascadeRightHistory (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
                = System.cascadeMiddle S
                    (cascadeLeftHistory
                      (xs ++ [Sum.inl u] ++ [Sum.inr y₁])) h := by
            intro h
            rw [hRxs', ← hmid]
            exact System.cascadeMiddle_congr S hLxs'.symm hS₁ h
          have hRnil' : cascadeLeftHistory
                (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) = []
              → cascadeRightHistory
                (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) = [] := by
            intro h
            rw [hLxs'] at h
            exact absurd h (by simp)
          obtain ⟨hS', hT', hlast'⟩ :=
            ih (usPre ++ [u]) (xs ++ [Sum.inl u] ++ [Sum.inr y₁])
              (ys ++ [some (Sum.inl y₁)] ++ [some (Sum.inr z₁)])
              (by simp only [List.length_append, List.length_singleton]; omega)
              (Or.inl hdomxs') hSpre' hRinv' hRnil' hrr (by simp [hrest])
          have hlist : cascadeLeftHistory
                (xs ++ [Sum.inl u] ++ [Sum.inr y₁]) ++ rest
              = cascadeLeftHistory xs ++ u :: rest := by
            rw [hLxs', List.append_assoc]
            rfl
          rw [← hrest]
          have hS : cascadeLeftHistory xs ++ u :: rest ∈ System.dom S := by
            rw [← hlist]; exact hS'
          have hT : System.cascadeMiddle S
              (cascadeLeftHistory xs ++ u :: rest) hS ∈ System.dom T := by
            rw [← System.cascadeMiddle_congr S hlist hS' hS]
            exact hT'
          refine ⟨hS, hT, ?_⟩
          have hlenrr := driveOuter_length cascadeFn (cascadeAccess S T) fuel hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              refine congrArg some ?_
              refine System.output_congr T ?_ hT' hT
              exact System.cascadeMiddle_congr S hlist hS' hS

/-! ### The honest cascade equation -/

/-- Membership characterization of the native cascade. -/
theorem mem_cascade_iff (S : System.DDS X Y) (T : System.DDS Y Z)
    (l : List X) (z : Z) :
    z ∈ (System.cascade S T).1 l ↔
      ∃ (hS : l ∈ System.dom S)
        (hT : System.cascadeMiddle S l hS ∈ System.dom T),
        z = System.output T (System.cascadeMiddle S l hS) hT := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h.choose, h.choose_spec, rfl⟩
  · rintro ⟨hS, hT, rfl⟩
    refine ⟨⟨hS, hT⟩, ?_⟩
    exact System.output_congr T
      (System.cascadeMiddle_congr S rfl _ hS) _ hT

/-- **The cascade converter, applied**: the transcript-equation application of
`cascadeFn` to the paired-access system is the native DDS-level cascade. -/
theorem apply_cascadeFn (S : System.DDS X Y) (T : System.DDS Y Z) :
    apply cascadeFn (cascadeAccess S T) = System.cascade S T := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro z
  rw [show (apply cascadeFn (cascadeAccess S T)).1
      = applyRaw cascadeFn (cascadeAccess S T) from rfl, mem_applyRaw,
    mem_cascade_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length cascadeFn (cascadeAccess S T) fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨hS, hT, hout⟩ := driveOuter_cascadeFn_mem_imp S T us [] [] []
      rfl (Or.inr rfl) (Or.inr rfl)
      (fun h => absurd h (System.empty_not_mem S)) (fun _ => rfl) hr hne
    rw [hlast] at hout
    have hz := Option.some.inj hout
    refine ⟨by simpa [cascadeLeftHistory] using hS, ?_, ?_⟩
    · rw [← System.cascadeMiddle_congr S
        (by simp [cascadeLeftHistory] :
          cascadeLeftHistory ([] : List (X ∪ₜ Y)) ++ us = us) hS _]
      exact hT
    · rw [hz]
      refine System.output_congr T ?_ hT _
      exact System.cascadeMiddle_congr S (by simp [cascadeLeftHistory]) hS _
  · rintro ⟨hS, hT, rfl⟩
    have hne : us ≠ [] := by
      rintro rfl
      exact System.empty_not_mem S hS
    have hS0 : cascadeLeftHistory ([] : List (X ∪ₜ Y)) ++ us
        ∈ System.dom S := by
      simpa [cascadeLeftHistory] using hS
    have hT0 : System.cascadeMiddle S
        (cascadeLeftHistory ([] : List (X ∪ₜ Y)) ++ us) hS0
          ∈ System.dom T := by
      rw [System.cascadeMiddle_congr S
        (by simp [cascadeLeftHistory]) hS0 hS]
      exact hT
    obtain ⟨vs, xs', ys', hmem, hlast⟩ :=
      driveOuter_cascadeFn_of_dom S T us [] [] [] rfl (Or.inr rfl)
        (Or.inr rfl) (fun h => absurd h (System.empty_not_mem S))
        (fun _ => rfl) (Or.inl ⟨hS0, hT0⟩)
    refine ⟨3, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, xs', ys'), hmem, ?_⟩
    rw [hlast hS0 hT0 hne]
    refine congrArg some ?_
    refine System.output_congr T ?_ hT0 hT
    exact System.cascadeMiddle_congr S (by simp [cascadeLeftHistory]) hS0 hS

/-- **The honest cascade equation (CR18 Definition 3.11 via Definition 3.9).**
The cascade converter, as a Definition 3.8 object applied by Definition 3.9 to
the paired-access system, *is* the native DDS-level cascade — the genuine
converter equation behind the `rfl`-by-definition
`cascadeViaConverter_eq_cascade`. -/
theorem apply_toDDC_cascadeFn (S : System.DDS X Y) (T : System.DDS Y Z) :
    DDC.apply (toDDC (cascadeFn (X := X) (Y := Y) (Z := Z)))
        (cascadeAccess S T) = System.cascade S T := by
  rw [apply_toDDC, apply_cascadeFn]

end Converter

end RandomSystems

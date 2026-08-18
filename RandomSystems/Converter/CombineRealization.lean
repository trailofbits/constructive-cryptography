/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Cascade

/-!
# The honest output-combine equation (CR18 Definition 3.12 via Definition 3.9)

Companion to `CascadeRealization.lean`, and the same statement for the `comb⋆`
converter: the output-combine converter, presented as a protocol function,
applied by Definition 3.9 to the parallel composition of the two systems,
**equals** the native DDS-level combine `System.combine`:

* `apply_combineFn` — the transcript-equation form
  `apply (combineFn op) [Combine.pair S T]ₚ = S ⋆ₚ[op] T`;
* `apply_toDDC_combineFn` — Definition 3.9 applied to the canonical Definition
  3.8 object, by `apply_toDDC`.

Per round the converter queries both components with the outer input and
answers the combined outputs — a fixed inner arity of 2, so the round boundary
is read off the two history *lengths* (the `queryLimitFn` idiom) and the proof
is a `drive`/`driveOuter` computation against `[Combine.pair S T]ₚ`.

Per Definition 3.9 the inner queries are answered by the Definition 3.3
completion, so a refusal of either component arrives as `none` and stalls the
converter: `combineFn` has no move on an improper answer, which is exactly
where the native combine is undefined.
-/

namespace RandomSystems

namespace Converter

open scoped System

universe u v

variable {X : Type u} {Y : Type v}

namespace Combine

@[simp] theorem pair_zero (S T : System.DDS X Y) : pair S T 0 = S := rfl

@[simp] theorem pair_one (S T : System.DDS X Y) : pair S T 1 = T := rfl

end Combine

/-! ### Evaluating the parallel-access system -/

/-- Each component projection of an accepted (or empty) access history is
either empty or accepted by its component. -/
theorem parallel_pair_restrict_or (S T : System.DDS X Y)
    {h : List (Sigma (fun _ : Fin 2 => X))}
    (hp : h = [] ∨ h ∈ System.dom (System.parallel (Combine.pair S T))) :
    ∀ j : Fin 2, System.restrict j h = [] ∨
      System.restrict j h ∈ System.dom (Combine.pair S T j) := by
  rcases hp with rfl | hd
  · exact fun j => Or.inl (System.restrict_nil j)
  · exact hd.2

/-- A tagged query extends the accepted access history whenever its component
accepts it. -/
theorem parallel_pair_dom_snoc (S T : System.DDS X Y) (i : Fin 2)
    {h : List (Sigma (fun _ : Fin 2 => X))} {x : X}
    (hp : h = [] ∨ h ∈ System.dom (System.parallel (Combine.pair S T)))
    (hd : System.restrict i h ++ [x] ∈ System.dom (Combine.pair S T i)) :
    h ++ [⟨i, x⟩] ∈ System.dom (System.parallel (Combine.pair S T)) :=
  (System.append_singleton_mem_parallel_dom_iff (Combine.pair S T)
    (parallel_pair_restrict_or S T hp) i x).mpr hd

/-- The parallel-access system's value on a tagged query, as an equation. -/
theorem parallel_pair_eval (S T : System.DDS X Y) (i : Fin 2)
    {h : List (Sigma (fun _ : Fin 2 => X))} {x : X}
    (hdom : h ++ [⟨i, x⟩] ∈ System.dom (System.parallel (Combine.pair S T)))
    (hd : System.restrict i h ++ [x] ∈ System.dom (Combine.pair S T i)) :
    (System.parallel (Combine.pair S T)).1 (h ++ [⟨i, x⟩])
      = Part.some ⟨i, System.output (Combine.pair S T i)
          (System.restrict i h ++ [x]) hd⟩ := by
  have hlast : (h ++ [(⟨i, x⟩ : Sigma (fun _ : Fin 2 => X))]).getLast?
      = some ⟨i, x⟩ := by simp
  have hout := System.parallel_output (Combine.pair S T) _ hdom hlast
  rw [← Part.some_get hdom]
  refine congrArg Part.some ?_
  refine hout.trans (congrArg (Sigma.mk i) ?_)
  exact System.output_congr _ (System.restrict_concat_self i x h) _ hd

/-- Membership destructor for a tagged query. -/
theorem parallel_pair_mem_elim (S T : System.DDS X Y) (i : Fin 2)
    {h : List (Sigma (fun _ : Fin 2 => X))} {x : X}
    {a : Sigma (fun _ : Fin 2 => Y)}
    (ha : a ∈ (System.parallel (Combine.pair S T)).1 (h ++ [⟨i, x⟩])) :
    ∃ hd : System.restrict i h ++ [x] ∈ System.dom (Combine.pair S T i),
      a = ⟨i, System.output (Combine.pair S T i)
        (System.restrict i h ++ [x]) hd⟩ := by
  have hdom : h ++ [(⟨i, x⟩ : Sigma (fun _ : Fin 2 => X))]
      ∈ System.dom (System.parallel (Combine.pair S T)) :=
    Part.dom_iff_mem.mpr ⟨a, ha⟩
  have hd : System.restrict i h ++ [x]
      ∈ System.dom (Combine.pair S T i) := by
    rcases hdom.2 i with hempty | hdomi
    · exact absurd hempty (by rw [System.restrict_concat_self]; simp)
    · rwa [System.restrict_concat_self] at hdomi
  refine ⟨hd, ?_⟩
  rw [parallel_pair_eval S T i hdom hd, Part.mem_some_iff] at ha
  exact ha

/-! ### The two components' restrictions -/

theorem restrict_zero_pair_snoc (h : List (Sigma (fun _ : Fin 2 => X)))
    (u : X) :
    System.restrict (0 : Fin 2) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
      = System.restrict 0 h ++ [u] := by
  rw [System.restrict_concat_ne (by decide : (1 : Fin 2) ≠ 0),
    System.restrict_concat_self]

theorem restrict_one_pair_snoc (h : List (Sigma (fun _ : Fin 2 => X)))
    (u : X) :
    System.restrict (1 : Fin 2) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
      = System.restrict 1 h ++ [u] := by
  rw [System.restrict_concat_self,
    System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]

/-! ### The output-combine converter as a protocol function -/

/-- **The output-combine converter** (CR18 Definition 3.12's `comb⋆`) as a
protocol function: query both components with the outer input, then answer
`op` of the two replies.

The round boundary is read off the history lengths — two inner queries per
outer input — in the `queryLimitFn` idiom.  As everywhere under the
`Y ∪ {⊥}` alphabet, both continuation branches fire only on proper answers,
so a refusal of either component leaves the converter with no move. -/
def combineFn (op : Y → Y → Y) :
    ProtocolFn X Y (Sigma (fun _ : Fin 2 => X))
      (Sigma (fun _ : Fin 2 => Y)) := fun p =>
  if p.2.length + 2 = 2 * p.1.length then
    match p.1.getLast? with
    | some u => Part.some (Sum.inl ⟨(0 : Fin 2), u⟩)
    | none => Part.none
  else if p.2.length + 1 = 2 * p.1.length then
    match p.1.getLast?, p.2.getLast? with
    | some u, some (some _) => Part.some (Sum.inl ⟨(1 : Fin 2), u⟩)
    | _, _ => Part.none
  else if p.2.length = 2 * p.1.length ∧ 0 < p.2.length then
    match p.2.dropLast.getLast?, p.2.getLast? with
    | some (some a), some (some b) => Part.some (Sum.inr (op a.2 b.2))
    | _, _ => Part.none
  else Part.none

variable {op : Y → Y → Y}

/-- Move constructor, first component. -/
theorem combineFn_zero_mem {us : List X}
    {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))} {u : X}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u) :
    Sum.inl (⟨(0 : Fin 2), u⟩ : Sigma (fun _ : Fin 2 => X))
      ∈ combineFn (X := X) op (us, ys) := by
  simp only [combineFn, if_pos hlen, hu]
  exact Part.mem_some _

/-- Move constructor, second component: after a proper first reply the
converter queries the second component with the same outer input. -/
theorem combineFn_one_mem {us : List X}
    {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))} {u : X}
    {a : Sigma (fun _ : Fin 2 => Y)}
    (hlen : ys.length + 1 = 2 * us.length) (hu : us.getLast? = some u)
    (ha : ys.getLast? = some (some a)) :
    Sum.inl (⟨(1 : Fin 2), u⟩ : Sigma (fun _ : Fin 2 => X))
      ∈ combineFn (X := X) op (us, ys) := by
  have hne : ¬ (ys.length + 2 = 2 * us.length) := by omega
  simp only [combineFn, if_neg hne, if_pos hlen, hu, ha]
  exact Part.mem_some _

/-- Move constructor, outer answer: after both proper replies the converter
delivers their combination. -/
theorem combineFn_answer_mem {us : List X}
    {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))}
    {a b : Sigma (fun _ : Fin 2 => Y)}
    (hlen : ys.length = 2 * us.length) (h0 : 0 < ys.length)
    (ha : ys.dropLast.getLast? = some (some a))
    (hb : ys.getLast? = some (some b)) :
    Sum.inr (op a.2 b.2) ∈ combineFn (X := X) op (us, ys) := by
  have hneA : ¬ (ys.length + 2 = 2 * us.length) := by omega
  have hneB : ¬ (ys.length + 1 = 2 * us.length) := by omega
  simp only [combineFn, if_neg hneA, if_neg hneB,
    if_pos (And.intro hlen h0), ha, hb]
  exact Part.mem_some _

/-- Move inversion, query branch. -/
theorem combineFn_inl_inv {us : List X}
    {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))}
    {q : Sigma (fun _ : Fin 2 => X)}
    (h : Sum.inl q ∈ combineFn (X := X) op (us, ys)) :
    (ys.length + 2 = 2 * us.length ∧
        ∃ u, q = ⟨(0 : Fin 2), u⟩ ∧ us.getLast? = some u) ∨
      (ys.length + 1 = 2 * us.length ∧
        ∃ u a, q = ⟨(1 : Fin 2), u⟩ ∧ us.getLast? = some u ∧
          ys.getLast? = some (some a)) := by
  simp only [combineFn] at h
  split_ifs at h with h1 h2 h3
  · rcases hu : us.getLast? with _ | u
    · rw [hu] at h; simp at h
    · rw [hu] at h
      simp only [Part.mem_some_iff, Sum.inl.injEq] at h
      subst h
      exact Or.inl ⟨h1, u, rfl, rfl⟩
  · rcases hu : us.getLast? with _ | u <;> rcases hy : ys.getLast? with _ | oy
    · rw [hu, hy] at h; simp at h
    · rcases oy with _ | a <;> (rw [hu, hy] at h; simp at h)
    · rw [hu, hy] at h; simp at h
    · rcases oy with _ | a
      · rw [hu, hy] at h; simp at h
      · rw [hu, hy] at h
        simp only [Part.mem_some_iff, Sum.inl.injEq] at h
        subst h
        exact Or.inr ⟨h2, u, a, rfl, rfl, rfl⟩
  · rcases ha : ys.dropLast.getLast? with _ | oa <;>
      rcases hb : ys.getLast? with _ | ob
    · rw [ha, hb] at h; simp at h
    · rcases ob with _ | b <;> (rw [ha, hb] at h; simp at h)
    · rcases oa with _ | a <;> (rw [ha, hb] at h; simp at h)
    · rcases oa with _ | a <;> rcases ob with _ | b <;>
        (rw [ha, hb] at h; simp at h)
  · simp at h

/-- Move inversion, outer-answer branch. -/
theorem combineFn_inr_inv {us : List X}
    {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))} {v : Y}
    (h : Sum.inr v ∈ combineFn (X := X) op (us, ys)) :
    ys.length = 2 * us.length ∧ 0 < ys.length ∧
      ∃ a b, ys.dropLast.getLast? = some (some a) ∧
        ys.getLast? = some (some b) ∧ v = op a.2 b.2 := by
  simp only [combineFn] at h
  split_ifs at h with h1 h2 h3
  · rcases hu : us.getLast? with _ | u
    · rw [hu] at h; simp at h
    · rw [hu] at h; simp at h
  · rcases hu : us.getLast? with _ | u <;> rcases hy : ys.getLast? with _ | oy
    · rw [hu, hy] at h; simp at h
    · rcases oy with _ | a <;> (rw [hu, hy] at h; simp at h)
    · rw [hu, hy] at h; simp at h
    · rcases oy with _ | a <;> (rw [hu, hy] at h; simp at h)
  · rcases ha : ys.dropLast.getLast? with _ | oa <;>
      rcases hb : ys.getLast? with _ | ob
    · rw [ha, hb] at h; simp at h
    · rcases ob with _ | b <;> (rw [ha, hb] at h; simp at h)
    · rcases oa with _ | a <;> (rw [ha, hb] at h; simp at h)
    · rcases oa with _ | a <;> rcases ob with _ | b
      · rw [ha, hb] at h; simp at h
      · rw [ha, hb] at h; simp at h
      · rw [ha, hb] at h; simp at h
      · rw [ha, hb] at h
        simp only [Part.mem_some_iff, Sum.inr.injEq] at h
        subst h
        exact ⟨h3.1, h3.2, a, b, rfl, rfl, rfl⟩
  · simp at h

/-! ### One combine round -/

/-- One combine round, computed: query both components with the outer input
and deliver their combination. -/
theorem drive_combineFn_round_mem (S T : System.DDS X Y)
    {us : List X} {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))}
    {h : List (Sigma (fun _ : Fin 2 => X))} {u : X} {y₁ y₂ : Y}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u)
    (hh : h ∈ System.dom (System.parallel (Combine.pair S T)) ∨ h = [])
    (hdS : System.restrict 0 h ++ [u] ∈ System.dom S)
    (hy₁ : System.output S (System.restrict 0 h ++ [u]) hdS = y₁)
    (hdT : System.restrict 1 h ++ [u] ∈ System.dom T)
    (hy₂ : System.output T (System.restrict 1 h ++ [u]) hdT = y₂) :
    (op y₁ y₂, h ++ [⟨0, u⟩] ++ [⟨1, u⟩],
        ys ++ [some ⟨0, y₁⟩] ++ [some ⟨1, y₂⟩])
      ∈ drive (combineFn op) (System.parallel (Combine.pair S T)) 3 us h ys := by
  have hdom₁ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]
      ∈ System.dom (System.parallel (Combine.pair S T)) :=
    parallel_pair_dom_snoc S T 0 hh.symm hdS
  have hout₁ : System.output (System.parallel (Combine.pair S T))
      (h ++ [⟨0, u⟩]) hdom₁ = ⟨(0 : Fin 2), y₁⟩ := by
    refine (System.parallel_output (Combine.pair S T) _ hdom₁
      (j := 0) (x := u) (by simp)).trans ?_
    refine congrArg (Sigma.mk (0 : Fin 2)) ?_
    show System.output S _ _ = y₁
    exact (System.output_congr S (System.restrict_concat_self 0 u h) _ hdS).trans hy₁
  have hans₁ : System.output ((System.parallel (Combine.pair S T))⊥)
      (h ++ [⟨0, u⟩]) (by rw [System.dom_fullyDefined]; simp)
      = some ⟨(0 : Fin 2), y₁⟩ := by
    rw [System.output_fullyDefined_append_of_mem
      (System.parallel (Combine.pair S T)) h ⟨0, u⟩ hh hdom₁, hout₁]
  refine drive_mem_query (combineFn op) (System.parallel (Combine.pair S T))
    (combineFn_zero_mem hlen hu) ?_
  rw [hans₁]
  have hlen₂ : (ys ++ [some (⟨0, y₁⟩ : Sigma (fun _ : Fin 2 => Y))]).length + 1
      = 2 * us.length := by
    simp only [List.length_append, List.length_singleton]; omega
  have hdT₁ : System.restrict 1 (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))])
      ++ [u] ∈ System.dom T := by
    rw [System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
    exact hdT
  have hdom₂ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))] ++ [⟨1, u⟩]
      ∈ System.dom (System.parallel (Combine.pair S T)) :=
    parallel_pair_dom_snoc S T 1 (Or.inr hdom₁) hdT₁
  have hout₂ : System.output (System.parallel (Combine.pair S T))
      (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) hdom₂ = ⟨(1 : Fin 2), y₂⟩ := by
    refine (System.parallel_output (Combine.pair S T) _ hdom₂
      (j := 1) (x := u) (by simp)).trans ?_
    refine congrArg (Sigma.mk (1 : Fin 2)) ?_
    show System.output T _ _ = y₂
    refine (System.output_congr T ?_ _ hdT).trans hy₂
    rw [restrict_one_pair_snoc]
  have hans₂ : System.output ((System.parallel (Combine.pair S T))⊥)
      (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) (by rw [System.dom_fullyDefined]; simp)
      = some ⟨(1 : Fin 2), y₂⟩ := by
    rw [System.output_fullyDefined_append_of_mem
      (System.parallel (Combine.pair S T))
      (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))])
      (⟨1, u⟩ : Sigma (fun _ : Fin 2 => X)) (Or.inl hdom₁) hdom₂, hout₂]
  refine drive_mem_query (combineFn op) (System.parallel (Combine.pair S T))
    (combineFn_one_mem (a := ⟨0, y₁⟩) hlen₂ hu (by simp)) ?_
  rw [hans₂]
  exact drive_mem_answer (combineFn op) (System.parallel (Combine.pair S T))
    (combineFn_answer_mem (a := ⟨0, y₁⟩) (b := ⟨1, y₂⟩)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp) (by simp) (by simp)) 0

/-- One combine round, destructed. -/
theorem drive_combineFn_round_elim (S T : System.DDS X Y)
    {us : List X} {ys : List (Option (Sigma (fun _ : Fin 2 => Y)))}
    {h : List (Sigma (fun _ : Fin 2 => X))} {u : X} {fuel : ℕ}
    {p : Y × List (Sigma (fun _ : Fin 2 => X)) ×
      List (Option (Sigma (fun _ : Fin 2 => Y)))}
    (hlen : ys.length + 2 = 2 * us.length) (hu : us.getLast? = some u)
    (hh : h ∈ System.dom (System.parallel (Combine.pair S T)) ∨ h = [])
    (hp : p ∈ drive (combineFn op) (System.parallel (Combine.pair S T))
      fuel us h ys) :
    ∃ (hdS : System.restrict 0 h ++ [u] ∈ System.dom S)
      (hdT : System.restrict 1 h ++ [u] ∈ System.dom T),
      p = (op (System.output S (System.restrict 0 h ++ [u]) hdS)
              (System.output T (System.restrict 1 h ++ [u]) hdT),
        h ++ [⟨0, u⟩] ++ [⟨1, u⟩],
        ys ++ [some ⟨0, System.output S (System.restrict 0 h ++ [u]) hdS⟩]
          ++ [some ⟨1, System.output T (System.restrict 1 h ++ [u]) hdT⟩]) := by
  rcases fuel with _ | fuel
  · simp [drive] at hp
  rcases drive_succ_elim hp with ⟨x, hm, hp'⟩ | ⟨v, hm, rfl⟩
  swap
  · exact absurd (combineFn_inr_inv hm).1 (by omega)
  rcases combineFn_inl_inv hm with ⟨-, u', rfl, hu'⟩ | ⟨hbad, -⟩
  swap
  · exact absurd hbad (by omega)
  obtain rfl : u = u' := Option.some.inj (hu.symm.trans hu')
  rcases fuel with _ | fuel
  · simp [drive] at hp'
  rcases drive_succ_elim hp' with ⟨x₂, hm₂, hp''⟩ | ⟨v₂, hm₂, rfl⟩
  swap
  · exact absurd (combineFn_inr_inv hm₂).1
      (by simp only [List.length_append, List.length_singleton]; omega)
  rcases combineFn_inl_inv hm₂ with ⟨hbad, -⟩ | ⟨-, u₂, a₁, rfl, hu₂, ha₁⟩
  · exact absurd hbad
      (by simp only [List.length_append, List.length_singleton]; omega)
  obtain rfl : u = u₂ := Option.some.inj (hu.symm.trans hu₂)
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.some.injEq] at ha₁
  obtain ⟨hdom₁, hout₁⟩ :=
    System.mem_of_output_fullyDefined_append_eq_some
      (System.parallel (Combine.pair S T)) h
      (⟨0, u⟩ : Sigma (fun _ : Fin 2 => X)) hh ha₁
  have hmem₁ : a₁ ∈ (System.parallel (Combine.pair S T)).1
      (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]) := by
    rw [← hout₁]; exact Part.get_mem hdom₁
  obtain ⟨hdS', hEq₁⟩ := parallel_pair_mem_elim S T 0 hmem₁
  have hdS : System.restrict 0 h ++ [u] ∈ System.dom S := hdS'
  have hA₁ : a₁
      = ⟨(0 : Fin 2), System.output S (System.restrict 0 h ++ [u]) hdS⟩ := hEq₁
  rw [ha₁] at hp''
  rcases fuel with _ | fuel
  · simp [drive] at hp''
  rcases drive_succ_elim hp'' with ⟨x₃, hm₃, -⟩ | ⟨v₃, hm₃, rfl⟩
  · rcases combineFn_inl_inv hm₃ with ⟨hbad, -⟩ | ⟨hbad, -⟩ <;>
      exact absurd hbad
        (by simp only [List.length_append, List.length_singleton]; omega)
  obtain ⟨-, -, a, b, hA, hB, hv⟩ := combineFn_inr_inv hm₃
  simp only [List.dropLast_concat, List.getLast?_append, List.getLast?_singleton,
    Option.some_or, Option.some.injEq] at hA hB
  obtain ⟨hdom₂, hout₂⟩ :=
    System.mem_of_output_fullyDefined_append_eq_some
      (System.parallel (Combine.pair S T))
      (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))])
      (⟨1, u⟩ : Sigma (fun _ : Fin 2 => X)) (Or.inl hdom₁) hB
  have hmem₂ : b ∈ (System.parallel (Combine.pair S T)).1
      (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))] ++ [⟨1, u⟩]) := by
    rw [← hout₂]; exact Part.get_mem hdom₂
  obtain ⟨hdT₁, hEq₂⟩ := parallel_pair_mem_elim S T 1 hmem₂
  have hdT : System.restrict 1 h ++ [u] ∈ System.dom T := by
    rw [← System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1) u h]
    exact hdT₁
  have hB₂ : b
      = ⟨(1 : Fin 2), System.output T (System.restrict 1 h ++ [u]) hdT⟩ := by
    rw [hEq₂]
    refine congrArg (Sigma.mk (1 : Fin 2)) ?_
    show System.output T _ _ = _
    refine System.output_congr T ?_ hdT₁ hdT
    rw [System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
  have hv₃ : v₃ = op (System.output S (System.restrict 0 h ++ [u]) hdS)
      (System.output T (System.restrict 1 h ++ [u]) hdT) := by
    rw [hv, ← hA, hA₁, hB₂]
  refine ⟨hdS, hdT, ?_⟩
  rw [hv₃, hB, hB₂, hA₁]

/-! ### The outer fold -/

/-- Forward run of the output-combine converter over a whole outer history.
The threaded invariant is the reference's — both components have received the
same inputs — plus the ν-level round-boundary invariant
`ys.length = 2 * usPre.length`. -/
theorem driveOuter_combineFn_of_dom (S T : System.DDS X Y) :
    ∀ (rest usPre : List X) (h : List (Sigma (fun _ : Fin 2 => X)))
      (ys : List (Option (Sigma (fun _ : Fin 2 => Y)))),
      ys.length = 2 * usPre.length →
      (h ∈ System.dom (System.parallel (Combine.pair S T)) ∨ h = []) →
      System.restrict 1 h = System.restrict 0 h →
      ((System.restrict 0 h ++ rest ∈ System.dom S ∧
        System.restrict 0 h ++ rest ∈ System.dom T) ∨ rest = []) →
      ∃ vs h' ys',
        (vs, h', ys') ∈ driveOuter (combineFn op)
          (System.parallel (Combine.pair S T)) 3 usPre h ys rest ∧
        ∀ (hS : System.restrict 0 h ++ rest ∈ System.dom S)
          (hT : System.restrict 0 h ++ rest ∈ System.dom T),
          rest ≠ [] →
            vs.getLast? = some (op
              (System.output S (System.restrict 0 h ++ rest) hS)
              (System.output T (System.restrict 0 h ++ rest) hT)) := by
  intro rest
  induction rest with
  | nil =>
      intro usPre h ys _ _ _ _
      exact ⟨[], h, ys, by simp [driveOuter],
        fun _ _ hne => absurd rfl hne⟩
  | cons u rest ih =>
      intro usPre h ys hlen hh hsym hfull
      obtain ⟨hSfull, hTfull⟩ :
          System.restrict 0 h ++ u :: rest ∈ System.dom S ∧
            System.restrict 0 h ++ u :: rest ∈ System.dom T := by
        rcases hfull with hf | hf
        · exact hf
        · exact absurd hf (by simp)
      have hdS₁ : System.restrict 0 h ++ [u] ∈ System.dom S :=
        System.prefix_closed S ⟨rest, by simp⟩ (by simp) hSfull
      have hdT₁ : System.restrict 1 h ++ [u] ∈ System.dom T := by
        rw [hsym]
        exact System.prefix_closed T ⟨rest, by simp⟩ (by simp) hTfull
      set y₁ := System.output S (System.restrict 0 h ++ [u]) hdS₁ with hy₁def
      set y₂ := System.output T (System.restrict 1 h ++ [u]) hdT₁ with hy₂def
      have hround := drive_combineFn_round_mem (op := op) S T
        (us := usPre ++ [u]) (ys := ys) (h := h) (u := u)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp) hh hdS₁ rfl hdT₁ rfl
      have hdom₁ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]
          ∈ System.dom (System.parallel (Combine.pair S T)) :=
        parallel_pair_dom_snoc S T 0 hh.symm hdS₁
      have hdT₁' : System.restrict 1
          (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]) ++ [u]
            ∈ System.dom T := by
        rw [System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
        exact hdT₁
      have hdom₂ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))] ++ [⟨1, u⟩]
          ∈ System.dom (System.parallel (Combine.pair S T)) :=
        parallel_pair_dom_snoc S T 1 (Or.inr hdom₁) hdT₁'
      have hR0 := restrict_zero_pair_snoc h u
      have hR1 := restrict_one_pair_snoc h u
      have hsym' : System.restrict 1 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
          = System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) := by
        rw [hR0, hR1, hsym]
      have hlist : System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
          = System.restrict 0 h ++ u :: rest := by
        rw [hR0, List.append_assoc]
        rfl
      have hfull' : (System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
            ∈ System.dom S ∧
          System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
            ∈ System.dom T) ∨ rest = [] :=
        Or.inl ⟨by rw [hlist]; exact hSfull, by rw [hlist]; exact hTfull⟩
      obtain ⟨vs', h'', ys'', hmem', hlast'⟩ :=
        ih (usPre ++ [u]) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
          (ys ++ [some ⟨0, y₁⟩] ++ [some ⟨1, y₂⟩])
          (by simp only [List.length_append, List.length_singleton]; omega)
          (Or.inl hdom₂) hsym' hfull'
      refine ⟨op y₁ y₂ :: vs', h'', ys'', ?_, ?_⟩
      · simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff]
        exact ⟨(op y₁ y₂, h ++ [⟨0, u⟩] ++ [⟨1, u⟩],
          ys ++ [some ⟨0, y₁⟩] ++ [some ⟨1, y₂⟩]), hround,
          (vs', h'', ys''), hmem', rfl⟩
      · intro hS hT hne
        cases hvs : vs' with
        | nil =>
            have hrest : rest = [] := by
              have hlen' := driveOuter_length (combineFn op)
                (System.parallel (Combine.pair S T)) 3 hmem'
              rw [hvs] at hlen'
              exact List.eq_nil_of_length_eq_zero (by simpa using hlen'.symm)
            subst hrest
            rw [List.getLast?_singleton]
            refine congrArg some (congrArg₂ op ?_ ?_)
            · exact System.output_congr S rfl hdS₁ hS
            · exact System.output_congr T (by rw [hsym]) hdT₁ hT
        | cons v0 vs0 =>
            have hrest : rest ≠ [] := by
              have hlen' := driveOuter_length (combineFn op)
                (System.parallel (Combine.pair S T)) 3 hmem'
              rw [hvs] at hlen'
              intro hnil
              rw [hnil] at hlen'
              simp at hlen'
            have hS' : System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
                ∈ System.dom S := by rw [hlist]; exact hS
            have hT' : System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
                ∈ System.dom T := by rw [hlist]; exact hT
            have hlast'' := hlast' hS' hT' hrest
            rw [hvs] at hlast''
            rw [List.getLast?_cons_cons, hlast'']
            refine congrArg some (congrArg₂ op ?_ ?_)
            · exact System.output_congr S hlist hS' hS
            · exact System.output_congr T hlist hT' hT

/-- Backward run analysis of the output-combine converter. -/
theorem driveOuter_combineFn_mem_imp (S T : System.DDS X Y) :
    ∀ (rest usPre : List X) (h : List (Sigma (fun _ : Fin 2 => X)))
      (ys : List (Option (Sigma (fun _ : Fin 2 => Y)))) {fuel : ℕ}
      {r : List Y × List (Sigma (fun _ : Fin 2 => X)) ×
        List (Option (Sigma (fun _ : Fin 2 => Y)))},
      ys.length = 2 * usPre.length →
      (h ∈ System.dom (System.parallel (Combine.pair S T)) ∨ h = []) →
      System.restrict 1 h = System.restrict 0 h →
      r ∈ driveOuter (combineFn op) (System.parallel (Combine.pair S T))
        fuel usPre h ys rest →
      rest ≠ [] →
      ∃ (hS : System.restrict 0 h ++ rest ∈ System.dom S)
        (hT : System.restrict 0 h ++ rest ∈ System.dom T),
        r.1.getLast? = some (op
          (System.output S (System.restrict 0 h ++ rest) hS)
          (System.output T (System.restrict 0 h ++ rest) hT)) := by
  intro rest
  induction rest with
  | nil =>
      intro usPre h ys fuel r _ _ _ _ hne
      exact absurd rfl hne
  | cons u rest ih =>
      intro usPre h ys fuel r hlen hh hsym hr _
      simp only [driveOuter, Part.mem_bind_iff, Part.mem_map_iff] at hr
      obtain ⟨r₁, hr₁, rr, hrr, rfl⟩ := hr
      obtain ⟨hdS₁, hdT₁, rfl⟩ := drive_combineFn_round_elim (op := op) S T
        (us := usPre ++ [u]) (u := u)
        (by simp only [List.length_append, List.length_singleton]; omega)
        (by simp) hh hr₁
      set y₁ := System.output S (System.restrict 0 h ++ [u]) hdS₁ with hy₁def
      set y₂ := System.output T (System.restrict 1 h ++ [u]) hdT₁ with hy₂def
      have hdom₁ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]
          ∈ System.dom (System.parallel (Combine.pair S T)) :=
        parallel_pair_dom_snoc S T 0 hh.symm hdS₁
      have hdT₁' : System.restrict 1
          (h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))]) ++ [u]
            ∈ System.dom T := by
        rw [System.restrict_concat_ne (by decide : (0 : Fin 2) ≠ 1)]
        exact hdT₁
      have hdom₂ : h ++ [(⟨0, u⟩ : Sigma (fun _ : Fin 2 => X))] ++ [⟨1, u⟩]
          ∈ System.dom (System.parallel (Combine.pair S T)) :=
        parallel_pair_dom_snoc S T 1 (Or.inr hdom₁) hdT₁'
      have hR0 := restrict_zero_pair_snoc h u
      have hR1 := restrict_one_pair_snoc h u
      have hlist : System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) ++ rest
          = System.restrict 0 h ++ u :: rest := by
        rw [hR0, List.append_assoc]
        rfl
      cases hrest : rest with
      | nil =>
          subst hrest
          simp only [driveOuter, Part.mem_some_iff] at hrr
          subst hrr
          refine ⟨hdS₁, by rw [hsym] at hdT₁; exact hdT₁, ?_⟩
          rw [List.getLast?_singleton]
          refine congrArg some (congrArg₂ op ?_ ?_)
          · exact System.output_congr S rfl hdS₁ _
          · exact System.output_congr T (by rw [hsym]) hdT₁ _
      | cons r0 rs0 =>
          have hsym' : System.restrict 1 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
              = System.restrict 0 (h ++ [⟨0, u⟩] ++ [⟨1, u⟩]) := by
            rw [hR0, hR1, hsym]
          obtain ⟨hS', hT', hlast'⟩ :=
            ih (usPre ++ [u]) (h ++ [⟨0, u⟩] ++ [⟨1, u⟩])
              (ys ++ [some ⟨0, y₁⟩] ++ [some ⟨1, y₂⟩])
              (by simp only [List.length_append, List.length_singleton]; omega)
              (Or.inl hdom₂) hsym' hrr (by simp [hrest])
          rw [← hrest]
          have hS : System.restrict 0 h ++ u :: rest ∈ System.dom S := by
            rw [← hlist]; exact hS'
          have hT : System.restrict 0 h ++ u :: rest ∈ System.dom T := by
            rw [← hlist]; exact hT'
          refine ⟨hS, hT, ?_⟩
          have hlenrr := driveOuter_length (combineFn op)
            (System.parallel (Combine.pair S T)) fuel hrr
          cases hrr1 : rr.1 with
          | nil =>
              rw [hrr1] at hlenrr
              simp [hrest] at hlenrr
          | cons v0 vs0 =>
              rw [hrr1] at hlast'
              rw [List.getLast?_cons_cons, hlast']
              refine congrArg some (congrArg₂ op ?_ ?_)
              · exact System.output_congr S hlist hS' hS
              · exact System.output_congr T hlist hT' hT

/-! ### The honest output-combine equation -/

/-- Membership characterization of the native combine. -/
theorem mem_combine_iff (S T : System.DDS X Y) (l : List X) (y : Y) :
    y ∈ (System.combine op S T).1 l ↔
      ∃ (hS : l ∈ System.dom S) (hT : l ∈ System.dom T),
        y = op (System.output S l hS) (System.output T l hT) := by
  constructor
  · rintro ⟨⟨hS, hT⟩, rfl⟩
    exact ⟨hS, hT, rfl⟩
  · rintro ⟨hS, hT, rfl⟩
    exact ⟨⟨hS, hT⟩, rfl⟩

/-- **The output-combine converter, applied**: the transcript-equation
application of `combineFn op` to the parallel composition of the two systems
is the native DDS-level combine. -/
theorem apply_combineFn (S T : System.DDS X Y) :
    apply (combineFn op) (System.parallel (Combine.pair S T))
      = System.combine op S T := by
  apply Subtype.ext
  funext us
  apply Part.ext
  intro y
  rw [show (apply (combineFn op) (System.parallel (Combine.pair S T))).1
      = applyRaw (combineFn op) (System.parallel (Combine.pair S T)) from rfl,
    mem_applyRaw, mem_combine_iff]
  constructor
  · rintro ⟨fuel, hv⟩
    rw [mem_applyRawAt_iff] at hv
    obtain ⟨r, hr, hlast⟩ := hv
    have hne : us ≠ [] := by
      rintro rfl
      have hlen := driveOuter_length (combineFn op)
        (System.parallel (Combine.pair S T)) fuel hr
      rw [List.length_nil] at hlen
      rw [List.eq_nil_of_length_eq_zero hlen] at hlast
      simp at hlast
    obtain ⟨hS, hT, hout⟩ := driveOuter_combineFn_mem_imp (op := op) S T
      us [] [] [] rfl (Or.inr rfl) rfl hr hne
    rw [hlast] at hout
    have hy := Option.some.inj hout
    refine ⟨by simpa [System.restrict_nil] using hS,
      by simpa [System.restrict_nil] using hT, ?_⟩
    rw [hy]
    exact congrArg₂ op
      (System.output_congr S (by simp [System.restrict_nil]) hS _)
      (System.output_congr T (by simp [System.restrict_nil]) hT _)
  · rintro ⟨hS, hT, rfl⟩
    have hne : us ≠ [] := by
      rintro rfl
      exact System.empty_not_mem S hS
    have hS0 : System.restrict (0 : Fin 2)
        ([] : List (Sigma (fun _ : Fin 2 => X))) ++ us ∈ System.dom S := by
      simpa [System.restrict_nil] using hS
    have hT0 : System.restrict (0 : Fin 2)
        ([] : List (Sigma (fun _ : Fin 2 => X))) ++ us ∈ System.dom T := by
      simpa [System.restrict_nil] using hT
    obtain ⟨vs, h', ys', hmem, hlast⟩ :=
      driveOuter_combineFn_of_dom (op := op) S T us [] [] [] rfl
        (Or.inr rfl) rfl (Or.inl ⟨hS0, hT0⟩)
    refine ⟨3, ?_⟩
    rw [mem_applyRawAt_iff]
    refine ⟨(vs, h', ys'), hmem, ?_⟩
    rw [hlast hS0 hT0 hne]
    exact congrArg some (congrArg₂ op
      (System.output_congr S (by simp [System.restrict_nil]) hS0 hS)
      (System.output_congr T (by simp [System.restrict_nil]) hT0 hT))

/-- **The honest output-combine equation (CR18 Definition 3.12 via Definition
3.9).**  The output-combine converter, as a Definition 3.8 object applied by
Definition 3.9 to the parallel composition of the two systems, *is* the native
DDS-level combine — the genuine converter equation behind the
`rfl`-by-definition `combineViaConverter_eq_combine`. -/
theorem apply_toDDC_combineFn (S T : System.DDS X Y) :
    DDC.apply (toDDC (combineFn (X := X) op))
        (System.parallel (Combine.pair S T)) = System.combine op S T := by
  rw [apply_toDDC, apply_combineFn]

end Converter

end RandomSystems

module

public import Mathlib.Data.List.Basic

/-!
# List splits and fold-indexed predicates

Helpers for reasoning about an entry of a list together with the prefix before it:

* `List.exists_eq_append_cons_iff` and `List.forall_prefix_concat_iff_forall_take`:
  translate existential and universal properties of splits `l = p ++ e :: s` into
  finitely bounded quantifiers over positions `i < l.length`
* `List.exists_split_of_filterMap_eq` and `List.exists_split_of_filter_eq`:
  lift a split of `l.filterMap f` or `l.filter p` back to a split of `l`
* `List.ForallScan`, `List.ForallScan.append`, `List.ForallScan.of_append_cons`:
  assert a predicate `P c a` at every entry `a` against the running `foldl f b` state `c`
-/

@[expose] public section

namespace List

/-- Splitting `l` as `p ++ e :: s` with `P p e` is equivalent to finding a position
`i < l.length` where `P (l.take i) l[i]` holds. -/
lemma exists_eq_append_cons_iff
    -- `l` is the list being split; `P p e` relates entry `e` to the prefix `p` before it.
    {α : Type*} (l : List α) (P : List α → α → Prop) :
    (∃ p e s, l = p ++ e :: s ∧ P p e) ↔
      ∃ (i : ℕ) (hi : i < l.length), P (l.take i) l[i] := by
  constructor
  · rintro ⟨p, e, s, rfl, hp⟩
    refine ⟨p.length, ?_, ?_⟩
    · simp only [length_append, length_cons]
      omega
    · simp only [take_left', getElem_append_right, Nat.le_refl, Nat.sub_self, getElem_cons_zero]
      exact hp
  · rintro ⟨i, hi, hp⟩
    refine ⟨l.take i, l[i], l.drop (i + 1), ?_, hp⟩
    rw [getElem_cons_drop, take_append_drop]

/-- Checking `Q p e` on every prefix `p ++ [e] <+: l` is equivalent to checking
`Q (l.take i) l[i]` at every position `i < l.length`. -/
lemma forall_prefix_concat_iff_forall_take
    -- `l` is the list; `Q p e` relates entry `e` to the prefix `p` before it.
    {α : Type*} (l : List α) (Q : List α → α → Prop) :
    (∀ p e, p ++ [e] <+: l → Q p e) ↔
      ∀ (i : ℕ) (hi : i < l.length), Q (l.take i) l[i] := by
  constructor
  · intro h i hi
    refine h (l.take i) l[i] ⟨l.drop (i + 1), ?_⟩
    rw [append_assoc, singleton_append, getElem_cons_drop, take_append_drop]
  · rintro h p e ⟨s, rfl⟩
    have hi : p.length < ((p ++ [e]) ++ s).length := by
      simp only [length_append, length_cons, length_nil]
      omega
    have hq := h p.length hi
    simpa only [append_assoc, singleton_append, take_left', getElem_append_right, Nat.le_refl,
      Nat.sub_self, getElem_cons_zero] using hq

/-- A split `l.filterMap f = pre ++ d :: post` lifts to a split `l = l₁ ++ a :: l₂` with
`l₁.filterMap f = pre`, `f a = some d`, and `l₂.filterMap f = post`. -/
lemma exists_split_of_filterMap_eq
    -- `f` maps kept entries to `some`; `l` splits around the preimage of `d`.
    {α β : Type*} (f : α → Option β) (l : List α) (pre : List β) (d : β) (post : List β)
    (h : l.filterMap f = pre ++ d :: post) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.filterMap f = pre ∧ f a = some d ∧
      l₂.filterMap f = post := by
  obtain ⟨l₁, lrest, rfl, hpre, hrest⟩ := filterMap_eq_append_iff.mp h
  obtain ⟨lmid, a, l₂, rfl, hnone, hfa, hpost⟩ := filterMap_eq_cons_iff.mp hrest
  refine ⟨l₁ ++ lmid, a, l₂, (append_assoc l₁ lmid (a :: l₂)).symm, ?_, hfa, hpost⟩
  rw [filterMap_append, hpre, filterMap_eq_nil_iff.mpr hnone, append_nil]

/-- A split `l.filter p = pre ++ a :: post` lifts to a split `l = l₁ ++ a :: l₂` with
`l₁.filter p = pre`, `p a = true`, and `l₂.filter p = post`. -/
lemma exists_split_of_filter_eq
    -- `p` selects kept entries; `l` splits around the occurrence of `a`.
    {α : Type*} (p : α → Bool) (l : List α) (pre : List α) (a : α) (post : List α)
    (h : l.filter p = pre ++ a :: post) :
    ∃ l₁ l₂, l = l₁ ++ a :: l₂ ∧ l₁.filter p = pre ∧ p a = true ∧ l₂.filter p = post := by
  let f : α → Option α := fun x => if p x then some x else none
  have hfm : ∀ m : List α, m.filterMap f = m.filter p :=
    fun m => congrFun (filterMap_eq_filter (p := p)) m
  rw [← hfm l] at h
  obtain ⟨l₁, a', l₂, rfl, hpre, hfa, hpost⟩ := exists_split_of_filterMap_eq f l pre a post h
  have hpa : p a' = true ∧ a' = a := by
    cases hp : p a'
    · simp only [f, hp, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hfa
    · simp only [f, hp, ↓reduceIte, Option.some.injEq] at hfa
      exact ⟨rfl, hfa⟩
  rcases hpa with ⟨hpa, rfl⟩
  exact ⟨l₁, l₂, rfl, (hfm l₁).symm.trans hpre, hpa, (hfm l₂).symm.trans hpost⟩

/-- `ForallScan f P b l` holds when every entry `a` of `l` satisfies `P c a`, where `c` is the
state reached by folding `f` from `b` over the entries before `a`. -/
def ForallScan
    -- `f` advances the running state; `P c a` checks entry `a` against the state `c` before it.
    {α β : Type*} (f : β → α → β) (P : β → α → Prop) : β → List α → Prop
  | _, [] => True
  | b, a :: t => P b a ∧ ForallScan f P (f b a) t

instance instDecidableForallScan {α β : Type*} (f : β → α → β) (P : β → α → Prop)
    [∀ c a, Decidable (P c a)] (b : β) : (l : List α) → Decidable (ForallScan f P b l)
  | [] => isTrue trivial
  | a :: t =>
    letI := instDecidableForallScan f P (f b a) t
    instDecidableAnd

/-- `ForallScan` holds on `l ++ m` from `b` when it holds on `l` from `b` and on `m` from
`l.foldl f b`. -/
lemma ForallScan.append {α β : Type*} {f : β → α → β} {P : β → α → Prop}
    {b : β} {l m : List α}
    (hl : ForallScan f P b l) (hm : ForallScan f P (l.foldl f b) m) :
    ForallScan f P b (l ++ m) := by
  induction l generalizing b with
  | nil => exact hm
  | cons a t ih => exact ⟨hl.1, ih hl.2 hm⟩

/-- Splitting a scanned list as `l ++ a :: m` gives `P (l.foldl f b) a`. -/
lemma ForallScan.of_append_cons {α β : Type*} {f : β → α → β} {P : β → α → Prop}
    {b : β} {l m : List α} {a : α}
    (h : ForallScan f P b (l ++ a :: m)) :
    P (l.foldl f b) a := by
  induction l generalizing b with
  | nil => exact h.1
  | cons x t ih => exact ih h.2

/-- `ForallScan` decomposes across list concatenation. -/
lemma forallScan_append_iff {α β : Type*} {f : β → α → β} {P : β → α → Prop}
    {b : β} {l m : List α} :
    ForallScan f P b (l ++ m) ↔ ForallScan f P b l ∧ ForallScan f P (l.foldl f b) m := by
  induction l generalizing b with
  | nil => simp only [nil_append, ForallScan, foldl_nil, true_and]
  | cons a t ih =>
    simp only [cons_append, ForallScan, foldl_cons, ih, and_assoc]

/-- `ForallScan f P b l` is equivalent to checking `P (p.foldl f b) a` on every prefix
`p ++ [a] <+: l`. -/
lemma forallScan_iff_forall_prefix {α β : Type*} {f : β → α → β} {P : β → α → Prop}
    {b : β} {l : List α} :
    ForallScan f P b l ↔ ∀ p a, p ++ [a] <+: l → P (p.foldl f b) a := by
  constructor
  · rintro h p a ⟨s, rfl⟩
    rw [append_assoc, singleton_append] at h
    exact h.of_append_cons
  · intro h
    induction l generalizing b with
    | nil => trivial
    | cons x t ih =>
      refine ⟨h [] x ⟨t, rfl⟩, ih fun p a ⟨s, hs⟩ => ?_⟩
      have hp : (x :: p) ++ [a] <+: x :: t := ⟨s, by rw [cons_append, cons_append, hs]⟩
      simpa only [foldl_cons] using h (x :: p) a hp

end List

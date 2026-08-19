/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Phi

/-!
# Parallel composition at a splitting (MR16 §2.1)

MauRen16 §2.1 composes objects in parallel: `[R, S]` is the object that
offers both `R` and `S` at once.  Inside a single universe there is no
tagging step to perform — a query already carries its own address — so the
composition is parameterized by a **splitting** `c : Set X` of the query
alphabet: the queries in `c` are owned by the left component, the rest by
the right one.  Each component sees only the sub-history of the queries it
owns (`historyAt`), which is the whole content of "the two objects run
independently, side by side".

Disjointness is *not* a typing fact here: `[R, R]` is handled upstream by
re-addressing, not by this module.  The composition is total on every pair
of systems and every splitting, and the laws (`par_comm`, `par_assoc`) hold
unconditionally.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v

/-! ## The sub-history at an interface set -/

/-- The sub-history a component owning the queries in `c` sees: the
subsequence of `l` consisting of the queries addressed to `c`. -/
def historyAt {X : Type u} (c : Set X) (l : List X) : List X :=
  l.filter fun q => decide (q ∈ c)

@[simp]
theorem historyAt_nil {X : Type u} (c : Set X) : historyAt c ([] : List X) = [] :=
  rfl

@[simp]
theorem mem_historyAt {X : Type u} (c : Set X) (l : List X) (q : X) :
    q ∈ historyAt c l ↔ q ∈ l ∧ q ∈ c := by
  simp [historyAt]

/-- The sub-history is read off the history entrywise, so it distributes
over concatenation. -/
theorem historyAt_append {X : Type u} (c : Set X) (l₁ l₂ : List X) :
    historyAt c (l₁ ++ l₂) = historyAt c l₁ ++ historyAt c l₂ := by
  simp [historyAt, List.filter_append]

/-- A query owned by `c` extends `c`'s sub-history. -/
@[simp]
theorem historyAt_append_mem {X : Type u} (c : Set X) (l : List X) (q : X)
    (h : q ∈ c) : historyAt c (l ++ [q]) = historyAt c l ++ [q] := by
  rw [historyAt_append]
  simp [historyAt, h]

/-- A query owned by the other component leaves `c`'s sub-history alone. -/
@[simp]
theorem historyAt_append_not_mem {X : Type u} (c : Set X) (l : List X) (q : X)
    (h : q ∉ c) : historyAt c (l ++ [q]) = historyAt c l := by
  rw [historyAt_append]
  simp [historyAt, h]

/-- Sub-histories compose by intersecting the interface sets. -/
theorem historyAt_historyAt {X : Type u} (c c' : Set X) (l : List X) :
    historyAt c (historyAt c' l) = historyAt (c ∩ c') l := by
  induction l with
  | nil => rfl
  | cons q t ih =>
      by_cases hc' : q ∈ c' <;> by_cases hc : q ∈ c <;>
        simp [historyAt, hc, hc', Set.mem_inter_iff] at ih ⊢

/-- Taking a sub-history preserves prefix order. -/
theorem historyAt_prefix {X : Type u} (c : Set X) {l₁ l₂ : List X}
    (h : l₁ <+: l₂) : historyAt c l₁ <+: historyAt c l₂ := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨historyAt c t, (historyAt_append c l₁ t).symm⟩

/-! ## The composition -/

/-- The local rule of parallel composition at the splitting `c`: the query
just asked is answered by its owner, on the owner's own sub-history.  Not
prefix-closed on its own — `par` closes it. -/
def parRaw {X : Type u} {Y : Type v} (c : Set X) (R S : DDS X Y) : Raw X Y := fun l =>
  match l.getLast? with
  | none => Part.none
  | some q => if q ∈ c then R.1 (historyAt c l) else S.1 (historyAt cᶜ l)

/-- **MR16 §2.1 parallel composition at a splitting** `c`: the object that
offers `R` on the queries in `c` and `S` on the rest, each component seeing
only its own sub-history. -/
def par {X : Type u} {Y : Type v} (c : Set X) (R S : DDS X Y) : DDS X Y :=
  validate (parRaw c R S)

/-- A query owned by the left component is answered by it, on its own
extended sub-history. -/
theorem parRaw_concat_mem {X : Type u} {Y : Type v} (c : Set X) (R S : DDS X Y)
    (l : List X) (q : X) (h : q ∈ c) :
    parRaw c R S (l ++ [q]) = R.1 (historyAt c l ++ [q]) := by
  simp [parRaw, h]

/-- A query owned by the right component is answered by it, on its own
extended sub-history. -/
theorem parRaw_concat_not_mem {X : Type u} {Y : Type v} (c : Set X) (R S : DDS X Y)
    (l : List X) (q : X) (h : q ∉ c) :
    parRaw c R S (l ++ [q]) = S.1 (historyAt cᶜ l ++ [q]) := by
  rw [← historyAt_append_mem cᶜ l q (Set.mem_compl_iff c q |>.mpr h)]
  simp [parRaw, h]

/-! ## The laws -/

variable {X : Type u} {Y : Type v}

/-- The local rule is symmetric under swapping the components and
complementing the splitting: each query has the same owner on both sides. -/
theorem parRaw_comm (c : Set X) (R S : DDS X Y) : parRaw c R S = parRaw cᶜ S R := by
  funext l
  rcases List.eq_nil_or_concat l with rfl | ⟨L, e, rfl⟩
  · rfl
  · rw [List.concat_eq_append]
    by_cases h : e ∈ c
    · rw [parRaw_concat_mem c R S L e h,
        parRaw_concat_not_mem cᶜ S R L e (by simpa using h), compl_compl]
    · rw [parRaw_concat_not_mem c R S L e h, parRaw_concat_mem cᶜ S R L e h]

/-- **Commutativity**: the two components of a parallel composition are
interchangeable, once the splitting is complemented. -/
theorem par_comm (c : Set X) (R S : DDS X Y) : par c R S = par cᶜ S R :=
  congrArg validate (parRaw_comm c R S)

/-- A nonempty sub-history is already realized by a prefix of the history —
the shortest one ending at a query the component owns. -/
theorem exists_prefix_historyAt (c : Set X) :
    ∀ l : List X, historyAt c l ≠ [] →
      ∃ L e, L ++ [e] <+: l ∧ e ∈ c ∧ historyAt c L ++ [e] = historyAt c l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => exact fun h => absurd rfl h
  | append_singleton m a ih =>
      intro h
      by_cases ha : a ∈ c
      · exact ⟨m, a, List.prefix_rfl, ha, (historyAt_append_mem c m a ha).symm⟩
      · rw [historyAt_append_not_mem c m a ha] at h ⊢
        obtain ⟨L, e, hpre, he, heq⟩ := ih h
        exact ⟨L, e, hpre.trans (List.prefix_append m [a]), he, heq⟩

/-- **The domain of a parallel composition** is Maurer's parallel domain at
the splitting: a history is accepted exactly when it is nonempty and each
component's sub-history is either still empty or accepted by that
component. -/
theorem mem_dom_par (c : Set X) (R S : DDS X Y) (l : List X) :
    l ∈ dom (par c R S) ↔
      l ≠ [] ∧ (historyAt c l = [] ∨ historyAt c l ∈ dom R) ∧
        (historyAt cᶜ l = [] ∨ historyAt cᶜ l ∈ dom S) := by
  constructor
  · intro hl
    obtain ⟨hne, hall⟩ := (mem_dom_validate (parRaw c R S) l).mp hl
    refine ⟨hne, ?_, ?_⟩
    · by_cases hemp : historyAt c l = []
      · exact Or.inl hemp
      · obtain ⟨L, e, hpre, he, heq⟩ := exists_prefix_historyAt c l hemp
        have hraw := hall (L ++ [e]) hpre (by simp)
        rw [parRaw_concat_mem c R S L e he] at hraw
        exact Or.inr (heq ▸ hraw)
    · by_cases hemp : historyAt cᶜ l = []
      · exact Or.inl hemp
      · obtain ⟨L, e, hpre, he, heq⟩ := exists_prefix_historyAt cᶜ l hemp
        have hraw := hall (L ++ [e]) hpre (by simp)
        rw [parRaw_concat_not_mem c R S L e he] at hraw
        exact Or.inr (heq ▸ hraw)
  · rintro ⟨hne, hR, hS⟩
    refine (mem_dom_validate (parRaw c R S) l).mpr ⟨hne, fun l' hpre hne' => ?_⟩
    obtain ⟨L, e, rfl⟩ : ∃ L e, l' = L ++ [e] := by
      rcases List.eq_nil_or_concat l' with rfl | ⟨L, e, rfl⟩
      · exact absurd rfl hne'
      · exact ⟨L, e, List.concat_eq_append⟩
    by_cases he : e ∈ c
    · rw [parRaw_concat_mem c R S L e he]
      have hsub : historyAt c L ++ [e] <+: historyAt c l := by
        rw [← historyAt_append_mem c L e he]; exact historyAt_prefix c hpre
      rcases hR with hemp | hdom
      · rw [hemp] at hsub; simp at hsub
      · exact prefix_closed R hsub (by simp) hdom
    · rw [parRaw_concat_not_mem c R S L e he]
      have hsub : historyAt cᶜ L ++ [e] <+: historyAt cᶜ l := by
        rw [← historyAt_append_mem cᶜ L e he]; exact historyAt_prefix cᶜ hpre
      rcases hS with hemp | hdom
      · rw [hemp] at hsub; simp at hsub
      · exact prefix_closed S hsub (by simp) hdom

/-- At the frontier, a query owned by the left component certifies that
component's own extended sub-history. -/
theorem mem_dom_left_of_mem_dom_par (c : Set X) (R S : DDS X Y) (l : List X) (q : X)
    (hq : q ∈ c) (h : l ++ [q] ∈ dom (par c R S)) :
    historyAt c l ++ [q] ∈ dom R := by
  rcases ((mem_dom_par c R S (l ++ [q])).mp h).2.1 with hemp | hdom
  · rw [historyAt_append_mem c l q hq] at hemp; simp at hemp
  · rwa [historyAt_append_mem c l q hq] at hdom

/-- At the frontier, a query owned by the right component certifies that
component's own extended sub-history. -/
theorem mem_dom_right_of_mem_dom_par (c : Set X) (R S : DDS X Y) (l : List X) (q : X)
    (hq : q ∉ c) (h : l ++ [q] ∈ dom (par c R S)) :
    historyAt cᶜ l ++ [q] ∈ dom S := by
  rcases ((mem_dom_par c R S (l ++ [q])).mp h).2.2 with hemp | hdom
  · rw [historyAt_append_mem cᶜ l q hq] at hemp; simp at hemp
  · rwa [historyAt_append_mem cᶜ l q hq] at hdom

/-- The answer to a query owned by the left component is that component's
answer on its own sub-history. -/
theorem output_par_mem (c : Set X) (R S : DDS X Y) (l : List X) (q : X) (hq : q ∈ c)
    (h : l ++ [q] ∈ dom (par c R S)) (hR : historyAt c l ++ [q] ∈ dom R) :
    output (par c R S) (l ++ [q]) h = output R (historyAt c l ++ [q]) hR := by
  apply output_validate_of_eq_some
  rw [parRaw_concat_mem c R S l q hq]
  exact (Part.some_get hR).symm

/-- The answer to a query owned by the right component is that component's
answer on its own sub-history. -/
theorem output_par_not_mem (c : Set X) (R S : DDS X Y) (l : List X) (q : X) (hq : q ∉ c)
    (h : l ++ [q] ∈ dom (par c R S)) (hS : historyAt cᶜ l ++ [q] ∈ dom S) :
    output (par c R S) (l ++ [q]) h = output S (historyAt cᶜ l ++ [q]) hS := by
  apply output_validate_of_eq_some
  rw [parRaw_concat_not_mem c R S l q hq]
  exact (Part.some_get hS).symm

/-! ## The frontier receipts

Extending a parallel composition at the frontier: the query's owner is
tested on its own extended sub-history, and the other component's clause
is carried over untouched.  The `hl` hypothesis is the caller's coherence
certificate for the past. -/

/-- **The frontier receipt, left**: a query owned by `c` extends the
composition exactly when the left component accepts its own extended
sub-history, the right component's clause being unchanged. -/
theorem mem_dom_par_concat_mem (c : Set X) (R S : DDS X Y) {l : List X} {q : X}
    (hq : q ∈ c) (hl : l = [] ∨ l ∈ dom (par c R S)) :
    l ++ [q] ∈ dom (par c R S) ↔
      (historyAt c l ++ [q] ∈ dom R ∧
        (historyAt cᶜ l = [] ∨ historyAt cᶜ l ∈ dom S)) := by
  have hqc : q ∉ cᶜ := by simpa using hq
  constructor
  · intro h
    rw [mem_dom_par, historyAt_append_mem c l q hq,
      historyAt_append_not_mem cᶜ l q hqc] at h
    obtain ⟨-, hR, hS⟩ := h
    refine ⟨?_, hS⟩
    rcases hR with hemp | hdom
    · simp at hemp
    · exact hdom
  · rintro ⟨hR, -⟩
    refine (mem_dom_validate_concat (S := parRaw c R S) hl q).mpr ?_
    rw [parRaw_concat_mem c R S l q hq]
    exact hR

/-- **The frontier receipt, right**: the mirror — a query owned by the
complement extends the composition exactly when the right component
accepts its own extended sub-history. -/
theorem mem_dom_par_concat_not_mem (c : Set X) (R S : DDS X Y) {l : List X} {q : X}
    (hq : q ∉ c) (hl : l = [] ∨ l ∈ dom (par c R S)) :
    l ++ [q] ∈ dom (par c R S) ↔
      ((historyAt c l = [] ∨ historyAt c l ∈ dom R) ∧
        historyAt cᶜ l ++ [q] ∈ dom S) := by
  have hqc : q ∈ cᶜ := by simpa using hq
  constructor
  · intro h
    rw [mem_dom_par, historyAt_append_not_mem c l q hq,
      historyAt_append_mem cᶜ l q hqc] at h
    obtain ⟨-, hR, hS⟩ := h
    refine ⟨hR, ?_⟩
    rcases hS with hemp | hdom
    · simp at hemp
    · exact hdom
  · rintro ⟨-, hS⟩
    refine (mem_dom_validate_concat (S := parRaw c R S) hl q).mpr ?_
    rw [parRaw_concat_not_mem c R S l q hq]
    exact hS

/-- The domain of a composition whose **right** component is itself a
composition: the nested nonemptiness side condition collapses, leaving one
clause per leaf. -/
theorem mem_dom_par_right (c d : Set X) (R S T : DDS X Y) (l : List X) :
    l ∈ dom (par c R (par d S T)) ↔
      l ≠ [] ∧ (historyAt c l = [] ∨ historyAt c l ∈ dom R) ∧
        (historyAt (d ∩ cᶜ) l = [] ∨ historyAt (d ∩ cᶜ) l ∈ dom S) ∧
        (historyAt (dᶜ ∩ cᶜ) l = [] ∨ historyAt (dᶜ ∩ cᶜ) l ∈ dom T) := by
  have hS : historyAt d (historyAt cᶜ l) = historyAt (d ∩ cᶜ) l := historyAt_historyAt d cᶜ l
  have hT : historyAt dᶜ (historyAt cᶜ l) = historyAt (dᶜ ∩ cᶜ) l := historyAt_historyAt dᶜ cᶜ l
  rw [mem_dom_par]
  constructor
  · rintro ⟨hne, hR, hrest⟩
    refine ⟨hne, hR, ?_⟩
    rcases hrest with hemp | hdom
    · exact ⟨Or.inl (by rw [← hS, hemp, historyAt_nil]),
        Or.inl (by rw [← hT, hemp, historyAt_nil])⟩
    · obtain ⟨-, h2, h3⟩ := (mem_dom_par d S T _).mp hdom
      rw [hS] at h2
      rw [hT] at h3
      exact ⟨h2, h3⟩
  · rintro ⟨hne, hR, h2, h3⟩
    refine ⟨hne, hR, ?_⟩
    by_cases hemp : historyAt cᶜ l = []
    · exact Or.inl hemp
    · exact Or.inr ((mem_dom_par d S T _).mpr ⟨hemp, by rwa [hS], by rwa [hT]⟩)

/-- The domain of a composition whose **left** component is itself a
composition — the mirror of `mem_dom_par_right`, through `par_comm`. -/
theorem mem_dom_par_left (c d : Set X) (R S T : DDS X Y) (l : List X) :
    l ∈ dom (par c (par d R S) T) ↔
      l ≠ [] ∧ (historyAt (d ∩ c) l = [] ∨ historyAt (d ∩ c) l ∈ dom R) ∧
        (historyAt (dᶜ ∩ c) l = [] ∨ historyAt (dᶜ ∩ c) l ∈ dom S) ∧
        (historyAt cᶜ l = [] ∨ historyAt cᶜ l ∈ dom T) := by
  rw [par_comm c (par d R S) T, mem_dom_par_right cᶜ d T R S l, compl_compl]
  tauto

/-- **Associativity**: composing `R` against `S` and `T` already composed at
`c'` is composing `R` and `S` at `c` first — the splittings combine as the
union, and every query keeps its owner. -/
theorem par_assoc (c c' : Set X) (R S T : DDS X Y) :
    par c R (par c' S T) = par (c ∪ c') (par c R S) T := by
  have hset₁ : (c ∩ (c ∪ c') : Set X) = c :=
    Set.inter_eq_left.mpr Set.subset_union_left
  have hset₂ : (cᶜ ∩ (c ∪ c') : Set X) = c' ∩ cᶜ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff]
    tauto
  have hset₃ : ((c ∪ c')ᶜ : Set X) = c'ᶜ ∩ cᶜ := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_inter_iff]
    tauto
  have hA : ∀ m : List X, historyAt c (historyAt (c ∪ c') m) = historyAt c m := fun m => by
    rw [historyAt_historyAt, hset₁]
  have hB : ∀ m : List X,
      historyAt cᶜ (historyAt (c ∪ c') m) = historyAt c' (historyAt cᶜ m) := fun m => by
    rw [historyAt_historyAt, historyAt_historyAt, hset₂]
  have hC : ∀ m : List X,
      historyAt (c ∪ c')ᶜ m = historyAt c'ᶜ (historyAt cᶜ m) := fun m => by
    rw [historyAt_historyAt, hset₃]
  have hdom : ∀ m : List X,
      m ∈ dom (par c R (par c' S T)) ↔ m ∈ dom (par (c ∪ c') (par c R S) T) := fun m => by
    rw [mem_dom_par_right c c' R S T m, mem_dom_par_left (c ∪ c') c R S T m,
      hset₁, hset₂, hset₃]
  apply Subtype.ext
  funext l
  refine Part.ext' (hdom l) fun h₁ h₂ => ?_
  show output (par c R (par c' S T)) l h₁ = output (par (c ∪ c') (par c R S) T) l h₂
  obtain ⟨L, e, rfl⟩ : ∃ L e, l = L ++ [e] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, e, rfl⟩
    · exact absurd rfl ((mem_dom_par c R (par c' S T) []).mp h₁).1
    · exact ⟨L, e, List.concat_eq_append⟩
  by_cases he : e ∈ c
  · have hdomPar : historyAt (c ∪ c') L ++ [e] ∈ dom (par c R S) :=
      mem_dom_left_of_mem_dom_par (c ∪ c') (par c R S) T L e (Set.mem_union_left c' he) h₂
    have hdomR : historyAt c L ++ [e] ∈ dom R :=
      mem_dom_left_of_mem_dom_par c R (par c' S T) L e he h₁
    have hdomR' : historyAt c (historyAt (c ∪ c') L) ++ [e] ∈ dom R :=
      mem_dom_left_of_mem_dom_par c R S _ e he hdomPar
    rw [output_par_mem c R (par c' S T) L e he h₁ hdomR,
      output_par_mem (c ∪ c') (par c R S) T L e (Set.mem_union_left c' he) h₂ hdomPar,
      output_par_mem c R S (historyAt (c ∪ c') L) e he hdomPar hdomR']
    exact output_congr R (by rw [hA L]) hdomR hdomR'
  · have hdomInner : historyAt cᶜ L ++ [e] ∈ dom (par c' S T) :=
      mem_dom_right_of_mem_dom_par c R (par c' S T) L e he h₁
    by_cases he' : e ∈ c'
    · have hdomPar : historyAt (c ∪ c') L ++ [e] ∈ dom (par c R S) :=
        mem_dom_left_of_mem_dom_par (c ∪ c') (par c R S) T L e (Set.mem_union_right c he') h₂
      have hdomS : historyAt c' (historyAt cᶜ L) ++ [e] ∈ dom S :=
        mem_dom_left_of_mem_dom_par c' S T _ e he' hdomInner
      have hdomS' : historyAt cᶜ (historyAt (c ∪ c') L) ++ [e] ∈ dom S :=
        mem_dom_right_of_mem_dom_par c R S _ e he hdomPar
      rw [output_par_not_mem c R (par c' S T) L e he h₁ hdomInner,
        output_par_mem c' S T (historyAt cᶜ L) e he' hdomInner hdomS,
        output_par_mem (c ∪ c') (par c R S) T L e (Set.mem_union_right c he') h₂ hdomPar,
        output_par_not_mem c R S (historyAt (c ∪ c') L) e he hdomPar hdomS']
      exact output_congr S (by rw [hB L]) hdomS hdomS'
    · have heu : e ∉ c ∪ c' := fun hmem => hmem.elim he he'
      have hdomT : historyAt c'ᶜ (historyAt cᶜ L) ++ [e] ∈ dom T :=
        mem_dom_right_of_mem_dom_par c' S T _ e he' hdomInner
      have hdomT' : historyAt (c ∪ c')ᶜ L ++ [e] ∈ dom T :=
        mem_dom_right_of_mem_dom_par (c ∪ c') (par c R S) T L e heu h₂
      rw [output_par_not_mem c R (par c' S T) L e he h₁ hdomInner,
        output_par_not_mem c' S T (historyAt cᶜ L) e he' hdomInner hdomT,
        output_par_not_mem (c ∪ c') (par c R S) T L e heu h₂ hdomT']
      exact output_congr T (by rw [hC L]) hdomT hdomT'

/-- **The interface set of a parallel composition**: each component
contributes only the queries it owns. -/
theorem support_par (c : Set X) (R S : DDS X Y) :
    support (par c R S) ⊆ (support R ∩ c) ∪ (support S ∩ cᶜ) := by
  rintro q ⟨l, hl, hq⟩
  obtain ⟨-, hR, hS⟩ := (mem_dom_par c R S l).mp hl
  by_cases hc : q ∈ c
  · refine Or.inl ⟨?_, hc⟩
    have hmem : q ∈ historyAt c l := (mem_historyAt c l q).mpr ⟨hq, hc⟩
    rcases hR with hemp | hdom
    · rw [hemp] at hmem; simp at hmem
    · exact ⟨historyAt c l, hdom, hmem⟩
  · refine Or.inr ⟨?_, hc⟩
    have hmem : q ∈ historyAt cᶜ l := (mem_historyAt cᶜ l q).mpr ⟨hq, hc⟩
    rcases hS with hemp | hdom
    · rw [hemp] at hmem; simp at hmem
    · exact ⟨historyAt cᶜ l, hdom, hmem⟩

/-! ## Attachment against the parallel frame (MR16 §2.2 · Φ-SPEC O6)

The statement is MR16 §2.2's *context-insensitivity*, `𝓡 —γ→ 𝒮 ⟹
[𝓤,𝓡,𝓥] —γ→ [𝓤,𝒮,𝓥]`, with "`γ` knows which resource it needs to access"
realized by the tag: §7 supplies only the party grouping that names `Z`.

An engine attached at interface `i` cannot see a parallel frame installed
at an interface set `Z ∋ i`: every request the engine places carries the
tag `i`, so it is owned by the left component throughout, and the right
component's sub-history never moves.  The theorems below are the framing
law `attachEngine i E [R, S] = [attachEngine i E R, S]` at the splitting
`{p | p.1 ∈ Z}`, proven exactly as the other mixed cells — a fuel-inducted
round receipt, a snoc-inducted master carrying the reached states of both
sides, and the `Subtype.ext` ending.

These statements live here rather than in `Connect.lean` only because
`par` does: `Connect.lean` is upstream of this module.  Namespaces and
names are the ones the attachment theory uses. -/

section Framing

universe w

variable {P : Type u} {A : Type v} {B : Type w}

/-- **The engine cannot see the parallel frame**: a round of the tagged
engine against `[R, S]` at a splitting owning `i` is its round against `R`
alone on `R`'s own sub-history, re-based over the outer resource
history. -/
theorem serve_tagAt_par {i : P} {Z : Set P} (hiZ : i ∈ Z)
    {E : DDS (A ⊕ B) (B ⊕ A)} {R S : Resource P A B} :
    ∀ (n : ℕ) {conv : List (A ⊕ B)} {rh : List (P × A)},
      (historyAt {p : P × A | p.1 ∈ Z} rh = [] ∨
        historyAt {p : P × A | p.1 ∈ Z} rh ∈ dom R) →
      (historyAt {p : P × A | p.1 ∈ Z}ᶜ rh = [] ∨
        historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ∈ dom S) →
      Connect.serve (tagAt i E) (par {p : P × A | p.1 ∈ Z} R S) n (conv, rh) =
        (Connect.serve (tagAt i E) R n
            (conv, historyAt {p : P × A | p.1 ∈ Z} rh)).map
          (fun q => (q.1, (q.2.1,
            rh ++ q.2.2.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length))) := by
  intro n
  induction n with
  | zero =>
      intro conv rh _ _
      show Part.none = Part.map _ Part.none
      simp
  | succ n ih =>
      intro conv rh hRc hSc
      rw [Connect.serve_succ, Connect.serve_succ]
      by_cases hE : conv ∈ dom (tagAt i E)
      · rw [dif_pos hE, dif_pos hE]
        have hE' : conv ∈ dom E := (mem_dom_tagAt i E conv).mp hE
        rw [output_tagAt i E hE hE']
        rcases hout : output E conv hE' with b | a'
        · simp only [Sum.map_inl, id_eq, Sum.elim_inl, Part.map_some,
            List.drop_length, List.append_nil]
        · simp only [Sum.map_inr, Sum.elim_inr]
          have hq : ((i, a') : P × A) ∈ {p : P × A | p.1 ∈ Z} := hiZ
          have hqc : ((i, a') : P × A) ∉ {p : P × A | p.1 ∈ Z}ᶜ := by
            simpa using hq
          have hl : rh = [] ∨ rh ∈ dom (par {p : P × A | p.1 ∈ Z} R S) := by
            rcases eq_or_ne rh [] with rfl | hne
            · exact Or.inl rfl
            · exact Or.inr ((mem_dom_par _ R S rh).mpr ⟨hne, hRc, hSc⟩)
          have hdomiff : rh ++ [(i, a')] ∈ dom (par {p : P × A | p.1 ∈ Z} R S) ↔
              historyAt {p : P × A | p.1 ∈ Z} rh ++ [(i, a')] ∈ dom R := by
            rw [mem_dom_par_concat_mem _ R S hq hl]
            exact ⟨fun h => h.1, fun h => ⟨h, hSc⟩⟩
          by_cases hR : historyAt {p : P × A | p.1 ∈ Z} rh ++ [(i, a')] ∈ dom R
          · rw [dif_pos (hdomiff.mpr hR), dif_pos hR,
              output_par_mem _ R S rh (i, a') hq (hdomiff.mpr hR) hR]
            have hstep := ih
              (conv := conv ++ [Sum.inr (output R
                (historyAt {p : P × A | p.1 ∈ Z} rh ++ [(i, a')]) hR)])
              (rh := rh ++ [(i, a')])
              (by rw [historyAt_append_mem _ rh (i, a') hq]; exact Or.inr hR)
              (by rw [historyAt_append_not_mem _ rh (i, a') hqc]; exact hSc)
            rw [historyAt_append_mem _ rh (i, a') hq] at hstep
            rw [hstep]
            have hidx : ∀ {rh₂ : List (P × A)},
                historyAt {p : P × A | p.1 ∈ Z} rh ++ [(i, a')] <+: rh₂ →
                (rh ++ [(i, a')]) ++
                    rh₂.drop (historyAt {p : P × A | p.1 ∈ Z} rh ++
                      [(i, a')]).length =
                  rh ++ rh₂.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length := by
              rintro rh₂ ⟨t, rfl⟩
              rw [List.drop_left,
                List.append_assoc (historyAt {p : P × A | p.1 ∈ Z} rh),
                List.drop_left]
              simp
            refine Part.ext fun z => ?_
            rw [Part.mem_map_iff, Part.mem_map_iff]
            constructor
            · rintro ⟨q, hq', rfl⟩
              exact ⟨q, hq', by rw [hidx (Connect.serve_rh_prefix hq')]⟩
            · rintro ⟨q, hq', rfl⟩
              exact ⟨q, hq', by rw [hidx (Connect.serve_rh_prefix hq')]⟩
          · rw [dif_neg (fun hc => hR (hdomiff.mp hc)), dif_neg hR]
            show Part.none = Part.map _ Part.none
            simp
      · rw [dif_neg hE, dif_neg hE]
        show Part.none = Part.map _ Part.none
        simp

/-- **The frame is untouched**: the propagation clause of `serve_tagAt_par`.
Every query the tagged engine appends carries the tag `i ∈ Z`, so the
resolved run's outer resource history projects onto the inner run's final
history at `Z`, leaves the complement's sub-history where it was, and
carries both components' domain clauses forward. -/
theorem serve_tagAt_par_state {i : P} {Z : Set P} (hiZ : i ∈ Z)
    {E : DDS (A ⊕ B) (B ⊕ A)} {R S : Resource P A B} {n : ℕ}
    {conv : List (A ⊕ B)} {rh : List (P × A)} {b : B}
    {conv' : List (A ⊕ B)} {rh' : List (P × A)}
    (hRc : historyAt {p : P × A | p.1 ∈ Z} rh = [] ∨
      historyAt {p : P × A | p.1 ∈ Z} rh ∈ dom R)
    (hSc : historyAt {p : P × A | p.1 ∈ Z}ᶜ rh = [] ∨
      historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ∈ dom S)
    (hmem : (b, (conv', rh')) ∈
      Connect.serve (tagAt i E) R n
        (conv, historyAt {p : P × A | p.1 ∈ Z} rh)) :
    historyAt {p : P × A | p.1 ∈ Z}
        (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) = rh' ∧
      historyAt {p : P × A | p.1 ∈ Z}ᶜ
          (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) =
        historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ∧
      (historyAt {p : P × A | p.1 ∈ Z}
          (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) = [] ∨
        historyAt {p : P × A | p.1 ∈ Z}
          (rh ++ rh'.drop
            (historyAt {p : P × A | p.1 ∈ Z} rh).length) ∈ dom R) ∧
      (historyAt {p : P × A | p.1 ∈ Z}ᶜ
          (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) = [] ∨
        historyAt {p : P × A | p.1 ∈ Z}ᶜ
          (rh ++ rh'.drop
            (historyAt {p : P × A | p.1 ∈ Z} rh).length) ∈ dom S) := by
  have hpre : historyAt {p : P × A | p.1 ∈ Z} rh <+: rh' :=
    Connect.serve_rh_prefix hmem
  obtain ⟨t, ht⟩ := hpre
  have htZ : ∀ q ∈ t, q.1 ∈ Z := by
    intro q hqt
    have hq' : q ∈ rh' := by
      rw [← ht]
      exact List.mem_append_right _ hqt
    rcases serve_tagAt_rh_mem hmem q hq' with hin | htag
    · exact ((mem_historyAt _ rh q).mp hin).2
    · rw [htag]
      exact hiZ
  have hdrop : rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length = t := by
    rw [← ht, List.drop_left]
  have htself : historyAt {p : P × A | p.1 ∈ Z} t = t := by
    simpa [historyAt, List.filter_eq_self] using htZ
  have htnil : historyAt {p : P × A | p.1 ∈ Z}ᶜ t = [] := by
    simpa [historyAt, List.filter_eq_nil_iff] using htZ
  have hproj₁ : historyAt {p : P × A | p.1 ∈ Z}
      (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) = rh' := by
    rw [hdrop, historyAt_append, htself]
    exact ht
  have hproj₂ : historyAt {p : P × A | p.1 ∈ Z}ᶜ
      (rh ++ rh'.drop (historyAt {p : P × A | p.1 ∈ Z} rh).length) =
      historyAt {p : P × A | p.1 ∈ Z}ᶜ rh := by
    rw [hdrop, historyAt_append, htnil, List.append_nil]
  refine ⟨hproj₁, hproj₂, ?_, ?_⟩
  · rw [hproj₁]
    have hrhd : rh' = historyAt {p : P × A | p.1 ∈ Z} rh ∨ rh' ∈ dom R :=
      Connect.serve_rh_dom hmem
    rcases hrhd with heq | hdom
    · rw [heq]
      exact hRc
    · exact Or.inr hdom
  · rw [hproj₂]
    exact hSc

/-- The framing master: the two systems agree on domain and output, and
the induction carries the reached states of both sides together with their
cross-identifications — the engine's conversations agree, the outer
resource history projects onto the inner one at `Z`, and the complement's
sub-history is the outer one's. -/
theorem attachEngine_par_aux {i : P} {Z : Set P} (hiZ : i ∈ Z)
    (E : DDS (A ⊕ B) (B ⊕ A)) (R S : Resource P A B) :
    ∀ us : List (P × A),
      (us ∈ dom (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S)) ↔
        us ∈ dom (par {p : P × A | p.1 ∈ Z} (connect (liftAt i E) R) S)) ∧
      (∀ (h₁ : us ∈ dom (connect (liftAt i E)
            (par {p : P × A | p.1 ∈ Z} R S)))
        (h₂ : us ∈ dom (par {p : P × A | p.1 ∈ Z}
            (connect (liftAt i E) R) S)),
        output (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S)) us h₁ =
          output (par {p : P × A | p.1 ∈ Z}
            (connect (liftAt i E) R) S) us h₂) ∧
      (us = [] ∨ us ∈ dom (connect (liftAt i E)
          (par {p : P × A | p.1 ∈ Z} R S)) →
        ∃ ehA rh ehB,
          AttachState (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S) us
            (ehA, rh) ∧
          AttachState (liftAt i E) R (historyAt {p : P × A | p.1 ∈ Z} us)
            (ehB, historyAt {p : P × A | p.1 ∈ Z} rh) ∧
          eProj i ehB = eProj i ehA ∧
          historyAt {p : P × A | p.1 ∈ Z}ᶜ rh =
            historyAt {p : P × A | p.1 ∈ Z}ᶜ us ∧
          (historyAt {p : P × A | p.1 ∈ Z} rh = [] ∨
            historyAt {p : P × A | p.1 ∈ Z} rh ∈ dom R) ∧
          (historyAt {p : P × A | p.1 ∈ Z}ᶜ rh = [] ∨
            historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ∈ dom S)) := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨iff_of_false (empty_not_mem _) (empty_not_mem _),
        fun h₁ _ => absurd h₁ (empty_not_mem _), fun _ => ?_⟩
      exact ⟨[], [], [], attachState_nil _ _, attachState_nil _ _, rfl, rfl,
        Or.inl rfl, Or.inl rfl⟩
  | append_singleton us x ihus =>
      obtain ⟨p, a⟩ := x
      by_cases hus : us = [] ∨
        us ∈ dom (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S))
      · obtain ⟨ehA, rh, ehB, hA, hB, hproj, hcompl, hRc, hSc⟩ := ihus.2.2 hus
        have hlR : us = [] ∨
            us ∈ dom (par {p : P × A | p.1 ∈ Z}
              (connect (liftAt i E) R) S) := by
          rcases hus with hnil | hd
          · exact Or.inl hnil
          · exact Or.inr (ihus.1.mp hd)
        have hlrh : rh = [] ∨ rh ∈ dom (par {p : P × A | p.1 ∈ Z} R S) := by
          rcases eq_or_ne rh [] with rfl | hne
          · exact Or.inl rfl
          · exact Or.inr ((mem_dom_par _ R S rh).mpr ⟨hne, hRc, hSc⟩)
        have hScus : historyAt {p : P × A | p.1 ∈ Z}ᶜ us = [] ∨
            historyAt {p : P × A | p.1 ∈ Z}ᶜ us ∈ dom S := by
          rw [← hcompl]
          exact hSc
        by_cases hpi : p = i
        · subst hpi
          have hqc : ((p, a) : P × A) ∈ {p : P × A | p.1 ∈ Z} := hiZ
          have hqcc : ((p, a) : P × A) ∉ {p : P × A | p.1 ∈ Z}ᶜ := by
            simpa using hqc
          have hL₂ : us ++ [(p, a)] ∈
              dom (connect (liftAt p E) (par {p : P × A | p.1 ∈ Z} R S)) ↔
              ∃ n, (Connect.serve (tagAt p E) R n (eProj p ehA ++ [Sum.inl a],
                historyAt {p : P × A | p.1 ∈ Z} rh)).Dom := by
            rw [attachState_own_dom_iff hA a]
            constructor
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [serve_tagAt_par hiZ (E := E) n hRc hSc] at hn
              exact hn
            · rintro ⟨n, hn⟩
              refine ⟨n, ?_⟩
              rw [serve_tagAt_par hiZ (E := E) n hRc hSc]
              exact hn
          have hR₂ : us ++ [(p, a)] ∈
              dom (par {p : P × A | p.1 ∈ Z} (connect (liftAt p E) R) S) ↔
              ∃ n, (Connect.serve (tagAt p E) R n (eProj p ehB ++ [Sum.inl a],
                historyAt {p : P × A | p.1 ∈ Z} rh)).Dom := by
            rw [mem_dom_par_concat_mem _ (connect (liftAt p E) R) S hqc hlR,
              attachState_own_dom_iff hB a]
            exact ⟨fun h => h.1, fun h => ⟨h, hScus⟩⟩
          refine ⟨by rw [hL₂, hR₂, hproj], ?_, ?_⟩
          · intro h₁ h₂
            obtain ⟨n, hn⟩ := hL₂.mp h₁
            obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
            have hqPar : (b, (conv', rh ++ rh'.drop
                (historyAt {p : P × A | p.1 ∈ Z} rh).length)) ∈
                Connect.serve (tagAt p E) (par {p : P × A | p.1 ∈ Z} R S) n
                  (eProj p ehA ++ [Sum.inl a], rh) := by
              rw [serve_tagAt_par hiZ (E := E) n hRc hSc]
              exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
            have hqB : (b, (conv', rh')) ∈ Connect.serve (tagAt p E) R n
                (eProj p ehB ++ [Sum.inl a],
                  historyAt {p : P × A | p.1 ∈ Z} rh) := by
              rw [hproj]
              exact hq
            have hTin : historyAt {p : P × A | p.1 ∈ Z} us ++ [(p, a)] ∈
                dom (connect (liftAt p E) R) :=
              (attachState_own_dom_iff hB a).mpr
                ⟨n, Part.dom_iff_mem.mpr ⟨_, hqB⟩⟩
            rw [attachState_own_output hA a hqPar h₁,
              output_par_mem _ (connect (liftAt p E) R) S us (p, a) hqc h₂
                hTin,
              attachState_own_output hB a hqB hTin]
          · rintro (hcon | h₁)
            · exact absurd hcon (by simp)
            · obtain ⟨n, hn⟩ := hL₂.mp h₁
              obtain ⟨⟨b, conv', rh'⟩, hq⟩ := Part.dom_iff_mem.mp hn
              have hqPar : (b, (conv', rh ++ rh'.drop
                  (historyAt {p : P × A | p.1 ∈ Z} rh).length)) ∈
                  Connect.serve (tagAt p E) (par {p : P × A | p.1 ∈ Z} R S) n
                    (eProj p ehA ++ [Sum.inl a], rh) := by
                rw [serve_tagAt_par hiZ (E := E) n hRc hSc]
                exact (Part.mem_map_iff _).mpr ⟨(b, (conv', rh')), hq, rfl⟩
              have hqB : (b, (conv', rh')) ∈ Connect.serve (tagAt p E) R n
                  (eProj p ehB ++ [Sum.inl a],
                    historyAt {p : P × A | p.1 ∈ Z} rh) := by
                rw [hproj]
                exact hq
              obtain ⟨ehA', hstA', hconvA'⟩ := attachState_own_state hA a hqPar
              obtain ⟨ehB', hstB', hconvB'⟩ := attachState_own_state hB a hqB
              obtain ⟨hp₁, hp₂, hRc', hSc'⟩ :=
                serve_tagAt_par_state hiZ (S := S) hRc hSc hq
              refine ⟨ehA', rh ++ rh'.drop
                  (historyAt {p : P × A | p.1 ∈ Z} rh).length, ehB',
                hstA', ?_, ?_, ?_, hRc', hSc'⟩
              · rw [historyAt_append_mem _ us (p, a) hqc, hp₁]
                exact hstB'
              · rw [hconvA', hconvB']
              · rw [hp₂, historyAt_append_not_mem _ us (p, a) hqcc]
                exact hcompl
        · by_cases hpZ : p ∈ Z
          · have hqc : ((p, a) : P × A) ∈ {p : P × A | p.1 ∈ Z} := hpZ
            have hqcc : ((p, a) : P × A) ∉ {p : P × A | p.1 ∈ Z}ᶜ := by
              simpa using hqc
            have hL₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S)) ↔
                historyAt {p : P × A | p.1 ∈ Z} rh ++ [(p, a)] ∈ dom R := by
              rw [attachState_foreign_dom_iff hA hpi a,
                mem_dom_par_concat_mem _ R S hqc hlrh]
              exact ⟨fun h => h.1, fun h => ⟨h, hSc⟩⟩
            have hR₂ : us ++ [(p, a)] ∈
                dom (par {p : P × A | p.1 ∈ Z} (connect (liftAt i E) R) S) ↔
                historyAt {p : P × A | p.1 ∈ Z} rh ++ [(p, a)] ∈ dom R := by
              rw [mem_dom_par_concat_mem _ (connect (liftAt i E) R) S hqc hlR,
                attachState_foreign_dom_iff hB hpi a]
              exact ⟨fun h => h.1, fun h => ⟨h, hScus⟩⟩
            refine ⟨by rw [hL₂, hR₂], ?_, ?_⟩
            · intro h₁ h₂
              have hRdom : historyAt {p : P × A | p.1 ∈ Z} rh ++ [(p, a)] ∈
                  dom R := hL₂.mp h₁
              have hTpar : rh ++ [(p, a)] ∈
                  dom (par {p : P × A | p.1 ∈ Z} R S) :=
                (mem_dom_par_concat_mem _ R S hqc hlrh).mpr ⟨hRdom, hSc⟩
              have hTin : historyAt {p : P × A | p.1 ∈ Z} us ++ [(p, a)] ∈
                  dom (connect (liftAt i E) R) :=
                (attachState_foreign_dom_iff hB hpi a).mpr hRdom
              rw [attachState_foreign_output hA hpi hTpar h₁,
                output_par_mem _ R S rh (p, a) hqc hTpar hRdom,
                output_par_mem _ (connect (liftAt i E) R) S us (p, a) hqc h₂
                  hTin,
                attachState_foreign_output hB hpi hRdom hTin]
            · rintro (hcon | h₁)
              · exact absurd hcon (by simp)
              · have hRdom : historyAt {p : P × A | p.1 ∈ Z} rh ++ [(p, a)] ∈
                    dom R := hL₂.mp h₁
                have hTpar : rh ++ [(p, a)] ∈
                    dom (par {p : P × A | p.1 ∈ Z} R S) :=
                  (mem_dom_par_concat_mem _ R S hqc hlrh).mpr ⟨hRdom, hSc⟩
                refine ⟨ehA ++ [Sum.inl (p, a),
                    Sum.inr (output (par {p : P × A | p.1 ∈ Z} R S)
                      (rh ++ [(p, a)]) hTpar)],
                  rh ++ [(p, a)],
                  ehB ++ [Sum.inl (p, a),
                    Sum.inr (output R (historyAt {p : P × A | p.1 ∈ Z} rh ++
                      [(p, a)]) hRdom)],
                  attachState_foreign_state hA hpi hTpar, ?_, ?_, ?_, ?_, ?_⟩
                · rw [historyAt_append_mem _ us (p, a) hqc,
                    historyAt_append_mem _ rh (p, a) hqc]
                  exact attachState_foreign_state hB hpi hRdom
                · rw [eProj_append_foreign hpi, eProj_append_foreign hpi]
                  exact hproj
                · rw [historyAt_append_not_mem _ rh (p, a) hqcc,
                    historyAt_append_not_mem _ us (p, a) hqcc]
                  exact hcompl
                · rw [historyAt_append_mem _ rh (p, a) hqc]
                  exact Or.inr hRdom
                · rw [historyAt_append_not_mem _ rh (p, a) hqcc]
                  exact hSc
          · have hqc : ((p, a) : P × A) ∉ {p : P × A | p.1 ∈ Z} := hpZ
            have hqcc : ((p, a) : P × A) ∈ {p : P × A | p.1 ∈ Z}ᶜ := hpZ
            have hRcus : historyAt {p : P × A | p.1 ∈ Z} us = [] ∨
                historyAt {p : P × A | p.1 ∈ Z} us ∈
                  dom (connect (liftAt i E) R) := by
              rcases hB with ⟨hnil, -⟩ | ⟨n, b, hmem⟩
              · exact Or.inl hnil
              · exact Or.inr ((mem_dom_connect_iff _ _ _).mpr
                  ⟨n, Part.dom_iff_mem.mpr ⟨_, hmem⟩⟩)
            have hL₂ : us ++ [(p, a)] ∈
                dom (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S)) ↔
                historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ++ [(p, a)] ∈ dom S := by
              rw [attachState_foreign_dom_iff hA hpi a,
                mem_dom_par_concat_not_mem _ R S hqc hlrh]
              exact ⟨fun h => h.2, fun h => ⟨hRc, h⟩⟩
            have hR₂ : us ++ [(p, a)] ∈
                dom (par {p : P × A | p.1 ∈ Z} (connect (liftAt i E) R) S) ↔
                historyAt {p : P × A | p.1 ∈ Z}ᶜ us ++ [(p, a)] ∈ dom S := by
              rw [mem_dom_par_concat_not_mem _ (connect (liftAt i E) R) S hqc
                hlR]
              exact ⟨fun h => h.2, fun h => ⟨hRcus, h⟩⟩
            refine ⟨by rw [hL₂, hR₂, hcompl], ?_, ?_⟩
            · intro h₁ h₂
              have hSdom : historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ++ [(p, a)] ∈
                  dom S := hL₂.mp h₁
              have hSdom' : historyAt {p : P × A | p.1 ∈ Z}ᶜ us ++ [(p, a)] ∈
                  dom S := by
                rw [← hcompl]
                exact hSdom
              have hTpar : rh ++ [(p, a)] ∈
                  dom (par {p : P × A | p.1 ∈ Z} R S) :=
                (mem_dom_par_concat_not_mem _ R S hqc hlrh).mpr ⟨hRc, hSdom⟩
              rw [attachState_foreign_output hA hpi hTpar h₁,
                output_par_not_mem _ R S rh (p, a) hqc hTpar hSdom,
                output_par_not_mem _ (connect (liftAt i E) R) S us (p, a) hqc
                  h₂ hSdom']
              exact output_congr S (by rw [hcompl]) hSdom hSdom'
            · rintro (hcon | h₁)
              · exact absurd hcon (by simp)
              · have hSdom : historyAt {p : P × A | p.1 ∈ Z}ᶜ rh ++ [(p, a)] ∈
                    dom S := hL₂.mp h₁
                have hTpar : rh ++ [(p, a)] ∈
                    dom (par {p : P × A | p.1 ∈ Z} R S) :=
                  (mem_dom_par_concat_not_mem _ R S hqc hlrh).mpr ⟨hRc, hSdom⟩
                refine ⟨ehA ++ [Sum.inl (p, a),
                    Sum.inr (output (par {p : P × A | p.1 ∈ Z} R S)
                      (rh ++ [(p, a)]) hTpar)],
                  rh ++ [(p, a)], ehB,
                  attachState_foreign_state hA hpi hTpar, ?_, ?_, ?_, ?_, ?_⟩
                · rw [historyAt_append_not_mem _ us (p, a) hqc,
                    historyAt_append_not_mem _ rh (p, a) hqc]
                  exact hB
                · rw [eProj_append_foreign hpi]
                  exact hproj
                · rw [historyAt_append_mem _ rh (p, a) hqcc,
                    historyAt_append_mem _ us (p, a) hqcc, hcompl]
                · rw [historyAt_append_not_mem _ rh (p, a) hqc]
                  exact hRc
                · rw [historyAt_append_mem _ rh (p, a) hqcc]
                  exact Or.inr hSdom
      · push Not at hus
        obtain ⟨hne, hnd⟩ := hus
        have hL' : us ++ [(p, a)] ∉
            dom (connect (liftAt i E) (par {p : P × A | p.1 ∈ Z} R S)) :=
          fun h => hnd (prefix_closed _ (List.prefix_append _ _) hne h)
        have hR' : us ++ [(p, a)] ∉
            dom (par {p : P × A | p.1 ∈ Z} (connect (liftAt i E) R) S) :=
          fun h => hnd (ihus.1.mpr
            (prefix_closed _ (List.prefix_append _ _) hne h))
        refine ⟨iff_of_false hL' hR', fun h₁ _ => absurd h₁ hL',
          fun hcon => ?_⟩
        rcases hcon with hcon | hcon
        · exact absurd hcon (by simp)
        · exact absurd hcon hL'

/-- **The framing law** (Φ-SPEC O6): an engine attached at an interface of
`Z` cannot see a parallel frame installed at `Z` — attachment passes
through the composition, leaving the other component alone. -/
theorem attachEngine_par {i : P} {Z : Set P} (hiZ : i ∈ Z)
    (E : DDS (A ⊕ B) (B ⊕ A)) (R S : Resource P A B) :
    attachEngine i E (par {p : P × A | p.1 ∈ Z} R S) =
      par {p : P × A | p.1 ∈ Z} (attachEngine i E R) S := by
  apply Subtype.ext
  funext us
  refine Part.ext' (attachEngine_par_aux hiZ E R S us).1
    fun h₁ h₂ => (attachEngine_par_aux hiZ E R S us).2.1 h₁ h₂

end Framing

/-! ## Inclusion transfers

The typed view of a parallel composition installed at an interface set's
included queries is the parallel composition of the typed views, at the
tag cylinder: the inclusion is entrywise, so it commutes with taking
sub-histories, and `encode_preimage_tags` identifies the two splittings. -/

section Inclusion

variable {P A B : Type u}

/-- Sub-histories commute with the inclusion: the inclusion is entrywise,
so the queries an included history contributes at `c` are the included
queries contributed at `c`'s preimage. -/
theorem historyAt_map_encode (c : Set Uni.{u}) (l : List X) :
    historyAt c (l.map (encode X)) =
      (historyAt (encode X ⁻¹' c) l).map (encode X) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton m x ih =>
      rw [List.map_append, List.map_cons, List.map_nil]
      by_cases hx : x ∈ encode X ⁻¹' c
      · rw [historyAt_append_mem c (m.map (encode X)) (encode X x) hx,
          historyAt_append_mem _ m x hx, ih, List.map_append, List.map_cons,
          List.map_nil]
      · rw [historyAt_append_not_mem c (m.map (encode X)) (encode X x) hx,
          historyAt_append_not_mem _ m x hx, ih]

/-- **Inclusion transfer for `par`**: the typed view of a composition
split at an interface set's included queries is the composition of the
typed views split at the tag cylinder. -/
theorem toTyped_par (Z : Set P) (Rb Sb : DDS Uni.{u} Uni.{u}) :
    toTyped (P × A) B
        (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A, q = encode (P × A) (p, a)}
          Rb Sb) =
      par {p : P × A | p.1 ∈ Z} (toTyped (P × A) B Rb)
        (toTyped (P × A) B Sb) := by
  have hmapZ : ∀ l : List (P × A),
      historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A, q = encode (P × A) (p, a)}
          (l.map (encode (P × A))) =
        (historyAt {p : P × A | p.1 ∈ Z} l).map (encode (P × A)) := fun l => by
    rw [historyAt_map_encode, encode_preimage_tags]
  have hmapZc : ∀ l : List (P × A),
      historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A, q = encode (P × A) (p, a)}ᶜ
          (l.map (encode (P × A))) =
        (historyAt {p : P × A | p.1 ∈ Z}ᶜ l).map (encode (P × A)) := fun l => by
    rw [historyAt_map_encode, Set.preimage_compl, encode_preimage_tags]
  have hclauses : ∀ {m : List Uni.{u}},
      (m = [] ∨ m ∈ dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} Rb Sb)) →
      (historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)} m = [] ∨
        historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)} m ∈ dom Rb) ∧
      (historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)}ᶜ m = [] ∨
        historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)}ᶜ m ∈ dom Sb) := by
    rintro m (rfl | hm)
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨((mem_dom_par _ Rb Sb m).mp hm).2.1,
        ((mem_dom_par _ Rb Sb m).mp hm).2.2⟩
  have hrawMem : ∀ {l : List (P × A)} {x : P × A},
      (l.map (encode (P × A)) = [] ∨ l.map (encode (P × A)) ∈
        dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb)) → x.1 ∈ Z →
      toTypedRaw (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb) (l ++ [x]) =
        toTypedRaw (P × A) B Rb
          (historyAt {p : P × A | p.1 ∈ Z} l ++ [x]) := by
    intro l x hpar hx
    have hq : encode (P × A) x ∈ {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} := ⟨x.1, hx, x.2, rfl⟩
    have hcomp : (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb).1
          (l.map (encode (P × A)) ++ [encode (P × A) x]) =
        Rb.1 ((historyAt {p : P × A | p.1 ∈ Z} l).map (encode (P × A)) ++
          [encode (P × A) x]) := by
      refine Part.ext' ?_ ?_
      · show l.map (encode (P × A)) ++ [encode (P × A) x] ∈
            dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
              q = encode (P × A) (p, a)} Rb Sb) ↔
          (historyAt {p : P × A | p.1 ∈ Z} l).map (encode (P × A)) ++
            [encode (P × A) x] ∈ dom Rb
        rw [mem_dom_par_concat_mem _ Rb Sb hq hpar, hmapZ l]
        exact ⟨fun h => h.1, fun h => ⟨h, (hclauses hpar).2⟩⟩
      · intro h₁ h₂
        have hRdom : historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
              q = encode (P × A) (p, a)} (l.map (encode (P × A))) ++
            [encode (P × A) x] ∈ dom Rb := by
          rw [hmapZ l]
          exact h₂
        show output (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)} Rb Sb) _ h₁ = output Rb _ h₂
        rw [output_par_mem _ Rb Sb (l.map (encode (P × A)))
          (encode (P × A) x) hq h₁ hRdom]
        exact output_congr Rb (by rw [hmapZ l]) hRdom h₂
    show ((par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} Rb Sb).1
          ((l ++ [x]).map (encode (P × A)))).bind (decode B) =
      (Rb.1 ((historyAt {p : P × A | p.1 ∈ Z} l ++ [x]).map
        (encode (P × A)))).bind (decode B)
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hcomp]
  have hrawNotMem : ∀ {l : List (P × A)} {x : P × A},
      (l.map (encode (P × A)) = [] ∨ l.map (encode (P × A)) ∈
        dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb)) → x.1 ∉ Z →
      toTypedRaw (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb) (l ++ [x]) =
        toTypedRaw (P × A) B Sb
          (historyAt {p : P × A | p.1 ∈ Z}ᶜ l ++ [x]) := by
    intro l x hpar hx
    have hq : encode (P × A) x ∉ {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} := by
      intro hc
      have hmem : x ∈ encode (P × A) ⁻¹' {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} := hc
      rw [encode_preimage_tags] at hmem
      exact hx hmem
    have hcomp : (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb).1
          (l.map (encode (P × A)) ++ [encode (P × A) x]) =
        Sb.1 ((historyAt {p : P × A | p.1 ∈ Z}ᶜ l).map (encode (P × A)) ++
          [encode (P × A) x]) := by
      refine Part.ext' ?_ ?_
      · show l.map (encode (P × A)) ++ [encode (P × A) x] ∈
            dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
              q = encode (P × A) (p, a)} Rb Sb) ↔
          (historyAt {p : P × A | p.1 ∈ Z}ᶜ l).map (encode (P × A)) ++
            [encode (P × A) x] ∈ dom Sb
        rw [mem_dom_par_concat_not_mem _ Rb Sb hq hpar, hmapZc l]
        exact ⟨fun h => h.2, fun h => ⟨(hclauses hpar).1, h⟩⟩
      · intro h₁ h₂
        have hSdom : historyAt {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
              q = encode (P × A) (p, a)}ᶜ (l.map (encode (P × A))) ++
            [encode (P × A) x] ∈ dom Sb := by
          rw [hmapZc l]
          exact h₂
        show output (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)} Rb Sb) _ h₁ = output Sb _ h₂
        rw [output_par_not_mem _ Rb Sb (l.map (encode (P × A)))
          (encode (P × A) x) hq h₁ hSdom]
        exact output_congr Sb (by rw [hmapZc l]) hSdom h₂
    show ((par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} Rb Sb).1
          ((l ++ [x]).map (encode (P × A)))).bind (decode B) =
      (Sb.1 ((historyAt {p : P × A | p.1 ∈ Z}ᶜ l ++ [x]).map
        (encode (P × A)))).bind (decode B)
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hcomp]
  have hparOf : ∀ {l : List (P × A)},
      (l = [] ∨ l ∈ dom (toTyped (P × A) B
        (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb))) →
      (l.map (encode (P × A)) = [] ∨ l.map (encode (P × A)) ∈
        dom (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb)) := by
    rintro l (rfl | hd)
    · exact Or.inl rfl
    · exact Or.inr (hd.2 l (List.prefix_refl l) hd.1).fst
  have hdom : ∀ l : List (P × A),
      l ∈ dom (toTyped (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
          q = encode (P × A) (p, a)} Rb Sb)) ↔
        l ∈ dom (par {p : P × A | p.1 ∈ Z} (toTyped (P × A) B Rb)
          (toTyped (P × A) B Sb)) := by
    intro l
    induction l using List.reverseRecOn with
    | nil => exact iff_of_false (empty_not_mem _) (empty_not_mem _)
    | append_singleton l x ih =>
        by_cases hlL : l = [] ∨ l ∈ dom (toTyped (P × A) B
          (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
            q = encode (P × A) (p, a)} Rb Sb))
        · have hlR : l = [] ∨ l ∈ dom (par {p : P × A | p.1 ∈ Z}
              (toTyped (P × A) B Rb) (toTyped (P × A) B Sb)) := by
            rcases hlL with h | h
            · exact Or.inl h
            · exact Or.inr (ih.mp h)
          have hRR : historyAt {p : P × A | p.1 ∈ Z} l = [] ∨
              historyAt {p : P × A | p.1 ∈ Z} l ∈
                dom (toTyped (P × A) B Rb) := by
            rcases hlR with rfl | hd
            · exact Or.inl rfl
            · exact ((mem_dom_par _ _ _ l).mp hd).2.1
          have hSS : historyAt {p : P × A | p.1 ∈ Z}ᶜ l = [] ∨
              historyAt {p : P × A | p.1 ∈ Z}ᶜ l ∈
                dom (toTyped (P × A) B Sb) := by
            rcases hlR with rfl | hd
            · exact Or.inl rfl
            · exact ((mem_dom_par _ _ _ l).mp hd).2.2
          by_cases hx : x.1 ∈ Z
          · have hx' : x ∈ {p : P × A | p.1 ∈ Z} := hx
            calc l ++ [x] ∈ dom (toTyped (P × A) B
                  (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
                    q = encode (P × A) (p, a)} Rb Sb))
                ↔ (toTypedRaw (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
                    q = encode (P × A) (p, a)} Rb Sb) (l ++ [x])).Dom :=
                  mem_dom_validate_concat hlL x
              _ ↔ (toTypedRaw (P × A) B Rb
                    (historyAt {p : P × A | p.1 ∈ Z} l ++ [x])).Dom := by
                  rw [hrawMem (hparOf hlL) hx]
              _ ↔ historyAt {p : P × A | p.1 ∈ Z} l ++ [x] ∈
                    dom (toTyped (P × A) B Rb) :=
                  (mem_dom_validate_concat hRR x).symm
              _ ↔ l ++ [x] ∈ dom (par {p : P × A | p.1 ∈ Z}
                    (toTyped (P × A) B Rb) (toTyped (P × A) B Sb)) := by
                  rw [mem_dom_par_concat_mem _ (toTyped (P × A) B Rb)
                    (toTyped (P × A) B Sb) hx' hlR]
                  exact ⟨fun h => ⟨h, hSS⟩, fun h => h.1⟩
          · have hx' : x ∉ {p : P × A | p.1 ∈ Z} := hx
            calc l ++ [x] ∈ dom (toTyped (P × A) B
                  (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
                    q = encode (P × A) (p, a)} Rb Sb))
                ↔ (toTypedRaw (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
                    q = encode (P × A) (p, a)} Rb Sb) (l ++ [x])).Dom :=
                  mem_dom_validate_concat hlL x
              _ ↔ (toTypedRaw (P × A) B Sb
                    (historyAt {p : P × A | p.1 ∈ Z}ᶜ l ++ [x])).Dom := by
                  rw [hrawNotMem (hparOf hlL) hx]
              _ ↔ historyAt {p : P × A | p.1 ∈ Z}ᶜ l ++ [x] ∈
                    dom (toTyped (P × A) B Sb) :=
                  (mem_dom_validate_concat hSS x).symm
              _ ↔ l ++ [x] ∈ dom (par {p : P × A | p.1 ∈ Z}
                    (toTyped (P × A) B Rb) (toTyped (P × A) B Sb)) := by
                  rw [mem_dom_par_concat_not_mem _ (toTyped (P × A) B Rb)
                    (toTyped (P × A) B Sb) hx' hlR]
                  exact ⟨fun h => ⟨hRR, h⟩, fun h => h.2⟩
        · push Not at hlL
          obtain ⟨hne, hnd⟩ := hlL
          have hL' : l ++ [x] ∉ dom (toTyped (P × A) B
              (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
                q = encode (P × A) (p, a)} Rb Sb)) :=
            fun h => hnd (prefix_closed _ (List.prefix_append _ _) hne h)
          have hR' : l ++ [x] ∉ dom (par {p : P × A | p.1 ∈ Z}
              (toTyped (P × A) B Rb) (toTyped (P × A) B Sb)) :=
            fun h => hnd (ih.mpr
              (prefix_closed _ (List.prefix_append _ _) hne h))
          exact iff_of_false hL' hR'
  apply Subtype.ext
  funext l
  refine Part.ext' (hdom l) fun h₁ h₂ => ?_
  show output (toTyped (P × A) B (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
      q = encode (P × A) (p, a)} Rb Sb)) l h₁ =
    output (par {p : P × A | p.1 ∈ Z} (toTyped (P × A) B Rb)
      (toTyped (P × A) B Sb)) l h₂
  obtain ⟨l₀, x, rfl⟩ : ∃ l₀ x, l = l₀ ++ [x] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨l₀, x, rfl⟩
    · exact absurd rfl h₁.1
    · exact ⟨l₀, x, List.concat_eq_append⟩
  have hlL : l₀ = [] ∨ l₀ ∈ dom (toTyped (P × A) B
      (par {q : Uni.{u} | ∃ p ∈ Z, ∃ a : A,
        q = encode (P × A) (p, a)} Rb Sb)) := by
    rcases eq_or_ne l₀ [] with rfl | hne
    · exact Or.inl rfl
    · exact Or.inr (prefix_closed _ (List.prefix_append _ _) hne h₁)
  have hlR : l₀ = [] ∨ l₀ ∈ dom (par {p : P × A | p.1 ∈ Z}
      (toTyped (P × A) B Rb) (toTyped (P × A) B Sb)) := by
    rcases hlL with h | h
    · exact Or.inl h
    · exact Or.inr ((hdom l₀).mp h)
  by_cases hx : x.1 ∈ Z
  · have hx' : x ∈ {p : P × A | p.1 ∈ Z} := hx
    have hTin : historyAt {p : P × A | p.1 ∈ Z} l₀ ++ [x] ∈
        dom (toTyped (P × A) B Rb) :=
      ((mem_dom_par_concat_mem _ (toTyped (P × A) B Rb)
        (toTyped (P × A) B Sb) hx' hlR).mp h₂).1
    rw [output_par_mem _ (toTyped (P × A) B Rb) (toTyped (P × A) B Sb) l₀ x
      hx' h₂ hTin]
    refine output_validate_of_eq_some h₁ ?_
    rw [hrawMem (hparOf hlL) hx]
    exact (Part.some_get (hTin.2 _ (List.prefix_refl _) hTin.1)).symm
  · have hx' : x ∉ {p : P × A | p.1 ∈ Z} := hx
    have hTin : historyAt {p : P × A | p.1 ∈ Z}ᶜ l₀ ++ [x] ∈
        dom (toTyped (P × A) B Sb) :=
      ((mem_dom_par_concat_not_mem _ (toTyped (P × A) B Rb)
        (toTyped (P × A) B Sb) hx' hlR).mp h₂).2
    rw [output_par_not_mem _ (toTyped (P × A) B Rb) (toTyped (P × A) B Sb) l₀
      x hx' h₂ hTin]
    refine output_validate_of_eq_some h₁ ?_
    rw [hrawNotMem (hparOf hlL) hx]
    exact (Part.some_get (hTin.2 _ (List.prefix_refl _) hTin.1)).symm

end Inclusion

end

end System

/-! ## The probabilistic layer

MauRen16 §2.1 composes the *objects*; on Φ the composition is the
independent product of the component laws pushed along the deterministic
composition, and the two laws are the deterministic ones transported —
`prod` is a bifunctor for `fTransform`, symmetric and associative. -/

noncomputable section

open Probability (Distribution)

universe u

/-- **Parallel composition on Φ at a splitting** `c`: the components are
selected independently, and the pair runs as `System.par c`. -/
noncomputable def par (c : Set Uni.{u}) (RL SL : Phi.{u}) : Phi.{u} :=
  Probability.Distribution.fTransform
    (fun p : System.DDS Uni.{u} Uni.{u} × System.DDS Uni.{u} Uni.{u} =>
      System.par c p.1 p.2)
    (Probability.Distribution.prod RL SL)

/-- **Commutativity on Φ**: swapping the components and complementing the
splitting, the deterministic law under the symmetry of the independent
product. -/
theorem par_comm (c : Set Uni.{u}) (RL SL : Phi.{u}) : par c RL SL = par cᶜ SL RL := by
  unfold par
  rw [← Distribution.fTransform_swap_prod RL SL, Distribution.fTransform_fTransform]
  exact congrArg
    (fun f => Distribution.fTransform f (Distribution.prod RL SL))
    (funext fun p => System.par_comm c p.1 p.2)

/-- **Associativity on Φ**: the deterministic law under the associativity of
the independent product. -/
theorem par_assoc (c c' : Set Uni.{u}) (RL SL TL : Phi.{u}) :
    par c RL (par c' SL TL) = par (c ∪ c') (par c RL SL) TL := by
  unfold par
  rw [Distribution.fTransform_prod_right, Distribution.fTransform_prod_left,
    Distribution.fTransform_fTransform, Distribution.fTransform_fTransform,
    ← Distribution.fTransform_assoc_prod, Distribution.fTransform_fTransform]
  exact congrArg
    (fun f => Distribution.fTransform f (Distribution.prod RL (Distribution.prod SL TL)))
    (funext fun p => System.par_assoc c c' p.1 p.2.1 p.2.2)

end

end RandomSystems

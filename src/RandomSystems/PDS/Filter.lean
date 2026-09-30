import RandomSystems.PDS.Function

/-!
# Restricting the domain of a system

A filter keeps the replies on a prefix-closed set of input histories and leaves
every other history undefined. Source: CR18 §3.4.3 (printed p. 62);
Lanzenberger–Maurer, Definition 5 (printed p. 11).

## Main definitions

* `filterDom F s`, `DDS.filterDom`: the restriction of a system to `F`
* `Domain.restrict D F`: the domain `D` restricted to `F`
* `PDS.filterDom`: the restriction of every sample

## Main results

* `filterDom_filterDom`, `DDS.filterDom_ofFunction`: restrictions compose
* `HasDomain.filterDom`: a restriction has the restricted domain
* `replies_filterDom_iff`: on its domain, a restriction replies as the system
-/

namespace SystemAlgebra

open Classical Probability

/-- Retain the replies on `D`, leaving every other history undefined. -/
noncomputable def filterDom {X Y : Type} (D : List X → Prop)
    (s : System X Y) : System X Y :=
  fun h => if D h then s h else Part.none

theorem filterDom_dom {X Y : Type} (D : List X → Prop)
    (s : System X Y) (h : List X) :
    (filterDom D s h).Dom ↔ D h ∧ (s h).Dom := by
  by_cases hd : D h <;> simp [filterDom, hd, Part.not_none_dom]

theorem filterDom_mem_iff {X Y : Type} (D : List X → Prop)
    (s : System X Y) (h : List X) (y : Y) :
    y ∈ filterDom D s h ↔ D h ∧ y ∈ s h := by
  by_cases hd : D h <;> simp [filterDom, hd]

/-- Restriction retains the complete behavior at every admitted prefix. -/
theorem run_filterDom {X Y : Type} (P : Y → Prop) (D : List X → Prop)
    (hD : ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (s : System X Y) {h : List X} (hd : D h) :
    run P (filterDom D s) h = run P s h := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih =>
    rw [run_snoc, run_snoc]
    simp only [filterDom, if_pos hd]
    split_ifs
    · by_cases hn : h = []
      · subst hn; rfl
      · rw [ih (hD (List.prefix_append _ _) hn hd)]
    · rfl

theorem filterDom_filterDom {X Y : Type} (D E : List X → Prop) (s : System X Y) :
    filterDom D (filterDom E s) = filterDom (fun h => D h ∧ E h) s := by
  funext h
  by_cases hd : D h <;> by_cases he : E h <;> simp [filterDom, hd, he]

theorem IsDDS.filterDom {X Y : Type} {s : System X Y} (hs : IsDDS s)
    (D : List X → Prop)
    (hD : ∀ {p h}, p <+: h → p ≠ [] → D h → D p) :
    IsDDS (filterDom D s) := by
  constructor
  · exact fun hd => hs.1 ((filterDom_dom D s []).mp hd).2
  · intro p h hp hn hd
    obtain ⟨hh, hs'⟩ := (filterDom_dom D s h).mp hd
    exact (filterDom_dom D s p).mpr ⟨hD hp hn hh, hs.2 hp hn hs'⟩

namespace DDS

/-- Domain restriction preserves the defining DDS conditions. -/
noncomputable def filterDom {X Y : Type} (D : List X → Prop)
    (hD : ∀ {p h}, p <+: h → p ≠ [] → D h → D p) (s : DDS X Y) : DDS X Y :=
  ⟨SystemAlgebra.filterDom D s.1, s.2.filterDom D hD⟩

theorem filterDom_ofFunction {X Y : Type} (D E : List X → Prop)
    (hD : ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (f : X → Y) :
    filterDom D hD (ofFunction E hE f) =
      ofFunction (fun h => D h ∧ E h)
        ⟨fun h => hE.1 h.2, fun hp hn h => ⟨hD hp hn h.1, hE.2 hp hn h.2⟩⟩ f := by
  apply Subtype.ext
  funext h
  by_cases hd : D h <;> by_cases he : E h <;>
    simp [filterDom, SystemAlgebra.filterDom, ofFunction, hd, he]

end DDS

/-- A domain restricted to the input histories satisfying `F`. -/
def Domain.restrict {X Y : Type} (D : Domain X Y) (F : List X → Prop) : Domain X Y where
  admits h x := F (h.map Prod.fst ++ [x]) ∧ D h x
  bound := D.bound
  length_lt h x hx := D.length_lt h x hx.2

/-- A restriction answers precisely the transcripts it retains. -/
theorem replies_filterDom {X Y : Type} (F : List X → Prop) (s : System X Y) {xs ys} :
    Replies (filterDom F s) xs ys → Replies s xs ys :=
  Replies.mono fun h y hy => ((filterDom_mem_iff F s h y).mp hy).2

/-- On a history in a domain closed under nonempty prefixes, the restriction replies as the
system. -/
theorem replies_filterDom_iff {X Y : Type} {F : List X → Prop}
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) (s : System X Y) {xs ys}
    (hx : xs ≠ [] → F xs) :
    Replies (filterDom F s) xs ys ↔ Replies s xs ys := by
  refine ⟨replies_filterDom F s, fun hr => ⟨hr.1, fun k hk hk' => ?_⟩⟩
  have hne : xs.take (k + 1) ≠ [] := List.ne_nil_of_length_pos (by simp; omega)
  rw [filterDom, if_pos (hF (List.take_prefix _ _) hne (hx fun he => by simp [he] at hne))]
  exact hr.2 k hk hk'

theorem HasDomain.filterDom {X Y : Type} {D : Domain X Y} {s : System X Y}
    (hs : HasDomain D s) (F : List X → Prop) :
    HasDomain (D.restrict F) (SystemAlgebra.filterDom F s) := fun h x hr =>
  (filterDom_dom F s _).trans (and_congr_right fun _ => hs h x (replies_filterDom F s hr))

namespace PDS

/-- Apply the same domain restriction to every sampled DDS. -/
noncomputable def filterDom {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y}
    (F : List X → Prop) (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) (P : PDS X Y D) :
    PDS X Y (D.restrict F) :=
  Distribution.fTransform (fun s => ⟨SystemAlgebra.filterDom F s.1, s.2.1.filterDom F hF,
    s.2.2.filterDom F⟩) P

instance {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y} (F : List X → Prop)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) (P : PDS X Y D)
    [Distribution.IsProbability P] : Distribution.IsProbability (filterDom F hF P) :=
  inferInstanceAs (Distribution.IsProbability (Distribution.fTransform _ P))

end PDS
end SystemAlgebra

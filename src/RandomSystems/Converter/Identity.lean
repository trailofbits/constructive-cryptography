import RandomSystems.DDC.Serial
import RandomSystems.Cumulative.ConnectionObservation

/-!
# The identity on responsive converters

The identity converter forwards each outside query to the inside interface with the
same label and each reply back. Composed on either side of a responsive converter, it
changes nothing. Completed replies determine a responsive converter on their prefixes.
Source: Jost, Definition 2.2.2 (printed pp. 17–18).

## Main results

* `serialM_forwardAll`, `forwardAll_serialM`: unrestricted forwarding is a unit of
  serial connection
* `trim_serialM_id`, `trim_id_serialM`: the identity laws for responsive converters
* `IsResponsiveDDC.prefix_eq_of_replies`, `IsResponsiveDDC.exists_prefix_test`: completed
  replies determine a responsive converter on their prefixes
-/

namespace SystemAlgebra

open Classical

theorem pair_mono {A B C D : Type} {s s' : System A B} {t t' : System C D}
    (hs : ∀ h y, y ∈ s h → y ∈ s' h) (ht : ∀ h y, y ∈ t h → y ∈ t' h) :
    ∀ h y, y ∈ pair s t h → y ∈ pair s' t' h := by
  intro h y hy
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨_ | ⟨⟨⟩⟩, x⟩, rfl⟩
  · simp [pair, parAll] at hy
  · simp only [List.concat_eq_append, pair_left, Part.mem_map_iff] at hy ⊢
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', hs _ _ hy', rfl⟩
  · simp only [List.concat_eq_append, pair_right, Part.mem_map_iff] at hy ⊢
    obtain ⟨y', hy', rfl⟩ := hy
    exact ⟨y', ht _ _ hy', rfl⟩

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- Responsiveness fixes the domain once preceding replies agree; therefore
inclusion of complete converter behavior already gives equality. -/
theorem IsResponsiveDDC.eq_of_replies_imp {b c : ℕ} {α β : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α) (hβ : IsResponsiveDDC c β)
    (he : ∀ xs ys, Replies α xs ys → Replies β xs ys) : α = β := by
  have key : ∀ h, α h = β h ∧ (Admissible α h ↔ Admissible β h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      exact ⟨Part.ext (fun y => ⟨fun hy => False.elim (hα.dds.1
        (Part.dom_iff_mem.mpr ⟨y, hy⟩)), fun hy => False.elim (hβ.dds.1
        (Part.dom_iff_mem.mpr ⟨y, hy⟩))⟩), by simp⟩
    | append_singleton h x ih =>
      have ha : Admissible α (h ++ [x]) ↔ Admissible β (h ++ [x]) := by
        simp only [admissible_snoc, ih.2, ih.1, Admits, replyLabel]
      refine ⟨?_, ha⟩
      have hd : (α (h ++ [x])).Dom ↔ (β (h ++ [x])).Dom := by
        rw [hα.dom_iff, hβ.dom_iff, ha]
      by_cases hp : (α (h ++ [x])).Dom
      · obtain ⟨ys, hr⟩ := (hα.dds.reach_iff (by simp)).mpr hp |>.exists_replies
        have hr' := he _ _ hr
        have hn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
        obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
        exact ((replies_snoc.mp (by simpa only [List.concat_eq_append] using hr)).2).trans
          ((replies_snoc.mp (by simpa only [List.concat_eq_append] using hr')).2).symm
      · exact Part.ext (fun y => ⟨fun hy => False.elim (hp
          (Part.dom_iff_mem.mpr ⟨y, hy⟩)), fun hy => False.elim (hp
          (hd.mpr (Part.dom_iff_mem.mpr ⟨y, hy⟩)))⟩)
  exact funext (fun h => (key h).1)

theorem canon_mem {α : InsideOutsideSystem O J U V X Y} {h y} (hy : y ∈ canon α h) : y ∈ α h := by
  unfold canon at hy
  split_ifs at hy with ha
  · exact hy
  · simp at hy

theorem forwardAll_heterogeneous :
    Forwarder (forwardAll J X Y) (fun
      | ⟨⟨none, j⟩, x⟩ => ⟨⟨some (), j⟩, x⟩
      | ⟨⟨some (), j⟩, y⟩ => ⟨⟨none, j⟩, y⟩) := by
  refine ⟨by simp [SilentAtEmpty, forwardAll], ?_⟩
  rintro h ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
  · exact forwardAll_snoc_outer h j v
  · exact forwardAll_snoc_inner h j v

theorem serialM_forwardAll {α : InsideOutsideSystem O J U V X Y} (hα : SilentAtEmpty α) :
    serialM α (forwardAll J X Y) = α := by
  unfold serialM
  rw [interconnect_forwarder hα forwardAll_heterogeneous (f := id) (g := id), relabel_id]
  constructor
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, rfl⟩
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, rfl⟩

theorem forwardAll_serialM {α : InsideOutsideSystem O J U V X Y} (hα : SilentAtEmpty α) :
    serialM (forwardAll O U V) α = α := by
  unfold serialM
  rw [pair_swap, interconnect_relabel,
    interconnect_forwarder hα forwardAll_heterogeneous (f := id) (g := id), relabel_id]
  constructor
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl rfl
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl rfl

theorem trim_serialM_id {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsResponsiveDDC b α) :
    trim (serialM α (idConverter J X Y)) = α := by
  apply (hα.comp (idConverter_isResponsiveDDC ..)).eq_of_replies_imp hα
  intro xs ys hr
  have hr' := ((replies_trim_iff _ _ _).mp hr).interconnect_mono
    (pair_mono (fun _ _ h => h) (fun _ _ h => canon_mem h))
  change Replies (serialM α (forwardAll J X Y)) xs ys at hr'
  rwa [serialM_forwardAll hα.dds.1] at hr'

theorem trim_id_serialM {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsResponsiveDDC b α) :
    trim (serialM (idConverter O U V) α) = α := by
  apply ((idConverter_isResponsiveDDC ..).comp hα).eq_of_replies_imp hα
  intro xs ys hr
  have hr' := ((replies_trim_iff _ _ _).mp hr).interconnect_mono
    (pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => h))
  change Replies (serialM (forwardAll O U V) α) xs ys at hr'
  rwa [forwardAll_serialM hα.dds.1] at hr'

/-- Equal completed replies identify every function value on their input prefixes. -/
theorem IsResponsiveDDC.prefix_eq_of_replies {b c : ℕ} {α β : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α) (hβ : IsResponsiveDDC c β) {xs ys}
    (hr : Replies α xs ys) (hr' : Replies β xs ys) :
    ∀ p, p <+: xs → α p = β p := by
  intro p hp
  rcases List.eq_nil_or_concat p with rfl | ⟨p, x, rfl⟩
  · exact Part.ext (fun y => ⟨fun hy => False.elim (hα.dds.1 hy.1),
      fun hy => False.elim (hβ.dds.1 hy.1)⟩)
  rw [List.concat_eq_append] at hp ⊢
  have hi : p.length < xs.length := by have := hp.length_le; simp at this; omega
  have hj : p.length < ys.length := by rw [hr.length]; exact hi
  have he : xs.take (p.length + 1) = p ++ [x] := by
    obtain ⟨e, rfl⟩ := hp
    simpa using (List.take_left (l₁ := p ++ [x]) (l₂ := e))
  exact (he ▸ hr.2 p.length hi hj).trans (he ▸ hr'.2 p.length hi hj).symm

/-- A finite input sequence is determined by one finite completed converter
history. If a query is illegal, agreement up to that query also determines all
later undefined prefixes, by prefix closure and responsiveness. -/
theorem IsResponsiveDDC.exists_prefix_test {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α) (H : List (Σ l, twoFam U Y l)) :
    ∃ xs ys, xs <+: H ∧ Replies α xs ys ∧
      ∀ {c : ℕ} {β : InsideOutsideSystem O J U V X Y}, IsResponsiveDDC c β → Replies β xs ys →
        ∀ p, p <+: H → α p = β p := by
  induction H using List.reverseRecOn with
  | nil =>
    exact ⟨[], [], List.prefix_refl [], replies_nil α,
      fun hβ hr p hp => hα.prefix_eq_of_replies hβ (replies_nil α) hr p hp⟩
  | append_singleton H x ih =>
    by_cases hd : (α (H ++ [x])).Dom
    · obtain ⟨ys, hr⟩ := ((hα.dds.reach_iff (by simp)).mpr hd).exists_replies
      exact ⟨H ++ [x], ys, List.prefix_refl _, hr,
        fun hβ hr' => hα.prefix_eq_of_replies hβ hr hr'⟩
    · obtain ⟨xs, ys, hx, hr, he⟩ := ih
      refine ⟨xs, ys, hx.trans ⟨[x], rfl⟩, hr, fun {c} {β} hβ hr' p hp => ?_⟩
      have hn : ¬ (β (H ++ [x])).Dom := by
        intro hb
        apply hd
        apply hα.responsive _ ?_ (by simp)
        intro h' z e hfull
        have hlen : h'.length ≤ H.length := by
          have := congrArg List.length hfull
          simp at this; omega
        have hp' : h' <+: H := List.prefix_of_prefix_length_le
          ⟨z :: e, hfull.symm⟩ ⟨[x], rfl⟩ hlen
        have hs := (hβ.admissible hb) h' z e hfull
        have hl : replyLabel α h' = replyLabel β h' := by
          unfold replyLabel
          rw [he hβ hr' h' hp']
        simpa only [Admits, hl, he hβ hr' h' hp'] using hs
      have hlast : α (H ++ [x]) = β (H ++ [x]) :=
        Part.ext (fun y => ⟨fun hy => False.elim (hd hy.1), fun hy => False.elim (hn hy.1)⟩)
      by_cases hl : p.length ≤ H.length
      · exact he hβ hr' p (List.prefix_of_prefix_length_le hp ⟨[x], rfl⟩ hl)
      · have hpLen : p.length = (H ++ [x]).length := by have := hp.length_le; simp at *; omega
        have hpEq := hp.eq_of_length hpLen
        simpa only [hpEq] using hlast

end SystemAlgebra

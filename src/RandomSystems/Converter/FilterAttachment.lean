import RandomSystems.Converter.PartialConverter
import RandomSystems.Converter.ResourceAttachment

/-!
# Filters

A filter forwards the admitted queries and their replies; attaching it restricts the
domain of a system. Source: CR18, §3.4.3 (printed p. 62).

## Main results

* `Induces.outsideInputs_resource`: the converter receives exactly the outside queries
* `trim_apply_filter`, `DDC.filter_attach`: attaching a filter is domain restriction
* `apply_filterDom_outside`: restricting a converter's outside domain restricts its attachment
-/

namespace SystemAlgebra

open Classical

variable {O J : Type} {U V : O → Type} {X Y : J → Type}
    {α : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y}

/-- Internal exchanges append no outside query to the converter's history. -/
theorem Exchange.outsideInputs_resource {G out H}
    (ex : Exchange (pair α R) resourceRoute G out H) :
    outsideInputs (restrict none H) = outsideInputs (restrict none G) := by
  induction ex with
  | silent => rfl
  | out => rfl
  | feed G y x out H _ hr _ ih =>
    rw [ih]
    rcases y with ⟨_ | ⟨⟩, y⟩
    · rcases y with ⟨⟨_ | ⟨⟩, i⟩, y⟩
      · cases hr
      · cases hr
        simp
    · rcases y with ⟨j, y⟩
      cases hr
      simp [outsideInputs, List.map_append, splitIn]

/-- The converter sees exactly the exposed input history at its outside ports. -/
theorem Induces.outsideInputs_resource {us out H}
    (hi : Induces (pair α R) resourceRoute resourceInput us out H) :
    outsideInputs (restrict none H) = us := by
  induction hi with
  | nil => rfl
  | snoc us u out H out' H' _ ex ih =>
    rw [ex.outsideInputs_resource]
    simpa [resourceInput, outsideInputs, List.map_append, splitIn] using
      congrArg (fun h => h ++ [u]) ih

/-- A successful filtered call must lie in the retained outside domain. -/
theorem apply_filterDom_dom
    (D : List (Σ o, U o) → Prop) {us : List (Σ o, U o)}
    (hd : (apply (filterDom (fun h => D (outsideInputs h)) α) R us).Dom) : D us := by
  rw [apply_eq] at hd
  obtain ⟨H, hi⟩ := mem_interconnect.mp (Part.get_mem hd)
  have hs := hi.outsideInputs_resource
  cases hi with
  | snoc _ _ _ _ _ _ _ ex =>
    have key {G out H} (ex : Exchange
        (pair (filterDom (fun h => D (outsideInputs h)) α) R) resourceRoute G out H) :
        ∀ v, out = some v → D (outsideInputs (restrict none H)) := by
      induction ex with
      | silent => simp
      | out G y v hy hr =>
        intro _ _
        rcases y with ⟨_ | ⟨⟩, y⟩
        · rcases y with ⟨⟨_ | ⟨⟩, i⟩, y⟩
          · rcases List.eq_nil_or_concat G with rfl | ⟨G, z, rfl⟩
            · simp [pair] at hy
            · rw [List.concat_eq_append, pair] at hy
              rcases z with ⟨_ | ⟨⟩, z⟩
              · rw [parAll_snoc] at hy
                obtain ⟨_, hy, _⟩ := Part.mem_map_iff _ |>.mp hy
                simpa using ((filterDom_mem_iff
                  (fun h => D (outsideInputs h)) α _ _).mp hy).1
              · rw [parAll_snoc] at hy
                obtain ⟨_, _, he⟩ := Part.mem_map_iff _ |>.mp hy
                cases he
          · cases hr
        · cases hr
      | feed _ _ _ _ _ _ _ _ ih => exact ih
    exact hs ▸ key ex _ rfl

/-- Along an induced history whose exposed queries lie in a domain closed under nonempty
prefixes, the converter restricted to that outside domain acts as the converter. -/
theorem Induces.pair_filterDom_outside (F : List (Σ o, U o) → Prop)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) {α' : InsideOutsideSystem O J U V X Y}
    {us o H} (hi : Induces (pair α' R) resourceRoute resourceInput us o H) (hu : F us) :
    ∀ p, p <+: H → pair (filterDom (fun h => outsideInputs h = [] ∨ F (outsideInputs h)) α) R p =
      pair α R p := by
  intro p hp
  have hD : ∀ G, G <+: H → outsideInputs (restrict none G) = [] ∨
      F (outsideInputs (restrict none G)) := by
    intro G hG
    have hpre : outsideInputs (restrict none G) <+: us := by
      rw [← hi.outsideInputs_resource]
      exact restrict_prefix none ((restrict_prefix none hG).map splitIn)
    by_cases he : outsideInputs (restrict none G) = []
    · exact Or.inl he
    · exact Or.inr (hF hpre he hu)
  rcases List.eq_nil_or_concat p with rfl | ⟨G, z, rfl⟩
  · simp [pair]
  rw [List.concat_eq_append] at hp ⊢
  rcases z with ⟨_ | ⟨⟩, z⟩
  · rw [pair_left, pair_left, filterDom, if_pos]
    simpa only [restrict_none_snoc_left] using hD _ hp
  · rw [pair_right, pair_right]

/-- **Restricting a converter's outside domain restricts its attachment**, for a domain closed
under nonempty prefixes. -/
theorem apply_filterDom_outside (F : List (Σ o, U o) → Prop)
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p) :
    apply (filterDom (fun h => outsideInputs h = [] ∨ F (outsideInputs h)) α) R =
      filterDom F (apply α R) := by
  funext us
  by_cases hu : F us
  · rw [filterDom, if_pos hu, apply_eq, apply_eq]
    ext b
    rw [mem_interconnect, mem_interconnect]
    constructor
    · rintro ⟨H, hi⟩
      exact ⟨H, hi.congr_of_prefix_eq (hi.pair_filterDom_outside F hF hu)⟩
    · rintro ⟨H, hi⟩
      exact ⟨H, hi.congr_of_prefix_eq fun p hp =>
        (hi.pair_filterDom_outside (α := α) F hF hu p hp).symm⟩
  · rw [filterDom, if_neg hu]
    refine Part.eq_none_iff'.mpr fun hd => ?_
    rcases apply_filterDom_dom (fun us => us = [] ∨ F us) hd with rfl | h
    · rw [apply_eq, interconnect_eq_none Induces.nil] at hd
      exact hd
    · exact hu h

/-- Forwarding through a filter is exactly domain restriction, including
undefined behavior. The proof reuses identity attachment on admitted prefixes. -/
theorem trim_apply_filter (D : List (Σ j, X j) → Prop)
    (hD : ∀ {p h}, p <+: h → D h → D p)
    {R : InterfaceSystem J X Y} (hR : IsDDS R) (hr : RepliesAtQueriedInterface R) :
    trim (apply (DDC.filter (Y := Y) D hD).1 R) = filterDom D R := by
  apply IsDDS.eq_of_replies_iff
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
    (hR.filterDom D (fun hp _ => hD hp))
  intro xs ys
  rw [replies_trim_iff]
  constructor
  · intro ht
    have hm : Replies (apply (idConverter J X Y) R) xs ys := by
      rw [apply_eq] at ht ⊢
      dsimp only [DDC.filter] at ht
      exact ht.interconnect_mono (pair_mono
        (fun h y hy => ((filterDom_mem_iff (fun h => D (outsideInputs h))
          (idConverter J X Y) h y).mp hy).2) (fun _ _ hy => hy))
    have hbase : Replies R xs ys := by
      rw [← trim_apply_id hR hr]
      exact (replies_trim_iff _ _ _).mpr hm
    refine ⟨hbase.length, fun k hk hk' => ?_⟩
    have hd : D (xs.take (k + 1)) :=
      apply_filterDom_dom D (Part.eq_some_iff.mp (ht.2 k hk hk')).1
    rw [filterDom, if_pos hd]
    exact hbase.2 k hk hk'
  · intro ht
    have hbase : Replies R xs ys :=
      ht.mono (fun h y hy => ((filterDom_mem_iff D R h y).mp hy).2)
    have hid := replies_apply_id hr hbase
    refine ⟨ht.length, fun k hk hk' => ?_⟩
    have hd := ((filterDom_dom D R _).mp (Part.eq_some_iff.mp (ht.2 k hk hk')).1).1
    have hy := Part.eq_some_iff.mp (hid.2 k hk hk')
    rw [apply_eq] at hy ⊢
    obtain ⟨H, hi⟩ := mem_interconnect.mp hy
    apply Part.eq_some_iff.mpr
    apply mem_interconnect.mpr
    refine ⟨H, hi.congr_of_prefix_eq ?_⟩
    intro p hp
    have hdp : D (outsideInputs (restrict none p)) := by
      apply hD _ hd
      rw [← hi.outsideInputs_resource]
      obtain ⟨e, rfl⟩ := hp
      exact ⟨outsideInputs (restrict none e), by
        rw [restrict_append, outsideInputs_append]⟩
    rcases List.eq_nil_or_concat p with rfl | ⟨p, z, rfl⟩
    · rfl
    · rw [List.concat_eq_append] at hdp ⊢
      rcases z with ⟨_ | ⟨⟩, z⟩
      · simp only [pair_left] at *
        simp only [DDC.filter, filterDom, restrict_none_snoc_left] at hdp ⊢
        rw [if_pos hdp]
      · rw [pair_right, pair_right]

namespace DDC

/-- The DDS-level action of the forwarding filter is the same restriction. -/
theorem filter_attach (D : List (Σ j, X j) → Prop)
    (hD : ∀ {p h}, p <+: h → D h → D p)
    (R : DDS (Σ j, X j) (Σ j, Y j)) (hR : RepliesAtQueriedInterface R.1) :
    attach (filter D hD) R = DDS.filterDom D (fun hp _ => hD hp) R := by
  apply Subtype.ext
  exact trim_apply_filter D hD R.2 hR

end DDC

end SystemAlgebra

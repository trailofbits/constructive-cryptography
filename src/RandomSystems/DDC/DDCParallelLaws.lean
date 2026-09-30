import RandomSystems.Converter.ResourceCanon
import RandomSystems.Converter.ConverterDomain
import RandomSystems.DDC.Tensor

/-!
# Parallel converter laws

Equations between parallel and serial compositions of responsive converters.
A responsive canonical converter is determined by any history function
containing its completed histories, so each equation is first proved on the
unrestricted wiring.

## Main results

* `IsResponsiveDDC.eq_of_common_replies`: responsive canonical converters
  contained in a common history function are equal
* `serialM_tensorRaw`, `trim_serialM_tensorL`: interchange of serial and
  parallel composition
* `tensorL_id`: the parallel composition of identity converters is the
  identity converter
-/

namespace SystemAlgebra

open Classical

theorem trim_mem {A B : Type} {s : System A B} {h y} (hy : y ∈ trim s h) : y ∈ s h := by
  unfold trim at hy
  split_ifs at hy
  · exact hy
  · exact (Part.not_none_dom hy.1).elim

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- A common extension uniquely determines a responsive canonical converter. -/
theorem IsResponsiveDDC.eq_of_common_replies {ba bb : ℕ}
    {α β c : InsideOutsideSystem O J U V X Y} (ha : IsResponsiveDDC ba α) (hb : IsResponsiveDDC bb β)
    (hα : ∀ xs ys, Replies α xs ys → Replies c xs ys)
    (hβ : ∀ xs ys, Replies β xs ys → Replies c xs ys) : α = β := by
  have value {s : InsideOutsideSystem O J U V X Y} (hs : IsDDS s)
      (hc : ∀ xs ys, Replies s xs ys → Replies c xs ys)
      (h : List (Σ l, twoFam U Y l)) (hd : (s h).Dom) : s h = c h := by
    have hn : h ≠ [] := fun he => hs.1 (he ▸ hd)
    obtain ⟨ys, hr⟩ := (hs.reach_iff hn).mpr hd |>.exists_replies
    obtain ⟨p, x, rfl⟩ := List.eq_nil_or_concat h |>.resolve_left hn
    have hyn : ys ≠ [] := by intro he; have hl := hr.length; simp [he] at hl
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hyn
    simp only [List.concat_eq_append] at hr ⊢
    exact (replies_snoc.mp hr).2.trans (replies_snoc.mp (hc _ _ hr)).2.symm
  have key : ∀ h, α h = β h ∧ (Admissible α h ↔ Admissible β h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      exact ⟨Part.ext (fun y => ⟨fun hy => (ha.dds.1 hy.1).elim,
        fun hy => (hb.dds.1 hy.1).elim⟩), by simp⟩
    | append_singleton h x ih =>
      have hp : Admissible α (h ++ [x]) ↔ Admissible β (h ++ [x]) := by
        simp only [admissible_snoc, ih.2, ih.1, Admits, replyLabel]
      have hd : (α (h ++ [x])).Dom ↔ (β (h ++ [x])).Dom := by
        rw [ha.dom_iff, hb.dom_iff, hp]
      refine ⟨?_, hp⟩
      by_cases hx : (α (h ++ [x])).Dom
      · exact (value ha.dds hα _ hx).trans (value hb.dds hβ _ (hd.mp hx)).symm
      · exact Part.ext (fun y => ⟨fun hy => (hx hy.1).elim, fun hy => (hx (hd.mpr hy.1)).elim⟩)
  exact funext (fun h => (key h).1)

section Interchange

variable {O' M M' J' : Type} {U V : O ⊕ O' → Type}
    {Xm Ym : M ⊕ M' → Type} {X Y : J ⊕ J' → Type}
    {a : InsideOutsideSystem O M (U ∘ Sum.inl) (V ∘ Sum.inl) (Xm ∘ Sum.inl) (Ym ∘ Sum.inl)}
    {b : InsideOutsideSystem O' M' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xm ∘ Sum.inr) (Ym ∘ Sum.inr)}
    {c : InsideOutsideSystem M J (Xm ∘ Sum.inl) (Ym ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {d : InsideOutsideSystem M' J' (Xm ∘ Sum.inr) (Ym ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    {ba bb bc bd : ℕ}

/-- Both orders connect the same four constituents. -/
theorem serialM_tensorRaw (ha : IsDDC ba a) (hb : IsDDC bb b) :
    serialM (tensorRaw a b) (tensorRaw c d) =
      tensorRaw (serialM a c) (serialM b d) := by
  simp only [serialM, tensorRaw, pair_relabel, interconnect_relabel]
  rw [pair_interconnect_left (ha.converges_serial c),
    pair_interconnect_right (pair a c) (hb.converges_serial d),
    interconnect_interconnect, relabel_interconnect,
    pair_middle a b c d, interconnect_relabel]
  congr 1
  · funext z
    rcases z with ⟨(_ | ⟨⟩), ⟨(_ | ⟨⟩), ⟨⟨(_ | ⟨⟩), i⟩, z⟩⟩⟩ <;> rfl
  · funext z
    rcases z with ⟨⟨(_ | ⟨⟩), (i | j)⟩, z⟩ <;> rfl

/-- Serial and parallel composition satisfy interchange on complete converter behavior. -/
theorem trim_serialM_tensorL (ha : IsResponsiveDDC ba a) (hb : IsResponsiveDDC bb b)
    (hc : IsResponsiveDDC bc c) (hd : IsResponsiveDDC bd d) :
    trim (serialM (tensorL a b) (tensorL c d)) =
      tensorL (trim (serialM a c)) (trim (serialM b d)) := by
  apply ((ha.tensorL hb).comp (hc.tensorL hd)).eq_of_common_replies
    ((ha.comp hc).tensorL (hb.comp hd))
    (c := tensorRaw (serialM a c) (serialM b d))
  · intro xs ys hr
    have hr' := ((replies_trim_iff _ _ _).mp hr).interconnect_mono
      (pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => canon_mem h))
    change Replies (serialM (tensorRaw a b) (tensorRaw c d)) xs ys at hr'
    rwa [serialM_tensorRaw ha.isDDC hb.isDDC] at hr'
  · intro xs ys hr
    apply hr.mono
    intro h y hy
    have hy' := canon_mem hy
    obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp hy'
    refine Part.mem_map_iff _ |>.mpr ⟨v, ?_, he⟩
    exact pair_mono (fun _ _ h => trim_mem h) (fun _ _ h => trim_mem h) _ _ hv

end Interchange

section Identity

variable {J' : Type} {X Y : J ⊕ J' → Type}

theorem tensorRaw_forwardAll :
    tensorRaw (U := X) (V := Y) (Xi := X) (Yi := Y)
      (forwardAll J (X ∘ Sum.inl) (Y ∘ Sum.inl))
      (forwardAll J' (X ∘ Sum.inr) (Y ∘ Sum.inr)) = forwardAll (J ⊕ J') X Y := by
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨⟨(_ | ⟨⟨⟩⟩), (i | j)⟩, x⟩, rfl⟩
  · simp [tensorRaw, relabel, pair, parAll, forwardAll]
  all_goals
    simp only [List.concat_eq_append, tensorRaw, relabel, List.map_append, List.map_singleton,
      tIn, pair_left, pair_right, forwardAll_snoc_outer, forwardAll_snoc_inner,
      Part.map_some, tOut]

/-- Parallel identity converters forward the combined interface family unchanged. -/
theorem tensorL_id :
    tensorL (U := X) (V := Y) (Xi := X) (Yi := Y)
      (idConverter J (X ∘ Sum.inl) (Y ∘ Sum.inl))
      (idConverter J' (X ∘ Sum.inr) (Y ∘ Sum.inr)) = idConverter (J ⊕ J') X Y := by
  apply ((idConverter_isResponsiveDDC (J := J) (X := X ∘ Sum.inl) (Y := Y ∘ Sum.inl)).tensorL
    (idConverter_isResponsiveDDC (J := J') (X := X ∘ Sum.inr) (Y := Y ∘ Sum.inr))).eq_of_common_replies
    (idConverter_isResponsiveDDC ..) (c := forwardAll (J ⊕ J') X Y)
  · intro xs ys hr
    rw [← tensorRaw_forwardAll]
    apply hr.mono
    intro h y hy
    obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp (canon_mem hy)
    exact (Part.mem_map_iff _).mpr ⟨v,
      pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => canon_mem h) _ _ hv, he⟩
  · intro xs ys hr
    exact hr.mono (fun _ _ h => canon_mem h)

end Identity

end SystemAlgebra

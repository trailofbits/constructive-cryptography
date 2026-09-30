import RandomSystems.DDC.DDCParallelLaws

/-!
# Relabeling converters

Message maps on the outside or the inside interfaces of a converter, and the
renaming converter that forwards between two outside vocabularies.

## Main definitions

* `outsideMap f`, `insideMap f`: apply a message map on one side
* `renameConverter f g`: the forwarding converter for a change of the outside
  vocabulary

## Main results

* `IsResponsiveDDC.relabelOutside`: relabeling the outside preserves
  converters
* `renameConverter_isResponsiveDDC`, `renameConverter_mapsDomain`: the renaming
  converter is a converter and transports the domain
* `trim_renameConverter_serialM`: composing with a renaming converter
  relabels
* `renameConverter_id`, `renameConverter_comp`: functoriality
* `ResponsiveConverter.ofConverter_mass`: the behavior of a converter read as a
  probabilistic converter
-/

namespace SystemAlgebra

open Classical

variable {O O' J : Type} {U V : O → Type} {U' V' : O' → Type} {X Y : J → Type}

/-- Apply a message map on the outside; retain every inside message. -/
def outsideMap (f : (Σ o, U o) → (Σ o, U' o)) :
    (Σ l, twoFam U Y l) → (Σ l, twoFam U' Y l)
  | ⟨⟨none, o⟩, u⟩ => ⟨⟨none, (f ⟨o, u⟩).1⟩, (f ⟨o, u⟩).2⟩
  | ⟨⟨some (), j⟩, y⟩ => ⟨⟨some (), j⟩, y⟩

theorem outsideMap_fst (e : O → O') (f : (Σ o, U o) → (Σ o, U' o))
    (hf : ∀ u, (f u).1 = e u.1) (z : Σ l, twoFam U Y l) :
    (outsideMap f z).1 = twoMap e id z.1 := by
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩
  · exact congrArg (Sigma.mk none) (hf ⟨i, z⟩)
  · rfl

theorem isInside_outsideMap (f : (Σ o, V o) → (Σ o, V' o)) (z : Σ l, twoFam V X l) :
    IsInside (outsideMap f z) ↔ IsInside z := by
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl

variable (e : O' ≃ O) (f : (Σ o, U' o) → (Σ o, U o))
    (g : (Σ o, V o) → (Σ o, V' o))
    (hf : ∀ u, (f u).1 = e u.1) (hg : ∀ v, (g v).1 = e.symm v.1)
    (α : InsideOutsideSystem O J U V X Y)

include hg in
theorem replyLabel_outsideMap (h : List (Σ l, twoFam U' Y l)) :
    replyLabel (relabel α (outsideMap f) (outsideMap g)) h =
      (replyLabel α (h.map (outsideMap f))).map (twoMap e.symm id) := by
  unfold replyLabel
  by_cases hd : (α (h.map (outsideMap f))).Dom
  · have hd' : (relabel α (outsideMap f) (outsideMap g) h).Dom := by
      simpa only [relabel, Part.map_Dom] using hd
    rw [dif_pos hd, dif_pos hd']
    exact congrArg some (outsideMap_fst e.symm g hg _)
  · have hd' : ¬ (relabel α (outsideMap f) (outsideMap g) h).Dom := by
      simpa only [relabel, Part.map_Dom] using hd
    rw [dif_neg hd, dif_neg hd']
    rfl

include hf hg in
theorem admits_outsideMap (h : List (Σ l, twoFam U' Y l)) (z : Σ l, twoFam U' Y l) :
    Admits (relabel α (outsideMap f) (outsideMap g)) h z ↔
      Admits α (h.map (outsideMap f)) (outsideMap f z) := by
  unfold Admits
  rw [replyLabel_outsideMap e f g hg α, outsideMap_fst e f hf]
  rcases replyLabel α (h.map (outsideMap f)) with _ | ⟨(_ | ⟨⟨⟩⟩), i⟩ <;>
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), j⟩, z⟩ <;> simp [admitAfter, twoMap]

include hf hg in
theorem admissible_outsideMap (h : List (Σ l, twoFam U' Y l)) :
    Admissible (relabel α (outsideMap f) (outsideMap g)) h ↔
      Admissible α (h.map (outsideMap f)) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [admissible_snoc, List.map_append, List.map_singleton, admissible_snoc,
      ih, admits_outsideMap e f g hf hg α]
    simp only [relabel, Part.map_Dom]
    have hn : h.map (outsideMap f) ≠ [] ↔ h ≠ [] := not_congr List.map_eq_nil_iff
    exact and_congr Iff.rfl (and_congr (imp_congr hn.symm Iff.rfl) Iff.rfl)

theorem insideRun_outsideMap (h : List (Σ l, twoFam U' Y l)) :
    insideRun (relabel α (outsideMap f) (outsideMap g)) h =
      insideRun α (h.map (outsideMap f)) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    simp only [insideRun, run_snoc, List.map_append, List.map_singleton] at ih ⊢
    rw [ih]
    congr 1
    simp only [relabel, Part.mem_map_iff, List.map_append, List.map_singleton]
    exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_outsideMap g y).mp hi⟩,
      fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_outsideMap g y).mpr hi⟩⟩

include hf in
theorem lastOuter_outsideMap (h : List (Σ l, twoFam U' Y l)) :
    lastOuter (h.map (outsideMap f)) = (lastOuter h).map e := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [List.map_append, List.map_singleton, lastOuter_snoc, lastOuter_snoc, ih]
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩
    · simp only [outsideMap, outerOf, Option.some_or, Option.map_some, hf]
    · rfl

include hf hg in
theorem IsResponsiveDDC.relabelOutside {b : ℕ} (hα : IsResponsiveDDC b α) :
    IsResponsiveDDC b (relabel α (outsideMap f) (outsideMap g)) := by
  refine ⟨⟨?_, ?_⟩, fun h z hd => ?_, fun h hd => ?_, fun h ha hn => ?_, fun h y o hy hl => ?_⟩
  · simpa only [SilentAtEmpty, relabel, List.map_nil, Part.map_Dom] using hα.dds.1
  · intro p h hp hn hd
    exact hα.dds.2 (hp.map (outsideMap f)) (fun he => hn (List.map_eq_nil_iff.mp he)) hd
  · rw [admits_outsideMap e f g hf hg α]
    exact hα.admits _ _ (by simpa only [relabel, List.map_append, List.map_singleton, Part.map_Dom] using hd)
  · rw [insideRun_outsideMap f g α]
    exact hα.bound _ hd
  · exact hα.responsive _ ((admissible_outsideMap e f g hf hg α h).mp ha)
      (fun he => hn (List.map_eq_nil_iff.mp he))
  · obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp hy
    subst y
    rcases v with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, v⟩
    · have he : e.symm i = o := by
        simpa only [outsideMap, Sigma.mk.inj_iff, heq_eq_eq, true_and, hg] using hl
      have hr := hα.replies _ _ i hv rfl
      rw [lastOuter_outsideMap e f hf] at hr
      obtain ⟨o', ho', hio⟩ := Option.map_eq_some_iff.mp hr
      rw [ho']
      rw [← hio, e.symm_apply_apply] at he
      exact congrArg some he
    · cases hl

include hf hg in
theorem canon_outsideMap :
    canon (relabel α (outsideMap f) (outsideMap g)) =
      relabel (canon α) (outsideMap f) (outsideMap g) := by
  funext h
  simp only [canon, admissible_outsideMap e f g hf hg α, relabel]
  split_ifs
  · rfl
  · exact (Part.map_none _).symm

/-- The forwarding converter for a change of the outside vocabulary. -/
noncomputable def renameConverter : InsideOutsideSystem O' O U' V' U V :=
  relabel (idConverter O U V) (outsideMap f) (outsideMap g)

include hf hg in
theorem renameConverter_isResponsiveDDC : IsResponsiveDDC 1 (renameConverter f g) :=
  IsResponsiveDDC.relabelOutside e f g hf hg _ (idConverter_isResponsiveDDC ..)

theorem serialM_relabel_forwardAll (hα : SilentAtEmpty α) :
    serialM (relabel (forwardAll O U V) (outsideMap f) (outsideMap g)) α =
      relabel α (outsideMap f) (outsideMap g) := by
  unfold serialM
  rw [pair_relabel_left, interconnect_relabel, pair_swap, interconnect_relabel]
  apply interconnect_forwarder hα forwardAll_heterogeneous
  constructor
  · rintro ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, x⟩
    · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl rfl
  · rintro ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, y⟩
    · exact Or.inr ⟨_, rfl, rfl⟩
    · exact Or.inl rfl

include hf hg in
/-- A renaming converter is precisely the relabeled history function. -/
theorem trim_renameConverter_serialM {b : ℕ} (hα : IsResponsiveDDC b α) :
    trim (serialM (renameConverter f g) α) = relabel α (outsideMap f) (outsideMap g) := by
  apply ((renameConverter_isResponsiveDDC e f g hf hg).comp hα).eq_of_replies_imp
    (hα.relabelOutside e f g hf hg α)
  intro xs ys hr
  have hm : ∀ h y, y ∈ renameConverter f g h →
      y ∈ relabel (forwardAll O U V) (outsideMap f) (outsideMap g) h := by
    intro h y hy
    obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp hy
    exact (Part.mem_map_iff _).mpr ⟨v, canon_mem hv, he⟩
  have hr' := ((replies_trim_iff _ _ _).mp hr).interconnect_mono
    (pair_mono hm (fun _ _ h => h))
  change Replies (serialM (relabel (forwardAll O U V) (outsideMap f) (outsideMap g)) α) xs ys at hr'
  rwa [serialM_relabel_forwardAll f g α hα.dds.1] at hr'

theorem apply_relabel_forwardAll {R : InterfaceSystem O U V} (hR : SilentAtEmpty R) :
    apply (relabel (forwardAll O U V) (outsideMap f) (outsideMap g)) R = relabel R f g := by
  rw [apply_eq, pair_relabel_left, interconnect_relabel, pair_swap, interconnect_relabel]
  apply interconnect_forwarder hR forwardAll_heterogeneous
  constructor
  · rintro ⟨i, x⟩
    exact Or.inr ⟨_, rfl, rfl⟩
  · rintro ⟨i, y⟩
    exact Or.inr ⟨_, rfl, rfl⟩

include hf hg in
theorem trim_apply_renameConverter {R : InterfaceSystem O U V} (hR : IsDDS R) (hr : RepliesAtQueriedInterface R) :
    trim (apply (renameConverter f g) R) = relabel R f g := by
  have he := canon_outsideMap e f g hf hg (forwardAll O U V)
  change canon (relabel (forwardAll O U V) (outsideMap f) (outsideMap g)) = renameConverter f g at he
  rw [← he, trim_apply_canon (he.symm ▸ renameConverter_isResponsiveDDC e f g hf hg).isDDC hr,
    apply_relabel_forwardAll f g hR.1, trim_relabel, hR.trim_eq]

include hf hg in
/-- Renaming transports the exact admitted domain; it does not change its replies. -/
theorem renameConverter_mapsDomain (E : List (Σ o, U o) → Prop)
    (F : List (Σ o, U' o) → Prop) (hd : ∀ h, E (h.map f) ↔ F h) :
    MapsDomain E F (renameConverter f g) := by
  intro R hR hr hE
  rw [trim_apply_renameConverter e f g hf hg hR hr]
  constructor
  · apply hr.relabel f g
    intro x y hy
    rw [hg, hy, hf, e.symm_apply_apply]
  · intro h
    exact (Part.map_Dom _ _).to_iff.trans ((hE _).trans (hd h))

theorem outsideMap_id :
    outsideMap (Y := Y) (id : (Σ o, U o) → (Σ o, U o)) = id := by
  funext z
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl

theorem outsideMap_comp {O'' : Type} {U'' : O'' → Type}
    (f' : (Σ o, U'' o) → (Σ o, U' o)) :
    outsideMap (Y := Y) f ∘ outsideMap f' = outsideMap (f ∘ f') := by
  funext z
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl

theorem renameConverter_id :
    renameConverter (id : (Σ o, U o) → (Σ o, U o))
      (id : (Σ o, V o) → (Σ o, V o)) = idConverter O U V := by
  rw [renameConverter, outsideMap_id, outsideMap_id, relabel_id]

include hf hg in
theorem renameConverter_comp {O'' : Type} {U'' V'' : O'' → Type}
    (e' : O'' ≃ O') (f' : (Σ o, U'' o) → (Σ o, U' o)) (g' : (Σ o, V' o) → (Σ o, V'' o))
    (hf' : ∀ u, (f' u).1 = e' u.1) (hg' : ∀ v, (g' v).1 = e'.symm v.1) :
    trim (serialM (renameConverter f' g') (renameConverter f g)) =
      renameConverter (f ∘ f') (g' ∘ g) := by
  rw [trim_renameConverter_serialM e' f' g' hf' hg' _ (renameConverter_isResponsiveDDC e f g hf hg)]
  simp only [renameConverter, relabel_relabel, outsideMap_comp]

section Inside

variable {J' : Type} {X' Y' : J' → Type}

/-- Apply a message map on the inside; retain every outside message. -/
def insideMap (k : (Σ j, Y j) → (Σ j, Y' j)) :
    (Σ l, twoFam U Y l) → (Σ l, twoFam U Y' l)
  | ⟨⟨none, o⟩, u⟩ => ⟨⟨none, o⟩, u⟩
  | ⟨⟨some (), j⟩, y⟩ => ⟨⟨some (), (k ⟨j, y⟩).1⟩, (k ⟨j, y⟩).2⟩

theorem serialM_forwardAll_relabel (k : (Σ j, X j) → (Σ j, X' j))
    (l : (Σ j, Y' j) → (Σ j, Y j)) (hα : SilentAtEmpty α) :
    serialM α (relabel (forwardAll J' X' Y') (outsideMap k) (outsideMap l)) =
      relabel α (insideMap l) (insideMap k) := by
  unfold serialM
  rw [pair_relabel_right, interconnect_relabel]
  apply interconnect_forwarder hα forwardAll_heterogeneous
  constructor
  · rintro ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, x⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, rfl⟩
  · rintro ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, y⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl, rfl⟩

end Inside

end SystemAlgebra

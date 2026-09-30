import RandomSystems.DDC.DDCRelabel
import RandomSystems.DDC.CanonWiring

/-!
# Relabeling DDCs from `E` to `F`

Relabeling the outside of a DDC by a label-preserving bijection gives a DDC, and a DDC from
`E` to `F` becomes a DDC from `E` to the transported outside domain. Composing a DDC with a
renaming converter relabels it.

## Main results

* `IsDDC.relabelOutside`, `IsDDCFrom.relabelOutside`: relabeling the outside preserves DDCs,
  and DDCs from `E` to `F`
* `IsDDC.trim_renameConverter_serialM`, `IsDDC.replies_serialM_renameConverter`: composing
  with a renaming converter relabels
* `admitted_map_iff`: label-preserving relabelings preserve admitted histories
-/

namespace SystemAlgebra

open Classical

theorem renameConverter_mem {O J : Type} {U V : O → Type} {X Y : J → Type}
    (f : (Σ o, U o) → (Σ j, X j)) (g : (Σ j, Y j) → (Σ o, V o)) :
    ∀ h y, y ∈ renameConverter f g h →
      y ∈ relabel (forwardAll J X Y) (outsideMap f) (outsideMap g) h :=
  relabel_mono (fun _ _ h => canon_mem h) _ _

section Renaming

variable {O O' J : Type} {U V : O → Type} {U' V' : O' → Type} {X Y : J → Type}
    (e : O' ≃ O) (f : (Σ o, U' o) → (Σ o, U o))
    (g : (Σ o, V o) → (Σ o, V' o))
    (hf : ∀ u, (f u).1 = e u.1) (hg : ∀ v, (g v).1 = e.symm v.1)

include hf hg in
/-- The renaming converter is the canonical restriction of relabeled forwarding. -/
theorem renameConverter_eq_canon :
    renameConverter f g = canon (relabel (forwardAll O U V) (outsideMap f) (outsideMap g)) :=
  (canon_outsideMap e f g hf hg (forwardAll O U V)).symm

include hf hg in
/-- A renamed partial converter is a partial converter. -/
theorem IsDDC.relabelOutside {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α) :
    IsDDC b (relabel α (outsideMap f) (outsideMap g)) := by
  refine ⟨⟨?_, ?_⟩, fun h z hd => ?_, fun h hd => ?_, fun h y o hy hl => ?_⟩
  · simpa only [SilentAtEmpty, relabel, List.map_nil, Part.map_Dom] using hα.dds.1
  · intro p h hp hn hd
    exact hα.dds.2 (hp.map (outsideMap f)) (fun he => hn (List.map_eq_nil_iff.mp he)) hd
  · rw [admits_outsideMap e f g hf hg α]
    exact hα.admits _ _ (by simpa only [relabel, List.map_append, List.map_singleton,
      Part.map_Dom] using hd)
  · rw [insideRun_outsideMap f g α]
    exact hα.bound _ hd
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
/-- Composing a partial converter after a renaming converter relabels it. -/
theorem IsDDC.trim_renameConverter_serialM {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α) :
    trim (serialM (renameConverter f g) α) = relabel α (outsideMap f) (outsideMap g) := by
  have hr := (renameConverter_isResponsiveDDC e f g hf hg).isDDC
  apply (hr.comp hα).eq_of_admitted_replies (hα.relabelOutside e f g hf hg)
  intro h hh
  rw [replies_trim_iff, renameConverter_eq_canon e f g hf hg]
  rw [renameConverter_eq_canon e f g hf hg] at hr
  conv_lhs => rw [← hα.canon_eq]
  rw [replies_serialM_canon_iff hr (hα.canon_eq.symm ▸ hα) h hh,
    serialM_relabel_forwardAll f g α hα.dds.1]

end Renaming

section InsideRenaming

variable {O J J' : Type} {U V : O → Type} {X Y : J → Type} {X' Y' : J' → Type}
    (e : J ≃ J') (k : (Σ j, X j) → (Σ j, X' j)) (l : (Σ j, Y' j) → (Σ j, Y j))
    (hk : ∀ x, (k x).1 = e x.1) (hl : ∀ y, (l y).1 = e.symm y.1)

include hk hl in
/-- Composing a partial converter before a renaming converter relabels its inside, on
admitted histories. -/
theorem IsDDC.replies_serialM_renameConverter {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsDDC b α) (h : List ((Σ l, twoFam U Y' l) × (Σ l, twoFam V X' l)))
    (hh : Admitted converterAdmits h) :
    Replies (serialM α (renameConverter k l)) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (relabel α (insideMap l) (insideMap k)) (h.map Prod.fst) (h.map Prod.snd) := by
  have hr := (renameConverter_isResponsiveDDC e k l hk hl).isDDC
  rw [renameConverter_eq_canon e k l hk hl] at hr ⊢
  have hα' : IsDDC b (canon α) := by rw [hα.canon_eq]; exact hα
  conv_lhs => rw [← hα.canon_eq]
  rw [replies_serialM_canon_iff hα' hr h hh, serialM_forwardAll_relabel (α := α) k l hα.dds.1]

end InsideRenaming

section Relabeling

variable {O J O' J' : Type} {U V : O → Type} {X Y : J → Type}
    {U' V' : O' → Type} {X' Y' : J' → Type}

theorem admitAfter_twoMap (e : O' → O) (κ : J' → J) (hκ : Function.Injective κ)
    (r : Option (Two O' J')) (l : Two O' J') :
    admitAfter (r.map (twoMap e κ)) (twoMap e κ l) ↔ admitAfter r l := by
  rcases r with _ | ⟨_ | ⟨⟨⟩⟩, r⟩ <;> rcases l with ⟨_ | ⟨⟨⟩⟩, l⟩ <;>
    simp [admitAfter, twoMap, hκ.eq_iff]

/-- A relabeling preserving outside/inside labels, with one injective map on
inside labels, preserves the admission of the next input. -/
theorem converterAdmits_map_iff
    (i : (Σ l, twoFam U' Y' l) → (Σ l, twoFam U Y l))
    (o : (Σ l, twoFam V' X' l) → (Σ l, twoFam V X l))
    (e : O' → O) (κ : J' → J) (hκ : Function.Injective κ)
    (hi : ∀ z, (i z).1 = twoMap e κ z.1) (ho : ∀ z, (o z).1 = twoMap e κ z.1)
    (h : List ((Σ l, twoFam U' Y' l) × (Σ l, twoFam V' X' l))) (x : Σ l, twoFam U' Y' l) :
    converterAdmits (h.map (Prod.map i o)) (i x) ↔ converterAdmits h x := by
  simp only [converterAdmits, hi, List.getLast?_map, Option.map_map]
  have hm : ((fun z : (Σ l, twoFam U Y l) × (Σ l, twoFam V X l) => z.2.1) ∘ Prod.map i o) =
      twoMap e κ ∘ (fun z : (Σ l, twoFam U' Y' l) × (Σ l, twoFam V' X' l) => z.2.1) := by
    funext w
    exact ho w.2
  rw [hm, ← Option.map_map]
  exact admitAfter_twoMap e κ hκ _ _

/-- A relabeling preserving outside/inside labels, with one injective map on
inside labels, preserves admitted histories. -/
theorem admitted_map_iff
    (i : (Σ l, twoFam U' Y' l) → (Σ l, twoFam U Y l))
    (o : (Σ l, twoFam V' X' l) → (Σ l, twoFam V X l))
    (e : O' → O) (κ : J' → J) (hκ : Function.Injective κ)
    (hi : ∀ z, (i z).1 = twoMap e κ z.1) (ho : ∀ z, (o z).1 = twoMap e κ z.1) :
    ∀ h : List ((Σ l, twoFam U' Y' l) × (Σ l, twoFam V' X' l)),
      Admitted converterAdmits (h.map (Prod.map i o)) ↔ Admitted converterAdmits h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [List.map_append, List.map_singleton, admitted_snoc, admitted_snoc, ih]
    exact and_congr Iff.rfl (converterAdmits_map_iff i o e κ hκ hi ho h z.1)

/-- Relabeling transports agreement of completed histories on admitted inputs. -/
theorem replies_relabel_congr_of_admitted
    {s t : InsideOutsideSystem O J U V X Y}
    (i : (Σ l, twoFam U' Y' l) ≃ (Σ l, twoFam U Y l))
    (o : (Σ l, twoFam V X l) ≃ (Σ l, twoFam V' X' l))
    (e : O' → O) (κ : J' → J) (hκ : Function.Injective κ)
    (hi : ∀ z, (i z).1 = twoMap e κ z.1) (ho : ∀ z, (o.symm z).1 = twoMap e κ z.1)
    (hst : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)), Admitted converterAdmits h →
      (Replies s (h.map Prod.fst) (h.map Prod.snd) ↔ Replies t (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ l, twoFam U' Y' l) × (Σ l, twoFam V' X' l))) (hh : Admitted converterAdmits h) :
    Replies (relabel s i o) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (relabel t i o) (h.map Prod.fst) (h.map Prod.snd) := by
  rw [replies_relabel_iff, replies_relabel_iff]
  apply hst
  have he : h.map (i.prodCongr o.symm) = h.map (Prod.map i o.symm) := rfl
  rw [he, admitted_map_iff i o.symm e κ hκ hi ho]
  exact hh

/-- Relabeling of inside messages as an equivalence. -/
def insideEquiv (k : (Σ j, Y j) ≃ (Σ j, Y' j)) : (Σ l, twoFam U Y l) ≃ (Σ l, twoFam U Y' l) where
  toFun := insideMap k
  invFun := insideMap k.symm
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · rfl
    · have e1 := k.symm_apply_apply ⟨i, y⟩
      simp only [insideMap]
      generalize k ⟨i, y⟩ = w at e1 ⊢
      rcases w with ⟨j', y'⟩
      rw [e1]
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · rfl
    · have e1 := k.apply_symm_apply ⟨i, y⟩
      simp only [insideMap]
      generalize k.symm ⟨i, y⟩ = w at e1 ⊢
      rcases w with ⟨j', y'⟩
      rw [e1]

/-- Relabeling of outside messages as an equivalence. -/
def outsideEquiv (f : (Σ o, U o) ≃ (Σ o, U' o)) : (Σ l, twoFam U Y l) ≃ (Σ l, twoFam U' Y l) where
  toFun := outsideMap f
  invFun := outsideMap f.symm
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · have e1 := f.symm_apply_apply ⟨i, y⟩
      simp only [outsideMap]
      generalize f ⟨i, y⟩ = w at e1 ⊢
      rcases w with ⟨j', y'⟩
      rw [e1]
    · rfl
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · have e1 := f.apply_symm_apply ⟨i, y⟩
      simp only [outsideMap]
      generalize f.symm ⟨i, y⟩ = w at e1 ⊢
      rcases w with ⟨j', y'⟩
      rw [e1]
    · rfl

end Relabeling

section Transport

variable {O O' J : Type} {U V : O → Type} {U' V' : O' → Type} {X Y : J → Type}

theorem outsideInputs_outsideMap (f : (Σ o, U' o) → (Σ o, U o)) (xs : List (Σ l, twoFam U' Y l)) :
    outsideInputs (xs.map (outsideMap f)) = (outsideInputs xs).map f := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    rw [List.map_append, outsideInputs_append, outsideInputs_append, ih, List.map_append]
    congr 1
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩ <;>
      simp [outsideInputs, outsideMap, splitIn, restrict_cons_self, restrict_cons_ne]

theorem insideQueries_outsideMap (g : (Σ o, V o) → (Σ o, V' o)) (ys : List (Σ l, twoFam V X l)) :
    insideQueries (ys.map (outsideMap g)) = insideQueries ys := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    rw [List.map_append, insideQueries_append, insideQueries_append, ih]
    congr 1
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ <;>
      simp [insideQueries, outsideMap, splitIn, restrict_cons_self, restrict_cons_ne]

variable {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop} {F' : List (Σ o, U' o) → Prop}

/-- **Relabeling the outside of a DDC from `E` to `F`** by a label-preserving bijection gives a
DDC from `E` to the transported outside domain. -/
theorem IsDDCFrom.relabelOutside (e : O' ≃ O) (f : (Σ o, U' o) ≃ (Σ o, U o))
    (g : (Σ o, V o) ≃ (Σ o, V' o)) (hf : ∀ u, (f u).1 = e u.1) (hg : ∀ v, (g v).1 = e.symm v.1)
    (hd : ∀ h, F (h.map f) ↔ F' h) {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsDDCFrom E F b α) : IsDDCFrom E F' b (relabel α (outsideMap f) (outsideMap g)) := by
  have hg' : ∀ v, (g.symm v).1 = e v.1 := fun v => by
    have h1 := congrArg e (hg (g.symm v))
    rw [g.apply_symm_apply, e.apply_symm_apply] at h1
    exact h1.symm
  have hfst (h : List ((Σ l, twoFam U' Y l) × (Σ l, twoFam V' X l))) :
      (h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)).map Prod.fst =
        (h.map Prod.fst).map (outsideMap f) := by
    simp only [List.map_map]; rfl
  have hQ (h : List ((Σ l, twoFam U' Y l) × (Σ l, twoFam V' X l))) :
      insideQueries ((h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)).map Prod.snd) =
        insideQueries (h.map Prod.snd) := by
    have hs : (h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)).map Prod.snd =
        (h.map Prod.snd).map (outsideMap g.symm) := by
      simp only [List.map_map]; rfl
    rw [hs, insideQueries_outsideMap]
  refine ⟨hα.isDDC.relabelOutside e f g hf hg, fun h x hr => ?_, fun h hr => ?_⟩
  · have hr' := (replies_relabel_iff α (outsideEquiv f) (outsideEquiv g) h).mp hr
    have hans := hα.answers _ (outsideMap f x) hr'
    change (α ((h.map Prod.fst ++ [x]).map (outsideMap f))).Dom ↔ _
    rw [List.map_append, List.map_singleton, ← hfst, hans]
    have hA : Admitted converterAdmits (h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)) ↔
        Admitted converterAdmits h :=
      admitted_map_iff (outsideMap f) (outsideMap g.symm) e id Function.injective_id
        (outsideMap_fst e f hf) (outsideMap_fst e g.symm hg') h
    have hC : converterAdmits (h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm))
        (outsideMap f x) ↔ converterAdmits h x :=
      converterAdmits_map_iff (outsideMap f) (outsideMap g.symm) e id Function.injective_id
        (outsideMap_fst e f hf) (outsideMap_fst e g.symm hg') h x
    have hF : F (outsideInputs ((h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)).map
        Prod.fst ++ [outsideMap f x])) ↔ F' (outsideInputs (h.map Prod.fst ++ [x])) := by
      have hm : (h.map ((outsideEquiv f).prodCongr (outsideEquiv g).symm)).map Prod.fst ++
          [outsideMap f x] = (h.map Prod.fst ++ [x]).map (outsideMap f) := by
        rw [hfst, List.map_append, List.map_singleton]
      rw [hm, outsideInputs_outsideMap]
      exact hd _
    unfold converterDomain
    rw [hQ]
    exact and_congr hA (and_congr hC (and_congr hF Iff.rfl))
  · have hr' := (replies_relabel_iff α (outsideEquiv f) (outsideEquiv g) h).mp hr
    rw [← hQ]
    exact hα.queries _ hr'

end Transport

end SystemAlgebra

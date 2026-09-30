import ConstructiveCryptography.DDCCoherence

/-!
# Parallel renaming

Renaming two disjoint interface families independently is renaming their union.

## Main definitions

* `Interface.sumEquiv`: the union of two alphabet bijections

## Main results

* `Interface.tensorL_renameConverter`: parallel renaming converters are the renaming
  converter of the union
* `Interface.parallelConverter_rename`: the parallel composition of two renamings is the
  renaming of the union
-/

namespace SystemAlgebra.Interface

open Classical CategoryTheory

def sumEquiv {I J K L : Type} {U : I → Type} {V : J → Type} {X : K → Type} {Y : L → Type}
    (f : (Σ i, U i) ≃ (Σ j, V j)) (g : (Σ k, X k) ≃ (Σ l, Y l)) :
    (Σ i, Sum.rec U X i) ≃ (Σ j, Sum.rec V Y j) where
  toFun
    | ⟨.inl i, u⟩ => ⟨.inl (f ⟨i, u⟩).1, (f ⟨i, u⟩).2⟩
    | ⟨.inr k, x⟩ => ⟨.inr (g ⟨k, x⟩).1, (g ⟨k, x⟩).2⟩
  invFun
    | ⟨.inl j, v⟩ => ⟨.inl (f.symm ⟨j, v⟩).1, (f.symm ⟨j, v⟩).2⟩
    | ⟨.inr l, y⟩ => ⟨.inr (g.symm ⟨l, y⟩).1, (g.symm ⟨l, y⟩).2⟩
  left_inv := by
    rintro ⟨(i | k), x⟩
    · simpa only [Sigma.eta] using congrArg (fun z : Σ i, U i =>
        (⟨.inl z.1, z.2⟩ : Σ i, Sum.rec U X i)) (f.symm_apply_apply ⟨i, x⟩)
    · simpa only [Sigma.eta] using congrArg (fun z : Σ k, X k =>
        (⟨.inr z.1, z.2⟩ : Σ i, Sum.rec U X i)) (g.symm_apply_apply ⟨k, x⟩)
  right_inv := by
    rintro ⟨(j | l), x⟩
    · simpa only [Sigma.eta] using congrArg (fun z : Σ j, V j =>
        (⟨.inl z.1, z.2⟩ : Σ j, Sum.rec V Y j)) (f.apply_symm_apply ⟨j, x⟩)
    · simpa only [Sigma.eta] using congrArg (fun z : Σ l, Y l =>
        (⟨.inr z.1, z.2⟩ : Σ j, Sum.rec V Y j)) (g.apply_symm_apply ⟨l, x⟩)

theorem sumEquiv_label {A B C D : Interface} (e : A.I ≃ B.I) (e' : C.I ≃ D.I)
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (f' : (Σ i, C.X i) ≃ (Σ j, D.X j))
    (hf : ∀ x, (f x).1 = e x.1) (hf' : ∀ x, (f' x).1 = e' x.1)
    (x : Σ i, Sum.rec A.X C.X i) :
    (sumEquiv f f' x).1 = Equiv.sumCongr e e' x.1 := by
  rcases x with ⟨(i | j), x⟩
  · exact congrArg Sum.inl (hf ⟨i, x⟩)
  · exact congrArg Sum.inr (hf' ⟨j, x⟩)

theorem parallelDomain_sumEquiv {A B C D : Interface}
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (f' : (Σ i, C.X i) ≃ (Σ j, D.X j))
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h)
    (hd' : ∀ h, D.domain (h.map f') ↔ C.domain h)
    (h : List (Σ i, Sum.rec A.X C.X i)) :
    parallelDomain B D (h.map (sumEquiv f f')) ↔ parallelDomain A C h := by
  have hp :
      restrict none ((h.map (sumEquiv f f')).map (sumAlphabet (Sum.rec B.X D.X)).symm) =
        (restrict none (h.map (sumAlphabet (Sum.rec A.X C.X)).symm)).map f ∧
      restrict (some ()) ((h.map (sumEquiv f f')).map (sumAlphabet (Sum.rec B.X D.X)).symm) =
        (restrict (some ()) (h.map (sumAlphabet (Sum.rec A.X C.X)).symm)).map f' := by
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | cons x h ih =>
      rcases x with ⟨(i | j), x⟩ <;>
        simpa only [List.map_cons, sumEquiv, sumAlphabet, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
          restrict_cons_self, restrict_cons_ne (by simp : (some () : Option Unit) ≠ none),
          restrict_cons_ne (by simp : (none : Option Unit) ≠ some ()),
          Sigma.eta, List.cons.injEq, true_and] using ih
  simp only [parallelDomain, parallelInputs, hp.1, hp.2, ne_eq, List.map_eq_nil_iff, hd, hd']

variable {A B C D : Interface}
    (e : A.I ≃ B.I) (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (e' : C.I ≃ D.I) (f' : (Σ i, C.X i) ≃ (Σ j, D.X j)) (g' : (Σ i, C.Y i) ≃ (Σ j, D.Y j))
    (hf' : ∀ x, (f' x).1 = e' x.1) (hg' : ∀ y, (g' y).1 = e' y.1)

theorem tensorRaw_rename_forwardAll :
    (tensorRaw (relabel (forwardAll B.I B.X B.Y) (outsideMap f) (outsideMap g.symm))
      (relabel (forwardAll D.I D.X D.Y) (outsideMap f') (outsideMap g'.symm)) :
      InsideOutsideSystem (A.I ⊕ C.I) (B.I ⊕ D.I) (Sum.rec A.X C.X) (Sum.rec A.Y C.Y)
        (Sum.rec B.X D.X) (Sum.rec B.Y D.Y)) =
    relabel (forwardAll (B.I ⊕ D.I) (Sum.rec B.X D.X) (Sum.rec B.Y D.Y))
      (outsideMap (sumEquiv f f')) (outsideMap (sumEquiv g g').symm) := by
  rw [← tensorRaw_forwardAll]
  simp only [tensorRaw, pair_relabel, relabel_relabel]
  congr 1
  · funext z
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), (i | j)⟩, z⟩ <;> rfl
  · funext z
    rcases z with ⟨(_ | ⟨⟨⟩⟩), ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩⟩ <;> rfl

include hf hg hf' hg' in
theorem tensorL_renameConverter :
    (tensorL (renameConverter f g.symm) (renameConverter f' g'.symm) :
      InsideOutsideSystem (A.I ⊕ C.I) (B.I ⊕ D.I) (Sum.rec A.X C.X) (Sum.rec A.Y C.Y)
        (Sum.rec B.X D.X) (Sum.rec B.Y D.Y)) =
      renameConverter (sumEquiv f f') (sumEquiv g g').symm := by
  have h₁ := renameConverter_isResponsiveDDC e f g.symm hf (alphabet_symm_label e g hg)
  have h₂ := renameConverter_isResponsiveDDC e' f' g'.symm hf' (alphabet_symm_label e' g' hg')
  have h₃ := renameConverter_isResponsiveDDC (Equiv.sumCongr e e') (sumEquiv f f') (sumEquiv g g').symm
    (sumEquiv_label e e' f f' hf hf')
    (alphabet_symm_label (Equiv.sumCongr e e') (sumEquiv g g')
      (by rintro ⟨(i | j), y⟩; exact congrArg Sum.inl (hg ⟨i, y⟩); exact congrArg Sum.inr (hg' ⟨j, y⟩)))
  apply (h₁.tensorL h₂).eq_of_common_replies h₃
    (c := relabel (forwardAll (B.I ⊕ D.I) (Sum.rec B.X D.X) (Sum.rec B.Y D.Y))
      (outsideMap (sumEquiv f f')) (outsideMap (sumEquiv g g').symm))
  · intro xs ys hr
    rw [← tensorRaw_rename_forwardAll f g f' g']
    apply hr.mono
    intro h y hy
    exact tensorRaw_mono (renameConverter_mem f g.symm) (renameConverter_mem f' g'.symm) h y
      (canon_mem hy)
  · intro xs ys hr
    exact hr.mono (renameConverter_mem _ _)

end SystemAlgebra.Interface


namespace SystemAlgebra.Interface

open Classical CategoryTheory

theorem parallelConverter_rename {A B C D : Interface}
    (e : A.I ≃ B.I) (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h)
    (e' : C.I ≃ D.I) (f' : (Σ i, C.X i) ≃ (Σ j, D.X j)) (g' : (Σ i, C.Y i) ≃ (Σ j, D.Y j))
    (hf' : ∀ x, (f' x).1 = e' x.1) (hg' : ∀ y, (g' y).1 = e' y.1)
    (hd' : ∀ h, D.domain (h.map f') ↔ C.domain h) :
    parallelConverter (rename e f g hf hg hd) (rename e' f' g' hf' hg' hd') =
      rename (Equiv.sumCongr e e') (sumEquiv f f') (sumEquiv g g')
        (sumEquiv_label e e' f f' hf hf')
        (by rintro ⟨(i | j), y⟩; exact congrArg Sum.inl (hg ⟨i, y⟩); exact congrArg Sum.inr (hg' ⟨j, y⟩))
        (parallelDomain_sumEquiv f f' hd hd') := by
  change PDCBehavior.tensor (PDCBehavior.ofDDC _ _) (PDCBehavior.ofDDC _ _) =
    PDCBehavior.ofDDC _ _
  rw [PDCBehavior.tensor_ofDDC]
  refine PDCBehavior.ofDDC_eq_of_le _ _
    (W := (tensorRaw (renameConverter f g.symm) (renameConverter f' g'.symm) :
      InsideOutsideSystem (A.I ⊕ C.I) (B.I ⊕ D.I) (Sum.rec A.X C.X) (Sum.rec A.Y C.Y)
        (Sum.rec B.X D.X) (Sum.rec B.Y D.Y))) ?_ ?_
  · intro xs ys hr
    exact hr.mono fun h y hy => tensorRaw_mono
      (relabel_mono (fun _ _ hy => filter_mem hy) _ _)
      (relabel_mono (fun _ _ hy => filter_mem hy) _ _) h y (canon_mem hy)
  · intro xs ys hr
    have hs : Replies (renameConverter (sumEquiv f f') (sumEquiv g g').symm) xs ys :=
      hr.mono (relabel_mono (fun _ _ hy => filter_mem hy) _ _)
    rw [← tensorL_renameConverter e f g hf hg e' f' g' hf' hg'] at hs
    exact hs.mono fun h y hy => canon_mem hy

end SystemAlgebra.Interface

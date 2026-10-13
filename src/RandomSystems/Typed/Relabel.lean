import RandomSystems.Converter.ConverterRelabel
import RandomSystems.Typed.Parallel

/-!
# Renaming heterogeneous interfaces

A bijection of interfaces that keeps each message's label and transports the domain gives a
typed converter: the identity of the inside interface, with its outside relabeled. Renamings
compose, and the renaming by the identity is the identity.

## Main definitions

* `TypedConverter.rename e f g`: the renaming converter of a label-preserving bijection

## Main results

* `TypedConverter.rename_refl`: the renaming by the identity is the identity
* `TypedConverter.rename_comp`: renamings compose
-/

namespace SystemAlgebra

open Classical

namespace Interface

lemma alphabet_symm_label {I J : Type} {X : I → Type} {Y : J → Type}
    (e : I ≃ J) (f : (Σ i, X i) ≃ (Σ j, Y j))
    (hf : ∀ x, (f x).1 = e x.1) (y : Σ j, Y j) :
    (f.symm y).1 = e.symm y.1 := by
  have he := congrArg e.symm (hf (f.symm y))
  simpa only [f.apply_symm_apply, e.symm_apply_apply] using he.symm

/-- The identity filter lies below the forwarding converter. -/
lemma filter_mem {A : Interface} {h y}
    (hy : y ∈ (DDC.filter (Y := A.Y) (fun h => h = [] ∨ A.domain h)
      (prefix_or_nil A.nonempty_prefix.2)).1 h) : y ∈ idConverter A.I A.X A.Y h :=
  ((filterDom_mem_iff _ _ h y).mp hy).2

end Interface

namespace TypedConverter

open Interface

/-- The forwarding converter for a label-preserving bijection of alphabets and domains: the
identity of `B`, with its outside relabeled to `A`. -/
noncomputable def rename {A B : Interface} (e : A.I ≃ B.I)
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h) : TypedConverter A B :=
  ofDDC (relabel (DDC.filter (Y := B.Y) (fun h => h = [] ∨ B.domain h)
      (prefix_or_nil B.nonempty_prefix.2)).1 (outsideMap f) (outsideMap g.symm))
    ((isDDCFrom_filter B.nonempty_prefix).relabelOutside e f g.symm hf
      (alphabet_symm_label e g hg) hd)

/-- A renaming is the behavior of a DDC below the renaming converter. -/
lemma exists_rename_eq_ofDDC {A B : Interface} (e : A.I ≃ B.I)
    (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h) :
    ∃ (r : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y) (hr : IsDDCFrom B.domain A.domain 1 r),
      rename e f g hf hg hd = PDCBehavior.ofDDC r hr ∧
        ∀ h y, y ∈ r h → y ∈ renameConverter f g.symm h :=
  ⟨_, _, rfl, relabel_mono (fun _ _ hy => filter_mem hy) _ _⟩

lemma rename_refl (A : Interface) :
    rename (Equiv.refl A.I) (Equiv.refl (Σ i, A.X i)) (Equiv.refl (Σ i, A.Y i))
      (fun _ => rfl) (fun _ => rfl)
      (fun h => (congrArg A.domain (List.map_id h)).to_iff) = TypedConverter.id A := by
  have he : relabel (DDC.filter (Y := A.Y) (fun h => h = [] ∨ A.domain h)
      (prefix_or_nil A.nonempty_prefix.2)).1 (outsideMap (Equiv.refl (Σ i, A.X i)))
      (outsideMap (Equiv.refl (Σ i, A.Y i)).symm) =
      (DDC.filter (Y := A.Y) (fun h => h = [] ∨ A.domain h) (prefix_or_nil A.nonempty_prefix.2)).1 := by
    simp only [Equiv.refl_symm, Equiv.coe_refl, outsideMap_id, relabel_id]
  refine PDCBehavior.ofDDC_eq_of_le _ _ ?_ (fun _ _ hr => hr)
  intro xs ys hr
  rwa [he] at hr

lemma rename_comp {A B C : Interface}
    (e : A.I ≃ B.I) (f : (Σ i, A.X i) ≃ (Σ j, B.X j)) (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h)
    (e' : B.I ≃ C.I) (f' : (Σ i, B.X i) ≃ (Σ j, C.X j)) (g' : (Σ i, B.Y i) ≃ (Σ j, C.Y j))
    (hf' : ∀ x, (f' x).1 = e' x.1) (hg' : ∀ y, (g' y).1 = e' y.1)
    (hd' : ∀ h, C.domain (h.map f') ↔ B.domain h) :
    comp (rename e f g hf hg hd) (rename e' f' g' hf' hg' hd') =
      rename (e.trans e') (f.trans f') (g.trans g')
        (fun x => (hf' (f x)).trans (congrArg e' (hf x)))
        (fun y => (hg' (g y)).trans (congrArg e' (hg y)))
        (fun h => by
          have hm : h.map (f.trans f') = (h.map f).map f' := by
            change h.map ((f' : _ → _) ∘ (f : _ → _)) = _
            exact List.map_map.symm
          exact (congrArg C.domain hm).to_iff.trans ((hd' (h.map f)).trans (hd h))) := by
  change PDCBehavior.comp (PDCBehavior.ofDDC _ _) (PDCBehavior.ofDDC _ _) = _
  rw [PDCBehavior.comp_ofDDC]
  refine PDCBehavior.ofDDC_eq_of_le _ _
    (W := renameConverter (f.trans f') (g.trans g').symm) ?_ ?_
  · intro xs ys hr
    have hm : Replies (serialM (renameConverter f g.symm) (renameConverter f' g'.symm)) xs ys :=
      ((replies_trim_iff _ _ _).mp hr).serialM_mono
      (relabel_mono (fun _ _ hy => filter_mem hy) (outsideMap f) (outsideMap g.symm))
      (relabel_mono (fun _ _ hy => filter_mem hy) (outsideMap f') (outsideMap g'.symm))
    have he := renameConverter_comp e' f' g'.symm hf' (alphabet_symm_label e' g' hg')
      e f g.symm hf (alphabet_symm_label e g hg)
    have ht := (replies_trim_iff _ _ _).mpr hm
    rw [he] at ht
    exact ht
  · intro xs ys hr
    exact hr.mono (relabel_mono (fun _ _ hy => filter_mem hy) _ _)

end TypedConverter

end SystemAlgebra

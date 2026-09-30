import ConstructiveCryptography.ResourceParallel

/-!
# Locality of independent attachment

Attaching parallel converters to parallel resources is attachment component by component:
`(α ⊗ β)(R ∥ S) = αR ∥ βS`. With presentations of the two converters and the two resources,
both sides are mixtures over the same four independent samples.
-/

namespace SystemAlgebra.Interface

open Classical Probability CategoryTheory

variable {A B C D : Interface}

/-- **Locality**: parallel converters act on parallel resources component by component. -/
theorem parallel_attach (α : A ⟶ B) (β : C ⟶ D) (R : Resource B) (S : Resource D) :
    (parallelConverter α β • parallel R S : Resource (tensor A C)) =
      parallel (α • R : Resource A) (β • S : Resource C) := by
  obtain ⟨ba, P, hP⟩ := α.2
  obtain ⟨bb, Q, hQ⟩ := β.2
  obtain ⟨T, rfl⟩ := R.exists_ofPDS
  obtain ⟨U, rfl⟩ := S.exists_ofPDS
  have hαT : (α • Resource.ofPDS T : Resource A) =
      Resource.ofPDS (attachPDS A.nonempty_prefix P T) :=
    Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix α (Resource.ofPDS T).1
        (Resource.ofPDS T).2 P T hP (fun _ => rfl) h)
  have hβU : (β • Resource.ofPDS U : Resource C) =
      Resource.ofPDS (attachPDS C.nonempty_prefix Q U) :=
    Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents D.nonempty_prefix C.nonempty_prefix β (Resource.ofPDS U).1
        (Resource.ofPDS U).2 Q U hQ (fun _ => rfl) h)
  have hαβ := fun h => (PDCBehavior.tensor_presents α β P Q hP hQ h).symm
  rw [hαT, hβU, parallel_ofPDS, parallel_ofPDS]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [smul_val, PDCBehavior.attach_presents (tensor B D).nonempty_prefix
    (tensor A C).nonempty_prefix (parallelConverter α β)
    (Resource.ofPDS (A := tensor B D) (parallelPDS T U)).1
    (Resource.ofPDS (A := tensor B D) (parallelPDS T U)).2 _ (parallelPDS T U) hαβ
    (fun _ => rfl) h,
    behaviorMass_attachPDS]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, tensorPDC, parallelPDS, attachPDS, Distribution.mass_fTransform,
    Distribution.fTransform_prod_left, Distribution.fTransform_prod_right]
  rw [← Distribution.independent_product_middle P.1 Q.1 T.1 U.1, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro p
  exact iff_of_eq (congrArg (fun t => Replies t (h.map Prod.fst) (h.map Prod.snd))
    (trim_apply_tensorL_pair p.1.1.2.isDDC p.1.2.2.isDDC p.2.1.2.2.1 p.2.2.2.2.1))

end SystemAlgebra.Interface

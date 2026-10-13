import RandomSystems.Typed.SystemParallel

/-!
# Locality of independent attachment

Attaching parallel typed converters to parallel typed systems is attachment component by
component: `(α ⊗ β)(R ∥ S) = αR ∥ βS`. With presentations of the two converters and the two
systems, both sides are mixtures over the same four independent samples.

## Main results

* `TypedConverter.parallel_attach`: locality of attachment
-/

namespace SystemAlgebra.TypedConverter

open Classical Probability Interface

variable {A B C D : Interface}

/-- **Locality**: parallel typed converters act on parallel typed systems component by
component. -/
lemma parallel_attach (α : TypedConverter A B) (β : TypedConverter C D) (R : TypedSystem B)
    (S : TypedSystem D) :
    (parallel α β • TypedSystem.parallel R S : TypedSystem (tensor A C)) =
      TypedSystem.parallel (α • R : TypedSystem A) (β • S : TypedSystem C) := by
  obtain ⟨ba, P, hP⟩ := α.2
  obtain ⟨bb, Q, hQ⟩ := β.2
  obtain ⟨T, rfl⟩ := R.exists_ofPDS
  obtain ⟨U, rfl⟩ := S.exists_ofPDS
  have hαT : (α • TypedSystem.ofPDS T : TypedSystem A) =
      TypedSystem.ofPDS (attachPDS A.nonempty_prefix P T) :=
    Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix α (TypedSystem.ofPDS T).1
        (TypedSystem.ofPDS T).2 P T hP (fun _ => rfl) h)
  have hβU : (β • TypedSystem.ofPDS U : TypedSystem C) =
      TypedSystem.ofPDS (attachPDS C.nonempty_prefix Q U) :=
    Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents D.nonempty_prefix C.nonempty_prefix β (TypedSystem.ofPDS U).1
        (TypedSystem.ofPDS U).2 Q U hQ (fun _ => rfl) h)
  have hαβ := fun h => (PDCBehavior.tensor_presents α β P Q hP hQ h).symm
  rw [hαT, hβU, TypedSystem.parallel_ofPDS, TypedSystem.parallel_ofPDS]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [smul_val, PDCBehavior.attach_presents (tensor B D).nonempty_prefix
    (tensor A C).nonempty_prefix (parallel α β)
    (TypedSystem.ofPDS (A := tensor B D) (parallelPDS T U)).1
    (TypedSystem.ofPDS (A := tensor B D) (parallelPDS T U)).2 _ (parallelPDS T U) hαβ
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

end SystemAlgebra.TypedConverter

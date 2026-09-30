import ConstructiveCryptography.Specification.Relaxation.Closure

/-!
# Kernel relaxation

A map `view : X → Y` induces the reflexive relation `view R = view S`.
Its union lift is `view ⁻¹' (view '' S)` and is idempotent. The codomain
of the view is arbitrary.
-/

namespace ConstructiveCryptography.Relaxation

universe u v

/-- The relaxation identifying resources with the same image under a selected map. -/
def kernel {X : Type u} {Y : Type v} (view : X → Y) : Relaxation X :=
  Relaxation.ofPointwise (fun center => {R | view R = view center}) (fun _ => rfl)

/-- Kernel relaxation is the preimage of the specification image. -/
theorem kernel_apply {X : Type u} {Y : Type v} (view : X → Y) (S : Set X) :
    kernel view S = view ⁻¹' (view '' S) := by
  ext R
  -- An equal-view center is exactly a witness for membership in the image.
  simp only [kernel, Relaxation.mem_ofPointwise_iff,
    Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_image]
  exact exists_congr fun _ => and_congr_right fun _ => eq_comm

/-- Identifying equal images twice gives the same specification. -/
theorem kernel_idem {X : Type u} {Y : Type v} (view : X → Y) (S : Set X) :
    kernel view (kernel view S) = kernel view S := by
  apply Set.Subset.antisymm
  · -- Two equal-view relations compose by transitivity.
    intro R h
    obtain ⟨middle, hm, outer⟩ := Relaxation.mem_ofPointwise_iff.mp h
    obtain ⟨center, admitted, same⟩ := Relaxation.mem_ofPointwise_iff.mp hm
    exact Relaxation.mem_ofPointwise_iff.mpr ⟨center, admitted, outer.trans same⟩
  · -- Reflexivity retains every already-relaxed resource.
    exact (kernel view).subset_apply _

end ConstructiveCryptography.Relaxation

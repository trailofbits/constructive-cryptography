import ConstructiveCryptography.ResourceParallelAttachment
import ConstructiveCryptography.ResourceCoherence
import ConstructiveCryptography.InterfaceMonoidal
import RandomSystems.Converter.EmptyInterface

/-!
# Fixed contexts

A resource `R` on `A` is a converter from `A` to the unit interface (`resourceConverter`):
the PDC of the DDC readings (`resourcePDC`) of the deterministic resources presenting `R`.
Attaching it to the unit resource gives `R`. In parallel with the identity it gives the fixed
contexts: attaching `rightContext A S` to `R` is `R ∥ S`, and so is attaching
`leftContext R B` to `S`.

## Main definitions

* `Interface.resourceConverter R`: `R` as a converter with no inside interfaces
* `Interface.constant R B`: the converter that ignores its inside resource and exposes `R`
* `Interface.rightContext A S`, `Interface.leftContext R B`: the fixed contexts

## Main results

* `Interface.attach_resourceConverter`, `Interface.attach_constant`: attaching them gives `R`
* `Interface.attach_rightContext`, `Interface.attach_leftContext`: attaching a context is parallel
  composition

Source: Jost, §2.2.2 and Proposition 2.2.3.
-/

namespace SystemAlgebra.Interface

open Classical Probability CategoryTheory MonoidalCategory

variable {A B : Interface}

/-! ## A resource as a converter with no inside interfaces -/

/-- A resource as a converter with no inside interfaces: the PDC of the DDC readings of a
presentation of the resource. -/
noncomputable def resourceConverter (R : Interface.Resource A) : A ⟶ Interface.unit :=
  PDCBehavior.ofPDC (resourcePDC R.exists_ofPDS.choose)

/-- The unit interface has exactly one resource. -/
theorem resource_empty_eq (S : Interface.Resource Interface.unit) : S = Interface.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  rintro (_ | ⟨⟨⟨e, _⟩, _⟩, _⟩)
  · rw [S.1.mass_nil, Interface.dummy.1.mass_nil]
  · exact e.elim

theorem attach_resourceConverter (R : Interface.Resource A)
    (S : Interface.Resource Interface.unit) :
    (resourceConverter R • S : Interface.Resource A) = R := by
  rw [resource_empty_eq S]
  have hQ := R.exists_ofPDS.choose_spec
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [Interface.smul_val, PDCBehavior.attach_presents Interface.unit.nonempty_prefix
    A.nonempty_prefix (resourceConverter R) Interface.dummy.1 Interface.dummy.2
    (resourcePDC R.exists_ofPDS.choose) _ (fun _ => rfl) (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_right, Distribution.mass_fTransform]
  conv_rhs => rw [← hQ]
  change _ = R.exists_ofPDS.choose.1.mass _
  rw [resourcePDC, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun s => ?_
  dsimp only
  erw [apply_resourceDDC _ s.2.1.1, s.2.1.trim_eq]

/-! ## Constant converters and fixed contexts -/

/-- The converter that attaches to any resource and exposes no interface. -/
noncomputable def discardConverter (B : Interface) : Interface.unit ⟶ B :=
  Interface.ofDDC (discardSystem B.I B.X B.Y) (discardSystem_isDDCFrom B.domain)

/-- A constant converter: it ignores its inside resource and exposes `R`. No
efficiency claim is made for this unrestricted mathematical converter. -/
noncomputable def constant (R : Interface.Resource A) (B : Interface) : A ⟶ B :=
  resourceConverter R ≫ discardConverter B

theorem attach_constant (R : Interface.Resource A) {B : Interface} (S : Interface.Resource B) :
    (constant R B • S : Interface.Resource A) = R := by
  rw [constant, Interface.comp_smul, attach_resourceConverter]

theorem rightUnitor_hom_attach (R : Interface.Resource A) :
    ((Interface.rightUnitor A).hom • R : Interface.Resource (Interface.tensor A Interface.unit)) =
      Interface.parallel R Interface.dummy := by
  have h := congrArg (fun S : Interface.Resource A => ((Interface.rightUnitor A).hom • S :
    Interface.Resource (Interface.tensor A Interface.unit))) (Interface.parallel_dummy_right R)
  rw [← Interface.comp_smul, Iso.hom_inv_id, Interface.identity_attach] at h
  exact h.symm

theorem leftUnitor_hom_attach (R : Interface.Resource A) :
    ((Interface.leftUnitor A).hom • R : Interface.Resource (Interface.tensor Interface.unit A)) =
      Interface.parallel Interface.dummy R := by
  have h := congrArg (fun S : Interface.Resource A => ((Interface.leftUnitor A).hom • S :
    Interface.Resource (Interface.tensor Interface.unit A))) (Interface.parallel_dummy_left R)
  rw [← Interface.comp_smul, Iso.hom_inv_id, Interface.identity_attach] at h
  exact h.symm

/-- The fixed right context, expressed in the existing converter category. -/
noncomputable def rightContext (A : Interface) {B : Interface} (S : Interface.Resource B) :
    A ⊗ B ⟶ A :=
  (𝟙 A ⊗ₘ resourceConverter S) ≫ (Interface.rightUnitor A).hom

/-- The fixed left context; no symmetry of the selected substitution relation is used. -/
noncomputable def leftContext {A : Interface} (R : Interface.Resource A) (B : Interface) :
    A ⊗ B ⟶ B :=
  (resourceConverter R ⊗ₘ 𝟙 B) ≫ (Interface.leftUnitor B).hom

theorem attach_rightContext (R : Interface.Resource A) (S : Interface.Resource B) :
    (rightContext A S • R : Interface.Resource (A ⊗ B)) = Interface.parallel R S := by
  rw [rightContext, Interface.comp_smul, rightUnitor_hom_attach, Interface.tensorHom_eq, Interface.parallel_attach, Interface.identity_attach,
    attach_resourceConverter]

theorem attach_leftContext (R : Interface.Resource A) (S : Interface.Resource B) :
    (leftContext R B • S : Interface.Resource (A ⊗ B)) = Interface.parallel R S := by
  rw [leftContext, Interface.comp_smul, leftUnitor_hom_attach, Interface.tensorHom_eq, Interface.parallel_attach, Interface.identity_attach,
    attach_resourceConverter]

end SystemAlgebra.Interface

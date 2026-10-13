import RandomSystems.Typed.ParallelAttachment
import RandomSystems.Typed.SystemCoherence
import RandomSystems.Converter.EmptyInterface

/-!
# Fixed contexts

A typed system `R` on `A` is a typed converter from `A` to the unit interface (`ofSystem`):
the PDC of the DDC readings (`resourcePDC`) of the deterministic systems presenting `R`.
Attaching it to the unit system gives `R`. In parallel with the identity it gives the fixed
contexts: attaching `rightContext A S` to `R` is `R ∥ S`, and so is attaching
`leftContext R B` to `S`.

## Main definitions

* `TypedConverter.ofSystem R`: `R` as a typed converter with no inside interfaces
* `TypedConverter.constant R B`: the converter that ignores its inside system and exposes `R`
* `TypedConverter.rightContext A S`, `TypedConverter.leftContext R B`: the fixed contexts

## Main results

* `TypedConverter.attach_ofSystem`, `TypedConverter.attach_constant`: attaching them gives `R`
* `TypedConverter.attach_rightContext`, `TypedConverter.attach_leftContext`: attaching a
  context is parallel composition

Source: Jost, §2.2.2 and Proposition 2.2.3.
-/

namespace SystemAlgebra

open Classical Probability Interface

variable {A B : Interface}

/-- The unit interface has exactly one typed system. -/
lemma TypedSystem.empty_eq (S : TypedSystem unit) : S = TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  rintro (_ | ⟨⟨⟨e, _⟩, _⟩, _⟩)
  · rw [S.1.mass_nil, TypedSystem.dummy.1.mass_nil]
  · exact e.elim

namespace TypedConverter

/-! ## A typed system as a converter with no inside interfaces -/

/-- A typed system as a typed converter with no inside interfaces: the PDC of the DDC readings
of a presentation of the system. -/
noncomputable def ofSystem (R : TypedSystem A) : TypedConverter A unit :=
  PDCBehavior.ofPDC (resourcePDC R.exists_ofPDS.choose)

lemma attach_ofSystem (R : TypedSystem A) (S : TypedSystem unit) :
    (ofSystem R • S : TypedSystem A) = R := by
  rw [TypedSystem.empty_eq S]
  have hQ := R.exists_ofPDS.choose_spec
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [smul_val, PDCBehavior.attach_presents unit.nonempty_prefix
    A.nonempty_prefix (ofSystem R) TypedSystem.dummy.1 TypedSystem.dummy.2
    (resourcePDC R.exists_ofPDS.choose) _ (fun _ => rfl) (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_right, Distribution.mass_fTransform]
  conv_rhs => rw [← hQ]
  change _ = R.exists_ofPDS.choose.1.mass _
  rw [resourcePDC, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun s => ?_
  dsimp only
  erw [apply_resourceDDC _ s.2.1.1, s.2.1.trim_eq]

/-! ## Constant converters and fixed contexts -/

/-- The typed converter that attaches to any typed system and exposes no interface. -/
noncomputable def discard (B : Interface) : TypedConverter unit B :=
  ofDDC (discardSystem B.I B.X B.Y) (discardSystem_isDDCFrom B.domain)

/-- A constant converter: it ignores its inside system and exposes `R`. No
efficiency claim is made for this unrestricted mathematical converter. -/
noncomputable def constant (R : TypedSystem A) (B : Interface) : TypedConverter A B :=
  comp (ofSystem R) (discard B)

lemma attach_constant (R : TypedSystem A) {B : Interface} (S : TypedSystem B) :
    (constant R B • S : TypedSystem A) = R := by
  rw [constant, comp_smul, attach_ofSystem]

/-- The right unit renaming attached to a typed system puts the dummy system beside it. -/
lemma rightUnitor_hom_attach (R : TypedSystem A) :
    (rename (A := tensor A unit) (B := A) (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X)
        (rightUnitAlphabet A.Y) (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y)
        (parallelDomain_unit_right A) • R : TypedSystem (tensor A unit)) =
      TypedSystem.parallel R TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_right_mass]

/-- The left unit renaming attached to a typed system puts the dummy system beside it. -/
lemma leftUnitor_hom_attach (R : TypedSystem A) :
    (rename (A := tensor unit A) (B := A) (Equiv.emptySum Empty A.I) (leftUnitAlphabet A.X)
        (leftUnitAlphabet A.Y) (leftUnitAlphabet_fst A.X) (leftUnitAlphabet_fst A.Y)
        (parallelDomain_unit_left A) • R : TypedSystem (tensor unit A)) =
      TypedSystem.parallel TypedSystem.dummy R := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [rename_mass, TypedSystem.parallel_unit_left_mass]

/-- The fixed right context: the identity beside `S` as a converter, followed by the right unit
renaming. -/
noncomputable def rightContext (A : Interface) {B : Interface} (S : TypedSystem B) :
    TypedConverter (tensor A B) A :=
  comp (parallel (TypedConverter.id A) (ofSystem S))
    (rename (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y)
      (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A))

/-- The fixed left context; no symmetry of the selected substitution relation is used. -/
noncomputable def leftContext {A : Interface} (R : TypedSystem A) (B : Interface) :
    TypedConverter (tensor A B) B :=
  comp (parallel (ofSystem R) (TypedConverter.id B))
    (rename (Equiv.emptySum Empty B.I) (leftUnitAlphabet B.X) (leftUnitAlphabet B.Y)
      (leftUnitAlphabet_fst B.X) (leftUnitAlphabet_fst B.Y) (parallelDomain_unit_left B))

lemma attach_rightContext (R : TypedSystem A) (S : TypedSystem B) :
    (rightContext A S • R : TypedSystem (tensor A B)) = TypedSystem.parallel R S := by
  rw [rightContext, comp_smul, rightUnitor_hom_attach, parallel_attach, identity_attach,
    attach_ofSystem]

lemma attach_leftContext (R : TypedSystem A) (S : TypedSystem B) :
    (leftContext R B • S : TypedSystem (tensor A B)) = TypedSystem.parallel R S := by
  rw [leftContext, comp_smul, leftUnitor_hom_attach, parallel_attach, identity_attach,
    attach_ofSystem]

end TypedConverter

end SystemAlgebra

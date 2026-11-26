module

public import RandomSystems.Converter.ChronologicalLabeling.Sampling
public import Tests.ChronologicalLabeling

/-!
# Retained sampling through chronological labels

A nonuniform law chooses one constant function, retained across repeated queries.
Collapsing both label inputs to zero preserves that law. Its positive repeated-reply mass
and zero conflicting-reply mass exercise the coefficient theorem with a noninjective map.
-/

@[expose] public section

namespace Tests.ChronologicalSampling

open Probability Probability.Distribution SystemAlgebra Tests.ChronologicalLabeling

/-- One retained function is constantly `42` with mass `1/3`, or constantly `7` with mass `2/3`. -/
noncomputable def retainedLaw : Distribution (Fin 2 → ℕ) :=
  Finsupp.single (fun _ => 42) (1 / 3) + Finsupp.single (fun _ => 7) (2 / 3)

/-- Collapsing both labels to `0` leaves either constant function unchanged. -/
lemma retainedLaw_invariant :
    fTransform (fun g : Fin 2 → ℕ => g ∘ fun _ => (0 : Fin 2)) retainedLaw = retainedLaw := by
  rw [retainedLaw, fTransform_add, fTransform_single, fTransform_single]
  rfl

/-- The chosen input map is genuinely noninjective. -/
example : ¬ Function.Injective (fun _ : Fin 2 => (0 : Fin 2)) := by
  intro injective
  have equal : (0 : Fin 2) = 1 := injective rfl
  norm_num at equal

-- `labels` may use either enumeration of the two-label pool.
variable (labels : Fin (Fintype.card (Fin 2)) ≃ Fin 2)

/-- Three replies use one retained draw, so their joint mass is `1/3`. -/
lemma repeated_reply_mass :
    retainedLaw.mass (fun g => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain 3))
      (DDS.ofFunction (insideDomain 3) (insideDomain_prefix 3)
        (fun b => ⟨b.1, g b.2⟩)).1))
      [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] [⟨(), 42⟩, ⟨(), 42⟩, ⟨(), 42⟩]) = 1 / 3 := by
  classical
  have coefficient := chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq
    labels 0 (insideDomain_prefix 3) (outsideDomain_prefix 3)
    (chronologicalLabelingProgram_isDDCFrom labels 0 3)
    (fun _ => (0 : Fin 2)) (fun _ : ℕ => (0 : Fin 2))
    [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] (fun _ _ _ _ => rfl)
    retainedLaw retainedLaw_invariant [⟨(), 42⟩, ⟨(), 42⟩, ⟨(), 42⟩]
  rw [coefficient]
  norm_num [retainedLaw, mass_add, mass_single, DDS.replies_ofFunction_iff, outsideDomain]

/-- Inconsistent replies on the repeated input cannot come from the retained draw. -/
lemma conflicting_reply_mass :
    retainedLaw.mass (fun g => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain 3))
      (DDS.ofFunction (insideDomain 3) (insideDomain_prefix 3)
        (fun b => ⟨b.1, g b.2⟩)).1))
      [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] [⟨(), 42⟩, ⟨(), 42⟩, ⟨(), 7⟩]) = 0 := by
  classical
  have coefficient := chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq
    labels 0 (insideDomain_prefix 3) (outsideDomain_prefix 3)
    (chronologicalLabelingProgram_isDDCFrom labels 0 3)
    (fun _ => (0 : Fin 2)) (fun _ : ℕ => (0 : Fin 2))
    [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] (fun _ _ _ _ => rfl)
    retainedLaw retainedLaw_invariant [⟨(), 42⟩, ⟨(), 42⟩, ⟨(), 7⟩]
  rw [coefficient]
  norm_num [retainedLaw, mass_add, mass_single, DDS.replies_ofFunction_iff, outsideDomain]

#print axioms chronologicalLabelingProgram_replies_iff_of_prefix_alignment
#print axioms chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq
#print axioms retainedLaw_invariant
#print axioms repeated_reply_mass
#print axioms conflicting_reply_mass

end Tests.ChronologicalSampling

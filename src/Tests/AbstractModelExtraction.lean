module

public import Commons.Definitions.AbstractModel.Extraction
public import Tests.AbstractModelConverter

/-!
# Extraction model checks

The existing Boolean register model is reused. The first submitted guess fixes the hidden
condition. A final guess is legal with zero ordinary commands, and overwriting the input
register does not replace the original secret in that condition.
-/

@[expose] public noncomputable section

namespace Tests.AbstractModelExtraction

open Commons.AbstractModel SystemAlgebra Probability
open Tests.AbstractModelConverter (model overwrite observe)

/-- No computation or observation constitutes a submitted guess. -/
example : model.submitted [overwrite, observe false] = none := rfl

/-- The condition remains true after extending a successful submission. -/
lemma first_submission :
    (model.extracted false).1 ([⟨.submit, false⟩, ⟨.submit, true⟩] : List (model.Command Bool)) :=
  (model.extracted (ι := Bool) false).2
    (List.prefix_append ([⟨.submit, false⟩] : List (model.Command Bool))
      [⟨.submit, true⟩]) rfl

/-- A later guess cannot replace the first one, even in an extension outside the legal domain. -/
example :
    ¬ (model.extracted true).1
      ([⟨.submit, false⟩, ⟨.submit, true⟩] : List (model.Command Bool)) := by
  change ¬ some false = some true
  simp only [Option.some.injEq, Bool.false_eq_true, not_false_eq_true]

/-- Submission is separate from the ordinary-query allowance, including allowance zero. -/
lemma zero_query_extraction :
    model.Admitted false 0 [⟨.submit, false⟩] ∧
      (model.extracted false).1 ([⟨.submit, false⟩] : List (model.Command Bool)) := by
  refine ⟨?_, rfl⟩
  apply (admitted_snoc_iff false 0 [] ⟨.submit, false⟩).mpr
  simp [ordinary, reads]

/-- `overwrite` changes the stored bit to true, while success still tests the original false. -/
lemma original_secret_after_overwrite :
    (model.extracted false).1 [overwrite, ⟨.submit, false⟩] ∧
      ¬ (model.extracted false).1 [overwrite, ⟨.submit, true⟩] := by
  refine ⟨rfl, ?_⟩
  change ¬ some true = some false
  simp only [Option.some.injEq, Bool.true_eq_false, not_false_eq_true]

/-- The full system accepts one joint finite law and retains it around both components. -/
example (D : Distribution.ProbDist (Unit × Bool)) :
    TypedSystem (model.interface false 0) :=
  model.extractionSystem false 0 D

#print axioms Commons.AbstractModel.extracted
#print axioms Commons.AbstractModel.extractionSystem
#print axioms first_submission
#print axioms zero_query_extraction
#print axioms original_secret_after_overwrite

end Tests.AbstractModelExtraction

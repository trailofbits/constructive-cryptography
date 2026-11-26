module

public import Commons.Definitions.GenericGroup.Affine.Laws
public import Tests.GenericGroupDense

/-!
# Affine dense-game presentation checks

The existing five-element dense model keeps its sampled secret after overwriting the input
register. Its affine presentation preserves the full system/condition pair. Tests also cover
a pending observation, the zero-allowance resource, and noninjective coefficient evaluation.
-/

@[expose] public noncomputable section

namespace Tests.GenericGroupAffine

open SystemAlgebra SystemAlgebra.DSL Commons.AbstractModel Commons.GenericGroup
open Probability Probability.Distribution Tests.GenericGroupDense

/-- Replace the initial register by the constant one, without changing the sampled secret. -/
def overwrite : model.Command Bool := ⟨.compute .one, (Fin.elim0, false)⟩

/-- The affine register converter calls the same observations after evaluation at `z.2`. -/
def affineVisible (z : Equiv.Perm (ZMod 5) × ZMod 5) :
    System (model.Command Bool) (Σ i, model.Output i) :=
  trim (apply (model.registersDDC false 2 affineOperate (1, 0)).1
    (relabel (model.observationsDDS 2 z.1).1
      (Sigma.map id (fun _ a => affineEvaluation z.2 ∘ a)) id))

/-- Lift the pointwise presentation at the actual joint draw, retaining its condition. -/
example :
    (model.extractionPDG false 2 (denseLaw (ZMod 5))).map (fun g => (g.1.1.1, g.1.2)) =
      (denseLaw (ZMod 5)).map (fun z => (affineVisible z, model.extracted z.2)) := by
  rw [extractionPDG, ProbDist.map_map]
  congr 1
  funext z
  exact Prod.ext (extractionDDS_eq_affine false 2 z.1 z.2) rfl

/-- Overwriting changes the register contents to one for every original secret. -/
example (π : Equiv.Perm (ZMod 5)) (x : ZMod 5) :
    model.registers (model.operate π) (initial false x) [overwrite] false = some 1 := by
  simp [registers, write, overwrite, Commons.AbstractModel.read,
    Commons.GenericGroup.operate, initial]

/-- The overwrite and terminal guess are legal on the unchanged command domain. -/
example : model.Admitted false 2 [overwrite, ⟨.submit, (0 : ZMod 5)⟩] := by
  apply (admitted_snoc_iff false 2 [overwrite] ⟨.submit, (0 : ZMod 5)⟩).mpr
  refine ⟨Or.inr ?_, ?_, ?_, ?_⟩
  · apply (admitted_snoc_iff false 2 [] overwrite).mpr
    simp [overwrite, ordinary, reads]
  · change (1 : ℕ) ≤ 2
    omega
  · simp [overwrite, ordinary]
  · exact Finset.empty_subset _

/-- The original zero secret still has its sampled mass after the register is overwritten. -/
lemma sampled_original_secret :
    (model.extractionPDG false 2 (denseLaw (ZMod 5))).1.mass
      (fun g => g.1.2.1 [overwrite, ⟨.submit, (0 : ZMod 5)⟩]) =
      1 / (Fintype.card (ZMod 5) : ℝ) := by
  calc
    _ = (denseLaw (ZMod 5)).1.mass (fun z => z.2 = 0) := by
      rw [extractionPDG, ProbDist.map_val, mass_fTransform]
      apply mass_congr
      intro z
      simp [extracted, submitted, overwrite, eq_comm]
    _ = _ := by
      rw [denseLaw, prodProbDist_val,
        mass_prod_snd _ _ (fun x : ZMod 5 => x = 0)]
      simp only [ProbDist.uniform, weight_uniform, one_mul, mass_singleton, uniform_apply]

/-- Before an inside reply, observing the input register emits its affine value `(1,0)`. -/
example : model.registerProgram false affineOperate (1, 0) [] (.query ())
    (fun _ => false) [] = .inr ⟨(), fun _ => ((1, 0) : ZMod 5 × ZMod 5)⟩ := by
  simp [registerProgram, callProg, registers, Commons.AbstractModel.read, initial]

/-- The fixed observation resource refuses a query when its allowance is zero. -/
example : (model.observationsDDS 0 (Equiv.refl (ZMod 5))).1
    [⟨(), fun _ => (0 : ZMod 5)⟩] = Part.none := by
  simp [observationsDDS, DDS.ofFunction]

/-- Evaluation at zero identifies different affine coefficients. -/
example : affineEvaluation (0 : ZMod 5) (0, 2) = affineEvaluation 0 (1, 2) := by
  simp only [affineEvaluation, mul_zero, zero_add]

#print axioms Commons.GenericGroup.affine_operate_map
#print axioms Commons.GenericGroup.extractionDDS_eq_affine
#print axioms sampled_original_secret

end Tests.GenericGroupAffine

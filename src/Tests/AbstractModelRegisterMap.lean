module

public import Commons.Definitions.AbstractModel.RegisterDDC.Laws
public import Tests.AbstractModelRegisters

/-!
# Register interpretation through the converter

The existing affine-register fixture is evaluated at zero, a noninjective map from integer
pairs to integers. Its converter keeps natural-number submissions unchanged. The same body
law covers an overwrite and missing operands, whose fallback is the initial value.
-/

@[expose] public section

namespace Tests.AbstractModelRegisterMap

open Commons.AbstractModel SystemAlgebra SystemAlgebra.DSL
open Tests.AbstractModel Tests.AbstractModelRegisters

/-- Affine evaluation at zero transports the whole converter, with allowance two. -/
lemma affine_converter :
    (model.registersDDC (0 : ℕ) 2 operate 0).1 =
      relabel (model.registersDDC (0 : ℕ) 2 operateAffine (1, 0)).1 id
        (insideMap (Sigma.map id (fun _ a => affineEvaluation 0 ∘ a))) := by
  apply model.registersDDC_relabel_of_map 0 2 operateAffine operate
    (affineEvaluation 0) (affine_operation 0) (1, 0) 0
  simp only [affineEvaluation, one_mul, add_zero]

/-- Overwriting the input register transports the subsequent observation call. -/
example (t : List ((Σ ρ, Fin (model.queryArity ρ) → ℤ × ℤ) ×
    (Σ ρ, model.Reply ρ))) :
    Sum.map id (Sigma.map id (fun _ a => affineEvaluation 0 ∘ a))
        (model.registerProgram 0 operateAffine (1, 0)
          [⟨.compute (), (fun _ => 0, 0)⟩] (.query false) (fun _ => 0) t) =
      model.registerProgram 0 operate 0 [⟨.compute (), (fun _ => 0, 0)⟩]
        (.query false) (fun _ => 0)
        (t.map (Prod.map (Sigma.map id (fun _ a => affineEvaluation 0 ∘ a)) id)) := by
  apply model.registerProgram_queryMap 0 operateAffine operate
    (affineEvaluation 0) (affine_operation 0) (1, 0) 0
  simp only [affineEvaluation, one_mul, add_zero]

/-- An uninitialized operand is replaced by the same interpreted initial value. -/
example :
    Sum.map id (Sigma.map id (fun _ a => affineEvaluation 0 ∘ a))
        (model.registerProgram 0 operateAffine (1, 0) [] (.query false) (fun _ => 7) []) =
      model.registerProgram 0 operate 0 [] (.query false) (fun _ => 7) [] := by
  apply model.registerProgram_queryMap 0 operateAffine operate
    (affineEvaluation 0) (affine_operation 0) (1, 0) 0
  simp only [affineEvaluation, one_mul, add_zero]

example : model.registerProgram 0 operate 0 [] (.query false) (fun _ => 7) [] =
    .inr ⟨false, fun _ => 0⟩ := by
  simp [registerProgram, callProg, registers, Commons.AbstractModel.read, initial]

/-- Submission still carries the original natural-number candidate `3`. -/
example : model.registerProgram 0 operateAffine (1, 0) [] .submit 3 [] =
    .inl ([submit], ()) := rfl

example : model.registerProgram 0 operate 0 [] .submit 3 [] =
    .inl ([submit], ()) := rfl

#print axioms Commons.AbstractModel.registerProgram_queryMap
#print axioms Commons.AbstractModel.registersDDC_relabel_of_map
#print axioms affine_converter

end Tests.AbstractModelRegisterMap

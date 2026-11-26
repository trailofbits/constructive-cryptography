module

public import Tests.AbstractModelConverter
public import Commons.Definitions.AbstractModel.ExtractionPresentation

/-!
# Internal values and arbitrary register names

The Boolean command model uses natural-number internal values and addresses. Computation
updates one shared register, submission still carries a Boolean guess, and the raw game
presentation accepts natural-number register names.
-/

@[expose] public noncomputable section

namespace Tests.AbstractModelRegisterPresentation

open Commons.AbstractModel SystemAlgebra SystemAlgebra.DSL Probability
open Tests.AbstractModelConverter

example (M : Commons.AbstractModel ℕ Unit) [Fintype M.Query]
    [∀ ρ, Fintype (M.Reply ρ)] : Interface := M.observationInterface Bool 2

/-- The internal computation increments its one natural-number operand. -/
def increment (_ : model.Operation) (values : Fin 1 → ℕ) : ℕ := values 0 + 1

/-- The command overwrites natural-number register zero using its current contents. -/
def overwriteNat : model.Command ℕ := ⟨.compute (), (fun _ => 0, 0)⟩

example : model.registerProgram 0 increment 0 [overwriteNat] (.query false)
    (fun _ => 0) [] = .inr ⟨false, fun _ => 1⟩ := by
  simp [registerProgram, callProg, registers, write, overwriteNat,
    Commons.AbstractModel.read, initial, increment]

example : model.registerProgram 0 increment 0 [] .submit true [] =
    .inl ([⟨.submit, true⟩], ()) := rfl

example : model.registerProgram 0 increment 0 [] (.query false)
    (fun _ => 9) [] = .inr ⟨false, fun _ => 0⟩ := by
  simp [registerProgram, callProg, registers, Commons.AbstractModel.read, initial]

/-- The raw certificate needs neither finite register names nor finite internal values. -/
lemma natural_register_domain :
    IsDDCFrom (fun xs => xs ≠ [] ∧ xs.length ≤ 2) (model.Admitted 0 2) 1
      (model.registersDDC 0 2 increment 0).1 :=
  (model.registersDDC 0 2 increment 0).2

example : Distribution.ProbDist
    {g : DDG (model.Command ℕ) (Σ i, model.Output i) //
      HasDomain (Domain.ofInputs (model.Admitted 0 2) 3 (fun _ h => h.length_le)) g.1.1} :=
  model.extractionPDG 0 2 (Distribution.ProbDist.single ((), false))

#print axioms natural_register_domain
#print axioms Commons.AbstractModel.extractionPDG

end Tests.AbstractModelRegisterPresentation

module

public import Commons.Definitions.AbstractModel.RegisterProgram.Laws
public import Tests.AbstractModel

/-!
# Register invocation with a stateful observation component

The existing model reads its initial value through an arbitrary deterministic inside component.
The result keeps that component's updated state and records the completed outside command.
-/

@[expose] public section

namespace Tests.RegisterProgramAttachment

open Commons.AbstractModel SystemAlgebra Tests.AbstractModel

/-- The query reads the actual initial register, then uses the inside component's own result. -/
theorem initial_query {R : Type}
    (stepR : R → (ρ : model.Query) → (Fin (model.queryArity ρ) → ℕ) → R × model.Reply ρ)
    (r : R) :
    (model.registerProgram 0 (model.operate 0) 7).combine stepR
        (model.registerProgram_bounded 0 (model.operate 0) 7)
        ([], r) (.query false) (fun _ => 0) =
      (([⟨.query false, fun _ => 0⟩], (stepR r false (fun _ => 7)).1),
        (stepR r false (fun _ => 7)).2) := by
  apply model.registerProgram_combine_query 0 (model.operate 0) 7 stepR [] false
    (fun _ => 0) (fun _ => 7)
  apply (read_eq_some_iff _ _ _).mpr
  intro j
  exact initial_self 0 7

#print axioms registerProgram_combine_query
#print axioms initial_query

end Tests.RegisterProgramAttachment

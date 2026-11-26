module

public import Commons.Definitions.AbstractModel.ObservationRefinement.Laws
public import Commons.Definitions.GenericGroup.Dense

/-!
# Two dense observations implement equality

The source model retains its Unit parameter. Adapter types also match the actual dense
model's permutation-parameter command families, since interpretation parameters are absent
from commands. Tests cover the first and pending second call, the final comparison, and
unchanged computation/submission forwarding.
-/

@[expose] public section

namespace Tests.ObservationRefinement

open Commons Commons.AbstractModel Commons.GenericGroup SystemAlgebra

/-- Equality observes the two operands directly; arithmetic is addition and insertion of 1. -/
abbrev equalityModel : AbstractModel Nat Unit where
  Operation := GenericGroup.Operation
  Query := Unit
  arity := operationArity
  queryArity _ := 2
  Reply _ := Bool
  operate _ := GenericGroup.operate
  evaluate _ _ values := values 0 == values 1

/-- Query both selected values and compare their dense labels. -/
noncomputable def compareValues := equalityModel.observationValueProgram
  (fun _ : Unit => 1) (fun _ => Nat) (fun _ => 2) (fun _ _ => ())
  (fun _ i _ => i) (fun _ ys => ys 0 == ys 1) (W := Nat)

/-- The same adapter on register names has the actual source and target command types. -/
noncomputable def compareCommands :
    Program Unit (Port equalityModel.Operation equalityModel.Query)
      (Port (denseModel Nat).Operation (denseModel Nat).Query)
      (equalityModel.Input Nat) equalityModel.Output
      ((denseModel Nat).Input Nat) (denseModel Nat).Output :=
  equalityModel.observationCommandProgram
    (fun _ : Unit => 1) (fun _ => Nat) (fun _ => 2) (fun _ _ => ())
    (fun _ i _ => i) (fun _ ys => ys 0 == ys 1)

example : compareValues () () ![7, 2] [] = .inr ⟨(), fun _ => 7⟩ := rfl

example : compareValues () () ![7, 2] [(⟨(), fun _ => 7⟩, ⟨(), 11⟩)] =
    .inr ⟨(), fun _ => 2⟩ := by
  simp only [compareValues, observationValueProgram, SystemAlgebra.DSL.collectCalls,
    SystemAlgebra.DSL.callProg, ↓reduceDIte]
  rfl

example : compareValues () () ![7, 2]
    [(⟨(), fun _ => 7⟩, ⟨(), 11⟩), (⟨(), fun _ => 2⟩, ⟨(), 11⟩)] =
    .inl ((), true) := by
  simp only [compareValues, observationValueProgram, SystemAlgebra.DSL.collectCalls,
    SystemAlgebra.DSL.callProg, SystemAlgebra.DSL.returnProg, ↓reduceDIte]
  rfl

example : compareCommands () (.compute .one) ((fun i => Fin.elim0 i), 3) [] =
    .inr ⟨.compute .one, ((fun i => Fin.elim0 i), 3)⟩ := rfl

example : compareCommands () .submit 7 [] = .inr ⟨.submit, 7⟩ := rfl

#print axioms observationValueProgram_costs
#print axioms observationValueProgram_next
#print axioms observationValueProgram_reply
#print axioms observationCommandProgram_costs
#print axioms observationCommandProgram_next
#print axioms observationCommandProgram_query_reply

end Tests.ObservationRefinement

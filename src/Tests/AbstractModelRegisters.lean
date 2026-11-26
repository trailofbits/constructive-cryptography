module

public import Commons.Definitions.AbstractModel.Registers.Laws
public import Tests.AbstractModel

/-!
# Register interpretation checks

The domain test model is reused with natural-number addresses and integer internal values.
Its computations add two internally. Tests cover a shared update, overwrite, undefined reads,
and the initialized-address invariant through a terminal submission.
-/

@[expose] public section

namespace Tests.AbstractModelRegisters

open Commons.AbstractModel Tests.AbstractModel

/-- Interpret the model's unary operation on integers by `v ↦ v + 2`. -/
def operate (_ : model.Operation) (values : Fin (model.arity ()) → ℤ) : ℤ :=
  values 0 + 2

/-- Initially address 0 contains 7; all other natural-number addresses are uninitialized. -/
def initialRegisters : ℕ → Option ℤ := initial 0 7

example : initialRegisters 0 = some 7 := initial_self 0 7

example : initialRegisters 7 = none := by
  simp only [initialRegisters, initial, Function.update_of_ne (by omega : (7 : ℕ) ≠ 0)]

example : read initialRegisters (fun _ : Fin 1 => 0) = some (fun _ => (7 : ℤ)) := by
  simp [Commons.AbstractModel.read, initialRegisters, initial]

example : read initialRegisters (fun _ : Fin 1 => 7) = none := by
  simp [Commons.AbstractModel.read, initialRegisters, initial]

/-- Both the stored value and its subsequent observation use the same register contents. -/
lemma stored_value : model.registers operate initialRegisters [store, observe] 7 = some 9 := by
  simp [registers, write, store, observe, Commons.AbstractModel.read, operate,
    initialRegisters, initial]

/-- Overwriting an initialized address replaces its value. -/
example : model.registers operate initialRegisters
    [⟨.compute (), (fun _ => 0, 0)⟩] 0 = some 9 := by
  simp [registers, write, Commons.AbstractModel.read, operate, initialRegisters, initial]

/-- An undefined operand leaves the computation's destination undefined. -/
example : model.write operate initialRegisters ⟨.compute (), (fun _ => 7, 0)⟩ 0 = none := by
  simp [write, Commons.AbstractModel.read, initialRegisters, initial]

/-- The generic invariant uses the actual domain certificate, including terminal submission. -/
lemma completed_initialized (i : ℕ) :
    (model.registers operate initialRegisters [store, observe, submit] i).isSome ↔
      i ∈ model.initialized 0 [store, observe, submit] :=
  registers_isSome operate initialRegisters 0 (initial_isSome 0 7)
    [store, observe, submit] complete_admitted.2.2.2 i

example : (model.registers operate initialRegisters [store, observe, submit] 7).isSome := by
  apply (completed_initialized 7).mpr
  simp [initialized, store, observe, submit, target]

example : ¬ (model.registers operate initialRegisters [store, observe, submit] 8).isSome := by
  rw [completed_initialized]
  simp [initialized, store, observe, submit, target]

#print axioms stored_value
#print axioms completed_initialized
#print axioms Commons.AbstractModel.initial_self
#print axioms Commons.AbstractModel.initial_isSome
#print axioms Commons.AbstractModel.read_isSome
#print axioms Commons.AbstractModel.registers_snoc
#print axioms Commons.AbstractModel.initialized_snoc
#print axioms Commons.AbstractModel.registers_isSome

end Tests.AbstractModelRegisters

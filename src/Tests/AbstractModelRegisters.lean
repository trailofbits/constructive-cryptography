module

public import Commons.Definitions.AbstractModel.Registers.Laws
public import Tests.AbstractModel
public import Mathlib.Algebra.Ring.Int.Defs

/-!
# Register interpretation checks

The domain test model is reused with natural-number addresses and integer internal values.
Its computations add two internally. Tests cover a shared update, overwrite, undefined reads,
and the initialized-address invariant through a terminal submission.
Affine evaluation also transports these commands from integer pairs to integers, including
at a noninjective evaluation point, after overwrites, and when an operand is missing.
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

/-- The pair `(a,b)` represents the affine expression `a*x+b` at the fixed integer `x`. -/
def affineEvaluation (x : ℤ) (p : ℤ × ℤ) : ℤ := p.1 * x + p.2

/-- Adding two to an affine expression changes only its constant coefficient. -/
def operateAffine (_ : model.Operation) (values : Fin (model.arity ()) → ℤ × ℤ) : ℤ × ℤ :=
  ((values 0).1, (values 0).2 + 2)

/-- Affine evaluation preserves the model's chosen internal operation. -/
lemma affine_operation (x : ℤ) (o : model.Operation)
    (values : Fin (model.arity o) → ℤ × ℤ) :
    operate o (affineEvaluation x ∘ values) =
      affineEvaluation x (operateAffine o values) := by
  change (values 0).1 * x + (values 0).2 + 2 =
    (values 0).1 * x + ((values 0).2 + 2)
  exact add_assoc _ _ _

/-- Evaluating at zero identifies different affine expressions. -/
example : affineEvaluation 0 (0, 7) = affineEvaluation 0 (1, 7) := by
  simp only [affineEvaluation, mul_zero, zero_add]

/-- The same computation, observation and natural-number submission transport as one history. -/
lemma affine_history (x : ℤ) :
    model.registers operate (initial 0 x) [store, observe, submit] =
      Option.map (affineEvaluation x) ∘
        model.registers operateAffine (initial 0 (1, 0)) [store, observe, submit] := by
  have start := initial_map (affineEvaluation x) (0 : ℕ) (1, 0)
  have initial_value : affineEvaluation x (1, 0) = x := by
    simp only [affineEvaluation, one_mul, add_zero]
  rw [initial_value] at start
  rw [start]
  exact registers_map operateAffine operate (affineEvaluation x) (affine_operation x) _ _

/-- At the noninjective point zero, the concrete destination still contains the value two. -/
example : model.registers operate (initial 0 0) [store, observe, submit] 7 = some 2 := by
  rw [affine_history]
  simp [Function.comp_apply, registers, write, store, observe, submit,
    Commons.AbstractModel.read, operateAffine, initial, affineEvaluation]

/-- Interpretation also commutes with overwriting the initially occupied address. -/
example :
    model.write operate (Option.map (affineEvaluation 0) ∘ initial 0 (1, 0))
        ⟨.compute (), (fun _ => 0, 0)⟩ =
      Option.map (affineEvaluation 0) ∘
        model.write operateAffine (initial 0 (1, 0)) ⟨.compute (), (fun _ => 0, 0)⟩ :=
  write_map operateAffine operate (affineEvaluation 0) (affine_operation 0) _ _

/-- Reading an uninitialized address stays undefined after interpretation. -/
example : read (Option.map (affineEvaluation 0) ∘ initial 0 (1, 0))
    (fun _ : Fin 1 => 7) = none := by
  rw [read_map]
  simp [Commons.AbstractModel.read, initial]

#print axioms stored_value
#print axioms completed_initialized
#print axioms Commons.AbstractModel.initial_self
#print axioms Commons.AbstractModel.initial_isSome
#print axioms Commons.AbstractModel.read_isSome
#print axioms Commons.AbstractModel.registers_snoc
#print axioms Commons.AbstractModel.initialized_snoc
#print axioms Commons.AbstractModel.registers_isSome
#print axioms Commons.AbstractModel.read_map
#print axioms Commons.AbstractModel.initial_map
#print axioms Commons.AbstractModel.write_map
#print axioms Commons.AbstractModel.registers_map
#print axioms affine_operation
#print axioms affine_history

end Tests.AbstractModelRegisters

module

public import Tests.AbstractModelRegisters

/-!
# Register address embeddings

The existing model's natural-number registers are shifted by five. Its initial value moves
from address zero to five. A computation stores at address twelve, which is never read;
another computation overwrites the input register. The submission remains the value three.
-/

@[expose] public section

namespace Tests.AbstractModelAddressMap

open Commons.AbstractModel Tests.AbstractModel Tests.AbstractModelRegisters

/-- Embed natural-number register addresses by `d(n) = n + 5`. -/
def shift : ℕ ↪ ℕ := ⟨fun n => n + 5, fun _ _ h => Nat.add_right_cancel h⟩

/-- Add two to the current input register and overwrite that same address. -/
def overwrite : model.Command ℕ := ⟨.compute (), (fun _ => 0, 0)⟩

example : initial (shift 0) (7 : ℤ) (shift 0) = some 7 := initial_self _ _

example : shift 0 = 5 := rfl

example : model.mapCommand shift store =
    ⟨.compute (), (fun _ => 5, 12)⟩ := rfl

example : model.mapCommand shift observe = ⟨.query false, fun _ => 12⟩ := rfl

example : model.mapCommand shift submit = submit := rfl

/-- The complete renamed history retains both the overwritten input and never-read destination. -/
lemma history_embedding :
    model.registers operate (initial (shift 0) 7)
        ([store, overwrite, submit].map (model.mapCommand shift)) ∘ shift =
      model.registers operate (initial 0 7) [store, overwrite, submit] := by
  rw [registers_mapCommand, initial_comp_embedding]

/-- Overwriting address zero becomes overwriting the nonzero address five. -/
example : model.registers operate (initial (shift 0) 7)
    ([store, overwrite, submit].map (model.mapCommand shift)) 5 = some 9 := by
  have transported := congrFun history_embedding 0
  change model.registers operate (initial (shift 0) 7)
    ([store, overwrite, submit].map (model.mapCommand shift)) 5 = _ at transported
  rw [transported]
  simp [registers, write, store, overwrite, submit, Commons.AbstractModel.read,
    AbstractModelRegisters.operate, initial]

/-- The never-read destination is still renamed and retains its stored value. -/
example : model.registers operate (initial (shift 0) 7)
    ([store, overwrite, submit].map (model.mapCommand shift)) 12 = some 9 := by
  have transported := congrFun history_embedding 7
  change model.registers operate (initial (shift 0) 7)
    ([store, overwrite, submit].map (model.mapCommand shift)) 12 = _ at transported
  rw [transported]
  simp [registers, write, store, overwrite, submit, Commons.AbstractModel.read,
    AbstractModelRegisters.operate, initial]

#print axioms read_comp
#print axioms initial_comp_embedding
#print axioms write_mapCommand
#print axioms registers_mapCommand
#print axioms history_embedding

end Tests.AbstractModelAddressMap

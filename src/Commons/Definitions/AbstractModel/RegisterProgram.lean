module

public import Commons.Definitions.AbstractModel.Registers
public import RandomSystems.Typed.DSL.Programs

/-!
# Register commands as a program

`registerProgram` stores only the completed command history. It computes register contents
with `registers`, returns immediately on computation or submission, and makes one observation
call on a query. `observationCost` counts that call. The interpretation `op` and initial value `w`
fix internal values. Outside commands and submitted guesses retain the model's types.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
  -- `M` fixes external commands and replies; `W` carries internal values, and `ι` names registers.
  {S P W ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- `registerProgram` returns on compute/submit and calls `ρ(read(registers h,a))` on query.
Missing reads are totalized by the initial `w`; admitted commands have initialized operands. -/
noncomputable def registerProgram
    -- `input` initially contains `w`; `op` interprets computations on internal values `W`.
    (input : ι) (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W) :
    Program (List (M.Command ι)) (Port M.Operation M.Query) M.Query
      (M.Input ι) M.Output (fun ρ => Fin (M.queryArity ρ) → W) M.Reply :=
  fun h i u => match i with
  | .compute o => returnProg (h ++ [⟨.compute o, u⟩], ())
  | .query ρ =>
      callProg ρ ((read (M.registers op (initial input w) h) u).getD (fun _ => w))
        (fun y => returnProg (h ++ [⟨.query ρ, u⟩], y))
  | .submit => returnProg (h ++ [⟨.submit, u⟩], ())

/-- Observations cost one inside call; computations and terminal submissions cost zero. -/
def observationCost : M.Command ι → ℕ
  | ⟨.query _, _⟩ => 1
  | _ => 0

end Commons.AbstractModel

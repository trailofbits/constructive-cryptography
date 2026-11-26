module

public import Commons.Definitions.AbstractModel.Registers
public import RandomSystems.Typed.DSL.Programs

/-!
# Register commands as a program

`registerProgram` stores only the completed command history. It computes register contents
with `registers`, returns immediately on computation or submission, and makes one observation
call on a query. `observationCost` counts that call. The fixed parameters `p,x` belong to the
surrounding retained sample, not to separately sampled program state.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
  -- `M` supplies operations on `S`; `ι` gives register names without a finiteness requirement.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- `registerProgram` returns on compute/submit and calls `ρ(read(registers h,a))` on query.
Missing reads are totalized by the retained `x`; admitted commands have initialized operands. -/
noncomputable def registerProgram
    -- `input` initially contains `x`; `p` fixes the operation interpretation.
    (input : ι) (p : P) (x : S) :
    Program (List (M.Command ι)) (Port M.Operation M.Query) M.Query
      (M.Input ι) M.Output (fun ρ => Fin (M.queryArity ρ) → S) M.Reply :=
  fun h i u => match i with
  | .compute o => returnProg (h ++ [⟨.compute o, u⟩], ())
  | .query ρ =>
      callProg ρ ((read (M.registers (M.operate p) (initial input x) h) u).getD (fun _ => x))
        (fun y => returnProg (h ++ [⟨.query ρ, u⟩], y))
  | .submit => returnProg (h ++ [⟨.submit, u⟩], ())

/-- Observations cost one inside call; computations and terminal submissions cost zero. -/
def observationCost : M.Command ι → ℕ
  | ⟨.query _, _⟩ => 1
  | _ => 0

end Commons.AbstractModel

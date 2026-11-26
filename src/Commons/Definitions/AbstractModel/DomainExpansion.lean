module

public import Commons.Definitions.AbstractModel

/-!
# A fold presentation of command admission

`admissionUpdate` accumulates initialized addresses and permission to continue.
`admissionAllowed` checks that permission and the next command's reads. Their scan
characterizes the existing `Admitted` predicate in `DomainExpansion.Laws`.
-/

@[expose] public section

namespace Commons.AbstractModel

variable
    -- `M` has submitted values `S` and parameters `P`; `ι` names its registers.
    {S P ι : Type} (M : AbstractModel S P) [DecidableEq ι]

/-- Insert a computation destination and keep permission to continue exactly while commands
remain ordinary. The pair contains initialized addresses and permission for another command. -/
def admissionUpdate (state : Finset ι × Bool) (z : M.Command ι) : Finset ι × Bool :=
  ((M.target z).elim state.1 (fun i => insert i state.1), state.2 && M.ordinary z)

/-- A command is allowed when execution may continue and every operand is initialized. -/
def admissionAllowed (state : Finset ι × Bool) (z : M.Command ι) : Prop :=
  state.2 = true ∧ M.reads z ⊆ state.1

end Commons.AbstractModel

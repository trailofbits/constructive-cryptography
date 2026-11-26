module

public import Commons.Definitions.AbstractModel.Interface
public import Commons.Definitions.AbstractModel.RegisterProgram.Laws
public import RandomSystems.Typed.DSL.Converters

/-!
# The register converter

`registersConverter` connects commands on register names to observations on their current
values. Its state is the completed command history, and its domain is exactly `Admitted`.
The existing costed-program constructor counts a pending observation before its reply arrives.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `M` interprets values `S` at parameters `P`; `ι` names the finite registers.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  [Fintype S] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
  [∀ ρ, Fintype (M.Reply ρ)]

/-- The command history starts empty; `input` contains `x`, and operations use retained `p`.
Computations and submission return directly; each observation queries its current operands. -/
noncomputable def registersConverter (input : ι) (k : ℕ) (p : P) (x : S) :
    TypedConverter (M.interface input k) (M.observationInterface k) :=
  TypedConverter.ofCostedProgram [] (M.registerProgram input p x)
    (M.registerProgram_bounded input p x) M.observationCost
    (M.registerProgram_costs input p x) (M.observationCost_sum_le input k)
    (fun _ hne hlen => ⟨hne, hlen⟩)

end Commons.AbstractModel

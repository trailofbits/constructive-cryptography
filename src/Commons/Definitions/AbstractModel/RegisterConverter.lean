module

public import Commons.Definitions.AbstractModel.Interface
public import Commons.Definitions.AbstractModel.RegisterDDC
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
  {S P W ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  [Fintype S] [Fintype W] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
  [∀ ρ, Fintype (M.Reply ρ)]

/-- The command history starts empty; `input` contains `w`, and operations use `op`.
Computations and submission return directly; each observation queries its current operands. -/
noncomputable def registersConverter (input : ι) (k : ℕ)
    -- `W` carries internal values; `op` and `w` fix their interpretation and initial value.
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W) :
    TypedConverter (M.interface input k) (M.observationInterface W k) :=
  TypedConverter.ofDDC (M.registersDDC input k op w).1 (M.registersDDC input k op w).2

end Commons.AbstractModel

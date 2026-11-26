module

public import Commons.Definitions.AbstractModel.RegisterProgram.Laws

/-!
# The register program's domain certificate

`registersDDC` connects commands on arbitrary register names to observations on internal
values. The exact 0/1/0 observation costs certify the original command domain.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `M` fixes external commands and replies; `W` carries internal values, and `ι` names registers.
  {S P W ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- The completed-history program admits `Admitted input k` and makes at most `k` observations. -/
noncomputable def registersDDC
    -- `input` starts with `w`; `op` interprets computations on internal values `W`.
    (input : ι) (k : ℕ)
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W) :
    {a : InsideOutsideSystem (Port M.Operation M.Query) M.Query
      (M.Input ι) M.Output (fun ρ => Fin (M.queryArity ρ) → W) M.Reply //
      IsDDCFrom (fun xs => xs ≠ [] ∧ xs.length ≤ k) (M.Admitted input k) 1 a} :=
  ⟨DDC.ofProgramOn [] (M.registerProgram input op w) (M.Admitted input k),
    DDC.ofProgramOn_isDDCFrom_of_costs (M.registerProgram_bounded input op w)
      (fun hp hne hh => hh.prefix hp hne) (M.registerProgram_costs input op w)
      (M.observationCost_sum_le input k) (fun _ hne hlen => ⟨hne, hlen⟩)⟩

end Commons.AbstractModel

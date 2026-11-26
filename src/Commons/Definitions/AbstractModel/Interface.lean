module

public import Commons.Definitions.AbstractModel.Domain
public import RandomSystems.Typed.Interface
public import Mathlib.Tactic.DeriveFintype

/-!
# Interfaces of an abstract computation model

`interface M ι input k` exposes the model's computations, observations and terminal submission
on its initialized-register domain. `observationInterface M W k` accepts at most `k` queries on
actual values. The register converter connects these interfaces; only this typed boundary
requires finite alphabets.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

deriving instance Fintype for Port

section Commands

variable
  -- `M` interprets operations on `S` at parameters `P`; `ι` names the finite registers.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  [Fintype S] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
  [∀ ρ, Fintype (M.Reply ρ)]

/-- Computations and observations share `k` ordinary commands; a final submission is separate. -/
def interface (input : ι) (k : ℕ) : Interface where
  I := Port M.Operation M.Query
  X := M.Input ι
  Y := M.Output
  instFintypeX i := by cases i <;> dsimp [Input] <;> infer_instance
  instFintypeY i := by cases i <;> dsimp [Output] <;> infer_instance
  domain := M.Admitted input k
  nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne hh => hh.prefix hp hne⟩
  bound := k + 1
  length_le _ hh := hh.length_le

end Commands

variable
  -- `M` supplies observation ports and replies; the submitted-value carrier `S` is arbitrary.
  {S P : Type} (M : Commons.AbstractModel S P)
  [Fintype M.Query] [∀ ρ, Fintype (M.Reply ρ)]

/-- Each `ρ(a)` observes the tuple of values `a`; at most `k` such calls are admitted. -/
abbrev observationInterface
    -- `W` carries the finite internal values supplied to each observation.
    (W : Type) [Fintype W] (k : ℕ) : Interface :=
  Interface.queryBudget M.Query (fun ρ => Fin (M.queryArity ρ) → W) M.Reply k

end Commons.AbstractModel

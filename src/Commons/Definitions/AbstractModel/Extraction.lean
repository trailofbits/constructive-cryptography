module

public import Commons.Definitions.AbstractModel.RegisterConverter
public import RandomSystems.Typed.Functional
public import RandomSystems.Game.DiscreteMBO

/-!
# Extraction in an abstract computation model

`observationsDDS` and its typed form `observations` evaluate the model's queries at a fixed
parameter. `extractionSystem` retains
one joint draw `(p,x)` and attaches the register converter to those observations.
`submitted` selects the first terminal guess; `extracted x` marks equality with the original
secret, as in [1, Figure 1 and Definition 7, p. 8].

```text
           ┌──────── retained (p,x) ← D ────────┐
commands ──► registersConverter (M.operate p) x ─► observations p
           └──────────────────────────────────┘
                    first submitted guess = x
```

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.AbstractModel

open Probability SystemAlgebra

variable
  -- `M` supplies commands with values in `S` and parameters in `P`; `ι` names registers.
  {S P ι : Type} (M : Commons.AbstractModel S P)

/-- The first submitted value in `h`, or `none` before any submission. -/
def submitted (h : List (M.Command ι)) : Option S :=
  h.findSome? fun z => match z with
    | ⟨.submit, guess⟩ => some guess
    | ⟨.compute _, _⟩ => none
    | ⟨.query _, _⟩ => none

/-- `extracted x h` means `submitted h = some x`: "The game is won if x' = x"
[1, Figure 1, p. 8]. The first guess stays fixed under extension. -/
def extracted
    -- `x` is the original secret; overwriting a register leaves this success condition unchanged.
    (x : S) : MC (M.Command ι) :=
  ⟨fun h => M.submitted h = some x,
    fun {_ _} pre reached => pre.findSome?_eq_some reached⟩

/-- At most `k` observations, each replying `M.evaluate p ρ a` at its queried port.
This is the deterministic presentation of `observations`, before finite typed packaging. -/
noncomputable def observationsDDS
    -- `k` bounds observations; `p` fixes their interpretation, with arbitrary value/reply types.
    (k : ℕ) (p : P) : DDS (Σ ρ, Fin (M.queryArity ρ) → S) (Σ ρ, M.Reply ρ) :=
  DDS.ofFunction (fun xs => xs ≠ [] ∧ xs.length ≤ k)
    ⟨fun h => h.1 rfl, fun hp hne hh => ⟨hne, hp.length_le.trans hh.2⟩⟩
    (fun v => ⟨v.1, M.evaluate p v.1 v.2⟩)

variable [Fintype S] [Fintype M.Query] [∀ ρ, Fintype (M.Reply ρ)]

/-- At query `ρ(a)`, reply with `M.evaluate p ρ a`: "the result output to the user"
[1, §3.1, p. 7]. The domain allows at most `k` observations. -/
noncomputable def observations
    -- `k` bounds observation calls; `p` fixes the model's observation functions.
    (k : ℕ) (p : P) : TypedSystem (M.observationInterface S k) :=
  TypedSystem.ofFunction (M.evaluate p)

variable [DecidableEq ι] [Fintype ι] [Fintype M.Operation]

/-- Draw `(p,x) ← D` once and retain `registersConverter (M.operate p) x • observations p`
[1, Figure 1, p. 8]. There are at most `k` ordinary commands and one terminal submission. -/
noncomputable def extractionSystem
    -- `input` initially contains `x`; `k` counts computations and observations together.
    (input : ι) (k : ℕ)
    -- `D` is the joint law of parameter `p` and secret `x`, with arbitrary dependence.
    (D : Distribution.ProbDist (P × S)) : TypedSystem (M.interface input k) :=
  TypedSystem.sample D.1 fun z =>
    M.registersConverter input k (M.operate z.1) z.2 • M.observations k z.1

end Commons.AbstractModel

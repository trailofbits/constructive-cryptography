module

public import Commons.Definitions.AbstractModel.ExtractionGame
public import Probability.Kernel
public import Mathlib.Data.Fintype.Perm

/-!
# Dense generic-group extraction

`denseModel` instantiates `AbstractModel` with addition, insertion of `1`, and the observation
`π(v)` through one retained permutation. Its source specialization is `F = ZMod N`
[1, Definition 10, p. 10]. Register storage, legal commands, and terminal extraction use the
existing abstract-model assembly.

`denseLaw` samples an independent uniform permutation and secret. `denseGame` supplies this
law to `extractionGame`; its `k` ordinary calls precede the separate terminal submission.
Arbitrary joint laws use `(denseModel F).extractionGame input k D`.

```text
                    retained (π,x) ← denseLaw F
commands ── registers(initial x, +,1) ── observation v ↦ π(v)
     └──────── terminal guess x' ────── success iff x'=original x
```

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.GenericGroup

open Probability Probability.Distribution SystemAlgebra

/-- Computation symbols `Π = {+, 1}` [1, Definition 5, p. 7]. -/
inductive Operation where
  /-- Read two registers and store their sum. -/
  | add
  /-- Store `1` without reading an operand register. -/
  | one
  deriving DecidableEq

/-- The two computation symbols form a finite alphabet. -/
instance : Fintype Operation := Fintype.ofEquiv Bool
  { toFun := fun b => if b then .add else .one
    invFun := fun | .add => true | .one => false
    left_inv := by intro b; cases b <;> rfl
    right_inv := by intro o; cases o <;> rfl }

/-- Addition has two operands; insertion of `1` is nullary. The destination is separate. -/
abbrev operationArity : Operation → ℕ
  | .add => 2
  | .one => 0

/-- Interpret the symbols by `add(a,b)=a+b` and `one()=1`. -/
def operate
    -- `F` carries register values with the selected addition and constant `1`.
    {F : Type} [Add F] [One F] : (o : Operation) → (Fin (operationArity o) → F) → F
  | .add, values => values 0 + values 1
  | .one, _ => 1

/-- Dense observations return `π(v)` [1, §4, p. 9]: "returns π(v)".
The parameter `π` leaves arithmetic unchanged and interprets the single observation query. -/
abbrev denseModel
    -- `F` carries values and labels; a parameter `π : Equiv.Perm F` encodes those values.
    (F : Type) [Add F] [One F] : Commons.AbstractModel F (Equiv.Perm F) where
  Operation := Operation
  Query := Unit
  arity := operationArity
  queryArity _ := 1
  Reply _ := F
  operate _ := operate
  evaluate π _ values := π (values 0)

open Classical in
/-- One uniform permutation and one independent uniform secret:
`denseLaw F = 𝒰[Perm F] × 𝒰[F]`. This is the "uniform distribution on V = P × S"
of [1, Definition 8, p. 8]. -/
noncomputable def denseLaw
    -- `F` is the finite nonempty secret and dense-label alphabet.
    (F : Type) [Fintype F] [Nonempty F] : ProbDist (Equiv.Perm F × F) :=
  prodProbDist 𝒰[Equiv.Perm F] 𝒰[F]

/-- The average-case game is `extractionGame` at `denseLaw F` [1, Definitions 8 and 10,
pp. 8, 10]. It retains `(π,x)`, initializes `input` with `x`, and tests the terminal guess. -/
noncomputable def denseGame
    -- `F` carries the register values; finite `ι` names the available registers.
    (F : Type) [Add F] [One F] [Fintype F]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    -- `input` initially stores the secret; `k` counts computations and observations together.
    (input : ι) (k : ℕ) : TypedGame ((denseModel F).interface input k) :=
  letI : Nonempty F := ⟨1⟩
  (denseModel F).extractionGame input k (denseLaw F)

end Commons.GenericGroup

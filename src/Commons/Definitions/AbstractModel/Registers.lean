module

public import Commons.Definitions.AbstractModel
public import Mathlib.Logic.Function.Basic

/-!
# Register interpretation of abstract commands

`initial input x` stores `x` only at `input`. `read r a` obtains the operand tuple from
registers `a`, returning `none` if an operand is uninitialized. `write` applies one computation
and `registers` folds these updates over completed commands. Queries and submissions preserve
register contents. The internal carrier `W` and register names `ι` are arbitrary.

This interprets the destination rule of [1, §3.1, p. 7]: "the result is stored in the register".
`AbstractModel.Registers.Laws` identifies the initialized addresses along legal histories.

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.AbstractModel

variable
  -- `ι` names registers; `W` carries their internal values. Neither carrier must be finite.
  {ι W : Type}

/-- `initial input x` stores `some x` at `input` and `none` at every other address. -/
def initial [DecidableEq ι] (input : ι) (x : W) : ι → Option W :=
  Function.update (fun _ => none) input (some x)

/-- `read r a` is the tuple `(r(a₁),…,r(aₙ))` when all operands are initialized, else `none`. -/
def read
    -- `r` gives optional register values; `a` selects the `n` operand addresses.
    (r : ι → Option W) {n : ℕ} (a : Fin n → ι) : Option (Fin n → W) :=
  if h : ∀ j, (r (a j)).isSome then some fun j => (r (a j)).get (h j) else none

variable
  -- `M` supplies the command arities and external submitted values `S`.
  {S P : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  -- `operate o` interprets `M`'s operation `o` on internal values `W`, at a fixed parameter.
  (operate : (o : M.Operation) → (Fin (M.arity o) → W) → W)

/-- A computation writes `operate o` of its read operands to its destination; other commands
preserve `r`. An undefined operand gives an undefined destination. -/
def write
    -- `r` gives the current contents; the command supplies operands and destination.
    (r : ι → Option W) : M.Command ι → ι → Option W
  | ⟨.compute o, (a, t)⟩ => Function.update r t ((read r a).map (operate o))
  | ⟨.query _, _⟩ => r
  | ⟨.submit, _⟩ => r

/-- `registers M operate r h = h.foldl (write M operate) r`: contents after commands `h`. -/
def registers
    -- `r` gives the initial contents; `h` lists completed commands in their execution order.
    (r : ι → Option W) (h : List (M.Command ι)) : ι → Option W :=
  h.foldl (M.write operate) r

end Commons.AbstractModel

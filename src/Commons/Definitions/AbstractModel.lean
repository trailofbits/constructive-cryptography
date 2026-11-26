module

public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Dedup

/-!
# Abstract models of computation

`AbstractModel` gives computation operations and observable functions over a carrier `S`,
interpreted at a parameter `p : P`. Computation stores a result in a selected register;
queries return an observation; submission supplies a guess [1, §3.1 and Figure 1, pp. 7–8].

`Port.Input` and `Port.Output` give these commands their alphabets from their signature;
`Input` and `Output` instantiate them at a model. `Admitted input k`
allows at most `k` ordinary commands and one terminal submission, with every read referring
to an initialized register. Registers have arbitrary names `ι`; `input : ι` names the one
initially populated register. The domain certificates are in `AbstractModel.Domain`.

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons

/-- Operations and observations interpreted at `p : P`; [1, §3.1, p. 7] adds
"a set P of possible parameter values" to the computation model. -/
structure AbstractModel
    -- `S` carries register values and submitted guesses; `P` carries model parameters.
    (S P : Type) where
  /-- `Operation` indexes computation operations, each storing one result. -/
  Operation : Type
  /-- `Query` indexes observable functions. -/
  Query : Type
  /-- `arity o` counts operand registers, excluding parameter `p` and the destination. -/
  arity : Operation → ℕ
  /-- `queryArity ρ` counts operand registers, excluding parameter `p`. -/
  queryArity : Query → ℕ
  /-- `Reply ρ` carries the observation returned by query `ρ`. -/
  Reply : Query → Type
  /-- `operate p o v` is the value stored after applying `o` to operand tuple `v`. -/
  operate : P → (o : Operation) → (Fin (arity o) → S) → S
  /-- `evaluate p ρ v` is the observation returned for operand tuple `v`. -/
  evaluate : P → (ρ : Query) → (Fin (queryArity ρ) → S) → Reply ρ

namespace AbstractModel

/-- Named commands: compute with `o`, observe with `ρ`, or submit a guessed value. -/
inductive Port (Operation Query : Type) where
  /-- Apply `o` to selected registers and store its result. -/
  | compute (o : Operation)
  /-- Return the observation selected by `ρ`. -/
  | query (ρ : Query)
  /-- Submit the candidate for the initially stored secret. -/
  | submit
  deriving DecidableEq

namespace Port

variable {Operation Query : Type}

/-- Computations give operand addresses and a destination; queries give operand addresses;
submissions give a value. These input families depend only on the command signature. -/
abbrev Input
    -- `S` carries submitted guesses; `ι` names registers.
    (S ι : Type)
    -- `arity o` and `queryArity ρ` count the selected operand addresses.
    (arity : Operation → ℕ) (queryArity : Query → ℕ) : Port Operation Query → Type
  | .compute o => (Fin (arity o) → ι) × ι
  | .query ρ => Fin (queryArity ρ) → ι
  | .submit => S

/-- Computations and submissions return unit; query `ρ` returns a value of `Reply ρ`. -/
abbrev Output
    -- `Reply` supplies the observation reply family, independently of its interpretation.
    (Reply : Query → Type) : Port Operation Query → Type
  | .compute _ => Unit
  | .query ρ => Reply ρ
  | .submit => Unit

end Port

variable
  -- `M` supplies the operations, arities and reply types on values `S` at parameters `P`.
  {S P : Type} (M : AbstractModel S P)
  -- `ι` names registers; it need not be finite.
  (ι : Type)

/-- A computation gives operand addresses and a destination; a query gives operand addresses;
a submission gives a value. The destination is separate from `M.arity o` operands. -/
abbrev Input : Port M.Operation M.Query → Type :=
  Port.Input S ι M.arity M.queryArity

/-- Computations and submissions acknowledge with `()`; query `ρ` returns `M.Reply ρ`. -/
abbrev Output : Port M.Operation M.Query → Type := Port.Output M.Reply

/-- A command pairs its named port with the input for that port. -/
abbrev Command := Σ i, M.Input ι i

variable {ι}

/-- `reads z` is the finite set of operand addresses of command `z`. -/
def reads [DecidableEq ι] : M.Command ι → Finset ι
  | ⟨.compute _, (a, _)⟩ => Finset.univ.image a
  | ⟨.query _, a⟩ => Finset.univ.image a
  | ⟨.submit, _⟩ => ∅

/-- `target z` is the destination of a computation; other commands write no register. -/
def target : M.Command ι → Option ι
  | ⟨.compute _, (_, t)⟩ => some t
  | ⟨.query _, _⟩ => none
  | ⟨.submit, _⟩ => none

/-- Both computation and query count as ordinary interactions; submission does not. -/
def ordinary : M.Command ι → Bool
  | ⟨.compute _, _⟩ => true
  | ⟨.query _, _⟩ => true
  | ⟨.submit, _⟩ => false

/-- `initialized input h` contains the initial address and every computation destination in `h`.
A destination may overwrite an initialized register [1, §3.1, p. 7]. -/
def initialized [DecidableEq ι]
    -- `input` names the initially populated register; `h` lists completed commands.
    (input : ι) (h : List (M.Command ι)) : Finset ι :=
  insert input (h.filterMap M.target).toFinset

/-- Legal histories allow "at most k computation operations Π and function queries Σ"
[1, Figure 1, p. 8], then a separate submission. Since only the input register is initialized,
legal reads require an earlier initialized address. -/
def Admitted [DecidableEq ι]
    -- `input` names the initial register; `k` bounds ordinary interactions, excluding submission.
    (input : ι) (k : ℕ)
    -- `h` is nonempty; a submission, if present, must be its last command.
    (h : List (M.Command ι)) : Prop :=
  h ≠ [] ∧ h.countP M.ordinary ≤ k ∧ (∀ z ∈ h.dropLast, M.ordinary z) ∧
    ∀ t z, t ++ [z] <+: h → M.reads z ⊆ M.initialized input t

end AbstractModel
end Commons

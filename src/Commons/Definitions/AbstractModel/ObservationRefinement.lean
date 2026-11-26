module

public import Commons.Definitions.AbstractModel
public import RandomSystems.Typed.DSL.Collect

/-!
# Observation schedules

`observationValueProgram` collects selected observations of one operand tuple.
`observationCommandProgram` uses the same schedule on register addresses and forwards
computations and submissions.
Both programs retain unit state. The command alphabets depend on operation and observation
signatures, so source and target model parameters may differ.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
    -- `M` fixes source commands on values `S`; `W` carries operands and `ι` names registers.
    {S P Q W ι : Type} (M : Commons.AbstractModel S P)
    -- `arity` and `Reply` describe target observations; model parameters are not consulted.
    (arity : Q → ℕ) (Reply : Q → Type)
    -- `n ρ` target queries implement source observation `ρ` in the given order.
    (n : M.Query → ℕ) (request : (ρ : M.Query) → Fin (n ρ) → Q)
    -- `select ρ i` chooses the source operands for target query number `i`.
    (select : (ρ : M.Query) → (i : Fin (n ρ)) →
      Fin (arity (request ρ i)) → Fin (M.queryArity ρ))
    -- `finish ρ` combines all target replies into the source reply.
    (finish : (ρ : M.Query) → ((i : Fin (n ρ)) → Reply (request ρ i)) → M.Reply ρ)

/-- Collect the selected target observations of `values` and return their combined reply. -/
noncomputable def observationValueProgram :
    Program Unit M.Query Q (fun ρ => Fin (M.queryArity ρ) → W) M.Reply
      (fun q => Fin (arity q) → W) Reply :=
  fun _ ρ values => collectCalls (n ρ)
    (fun i => ⟨request ρ i, values ∘ select ρ i⟩) (fun ys => ((), finish ρ ys))

/-- The complete target command schedule for one source command. -/
def observationCommandSchedule : M.Command ι →
    List (Σ i : Port M.Operation Q, Port.Input S ι M.arity arity i)
  | ⟨.compute o, u⟩ => [⟨.compute o, u⟩]
  | ⟨.query ρ, u⟩ => List.ofFn fun i => ⟨.query (request ρ i), u ∘ select ρ i⟩
  | ⟨.submit, u⟩ => [⟨.submit, u⟩]

/-- Computation and submission are forwarded once; observations use the selected schedule.
`Port.Input`/`Port.Output` keep computation and submission types while changing observations. -/
noncomputable def observationCommandProgram :
    Program Unit (Port M.Operation M.Query) (Port M.Operation Q) (M.Input ι) M.Output
      (Port.Input S ι M.arity arity) (Port.Output Reply) :=
  fun _ i u => match i with
  | .compute o => collectCalls 1 (fun _ => ⟨.compute o, u⟩) (fun _ => ((), ()))
  | .query ρ => collectCalls (n ρ)
      (fun i => ⟨.query (request ρ i), u ∘ select ρ i⟩) (fun ys => ((), finish ρ ys))
  | .submit => collectCalls 1 (fun _ => ⟨.submit, u⟩) (fun _ => ((), ()))

end Commons.AbstractModel

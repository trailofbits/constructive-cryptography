module

public import Commons.Definitions.AbstractModel.ObservationRefinement

/-!
# Local contracts for observation schedules

Each value invocation makes its scheduled calls in order and returns `finish` of their replies.
These are the local contracts used by the existing fixed-schedule domain certificate.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
    -- `M` gives source commands on submitted values `S` at parameters `P`; `W` carries operands.
    {S P Q W : Type} (M : Commons.AbstractModel S P)
    -- `arity` and `Reply` give the target observation input lengths and reply types.
    (arity : Q → ℕ) (Reply : Q → Type)
    -- `n ρ` counts target calls; `request ρ i` chooses the call at position `i`.
    (n : M.Query → ℕ) (request : (ρ : M.Query) → Fin (n ρ) → Q)
    -- `select ρ i` selects that target call's operands from the source operand tuple.
    (select : (ρ : M.Query) → (i : Fin (n ρ)) →
      Fin (arity (request ρ i)) → Fin (M.queryArity ρ))
    -- `finish ρ` combines the ordered target replies into one source observation.
    (finish : (ρ : M.Query) → ((i : Fin (n ρ)) → Reply (request ρ i)) → M.Reply ρ)

/-- Source observation `ρ` makes exactly `n ρ` target calls, including a pending call. -/
lemma observationValueProgram_costs :
    (M.observationValueProgram arity Reply n request select finish (W := W)).Costs
      (fun u => n u.1) := by
  intro s ρ values
  exact collectCalls_cost _ _ _

/-- The next target call selects the operands scheduled at the current exchange length. -/
lemma observationValueProgram_next (ρ : M.Query) (values : Fin (M.queryArity ρ) → W)
    (h) (q) (consistent :
      (M.observationValueProgram arity Reply n request select finish).Consistent () ρ values h)
    (issued : M.observationValueProgram arity Reply n request select finish () ρ values h =
      .inr q) :
    (List.ofFn fun i => (⟨request ρ i, values ∘ select ρ i⟩ :
      Σ q, Fin (arity q) → W))[h.length]? = some q :=
  collectCalls_next _ _ _ h q consistent issued

/-- Complete matching replies return the specified combination, preserving unit state. -/
lemma observationValueProgram_reply (ρ : M.Query) (values : Fin (M.queryArity ρ) → W)
    (ys : (i : Fin (n ρ)) → Reply (request ρ i)) :
    M.observationValueProgram arity Reply n request select finish () ρ values
      (List.ofFn fun i =>
        (⟨request ρ i, values ∘ select ρ i⟩, ⟨request ρ i, ys i⟩)) =
      .inl ((), finish ρ ys) :=
  collectCalls_reply (X := fun q => Fin (arity q) → W) (Y := Reply) (n ρ)
    (fun i => ⟨request ρ i, values ∘ select ρ i⟩) (fun ys => ((), finish ρ ys)) ys

/-- Each command makes exactly the number of calls in its complete schedule. -/
lemma observationCommandProgram_costs {ι : Type} :
    (M.observationCommandProgram arity Reply n request select finish (ι := ι)).Costs
      (fun z => (M.observationCommandSchedule arity n request select z).length) := by
  intro s i u
  cases i with
  | compute o => exact collectCalls_cost _ _ _
  | query ρ =>
    simp only [observationCommandSchedule, List.length_ofFn]
    exact collectCalls_cost _ _ _
  | submit => exact collectCalls_cost _ _ _

/-- Every issued target command is the next entry of the declared schedule. -/
lemma observationCommandProgram_next {ι : Type}
    (i : Port M.Operation M.Query) (u : M.Input ι i) (h) (q)
    (consistent :
      (M.observationCommandProgram arity Reply n request select finish).Consistent () i u h)
    (issued : M.observationCommandProgram arity Reply n request select finish () i u h =
      .inr q) :
    (M.observationCommandSchedule arity n request select ⟨i, u⟩)[h.length]? = some q := by
  cases i with
  | compute o =>
    simpa only [observationCommandSchedule, List.ofFn_succ, List.ofFn_zero] using
      collectCalls_next (X := Port.Input S ι M.arity arity) (Y := Port.Output Reply)
        1 (fun _ => ⟨.compute o, u⟩) (fun _ => ((), ())) h q consistent issued
  | query ρ => exact collectCalls_next _ _ _ h q consistent issued
  | submit =>
    simpa only [observationCommandSchedule, List.ofFn_succ, List.ofFn_zero] using
      collectCalls_next (X := Port.Input S ι M.arity arity) (Y := Port.Output Reply)
        1 (fun _ => ⟨.submit, u⟩) (fun _ => ((), ())) h q consistent issued

/-- A source query returns the same combination whether its operands are addresses or values. -/
lemma observationCommandProgram_query_reply {ι : Type}
    (ρ : M.Query) (addresses : Fin (M.queryArity ρ) → ι)
    (ys : (i : Fin (n ρ)) → Reply (request ρ i)) :
    M.observationCommandProgram arity Reply n request select finish () (.query ρ) addresses
      (List.ofFn fun i =>
        (⟨.query (request ρ i), addresses ∘ select ρ i⟩, ⟨.query (request ρ i), ys i⟩)) =
      .inl ((), finish ρ ys) :=
  collectCalls_reply (X := Port.Input S ι M.arity arity) (Y := Port.Output Reply) (n ρ)
    (fun i => ⟨.query (request ρ i), addresses ∘ select ρ i⟩)
    (fun ys => ((), finish ρ ys)) ys

end Commons.AbstractModel

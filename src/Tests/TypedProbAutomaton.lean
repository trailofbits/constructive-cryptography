module

public import RandomSystems.Typed.ProbAutomaton
public import RandomSystems.System.Memoryless

/-!
# Fresh transitions with a named state

`countingSource` retains a natural-number call count and draws a fresh fair bit at either
of its two ports. Its interface allows at most two queries in total. Forgetting the counter
simulates `ProbStep.fresh`: `countingSource_eq_fresh` discharges the simulation's
local invariant and kernel obligations. The two-reply calculation gives probability `1/4`
for every pair of bits, including different replies on repeated queries. Further exchanges
and replies at another port have probability zero.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution

namespace Tests.TypedProbAutomaton

/-- Two Boolean-labelled ports accept unit triggers and return bits, with two queries total. -/
abbrev countingInterface : Interface :=
  Interface.queryBudget Bool (fun _ => Unit) (fun _ => Bool) 2

/-- The retained state records the number of queries answered so far. -/
structure CountingState where
  /-- `calls` starts at zero and increases by one on either port. -/
  calls : ℕ

/-- At either port, draw `b ∼ 𝒰[Bool]`, increment `calls`, and reply `b`. -/
noncomputable def countingStep : ProbStep CountingState countingInterface.I
    countingInterface.X countingInterface.Y :=
  fun s _ _ => ProbDist.map (fun b => (CountingState.mk (s.calls + 1), b)) 𝒰[Bool]

/-- Start with zero calls; allow two queries total across both ports.
Each query draws a new fair bit and returns it at the queried port. -/
noncomputable def countingSource : TypedSystem countingInterface :=
  TypedSystem.ofProbAutomaton countingInterface countingStep (ProbDist.single ⟨0⟩)

/-- Forgetting the counter commutes with one fresh reply, for any state and queried port. -/
lemma countingStep_simulatesAt
    -- `s` stores the current count; `x` is the tagged trigger at either port.
    (s : CountingState) (x : Σ i, countingInterface.X i) :
    ProbStep.SimulatesAt countingStep (ProbStep.fresh fun _ _ => 𝒰[Bool])
      (fun _ => ProbDist.single ()) s x := by
  -- Both routes keep the new fair reply and replace its counter by the unique unit state.
  simp only [ProbStep.SimulatesAt, ProbDist.single, bindK_single, one_smul,
    ProbStep.outcome, ProbStep.fresh, countingStep, ProbDist.map_val,
    fTransform_fTransform, fTransform_single, bindK_single_comp]
  rfl

/-- Removing the retained count gives the `ProbStep.fresh` automaton on the same domain. -/
lemma countingSource_eq_fresh :
    countingSource = TypedSystem.ofProbAutomaton countingInterface
      (ProbStep.fresh fun _ _ => 𝒰[Bool]) (ProbDist.single ()) := by
  -- The invariant ties the retained count to the input history, at every supported state.
  have simulation := TypedSystem.ofProbAutomaton_eq_of_simulation
    (A := countingInterface) countingStep (ProbStep.fresh fun _ _ => 𝒰[Bool])
    (fun _ => ProbDist.single ()) (fun xs s => s.calls = xs.length)
    (by
      intro xs s x hs _ p hp
      -- Supported tagged outcomes come from a draw whose next counter is `s.calls + 1`.
      obtain ⟨sy, hsy, rfl⟩ := mem_support_fTransform _ _ hp
      obtain ⟨b, _, rfl⟩ := mem_support_fTransform _ _ hsy
      change s.calls + 1 = (xs ++ [x]).length
      simp only [hs, List.length_append, List.length_singleton])
    (fun _ s x _ _ => countingStep_simulatesAt s x)
    (ProbDist.single ⟨0⟩)
    (by
      intro s hs
      -- The initial law is a point at count zero, the length of the empty input history.
      have hzero : s = CountingState.mk 0 := (Finsupp.mem_support_single _ _ _).mp hs |>.1
      exact congrArg CountingState.calls hzero)
  -- A constant forgetful kernel sends the initial count law to the unit point law.
  simpa only [countingSource, ProbDist.bind_const] using simulation

/-- Every pair of successive replies has probability `1/4`, including unequal bits. -/
lemma countingSource_two_replies_eq
    -- `i`, `j` are the ports of two successive queries, which may be equal.
    (i j : Bool)
    -- `b`, `c` are the respective reply bits, which may differ.
    (b c : Bool) :
    countingSource.1
      [(⟨i, ()⟩, ⟨i, b⟩), (⟨j, ()⟩, ⟨j, c⟩)] = 1 / 4 := by
  rw [countingSource_eq_fresh, TypedSystem.ofProbAutomaton_val,
    RandomSystem.ofProbAutomaton_eq_memoryless _ (ProbStep.memoryless_fresh _) _]
  -- The memoryless chain rule contributes a factor `1/2` for each admitted query.
  change RandomSystem.memoryless countingInterface.inputDomain
    (RandomSystem.portLaw fun _ _ => 𝒰[Bool])
    ([(⟨i, ()⟩, ⟨i, b⟩)] ++ [(⟨j, ()⟩, ⟨j, c⟩)]) = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, countingInterface,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil, List.cons_ne_nil, not_false_eq_true,
    and_self, ite_true, RandomSystem.portLaw_apply_mk, ProbDist.uniform,
    uniform_apply, Fintype.card_bool]
  change RandomSystem.memoryless countingInterface.inputDomain
    (RandomSystem.portLaw fun _ _ => 𝒰[Bool])
    ([] ++ [(⟨i, ()⟩, ⟨i, b⟩)]) * _ = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, countingInterface,
    List.map_nil, List.nil_append, List.length_cons, List.length_nil,
    List.cons_ne_nil, not_false_eq_true, and_self, ite_true,
    RandomSystem.portLaw_apply_mk, ProbDist.uniform, uniform_apply, Fintype.card_bool,
    RandomSystem.mass_nil]
  change (1 : ℝ) * (1 / Fintype.card Bool) * (1 / Fintype.card Bool) = 1 / 4
  norm_num only [Fintype.card_bool]

/-- The interface's total budget makes a third reply impossible even when ports differ. -/
example
    -- `b`, `c`, `d` are the replies to queries at ports `false`, `true`, `false`.
    (b c d : Bool) :
    countingSource.1 [(⟨false, ()⟩, ⟨false, b⟩), (⟨true, ()⟩, ⟨true, c⟩),
      (⟨false, ()⟩, ⟨false, d⟩)] = 0 := by
  apply RandomSystem.mass_eq_zero_of_not_admitted countingSource.1
    (h := [(⟨false, ()⟩, ⟨false, b⟩), (⟨true, ()⟩, ⟨true, c⟩)])
  -- The combined input history has length three, exceeding the total budget of two.
  change ¬ (_ ≠ [] ∧ _ ≤ 2)
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil]
  omega

/-- The port-coherence certificate gives zero probability to a reply at a different port. -/
example : countingSource.1 [(⟨false, ()⟩, ⟨true, false⟩)] = 0 :=
  countingSource.2 [] ⟨false, ()⟩ ⟨true, false⟩ Bool.noConfusion

/-- Point-step specialization rewrites directly beneath a typed converter. -/
example
    -- `A` is the automaton interface; `B` is exposed by the converter `α`; `S` carries states.
    {A B : Interface} {S : Type} (α : TypedConverter B A)
    -- `step` is deterministic after the common initial draw from `init`.
    (step : S → (i : A.I) → A.X i → S × A.Y i) (init : ProbDist S) :
    α • TypedSystem.ofProbAutomaton A (ProbStep.ofDeterministic step) init =
      α • TypedSystem.ofAutomaton A step init := by
  rw [TypedSystem.ofProbAutomaton_ofDeterministic]

#print axioms TypedSystem.ofProbAutomaton
#print axioms TypedSystem.ofProbAutomaton_ofDeterministic
#print axioms TypedSystem.ofProbAutomaton_eq_of_simulation
#print axioms countingSource_two_replies_eq

end Tests.TypedProbAutomaton

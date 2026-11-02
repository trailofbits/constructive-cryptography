module

public import RandomSystems.Typed.Keyed
public import RandomSystems.Typed.ProbAutomaton

/-!
# Retained keys as probabilistic automata

`ofProbAutomaton_bind` moves the mixture of initial state laws outside an automaton.
`ofProbAutomaton_eq_keyed` then identifies an automaton which retains its state `k` and
draws each reply from `ν k i x` with `keyed P ν`. The equality holds for every transcript
on the declared domain, so it preserves repeated and adaptive queries at all ports.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

-- `A` fixes the query/reply types and admitted input histories; `S`, `K` carry states and keys.
variable {A : Interface} {S K : Type}

/-- Sampling an initial state from `P.bind μ` equals retaining `k ∼ P` and using `μ k`. -/
lemma ofProbAutomaton_bind
    -- `step s i x` gives the next state and reply at the queried port.
    (step : ProbStep S A.I A.X A.Y)
    -- `P` mixes the normalized initial state laws `μ k`.
    (P : ProbDist K) (μ : K → ProbDist S) :
    ofProbAutomaton A step (P.bind μ) =
      TypedSystem.sample P (fun k => ofProbAutomaton A step (μ k)) := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- The state sub-law is linear in initialization; taking its weight gives the mixture mass.
  rw [ofProbAutomaton_mass, ProbDist.bind_val, ProbStep.belief_bindK, weight_bindK]
  rfl

/-- Keeping the sampled state `k` unchanged and drawing `ν k i x` freshly realizes `keyed P ν`. -/
theorem ofProbAutomaton_eq_keyed
    -- `P` is the retained key law, shared by all ports.
    (P : ProbDist K)
    -- `ν k i x` supplies the fresh reply law given the retained key and current query.
    (ν : K → ∀ i, A.X i → ProbDist (A.Y i)) :
    ofProbAutomaton A (fun k i x => (ν k i x).map (fun y => (k, y))) P = keyed P ν := by
  let step : ProbStep K A.I A.X A.Y := fun k i x => (ν k i x).map (fun y => (k, y))
  -- Mix point initial laws to expose the one sampled key through `ofProbAutomaton_bind`.
  have hinit : P.bind (fun k => ProbDist.single k) = P :=
    Subtype.ext (bindK_single_one P.1)
  conv_lhs => rw [← hinit, ofProbAutomaton_bind]
  change TypedSystem.sample P (fun k => ofProbAutomaton A step (ProbDist.single k)) =
    TypedSystem.sample P (fun k => ofMemoryless A (ν k))
  congr 1
  funext k
  -- From a fixed key, the trivial fresh-sampling state maps to that same key after every query.
  have hsim := ofProbAutomaton_eq_of_simulation (A := A) (ProbStep.fresh (ν k)) step
    (fun _ => ProbDist.single k) (fun _ _ => True) (by intros; trivial)
    (by
      intro xs s x _ _
      simp only [ProbStep.SimulatesAt, ProbDist.single, bindK_single, one_smul,
        ProbStep.outcome, ProbStep.fresh, step, ProbDist.map_val, fTransform_fTransform,
        fTransform_single, bindK_fTransform, Function.comp_def]
      rw [bindK_single_comp]
      rfl)
    (ProbDist.single ()) (by intros; trivial)
  -- The trivial source state maps to the point law at the fixed key.
  have hsingle : (ProbDist.single ()).bind (fun _ => ProbDist.single k) =
      ProbDist.single k := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul]
  rw [hsingle] at hsim
  rw [← hsim]
  -- The fresh-sampling automaton has the memoryless law of replies conditional on `k`.
  exact Subtype.ext (RandomSystem.ofProbAutomaton_eq_memoryless A.inputDomain
    (ProbStep.memoryless_fresh (ν k)) (ProbDist.single ()))

end SystemAlgebra.TypedSystem

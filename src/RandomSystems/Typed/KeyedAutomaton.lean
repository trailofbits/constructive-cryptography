module

public import RandomSystems.Typed.Keyed
public import RandomSystems.Typed.ProbAutomaton

/-!
# Retained keys as probabilistic automata

`ofProbAutomaton_bind` moves the mixture of initial state laws outside an automaton.
`ofProbAutomaton_eq_keyed` then identifies an automaton which retains its state `k` and
draws each reply from `ν k i x` with `keyed P ν`. The equality holds for every transcript
on the declared domain, so it preserves repeated and adaptive queries at all ports.

`ofProbAutomaton_eq_keyed_of_optional_key` moves a first-query key draw to initialization.
Its local transition contract records the sampled key and retains it on every later query.
The proof represents an absent key by `P` and a present key by its point law, then applies
`ofProbAutomaton_eq_keyed`.
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

/-- Drawing a missing key on the first query and retaining it realizes `keyed P ν`. -/
lemma ofProbAutomaton_eq_keyed_of_optional_key
    -- `P` is the key law; `ν k i x` gives fresh replies conditional on retained `k`.
    (P : ProbDist K) (ν : K → ∀ i, A.X i → ProbDist (A.Y i))
    -- `step` stores an optional key; the unit coordinate is the fresh source's state.
    (step : ProbStep (Option K × Unit) A.I A.X A.Y)
    -- `hstep` draws from `P` exactly when no key is stored, then keeps the selected key.
    (hstep : ∀ keys i x, step (keys, ()) i x =
      match keys with
      | none => P.bind fun k => (ν k i x).map (fun y => ((some k, ()), y))
      | some k => (ν k i x).map (fun y => ((some k, ()), y))) :
    ofProbAutomaton A step (ProbDist.single (none, ())) = keyed P ν := by
  let retained : ProbStep K A.I A.X A.Y := fun k i x => (ν k i x).map fun y => (k, y)
  -- An absent key represents its initial law; a stored key represents its point law.
  let keyLaw : Option K × Unit → ProbDist K
    | (none, _) => P
    | (some k, _) => ProbDist.single k
  -- The local contract gives the commuting square:
  -- step(s, i, x) >>= ((s′, y) ↦ keyLaw(s′).map (·, y))
  --   = keyLaw(s) >>= (k ↦ retained(k, i, x)).
  have hsim := ofProbAutomaton_eq_of_simulation (A := A) step retained keyLaw
    (fun _ _ => True) (by intros; trivial)
    (by
      intro xs s x _ _
      rcases s with ⟨keys, ⟨⟩⟩
      unfold ProbStep.SimulatesAt ProbStep.outcome
      rw [hstep keys x.1 x.2]
      cases keys <;>
        simp only [keyLaw, retained, ProbDist.bind_val, ProbDist.map_val, ProbDist.single,
          bindK_single, one_smul, fTransform_bindK, bindK_bindK, fTransform_fTransform,
          bindK_fTransform, Function.comp_def, ProbStep.tagged, fTransform_single,
          bindK_single_comp])
    (ProbDist.single (none, ())) (by intros; trivial)
  -- The initial absent state represents `P`; normalization gives empty-transcript mass one.
  have hi : (ProbDist.single (none, ())).bind keyLaw = P := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul, keyLaw]
  rw [hi] at hsim
  exact hsim.trans (ofProbAutomaton_eq_keyed P ν)

end SystemAlgebra.TypedSystem

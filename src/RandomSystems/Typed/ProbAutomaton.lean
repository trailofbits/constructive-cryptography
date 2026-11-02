module

public import RandomSystems.System.ProbAutomaton
public import RandomSystems.Typed.Automaton

/-!
# Probabilistic automata on interfaces

`TypedSystem.ofProbAutomaton` packages `RandomSystem.ofProbAutomaton` with its queried-port
proof on `A.inputDomain`. The state type may be infinite; each initial and transition law
has finite support. `ofProbAutomaton_mass` gives the weight of the state sub-law after a
transcript. `ofProbAutomaton_eq_of_simulation` lifts the kernel simulation law: preservation
of an input-history invariant and commuting transitions at admitted queries give equality
of typed systems.

`ofProbAutomaton_ofDeterministic` identifies point transitions with `ofAutomaton`.
In [1, Definition 2, p. 6], internal randomness is fixed in one seed;
`ProbStep` draws per transition.
`RandomSystem.ofProbAutomaton_eq_drawStep`, in `RandomSystems.Converter.ProbProgramAttachment`,
relates these presentations on bounded domains by retaining a table of independent draws.

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology —
   EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002. Page numbers refer to the preprint.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

/-- Draw `s ← init` once; each admitted `i(x)` draws `(s', y) ← step s i x`, retains `s'`,
and returns `y` at `i`. Its transcript probabilities are those of `RandomSystem.ofProbAutomaton`
on exactly `A.domain`. -/
noncomputable def ofProbAutomaton
    -- `A` fixes the ports, query/reply types and admitted input histories; `S` carries states.
    (A : Interface) {S : Type}
    -- `step s i x` is the normalized law of the next state and reply at queried port `i`.
    (step : ProbStep S A.I A.X A.Y)
    -- `init` is the normalized initial state law, with finite support in `S`.
    (init : ProbDist S) : TypedSystem A :=
  ⟨RandomSystem.ofProbAutomaton A.inputDomain step init,
    RandomSystem.ofProbAutomaton_repliesAtQueriedInterface A.inputDomain step init⟩

-- `A` fixes the interface and its domain; `S` carries the retained automaton state.
variable {A : Interface} {S : Type}

/-- Forgetting the port certificate gives `RandomSystem.ofProbAutomaton`. -/
@[simp] lemma ofProbAutomaton_val
    -- `step` supplies each state/reply law; `init` supplies the initial state law.
    (step : ProbStep S A.I A.X A.Y) (init : ProbDist S) :
    (ofProbAutomaton A step init).1 =
      RandomSystem.ofProbAutomaton A.inputDomain step init := rfl

/-- The probability of `h` is the weight of the states reached with the replies of `h`. -/
lemma ofProbAutomaton_mass
    -- `step` supplies each state/reply law; `init` supplies the initial state law.
    (step : ProbStep S A.I A.X A.Y) (init : ProbDist S)
    -- `h` pairs each tagged query with its tagged reply on `A`.
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (ofProbAutomaton A step init).1 h = (step.belief A.inputDomain init.1 h).weight :=
  RandomSystem.ofProbAutomaton_apply A.inputDomain step init h

/-- Point transitions give `ofAutomaton`: one draw from `init` fixes the retained state,
which may include a random seed. This realizes [1, Definition 2, p. 6]:
“specifying the internal randomness and the initial state”. -/
lemma ofProbAutomaton_ofDeterministic
    -- `step s i x` is the next state and reply, without a further random draw.
    (step : S → (i : A.I) → A.X i → S × A.Y i)
    -- `init` supplies the common initial state law for both presentations.
    (init : ProbDist S) :
    ofProbAutomaton A (ProbStep.ofDeterministic step) init = ofAutomaton A step init := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- Both probabilities are the `init`-mass of the initial states producing `h` on `A.domain`.
  exact (RandomSystem.ofProbAutomaton_ofDeterministic_apply step init h).trans
    (ofAutomaton_mass A step init h).symm

/-- A kernel simulation on admitted queries gives equal typed systems when the second
initial law is the kernel image of the first. -/
lemma ofProbAutomaton_eq_of_simulation
    -- `S₁`, `S₂` carry the two state representations of the same interface `A`.
    {S₁ S₂ : Type}
    -- `step₁`, `step₂` give their normalized next-state/reply laws.
    (step₁ : ProbStep S₁ A.I A.X A.Y) (step₂ : ProbStep S₂ A.I A.X A.Y)
    -- `K s` is the normalized law representing state `s : S₁` as a state in `S₂`.
    (K : S₁ → ProbDist S₂)
    -- `inv xs s` relates the input history `xs` to the current state `s` of `step₁`.
    (inv : List (Σ i, A.X i) → S₁ → Prop)
    -- `hpres` preserves `inv` at every possible outcome of an admitted next query `x`.
    (hpres : ∀ xs s x, inv xs s → A.domain (xs ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1)
    -- `hsim` commutes `K` with the transitions, retaining the same reply, on those states.
    (hsim : ∀ xs s x, inv xs s → A.domain (xs ++ [x]) →
      ProbStep.SimulatesAt step₁ step₂ K s x)
    -- `init` supplies the first initial law; `hinit` establishes `inv` on its support.
    (init : ProbDist S₁) (hinit : ∀ s ∈ init.1.support, inv [] s) :
    ofProbAutomaton A step₁ init = ofProbAutomaton A step₂ (init.bind K) :=
  Subtype.ext (RandomSystem.ofProbAutomaton_eq_of_simulation
    step₁ step₂ K inv hpres hsim init hinit)

end SystemAlgebra.TypedSystem

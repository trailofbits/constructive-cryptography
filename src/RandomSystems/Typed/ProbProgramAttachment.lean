module

public import RandomSystems.Typed.ProbAutomaton
public import RandomSystems.Typed.DSL.Converters
public import RandomSystems.Converter.ProbProgramAttachment

/-!
# Program attachment to typed probabilistic automata

`TypedConverter.ofProgram_smul_ofProbAutomaton` identifies program attachment with the
existing combined transition law `Program.probCombine`. Its hypothesis `hB` admits every
nonempty inside history of length at most `b * A.bound`, covering all program calls.
Each inside transition uses a fresh draw.
The initial law retains the program's initial state beside the sampled inside state.
-/

@[expose] public section

namespace SystemAlgebra.TypedConverter

open Probability.Distribution

/-- Attaching a bounded program to an automaton combines their states and transitions. -/
lemma ofProgram_smul_ofProbAutomaton
    -- `A`, `B` are the outside and inside interfaces; `S`, `R` carry their retained states.
    {A B : Interface} {S R : Type}
    -- `s` initializes program `P`; `hb` bounds each invocation by `b` inside queries.
    (s : S) (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hB` admits all nonempty inside histories of length at most `b * A.bound`.
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    -- `step` gives the inside transition law; `init` samples its starting state once.
    (step : ProbStep R B.I B.X B.Y) (init : ProbDist R) :
    ofProgram s P hb hB • TypedSystem.ofProbAutomaton B step init =
      TypedSystem.ofProbAutomaton A (P.probCombine step hb) (init.map fun r => (s, r)) :=
  Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton
    B.nonempty_prefix A.nonempty_prefix s P hb _ step init)

end SystemAlgebra.TypedConverter

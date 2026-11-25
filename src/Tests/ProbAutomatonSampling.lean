module

public import RandomSystems.Typed.ProbAutomatonSampling

/-! A retained bit is shared by every query of the automaton. -/

@[expose] public section

namespace Tests.ProbAutomatonSampling

open SystemAlgebra Probability Probability.Distribution

/-- Two unit queries, each returning a Boolean reply. -/
def port : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- Every query returns the retained `bit`, without changing the unit state. -/
noncomputable def reply (bit : Bool) : ProbStep Unit port.I port.X port.Y :=
  fun s _ _ => ProbDist.single (s, bit)

example (μ : ProbDist Bool) :
    TypedSystem.sample μ.1 (fun bit =>
      TypedSystem.ofProbAutomaton port (reply bit) (ProbDist.single ())) =
    TypedSystem.ofProbAutomaton port
      (fun bs i x => (reply bs.1 bs.2 i x).map fun sy => ((bs.1, sy.1), sy.2))
      (μ.bind fun bit => (ProbDist.single ()).map fun s => (bit, s)) :=
  TypedSystem.sample_ofProbAutomaton_eq μ reply (fun _ => ProbDist.single ())

#print axioms TypedSystem.sample_ofProbAutomaton_eq

end Tests.ProbAutomatonSampling

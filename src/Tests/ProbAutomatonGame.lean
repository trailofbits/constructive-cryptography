module

public import RandomSystems.Typed.ProbAutomatonGame

/-! A one-port game sets its bit on a query and keeps its visible reply constant. -/

@[expose] public section

namespace Tests.ProbAutomatonGame

open SystemAlgebra Probability Probability.Distribution

/-- The oracle accepts at most two unit queries and replies with a unit value. -/
def port : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 2

/-- Every query sets the hidden bit and replies `()`. -/
noncomputable def mark : ProbStep (Unit × Bool) port.I port.X (withMBO port.Y) :=
  fun _ _ _ => ProbDist.single (((), true), ((), true))

lemma mark_flag (s : Unit) (b : Bool) (i : port.I) (x : port.X i)
    (p : (Unit × Bool) × (port.Y i × Bool))
    (hp : p ∈ (mark (s, b) i x).1.support) :
    p.2.2 = p.1.2 ∧ (b = true → p.1.2 = true) := by
  classical
  change p ∈ (Finsupp.single (((), true), ((), true)) (1 : ℝ)).support at hp
  rw [Finsupp.support_single _ one_ne_zero] at hp
  have heq := Finset.mem_singleton.mp hp
  subst p
  exact ⟨rfl, fun _ => rfl⟩

example : (TypedGame.ofProbAutomaton mark (ProbDist.single ()) mark_flag).visible =
    TypedSystem.ofProbAutomaton port (ProbStep.forgetMBO mark)
      ((ProbDist.single ()).map fun s => (s, false)) :=
  TypedGame.visible_ofProbAutomaton mark (ProbDist.single ()) mark_flag

#print axioms TypedGame.ofProbAutomaton
#print axioms TypedGame.visible_ofProbAutomaton

end Tests.ProbAutomatonGame

module

public import RandomSystems.Typed.GameEventReflection
public import RandomSystems.Typed.AutomatonGame
public import RandomSystems.Typed.DSL.Converters
public import Mathlib.Tactic.IntervalCases

/-!
# Completed verification-call regression

A verifier receives one outside query, makes two inside calls, and returns the second reply.
The first reply has MBO `false`; the final verification reply may set it. The completed
interaction retains that last bit, whereas the prefix before verification is unfinished.
The typed endpoint accepts randomized callers and an explicit reflection contract.
-/

@[expose] public section

namespace Tests.GameEventReflection

open SystemAlgebra Probability Probability.Distribution

/-- One outside unit query returns the verifier's Boolean answer. -/
abbrev outside : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Two inside unit queries return Boolean answers. -/
abbrev inside : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- Make the initial call and the final verification call, then return the second reply. -/
def verify : Program Unit outside.I inside.I outside.X outside.Y inside.X inside.Y :=
  fun _ _ _ exchanges => match exchanges with
    | [] => .inr ⟨(), ()⟩
    | [_] => .inr ⟨(), ()⟩
    | _ :: (_, ⟨(), reply⟩) :: _ => .inl ((), reply)

lemma verify_bounded : verify.Bounded 2 := by
  intro _ _ _ exchanges q _ hq
  rcases exchanges with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · simp only [List.length_nil]; omega
  · simp only [List.length_cons, List.length_nil]; omega
  · rcases second with ⟨_, ⟨⟨⟩, reply⟩⟩
    simp only [verify, reduceCtorEq] at hq

/-- `verifier` keeps the one-query outside domain and spends two inside queries. -/
noncomputable def verifier : TypedConverter outside inside :=
  TypedConverter.ofProgram () verify verify_bounded (fun _ hne hlen => ⟨hne, hlen⟩)

/-- The joint request alphabet: converter input or game query. -/
abbrev JointQuery := Two (Σ l, twoFam outside.X (withMBO inside.Y) l) (Σ i, inside.X i)

/-- The joint reply alphabet: converter output or tagged game reply. -/
abbrev JointReply := Two (Σ l, twoFam (withMBO outside.Y) inside.X l)
  (Σ i, withMBO inside.Y i)

/-- Query, first reply, final query, final reply, outside answer; `b` is the final bit. -/
def completed (b : Bool) : List (JointQuery × JointReply) :=
  [(resourceInput ⟨(), ()⟩, ⟨none, ⟨⟨some (), ()⟩, ()⟩⟩),
   (⟨some (), ⟨(), ()⟩⟩, ⟨some (), ⟨(), (false, false)⟩⟩),
   (⟨none, ⟨⟨some (), ()⟩, (false, false)⟩⟩, ⟨none, ⟨⟨some (), ()⟩, ()⟩⟩),
   (⟨some (), ⟨(), ()⟩⟩, ⟨some (), ⟨(), (b, b)⟩⟩),
   (⟨none, ⟨⟨some (), ()⟩, (b, b)⟩⟩, ⟨none, ⟨⟨none, ()⟩, (b, b)⟩⟩)]

example (b : Bool) : FollowsStrategy
    (connectionQueries resourceRoute resourceInput [⟨(), ()⟩]) (completed b) := by
  rw [FollowsStrategy.iff_getElem]
  intro i hi
  simp only [completed, List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [completed, connectionQueries, exposedReplies, resourceRoute, resourceInput]

-- The verifier has actually consumed both inside replies before it returns its answer.
example (b : Bool) :
    (DDC.ofProgram () verify)
      [⟨⟨none, ()⟩, ()⟩, ⟨⟨some (), ()⟩, false⟩, ⟨⟨some (), ()⟩, b⟩] =
        Part.some ⟨⟨none, ()⟩, b⟩ := by
  simp [DDC.ofProgram, Program.after, Program.run, Program.step, Program.emit, verify]

-- All requested outside replies have arrived, and the final inside call is included.
example (b : Bool) :
    ¬ (connectionQueries (resourceRoute (U := outside.X)) resourceInput
      [⟨(), ()⟩] ((completed b).map Prod.snd)).Dom := by
  simp [connectionQueries, exposedReplies, completed, resourceRoute]

example (b : Bool) :
    finalMBO (RandomSystem.parallelRight (completed b)) = b := rfl

-- The prefix before the final verification reply still has no outside answer and no bad bit.
example (b : Bool) :
    (connectionQueries (resourceRoute (U := outside.X)) resourceInput
      [⟨(), ()⟩] (((completed b).take 3).map Prod.snd)).Dom ∧
      finalMBO (RandomSystem.parallelRight ((completed b).take 3)) = false := by
  exact ⟨by norm_num [connectionQueries, exposedReplies, completed, resourceRoute], rfl⟩

-- The reduction endpoint uses exactly this verifier, with its one-to-two query certificate.
example (P : outside.inputDomain.Distinguisher) (G : TypedGame inside)
    (hreflect : P.ReflectsMBO verifier G.1.1) :
    (TypedSolver.ofDistinguisher P).decision.1 (verifier • G.visible) ≤
      ((TypedSolver.ofDistinguisher P).absorb verifier).winProbability G :=
  TypedSolver.probability_attach_le_winProbability_absorb (TypedSolver.ofDistinguisher P)
    verifier G (TypedSolver.ofDistinguisher_reflectsMBO P verifier G hreflect)

-- Success before making any call cannot imply a hidden event: the empty interaction has no MBO.
example (α : TypedConverter outside inside) (G : TypedGame inside) :
    ¬ α.ReflectsMBO G.1.1 (fun _ => True) := by
  intro hreflect
  have hb := hreflect [] [] FollowsStrategy.nil
    (by simp [connectionQueries, exposedReplies])
    (by rw [RandomSystem.mass_nil]; exact one_ne_zero) rfl trivial
  exact Bool.noConfusion hb

/-- The monitor is set only by the second query, including a final verification query. -/
def secondCall : MC (Σ i, inside.X i) :=
  ⟨fun xs => 2 ≤ xs.length, fun _ _ hp h => h.trans hp.length_le⟩

/-- Reply `false` then `true`; the final verification call sets the hidden event. -/
noncomputable def monitored : TypedGame inside :=
  TypedGame.ofAutomaton inside (fun (seen : Bool) _ _ => (true, seen))
    (ProbDist.single false) (fun _ => secondCall)

example : monitored.1.1.unsetProbability [⟨(), ()⟩] = 1 := by
  rw [monitored, TypedGame.ofAutomaton_unsetProbability _ _ _ _
    (show inside.domain [⟨(), ()⟩] from ⟨by simp, by simp⟩)]
  norm_num [Distribution.mass_single, secondCall, ProbDist.single]

example : monitored.1.1.unsetProbability [⟨(), ()⟩, ⟨(), ()⟩] = 0 := by
  rw [monitored, TypedGame.ofAutomaton_unsetProbability _ _ _ _
    (show inside.domain [⟨(), ()⟩, ⟨(), ()⟩] from ⟨by simp, by simp⟩)]
  norm_num [Distribution.mass_single, secondCall, ProbDist.single]

#print axioms PDCBehavior.probability_attach_le_winProbability
#print axioms TypedSolver.probability_attach_le_winProbability_absorb

end Tests.GameEventReflection

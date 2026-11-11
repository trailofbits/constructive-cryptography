module

public import RandomSystems.Typed.FreshComponent

/-!
# Fresh samples beside an arbitrary resource

A two-call Boolean source remains fresh when placed beside any independent resource.
The selected value is the source's reply; exchanges with the other resource select nothing.
-/

@[expose] public section

namespace SystemAlgebra.Tests.FreshComponent

open Probability Probability.Distribution

/-- Both calls to the uniform Boolean source satisfy the same conditional reply bound. -/
lemma fresh_bits : (TypedSystem.source (ProbDist.uniform Bool) 2).AnswersFresh
    (fun z => some z.2.2) (ProbDist.uniform Bool).1 := by
  have h := TypedSystem.AnswersFresh.source (ProbDist.uniform Bool) 2 id
  rw [fTransform_id] at h
  exact h

/-- An arbitrary independent neighbor preserves the source's selected fresh replies. -/
lemma fresh_bits_beside {B : Interface} (S : TypedSystem B) :
    (TypedSystem.parallel (TypedSystem.source (ProbDist.uniform Bool) 2) S).AnswersFresh
      (fun e => match e with
        | (⟨.inl _, _⟩, ⟨.inl _, y⟩) => some y
        | _ => none) (ProbDist.uniform Bool).1 := by
  intro h x v hx
  have bound := TypedSystem.AnswersFresh.parallel_left S
    (ProbDist.uniform Bool).2.1 fresh_bits h x v hx
  obtain ⟨i | j, x⟩ := x <;> exact bound

#print axioms TypedSystem.AnswersFresh.ofMemoryless
#print axioms TypedSystem.AnswersFresh.parallel_left
#print axioms TypedSystem.AnswersFresh.rename
#print axioms fresh_bits_beside

end SystemAlgebra.Tests.FreshComponent

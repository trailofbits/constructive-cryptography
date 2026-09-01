import RandomSystems.Game

set_option autoImplicit false

/-!
# Function-evaluator games

This module equips Lanzenberger function evaluators with monotone conditions
and maps distributions to the resulting games.
-/

noncomputable section

namespace RandomSystems

open Probability

universe u v w

namespace System.DDG

variable {X : Type u} {Y : Type v}

/-- A function evaluator equipped with a monotone condition. -/
def ofFunction (function : X → Y) (condition : System.MC X) :
    System.DDG X Y where
  system := System.functionEvaluator function
  condition := condition

end System.DDG

namespace PDG

variable {A : Type w} {X : Type u} {Y : Type v}

/-- Map a distribution to function evaluators carrying monotone conditions. -/
def ofFunction (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X) : PDG X Y :=
  Distribution.fTransform
    (fun value => System.DDG.ofFunction (function value) (condition value)) source

/-- A probability distribution induces a probability game. -/
lemma isProbDist_ofFunction (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X)
    (probability : source.isProbDist) :
    (ofFunction source function condition).isProbDist :=
  Distribution.fTransform_isProbDist _ probability

/-- Every function evaluator has the domain of nonempty histories. -/
lemma hasDomain_ofFunction (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X) :
    HasDomain (ofFunction source function condition)
      {queries : List X | queries ≠ []} := by
  intro deterministic supported
  obtain ⟨value, _, rfl⟩ :=
    Distribution.exists_mem_support_of_mem_support_fTransform
      (fun value => System.DDG.ofFunction (function value) (condition value))
      source supported
  exact System.dom_functionEvaluator (function value)

/-- Forgetting the condition leaves the function-evaluator law. -/
lemma underlying_ofFunction (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X) :
    (ofFunction source function condition).underlying =
      Distribution.fTransform
        (fun value => System.functionEvaluator (function value)) source := by
  unfold underlying ofFunction
  rw [Distribution.fTransform_fTransform]
  rfl

end PDG

end RandomSystems

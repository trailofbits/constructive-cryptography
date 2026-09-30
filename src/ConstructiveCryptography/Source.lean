import ConstructiveCryptography.Automaton

/-!
# Sources of fresh samples

A source answers each query with a fresh sample from its law (Maurer 2002, Definition 1: an
`X`-source is a sequence of random variables in `X`; here they are independent and identically
distributed). It is the primitive randomness resource: randomness enters a system only through
sources. It is the automaton that draws a table of `q` independent samples as its initial state
and answers the `k`-th query with the `k`-th entry.

## Main definitions

* `Interface.source X q`: a single port with no input and outputs in `X`, at most `q` queries
* `Interface.sourceStep law`: the `k`-th query receives the `k`-th entry of the table
* `Interface.Resource.source law q`: the source of fresh samples from `law`

## Main results

* `Interface.stateAfter_sourceStep`: after `k` queries the source reads entry `k`
-/

namespace SystemAlgebra

open Probability

namespace Interface

variable {X : Type}

/-- A source interface: a single port with no input and outputs in `X`, at most `q` queries. -/
abbrev source (X : Type) [Fintype X] (q : ℕ) : Interface :=
  queryBudget Unit (fun _ => Unit) (fun _ => X) q

/-- The step of a source: the `k`-th query receives the `k`-th entry of its table. -/
noncomputable def sourceStep {q : ℕ} (law : Distribution.ProbDist X) :
    (Fin q → X) × ℕ → (i : Unit) → Unit → ((Fin q → X) × ℕ) × X
  | (t, k), _, _ => ((t, k + 1), if hk : k < q then t ⟨k, hk⟩ else Classical.choice law.nonempty)

/-- After `k` queries the source reads entry `k` of its table. -/
theorem stateAfter_sourceStep {q : ℕ} (law : Distribution.ProbDist X) (t : Fin q → X)
    (h : List (Σ _ : Unit, Unit)) : stateAfter (sourceStep law) (t, 0) h = (t, h.length) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h x ih => rw [stateAfter_snoc, ih]; simp [sourceStep]

/-- **The source of fresh samples from `law`**: the automaton reading its answers from a table
of `q` independent samples. -/
noncomputable def Resource.source [Fintype X] (law : Distribution.ProbDist X) (q : ℕ) :
    Resource (Interface.source X q) :=
  Resource.ofAutomaton (Interface.source X q) (sourceStep law)
    ⟨Distribution.fTransform (fun t => (t, 0)) (Distribution.pi fun _ : Fin q => law.1),
      Distribution.fTransform_isProbDist _ (Distribution.pi_isProbDist fun _ => law.2)⟩

end Interface

end SystemAlgebra

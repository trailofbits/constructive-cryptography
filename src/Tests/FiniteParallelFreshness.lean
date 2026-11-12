module

public import ConstructiveCryptography.Instances.FiniteParallelFreshness
public import Tests.FreshComponent

/-!
# Freshness in a heterogeneous family

The selected member is a two-call Boolean source. Its neighbor is an arbitrary typed resource,
with its own interface and any retained state; no freshness assumption is imposed on it.
-/

@[expose] public section

namespace SystemAlgebra.Tests.FiniteParallelFreshness

open Probability Probability.Distribution

/-- The Boolean source interface at `false`, and an arbitrary interface `B` at `true`. -/
def interfaces (B : Interface) : Bool → Interface
  | false => Interface.source Bool 2
  | true => B

/-- Independent family: fresh Boolean source at `false`, supplied resource `S` at `true`. -/
noncomputable def resources {B : Interface} (S : TypedSystem B) :
    ∀ k, TypedSystem (interfaces B k)
  | false => TypedSystem.source (ProbDist.uniform Bool) 2
  | true => S

/-- The selected source retains its fresh reply bound beside any resource `S`. -/
lemma selected_source {B : Interface} (S : TypedSystem B) :
    (TypedSystem.parallelAll (resources S)).AnswersFresh
      (fun z => (Interface.selectExchange false z).bind (fun w => some w.2.2))
      (ProbDist.uniform Bool).1 :=
  TypedSystem.AnswersFresh.parallelAll (resources S) false (ProbDist.uniform Bool).2.1
    FreshComponent.fresh_bits

#print axioms TypedSystem.AnswersFresh.parallelAll
#print axioms selected_source

end SystemAlgebra.Tests.FiniteParallelFreshness

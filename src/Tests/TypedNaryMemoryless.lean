module

public import RandomSystems.Typed.ParallelAllMemoryless
public import Tests.TypedNaryParallel

/-!
# Memoryless families with heterogeneous and empty interfaces

`heterogeneousFamily` combines Boolean queries/replies with unit queries/replies
and different budgets. Its fresh reply laws rewrite through an arbitrary converter.
For an empty family, the same closure law gives the function on an interface with no ports,
and the interface admits no input history.
-/

@[expose] public section

namespace SystemAlgebra.Tests

open Probability Probability.Distribution
open scoped SystemAlgebra

/-- Component `false` returns a fresh fair bit; component `true` returns the unit reply. -/
noncomputable def heterogeneousReplyLaw :
    ∀ k i, (heterogeneousFamily k).X i → ProbDist ((heterogeneousFamily k).Y i)
  | false, _, _ => 𝒰[Bool]
  | true, _, _ => ProbDist.single ()

/-- The fresh laws on the heterogeneous family compose under a supplied converter. -/
example
    -- `A` is exposed by `α`, which consumes the family with budgets two and one.
    {A : Interface} (α : TypedConverter A (Interface.tensorAll heterogeneousFamily)) :
    α • (∥ k, TypedSystem.ofMemoryless (heterogeneousFamily k) (heterogeneousReplyLaw k)) =
      α • TypedSystem.ofMemoryless (Interface.tensorAll heterogeneousFamily)
        (fun l x => heterogeneousReplyLaw l.1 l.2 x) := by
  rw [TypedSystem.parallelAll_ofMemoryless]

/-- With no component labels, the closure law gives the unique empty-port reply function. -/
example
    -- `B` is an empty family; `ν` has no component at which to supply a law.
    (B : Empty → Interface) (ν : ∀ k i, (B k).X i → ProbDist ((B k).Y i)) :
    (∥ k, TypedSystem.ofMemoryless (B k) (ν k)) =
      TypedSystem.ofFunction (A := Interface.tensorAll B) (fun l => Empty.elim l.1) := by
  rw [TypedSystem.parallelAll_ofMemoryless]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- The empty transcript has mass one; a nonempty transcript would contain an empty tag.
  cases h with
  | nil => rw [RandomSystem.mass_nil, RandomSystem.mass_nil]
  | cons z _ => exact Empty.elim z.1.1.1

/-- The empty family's domain admits no input history. -/
example
    -- `B` has no component; `h` is any input history on its combined interface.
    (B : Empty → Interface) (h : List (Σ i, (Interface.tensorAll B).X i)) :
    ¬ (Interface.tensorAll B).domain h := by
  cases h with
  | nil => exact (Interface.tensorAll B).nonempty_prefix.1
  | cons x _ => exact Empty.elim x.1.1

#print axioms TypedSystem.parallelAll_ofMemoryless

end SystemAlgebra.Tests

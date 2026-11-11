module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel.PseudoMetric
public import ConstructiveCryptography.Instances.FiniteParallel
public import Tests.FiniteFamilyCoherence

/-!
# Abstract family distance bounds on typed resources

The empty-family bound applies over an arbitrary abstract algebra. The interface instance
transports nonzero local budgets for the existing heterogeneous family through a supplied
outside context.
-/

public section

open CategoryTheory MonoidalCategory
open ConstructiveCryptography CryptographicAlgebra FiniteParallel
open scoped BigOperators NNReal ConstructiveCryptography.FiniteParallel

universe u v w

/-- The selected empty family has zero distance. -/
example {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {Phi : C → Type w} [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi]
    [FiniteParallel C Phi] {A : PEmpty → C} (R S : ∀ k, Phi (A k)) :
    distance (∥ k, R k) (∥ k, S k) ≤ 0 := by
  simpa only [Finset.univ_eq_empty, Finset.sum_empty] using distance_parallelAll_le_sum R S

namespace Tests.FiniteParallelDistance

open SystemAlgebra SystemAlgebra.Tests

/-- Budgets two and three for heterogeneous components give budget five in a common context. -/
example {X : Interface} (R S : ∀ k, TypedSystem (heterogeneousFamily k))
    (context : X ⟶ (⨂ k, heterogeneousFamily k))
    (step : ∀ k, distance (R k) (S k) ≤ ((if k then 3 else 2 : ℝ≥0) : ENNReal)) :
    distance (context • (∥ k, R k)) (context • (∥ k, S k)) ≤ (5 : ENNReal) := by
  have h := distance_attach_parallelAll_le_sum context R S (fun k => if k then 3 else 2) step
  norm_num [Fintype.sum_bool] at h ⊢
  exact h

#print axioms distance_parallelAll_le_sum
#print axioms distance_parallelAll_update_le
#print axioms distance_attach_parallelAll_le_sum

end Tests.FiniteParallelDistance

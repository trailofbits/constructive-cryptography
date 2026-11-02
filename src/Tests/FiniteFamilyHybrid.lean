module

public import ConstructiveCryptography.Substitution.FiniteFamily
public import Tests.FiniteFamilyCollect

/-!
# Component bounds through a common finite-family assembly

The variable client retains its outer converter and heterogeneous family of component converters;
only local component bounds are premises. The tuple client instantiates that assembly with the
existing Boolean/ternary collector in reverse order. The implication's endpoints are exact,
and the empty family has zero error. The selected-observer client supplies closure for the actual
hybrid transformations, then uses local contracts at the reduced distinguishers.
-/

@[expose] public section

namespace SystemAlgebra.Tests

open ConstructiveCryptography.CryptographicAlgebra SystemAlgebra.Substitution
open scoped SystemAlgebra NNReal BigOperators

/-- Fixed component converters and the outside context preserve the sum of local budgets. -/
example
    -- `A k` and `B k` are component outside/inside interfaces; `C` is the assembly's outside.
    {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface} {C : Interface}
    -- `order` chooses each component's replacement position.
    {n : Nat} (order : Fin n ≃ K)
    -- `context` and `α k` are shared by both assemblies; `R k`, `S k` are the local pair.
    (context : TypedConverter C (⨂ k, A k)) (α : ∀ k, TypedConverter (A k) (B k))
    -- `error k` is the supplied scalar budget for the local pair.
    (R S : ∀ k, TypedSystem (B k)) (error : K → ℝ≥0)
    (step : ∀ k, Δ (R k)(S k) ≤ error k) :
    Δ (context • ((⨂ₘ k, α k) • (∥ k, R k)))
      (context • ((⨂ₘ k, α k) • (∥ k, S k))) ≤ (∑ k, error k : ℝ≥0) := by
  simpa only [TypedConverter.comp_smul] using distance_smul_parallelAll_le_sum R S order
    (TypedConverter.comp context (⨂ₘ k, α k)) error step

/-- The normalized update families retain a direct bound from the changed component alone. -/
example
    -- `K` tags the component interfaces `A j`.
    {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    -- `R j` fixes components outside the selected tag `k`.
    (R : ∀ k, TypedSystem (A k)) (k : K)
    -- `S`, `T` are the component pair; `hlocal` supplies their scalar budget `ε`.
    (S T : TypedSystem (A k)) (ε : ℝ≥0) (hlocal : Δ S T ≤ ε) :
    Δ (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤ ε :=
  (distance_parallelAll_update_le R k S T).trans hlocal

section Endpoints

-- `R k`, `S k` are the original and replacement systems at the same tuple-component interface.
variable (R S : ∀ k, TypedSystem (collectionComponent k))

/-- The implication begins at the supplied tuple assembly, with its original component tags. -/
example :
    (parallelAllImplication R S collectionOrder tupleCollector).targetLeft =
      tupleCollector • (∥ k, R k) := rfl

/-- The implication ends at the same tuple assembly with all component replacements. -/
example :
    (parallelAllImplication R S collectionOrder tupleCollector).targetRight =
      tupleCollector • (∥ k, S k) := rfl

/-- The witness retains the supplied reverse order as its assumption index. -/
example :
    (parallelAllImplication R S collectionOrder tupleCollector).index = collectionOrder := rfl

/-- One replacement changes the ternary component and retains the Boolean component. -/
example :
    parallelAllHybrid R S collectionOrder 1 true = S true ∧
      parallelAllHybrid R S collectionOrder 1 false = R false := by
  exact ⟨rfl, rfl⟩

end Endpoints

/-- Actual Boolean/ternary function systems leave only their two local distance bounds. -/
example
    -- `f k`, `g k` are the two coordinate functions; the collector keeps its two-query domain.
    (f g : ∀ k, collectionAlphabet k → collectionAlphabet k)
    -- `error k` bounds the distance between these two functions on component `k`.
    (error : Bool → ℝ≥0)
    (step : ∀ k, Δ
      (TypedSystem.ofFunction (A := collectionComponent k)
        (fun _ => f k))(TypedSystem.ofFunction (A := collectionComponent k) (fun _ => g k)) ≤
          error k) :
    Δ (tupleCollector • (∥ k, TypedSystem.ofFunction (A := collectionComponent k) (fun _ => f k)))
      (tupleCollector • (∥ k, TypedSystem.ofFunction (A := collectionComponent k) (fun _ => g k))) ≤
        (error true + error false : ℝ≥0) := by
  simpa only [Fintype.sum_bool] using distance_smul_parallelAll_le_sum
    (fun k => TypedSystem.ofFunction (A := collectionComponent k) (fun _ => f k))
    (fun k => TypedSystem.ofFunction (A := collectionComponent k) (fun _ => g k))
    collectionOrder tupleCollector error step

/-- An empty family contributes zero error under any compatible outside context. -/
example
    -- `A` is an empty family of interfaces, exposed at outside interface `C`.
    {A : Fin 0 → Interface} {C : Interface}
    -- `R`, `S` are its uniquely determined system family; `context` is any compatible converter.
    (R S : ∀ k, TypedSystem (A k)) (context : TypedConverter C (⨂ k, A k)) :
    Δ (context • (∥ k, R k)) (context • (∥ k, S k)) ≤ (0 : ℝ≥0) := by
  simpa only [Fin.sum_univ_zero, ENNReal.coe_zero] using
    distance_smul_parallelAll_le_sum R S (Equiv.refl (Fin 0)) context (fun _ => 0)
      (fun k => Fin.elim0 k)

/-- Only `step` is local; reduction and closure cover the collector and the fixed hybrid system. -/
example
    -- `D B` carries chosen tests at `B`; `model` supplies their advantages and admitted subset.
    {D : Interface → Type} (model : DistinguisherAdvantage Interface TypedSystem D)
    -- `R k`, `S k` are the component pair before and after replacement.
    (R S : ∀ k, TypedSystem (collectionComponent k))
    -- `reduce i` absorbs the collector and the unchanged component of this exact hybrid.
    (reduce : ∀ i : Fin 2, D collectionInterface → D (collectionComponent (collectionOrder i)))
    -- `closed` admits every reduced test after the collector and fixed component are absorbed.
    (closed : ∀ i d, d ∈ model.admissible collectionInterface →
      reduce i d ∈ model.admissible (collectionComponent (collectionOrder i)))
    -- `hadvantage` identifies the actual transformed advantage with the local one.
    (hadvantage : ∀ i d (U V : TypedSystem (collectionComponent (collectionOrder i))),
      model.advantage collectionInterface d
        (parallelAllHybridContext R S collectionOrder tupleCollector i • U)
        (parallelAllHybridContext R S collectionOrder tupleCollector i • V) =
        model.advantage (collectionComponent (collectionOrder i)) (reduce i d) U V)
    -- `error k` and `step k` concern only the two component systems at `k`.
    (error : ∀ k, D (collectionComponent k) → ENNReal)
    (step : ∀ k, model.SubstitutesWithin (error k) (R k) (S k)) :
    model.SubstitutesWithin (fun d => ∑ i, error (collectionOrder i) (reduce i d))
      (tupleCollector • (∥ k, R k)) (tupleCollector • (∥ k, S k)) :=
  substitutesWithin_smul_parallelAll R S collectionOrder tupleCollector model
    reduce closed hadvantage error step

/-- The canonical observation model admits every domain-compatible stopping typed distinguisher,
with advantage given by the difference of its decision probabilities. -/
noncomputable abbrev collectionObservationModel :=
  ConstructiveCryptography.Distinguishers.distinguisherAdvantage
    (Phi := TypedSystem) (fun _ => Set.univ)

/-- Typed absorption supplies the reductions and advantage equations for the tuple collector;
admitting all typed distinguishers discharges closure under these transformations. -/
example
    -- `R k`, `S k` are the local component pair; `error k` bounds each admitted local test.
    (R S : ∀ k, TypedSystem (collectionComponent k))
    (error : ∀ k, TypedDistinguisher (collectionComponent k) → ENNReal)
    (step : ∀ k, collectionObservationModel.SubstitutesWithin (error k) (R k) (S k)) :
    collectionObservationModel.SubstitutesWithin
      (fun d => ∑ i, error (collectionOrder i)
        (TypedDistinguisher.absorb d
          (parallelAllHybridContext R S collectionOrder tupleCollector i)))
      (tupleCollector • (∥ k, R k)) (tupleCollector • (∥ k, S k)) := by
  apply substitutesWithin_smul_parallelAll R S collectionOrder tupleCollector
    collectionObservationModel
    (fun i d => TypedDistinguisher.absorb d
      (parallelAllHybridContext R S collectionOrder tupleCollector i))
    (fun _ _ _ => Set.mem_univ _) _ error step
  intro i d U V
  -- Absorption preserves both decision probabilities, hence their absolute difference.
  exact (ConstructiveCryptography.DistinguisherAction.advantage_absorb (Phi := TypedSystem) d
    (parallelAllHybridContext R S collectionOrder tupleCollector i) U V).symm

/-- The concrete observation model also assigns zero error to an empty family. -/
example
    -- `A` has no components; `context` exposes that family at interface `C`.
    {A : Fin 0 → Interface} {C : Interface}
    (R S : ∀ k, TypedSystem (A k)) (context : TypedConverter C (⨂ k, A k)) :
    collectionObservationModel.SubstitutesWithin (fun _ => 0)
      (context • (∥ k, R k)) (context • (∥ k, S k)) := by
  simpa only [Fin.sum_univ_zero] using substitutesWithin_smul_parallelAll R S
    (Equiv.refl (Fin 0)) context collectionObservationModel
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    (fun _ _ => 0) (fun i => Fin.elim0 i)

#print axioms SystemAlgebra.Substitution.distance_parallelAll_update_le
#print axioms SystemAlgebra.Substitution.parallelAllImplication
#print axioms SystemAlgebra.Substitution.distance_smul_parallelAll_le_sum
#print axioms SystemAlgebra.Substitution.substitutesWithin_smul_parallelAll

end SystemAlgebra.Tests

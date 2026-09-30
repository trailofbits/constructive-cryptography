import ConstructiveCryptography.Substitution.Parallel
import ConstructiveCryptography.Notation
import ConstructiveCryptography.Tactics.Substitution

/-!
# Substitutions on interfaces

A single substitution establishes a construction `{R} —[π]→ …`, and the context rules of the
relaxation add an independent resource on either side (Jost, §2.2.2 and Proposition 2.2.3).
Constant converters supply the diagonal of the unrestricted converter class; a restricted class
needs its own closure under the two contexts. A calculation of statistical substitutions
`≈[ε]` joined by exact equalities gives an approximate construction `{R} —[π; ε]→ …`.

## Main results

* `unrestricted_diagonal`: constant converters are the diagonal of the unrestricted class
* `construction_with_right_context`, `construction_with_left_context`: a single substitution
  with an independent context on either side
* `constructsWithin_of_two_substitutions`: two statistical substitutions give an approximate
  construction
-/

namespace SubstitutionExamples

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra SystemAlgebra.Substitution
open scoped SystemAlgebra

/-- Constant converters supply the diagonal of the unrestricted converter class. -/
theorem unrestricted_diagonal {B : Interface} (left right : Interface.Resource B)
    (A : Interface) (resource : Interface.Resource A) :
    ∃ transformation ∈ (Set.univ : Set (A ⟶ B)),
      transformation • left = resource ∧ transformation • right = resource :=
  ⟨Interface.constant resource B, Set.mem_univ _,
    Interface.attach_constant resource left, Interface.attach_constant resource right⟩

/-- **A single substitution with a right context**: the substitution of `right` for `left`
through `transformation` constructs the simulated ideal, and an independent resource on the
right is carried along. -/
theorem construction_with_right_context {A B C D E : Interface}
    (left right : Interface.Resource B) (protocol : A ⟶ D) (simulator : A ⟶ E)
    (real : Interface.Resource D) (ideal : Interface.Resource E) (context : Interface.Resource C)
    (transformation : A ⟶ B)
    (realEq : protocol • real = transformation • left)
    (idealEq : transformation • right = simulator • ideal) :
    {real ∥ context} —[protocol ⊗ₘ 𝟙 C]→
      Specification.substitutionImage Set.univ left right {(simulator • ideal) ∥ context} := by
  have construction : {real} —[protocol]→
      Specification.substitutionImage Set.univ left right {simulator • ideal} :=
    (Specification.constructs_singleton_substitutionImage_iff
      Set.univ left right protocol simulator real ideal).mpr
      ⟨transformation, Set.mem_univ _, realEq, idealEq⟩
  have compatible := singleSubstitutionRelaxation_parallelCompatible
    (fun _ => Set.univ) left right (unrestricted_diagonal left right)
    (fun _ _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ _ => Set.mem_univ _)
  rw [← Specification.singleSubstitutionRelaxation_apply
    Set.univ left right (unrestricted_diagonal left right A)] at construction
  have result := Specification.Constructs.relax_left_context compatible construction {context}
  simp only [Specification.singleSubstitutionRelaxation_apply] at result
  exact (congrArg₂ (fun source target =>
    Specification.Constructs (protocol ⊗ₘ 𝟙 C) source
      (Specification.substitutionImage Set.univ left right target))
    (Specification.parallel_singleton real context)
    (Specification.parallel_singleton (simulator • ideal) context)).mp result

/-- **A single substitution with a left context**, in the other order. -/
theorem construction_with_left_context {A B C D E : Interface}
    (left right : Interface.Resource B) (protocol : A ⟶ D) (simulator : A ⟶ E)
    (real : Interface.Resource D) (ideal : Interface.Resource E) (context : Interface.Resource C)
    (transformation : A ⟶ B)
    (realEq : protocol • real = transformation • left)
    (idealEq : transformation • right = simulator • ideal) :
    {context ∥ real} —[𝟙 C ⊗ₘ protocol]→
      Specification.substitutionImage Set.univ left right {context ∥ (simulator • ideal)} := by
  have construction : {real} —[protocol]→
      Specification.substitutionImage Set.univ left right {simulator • ideal} :=
    (Specification.constructs_singleton_substitutionImage_iff
      Set.univ left right protocol simulator real ideal).mpr
      ⟨transformation, Set.mem_univ _, realEq, idealEq⟩
  have compatible := singleSubstitutionRelaxation_parallelCompatible
    (fun _ => Set.univ) left right (unrestricted_diagonal left right)
    (fun _ _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ _ => Set.mem_univ _)
  rw [← Specification.singleSubstitutionRelaxation_apply
    Set.univ left right (unrestricted_diagonal left right A)] at construction
  have result := Specification.Constructs.relax_right_context compatible {context} construction
  simp only [Specification.singleSubstitutionRelaxation_apply] at result
  exact (congrArg₂ (fun source target =>
    Specification.Constructs (𝟙 C ⊗ₘ protocol) source
      (Specification.substitutionImage Set.univ left right target))
    (Specification.parallel_singleton context real)
    (Specification.parallel_singleton context (simulator • ideal))).mp result

/-- A restricted class is compatible with parallel composition once it is closed under both
contexts; membership of the composed converter is not automatic. -/
example {D : Interface} (transformations : ∀ A : Interface, Set (A ⟶ D))
    (left right : Interface.Resource D)
    (diagonal : ∀ A (resource : Interface.Resource A),
      ∃ transformation ∈ transformations A,
        transformation • left = resource ∧ transformation • right = resource)
    (rightClosed : ∀ (A B : Interface) (context : Interface.Resource B)
      (transformation : A ⟶ D), transformation ∈ transformations A →
        Interface.rightContext A context ≫ transformation ∈ transformations (A ⊗ B))
    (leftClosed : ∀ (A B : Interface) (context : Interface.Resource A)
      (transformation : B ⟶ D), transformation ∈ transformations B →
        Interface.leftContext context B ≫ transformation ∈ transformations (A ⊗ B)) :
    Specification.Relaxation.ParallelCompatible
      (fun A => Specification.singleSubstitutionRelaxation
        (transformations A) left right (diagonal A)) := by
  fail_if_success
    exact singleSubstitutionRelaxation_parallelCompatible transformations left right diagonal
      (fun _ _ _ _ allowed => allowed) (fun _ _ _ _ allowed => allowed)
  exact singleSubstitutionRelaxation_parallelCompatible transformations left right diagonal
    rightClosed leftClosed

/-- **Two statistical substitutions give an approximate construction**: `R` by `H` through the
protocol, a join, `H'` by `S'` through a transformation, and a join to the simulated ideal. -/
theorem constructsWithin_of_two_substitutions {A B D E : Interface}
    (protocol : A ⟶ B) (transformation : A ⟶ D) (simulator : A ⟶ E)
    (R H : Interface.Resource B) (H' S' : Interface.Resource D) (ideal : Interface.Resource E)
    (ε₁ ε₂ : ENNReal) (first : Δ R H ≤ ε₁) (join : protocol • H = transformation • H')
    (second : Δ H' S' ≤ ε₂) (finish : transformation • S' = simulator • ideal) :
    {R} —[protocol; ε₁ + ε₂]→ {simulator • ideal} := by
  rw [Specification.constructsWithin_singleton_iff]
  cc_calc statistical
    protocol • R ≈[ε₁] protocol • H := first
    _ = transformation • H' := join
    _ ≈[ε₂] transformation • S' := second
    _ = simulator • ideal := finish

end

end SubstitutionExamples

import ConstructiveCryptography.CryptographicAlgebra.Relaxation
import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric

set_option autoImplicit false

/-!
# Distinguisher-indexed reductions

A distinguisher advantage assigns to each admitted distinguisher on an interface a symmetric
advantage satisfying the triangle inequality. Two systems substitute within an error
function when every admitted distinguisher has advantage at most its error. These
substitutions are symmetric, add errors, follow from statistical bounds, and are transported
by attachment along a reduction of distinguishers. The reduction relaxation of a
specification collects the resources within the error of one of its resources.

## Main definitions

* `DistinguisherAdvantage C Systems Distinguisher`: admitted distinguishers and their
  advantage
* `DistinguisherAdvantage.SubstitutesWithin`: substitution within an error function
* `Specification.reductionRelaxation`: the reduction relaxation

## Main results

* `SubstitutesWithin.symm`, `SubstitutesWithin.trans`, `SubstitutesWithin.of_statistical`,
  `SubstitutesWithin.of_distance`, `SubstitutesWithin.attach`,
  `SubstitutesWithin.attach_serial`
* `Specification.constructs_singleton_reductionRelaxation_iff`,
  `Specification.map_reductionRelaxation_subset`

Source: Banfi 2023, §2.3.3; Jost, Definitions 2.2.8–2.2.9 and Theorem 2.2.10.
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory

universe u v w x

/-- A typed family of admissible distinguishers and its advantage function.

Banfi 2023, Section 2.3.3 (printed p. 16) defines concrete substitution by
requiring `Δ_D(S, T) ≤ ε(D)` “for all poly-time (distinguishing) programs.”
The three advantage laws below are exactly the symmetry and triangle facts
used by the substitution and reduction-relaxation calculations. -/
structure DistinguisherAdvantage
    (C : Type u) (Systems : C → Type w) (Distinguisher : C → Type x) where
  /-- The distinguishers admitted at each resource interface. -/
  admissible : ∀ A, Set (Distinguisher A)
  /-- The distinguishing advantage between two resources in one fibre. -/
  advantage : ∀ A, Distinguisher A → Systems A → Systems A → ENNReal
  /-- A distinguisher has zero advantage between identical resources. -/
  advantage_self : ∀ A distinguisher resource,
    advantage A distinguisher resource resource = 0
  /-- Distinguishing advantage is symmetric in the compared resources. -/
  advantage_symm : ∀ A distinguisher left right,
    advantage A distinguisher left right = advantage A distinguisher right left
  /-- Distinguishing advantage satisfies the triangle inequality. -/
  advantage_triangle : ∀ A distinguisher left middle right,
    advantage A distinguisher left right ≤
      advantage A distinguisher left middle + advantage A distinguisher middle right

namespace DistinguisherAdvantage

variable {C : Type u} {Systems : C → Type w} {Distinguisher : C → Type x}

/-- Concrete substitution within one explicit distinguisher-indexed error
function.

Banfi 2023, Section 2.3.3 (printed p. 16) uses the condition
`Δ_D(S, T) ≤ ε(D)` for every admitted distinguisher `D`. -/
def SubstitutesWithin
    (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} (error : Distinguisher A → ENNReal)
    (left right : Systems A) : Prop :=
  ∀ distinguisher, distinguisher ∈ model.admissible A →
    model.advantage A distinguisher left right ≤ error distinguisher

/-- Reversing a concrete substitution preserves its error function. -/
theorem SubstitutesWithin.symm
    (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} {error : Distinguisher A → ENNReal}
    {left right : Systems A}
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin error right left := by
  intro distinguisher admitted
  -- Symmetry rewrites the reversed advantage to the supplied one.
  rw [← model.advantage_symm A distinguisher left right]
  exact substitution distinguisher admitted

/-- Consecutive concrete substitutions add their pointwise errors.

Jost 2020, Theorem 2.2.10 (printed p. 22): “the errors just adding up.” -/
theorem SubstitutesWithin.trans
    (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} {firstError secondError : Distinguisher A → ENNReal}
    {left middle right : Systems A}
    (first : model.SubstitutesWithin firstError left middle)
    (second : model.SubstitutesWithin secondError middle right) :
    model.SubstitutesWithin (fun distinguisher =>
      firstError distinguisher + secondError distinguisher) left right := by
  intro distinguisher admitted
  -- Apply the advantage triangle inequality at the named middle resource.
  exact (model.advantage_triangle A distinguisher left middle right).trans
      (add_le_add (first distinguisher admitted) (second distinguisher admitted))

/-- A uniform statistical observation bound gives a constant concrete loss.
Banfi, §2.3.1 (p. 15): “rather than a substitution”. The observation may be a
transcript distribution; a resource metric or category is not required. -/
theorem SubstitutesWithin.of_statistical
    (model : DistinguisherAdvantage C Systems Distinguisher)
    {A : C} {statistical : Distinguisher A → Systems A → Systems A → ENNReal}
    (domination : ∀ D ∈ model.admissible A, ∀ R S,
      model.advantage A D R S ≤ statistical D R S)
    {left right : Systems A} {error : ENNReal}
    (bound : ∀ D ∈ model.admissible A, statistical D left right ≤ error) :
    model.SubstitutesWithin (fun _ => error) left right := by
  intro D admitted
  exact (domination D admitted left right).trans (bound D admitted)

variable [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]

/-- A statistical step supplies a constant concrete loss, provided the selected
advantage is dominated by distance. Banfi, Section 2.3.1 (printed p. 15),
allows an approximate step "rather than a substitution". The domination
hypothesis is explicit; no computational premise is promoted to a metric bound. -/
theorem SubstitutesWithin.of_distance [MonoidalCategory C] [CompatiblePseudoMetric C Phi]
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A : C} {left right : Phi A} {error : ENNReal}
    (domination : ∀ distinguisher ∈ model.admissible A,
      ∀ first second, model.advantage A distinguisher first second ≤
        distance first second)
    (bound : distance left right ≤ error) :
    model.SubstitutesWithin (fun _ => error) left right := by
  intro distinguisher admitted
  -- Statistical distance controls this admitted distinguisher's advantage.
  exact (domination distinguisher admitted left right).trans bound

/-- An explicit black-box reduction transports a concrete substitution through
converter attachment and precomposes its error function.

Banfi 2023, Section 2.3.3 (printed p. 16) defines the transformed loss by
`ε'(D) := ε(D ∘ ρ)`. The `reduce` argument is that composed distinguisher;
its admissibility and the displayed advantage equality remain explicit. -/
theorem SubstitutesWithin.attach
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A B : C} (converter : A ⟶ B)
    (reduce : Distinguisher A → Distinguisher B)
    (reduce_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduce distinguisher ∈ model.admissible B)
    (advantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (attach converter left)
          (attach converter right) =
        model.advantage B (reduce distinguisher) left right)
    {error : Distinguisher B → ENNReal}
    {left right : Phi B}
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin (fun distinguisher => error (reduce distinguisher))
      (attach converter left)
      (attach converter right) := by
  intro distinguisher admitted
  -- Replace the transformed advantage by that of the supplied reduction.
  rw [advantage_eq]
  -- Efficiency closure admits the reduced distinguisher at the source fibre.
  exact substitution (reduce distinguisher)
    (reduce_admissible distinguisher admitted)

/-- Serial black-box reductions compose by nesting their distinguisher maps.

This is the iterated form of Banfi 2023, Section 2.3.3 (printed p. 16):
the final loss is `error (reduceInner (reduceOuter D))`, matching successive
precomposition by the two named transformations. -/
theorem SubstitutesWithin.attach_serial
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A B D : C} (outer : A ⟶ B) (inner : B ⟶ D)
    (reduceOuter : Distinguisher A → Distinguisher B)
    (reduceInner : Distinguisher B → Distinguisher D)
    (reduceOuter_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduceOuter distinguisher ∈ model.admissible B)
    (reduceInner_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible B →
        reduceInner distinguisher ∈ model.admissible D)
    (outerAdvantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (ConstructiveCryptography.CryptographicAlgebra.attach
            outer left)
          (ConstructiveCryptography.CryptographicAlgebra.attach
            outer right) =
        model.advantage B (reduceOuter distinguisher) left right)
    (innerAdvantage_eq : ∀ distinguisher left right,
      model.advantage B distinguisher
          (ConstructiveCryptography.CryptographicAlgebra.attach
            inner left)
          (ConstructiveCryptography.CryptographicAlgebra.attach
            inner right) =
        model.advantage D (reduceInner distinguisher) left right)
    {error : Distinguisher D → ENNReal}
    {left right : Phi D}
    (substitution : model.SubstitutesWithin error left right) :
    model.SubstitutesWithin
      (fun distinguisher => error (reduceInner (reduceOuter distinguisher)))
      (ConstructiveCryptography.CryptographicAlgebra.attach
        (outer ≫ inner) left)
      (ConstructiveCryptography.CryptographicAlgebra.attach
        (outer ≫ inner) right) := by
  -- First reduce through the inner transformation.
  have innerSubstitution := SubstitutesWithin.attach model inner reduceInner
    reduceInner_admissible innerAdvantage_eq substitution
  -- Then reduce the resulting statement through the outer transformation.
  have outerSubstitution := SubstitutesWithin.attach model outer reduceOuter
    reduceOuter_admissible outerAdvantage_eq innerSubstitution
  -- Serial attachment applies the inner converter first.
  simpa only [ConstructiveCryptography.CryptographicAlgebra.attach_serial]
    using outerSubstitution

end DistinguisherAdvantage

namespace Specification

variable {C : Type u} {Phi : C → Type w} {Distinguisher : C → Type x}

/-- Jost's pointwise reduction relaxation for one explicit advantage model and
distinguisher-indexed error function.

Jost 2020, Definition 2.2.9 (printed p. 22):
“`R^ε := {S | ∀D : |Δ^D(R,S)| ≤ ε(D)}`.” -/
noncomputable def reductionRelaxation
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A : C} (error : Distinguisher A → ENNReal) :
    ConstructiveCryptography.Relaxation (Phi A) :=
  ConstructiveCryptography.Relaxation.ofPointwise
    (fun center => {resource | model.SubstitutesWithin error center resource})
    (fun resource distinguisher _ => by
      -- Reflexive advantage is zero and every error is nonnegative.
      rw [model.advantage_self]
      exact bot_le)

@[simp]
theorem mem_reductionRelaxation_iff
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A : C} {error : Distinguisher A → ENNReal}
    {source : Specification (Phi A)} {resource : Phi A} :
    resource ∈ reductionRelaxation model error source ↔
      ∃ center ∈ source, model.SubstitutesWithin error center resource :=
  ConstructiveCryptography.Relaxation.mem_ofPointwise_iff

/-- Successive reduction relaxations add their errors pointwise.

Jost 2020, Theorem 2.2.10 (printed p. 22):
`(R^{ε₁})^{ε₂} ⊆ R^{ε₁+ε₂}`. -/
theorem reductionRelaxation_reductionRelaxation_subset
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A : C} (firstError secondError : Distinguisher A → ENNReal)
    (source : Specification (Phi A)) :
    reductionRelaxation model secondError
        (reductionRelaxation model firstError source) ⊆
      reductionRelaxation model
        (fun distinguisher => firstError distinguisher + secondError distinguisher)
        source := by
  intro resource relaxed
  rw [mem_reductionRelaxation_iff] at relaxed ⊢
  obtain ⟨middle, middleRelaxed, second⟩ := relaxed
  rw [mem_reductionRelaxation_iff] at middleRelaxed
  obtain ⟨center, admitted, first⟩ := middleRelaxed
  -- Transitivity uses the same distinguisher at both consecutive steps.
  exact ⟨center, admitted,
    DistinguisherAdvantage.SubstitutesWithin.trans model first second⟩

variable [Category.{v} C] [ResourceTheory C Phi]

/-- A concrete real/ideal reduction bound is the existing singleton
construction into Jost's reduction relaxation.

Jost, Definition 2.2.9 (printed p. 22): "R^ε := {S | ∀D : |Δᴰ(R,S)| ≤ ε(D)}".
MR16, Definition 1 (printed p. 11): "π R ⊆ S". The supplied ideal may
already have its explicitly chosen simulator attached. -/
theorem constructs_singleton_reductionRelaxation_iff
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A B : C} {protocol : A ⟶ B} {real : Phi B} {ideal : Phi A}
    {error : Distinguisher A → ENNReal} :
    Constructs protocol {real} (reductionRelaxation model error {ideal}) ↔
      model.SubstitutesWithin error (attach protocol real) ideal := by
  constructor
  · intro construction
    -- The singleton target supplies its unique center, namely the ideal.
    obtain ⟨center, centerEq, bound⟩ := (mem_reductionRelaxation_iff model).mp
      (constructs_iff.mp construction real (Set.mem_singleton _))
    obtain rfl := Set.mem_singleton_iff.mp centerEq
    exact DistinguisherAdvantage.SubstitutesWithin.symm model bound
  · intro bound
    apply constructs_iff.mpr
    intro resource admitted
    obtain rfl := Set.mem_singleton_iff.mp admitted
    -- Symmetry reconciles the real-first comparison with Jost's center-first set.
    exact (mem_reductionRelaxation_iff model).mpr
      ⟨ideal, Set.mem_singleton _, DistinguisherAdvantage.SubstitutesWithin.symm model bound⟩

/-- Converter attachment pulls a reduction relaxation through its image and
precomposes the error function with the explicit reduction.

Jost 2020, Theorem 2.2.11 (printed p. 22) states
`π(R^ε) ⊆ (πR)^{ε_π}` with `ε_π(D) := ε(Dπ(·))`. -/
theorem map_reductionRelaxation_subset
    (model : DistinguisherAdvantage C Phi Distinguisher)
    {A B : C} (converter : A ⟶ B)
    (reduce : Distinguisher A → Distinguisher B)
    (reduce_admissible : ∀ distinguisher,
      distinguisher ∈ model.admissible A →
        reduce distinguisher ∈ model.admissible B)
    (advantage_eq : ∀ distinguisher left right,
      model.advantage A distinguisher
          (attach converter left)
          (attach converter right) =
        model.advantage B (reduce distinguisher) left right)
    (error : Distinguisher B → ENNReal) (source : Specification (Phi B)) :
    map converter (reductionRelaxation model error source) ⊆
      reductionRelaxation model (fun distinguisher => error (reduce distinguisher))
        (map converter source) := by
  rintro resource ⟨original, originalRelaxed, rfl⟩
  rw [mem_reductionRelaxation_iff] at originalRelaxed ⊢
  obtain ⟨center, admitted, close⟩ := originalRelaxed
  -- Attach the converter to the selected unrelaxed center.
  refine ⟨attach converter center, ⟨center, admitted, rfl⟩, ?_⟩
  -- Banfi's composed distinguisher supplies the transformed bound.
  exact DistinguisherAdvantage.SubstitutesWithin.attach model
    converter reduce reduce_admissible advantage_eq close

end Specification
end ConstructiveCryptography.CryptographicAlgebra

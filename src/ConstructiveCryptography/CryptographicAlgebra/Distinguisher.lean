import ConstructiveCryptography.CryptographicAlgebra.PseudoMetric

set_option autoImplicit false

/-!
# Compatible distinguisher classes

A distinguisher on an interface assigns to each resource the probability that it outputs
`1` when connected to the resource. The advantage distance of a class of distinguishers is
the largest difference of these probabilities (Maurer 2011, §4.5:
`d(R, S) = sup_{D ∈ 𝒟} Δ^D(R, S)`). A class is compatible when it is closed under absorbing
a converter and under running a fixed resource beside the distinguished one (MR11,
Definition 16); its advantage distance is then a compatible pseudo-metric (Maurer 2011,
Lemma 1).

## Main definitions

* `advantageDistance D R S`: the advantage distance of a class `D`
* `CompatibleDistinguisherClass C Φ`: a compatible pseudo-metric that is the advantage
  distance of a closed class of distinguishers

## Main results

* `CompatibleDistinguisherClass.ofClosure`: Maurer 2011, Lemma 1
-/

namespace ConstructiveCryptography

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

/-- The advantage distance of a class of distinguishers: the largest difference of the
probabilities that a distinguisher outputs `1`. -/
noncomputable def advantageDistance {X : Type*} (distinguishers : Set (X → ℝ)) (R S : X) :
    ENNReal :=
  ⨆ d ∈ distinguishers, ENNReal.ofReal |d R - d S|

theorem advantageDistance_le {X : Type*} {distinguishers : Set (X → ℝ)} {R S : X}
    {ε : ENNReal} (h : ∀ d ∈ distinguishers, ENNReal.ofReal |d R - d S| ≤ ε) :
    advantageDistance distinguishers R S ≤ ε :=
  iSup₂_le h

theorem le_advantageDistance {X : Type*} {distinguishers : Set (X → ℝ)} {d : X → ℝ}
    (hd : d ∈ distinguishers) (R S : X) :
    ENNReal.ofReal |d R - d S| ≤ advantageDistance distinguishers R S :=
  le_iSup₂ (f := fun d (_ : d ∈ distinguishers) => ENNReal.ofReal |d R - d S|) d hd

/-- The advantage distance is a pseudo-metric. -/
@[reducible] noncomputable def advantagePseudoEMetricSpace {X : Type*} (distinguishers : Set (X → ℝ)) :
    PseudoEMetricSpace X where
  edist := advantageDistance distinguishers
  edist_self R := by
    refine le_antisymm ?_ bot_le
    apply advantageDistance_le
    intro d _
    simp
  edist_comm R S := by
    unfold advantageDistance
    congr 1; ext d; congr 1; ext _
    rw [abs_sub_comm]
  edist_triangle R S T := by
    apply advantageDistance_le
    intro d hd
    calc ENNReal.ofReal |d R - d T|
        ≤ ENNReal.ofReal (|d R - d S| + |d S - d T|) :=
          ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
      _ ≤ ENNReal.ofReal |d R - d S| + ENNReal.ofReal |d S - d T| := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add (le_advantageDistance hd R S) (le_advantageDistance hd S T)

open CryptographicAlgebra in
/-- **A compatible distinguisher class** (MR11, Definition 16; Maurer 2011, §4.5): the
compatible pseudo-metric is the advantage distance of a class of distinguishers on each
interface, closed under absorbing a converter and under running a fixed resource beside the
distinguished one. -/
class CompatibleDistinguisherClass
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (Phi : C → Type w) [ResourceTheory C Phi] extends CompatiblePseudoMetric C Phi where
  distinguishers : ∀ A : C, Set (Phi A → ℝ)
  closed_attach : ∀ {A B : C} (converter : A ⟶ B) {d : Phi A → ℝ},
    d ∈ distinguishers A → (fun R => d (attach converter R)) ∈ distinguishers B
  closed_parallel_left : ∀ {A B : C} (T : Phi B) {d : Phi (A ⊗ B) → ℝ},
    d ∈ distinguishers (A ⊗ B) →
      (fun R => d (resourceParallel laxMonoidal R T)) ∈ distinguishers A
  closed_parallel_right : ∀ {A B : C} (T : Phi A) {d : Phi (A ⊗ B) → ℝ},
    d ∈ distinguishers (A ⊗ B) →
      (fun S => d (resourceParallel laxMonoidal T S)) ∈ distinguishers B
  edist_eq : ∀ {A : C} (R S : Phi A),
    @edist _ (fibreMetric A).toEDist R S = advantageDistance (distinguishers A) R S

namespace CompatibleDistinguisherClass

open CryptographicAlgebra

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {Phi : C → Type w} [ResourceTheory C Phi]

/-- **Closed classes give compatible pseudo-metrics** (Maurer 2011, Lemma 1): the advantage
distance of a class closed under absorbing converters and running fixed resources beside
the distinguished one is non-expanding under attachment and adds under parallel
composition. -/
@[reducible] noncomputable def ofClosure [CryptographicAlgebra C Phi]
    (distinguishers : ∀ A : C, Set (Phi A → ℝ))
    (closed_attach : ∀ {A B : C} (converter : A ⟶ B) {d : Phi A → ℝ},
      d ∈ distinguishers A → (fun R => d (attach converter R)) ∈ distinguishers B)
    (closed_parallel_left : ∀ {A B : C} (T : Phi B) {d : Phi (A ⊗ B) → ℝ},
      d ∈ distinguishers (A ⊗ B) →
        (fun R => d (parallel R T)) ∈ distinguishers A)
    (closed_parallel_right : ∀ {A B : C} (T : Phi A) {d : Phi (A ⊗ B) → ℝ},
      d ∈ distinguishers (A ⊗ B) →
        (fun S => d (parallel T S)) ∈ distinguishers B) :
    CompatibleDistinguisherClass C Phi where
  toCryptographicAlgebra := inferInstance
  fibreMetric A := advantagePseudoEMetricSpace (distinguishers A)
  edist_smul_le converter R S := by
    apply advantageDistance_le
    intro d hd
    exact le_advantageDistance (closed_attach converter hd) R S
  edist_parallel_le R R' S S' := by
    apply advantageDistance_le
    intro d hd
    calc ENNReal.ofReal |d (parallel R S) - d (parallel R' S')|
        ≤ ENNReal.ofReal (|d (parallel R S) - d (parallel R' S)| +
            |d (parallel R' S) - d (parallel R' S')|) :=
          ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
      _ ≤ ENNReal.ofReal |d (parallel R S) - d (parallel R' S)| +
            ENNReal.ofReal |d (parallel R' S) -
              d (parallel R' S')| := ENNReal.ofReal_add_le
      _ ≤ _ := add_le_add
          (le_advantageDistance (closed_parallel_left S hd) R R')
          (le_advantageDistance (closed_parallel_right R' hd) S S')
  distinguishers := distinguishers
  closed_attach := closed_attach
  closed_parallel_left T _ hd := closed_parallel_left T hd
  closed_parallel_right T _ hd := closed_parallel_right T hd
  edist_eq _ _ := rfl

end CompatibleDistinguisherClass

end ConstructiveCryptography

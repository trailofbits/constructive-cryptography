import ConstructiveCryptography.Distinguisher
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

In Lean a distinguisher on interface `A` is just a real-valued function `d : Phi A → ℝ`.
Its reading as an output-1 probability is the intended model only: no range `[0, 1]`,
measurability or efficiency is required, and the class `distinguishers A` is an arbitrary
set, possibly empty, closed only under the operations its hypotheses list. The distance is
`ENNReal`-valued and may be `∞` for unbounded test functions.

This class concerns the metric only, and its closure fields serve the metric laws. On
interfaces its test functions are the evaluation maps `R ↦ Distinguishers.probability d R`
of all compatible typed distinguishers (`Interface.distinguishers A`). The admitted tests of
a computational substitution are chosen separately, by `AdmissibleDistinguishers`, and carry
no such closure.

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
probabilities that a distinguisher outputs `1`:

```text
advantageDistance distinguishers R S = ⨆_{d ∈ distinguishers} ofReal |d R - d S|  ∈ ENNReal
```

the supremum over an empty class being `0`. When the values `d R` are output-1
probabilities this is Maurer 2011's `sup_{D ∈ 𝒟} Δ^D(R, S)`. -/
noncomputable def advantageDistance
    -- `X` is the type of resources; `distinguishers` is a set of test functions `d : X → ℝ`,
    -- which may take arbitrary real values.
    {X : Type*} (distinguishers : Set (X → ℝ))
    -- `R S : X` are the two resources whose test outputs `d R`, `d S` are compared.
    (R S : X) :
    ENNReal :=
  ⨆ d ∈ distinguishers, ENNReal.ofReal |d R - d S|

/-- A bound `ε : ENNReal` on every admitted distinguisher's advantage `|d R - d S|` bounds
the advantage distance of `R` and `S`. -/
lemma advantageDistance_le {X : Type*} {distinguishers : Set (X → ℝ)} {R S : X}
    {ε : ENNReal} (h : ∀ d ∈ distinguishers, ENNReal.ofReal |d R - d S| ≤ ε) :
    advantageDistance distinguishers R S ≤ ε :=
  iSup₂_le h

/-- Each admitted distinguisher's advantage `|d R - d S|` is at most the advantage distance
of `R` and `S`. -/
lemma le_advantageDistance {X : Type*} {distinguishers : Set (X → ℝ)} {d : X → ℝ}
    (hd : d ∈ distinguishers) (R S : X) :
    ENNReal.ofReal |d R - d S| ≤ advantageDistance distinguishers R S :=
  le_iSup₂ (f := fun d (_ : d ∈ distinguishers) => ENNReal.ofReal |d R - d S|) d hd

/-- The advantage distance is a pseudo-metric on `X`, for any set of real test functions:
`d(R, R) = 0`, symmetry from `|a - b| = |b - a|`, and the triangle inequality for each
distinguisher, `|d R - d T| ≤ |d R - d S| + |d S - d T|`, passed to the supremum. Separation
is not required: resources that no admitted distinguisher tells apart are at distance zero,
even if they are distinct. -/
@[reducible] noncomputable def advantagePseudoEMetricSpace {X : Type*}
    (distinguishers : Set (X → ℝ)) :
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
distinguished one.

These are the only closure properties assumed; the class need not contain every efficient
distinguisher, and the inherited `edist_smul_le`, `edist_parallel_le` still appear as fields
(`ofClosure` derives them). -/
class CompatibleDistinguisherClass
    -- Objects `A : C` are interfaces, morphisms `A ⟶ B` converters, and `A ⊗ B` places two
    -- interfaces side by side.
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    -- `Phi A` is the type of resources on `A`, with attachment; the inherited
    -- `fibreMetric A` on `Phi A` is the metric identified with an advantage distance.
    (Phi : C → Type w) [ResourceTheory C Phi] extends CompatiblePseudoMetric C Phi where
  /-- The selected distinguishers on interface `A`: real test functions on `Phi A`. -/
  distinguishers : ∀ A : C, Set (Phi A → ℝ)
  /-- Absorbing `converter : A ⟶ B` into an admitted `d` on `A` gives an admitted
  distinguisher `R ↦ d(converter • R)` on `B`:

  ```text
  d ── converter ── R          d on A, converter : A ⟶ B, R : Phi B
  ```
  -/
  closed_attach : ∀ {A B : C} (converter : A ⟶ B) {d : Phi A → ℝ},
    d ∈ distinguishers A → (fun R => d (attach converter R)) ∈ distinguishers B
  /-- Running a fixed `T : Phi B` to the right of the tested resource: if `d` is admitted on
  `A ⊗ B`, then `R ↦ d(R ∥ T)` is admitted on `A`, `∥` being the selected `parallel`. Every
  resource `T` is allowed, with no efficiency restriction on it. -/
  closed_parallel_left : ∀ {A B : C} (T : Phi B) {d : Phi (A ⊗ B) → ℝ},
    d ∈ distinguishers (A ⊗ B) →
      (fun R => d (resourceParallel laxMonoidal R T)) ∈ distinguishers A
  /-- Running a fixed `T : Phi A` to the left of the tested resource: if `d` is admitted on
  `A ⊗ B`, then `S ↦ d(T ∥ S)` is admitted on `B`. -/
  closed_parallel_right : ∀ {A B : C} (T : Phi A) {d : Phi (A ⊗ B) → ℝ},
    d ∈ distinguishers (A ⊗ B) →
      (fun S => d (resourceParallel laxMonoidal T S)) ∈ distinguishers B
  /-- The selected fibre metric on `Phi A` equals the advantage distance of
  `distinguishers A`. -/
  edist_eq : ∀ {A : C} (R S : Phi A),
    @edist _ (fibreMetric A).toEDist R S = advantageDistance (distinguishers A) R S

namespace CompatibleDistinguisherClass

open CryptographicAlgebra

-- Objects `A : C` are interfaces with converters `A ⟶ B` and side-by-side `A ⊗ B`;
-- `Phi A` is the type of resources on `A`, on which converters act by attachment.
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {Phi : C → Type w} [ResourceTheory C Phi]

/-- **Closed classes give compatible pseudo-metrics** (Maurer 2011, Lemma 1): the advantage
distance of a class closed under absorbing converters and running fixed resources beside
the distinguished one is non-expanding under attachment and adds under parallel
composition. The result sets `fibreMetric A` to the advantage distance of
`distinguishers A`; callers install the chosen structure locally. The two compatibility laws
follow per admitted distinguisher `d`, embedding each absolute advantage into `ENNReal`:

```text
|d(αR) - d(αS)|                       ≤ adv(R, S)     d ∘ attach α is admitted on B
|d(R ∥ S) - d(R' ∥ S')|
  ≤ |d(R ∥ S) - d(R' ∥ S)| + |d(R' ∥ S) - d(R' ∥ S')|  triangle inequality in ℝ
  ≤ adv(R, R') + adv(S, S')           d(· ∥ S), d(R' ∥ ·) are admitted on A and B
```

Here `adv` is the advantage distance and `∥` the selected `parallel`. -/
@[reducible] noncomputable def ofClosure [CryptographicAlgebra C Phi]
    -- `distinguishers A` is the selected set of real test functions on `Phi A`, for each
    -- interface `A : C`.
    (distinguishers : ∀ A : C, Set (Phi A → ℝ))
    -- `closed_attach`: absorbing `converter : A ⟶ B` into an admitted `d` on `A` gives the
    -- admitted `R ↦ d(converter • R)` on `B`.
    (closed_attach : ∀ {A B : C} (converter : A ⟶ B) {d : Phi A → ℝ},
      d ∈ distinguishers A → (fun R => d (attach converter R)) ∈ distinguishers B)
    -- `closed_parallel_left`: for any fixed `T : Phi B` and admitted `d` on `A ⊗ B`,
    -- `R ↦ d(R ∥ T)` is admitted on `A`.
    (closed_parallel_left : ∀ {A B : C} (T : Phi B) {d : Phi (A ⊗ B) → ℝ},
      d ∈ distinguishers (A ⊗ B) →
        (fun R => d (parallel R T)) ∈ distinguishers A)
    -- `closed_parallel_right`: for any fixed `T : Phi A` and admitted `d` on `A ⊗ B`,
    -- `S ↦ d(T ∥ S)` is admitted on `B`.
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

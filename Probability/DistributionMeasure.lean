/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Expectation
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-!
# One-way transport of `Distribution` into mathlib's probability stack

The bridge from the library's signed, unnormalized `Distribution A = A →₀ ℝ` on
a `Fintype` carrier into mathlib's `PMF`/`Measure` stack, at the **bottom layer
only**: `isProbDist → PMF`.

This module supplies the finite-carrier bridge used by
`Probability.Divergence`.

## What is deliberately NOT here

The bridge deliberately stops at `isProbDist → PMF`; it does not define maps
from arbitrary nonnegative distributions to measures or from signed
distributions to signed measures.

## Instance discipline

Measure-theoretic instances are introduced at the proof site
(`letI : MeasurableSpace A := ⊤`), never in a `Distribution`/ℝ-facing
signature.  The transport machinery itself necessarily carries
`[MeasurableSpace A]` (+ `[MeasurableSingletonClass A]`): its conclusions *are*
measure-theory objects, so no `Distribution`/ℝ spelling of them exists.  Any
`Fintype` carrier enters the bridge by taking the `⊤` σ-algebra at the use
site; `@DiscreteMeasurableSpace α ⊤` is an instance and supplies
`MeasurableSingletonClass`.

`toPMF` itself needs no measurable-space structure at all: a `PMF` is a bare
`ℝ≥0∞`-valued mass function summing to one.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Probability

namespace Distribution

variable {A : Type*} [Fintype A]

/-- Transport of a probability `Distribution` on a `Fintype` carrier into
mathlib's `PMF`.  The `isProbDist` hypothesis is not decoration: `ENNReal.ofReal`
truncates negative mass, so on the signed carrier this map is lossy, and total
weight one is what makes the result a `PMF` at all. -/
def toPMF (X : Distribution A) (hX : X.isProbDist) : _root_.PMF A :=
  ⟨fun a => ENNReal.ofReal (X a), by
    have hsum : ∑ a, ENNReal.ofReal (X a) = 1 := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hX.1 a), ← weight_eq_sum,
        hX.2, ENNReal.ofReal_one]
    simpa [hsum] using hasSum_fintype fun a => ENNReal.ofReal (X a)⟩

/-- Pointwise value of the transported `PMF`. -/
@[simp]
theorem toPMF_apply (X : Distribution A) (hX : X.isProbDist) (a : A) :
    toPMF X hX a = ENNReal.ofReal (X a) := rfl

/-- The round trip through `ℝ≥0∞` is lossless on an honest probability
distribution. -/
theorem toPMF_apply_toReal (X : Distribution A) (hX : X.isProbDist) (a : A) :
    (toPMF X hX a).toReal = X a :=
  ENNReal.toReal_ofReal (hX.1 a)

section MeasurableSpace

variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- **The integral bridge**: the library expectation `Distribution.expect` is the
Bochner integral against the transported measure.  This is the identity that
lets mathlib's integral-vocabulary theorems land on `Distribution`
statements. -/
theorem integral_toPMF_eq_expect (X : Distribution A) (hX : X.isProbDist) (f : A → ℝ) :
    ∫ a, f a ∂(toPMF X hX).toMeasure = X.expect f := by
  rw [PMF.integral_eq_sum, expect_eq_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [toPMF_apply, ENNReal.toReal_ofReal (hX.1 a), smul_eq_mul]

/-- Event-mass correspondence: the transported measure of an event is
`ENNReal.ofReal` of its `Distribution.mass`. -/
theorem toPMF_toMeasure_apply (X : Distribution A) (hX : X.isProbDist) (P : A → Prop) :
    (toPMF X hX).toMeasure {a | P a} = ENNReal.ofReal (X.mass P) := by
  classical
  rw [show {a | P a} = ↑(Finset.univ.filter P) by ext a; simp,
    PMF.toMeasure_apply_finset, mass_eq_sum,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => by split <;> simp [hX.1 a])]
  simp [Finset.sum_filter, apply_ite ENNReal.ofReal]

end MeasurableSpace

end Distribution

end Probability

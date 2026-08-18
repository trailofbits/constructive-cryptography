/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography
import AbstractCryptography.MR11

/-!
# Non-vacuity of the indexed ε-relaxation

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

`AbstractCryptography.Metric.Epsilon` proves, abstractly, that a scalar
pseudo-emetric ball is exactly Jost Definition 2.2.9's indexed relaxation at a
**constant** budget (`reductionRelaxation_const_eq_epsilonRelaxation`), and gives a
criterion under which an indexed budget is matched by **no** scalar radius
(`reductionRelaxation_singleton_ne_epsilonRelaxation`).  Neither statement is worth
anything until a distinguisher class satisfying the criterion is exhibited, so
this file exhibits the smallest one.

Three resources and two tests suffice.  The centre `0` is passed by both
tests; `1` is detected by the first test only and `2` by the second only.  The
indexed budget charges the first test `0` and the second test `1`.  Then

* `2` is admitted — the only test that separates it from the centre is the one
  with the generous budget;
* `1` is rejected — it is separated by the test with budget `0`;
* yet `1` and `2` are at the *same* class distance `1` from the centre.

A scalar radius sees only that distance, so it must either admit both or reject
both.  The indexed budget admits exactly one of them, and therefore equals no
scalar ball at any radius (`separation`).  This is the expressiveness gap
between CR18's `ε`-relaxation and Jost's: the indexed form can charge different
distinguishers different amounts, and that distinction is invisible to a
supremum.

This is a non-default target, kept out of the public root: it is the only place
in the package that fixes a concrete carrier.  Build with
`lake build AbstractCryptographyIndexedRelaxationTests`.
-/

namespace AbstractCryptography.IndexedRelaxationSeparation

open scoped ENNReal
open DistinguisherClass

/-- The three-state resource carrier: `0` is the specification's centre, `1`
and `2` are the two deviations. -/
abbrev Phi : Type := Fin 3

/-- The converter monoid is trivial; nothing in the separation depends on
protocol application, so the neutral action is the honest choice. -/
instance : SMul Unit Phi := ⟨fun _ q => q⟩

/-- The test that detects state `1`. -/
noncomputable def testOne : Phi → ℝ≥0∞ := fun q => if q = 1 then 1 else 0

/-- The test that detects state `2`. -/
noncomputable def testTwo : Phi → ℝ≥0∞ := fun q => if q = 2 then 1 else 0

@[simp] theorem testOne_zero : testOne 0 = 0 := by
  simp only [testOne, if_neg (show (0 : Phi) ≠ 1 by decide)]

@[simp] theorem testOne_one : testOne 1 = 1 := by
  simp [testOne]

@[simp] theorem testOne_two : testOne 2 = 0 := by
  simp only [testOne, if_neg (show (2 : Phi) ≠ 1 by decide)]

@[simp] theorem testTwo_zero : testTwo 0 = 0 := by
  simp only [testTwo, if_neg (show (0 : Phi) ≠ 2 by decide)]

@[simp] theorem testTwo_one : testTwo 1 = 0 := by
  simp only [testTwo, if_neg (show (1 : Phi) ≠ 2 by decide)]

@[simp] theorem testTwo_two : testTwo 2 = 1 := by
  simp [testTwo]

/-- The two-test distinguisher class.  Closure under converter emulation
(MauRen11 Def 16) is immediate because the action is neutral. -/
noncomputable def sepClass : DistinguisherClass Unit Phi where
  tests := {testOne, testTwo}
  test_le_one := by
    rintro t (rfl | rfl) q <;> fin_cases q <;> simp
  test_attach := by
    rintro c t ht
    exact ht

theorem mem_sepClass_tests {t : Phi → ℝ≥0∞} :
    t ∈ sepClass.tests ↔ t = testOne ∨ t = testTwo := by
  simp [sepClass, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- **The indexed budget.**  Written as `1 - D(1)` so that it is a genuine
function of the distinguisher rather than a case split: the first test, which
fires on state `1`, is charged `0`; the second, which does not, is charged `1`.

This is precisely the shape a reduction gives in practice — the budget is read
off the distinguisher, not fixed in advance. -/
noncomputable def budget : sepClass.tests → ℝ≥0∞ := fun t => 1 - t.1 1

@[simp] theorem budget_testOne (h : testOne ∈ sepClass.tests) :
    budget ⟨testOne, h⟩ = 0 := by simp [budget]

@[simp] theorem budget_testTwo (h : testTwo ∈ sepClass.tests) :
    budget ⟨testTwo, h⟩ = 1 := by simp [budget]

/-- The specification: the single centre resource. -/
abbrev centre : Set Phi := {(0 : Phi)}

/-- State `2` is admitted by the indexed budget: the only test separating it
from the centre is the one carrying the generous budget. -/
theorem two_mem : (2 : Phi) ∈ sepClass.reductionRelaxation budget centre := by
  refine mem_reductionRelaxation_iff.mpr ⟨0, rfl, ?_⟩
  rintro ⟨t, ht⟩
  rcases mem_sepClass_tests.mp ht with rfl | rfl
  · simp [adv]
  · simp [adv]

/-- State `1` is rejected by the indexed budget: it is separated by the test
whose budget is `0`. -/
theorem one_not_mem : (1 : Phi) ∉ sepClass.reductionRelaxation budget centre := by
  intro hmem
  obtain ⟨q, hq, hb⟩ := mem_reductionRelaxation_iff.mp hmem
  rw [Set.mem_singleton_iff] at hq
  subst hq
  have h := hb ⟨testOne, by simp [mem_sepClass_tests]⟩
  simp [adv] at h

/-- Both deviations sit at class distance exactly `1` from the centre — the
scalar metric cannot tell them apart. -/
theorem edistD_one_le_edistD_two :
    sepClass.edistD 1 0 ≤ sepClass.edistD 2 0 := by
  refine le_trans (sepClass.edistD_le_one 1 0) ?_
  refine le_trans (le_of_eq ?_)
    (sepClass.adv_le_edistD (t := testTwo) (by simp [mem_sepClass_tests]) 2 0)
  simp [adv]

/-- **The separation.**  The indexed relaxation of `centre` at `budget` is
equal to `Relaxation.epsilonRelaxation c centre` for **no** radius `c` whatsoever.

Every scalar `ε`-relaxation of this specification either contains both
deviations or neither; the indexed one contains exactly `2`.  So this is an
indexed-`ε` statement with no scalar expression — the concrete witness that
Jost Definition 2.2.9 is strictly more expressive than CR18's scalar ball, and
hence that the indexed layer is not a notational variant of `epsilonRelaxation`. -/
theorem separation (c : ℝ≥0∞) :
    letI := sepClass.toPseudoEMetricSpace
    sepClass.reductionRelaxation budget centre ≠ Relaxation.epsilonRelaxation c centre :=
  letI := sepClass.toPseudoEMetricSpace
  sepClass.reductionRelaxation_singleton_ne_epsilonRelaxation (fun _ _ => rfl)
    two_mem one_not_mem edistD_one_le_edistD_two c

/-- By contrast, the **constant** budget is a scalar ball on the nose — the
recovery theorem, instantiated.  Nothing forked: `epsilonRelaxation` is the indexed
relaxation whenever the budget does not vary with the distinguisher. -/
theorem constant_budget_is_epsilonRelaxation (ε : ℝ≥0∞) :
    letI := sepClass.toPseudoEMetricSpace
    sepClass.reductionRelaxation (fun _ => ε) = Relaxation.epsilonRelaxation (Φ := Phi) ε :=
  sepClass.reductionRelaxation_const_eq_epsilonRelaxation_self ε

end AbstractCryptography.IndexedRelaxationSeparation

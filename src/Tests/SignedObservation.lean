module

public import RandomSystems.Distance.SignedObservation
public import Tests.Guessing

/-!
# Cancellation of signed decision gaps

Two observers query the same one-bit systems. One reports the reply and one reports its
complement. Sampling the observer with a fair bit gives signed gap zero, although each
individual gap has magnitude one.
-/

@[expose] public section

namespace Tests.SignedObservation

open SystemAlgebra SystemAlgebra.Tests SystemAlgebra.Tests.MixtureObservation
open Tests.Guessing.Operational
open Probability Distribution

noncomputable section

/-- Query the bit once and decide one when the reply is false. -/
def opposite : bitInterface.inputDomain.Distinguisher :=
  ProbDist.single ⟨envProbe bitQuery (fun t => t.1.zip t.2 ≠ trueTranscript),
    envProbe_isDDD bitQuery_bounded, Domain.envProbe_decisionCompatible bitQuery_compatible _⟩

/-- The two observers test complementary events on the same completed transcript. -/
lemma probability_add_opposite (R : TypedSystem bitInterface) :
    observer.probability R.1 + opposite.probability R.1 = 1 := by
  simp only [observer, opposite, ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul,
    RandomSystem.decisionProbability_envProbe bitQuery_bounded _ R.2, mass_add_compl]
  exact (R.1.sLaw_isProbDist (bitQuery_compatible R.1 R.2) 1).2

/-- The selected observer reports the reply when `readBit` is true and its complement otherwise. -/
def selected (readBit : Bool) : bitInterface.inputDomain.Distinguisher :=
  if readBit then observer else opposite

/-- Against the true and false systems the two individual signed gaps are `1` and `−1`. -/
lemma selected_gap (readBit : Bool) :
    (selected readBit).signedGap (fixedBit true).1 (fixedBit false).1 =
      if readBit then 1 else -1 := by
  have ht := probability_add_opposite (fixedBit true)
  have hf := probability_add_opposite (fixedBit false)
  have yes : observer.probability (fixedBit true).1 = 1 := observer_probability true
  have no : observer.probability (fixedBit false).1 = 0 := observer_probability false
  cases readBit <;> simp only [selected, Domain.Distinguisher.signedGap, Bool.false_eq_true,
    ↓reduceIte] <;> linarith only [ht, hf, yes, no]

/-- The sampled signed gap is zero and the mean absolute gap is one. -/
theorem opposite_gaps_cancel :
    Domain.Distinguisher.signedGap ((ProbDist.uniform Bool).bind selected)
        (fixedBit true).1 (fixedBit false).1 = 0 ∧
      (uniform Bool).expect (fun b => |(selected b).signedGap
        (fixedBit true).1 (fixedBit false).1|) = 1 := by
  rw [Domain.Distinguisher.signedGap_bind]
  simp only [expect_eq_sum, Fintype.sum_bool]
  rw [selected_gap true, selected_gap false]
  norm_num [ProbDist.uniform, uniform_apply]

end

end Tests.SignedObservation

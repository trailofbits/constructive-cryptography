module

public import RandomSystems.Cumulative.Mixture
public import RandomSystems.Typed.SourceCuts
public import RandomSystems.Typed.Functional

/-! One retained Boolean controls both replies; the source/cut adapter preserves that sharing. -/

@[expose] public section

namespace Tests.CumulativeMixture

open SystemAlgebra Probability Probability.Distribution

/-- Draw one fair bit and retain its deterministic source for both admitted queries. -/
noncomputable def retainedBit : TypedSystem (Interface.source Bool 2) :=
  TypedSystem.sample 𝒰[Bool] (fun b => TypedSystem.source (ProbDist.single b) 2)

/-- The typed sample is the finite cut of the mixture of whole-transcript source masses. -/
lemma retainedBit_mass (h : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Bool))) :
    retainedBit.1 h = cutMass
      (mixMass 𝒰[Bool] (fun b => sourceMass ((ProbDist.single b).map (Sigma.mk ())))) 2 h := by
  rw [retainedBit, TypedSystem.sample_mass, cutMass_mixMass]
  change _ = ∑ b ∈ (𝒰[Bool]).1.support, (𝒰[Bool]).1 b * _
  exact Finset.sum_congr rfl fun b _ =>
    congrArg (fun v => (𝒰[Bool]).1 b * v) (TypedSystem.source_eq_cutMass _ _ h)

/-- The unlimited retained mixture normalizes on every query prefix. -/
lemma retained_normalized :
    IsRandomSystem (fun (_ : List (Unit × Bool)) _ => True)
      (mixMass 𝒰[Bool] (fun b => sourceMass (ProbDist.single b))) :=
  mixMass_isRandomSystem _ _ (fun b => sourceMass_isRandomSystem (ProbDist.single b))

/-- Two replies from the retained bit cannot disagree. -/
lemma different_replies :
    retainedBit.1 [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)] = 0 := by
  classical
  rw [retainedBit_mass]
  norm_num [cutMass, mixMass, expect_eq_sum, sourceMass, ProbDist.map_val,
    ProbDist.single, fTransform_single, ProbDist.uniform, uniform_apply]

/-- Repeating the false reply has the probability of one retained false draw. -/
lemma repeated_false :
    retainedBit.1 [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), false⟩)] = 1 / 2 := by
  classical
  rw [retainedBit_mass]
  norm_num [cutMass, mixMass, expect_eq_sum, sourceMass, ProbDist.map_val,
    ProbDist.single, fTransform_single, ProbDist.uniform, uniform_apply]

#print axioms SystemAlgebra.cutMass_mixMass
#print axioms SystemAlgebra.mixMass_isRandomSystem
#print axioms SystemAlgebra.RandomSystem.mix_eq_mixMass
#print axioms retained_normalized
#print axioms retainedBit_mass
#print axioms different_replies
#print axioms repeated_false

end Tests.CumulativeMixture

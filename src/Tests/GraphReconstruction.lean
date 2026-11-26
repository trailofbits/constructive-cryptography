module

public import Probability.Coupling
public import Mathlib.Tactic.NormNum

/-!
# Graph reconstruction checks

A signed joint law on natural numbers is reconstructed from its second marginal.
A nonconstant kernel retains the first bit and samples a fresh second bit.
-/

@[expose] public section

namespace Probability.Distribution.GraphReconstructionTests

/-- Masses `-1` and `3` at `(4, 2)` and `(6, 3)` lie on the graph `b = 2a`. -/
noncomputable def signedJoint : Distribution (ℕ × ℕ) :=
  Finsupp.single (4, 2) (-1) + Finsupp.single (6, 3) 3

example : signedJoint (4, 2) < 0 := by
  norm_num [signedJoint]

/-- The graph law uses finite support, with neither a finite carrier nor positive masses. -/
example : signedJoint =
    fTransform (fun a => (2 * a, a)) (fTransform Prod.snd signedJoint) := by
  apply eq_fTransform_of_graph_support
  intro p hp
  simp only [signedJoint, Finsupp.mem_support_iff, Finsupp.add_apply,
    Finsupp.single_apply] at hp
  split_ifs at hp with h0 h1
  · subst p
    rfl
  · subst p
    rfl
  · subst p
    rfl
  · exact False.elim (hp (zero_add 0))

/-- `fiberLaw b` retains `b` and samples an independent uniform second bit. -/
noncomputable def fiberLaw (b : Bool) : ProbDist (Bool × Bool) :=
  (𝒰[Bool]).map (fun c => (b, c))

/-- Sampling the first bit, then its fiber, recovers the independent pair law. -/
example :
    ProbDist.jointLaw 𝒰[Bool] fiberLaw =
      (prodProbDist 𝒰[Bool] 𝒰[Bool]).map (fun a => (a.1, a)) := by
  apply ProbDist.jointLaw_eq_map_of_fiber
  · apply Subtype.ext
    exact (prod_eq_bindK (uniform Bool) (uniform Bool)).symm
  · intro b _ a ha
    obtain ⟨c, _, rfl⟩ := mem_support_fTransform (fun c => (b, c)) (uniform Bool) ha
    rfl

#print axioms eq_fTransform_of_graph_support
#print axioms ProbDist.jointLaw_eq_map_of_fiber

end Probability.Distribution.GraphReconstructionTests

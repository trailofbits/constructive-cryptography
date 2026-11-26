module

public import Probability.ConditionalProduct
public import Tests.Conditioning

/-!
# Joint reconstruction from private entries

Two independent latent coordinates have masses `1/2,1/3,1/6` on `0,1,2`. Their observations
merge `0` and `1`, retain `2`, and never equal `none`. Conditional draws use a distinct
fallback on that unreachable fiber. The reconstructed table retains its correlated observations.
-/

@[expose] public section

noncomputable section

namespace Probability.Distribution.Tests.ConditionalProduct

open ConditioningTests (biased)

/-- Observe whether the latent value is `2`; `none` is never observed. -/
def observe (n : ℕ) : Option Bool := some (n == 2)

/-- Draw from the observation's fiber; the unreachable `none` fiber returns `9`. -/
def conditional (o : Option Bool) : ProbDist ℕ :=
  biased.conditionOn (fun n => observe n = o) (ProbDist.single 9)

/-- Draw both observations and all private cells independently, then select `(i,f(i))`. -/
def reconstructed : ProbDist ((Bool → ℕ) × (Bool → Option Bool)) :=
  (prodProbDist (ProbDist.piDep (fun _ : Bool => biased.map observe))
    (ProbDist.piDep (fun p : Bool × Option Bool => conditional p.2))).map
      (fun pair => ((fun i => pair.2 (i, pair.1 i)), pair.1))

/-- Reconstruction preserves the complete latent/observed table pair. -/
theorem reconstructed_eq :
    reconstructed = (ProbDist.piDep (fun _ : Bool => biased)).map
      (fun x => (x, fun i => observe (x i))) := by
  exact ProbDist.map_prod_piDep_pair_eq_of_jointLaw
    (D := Bool) (O := Option Bool) (X := ℕ)
    (fun _ => biased) (fun _ => biased.map observe) (fun _ => conditional)
    (fun _ => observe) (fun _ => ProbDist.jointLaw_conditionOn_eq_map biased observe _)

/-- Looking at one coordinate keeps its observation tied to that same latent value. -/
lemma read_pair : reconstructed.map (fun pair => (pair.1 false, pair.2 false)) =
    biased.map (fun n => (n, observe n)) := by
  rw [reconstructed_eq, ProbDist.map_map]
  have homogeneous : ProbDist.piDep (fun _ : Bool => biased) =
      ProbDist.pi (fun _ : Bool => biased) := Subtype.ext (piDep_eq_pi _)
  rw [homogeneous]
  calc
    _ = ((ProbDist.pi (fun _ : Bool => biased)).map (fun f => f false)).map
        (fun n => (n, observe n)) := (ProbDist.map_map _ _ _).symm
    _ = _ := congrArg (ProbDist.map (fun n => (n, observe n)))
      (ProbDist.map_pi_apply (fun _ : Bool => biased) false)

/-- The correlated pair `(2,some true)` has mass `1/6`; a mismatched observation has mass zero. -/
example : (reconstructed.map (fun pair => (pair.1 false, pair.2 false))).1
      (2, some true) = 1 / 6 ∧
    (reconstructed.map (fun pair => (pair.1 false, pair.2 false))).1
      (0, some true) = 0 := by
  simp only [read_pair]
  norm_num [ProbDist.map_val, biased, fTransform_add, fTransform_single, observe]

/-- An unreachable conditional branch keeps its explicit fallback. -/
example : conditional none = ProbDist.single 9 := by
  apply ProbDist.conditionOn_of_mass_eq_zero
  norm_num [biased, mass_add, mass_single, observe]

#print axioms ProbDist.map_prod_piDep_select
#print axioms ProbDist.map_prod_piDep_eq_of_jointLaw
#print axioms ProbDist.map_prod_piDep_pair_eq_of_jointLaw
#print axioms reconstructed_eq

end Probability.Distribution.Tests.ConditionalProduct

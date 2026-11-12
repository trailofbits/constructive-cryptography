module

public import RandomSystems.Cumulative.Parallel
public import RandomSystems.System.Source

/-! Two independent fair sources distinguish total observation horizons from component horizons. -/

@[expose] public section

namespace Tests.CumulativeParallel

open SystemAlgebra RandomSystem Probability Probability.Distribution

/-- One false reply from the left source followed by one from the right source. -/
def oneEach : List ((Two Unit Unit) × (Two Bool Bool)) :=
  [(⟨none, ()⟩, ⟨none, false⟩), (⟨some (), ()⟩, ⟨some (), false⟩)]

/-- Two total observations retain the independent product probability. -/
lemma total_two :
    cutMass (parallelMass (sourceMass (𝒰[Bool])) (sourceMass (𝒰[Bool]))) 2 oneEach = 1 / 4 := by
  have left : parallelLeft oneEach = [((), false)] := rfl
  have right : parallelRight oneEach = [((), false)] := rfl
  have consistent : parallelConsistent oneEach := by simp [parallelConsistent, oneEach]
  rw [cutMass, ite_eq_left (by simp [oneEach]), parallelMass, ite_eq_left consistent,
    left, right]
  norm_num [sourceMass, ProbDist.uniform, uniform_apply]

/-- One total observation removes the two-exchange transcript. -/
lemma total_one :
    cutMass (parallelMass (sourceMass (𝒰[Bool])) (sourceMass (𝒰[Bool]))) 1 oneEach = 0 := by
  simp only [cutMass, oneEach, List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceLeDiff, ite_false]

/-- The two unlimited fresh sources normalize on the consistent parallel domain. -/
example : IsRandomSystem
    (fun h x => parallelConsistent h ∧ parallelAdmits
      (fun (_ : List (Unit × Bool)) _ => True)
      (fun (_ : List (Unit × Bool)) _ => True) h x)
    (parallelMass (sourceMass (𝒰[Bool])) (sourceMass (𝒰[Bool]))) :=
  parallelMass_isRandomSystem (sourceMass_isRandomSystem _) (sourceMass_isRandomSystem _)

/-- Bounded component cuts retain the same independent cumulative formula. -/
example :
    let R := IsRandomSystem.cut _ _ (sourceMass_isRandomSystem (A := Unit) (𝒰[Bool])) 1
    (RandomSystem.parallel R R : List ((Two Unit Unit) × (Two Bool Bool)) → ℝ) =
      parallelMass R R := by
  exact RandomSystem.parallel_eq_parallelMass _ _

#print axioms SystemAlgebra.cutDomain_parallel_cutDomain
#print axioms SystemAlgebra.cutMass_parallelMass
#print axioms SystemAlgebra.parallelMass_isRandomSystem
#print axioms SystemAlgebra.RandomSystem.parallel_eq_parallelMass
#print axioms total_two
#print axioms total_one

end Tests.CumulativeParallel

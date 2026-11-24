module

public import RandomSystems.Cumulative.FiniteCuts
public import RandomSystems.System.Memoryless

/-! Finite cuts recover an existing bounded memoryless system, including its zero tail. -/

@[expose] public section

namespace Tests.CumulativeFiniteCuts

open SystemAlgebra Probability Probability.Distribution

/-- A one-query Boolean source remains the same cumulative function after cutting at its bound. -/
lemma bounded_source_cut (ν : ProbDist Bool) :
    let D := cutDomain (fun (_ : List (Unit × Bool)) _ => True) 1
    let R := RandomSystem.memoryless D (fun _ => ν)
    (IsRandomSystem.cut D R R.2 1 : List (Unit × Bool) → ℝ) = R := by
  exact RandomSystem.cut_bound_val _

#print axioms SystemAlgebra.IsRandomSystem.cutMass
#print axioms SystemAlgebra.IsRandomSystem.cut_ext
#print axioms SystemAlgebra.RandomSystem.limitMass_isRandomSystem
#print axioms SystemAlgebra.RandomSystem.limitMass_cut
#print axioms SystemAlgebra.RandomSystem.cut_limitMass
#print axioms SystemAlgebra.RandomSystem.cut_bound_val
#print axioms bounded_source_cut

end Tests.CumulativeFiniteCuts

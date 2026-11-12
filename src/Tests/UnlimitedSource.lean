module

public import RandomSystems.Typed.SourceCuts

/-! A fair source has positive prefixes of every length and recovers the existing bounded source. -/

@[expose] public section

namespace Tests.UnlimitedSource

open SystemAlgebra Probability Probability.Distribution

/-- Every all-false reply prefix has positive mass, with no fixed horizon. -/
lemma fair_prefix_pos (n : ℕ) :
    0 < sourceMass (𝒰[Bool]) (List.replicate n ((), false)) := by
  change 0 < (List.map (fun xy : Unit × Bool => (𝒰[Bool]).1 xy.2)
    (List.replicate n ((), false))).prod
  rw [List.map_replicate, List.prod_replicate]
  apply pow_pos
  norm_num [ProbDist.uniform, Distribution.uniform_apply]

/-- The fair source has a positive transcript beyond every proposed global bound. -/
lemma fair_has_no_global_bound :
    ¬ ∃ q : ℕ, ∀ h : List (Unit × Bool), q < h.length → sourceMass (𝒰[Bool]) h = 0 := by
  rintro ⟨q, bound⟩
  have zero := bound (List.replicate (q + 1) ((), false))
    (by rw [List.length_replicate]; exact Nat.lt_succ_self q)
  exact (ne_of_gt (fair_prefix_pos (q + 1))) zero

/-- The existing three-query table source has exactly the corresponding unlimited-source cut. -/
lemma bounded_fair_source (h : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Bool))) :
    (TypedSystem.source (𝒰[Bool]) 3).1 h =
      cutMass (sourceMass ((𝒰[Bool]).map (Sigma.mk ()))) 3 h :=
  TypedSystem.source_eq_cutMass _ _ h

#print axioms SystemAlgebra.sourceMass_isRandomSystem
#print axioms SystemAlgebra.sourceMass_ofFn
#print axioms SystemAlgebra.RandomSystem.memoryless_eq_cut_sourceMass
#print axioms SystemAlgebra.TypedSystem.source_eq_cutMass
#print axioms fair_has_no_global_bound
#print axioms bounded_fair_source

end Tests.UnlimitedSource

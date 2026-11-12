module

public import RandomSystems.Cumulative.Presentation

/-!
# Conditional-table levels of a cumulative behavior

`IsRandomSystem.presentationLevel` presents the finite cut at each horizon by independently
sampling its conditional choices. The restriction laws identify these with one fixed family
of global kernels, including the choices at zero-mass histories.
-/

@[expose] public section

namespace SystemAlgebra.IsRandomSystem

open Probability Probability.Distribution

-- `A`, `B` are finite query/reply alphabets; `hp` normalizes behavior `p` on query domain `D`.
variable {A B : Type} [Fintype A] [Fintype B]
variable {D : List (A × B) → A → Prop} {p : List (A × B) → ℝ} (hp : IsRandomSystem D p)

/-- Sample a certified deterministic presentation of the behavior through horizon `n`. -/
noncomputable def presentationLevel (n : ℕ) :
    ProbDist {s : System A B // IsDDS s ∧ HasDomain (cutDomain D n) s} :=
  let R := cut D p hp n
  R.2.isSubprobabilistic.presentation (fun _ hh => R.mass_eq_zero_of_bound_lt hh) _
    (fun g hg => ⟨(realization g).2, R.hasDomain_realization hg⟩)

end SystemAlgebra.IsRandomSystem

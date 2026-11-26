module

public import RandomSystems.Cumulative.Cumulative
public import Probability.Lift

/-!
# Conditional reply normalization

A conditional reply law divides extension masses by the nonzero prefix mass `R h`.
`smul_conditional_eq_extensionLaw` cancels that normalization as an equality of distributions.
`conditional_mass` gives the corresponding event formula, used to transfer cumulative
bounds to conditional reply probabilities.
-/

@[expose] public section

namespace SystemAlgebra.RandomSystem

open Probability Probability.Distribution

-- `A`, `B` carry queries and replies; `D` specifies the admitted next queries.
variable {A B : Type} [Fintype A] [Fintype B] {D : Domain A B}

/-- Multiplying the conditional reply law by its prefix mass recovers the extension law. -/
lemma smul_conditional_eq_extensionLaw
    (R : RandomSystem A B D) (h : List (A × B)) (x : A)
    -- `defined` certifies admission of `x` after `h` and the nonzero mass `R h`.
    (defined : (R.conditional h x).Dom) :
    R h • ((R.conditional h x).get defined).1 = R.extensionLaw h x := by
  ext y
  rw [Finsupp.smul_apply, smul_eq_mul, conditional_apply, extensionLaw_apply, mul_comm,
    div_mul_cancel₀ _ (conditional_dom R h x |>.mp defined).2]

/-- Normalizing a cumulative extension divides each event mass by its prefix mass. -/
lemma conditional_mass
    (R : RandomSystem A B D) (h : List (A × B)) (x : A)
    (defined : (R.conditional h x).Dom)
    -- `event` selects replies; its conditional mass is scaled by the same prefix mass.
    (event : B → Prop) :
    ((R.conditional h x).get defined).1.mass event =
      (R.extensionLaw h x).mass event / R h := by
  have weighted := congrArg (fun P : Distribution B => P.mass event)
    (R.smul_conditional_eq_extensionLaw h x defined)
  rw [mass_smul] at weighted
  exact (eq_div_iff (conditional_dom R h x |>.mp defined).2).mpr
    (by simpa only [mul_comm] using weighted)

end SystemAlgebra.RandomSystem

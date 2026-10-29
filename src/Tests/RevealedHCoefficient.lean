import ConstructiveCryptography.InterfaceAlgebra
import RandomSystems.Typed.Functional

/-!
# Revealed H-coefficient tests

* `constantReveal`: an H-coefficient argument of error `0` from a typed system to itself, on
  every interface
* its consequence for the CC distance, through `Interface.distance_le_of_hCoefficient`
* `Distribution.expect_comp_eq_sum_mass` with three classes and arbitrary class errors
* the zero law is not a probability law, so it is not a conditional reveal law
* `statDist_le_expect_of_ratio` with pointwise errors: `δ(δ_false, 𝒰(Bool)) ≤ 1/2`
* `halfBadReveal`: a nonconstant ideal reveal, `z ← 𝒰(Bool)`, giving an argument of error `1/2`
  from a typed system to itself, on every interface
-/

open Probability SystemAlgebra
open scoped NNReal

namespace SystemAlgebra.Tests.RevealedHCoefficient

/-- **A constant reveal**: the argument of error `0` from a typed system `S` on `A` to itself.
The real system is the one-point mixture `mix δ_() (fun _ => S)` and reveals
`realReveal () h = ()`; the ideal system samples `() ← δ_()`; `Bad = ∅`, `ε₁ = ε₂ = 0`. Both
extended masses at `(h, ())` are `S(h)`. -/
noncomputable def constantReveal (A : Interface) (S : TypedSystem A) :
    RandomSystem.HCoefficient S.1 S.1 0 := by
  classical
  let P := Distribution.ProbDist.single ()
  have hp : S.1 = RandomSystem.mix P (fun _ => S.1) := by
    -- `(mix δ_() (fun _ => S))(h) = 1 · S(h)`.
    apply RandomSystem.ext
    intro h
    simp only [Distribution.ProbDist.single, RandomSystem.mix_mass, ne_eq, one_ne_zero,
      not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same, one_mul, Finset.sum_const,
      Finset.card_singleton, one_smul, P]
  -- Ratio: `(1 − 0) · S(h) · 1 ≤ 1 · [() = ()] · S(h)`; bad mass: `Pr[∅] = 0`.
  simpa only [add_zero] using
    RandomSystem.HCoefficient.ofGoodBad P (fun _ => S.1) hp (fun _ => S.2) S.2
    (fun _ _ => ()) (fun _ => Finsupp.single () 1)
    (fun _ => Distribution.isProbDist_single ()) (fun _ => False) (ε₁ := 0) (ε₂ := 0)
    le_rfl
    (fun τ _ => by
      rcases τ with ⟨h, ⟨⟩⟩
      simp only [sub_zero, RandomSystem.kernelMass, Finsupp.single_eq_same, mul_one, one_mul,
        RandomSystem.revealMass, Distribution.ProbDist.single, ne_eq, one_ne_zero,
        not_false_eq_true, Finsupp.support_single, ↓reduceIte, Finset.sum_const,
        Finset.card_singleton, one_smul, Std.le_refl, P])
    (fun _ _ _ _ => by simp only [Distribution.mass, ↓reduceIte, Finsupp.sum_fun_zero, Std.le_refl])

/-- The constant reveal bounds the CC distance of `S` to itself: `distance S S ≤ 0`. -/
example (A : Interface) (S : TypedSystem A) :
    ConstructiveCryptography.CryptographicAlgebra.distance S S ≤ (0 : ℝ≥0) :=
  Interface.distance_le_of_hCoefficient (constantReveal A S)

/-- Three classes with arbitrary errors:
`𝔼_law[error ∘ classOf] = ∑_c error c · law(classOf = c)`. -/
example {T : Type} (law : Distribution T) (classOf : T → Fin 3) (error : Fin 3 → ℝ) :
    law.expect (fun t => error (classOf t)) =
      ∑ c, error c * law.mass (fun t => classOf t = c) :=
  Distribution.expect_comp_eq_sum_mass law classOf error

/-- The zero law on `Unit` has weight `0 ≠ 1`, so it is not a probability law and cannot be
an `idealReveal`. -/
example : ¬ (0 : Distribution Unit).isProbDist := by
  intro h
  have hw := h.weight_eq
  norm_num [Distribution.weight] at hw

/-- Pointwise errors matter: `real = δ_false`, `ideal = 𝒰(Bool)` and
`ε(false) = 0`, `ε(true) = 1` give expected error `1/2`, below the maximum error `1`. -/
example : statDist (Finsupp.single false 1) (Distribution.uniform Bool) ≤ 1 / 2 := by
  -- Both laws have weight one; `ε ≥ 0`; ratio at `false`: `(1 − 0) · 1/2 ≤ 1`, at `true`:
  -- `(1 − 1) · 1/2 ≤ 0`.
  have h := statDist_le_expect_of_ratio (Finsupp.single false 1)
    (Distribution.uniform Bool) (fun b => if b then 1 else 0)
    (by rw [(Distribution.isProbDist_single false).weight_eq,
      (Distribution.uniform_isProbDist (A := Bool)).weight_eq])
    (by intro b; cases b <;> norm_num)
    Distribution.uniform_nonNeg
    (by intro b; cases b <;> norm_num [Distribution.uniform_apply, Finsupp.single_apply])
  -- `𝔼_{𝒰(Bool)}[ε] = 1/2 · 0 + 1/2 · 1 = 1/2`.
  simpa only [Distribution.expect_eq_sum, Fintype.sum_bool, Bool.false_eq_true, if_false,
    if_true, mul_zero, add_zero, mul_one, Distribution.uniform_apply,
    Fintype.card_bool, Nat.cast_ofNat] using h

/-- **A nonconstant reveal**: the argument of error `1/2` from a typed system `S` on `A` to
itself. The real system is the one-point mixture `mix δ_() (fun _ => S)` and reveals
`realReveal () h = false`; after the transcript the ideal system samples `z ← 𝒰(Bool)`.
`Bad τ := τ.2 = true`, `ε₁ = 0`, `ε₂ = 1/2`. On a good `τ = (h, false)`,
`kernelMass τ = S(h)/2 ≤ S(h) = revealMass τ`; the bad mass is `𝔼_{S.sLaw}[𝒰{true}] = 1/2`. -/
noncomputable def halfBadReveal (A : Interface) (S : TypedSystem A) :
    RandomSystem.HCoefficient S.1 S.1 (1 / 2) := by
  classical
  let P := Distribution.ProbDist.single ()
  have hp : S.1 = RandomSystem.mix P (fun _ => S.1) := by
    -- `(mix δ_() (fun _ => S))(h) = 1 · S(h)`.
    apply RandomSystem.ext
    intro h
    simp only [Distribution.ProbDist.single, RandomSystem.mix_mass, ne_eq, one_ne_zero,
      not_false_eq_true, Finsupp.support_single, Finsupp.single_eq_same, one_mul, Finset.sum_const,
      Finset.card_singleton, one_smul, P]
  simpa only [zero_add] using RandomSystem.HCoefficient.ofGoodBad P (fun _ => S.1) hp
    (fun _ => S.2) S.2 (fun _ _ => false) (fun _ => Distribution.uniform Bool)
    (fun _ => Distribution.uniform_isProbDist (A := Bool)) (fun τ => τ.2 = true)
    (ε₁ := 0) (ε₂ := 1 / 2) le_rfl
    (fun τ hg => by
      rcases τ with ⟨h, b⟩
      cases b with
      | false =>
        -- Good: `(1 − 0) · S(h) · 1/2 ≤ 1 · [false = false] · S(h)`, as `S(h) ≥ 0`.
        simp only [sub_zero, RandomSystem.kernelMass, Distribution.uniform_apply,
          Fintype.card_bool, Nat.cast_ofNat, one_div, one_mul, RandomSystem.revealMass,
          Distribution.ProbDist.single, ne_eq, one_ne_zero, not_false_eq_true,
          Finsupp.support_single, Finsupp.single_eq_same, ↓reduceIte, Finset.sum_const,
          Finset.card_singleton, one_smul, P]
        linarith [S.1.mass_nonneg h]
      -- `(h, true)` is bad, excluded by `hg`.
      | true => exact (hg rfl).elim)
    (fun E n _ hE => by
      -- `Pr[Bad] = 𝔼_{h ∼ S.sLaw E n}[𝒰{true}] = 1/2 · |S.sLaw E n| = 1/2`, the transcript law
      -- normalized by compatibility.
      rw [RandomSystem.kernelLaw_mass_eq_expect]
      have hmass : (Distribution.uniform Bool).mass (fun b => b = true) = 1 / 2 := by
        rw [Distribution.mass_singleton]
        norm_num [Distribution.uniform_apply]
      simp only [hmass, Distribution.expect_const,
        (S.1.sLaw_isProbDist (hE _ S.2) n).weight_eq, mul_one, le_refl])

#print axioms RandomSystem.statDist_sLaw_le_of_reveal
#print axioms RandomSystem.HCoefficient.transcriptDistance_le_nnreal
#print axioms Interface.distance_le_of_hCoefficient
#print axioms constantReveal
#print axioms halfBadReveal

end SystemAlgebra.Tests.RevealedHCoefficient

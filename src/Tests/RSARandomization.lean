module

public import Commons.Definitions.RSA

/-!
# A fallible root solver and its RSA specialization

`fallibleRootSolver` draws one fair coin: it returns the inverse-power root or fails.
`fallibleRootSolver_success_eq` identifies its success law with that coin.
`fallibleRootSolver_blinding_eq` reuses the same solver through `RSA.blinding_success_eq`,
so randomizing any fixed unit challenge preserves the fair success law.
-/

@[expose] public section

namespace Tests.RSARandomization

open Probability Probability.Distribution

section Group

-- `G` carries challenges and roots; `he` makes the `e`-th power map bijective.
variable {G : Type*} [Group G] (e : ℕ) (he : (Nat.card G).Coprime e)

/-- On challenge `z`, draw `b ← 𝒰[Bool]`: return its unique `e`-th root on `true`,
and `none` on `false`. -/
noncomputable def fallibleRootSolver (z : G) : ProbDist (Option G) :=
  𝒰[Bool].map (fun b : Bool => if b then some ((powCoprime he).symm z) else none)

/-- Success is exactly the solver's coin, since its returned value is an `e`-th root. -/
lemma fallibleRootSolver_success_eq
    -- `z` is the challenge; equality in `G` decides the success test.
    [DecidableEq G] (z : G) :
    ProbDist.rootSuccessLaw (fallibleRootSolver e he) e z = 𝒰[Bool] := by
  unfold ProbDist.rootSuccessLaw
  -- The inverse power permutation supplies a root of the challenge.
  have root : ((powCoprime he).symm z) ^ e = z := (powCoprime he).apply_symm_apply z
  unfold fallibleRootSolver
  rw [ProbDist.map_map]
  -- Failure gives `false`; the inverse-power answer gives `true`.
  have test : (fun b : Bool =>
      if (if b then some ((powCoprime he).symm z) else none).map (· ^ e) = some z
      then true else false) = id := by
    funext b
    cases b with
    | false => rfl
    | true =>
      simp only [↓reduceIte, Option.map_some, root, id_eq]
  change ProbDist.map (fun b : Bool =>
    if (if b then some ((powCoprime he).symm z) else none).map (· ^ e) = some z
    then true else false) 𝒰[Bool] = _
  -- Observing success therefore pushes the uniform coin along the identity.
  rw [test]
  exact Subtype.ext (fTransform_id _)

end Group

/-- The randomized solver succeeds with the same fair coin law at every fixed unit `y`. -/
lemma fallibleRootSolver_blinding_eq
    -- `N` is the nonzero modulus and `e` the exponent.
    -- `he` makes the unit power map bijective; `y` is the fixed unit challenge.
    (N e : ℕ) [NeZero N] (he : (Nat.card (ZMod N)ˣ).Coprime e) (y : (ZMod N)ˣ) :
    ProbDist.rootSuccessLaw (ProbDist.blindRootSolver (fallibleRootSolver e he) e) e y =
      𝒰[Bool] := by
  -- The RSA corollary takes the equivalent coprimality condition on `φ(N)`.
  have hφ : (Nat.totient N).Coprime e := by
    rw [← ZMod.card_units_eq_totient N, ← Nat.card_eq_fintype_card]
    exact he
  -- Blinding reduces the fixed challenge to the original solver on a uniform challenge.
  rw [Commons.RSA.blinding_success_eq N e hφ]
  -- Every `z` has success law `𝒰[Bool]`, so the mixture over challenges is constant.
  change 𝒰[(ZMod N)ˣ].bind (fun z =>
    ProbDist.rootSuccessLaw (fallibleRootSolver e he) e z) = _
  simp only [fallibleRootSolver_success_eq]
  exact ProbDist.bind_const _ _

#print axioms ProbDist.bind_const
#print axioms Probability.Distribution.fTransform_mul_pow_uniform
#print axioms Probability.Distribution.pow_mul_inv_eq_iff
#print axioms ProbDist.bind_uniform_mul_pow
#print axioms ProbDist.blinding_success_eq
#print axioms Commons.RSA.blinding_success_eq
#print axioms fallibleRootSolver_blinding_eq

end Tests.RSARandomization

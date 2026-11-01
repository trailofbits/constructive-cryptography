module

public import Probability.Kernel
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Uniform powers and root blinding

For a finite group `G` and an exponent `e` coprime to `|G|`,
`fTransform_mul_pow_uniform` makes `y * r^e` uniform when `r` is uniform.
`ProbDist.bind_uniform_mul_pow` transports any output kernel through this change of challenge.

In a commutative group, `pow_mul_inv_eq_iff` removes the multiplier from a proposed root.
`ProbDist.blindRootSolver` samples the multiplier and removes it from the solver's answer.
`ProbDist.rootSuccessLaw` observes whether the answer is a root.
`ProbDist.blinding_success_eq` shows that this randomized solver has the original solver's
uniform-challenge success law at each fixed challenge.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Probability.Distribution

/-- The inverse power formula “x = yᵈ” [1, Theorem 2.5, p. 45] makes the power map bijective.
Left multiplication then gives `y * r^e ∼ 𝒰[G]` for `r ← 𝒰[G]`. -/
lemma fTransform_mul_pow_uniform
    -- `G` is the finite group of challenges and multipliers; `e` is a natural exponent.
    {G : Type*} [Group G] [Fintype G] {e : ℕ}
    -- `he` makes the power map bijective; `y` is the fixed challenge.
    (he : (Nat.card G).Coprime e) (y : G) :
    fTransform (fun r : G => y * r ^ e) (uniform G) = uniform G :=
  fTransform_equiv_uniform ((powCoprime he).trans (Equiv.mulLeft y))

/-- Mixing `K` over the blinded challenge gives its mixture over a uniform challenge. -/
lemma ProbDist.bind_uniform_mul_pow
    -- `G` carries challenges; `Ω` (Omega) carries arbitrary outputs of the kernel `K`.
    {G Ω : Type*} [Group G] [Fintype G] {e : ℕ}
    -- `he`: `gcd(|G|, e) = 1`; `y` is fixed, while `r` is the fresh uniform multiplier.
    (he : (Nat.card G).Coprime e) (y : G) (K : G → ProbDist Ω) :
    𝒰[G].bind (fun r => K (y * r ^ e)) = 𝒰[G].bind K := by
  apply Subtype.ext
  change bindK (Distribution.uniform G) (fun r => (K (y * r ^ e)).1) = _
  -- Move the challenge map into the sampling law, which remains uniform.
  calc
    _ = bindK (fTransform (fun r : G => y * r ^ e) (Distribution.uniform G))
        (fun z => (K z).1) :=
      (bindK_fTransform (fun r : G => y * r ^ e) (Distribution.uniform G) (fun z => (K z).1)).symm
    _ = _ := by rw [fTransform_mul_pow_uniform he y]; rfl

/-- Removing `r` from a proposed root removes `r^e` from its challenge. -/
lemma pow_mul_inv_eq_iff
    -- Commutativity in `G` distributes the power over `x * r⁻¹`.
    {G : Type*} [CommGroup G]
    -- `x` is the proposed root, `y` the original challenge and `r` the multiplier.
    (x y r : G) (e : ℕ) :
    (x * r⁻¹) ^ e = y ↔ x ^ e = y * r ^ e := by
  rw [mul_pow, inv_pow, mul_inv_eq_iff_eq_mul]

/-- The success-bit law of `x ← A y`: test `x^e = y`, rejecting `none`. -/
noncomputable def ProbDist.rootSuccessLaw
    -- `G` carries challenges and roots; equality decides the success test.
    {G : Type*} [Monoid G] [DecidableEq G]
    -- `A y` returns a proposed root or `none`; `e` is the exponent, `y` the challenge.
    (A : G → ProbDist (Option G)) (e : ℕ) (y : G) : ProbDist Bool :=
  (A y).map (fun x => if x.map (· ^ e) = some y then true else false)

/-- The randomized root solver: `r ← 𝒰[G]; x ← A(y * r^e); return x / r`, keeping failure.
The challenge map is “ỹ ← rᵉy” [2, Exercise 10.28, Hint, p. 432], written here as `y * r^e`;
the two orders agree in the commutative groups of `ProbDist.blinding_success_eq`.

```text
       ┌── r ← 𝒰[G] (retained) ──┐
       ▼                         ▼
y ──[· r^e]──► A ──► some x ──[· r⁻¹]──► some (x * r⁻¹)
                     none ─────────────► none
```
-/
noncomputable def ProbDist.blindRootSolver
    -- `G` is the finite group in which challenges are blinded and answers unblinded.
    {G : Type*} [Group G] [Fintype G]
    -- `A z` is the answer law at `z`; `e` is the exponent and `y` the original challenge.
    (A : G → ProbDist (Option G)) (e : ℕ) (y : G) : ProbDist (Option G) :=
  𝒰[G].bind (fun r => (A (y * r ^ e)).map (Option.map (· * r⁻¹)))

/-- At each fixed challenge, the blinded solver has the original uniform-challenge success law.
The blinded challenge is “uniformly distributed” [2, Exercise 10.28, Hint, p. 432]; the
unblinding identity preserves the success test. -/
theorem ProbDist.blinding_success_eq
    -- `G` carries group elements; equality decides the Boolean success test.
    {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    -- `A z` is the answer law on challenge `z`: `some x` proposes a root, `none` fails.
    (A : G → ProbDist (Option G))
    -- `he`: the natural exponent `e` is coprime to `|G|`; `y` is the fixed challenge.
    (e : ℕ) (he : (Nat.card G).Coprime e) (y : G) :
    rootSuccessLaw (blindRootSolver A e) e y = 𝒰[G].bind (rootSuccessLaw A e) := by
  -- Move the success observation through sampling and compose it with unblinding.
  have observation : rootSuccessLaw (blindRootSolver A e) e y =
      𝒰[G].bind (fun r => (A (y * r ^ e)).map (fun x =>
        if x.map (fun z => (z * r⁻¹) ^ e) = some y then true else false)) := by
    apply Subtype.ext
    simp only [rootSuccessLaw, blindRootSolver, map_val, bind_val, fTransform_bindK,
      fTransform_fTransform, Function.comp_def, Option.map_map]
  rw [observation]
  -- Unblinding preserves success for a root; failure stays failure.
  have tests : ∀ r : G,
      (fun x : Option G => if x.map (fun z => (z * r⁻¹) ^ e) = some y
        then true else false) =
      (fun x : Option G => if x.map (· ^ e) = some (y * r ^ e)
        then true else false) := by
    intro r
    funext x
    cases x with
    | none => rfl
    | some x => simp only [Option.map_some, Option.some.injEq, pow_mul_inv_eq_iff]
  simp only [tests]
  -- The remaining success kernel depends only on the uniform blinded challenge.
  exact bind_uniform_mul_pow (G := G) (Ω := Bool) he y (rootSuccessLaw A e)

end Probability.Distribution

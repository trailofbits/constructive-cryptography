module

public import RandomSystems.Typed.Distinguisher
public import RandomSystems.Distance.DecisionLaw

/-!
# Hidden-bit guessing on typed interfaces

`guessingProbability d R₀ R₁` scores the final decision against a uniform hidden bit selecting
`R₀` or `R₁`. Write `p_b = Pr[d(R_b) = true]`. `guessingProbability_eq_mass` identifies the
score with the explicit interaction law of any distinguisher realizing `d`.

The signed identity is `2 * (guessingProbability - 1/2) = p₁ - p₀`; taking absolute values
gives the two-world advantage. `guessingProbability_absorb` transports the experiment through
one converter. Joint solvers use these laws through their `decision` projection.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace SystemAlgebra.TypedDistinguisher

/-- The guessing score `(1 - p₀ + p₁) / 2`, with `p_b = d.1 R_b`.
`guessingProbability_eq_mass` identifies it with success in the hidden-bit experiment.
This is the two-world form of [2, Theorem 2.10 and §2.2.5.1, pp. 26–27]. -/
noncomputable def guessingProbability
    -- `d` is one stopping distinguisher; `R₀`, `R₁` are the two systems on its interface `A`.
    {A : Interface} (d : TypedDistinguisher A) (R₀ R₁ : TypedSystem A) : ℝ :=
  (1 - d.1 R₀ + d.1 R₁) / 2

/-- Every distinguisher realizing the distinguisher behavior induces the same guessing success. -/
lemma guessingProbability_eq_mass
    -- `P` realizes `d` on all systems of `A`; its full interaction supplies the final-bit law.
    {A : Interface} (d : TypedDistinguisher A) (P : A.inputDomain.Distinguisher)
    (realizes : ∀ R : TypedSystem A, d.1 R = P.probability R.1)
    -- `R b` is the system selected for the entire interaction by hidden bit `b`.
    (R : Bool → TypedSystem A) :
    guessingProbability d (R false) (R true) =
      (P.guessingLaw (fun b => (R b).1) (fun b => (R b).2)).1.mass
        (fun bg => bg.2 = bg.1) := by
  rw [Domain.Distinguisher.guessingLaw_success]
  simp only [guessingProbability, realizes]

/-- Signed guessing performance equals the signed distinction `p₁ - p₀`.
[1, Definition 4.7, p. 91] orients distinction as `p₁ - p₀`; Definition 4.8, p. 92
normalizes guessing by two. Equation (4.7), “[S_U; U] = ⟨S₀ | S₁⟩”, selects `R₀`, `R₁`
by the uniform bit `U` on the left and compares their decision probabilities on the right. -/
theorem two_mul_guessingProbability_sub_half
    -- `d` is fixed across the worlds `R₀`, `R₁` on interface `A`.
    {A : Interface} (d : TypedDistinguisher A) (R₀ R₁ : TypedSystem A) :
    2 * (guessingProbability d R₀ R₁ - 1 / 2) = d.1 R₁ - d.1 R₀ := by
  unfold guessingProbability
  ring

/-- Absolute distinction is twice the deviation of guessing success from one half.
[2, Theorem 2.10, p. 26]: “SSadv[A, E] = 2 · SSadv*[A, E]”. -/
theorem abs_sub_eq_two_mul_abs_guessingProbability_sub_half
    -- Both worlds use the same distinguisher `d`; the absolute value removes orientation.
    {A : Interface} (d : TypedDistinguisher A) (R₀ R₁ : TypedSystem A) :
    |d.1 R₀ - d.1 R₁| =
      2 * |guessingProbability d R₀ R₁ - 1 / 2| := by
  rw [abs_sub_comm, ← two_mul_guessingProbability_sub_half, abs_mul, abs_two]

/-- The library's two-world advantage is twice the absolute guessing bias. -/
lemma advantage_eq_two_mul_abs_guessingProbability_sub_half
    -- `d` is one compatible distinguisher; the advantage uses the extended nonnegative reals.
    {A : Interface} (d : TypedDistinguisher A) (R₀ R₁ : TypedSystem A) :
    d.advantage R₀ R₁ = ENNReal.ofReal (2 * |guessingProbability d R₀ R₁ - 1 / 2|) := by
  change ENNReal.ofReal |d.1 R₀ - d.1 R₁| = _
  rw [abs_sub_eq_two_mul_abs_guessingProbability_sub_half]

/-- Absorption preserves the hidden-bit experiment with the same converter in both worlds. -/
lemma guessingProbability_absorb
    -- `α` connects outside `A` to inside `B`; `d` runs outside, and `R₀`, `R₁` sit inside.
    {A B : Interface} (d : TypedDistinguisher A) (α : TypedConverter A B)
    (R₀ R₁ : TypedSystem B) :
    guessingProbability (absorb d α) R₀ R₁ =
      guessingProbability d (α • R₀) (α • R₁) := rfl

end SystemAlgebra.TypedDistinguisher

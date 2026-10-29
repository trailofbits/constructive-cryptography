import ConstructiveCryptography.Problem

/-!
# Ordered reductions with explicit solvers

Two reductions transfer hardness across three independent solver types and three independent
preordered performance spaces. Solvers are values of the supplied types, not functions
identified by their performance on games. The `#check_failure` guards confirm that the
reduction layer brings neither `Real` nor `Games` nor `ResourceTheory` into scope.
-/

#check_failure Real
#check_failure ConstructiveCryptography.Games
#check_failure ConstructiveCryptography.ResourceTheory

namespace ProblemTests

open ConstructiveCryptography

universe u₁ u₂ u₃ v₁ v₂ v₃

/-- Hardness crosses two solver transformations and two monotone performance translations:
`p s ≤ f (q (ρ s)) ≤ f (g (r (σ (ρ s)))) ≤ f (g ε)`.
Every solver type and every performance space may differ. -/
lemma performance_le_of_two_reductions
    {S₁ : Type u₁} {S₂ : Type u₂} {S₃ : Type u₃}
    {Ω₁ : Type v₁} {Ω₂ : Type v₂} {Ω₃ : Type v₃}
    [Preorder Ω₁] [Preorder Ω₂] [Preorder Ω₃]
    (p : S₁ → Ω₁) (q : S₂ → Ω₂) (r : S₃ → Ω₃)
    (ρ : S₁ → S₂) (σ : S₂ → S₃) (f : Ω₂ → Ω₁) (g : Ω₃ → Ω₂)
    (hf : Monotone f) (hg : Monotone g) {ε : Ω₃}
    (first : ∀ s, p s ≤ f (q (ρ s))) (second : ∀ t, q t ≤ g (r (σ t)))
    (hardness : ∀ t, r t ≤ ε) (s : S₁) : p s ≤ f (g ε) :=
  -- The second reduction and hardness of `r` give `q t ≤ g ε`; the first reduction and
  -- monotonicity of `f` then give `p s ≤ f (g ε)`.
  Problem.performance_le_of_reduction p q ρ f hf first
    (fun t => Problem.performance_le_of_reduction q r σ g hg second hardness t) s

#print axioms Problem.performance_le_of_reduction
#print axioms performance_le_of_two_reductions

end ProblemTests

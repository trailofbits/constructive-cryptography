import ConstructiveCryptography.Notation
import RandomSystems.Typed.ParallelAllAttachment
import RandomSystems.Typed.SamplingAlgebra
import Tests.TypedNaryParallel

/-!
# Direct systems: notation and deterministic assembly

Every example starts with the elaborated direct-system expression and ends with the same
object in mathematical notation. `guard_target` checks the actual Lean goals. Shared initial
randomness is preserved by normalization; the independent product is a different system.
-/

namespace SystemAlgebra.Tests.ProofErgonomics

open Probability CategoryTheory
open scoped SystemAlgebra

/-- The probability notation elaborates to a normalized law, with the raw law explicit. -/
example : (𝒰[Bool] : Distribution.ProbDist Bool).1 = Distribution.uniform Bool := by
  guard_target = (Distribution.ProbDist.uniform Bool).1 = Distribution.uniform Bool
  rfl

/-- Direct functional notation has the existing carrier as its elaborated goal. -/
example {A : Interface} (f : ∀ i, A.X i → A.Y i) :
    (system [A] i x => f i x) = TypedSystem.ofFunction f := by
  guard_target = TypedSystem.ofFunction f = TypedSystem.ofFunction f
  rfl

/-- Initial sampling retains a single normalized sample without a DSL import. -/
example {A : Interface} (f : Bool → ∀ i, A.X i → A.Y i) :
    (sample b ←$ 𝒰[Bool]; system [A] i x => f b i x) =
      TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b)) := by
  change TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b)) =
    TypedSystem.sample (Distribution.uniform Bool) (fun b => TypedSystem.ofFunction (f b))
  rfl

/-- Before: the general attachment law assembles an arbitrary stochastic family explicitly. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    TypedConverter.parallelAll α • TypedSystem.parallelAll R =
      TypedSystem.parallelAll (fun k => α k • R k) := by
  exact TypedConverter.parallelAll_attach α R

/-- After: family notation and the curated normalizer discharge the same equality. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) := by
  guard_target = TypedConverter.parallelAll α • TypedSystem.parallelAll R =
    TypedSystem.parallelAll (fun k => α k • R k)
  cc_normalize

/-- Before: attachment enters the retained draw, then acts componentwise. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : Bool → ∀ k, TypedSystem (B k)) :
    TypedConverter.parallelAll α • TypedSystem.sample (Distribution.uniform Bool)
        (fun b => TypedSystem.parallelAll (R b)) =
      TypedSystem.sample (Distribution.uniform Bool)
        (fun b => TypedSystem.parallelAll (fun k => α k • R b k)) := by
  rw [TypedConverter.smul_sample]
  simp only [TypedConverter.parallelAll_attach]

/-- After: normalization keeps the one draw outside the whole family. -/
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : Bool → ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (sample b ←$ 𝒰[Bool]; ∥ k, R b k) =
      (sample b ←$ 𝒰[Bool]; ∥ k, α k • R b k) := by
  cc_normalize

/-- Normalization does not turn shared randomness into independent draws. -/
example : sharedBit ≠ independentBit := by
  fail_if_success solve | cc_normalize
  guard_target = sharedBit ≠ independentBit
  intro he
  have hm := congrArg (fun R : TypedSystem (⨂ _k : Bool, bitInterface) => R.1 mixedReplies) he
  rw [sharedBit_mixedReplies_eq_zero, independentBit_mixedReplies_eq_quarter] at hm
  norm_num at hm

-- The diagnostic names the retained-sample law; no semantic choice is selected.
/--
trace: [Meta.Tactic.simp.rewrite] TypedConverter.smul_sample:1000:
      α • TypedSystem.sample (Distribution.uniform Bool) R
    ==>
      TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k) =
        TypedSystem.sample (Distribution.uniform Bool) fun k => α • R k
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example {A B : Interface} (α : TypedConverter A B) (R : Bool → TypedSystem B) :
    α • TypedSystem.sample (Distribution.uniform Bool) R =
      TypedSystem.sample (Distribution.uniform Bool) (fun b => α • R b) := by
  cc_normalize?

-- Family locality is a separate registered rule, also visible in the diagnostic.
/--
trace: [Meta.Tactic.simp.rewrite] TypedConverter.parallelAll_attach:1000:
      (⨂ₘ (k : K), α k) • ∥ (k : K), R k
    ==>
      ∥ (k : K), α k • R k
[Meta.Tactic.simp.rewrite] eq_self:1000:
      (∥ (k : K), α k • R k) = ∥ (k : K), α k • R k
    ==>
      True
-/
#guard_msgs (whitespace := lax) in
example {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}
    (α : ∀ k, TypedConverter (A k) (B k)) (R : ∀ k, TypedSystem (B k)) :
    (⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k) := by
  cc_normalize?

end SystemAlgebra.Tests.ProofErgonomics

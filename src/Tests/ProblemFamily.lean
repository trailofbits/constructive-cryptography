module

public import ConstructiveCryptography.Problem.Family
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Uniform family reduction checks

One fixed guess cannot solve two opposite Boolean targets. The positive consumer uses a
nonidentity solver map, and its worst-case bound follows from the generic family theorem.
-/

@[expose] public section

namespace Tests.ProblemFamily

open ConstructiveCryptography

/-- The single source problem is always solved: `source () () = 1`. -/
def source (_ : Unit) (_ : Unit) : ℝ := 1

/-- `guess H b = 1` exactly when the chosen bit `b` equals the target `H`. -/
def guess (H b : Bool) : ℝ := if H = b then 1 else 0

/-- A target-dependent guess solves each problem separately. -/
lemma targetwise_transformations :
    ∀ H : Bool, ∃ ρ : Unit → Bool, ∀ s, source () s ≤ guess H (ρ s) := by
  intro H
  exact ⟨fun _ => H, fun _ => by simp only [source, guess, ite_true, le_refl]⟩

/-- No uniform map solves both opposite target bits. -/
lemma not_uniform_reduction :
    ¬ Problem.Easier source guess Set.univ Set.univ := by
  rintro ⟨ρ, reduces⟩
  obtain ⟨G, _, comparison⟩ := reduces (!(ρ ())) (Set.mem_univ _)
  have impossible := comparison ()
  cases bit : ρ () <;>
    simp only [source, bit, Bool.not_false, Bool.not_true, guess,
      Bool.true_eq_false, Bool.false_eq_true, ite_false] at impossible <;>
    exact (not_le_of_gt zero_lt_one) impossible

/-- The target interprets its solver bit oppositely to the source. -/
def oppositeGuess (H b : Bool) : ℝ := guess H (!b)

/-- Negating the solver preserves all scores, uniformly across target instances. -/
lemma opposite_reduction :
    Problem.Easier guess oppositeGuess Set.univ Set.univ := by
  refine ⟨Bool.not, fun H _ => ⟨H, Set.mem_univ _, fun b => ?_⟩⟩
  simp only [oppositeGuess, Bool.not_not, le_refl]

/-- The same uniform reduction compares the worst-case scores over both target bits. -/
example : ∃ ρ : Bool → Bool, ∀ b,
    Problem.worstCase Set.univ (guess · b) ≤
      Problem.worstCase Set.univ (oppositeGuess · (ρ b)) := by
  apply opposite_reduction.worstCase_le (Set.univ_nonempty)
  intro b
  refine ⟨0, ?_⟩
  rintro _ ⟨H, _, rfl⟩
  change 0 ≤ if H = b then 1 else 0
  split <;> first | exact zero_le_one | exact le_rfl

/-- With no target instance, the family relation is vacuous. -/
lemma empty_target_reduction : Problem.Easier source guess ∅ Set.univ :=
  ⟨fun _ => false, fun _ member => False.elim member⟩

/-- Target nonemptiness is necessary for the real-valued infimum comparison. -/
example : ¬ Problem.worstCase Set.univ (source · ()) ≤
    Problem.worstCase ∅ (guess · false) := by
  change ¬ sInf ((fun _ : Unit => (1 : ℝ)) '' Set.univ) ≤
    sInf ((guess · false) '' ∅)
  rw [(Set.univ_nonempty : (Set.univ : Set Unit).Nonempty).image_const,
    csInf_singleton, Set.image_empty, Real.sInf_empty]
  exact not_le_of_gt zero_lt_one

#print axioms Problem.Easier.lowerBounds_subset
#print axioms Problem.Easier.isGLB_le
#print axioms Problem.Easier.worstCase_le
#print axioms not_uniform_reduction

end Tests.ProblemFamily

import Probability.Counting

/-!
# Repeated-query table laws

Two identical queries constrain one uniform table coordinate. Conflicting replies to the same
query have zero mass.
-/

namespace Probability.Counting.Tests

/-- Repeating a consistent query pays for one coordinate, not two independent draws. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)), f z.1 = z.2) =
      (1 / 2 : ℝ) := by
  have hg : ∀ z ∈ ([(false, true), (false, true)] : List (Bool × Bool)),
      (fun x : Bool => !x) z.1 = z.2 := by
    intro z hz
    have hz' : z = (false, true) := by simpa using hz
    subst z
    rfl
  simpa using uniform_mass_transcript_eq
    ([(false, true), (false, true)] : List (Bool × Bool)) (fun x => !x) hg

/-- A uniform function cannot give contradictory answers to one input. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ∀ z ∈ ([(false, true), (false, false)] : List (Bool × Bool)), f z.1 = z.2) =
      0 := by
  classical
  simp [Distribution.mass]

/-- Repeating one input has the same output law for tables of different domain sizes. -/
example :
    Distribution.fTransform (fun f : Bool → Bool => fun _ : Fin 2 => f false)
        (Distribution.uniform (Bool → Bool)) =
      Distribution.fTransform (fun f : Fin 3 → Bool => fun _ : Fin 2 => f 0)
        (Distribution.uniform (Fin 3 → Bool)) := by
  apply fTransform_eval_uniform_eq_of_same_fibers
  intro i j
  simp

/-- No unordered pair exists when only one coordinate is visible. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f ({false} : Finset Bool)) ≤ 0 := by
  simpa using uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) ({false} : Finset Bool)

/-- Two visible coordinates incur exactly one pair opportunity in the union bound. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => ¬ Set.InjOn f (Finset.univ : Finset Bool)) ≤ (1 / 2 : ℝ) := by
  simpa using uniform_mass_not_injOn_le_choose (X := Bool) (Y := Bool) Finset.univ

/-- The second coordinate stays uniform after revealing the first. -/
example : (Distribution.uniform (Bool → Bool)).mass
    (fun f => f false = true ∧ f true = false) =
      (Distribution.uniform (Bool → Bool)).mass (fun f => f false = true) / 2 := by
  apply uniform_mass_fresh_eval_eq
  intro f g he
  simp only [he false (by simp)]

#print axioms Probability.Counting.uniform_mass_transcript_eq
#print axioms Probability.Counting.fTransform_eval_uniform_eq_of_same_fibers
#print axioms Probability.Counting.uniform_mass_fresh_eval_eq
#print axioms Probability.Counting.uniform_mass_not_injOn_le_choose
#print axioms Probability.Distribution.mass_exists_pair_le_choose

end Probability.Counting.Tests

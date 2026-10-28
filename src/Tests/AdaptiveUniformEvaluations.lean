import Probability.Counting

/-!
# A reply-dependent fresh coordinate

The first table value selects which of two other coordinates is queried. The selected
coordinate is always distinct from the first, so its reply stays uniform.
-/

namespace Probability.Counting.Tests

open Probability.Counting

def adaptiveBase : Unit → Fin 3 := fun _ => 0

def adaptiveNext : (Unit → Bool) → Unit → Fin 3 := fun b _ => if b () then 1 else 2

example : (Distribution.uniform (Fin 3 → Bool)).mass (fun f =>
    f (adaptiveNext (fun _ => f (adaptiveBase ())) ()) = true) = (1 / 2 : ℝ) := by
  have hbase : Function.Injective adaptiveBase := fun _ _ _ => Subsingleton.elim _ _
  have hfresh (b : Unit → Bool) :
      Function.Injective (Sum.elim adaptiveBase (adaptiveNext b)) := by
    intro i j hij
    cases i with
    | inl u =>
      cases j with
      | inl v => cases u; cases v; rfl
      | inr v =>
        change (0 : Fin 3) = (if b () then 1 else 2) at hij
        split_ifs at hij <;> simp at hij
    | inr u =>
      cases j with
      | inl v =>
        change (if b () then (1 : Fin 3) else 2) = 0 at hij
        split_ifs at hij <;> simp at hij
      | inr v => cases u; cases v; rfl
  have h := uniform_mass_adaptive_eval_eq_mul adaptiveBase hbase adaptiveNext
    (fun _ => True) (fun b _ => hfresh b) (fun _ => true)
  have he (f : Fin 3 → Bool) :
      ((fun i : Unit => f (adaptiveNext (fun b => f (adaptiveBase b)) i)) =
        (fun _ => true)) ↔
        f (adaptiveNext (fun b => f (adaptiveBase b)) ()) = true := by
    constructor
    · intro hf; exact congrFun hf ()
    · intro hf; funext i; simpa only [Subsingleton.elim i ()] using hf
  simp only [true_and] at h
  rw [Distribution.mass_congr _ he, Distribution.mass_true,
    Distribution.weight_uniform] at h
  simpa using h

/-- If the second query reuses the first coordinate, the freshness hypothesis fails. -/
example : ¬ Function.Injective
    (Sum.elim (fun _ : Unit => (0 : Fin 3)) (fun _ : Unit => (0 : Fin 3))) := by
  intro hi
  have h := hi (show Sum.elim (fun _ : Unit => (0 : Fin 3))
      (fun _ : Unit => (0 : Fin 3)) (.inl ()) =
        Sum.elim (fun _ : Unit => (0 : Fin 3))
          (fun _ : Unit => (0 : Fin 3)) (.inr ()) from rfl)
  cases h

#print axioms Probability.Counting.uniform_mass_adaptive_eval_eq_mul

end Probability.Counting.Tests

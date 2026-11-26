module

public import Probability.List.Permutation
public import Mathlib.Tactic.NormNum

/-!
# Extending two observed positions

The natural inputs `7,9` evaluate to distinct labels, while all other natural inputs share
label `1`. The extension law therefore uses injectivity only on the selected list.
-/

@[expose] public section

namespace Tests.ListPermutation

/-- `evaluate 7 = 0`; every other input has label `1`. -/
def evaluate (a : ℕ) : Fin 2 := if a = 7 then 0 else 1

/-- The two selected inputs have distinct labels. -/
lemma evaluate_injOn : Set.InjOn evaluate {a | a ∈ ([7, 9] : List ℕ)} := by
  intro a ha b hb equal
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · rfl
  · norm_num [evaluate] at equal
  · norm_num [evaluate] at equal
  · rfl

/-- Either enumeration of the label pool extends to the specified values at `7,9`. -/
example (labels : Fin (Fintype.card (Fin 2)) ≃ Fin 2) :
    ∃ θ : Equiv.Perm (Fin 2), θ (labels ⟨0, by norm_num⟩) = 0 ∧
      θ (labels ⟨1, by norm_num⟩) = 1 := by
  obtain ⟨capacity, θ, agrees⟩ := List.exists_perm_apply_idxOf_eq [7, 9]
    (by norm_num) labels evaluate evaluate_injOn
  refine ⟨θ, ?_, ?_⟩
  · simpa [evaluate] using agrees 7 (by simp)
  · simpa [evaluate] using agrees 9 (by simp)

#print axioms List.exists_perm_apply_idxOf_eq
#print axioms evaluate_injOn

end Tests.ListPermutation

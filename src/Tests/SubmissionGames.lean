module

public import ConstructiveCryptography.Game.Submission

/-!
# Submission contracts with optional submissions

An observer submits a Boolean or stops without submitting. Natural-valued scores check that
union bounds and decoding need no real-valued probability structure. Stopping scores zero
even for the full event; decoding by negation exchanges the two successful singleton events.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.SubmissionGames

open ConstructiveCryptography

open Classical in
/-- A present value scores one exactly on membership; absent submissions score zero. -/
noncomputable def performance (value : Option Bool) (p : Set Bool) : ℕ :=
  match value with
  | none => 0
  | some b => if b ∈ p then 1 else 0

/-- Each admitted winner chooses either a Boolean submission or no submission. -/
noncomputable instance optionalGames : Games Unit (fun _ => Set Bool) ℕ where
  winners _ := Set.range performance

/-- Sets interpret themselves, evaluated on the selected optional submission. -/
noncomputable def optionalSubmission : SubmissionGame (fun _ : Unit => Set Bool) ℕ Bool () where
  game := id
  mono := by
    classical
    rintro W ⟨value, rfl⟩ p q inclusion
    cases value with
    | none => exact le_rfl
    | some b =>
      change (if b ∈ p then 1 else 0) ≤ (if b ∈ q then 1 else 0)
      by_cases member : b ∈ p
      · simp only [member, inclusion member, ite_true, le_refl]
      · simp only [member, ite_false, Nat.zero_le]
  union_le := by
    classical
    rintro W ⟨value, rfl⟩ p q
    cases value with
    | none => exact le_rfl
    | some b =>
      by_cases hp : b ∈ p <;> by_cases hq : b ∈ q <;>
        simp only [performance, id_eq, Set.mem_union, hp, hq, or_true, or_false,
          ite_true, ite_false] <;> omega

/-- An absent submission has score zero on the full event, so normalization is not assumed. -/
example : performance none (optionalSubmission.game Set.univ) < 1 := Nat.zero_lt_one

/-- A local cover is transported by monotonicity and then the union contract. -/
example (value : Option Bool) :
    performance value (optionalSubmission.game Set.univ) ≤
      performance value (optionalSubmission.game {true}) +
        performance value (optionalSubmission.game {false}) := by
  have covered : (Set.univ : Set Bool) ⊆ {true} ∪ {false} := by
    intro b _
    cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  exact (optionalSubmission.mono _ ⟨value, rfl⟩ covered).trans
    (optionalSubmission.union_le _ ⟨value, rfl⟩ {true} {false})

/-- Negation decodes an actual `false` submission into a successful `true` submission. -/
example : performance (some false) ((optionalSubmission.reindex Bool.not).game {true}) = 1 := by
  simp only [SubmissionGame.reindex, optionalSubmission, Set.mem_preimage,
    Set.mem_singleton_iff, Bool.not_false, performance, ite_true, id_eq]

/-- A local implication cannot replace a failed guess by a successful one in reverse. -/
example : ¬ performance (some true) (optionalSubmission.game {true}) ≤
    performance (some true) (optionalSubmission.game {false}) := by
  simp only [optionalSubmission, id_eq, performance, Set.mem_singleton_iff,
    Bool.true_eq_false, ite_false, ite_true]
  exact Nat.not_succ_le_zero 0

/-- The union contract is an inequality: overlapping events are counted twice on its right. -/
example : performance (some true) (optionalSubmission.game ({true} ∪ {true})) <
    performance (some true) (optionalSubmission.game {true}) +
      performance (some true) (optionalSubmission.game {true}) := by
  simp only [optionalSubmission, id_eq, performance, Set.mem_union, Set.mem_singleton_iff,
    or_self, ite_true]
  exact Nat.lt_succ_self 1

#print axioms SubmissionGame.reindex
#print axioms optionalSubmission

end Tests.SubmissionGames

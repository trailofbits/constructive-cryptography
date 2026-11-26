module

public import Tests.GameEventReflection

/-!
# Unset coefficients and visible mass

The signed fiber test retains coefficient `-3`. The existing two-call monitored game has
positive all-unset mass after its first reply and zero all-unset mass after its second reply;
the latter still has positive visible mass.
-/

@[expose] public section

namespace Tests.MBOUnsetCoefficient

open SystemAlgebra Probability Probability.Distribution Tests.GameEventReflection

/-- One unit query receives `false` before the existing monitor is set. -/
def firstReply : List ((Σ i, inside.X i) × Σ i, inside.Y i) :=
  [(⟨(), ()⟩, ⟨(), false⟩)]

/-- The two visible replies of the completed verification interaction are `false,true`. -/
def twoReplies : List ((Σ i, inside.X i) × Σ i, inside.Y i) :=
  forgetMBOs (RandomSystem.parallelRight (completed true))

open Classical in
/-- The fiber collapse accepts negative coefficients and does not assume normalization. -/
example : sumMBO
    (fun k => if k = unsetMBOs (firstReply ++ firstReply) then (-3 : ℝ) else 0)
    (firstReply ++ firstReply) = -3 := by
  classical
  rw [sumMBO_eq_unsetMBOs_of_eq_zero _ _ (fun _ _ different => ite_eq_right different)]
  simp only [ite_true]

/-- Every positive tagged representative of the first reply has its final bit unset. -/
lemma first_final_false (k : List ((Σ i, inside.X i) × Σ i, withMBO inside.Y i))
    (displayed : forgetMBOs k = firstReply) (positive : monitored.1.1 k ≠ 0) :
    finalMBO k = false := by
  have replies : Replies monitoredDDS.1 (k.map Prod.fst) (k.map Prod.snd) := by
    rw [monitored_mass] at positive
    split_ifs at positive with replies
    · exact replies
    · exact False.elim (positive rfl)
  have length : k.length = 1 := by
    simpa only [forgetMBOs, List.length_map, firstReply, List.length_cons, List.length_nil]
      using congrArg List.length displayed
  obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp length
  dsimp only [monitoredDDS] at replies
  rw [DDG.replies_withMBO_iff] at replies
  have bit := replies.2 0 (Nat.zero_lt_succ 0)
  norm_num [secondCall] at bit
  change z.2.2.2 = false at bit
  exact bit

/-- The game corollary identifies its positive first-reply visible and unset coefficients. -/
theorem first_visible_eq_unset : monitored.1.1.visible firstReply =
    monitored.1.1 (unsetMBOs firstReply) :=
  monitored.1.1.visible_apply_eq_unsetMBOs_of_finalMBO_eq_false monitored.2 firstReply
    first_final_false

example : monitored.1.1 (unsetMBOs firstReply) = 1 := by
  have replies := (replies_snoc.mp (show Replies monitoredDDS.1
      ([⟨(), ()⟩] ++ [⟨(), ()⟩])
      ([⟨(), (false, false)⟩] ++ [⟨(), (true, true)⟩]) from completed_game_replies)).1
  rw [monitored_mass]
  exact ite_eq_left replies

/-- The second query reaches the monitor, so the all-unset coefficient vanishes. -/
lemma second_unset_zero : monitored.1.1 (unsetMBOs twoReplies) = 0 := by
  rw [monitored, TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _
    (fun _ _ => by norm_num [secondCall])]
  apply mass_eq_zero_of_forall_not
  intro _ impossible
  apply impossible.2
  change 2 ≤ 2
  exact le_rfl

/-- The actual tagged second reply has mass one, so its visible coefficient remains positive. -/
lemma second_visible_positive : 1 ≤ monitored.1.1.visible twoReplies := by
  have mass : monitored.1.1 (RandomSystem.parallelRight (completed true)) = 1 := by
    rw [monitored_mass]
    exact ite_eq_left completed_game_replies
  have lower := le_sumMBO monitored.1.1.mass_nonneg
    (RandomSystem.parallelRight (completed true))
  rw [mass] at lower
  exact lower

/-- Dropping the final-false hypothesis would incorrectly identify these unequal coefficients. -/
example : monitored.1.1.visible twoReplies ≠ monitored.1.1 (unsetMBOs twoReplies) := by
  rw [second_unset_zero]
  exact ne_of_gt (lt_of_lt_of_le (by norm_num) second_visible_positive)

#print axioms eq_unsetMBOs_iff
#print axioms sumMBO_eq_unsetMBOs_of_eq_zero
#print axioms RandomSystem.visible_apply_eq_unsetMBOs_of_finalMBO_eq_false
#print axioms first_visible_eq_unset

end Tests.MBOUnsetCoefficient

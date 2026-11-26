module

public import Tests.MBOOffBadAttachment

/-!
# Exact event correspondence needs both implications

The existing monitored verifier has unset coefficient `0` and visible coefficient `1`
on its true reply. The false outside event satisfies one-way `ReflectsMBO` vacuously, but
its complement does not retain that visible mass. This concrete counterexample checks why
the exact attachment formula requires both completed-interaction directions.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution Tests.GameEventReflection
open Tests.MBOOffBadAttachment

namespace Tests.MBOExactAttachment

/-- The false event satisfies the outside-to-inside implication. -/
lemma false_reflects : verifier.ReflectsMBO monitored.1.1 (fun _ => False) := by
  intro _ _ _ _ _ _ impossible
  exact impossible.elim

/-- The actual verification call sets the bit, excluding its all-unset history. -/
lemma true_unset_zero :
    PDCBehavior.attach inside.nonempty_prefix outside.nonempty_prefix
      (PDCBehavior.liftMBO verifier) monitored.1.1 monitored.1.2
      (unsetMBOs (outsideReply true)) = 0 :=
  PDCBehavior.attach_liftMBO_unset_eq_zero_of_reflectsMBO
    inside.nonempty_prefix outside.nonempty_prefix verifier monitored.1.1
    monitored.1.2 monitored.2 verifier_reflects rfl

/-- The existing two-call program returns the second deterministic reply, `true`. -/
lemma invocation : verify.combine (fun (seen : Bool) _ _ => (true, seen))
    verify_bounded ((), false) () () = (((), true), true) := rfl

/-- The same completed visible reply has probability one. -/
lemma true_visible_one : (verifier • monitored.visible).1 (outsideReply true) = 1 := by
  rw [monitored, TypedGame.visible_ofAutomaton, verifier,
    TypedConverter.ofProgram_smul_ofAutomaton, TypedSystem.ofAutomaton_mass,
    ProbDist.map_val, mass_fTransform]
  change Distribution.mass (Finsupp.single false 1) _ = 1
  rw [mass_single]
  apply ite_eq_left
  change Replies _ ([] ++ [(⟨(), ()⟩ : Σ i, outside.X i)])
    ([] ++ [(⟨(), true⟩ : Σ i, outside.Y i)])
  rw [replies_snoc]
  suffices (verify.combine (fun (seen : Bool) _ _ => (true, seen)) verify_bounded
      ((), false) () ()).2 = true by
    simpa [filterDom, automatonSystem, stateAfter, outside, Interface.queryBudget] using this
  exact congrArg Prod.snd invocation

/-- One-way reflection alone does not identify unset mass with the good visible mass. -/
example :
    PDCBehavior.attach inside.nonempty_prefix outside.nonempty_prefix
      (PDCBehavior.liftMBO verifier) monitored.1.1 monitored.1.2
      (unsetMBOs (outsideReply true)) ≠
      (if False then 0 else (verifier • monitored.visible).1 (outsideReply true)) := by
  rw [true_unset_zero, ite_eq_right (not_false), true_visible_one]
  norm_num

/-- On the good reply, pointwise event correspondence retains the visible mass `1/2`. -/
lemma good_unset_half :
    PDCBehavior.attach inside.nonempty_prefix outside.nonempty_prefix
      (PDCBehavior.liftMBO verifier) game.1.1 game.1.2 (unsetMBOs (outsideReply false)) =
      1 / 2 := by
  classical
  calc
    _ = if bad (outsideReply false) then 0 else
        (verifier • game.visible).1 (outsideReply false) := by
      apply PDCBehavior.attach_liftMBO_unset_eq_ite_of_finalMBO_iff
        inside.nonempty_prefix outside.nonempty_prefix verifier game.1.1 game.1.2 game.2
        (outsideReply false) bad
      intro t follows stopped positive displayed
      exact ⟨inside_bad false t follows stopped positive displayed,
        fun impossible => by simp [bad, outsideReply] at impossible⟩
    _ = 1 / 2 := by
      rw [ite_eq_right (by simp [bad, outsideReply])]
      exact visible_mass false

#print axioms PDCBehavior.attach_liftMBO_unset_eq_ite_of_finalMBO_iff
#print axioms false_reflects
#print axioms true_unset_zero
#print axioms true_visible_one
#print axioms good_unset_half

end Tests.MBOExactAttachment

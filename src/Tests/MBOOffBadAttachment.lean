module

public import Tests.GameEventReflection

/-!
# A completed verifier preserves the unset coefficient off its bad reply

One retained fair bit controls the second inside reply and its hidden event. The existing
two-call verifier returns that reply. Both visible answers have mass `1/2`; the unset
coefficient equals the visible coefficient on the false answer. The completed-interaction
contract is discharged from the two component executions.
-/

@[expose] public section

namespace Tests.MBOOffBadAttachment

open SystemAlgebra Probability Probability.Distribution Tests.GameEventReflection

/-- `seen` starts false; the retained bit `b` is returned from the second query onward. -/
def reply : Bool × Bool → (i : inside.I) → inside.X i → (Bool × Bool) × inside.Y i :=
  fun (seen, b) _ _ => ((true, b), seen && b)

/-- Draw one fair bit `b`; the first-query marker starts false. -/
noncomputable def initial : ProbDist (Bool × Bool) := (𝒰[Bool]).map (false, ·)

/-- Reach the hidden event on the second query exactly when the retained bit is true. -/
def condition (s : Bool × Bool) : MC (Σ i, inside.X i) :=
  ⟨fun xs => s.2 = true ∧ secondCall.1 xs,
    fun _ _ hp reached => ⟨reached.1, secondCall.2 hp reached.2⟩⟩

/-- A single retained draw controls both the second reply and the hidden event. -/
noncomputable def game : TypedGame inside :=
  TypedGame.ofAutomaton inside reply initial condition

/-- Fix the retained bit in the existing automaton-game presentation. -/
noncomputable abbrev branch (b : Bool) := DDG.withMBO
  (⟨(inside.automatonDDS reply (false, b)).1,
    (inside.automatonDDS reply (false, b)).2.1⟩, condition (false, b))

/-- The single visible outside query is answered by `b`. -/
def outsideReply (b : Bool) : List ((Σ i, outside.X i) × Σ i, outside.Y i) :=
  [(⟨(), ()⟩, ⟨(), b⟩)]

/-- A true final reply is the outside bad event. -/
def bad (h : List ((Σ i, outside.X i) × Σ i, outside.Y i)) : Prop :=
  ⟨(), true⟩ ∈ h.map Prod.snd

/-- The game's coefficient averages the executions of its retained-bit branches. -/
lemma game_mass (h) : game.1.1 h = (𝒰[Bool]).1.mass
    (fun b => Replies (branch b).1 (h.map Prod.fst) (h.map Prod.snd)) := by
  dsimp only [game, TypedGame.ofAutomaton, TypedGame.ofPDG]
  rw [PDG.behavior_apply, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
  rw [initial, ProbDist.map_val, mass_fTransform]

/-- The first tagged reply is `(false,false)` and the second is `(b,b)`. -/
lemma branch_replies (b : Bool) : Replies (branch b).1
    ((RandomSystem.parallelRight (completed b)).map Prod.fst)
    ((RandomSystem.parallelRight (completed b)).map Prod.snd) := by
  refine ⟨rfl, ?_⟩
  intro k hk _
  change k < 2 at hk
  interval_cases k <;>
    simp [completed, resourceInput, RandomSystem.parallelRight,
      branch, DDG.withMBO, Interface.automatonDDS, filterDom,
      automatonSystem, stateAfter, condition, secondCall, reply,
      inside, Interface.queryBudget, tagMBO]

/-- The checked component executions form the same completed interaction for either bit. -/
lemma branch_pair_replies (b : Bool) : Replies
    (pair (liftMBO (DDC.ofProgramOn () verify outside.domain)) (branch b).1)
    ((completed b).map Prod.fst) ((completed b).map Prod.snd) :=
  (RandomSystem.replies_pair_iff _ _ _).mpr
    ⟨by simp [RandomSystem.parallelConsistent, completed, resourceInput],
      completed_converter_replies b, branch_replies b⟩

/-- On any supported completed execution, an inside win appears as a true outside reply. -/
lemma inside_bad (a : Bool) (t : List (JointQuery × JointReply))
    (follows : FollowsStrategy
      (connectionQueries resourceRoute resourceInput ((outsideReply a).map Prod.fst)) t)
    (stopped : ¬ (connectionQueries resourceRoute resourceInput
      ((outsideReply a).map Prod.fst) (t.map Prod.snd)).Dom)
    (positive : RandomSystem.parallel (PDCBehavior.liftMBO verifier).1 game.1.1 t ≠ 0)
    (displayed : (exposedReplies (resourceRoute (U := outside.X))
      (t.map Prod.snd)).map forgetMBO = (outsideReply a).map Prod.snd)
    (reached : finalMBO (RandomSystem.parallelRight t) = true) :
    bad (outsideReply a) := by
  rw [RandomSystem.parallel_mass] at positive
  split_ifs at positive with consistent
  · obtain ⟨converterPositive, gamePositive⟩ := mul_ne_zero_iff.mp positive
    have converterRun := PDCBehavior.liftMBO_ofDDC_ne_zero_iff _ _ _ |>.mp converterPositive
    have retained : ∃ b, Replies (branch b).1
        ((RandomSystem.parallelRight t).map Prod.fst)
        ((RandomSystem.parallelRight t).map Prod.snd) := by
      by_contra absent
      apply gamePositive
      rw [game_mass]
      exact mass_eq_zero_of_forall_not _ (fun b hb => absent ⟨b, hb⟩)
    obtain ⟨b, branchRun⟩ := retained
    have jointRun := (RandomSystem.replies_pair_iff _ _ t).mpr
      ⟨consistent, converterRun, branchRun⟩
    -- Stopping identifies this execution with the checked retained-bit interaction.
    obtain ⟨hx, hy⟩ := (follows.transcript jointRun).eq_of_stopped
      ((completed_follows b).transcript (branch_pair_replies b)) stopped (completed_stops b)
    have history : t = completed b :=
      (List.zip_of_prod rfl rfl).trans
        ((congrArg₂ List.zip hx hy).trans (List.zip_of_prod rfl rfl).symm)
    subst t
    change b = true at reached
    subst b
    simpa [bad, outsideReply, completed, exposedReplies, resourceRoute, forgetMBO] using
      congrArg (fun ys => (⟨(), true⟩ : Σ i, outside.Y i) ∈ ys) displayed
  · exact (positive rfl).elim

/-- The generic off-bad law applies with its completed-interaction contract proved. -/
lemma unset_eq_visible :
    PDCBehavior.attach inside.nonempty_prefix outside.nonempty_prefix
      (PDCBehavior.liftMBO verifier) game.1.1 game.1.2 (unsetMBOs (outsideReply false)) =
      (verifier • game.visible).1 (outsideReply false) := by
  apply PDCBehavior.attach_liftMBO_unset_eq_attach_visible_of_not_bad
    inside.nonempty_prefix outside.nonempty_prefix verifier game.1.1 game.1.2 game.2
    (outsideReply false) bad
  · simp [bad, outsideReply]
  · exact inside_bad false

/-- The two calls retain one bit and return its value. -/
lemma combined_reply (b : Bool) :
    verify.combine reply verify_bounded ((), (false, b)) () () = (((), (true, b)), b) := by
  rfl

/-- Both good and bad outside replies have positive probability `1/2`. -/
lemma visible_mass (a : Bool) : (verifier • game.visible).1 (outsideReply a) = 1 / 2 := by
  rw [game, TypedGame.visible_ofAutomaton, verifier,
    TypedConverter.ofProgram_smul_ofAutomaton, TypedSystem.ofAutomaton_mass,
    ProbDist.map_val, mass_fTransform, initial, ProbDist.map_val, mass_fTransform]
  have event : ∀ b, Replies
      (filterDom outside.domain (automatonSystem (verify.combine reply verify_bounded)
        ((), (false, b))))
      ((outsideReply a).map Prod.fst) ((outsideReply a).map Prod.snd) ↔ b = a := by
    intro b
    change Replies _ ([] ++ [(⟨(), ()⟩ : Σ i, outside.X i)])
      ([] ++ [(⟨(), a⟩ : Σ i, outside.Y i)]) ↔ b = a
    rw [replies_snoc]
    suffices (verify.combine reply verify_bounded ((), (false, b)) () ()).2 = a ↔
        b = a by
      simpa [filterDom, automatonSystem, stateAfter, outside, Interface.queryBudget] using this
    rw [combined_reply b]
  rw [mass_congr _ event, mass_singleton]
  change uniform Bool a = 1 / 2
  norm_num [uniform_apply]

example :
    PDCBehavior.attach inside.nonempty_prefix outside.nonempty_prefix
      (PDCBehavior.liftMBO verifier) game.1.1 game.1.2 (unsetMBOs (outsideReply false)) =
      1 / 2 := unset_eq_visible.trans (visible_mass false)

#print axioms PDCBehavior.attach_liftMBO_unset_eq_attach_visible_of_not_bad
#print axioms inside_bad
#print axioms unset_eq_visible
#print axioms visible_mass

end Tests.MBOOffBadAttachment

module

public import RandomSystems.Typed.GameEventReflection
public import RandomSystems.Typed.AutomatonGame
public import RandomSystems.Typed.DSL.Converters
public import Mathlib.Tactic.IntervalCases

/-!
# Completed verification-call regression

A verifier receives one outside query, makes two inside calls, and returns the second reply.
The first reply has MBO `false`; the final verification reply may set it. The completed
interaction retains that last bit, whereas the prefix before verification is unfinished.
The caller’s reflection contract is proved and its success probability is one.
-/

@[expose] public section

namespace Tests.GameEventReflection

open SystemAlgebra Probability Probability.Distribution

/-- One outside unit query returns the verifier's Boolean answer. -/
abbrev outside : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Two inside unit queries return Boolean answers. -/
abbrev inside : Interface := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- Make the initial call and the final verification call, then return the second reply. -/
def verify : Program Unit outside.I inside.I outside.X outside.Y inside.X inside.Y :=
  fun _ _ _ exchanges => match exchanges with
    | [] => .inr ⟨(), ()⟩
    | [_] => .inr ⟨(), ()⟩
    | _ :: (_, ⟨(), reply⟩) :: _ => .inl ((), reply)

lemma verify_bounded : verify.Bounded 2 := by
  intro _ _ _ exchanges q _ hq
  rcases exchanges with _ | ⟨first, _ | ⟨second, rest⟩⟩
  · simp only [List.length_nil]; omega
  · simp only [List.length_cons, List.length_nil]; omega
  · rcases second with ⟨_, ⟨⟨⟩, reply⟩⟩
    simp only [verify, reduceCtorEq] at hq

/-- `verifier` keeps the one-query outside domain and spends two inside queries. -/
noncomputable def verifier : TypedConverter outside inside :=
  TypedConverter.ofProgram () verify verify_bounded (fun _ hne hlen => ⟨hne, hlen⟩)

/-- The joint request alphabet: converter input or game query. -/
abbrev JointQuery := Two (Σ l, twoFam outside.X (withMBO inside.Y) l) (Σ i, inside.X i)

/-- The joint reply alphabet: converter output or tagged game reply. -/
abbrev JointReply := Two (Σ l, twoFam (withMBO outside.Y) inside.X l)
  (Σ i, withMBO inside.Y i)

/-- Query, first reply, final query, final reply, outside answer; `b` is the final bit. -/
def completed (b : Bool) : List (JointQuery × JointReply) :=
  [(resourceInput ⟨(), ()⟩, ⟨none, ⟨⟨some (), ()⟩, ()⟩⟩),
   (⟨some (), ⟨(), ()⟩⟩, ⟨some (), ⟨(), (false, false)⟩⟩),
   (⟨none, ⟨⟨some (), ()⟩, (false, false)⟩⟩, ⟨none, ⟨⟨some (), ()⟩, ()⟩⟩),
   (⟨some (), ⟨(), ()⟩⟩, ⟨some (), ⟨(), (b, b)⟩⟩),
   (⟨none, ⟨⟨some (), ()⟩, (b, b)⟩⟩, ⟨none, ⟨⟨none, ()⟩, (b, b)⟩⟩)]

lemma completed_follows (b : Bool) : FollowsStrategy
    (connectionQueries resourceRoute resourceInput [⟨(), ()⟩]) (completed b) := by
  rw [FollowsStrategy.iff_getElem]
  intro i hi
  simp only [completed, List.length_cons, List.length_nil] at hi
  interval_cases i <;>
    simp [completed, connectionQueries, exposedReplies, resourceRoute, resourceInput]

-- The verifier has actually consumed both inside replies before it returns its answer.
example (b : Bool) :
    (DDC.ofProgram () verify)
      [⟨⟨none, ()⟩, ()⟩, ⟨⟨some (), ()⟩, false⟩, ⟨⟨some (), ()⟩, b⟩] =
        Part.some ⟨⟨none, ()⟩, b⟩ := by
  simp [DDC.ofProgram, Program.after, Program.run, Program.step, Program.emit, verify]

-- All requested outside replies have arrived, and the final inside call is included.
lemma completed_stops (b : Bool) :
    ¬ (connectionQueries (resourceRoute (U := outside.X)) resourceInput
      [⟨(), ()⟩] ((completed b).map Prod.snd)).Dom := by
  simp [connectionQueries, exposedReplies, completed, resourceRoute]

example (b : Bool) :
    finalMBO (RandomSystem.parallelRight (completed b)) = b := rfl

-- The prefix before the final verification reply still has no outside answer and no bad bit.
example (b : Bool) :
    (connectionQueries (resourceRoute (U := outside.X)) resourceInput
      [⟨(), ()⟩] (((completed b).take 3).map Prod.snd)).Dom ∧
      finalMBO (RandomSystem.parallelRight ((completed b).take 3)) = false := by
  exact ⟨by norm_num [connectionQueries, exposedReplies, completed, resourceRoute], rfl⟩

-- Success before making any call cannot imply a hidden event: the empty interaction has no MBO.
example (α : TypedConverter outside inside) (G : TypedGame inside) :
    ¬ α.ReflectsMBO G.1.1 (fun _ => True) := by
  intro hreflect
  have hb := hreflect [] [] FollowsStrategy.nil
    (by simp [connectionQueries, exposedReplies])
    (by rw [RandomSystem.mass_nil]; exact one_ne_zero) rfl trivial
  exact Bool.noConfusion hb

/-- The monitor is set only by the second query, including a final verification query. -/
def secondCall : MC (Σ i, inside.X i) :=
  ⟨fun xs => 2 ≤ xs.length, fun _ _ hp h => h.trans hp.length_le⟩

/-- Reply `false` then `true`; the final verification call sets the hidden event. -/
noncomputable def monitored : TypedGame inside :=
  TypedGame.ofAutomaton inside (fun (seen : Bool) _ _ => (true, seen))
    (ProbDist.single false) (fun _ => secondCall)

example : monitored.1.1.unsetProbability [⟨(), ()⟩] = 1 := by
  rw [monitored, TypedGame.ofAutomaton_unsetProbability _ _ _ _
    (show inside.domain [⟨(), ()⟩] from ⟨by simp, by simp⟩)]
  norm_num [Distribution.mass_single, secondCall, ProbDist.single]

example : monitored.1.1.unsetProbability [⟨(), ()⟩, ⟨(), ()⟩] = 0 := by
  rw [monitored, TypedGame.ofAutomaton_unsetProbability _ _ _ _
    (show inside.domain [⟨(), ()⟩, ⟨(), ()⟩] from ⟨by simp, by simp⟩)]
  norm_num [Distribution.mass_single, secondCall, ProbDist.single]


/-- The deterministic presentation already used by `monitored`, with its hidden bit. -/
noncomputable abbrev monitoredDDS := DDG.withMBO
  (⟨(inside.automatonDDS (fun (seen : Bool) _ _ => (true, seen)) false).1,
    (inside.automatonDDS (fun (seen : Bool) _ _ => (true, seen)) false).2.1⟩, secondCall)

open Classical in
/-- The single retained initial state gives mass one exactly on its deterministic replies. -/
lemma monitored_mass (h) : monitored.1.1 h =
    if Replies monitoredDDS.1 (h.map Prod.fst) (h.map Prod.snd) then 1 else 0 := by
  classical
  dsimp only [monitored, TypedGame.ofAutomaton, TypedGame.ofPDG]
  rw [PDG.behavior_apply, PDG.ofAutomaton, ProbDist.map_val, mass_fTransform]
  simp only [ProbDist.single, mass_single, monitoredDDS]

/-- The compiled program consumes two replies and returns the second with its current MBO. -/
lemma completed_converter_replies (b : Bool) : Replies
    (liftMBO (DDC.ofProgramOn () verify outside.domain))
    ((RandomSystem.parallelLeft (completed b)).map Prod.fst)
    ((RandomSystem.parallelLeft (completed b)).map Prod.snd) := by
  refine ⟨rfl, ?_⟩
  intro k hk _
  change k < 3 at hk
  interval_cases k <;>
    simp [completed, resourceInput, RandomSystem.parallelLeft, liftMBO,
      insideMap, outsideMap, forgetMBO, latestMBO, inputMBO, tagMBO,
      DDC.ofProgramOn, filterDom, outsideInputs, splitIn, SystemAlgebra.restrict,
      DDC.ofProgram, Program.after, Program.run, Program.step, Program.emit, verify,
      outside, Interface.queryBudget]
  rfl

/-- The retained game replies `(false,false)` and then `(true,true)`. -/
lemma completed_game_replies : Replies monitoredDDS.1
    ((RandomSystem.parallelRight (completed true)).map Prod.fst)
    ((RandomSystem.parallelRight (completed true)).map Prod.snd) := by
  refine ⟨rfl, ?_⟩
  intro k hk _
  change k < 2 at hk
  interval_cases k <;>
    simp [completed, resourceInput, RandomSystem.parallelRight,
      monitoredDDS, DDG.withMBO, Interface.automatonDDS, filterDom,
      automatonSystem, stateAfter, secondCall, inside, Interface.queryBudget, tagMBO]

/-- Pairing those component executions yields the full five-exchange interaction. -/
lemma completed_replies : Replies
    (pair (liftMBO (DDC.ofProgramOn () verify outside.domain)) monitoredDDS.1)
    ((completed true).map Prod.fst) ((completed true).map Prod.snd) :=
  (RandomSystem.replies_pair_iff _ _ _).mpr
    ⟨by simp [RandomSystem.parallelConsistent, completed, resourceInput],
      completed_converter_replies true, completed_game_replies⟩

/-- Completing the outside query includes the second inside call and hence sets the monitor. -/
lemma verifier_reflects : verifier.ReflectsMBO monitored.1.1 (fun h => h.length = 1) := by
  apply PDCBehavior.reflectsMBO_of_unset_eq_zero _ _ monitored.2
  intro h t hc hstop hpar hα hG _ hlen
  -- Positive component masses are executions of the same compiled program and retained game.
  have hra := PDCBehavior.liftMBO_ofDDC_ne_zero_iff _ _ _ |>.mp hα
  have hrg : Replies monitoredDDS.1
      ((RandomSystem.parallelRight t).map Prod.fst)
      ((RandomSystem.parallelRight t).map Prod.snd) := by
    rw [monitored_mass] at hG
    split_ifs at hG with hr
    · exact hr
    · exact (hG rfl).elim
  have hr := (RandomSystem.replies_pair_iff _ _ t).mpr ⟨hpar, hra, hrg⟩
  have hus : h.map Prod.fst = [⟨(), ()⟩] := by
    obtain ⟨z, rfl⟩ := List.length_eq_one_iff.mp hlen
    rcases z with ⟨⟨⟨⟩, ⟨⟩⟩, y⟩
    rfl
  rw [hus] at hc hstop
  -- Completion identifies the actual run with the checked five-exchange execution.
  obtain ⟨hx, hy⟩ := (hc.transcript hr).eq_of_stopped
    ((completed_follows true).transcript completed_replies) hstop (completed_stops true)
  have ht : t = completed true := by
    exact (List.zip_of_prod rfl rfl).trans
      ((congrArg₂ List.zip hx hy).trans (List.zip_of_prod rfl rfl).symm)
  rw [ht]
  change monitored.1.1
    (unsetMBOs [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)]) = 0
  rw [monitored, TypedGame.ofAutomaton_mass_unsetMBOs]
  · simp [secondCall, ProbDist.single, mass_single]
  · intro s _
    simp [secondCall]

/-- Ask one unit query, then stop. -/
def query : DDE (Σ i, outside.X i) (Σ i, outside.Y i) := DDE.ofQueries [⟨(), ()⟩]

lemma query_bounded : QueryBounded 1 query := by
  intro ys hd
  simpa only [Order.lt_one_iff, List.length_eq_zero_iff, query, DDE.ofQueries, fixedQueries,
    Part.ofOption_dom, isSome_getElem?, List.length_cons, List.length_nil, zero_add] using hd

lemma query_compatible : outside.inputDomain.Compatible query := by
  intro _ _ h x _ _ hx
  have hh : h = [] := List.length_eq_zero_iff.mp (by
    have hb := query_bounded (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    simp only [List.length_map] at hb
    omega)
  subst h
  exact ⟨by simp, by simp⟩

/-- Accept once the single requested reply arrives. -/
noncomputable def observer : outside.inputDomain.Distinguisher :=
  ProbDist.single ⟨envProbe query (fun t => t.2.length = 1),
    envProbe_isDDD query_bounded, Domain.envProbe_decisionCompatible query_compatible _⟩

/-- Acceptance of this probe certifies that one reply arrived. -/
lemma observer_accepts_length {h : List ((Σ i, outside.X i) × Σ i, outside.Y i)}
    (ha : (⟨.dec, true⟩ : Σ p, dOut outside.X p) ∈
      trim (envProbe query (fun t => t.2.length = 1)) (dHist (h.map Prod.snd))) :
    h.length = 1 := by
  classical
  unfold trim at ha
  split_ifs at ha with hr
  swap
  · simp at ha
  obtain ⟨ys, he, hf⟩ := envProbe_dom (Part.dom_iff_mem.mpr ⟨_, ha⟩)
  have hy : h.map Prod.snd = ys :=
    List.map_injective_iff.mpr envIn_injective (List.cons.inj he).2
  subst ys
  rw [envProbe_dHist hf, envReply] at ha
  split_ifs at ha
  · simp only [Part.mem_some_iff, Sigma.mk.inj_iff, reduceCtorEq, false_and] at ha
  · simp only [Part.mem_some_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and,
      List.length_map] at ha
    exact of_decide_eq_true ha.symm

/-- The observer accepts the actual attached system with probability one. -/
lemma observer_probability_eq_one : observer.probability (verifier • monitored.visible).1 = 1 := by
  simp only [observer, ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul]
  rw [RandomSystem.decisionProbability_envProbe query_bounded _
    (verifier • monitored.visible).2]
  let R := verifier • monitored.visible
  let law : ProbDist _ := ⟨R.1.sLaw query.1 1,
    R.1.sLaw_isProbDist (query_compatible _ R.2) 1⟩
  apply law.mass_eq_one_of_support
  intro h hh
  have hg : Good query.1 1 h := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hh (by rw [RandomSystem.sLaw_apply, ite_eq_right hn])
  rcases hg.2 with hl | ⟨hl, hstop⟩
  · simpa only [List.length_map] using hl
  · have he : h = [] := List.length_eq_zero_iff.mp (by omega)
    subst h
    exact (hstop (by simp [query, DDE.ofQueries, fixedQueries])).elim

/-- The concrete caller's reflection contract is proved, with no supplied reflection premise. -/
lemma observer_reflects : observer.ReflectsMBO verifier monitored.1.1 := by
  intro D hD h t hc hstop hp hexp hs
  have he : D = ⟨envProbe query (fun t => t.2.length = 1),
      envProbe_isDDD query_bounded, Domain.envProbe_decisionCompatible query_compatible _⟩ := by
    simpa only [observer, ProbDist.single, Finsupp.support_single _ one_ne_zero,
      Finset.mem_singleton] using hD
  subst D
  exact verifier_reflects h t hc hstop hp hexp (observer_accepts_length hs.2)

-- The full reduction uses the checked program, game and caller.
example :
    (TypedSolver.ofDistinguisher observer).decision.1 (verifier • monitored.visible) ≤
      ((TypedSolver.ofDistinguisher observer).absorb verifier).winProbability monitored :=
  TypedSolver.probability_attach_le_winProbability_absorb _ _ _
    (TypedSolver.ofDistinguisher_reflectsMBO _ _ _ observer_reflects)

-- The arbitrary-event corollary is independent of what the observer decides.
example (P : inside.inputDomain.Distinguisher) :
    (P.transcriptLaw monitored.visible).1.mass (fun h => 2 ≤ h.length) ≤
      P.winProbability monitored.1.1 := by
  apply Domain.Distinguisher.transcript_event_mass_le_winProbability
  intro h hh
  rw [monitored, TypedGame.ofAutomaton_mass_unsetMBOs]
  · simp only [ProbDist.single, mass_single, secondCall, List.length_map]
    simp only [hh, not_true_eq_false, and_false, ite_false]
  · intro s _
    simp [secondCall]

#print axioms observer_probability_eq_one
#print axioms observer_reflects
#print axioms verifier_reflects

#print axioms PDCBehavior.probability_attach_le_winProbability
#print axioms TypedSolver.probability_attach_le_winProbability_absorb

end Tests.GameEventReflection

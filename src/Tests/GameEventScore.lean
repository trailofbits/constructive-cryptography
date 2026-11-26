module

public import RandomSystems.Game.EventReflection
public import Tests.AutomatonGame

/-!
# Exact scores for a transcript event

The echo resource sets its hidden bit when a query is `true`. Its cumulative unset law is
exactly the echo law restricted to histories with no such query. The adaptive two-call observer
and the immediately stopping observer both use the same exact event-score theorem.
-/

@[expose] public section

namespace Tests.GameEventScore

open SystemAlgebra Probability Probability.Distribution Tests.GameTranscript

/-- The condition is reached as soon as a query carries `true`. -/
def queryTrue : MC (Σ i, port.X i) :=
  ⟨fun xs => (⟨(), true⟩ : Σ i, port.X i) ∈ xs,
    fun _ _ hp h => hp.sublist.subset h⟩

/-- Echo each query and monitor whether a `true` query has occurred. -/
noncomputable def monitored : TypedGame port :=
  TypedGame.ofAutomaton port AutomatonGame.retainedEcho (ProbDist.single false) (fun _ => queryTrue)

/-- The same echo resource supplies the reference transcript law. -/
noncomputable def reference : TypedSystem port :=
  TypedSystem.ofAutomaton port AutomatonGame.retainedEcho (ProbDist.single false)

/-- The event is a `true` query anywhere in the visible transcript. -/
def event (h : List ((Σ i, port.X i) × Σ i, port.Y i)) : Prop :=
  (⟨(), true⟩ : Σ i, port.X i) ∈ h.map Prod.fst

/-- The monitor removes precisely the reference transcripts containing a `true` query. -/
lemma unset (h) [DecidablePred event] :
    monitored.1.1 (unsetMBOs h) = if event h then 0 else reference.1 h := by
  rw [monitored, TypedGame.ofAutomaton_mass_unsetMBOs _ _ _ _
    (fun _ _ => List.not_mem_nil), reference, TypedSystem.ofAutomaton_mass]
  change (ProbDist.single false).1.mass (fun s =>
    Replies (filterDom port.domain (automatonSystem AutomatonGame.retainedEcho s))
      (h.map Prod.fst) (h.map Prod.snd) ∧ ¬ event h) = _
  by_cases he : event h
  · simp only [he, not_true_eq_false, and_false, ite_true]
    exact mass_eq_zero_of_forall_not _ (fun _ h => h)
  · simp only [he, not_false_eq_true, and_true, ite_false]

/-- The adaptive observer submits `true` on its second query, so its event mass is one. -/
example :
    (reference.1.sLaw (ddeOf winner_isDDD).1 winner_isDDD.2.1.choose).mass event = 1 := by
  classical
  have admitted := Domain.envProbe_decisionCompatible adaptive_compatible (fun _ => True)
  have score := RandomSystem.winProbability_eq_mass_of_unset
    monitored.1.2 monitored.2 reference.2 winner winner_isDDD admitted event (fun h _ => unset h)
  refine score.symm.trans ?_
  refine (TypedGame.winProbability_ofAutomaton_at_bound port AutomatonGame.retainedEcho
    (ProbDist.single false) (fun _ => queryTrue) winner winner_isDDD admitted
    AutomatonGame.winner_bounded).trans ?_
  apply (ProbDist.single false).mass_eq_one_of_support
  intro b _
  rw [AutomatonGame.retained_transcript]
  refine ⟨List.cons_ne_nil _ _, ?_⟩
  change (⟨(), true⟩ : Σ i, port.X i) ∈ [⟨(), false⟩, ⟨(), true⟩]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

/-- Immediate stopping has score zero, hence the exact event-score law gives event mass zero. -/
example : (reference.1.sLaw (ddeOf AutomatonGame.stopped_isDDD).1
    AutomatonGame.stopped_isDDD.2.1.choose).mass event = 0 := by
  classical
  have compatible : port.inputDomain.Compatible AutomatonGame.stop := by
    intro _ _ h x _ _ hx
    exact False.elim (Nat.not_lt_zero _
      (AutomatonGame.stop_bound (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)))
  have admitted := Domain.envProbe_decisionCompatible compatible (fun _ => True)
  have score := RandomSystem.winProbability_eq_mass_of_unset
    monitored.1.2 monitored.2 reference.2 AutomatonGame.stopped AutomatonGame.stopped_isDDD
    admitted event (fun h _ => unset h)
  refine score.symm.trans ?_
  refine (TypedGame.winProbability_ofAutomaton_at_bound port AutomatonGame.retainedEcho
    (ProbDist.single false) (fun _ => queryTrue) AutomatonGame.stopped
    AutomatonGame.stopped_isDDD admitted AutomatonGame.stopped_bound).trans ?_
  simp only [System.tr, ne_eq, not_true_eq_false, false_and]
  exact mass_eq_zero_of_forall_not _ (fun _ h => h)

#print axioms RandomSystem.winProbability_eq_mass_of_unset

end Tests.GameEventScore

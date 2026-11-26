module

public import ConstructiveCryptography.Instances.SubmissionGame
public import RandomSystems.Game.Transcript

/-!
# Submission-game boundaries

An empty submission type admits the game without a chosen value. An immediately stopping
observer loses. The same solver law handles overlapping predicates, and the abstract
submission structure is the typed game's instance.
-/

@[expose] public section

namespace Tests.SubmissionGame

open SystemAlgebra Probability Probability.Distribution

/-- No value of `Empty` is needed to construct or evaluate the game. -/
example (s : TypedSolver (Interface.submission Empty)) (p : Set Empty) :
    s.winProbability (TypedGame.submission p) = 0 := by
  obtain ⟨μ, score⟩ := s.exists_submission_law
  rw [score]
  exact mass_eq_zero_of_forall_not _ (fun _ ⟨x, _, _⟩ => Empty.elim x)

/-- The predicate `x = true` overlaps itself; the union bound needs no disjointness premise. -/
example (s : TypedSolver (Interface.submission Bool)) :
    s.winProbability (TypedGame.submission {true}) ≤
      s.winProbability (TypedGame.submission {true}) +
      s.winProbability (TypedGame.submission {true}) := by
  simpa only [Set.union_self] using s.submission_union_le {true} {true}

/-- An acknowledged successful submission has no all-unset mass. -/
example : (TypedGame.submission ({true} : Set Bool)).1.1
    (unsetMBOs [(⟨(), true⟩, ⟨(), ()⟩)]) = 0 := by
  classical
  rw [TypedGame.submission_unset, ite_eq_left]
  exact ⟨true, List.mem_singleton_self _, rfl⟩

/-- The abstract interpretation uses exactly the typed submission game. -/
example (p : Set Bool) : (Interface.submissionGame Bool).game p = TypedGame.submission p := rfl

/-- One Boolean submission with a unit acknowledgment. -/
abbrev port : Interface := Interface.submission Bool

/-- Stop before making the submission. -/
def stop : DDE (Σ i, port.X i) (Σ i, port.Y i) := DDE.ofQueries []

/-- The caller issues zero queries. -/
lemma stop_bound : QueryBounded 0 stop := by
  intro ys hd
  simpa only [stop, DDE.ofQueries, fixedQueries, Part.ofOption_dom,
    isSome_getElem?, List.length_nil] using hd

/-- The stopping caller still produces a decision. -/
noncomputable def stopped : DDD port.I port.X port.Y := envProbe stop (fun _ => True)

/-- The decision-producing probe inherits that finite bound. -/
lemma stopped_isDDD : IsDDD stopped := envProbe_isDDD stop_bound

/-- Even accepting every submitted value gives score zero if no value was submitted. -/
example : (TypedGame.submission (Set.univ : Set Bool)).1.1.winProbability
    stopped stopped_isDDD = 0 := by
  have hn := ddeOf_envProbe_queryBounded stop_bound (fun _ => True)
  have compatible : (TypedGame.submission (Set.univ : Set Bool)).visible.1.Compatible
      (ddeOf stopped_isDDD).1 := by
    intro h x _ _ hx
    exact False.elim (Nat.not_lt_zero _
      (hn (h.map Prod.snd) (Part.dom_iff_mem.mpr ⟨x, hx⟩)))
  let P := PDG.ofSingleFunction port.domain port.nonempty_prefix port.bound port.length_le
    (ProbDist.single ()).1 (fun _ _ => ()) (fun _ => submissionCondition (Set.univ : Set Bool))
  have hP : P.isProbDist := PDG.ofFunction_isProbDist port.domain port.nonempty_prefix
    port.bound port.length_le (ProbDist.single ()).2 _ _
  refine (PDG.winProbability_behavior P hP stopped stopped_isDDD compatible hn).trans ?_
  simp only [System.tr, ne_eq, not_true_eq_false, false_and]
  exact mass_eq_zero_of_forall_not _ (fun _ h => h)

#print axioms TypedSolver.exists_submission_law
#print axioms TypedSolver.submission_union_le

end Tests.SubmissionGame

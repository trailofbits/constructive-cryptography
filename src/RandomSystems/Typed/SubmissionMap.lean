module

public import RandomSystems.Typed.Submission
public import RandomSystems.Typed.GameRouting

/-!
# Decoding submissions

`TypedConverter.submissionMap f` sends the submitted value `x` to `f x` and returns the unit
acknowledgment. Both interfaces admit at most one query.

`TypedConverter.submissionMap_attachGame` identifies attachment with predicate preimage:
`submissionMap f • submission p = submission (f ⁻¹' p)`. Its proof uses the functional
presentation of the game and the MBO-preserving routing law.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `X` and `Y` carry submitted values before and after decoding; either may be empty.
variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The submission game replies with `((), decide (p x))` on its sole admitted query `x`. -/
lemma TypedGame.submission_eq_ofFunction (p : Set X) [DecidablePred p] :
    (submission p).1 = TypedSystem.ofFunction (A := (Interface.submission X).withMBO)
      (fun _ x => ((), decide (p x))) := by
  let A := Interface.submission X
  -- An admitted final input is the only submission, so its predicate is the whole condition.
  have condition (xs : List (Σ i, A.X i)) (x : Σ i, A.X i)
      (admitted : A.domain (xs ++ [x])) :
      (submissionCondition p).1 ((xs ++ [x]).map Sigma.snd) ↔ p x.2 := by
    have empty : xs = [] := List.length_eq_zero_iff.mp (by
      have length := admitted.2
      simp only [List.length_append, List.length_singleton] at length
      omega)
    subst xs
    simp only [List.nil_append, List.map_singleton, submissionCondition,
      List.mem_singleton]
    constructor
    · rintro ⟨z, rfl, hp⟩
      exact hp
    · exact fun hp => ⟨x.2, rfl, hp⟩
  -- The generic presentation keeps the same draw in the visible reply and monitor.
  have tagged := PDG.withMBO_ofFunction (Y := fun _ : Unit => Unit)
    A.domain A.nonempty_prefix A.bound A.length_le
    (ProbDist.single ()).1 (fun _ x => ⟨x.1, ()⟩)
    (fun _ => ⟨fun xs => (submissionCondition p).1 (xs.map Sigma.snd),
      fun {_ _} h hp => (submissionCondition p).2 (h.map Sigma.snd) hp⟩)
    (fun (_ : Unit) x => p x.2) (fun _ => condition)
  -- Both presentations have the same sampled replies; erase the unused unit draw.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  change behaviorMass _ (h.map Prod.fst) (h.map Prod.snd) = _
  rw [PDG.ofSingleFunction, tagged]
  have sampled := congrArg (fun R : TypedSystem A.withMBO => R.1 h)
    (TypedSystem.sample_const (ProbDist.single ()).1
      (TypedSystem.ofFunction (fun _ x => ((), decide (p x)))))
  rw [TypedSystem.sample_ofFunction_mass, behaviorMass, mass_fTransform] at sampled
  rw [behaviorMass, PDS.ofFunction, mass_fTransform]
  exact sampled

/-- Submit `f x` inside for outside value `x`, then return the unit acknowledgment. -/
noncomputable def TypedConverter.submissionMap (f : X → Y) :
    TypedConverter (Interface.submission X) (Interface.submission Y) :=
  TypedConverter.routing (fun u => ⟨(), f u.2⟩) (fun _ _ => ())
    (fun _ admitted => Interface.queryBudget_domain_map _ (le_refl 1) admitted)

/-- Decoding by `f` tests exactly the preimage `f ⁻¹' p` of the inside successful set. -/
theorem TypedConverter.submissionMap_attachGame (f : X → Y) (p : Set Y) :
    (submissionMap f).attachGame (TypedGame.submission p) =
      TypedGame.submission (f ⁻¹' p) := by
  classical
  let : DecidablePred p := fun _ => Classical.propDecidable _
  let : DecidablePred (f ⁻¹' p) := fun _ => Classical.propDecidable _
  apply Subtype.ext
  change TypedConverter.attach (A := (Interface.submission X).withMBO)
    (B := (Interface.submission Y).withMBO)
    (PDCBehavior.liftMBO (submissionMap f)) (TypedGame.submission p).1 = _
  rw [TypedGame.submission_eq_ofFunction p, submissionMap, liftMBO_routing]
  exact (routing_smul_ofFunction (A := (Interface.submission X).withMBO)
    (B := (Interface.submission Y).withMBO) (fun u => ⟨(), f u.2⟩)
    (fun _ r => ((), r.2.2)) _ (fun _ y => ((), decide (p y)))).trans
      (TypedGame.submission_eq_ofFunction (f ⁻¹' p)).symm

end SystemAlgebra

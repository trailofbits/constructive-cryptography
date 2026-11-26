module

public import RandomSystems.Typed.PresentedGame
public import RandomSystems.Typed.Solver
public import RandomSystems.Typed.TranscriptLaw
public import RandomSystems.Typed.SampleLaws
public import RandomSystems.Game.EventReflection

/-!
# Games testing one submission

`Interface.submission X` accepts at most one value `x : X` and acknowledges it with `()`.
`TypedGame.submission p` wins exactly when that value satisfies `p`. Stopping without a
submission loses, including when `X` is empty.

`TypedSolver.exists_submission_law` gives one distribution of submitted-value lists for every
predicate tested by the same solver. Monotonicity and the union bound follow from that law.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

/-- Submit at most one `x : X`; the sole port replies with the unit acknowledgment. -/
abbrev Interface.submission (X : Type) [Fintype X] : Interface :=
  Interface.queryBudget Unit (fun _ => X) (fun _ => Unit) 1

-- `X` is the finite set of submitted values; it may be empty.
variable {X : Type} [Fintype X]

/-- The hidden condition becomes true when a submitted value satisfies `p`. -/
def submissionCondition (p : Set X) : MC X :=
  ⟨fun xs => ∃ x ∈ xs, p x, fun {_ _} hp ⟨x, hx, hpx⟩ =>
    ⟨x, hp.sublist.subset hx, hpx⟩⟩

/-- The completed transcript contains a submitted value in `p`. -/
def submissionEvent (p : Set X)
    (h : List ((Σ i, (Interface.submission X).X i) ×
      Σ i, (Interface.submission X).Y i)) : Prop :=
  (submissionCondition p).1 ((h.map Prod.fst).map Sigma.snd)

/-- The visible acknowledgment system, independent of the tested predicate. -/
noncomputable def TypedSystem.submission (X : Type) [Fintype X] :
    TypedSystem (Interface.submission X) :=
  TypedSystem.ofFunction (fun _ _ => ())

/-- Submit `x`, receive `()`, and set the hidden winning bit exactly when `p x`. -/
noncomputable def TypedGame.submission (p : Set X) : TypedGame (Interface.submission X) :=
  let A := Interface.submission X
  TypedGame.ofSingleFunction A.domain A.nonempty_prefix A.bound A.length_le
    (ProbDist.single ()).1 (fun _ _ => ()) (fun _ => submissionCondition p)

/-- All-unset mass is the acknowledgment mass restricted to no successful submission. -/
lemma TypedGame.submission_unset (p : Set X) [DecidablePred (submissionEvent p)]
    (h : List ((Σ i, (Interface.submission X).X i) ×
      Σ i, (Interface.submission X).Y i)) :
    (submission p).1.1 (unsetMBOs h) =
      if submissionEvent p h then 0 else (TypedSystem.submission X).1 h := by
  classical
  let A := Interface.submission X
  let P := PDG.ofSingleFunction A.domain A.nonempty_prefix A.bound A.length_le
    (ProbDist.single ()).1 (fun _ _ => ()) (fun _ => submissionCondition p)
  have hP : P.isProbDist := PDG.ofFunction_isProbDist A.domain A.nonempty_prefix
    A.bound A.length_le (ProbDist.single ()).2 _ _
  refine (PDG.behavior_unsetMBOs hP h).trans ?_
  dsimp only [P, PDG.ofSingleFunction, PDG.ofFunction]
  rw [mass_fTransform]
  have reference := congrArg (fun R : TypedSystem (Interface.submission X) => R.1 h)
    (TypedSystem.sample_const (ProbDist.single ()).1 (TypedSystem.submission X))
  change (TypedSystem.sample (ProbDist.single ()).1
    (fun _ => TypedSystem.ofFunction (A := A) (fun _ _ => ()))).1 h = _ at reference
  rw [TypedSystem.sample_ofFunction_mass, behaviorMass, mass_fTransform] at reference
  rw [← reference]
  change _ = if submissionEvent p h then 0 else
    (ProbDist.single ()).1.mass (fun _ =>
      Replies (DDS.ofFunction (Interface.submission X).domain
        (Interface.submission X).nonempty_prefix
        (fun x => ⟨x.1, ()⟩)).1 (h.map Prod.fst) (h.map Prod.snd))
  by_cases event : submissionEvent p h
  · rw [ite_eq_left event]
    apply mass_eq_zero_of_forall_not
    rintro _ ⟨_, empty | hnot⟩
    · subst h
      rcases event with ⟨x, hx, _⟩
      exact List.not_mem_nil hx
    · exact hnot event
  · rw [ite_eq_right event]
    apply mass_congr
    intro _
    exact and_iff_left (Or.inr event)

/-- One law `μ` on submitted values scores every predicate; early stopping contributes `[]`. -/
theorem TypedSolver.exists_submission_law
    -- `s` is one compatible stopping solver; `μ` retains its submission randomness.
    (s : TypedSolver (Interface.submission X)) :
    ∃ μ : ProbDist (List X),
      ∀ p : Set X, s.winProbability (TypedGame.submission p) =
        μ.1.mass (fun xs => ∃ x ∈ xs, p x) := by
  classical
  obtain ⟨P, -, score⟩ := s.exists_realization
  refine ⟨(P.transcriptLaw (TypedSystem.submission X)).map
    (fun h => (h.map Prod.fst).map Sigma.snd), fun p => ?_⟩
  rw [ProbDist.map_val, mass_fTransform, score, Domain.Distinguisher.winProbability,
    Domain.Distinguisher.transcriptLaw_mass]
  apply Finsupp.sum_congr
  intro D _
  congr 1
  exact RandomSystem.winProbability_eq_mass_of_unset
    (TypedGame.submission p).1.2 (TypedGame.submission p).2
    (TypedSystem.submission X).2 D.1 D.2.1 D.2.2 (submissionEvent p)
    (fun h _ => TypedGame.submission_unset p h)

/-- Enlarging the successful set cannot reduce a fixed solver's winning probability. -/
lemma TypedSolver.submission_mono (s : TypedSolver (Interface.submission X)) :
    Monotone (fun p : Set X => s.winProbability (TypedGame.submission p)) := by
  obtain ⟨μ, score⟩ := s.exists_submission_law
  intro p q hpq
  change s.winProbability (TypedGame.submission p) ≤ s.winProbability (TypedGame.submission q)
  rw [score, score]
  exact mass_mono μ.2.1 (fun _ ⟨x, hx, hp⟩ => ⟨x, hx, hpq hp⟩)

/-- Winning for either predicate is at most the sum, including overlapping predicates. -/
lemma TypedSolver.submission_union_le (s : TypedSolver (Interface.submission X)) (p q : Set X) :
    s.winProbability (TypedGame.submission (p ∪ q)) ≤
      s.winProbability (TypedGame.submission p) + s.winProbability (TypedGame.submission q) := by
  obtain ⟨μ, score⟩ := s.exists_submission_law
  rw [score, score, score]
  have events : (fun xs : List X => ∃ x ∈ xs, (p ∪ q) x) =
      fun xs => (∃ x ∈ xs, p x) ∨ ∃ x ∈ xs, q x := by
    funext xs
    apply propext
    constructor
    · rintro ⟨x, hx, hp | hq⟩
      · exact Or.inl ⟨x, hx, hp⟩
      · exact Or.inr ⟨x, hx, hq⟩
    · rintro (⟨x, hx, hp⟩ | ⟨x, hx, hq⟩)
      · exact ⟨x, hx, Or.inl hp⟩
      · exact ⟨x, hx, Or.inr hq⟩
  rw [events]
  exact mass_or_le μ.2.1 _ _

end SystemAlgebra

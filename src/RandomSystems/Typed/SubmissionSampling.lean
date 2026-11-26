module

public import RandomSystems.Typed.SubmissionSampling.Definitions
public import Probability.Expectation
public import Probability.FiniteSupport

/-!
# Winning probabilities of sampled submissions

`TypedSolver.submission_winProbability` identifies the score of a supplied law `P` with
`P.mass p`. The fixed observer has exactly one submitted query (`Good.fixedQueries`), so its
winning indicator is `1[p x]`; the sampled solver averages that indicator under `P`.
`submission_onFinset_winProbability` presents a law on any carrier through its finite support
and decodes the submitted value without changing the score.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

/-- The complete law of the fixed submission observer is the one-query law of `R`. -/
lemma Submission.distinguisher_sLaw
    -- `x` is submitted to any system `R` at the one-submission interface.
    {X : Type} [Fintype X] (x : X) (R : TypedSystem (Interface.submission X)) :
    R.1.sLaw (ddeOf (distinguisher x).2.1).1 (distinguisher x).2.1.2.1.choose =
      R.1.sLaw (fixedQueries [⟨(), x⟩]) 1 := by
  rw [R.1.sLaw_eq_domainBound (ddeOf_bounded (distinguisher x).2.1)
    ((distinguisher x).2.2.environment (distinguisher x).2.1 R.1 R.2)]
  exact R.1.sLaw_trim_envProbe R.2 (DDE.ofQueries [⟨(), x⟩]) (fun _ => False) 1

open Classical in
/-- Submitting the fixed value `x` wins exactly when `p x` holds. -/
lemma Submission.distinguisher_winProbability
    -- `p` is the game's successful set of submitted values in `X`.
    {X : Type} [Fintype X] (x : X) (p : Set X) :
    (TypedGame.submission p).1.1.winProbability (distinguisher x).1 (distinguisher x).2.1 =
      if p x then 1 else 0 := by
  let R := TypedSystem.submission X
  let μ := R.1.sLaw (fixedQueries [⟨(), x⟩]) 1
  have normalized := R.1.sLaw_isProbDist
    ((distinguisher x).2.2.environment (distinguisher x).2.1 R.1 R.2)
    (distinguisher x).2.1.2.1.choose
  rw [distinguisher_sLaw x R] at normalized
  rw [RandomSystem.winProbability_eq_mass_of_unset (TypedGame.submission p).1.2
    (TypedGame.submission p).2 R.2 _ _ (distinguisher x).2.2 (submissionEvent p)
    (fun h _ => TypedGame.submission_unset p h), distinguisher_sLaw x R]
  have event : μ.mass (submissionEvent p) = μ.mass (fun _ => p x) := by
    apply mass_congr_of_support
    intro h supported
    have good := RandomSystem.tSupp_good (Finsupp.support_onFinset_subset supported)
    have queries := good.fixedQueries
    simp only [List.take_succ_cons, List.take_zero] at queries
    simp only [submissionEvent, submissionCondition, queries, List.map_singleton,
      List.mem_singleton]
    exact ⟨fun ⟨a, ha, accepted⟩ => ha ▸ accepted, fun accepted => ⟨x, rfl, accepted⟩⟩
  -- The event is constant on this normalized one-query law.
  change μ.mass (submissionEvent p) = _
  rw [event]
  by_cases accepted : p x
  · simpa only [accepted, ite_true, mass_true] using normalized.weight_eq
  · rw [ite_eq_right accepted]
    exact mass_eq_zero_of_forall_not μ (fun _ => accepted)

/-- Sampling one submission from `P` gives winning probability `P.mass p`. -/
theorem TypedSolver.submission_winProbability
    -- `P` retains the full joint law on `X`; `p` tests the submitted value.
    {X : Type} [Fintype X] (P : ProbDist X) (p : Set X) :
    (submission P).winProbability (TypedGame.submission p) = P.1.mass p := by
  classical
  change (P.map Submission.distinguisher).1.expect
    (fun D => (TypedGame.submission p).1.1.winProbability D.1 D.2.1) = _
  rw [ProbDist.map_val, expect_fTransform]
  calc
    _ = P.1.expect (fun x => if p x then 1 else 0) :=
      expect_congr_of_support (fun x _ => Submission.distinguisher_winProbability x p)
    _ = _ := expect_indicator P.1 (fun x => p x)

/-- Present `P` on a finite alphabet `s`, then decode by `Subtype.val`; its score is unchanged. -/
lemma TypedSolver.submission_onFinset_winProbability
    -- `X` may be infinite; `supported` places every sampled value of `P` inside `s`.
    {X : Type} (P : ProbDist X) (s : Finset X) (supported : P.1.support ⊆ s)
    -- `p` tests the decoded value in the original carrier `X`.
    (p : Set X) :
    (submission (P.onFinset s supported)).winProbability
      (TypedGame.submission {x | p x.1}) = P.1.mass p := by
  refine (submission_winProbability (P.onFinset s supported) (fun x => p x.1)).trans ?_
  have decoded := congrArg (fun Q : ProbDist X => Q.1.mass (fun x => p x))
    (P.map_onFinset_val s supported)
  rw [ProbDist.map_val, mass_fTransform] at decoded
  exact decoded

end SystemAlgebra

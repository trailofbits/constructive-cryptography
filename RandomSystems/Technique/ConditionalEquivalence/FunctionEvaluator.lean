import RandomSystems.Game.FunctionEvaluator
import RandomSystems.Tactics.ProofAutomationAttributes
import RandomSystems.Technique.ConditionalEquivalence

set_option autoImplicit false

/-!
# Conditional equivalence for function evaluators

The visible system and the monotone condition use Lanzenberger's single
`System.DDG` game carrier.  The conditional-equivalence theorem below reduces
CR18, equation (4.38), from complete transcripts to an equality on the list of
queried inputs.
-/

noncomputable section

namespace RandomSystems

open Probability

universe u v w z

attribute [rs_side_condition] PDG.isProbDist_ofFunction
  PDG.hasDomain_ofFunction
attribute [rs_normalization] PDG.underlying_ofFunction

namespace PDG

variable {A : Type w} {X : Type u} {Y : Type v}

/-- A function game is initially false when each supported condition is false
on the empty query history. -/
lemma initiallyFalse_ofFunction (source : Distribution A)
    (function : A → X → Y) (condition : A → System.MC X)
    (initiallyFalse : ∀ value ∈ source.support,
      (condition value).1 [] = false) :
    (PDG.ofFunction source function condition).InitiallyFalse := by
  apply PDG.initiallyFalse_fTransform
  intro value supported
  exact initiallyFalse value supported

end PDG

namespace ConditionalEquivalence

variable {A : Type w} {B : Type z} {X : Type u} {Y : Type v}

/-- CR18, Definition 4.19 (printed p. 108), says “we say that S is
conditionally equivalent to T.”  Its equation (4.38) reduces to query-list
masses: a factorization for every assignment supplies the consistent case,
while inconsistent repeated queries have zero mass on both sides. -/
lemma ofFunction_of_mass_eq
    (source : Distribution A) (targetSource : Distribution B)
    (function : A → X → Y) (targetFunction : B → X → Y)
    (condition : A → System.MC X)
    (initiallyFalse : ∀ value ∈ source.support,
      (condition value).1 [] = false)
    (targetProbability : targetSource.isProbDist)
    (mass_eq : ∀ (queries : List X) (answers : X → Y),
      source.mass (fun value =>
          (∀ query ∈ queries,
              function value query = answers query) ∧
            (condition value).1 queries = false) =
        targetSource.mass (fun value =>
          ∀ query ∈ queries,
            targetFunction value query = answers query) *
          source.mass (fun value =>
            (condition value).1 queries = false)) :
    PDG.ofFunction source function condition |≡
      Distribution.fTransform
        (fun value => System.functionEvaluator (targetFunction value))
        targetSource := by
  refine ⟨PDG.initiallyFalse_ofFunction source function condition
    initiallyFalse, ?_⟩
  intro transcript nonempty _ _
  let queries := transcript.map Prod.fst
  have queriesNonempty : queries ≠ [] := by
    intro empty
    exact nonempty (List.map_eq_nil_iff.mp empty)
  unfold massYAfalse massAfalse massDom PDS.transcriptSystemFactor
  rw [PDG.ofFunction, Distribution.mass_fTransform,
    Distribution.mass_fTransform, Distribution.mass_fTransform,
    Distribution.mass_fTransform]
  simp only [System.DDG.ofFunction, System.dom_functionEvaluator,
    Set.mem_ofPred_eq]
  have targetDomain :
      targetSource.mass (fun _ => queries ≠ []) = 1 := by
    rw [Distribution.mass_congr targetSource
      (Q := fun _ => True) (fun _ => iff_true_intro queriesNonempty),
      Distribution.mass_true, targetProbability.weight_eq]
  have gameDomain :
      source.mass (fun value =>
          queries ≠ [] ∧ (condition value).1 queries = false) =
        source.mass (fun value =>
          (condition value).1 queries = false) :=
    Distribution.mass_congr source fun _ => and_iff_right queriesNonempty
  rw [targetDomain, gameDomain, mul_one]
  have realConsistentMass :
      source.mass (fun value =>
          System.SystemConsistent
              (System.functionEvaluator (function value)) transcript ∧
            (condition value).1 queries = false) =
        source.mass (fun value =>
          (∀ entry ∈ transcript,
              function value entry.1 = entry.2) ∧
            (condition value).1 queries = false) :=
    Distribution.mass_congr source fun value => and_congr
      (System.systemConsistent_functionEvaluator_iff
        (function value) transcript)
      Iff.rfl
  have targetConsistentMass :
      targetSource.mass (fun value =>
          System.SystemConsistent
            (System.functionEvaluator (targetFunction value)) transcript) =
        targetSource.mass (fun value =>
          ∀ entry ∈ transcript,
            targetFunction value entry.1 = entry.2) :=
    Distribution.mass_congr targetSource fun value =>
      System.systemConsistent_functionEvaluator_iff
        (targetFunction value) transcript
  rw [realConsistentMass, targetConsistentMass]
  by_cases realizable : ∃ answers : X → Y,
      ∀ entry ∈ transcript, answers entry.1 = entry.2
  · obtain ⟨answers, answersMatch⟩ := realizable
    have answerEvent (candidate : X → Y) :
        (∀ entry ∈ transcript, candidate entry.1 = entry.2) ↔
          ∀ query ∈ queries, candidate query = answers query := by
      constructor
      · intro equal query member
        obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
        exact (equal entry entryMember).trans
          (answersMatch entry entryMember).symm
      · intro equal entry entryMember
        exact (equal entry.1
          (List.mem_map.mpr ⟨entry, entryMember, rfl⟩)).trans
            (answersMatch entry entryMember)
    rw [Distribution.mass_congr source (fun value => and_congr
      (answerEvent (function value)) Iff.rfl),
      Distribution.mass_congr targetSource
        (fun value => answerEvent (targetFunction value))]
    exact mass_eq queries answers
  · have targetZero :
        targetSource.mass (fun value =>
          ∀ entry ∈ transcript,
            targetFunction value entry.1 = entry.2) = 0 :=
      Distribution.mass_eq_zero_of_forall_not targetSource
        fun value equal => realizable ⟨targetFunction value, equal⟩
    have realZero :
        source.mass (fun value =>
          (∀ entry ∈ transcript,
              function value entry.1 = entry.2) ∧
            (condition value).1 queries = false) = 0 :=
      Distribution.mass_eq_zero_of_forall_not source
        fun value equal => realizable ⟨function value, equal.1⟩
    rw [realZero, targetZero, zero_mul]

end ConditionalEquivalence

end RandomSystems

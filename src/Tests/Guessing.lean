module

public import RandomSystems.Typed.Solver
public import RandomSystems.Typed.Guessing
public import Commons.Definitions.Encryption
public import Commons.Schemes.MAC.NMAC
public import Tests.MixtureObservation

/-!
# Hidden-bit guessing clients

The two-world identity applies to the left/right encryption pair and the NMAC/URF
pair. Equal worlds give success one half. A one-query observer of `fixedBit b` succeeds
with probability one; swapping the worlds makes its success zero.
-/

@[expose] public section

namespace Tests.Guessing

open SystemAlgebra Commons

/-- A joint solver's own realization supplies the operational guessing experiment. -/
example {A : Interface} (s : TypedSolver A) (R : Bool → TypedSystem A) :
    ∃ P : A.inputDomain.Distinguisher,
      s.decision.guessingProbability (R false) (R true) =
        (P.guessingLaw (fun b => (R b).1) (fun b => (R b).2)).1.mass
          (fun bg => bg.2 = bg.1) ∧
      ∀ G : TypedGame A, s.winProbability G = P.winProbability G.1.1 := by
  obtain ⟨P, realizes, wins⟩ := s.exists_realization
  exact ⟨P, s.decision.guessingProbability_eq_mass P realizes R, wins⟩

/-- Equal worlds leave every compatible solver at the uniform-guessing baseline. -/
example {A : Interface} (s : TypedSolver A) (R : TypedSystem A) :
    s.decision.guessingProbability R R = 1 / 2 := by
  unfold TypedDistinguisher.guessingProbability
  ring

/-- Correct world identification has guessing probability one; swapping worlds gives zero. -/
example
    -- `s` always decides `false` on `R₀` and `true` on `R₁`.
    {A : Interface} (s : TypedSolver A) (R₀ R₁ : TypedSystem A)
    (zero : s.decision.1 R₀ = 0) (one : s.decision.1 R₁ = 1) :
    s.decision.guessingProbability R₀ R₁ = 1 ∧ s.decision.guessingProbability R₁ R₀ = 0 := by
  constructor <;> norm_num only [TypedDistinguisher.guessingProbability, zero, one]

/-- The guessing identity applies to the left/right encryption system pair. -/
example
    -- `scheme` has finite keys, messages and ciphertexts; `q` bounds left/right queries.
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C) (q : ℕ)
    (s : TypedSolver (LeftRight M C q)) :
    let worlds := Encryption.LORCPA.systems scheme q
    |s.decision.1 worlds.1 - s.decision.1 worlds.2| =
      2 * |s.decision.guessingProbability worlds.1 worlds.2 - 1 / 2| := by
  exact s.decision.abs_sub_eq_two_mul_abs_guessingProbability_sub_half _ _

/-- The guessing identity applies to the NMAC/URF comparison. -/
example
    -- `f` compresses blocks `B` into chaining values `C`; `pad` and `blocks` encode messages `M`.
    {B C M : Type} [Fintype C] [Nonempty C] [Fintype M]
    (f : C → B → C) (pad : C ↪ B) (blocks : M → List B) (q : ℕ)
    (s : TypedSolver (Evaluation M C q)) :
    let R := NMAC.Real f pad blocks (q := q)
    let S := URF (Evaluation M C q)
    |s.decision.1 R - s.decision.1 S| = 2 * |s.decision.guessingProbability R S - 1 / 2| := by
  exact s.decision.abs_sub_eq_two_mul_abs_guessingProbability_sub_half _ _

namespace Operational

open SystemAlgebra SystemAlgebra.Tests SystemAlgebra.Tests.MixtureObservation
open Probability Distribution

noncomputable section

/-- The one-query transcript whose reply is `true`. -/
def trueTranscript : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i)) :=
  [(⟨(), ()⟩, ⟨(), true⟩)]

/-- Ask the one-query environment and output its reply bit. -/
def observer : bitInterface.inputDomain.Distinguisher :=
  ProbDist.single ⟨envProbe bitQuery (fun t => t.1.zip t.2 = trueTranscript),
    envProbe_isDDD bitQuery_bounded,
    Domain.envProbe_decisionCompatible bitQuery_compatible _⟩

/-- The true-reply transcript follows `bitQuery` and completes its one query. -/
lemma trueTranscript_good : Good bitQuery.1 1 trueTranscript := by
  constructor
  · apply (FollowsStrategy.snoc_iff (h := [])).mpr
    refine ⟨FollowsStrategy.nil, ?_⟩
    simp only [bitQuery, DDE.ofQueries, List.map_nil, fixedQueries, List.length_nil,
      List.getElem?_cons_zero, Part.coe_some, Part.mem_some_iff]
  · exact Or.inl rfl

/-- The true-decision probability on `fixedBit b` is one for `b = true` and zero otherwise. -/
lemma observer_probability (b : Bool) :
    observer.probability (fixedBit b).1 = if b then 1 else 0 := by
  simp only [observer, ProbDist.single, Domain.Distinguisher.probability,
    Finsupp.sum_single_index, zero_mul, one_mul]
  rw [RandomSystem.decisionProbability_envProbe bitQuery_bounded _ (fixedBit b).2]
  have zip_projections (h : List ((Σ i, bitInterface.X i) × (Σ i, bitInterface.Y i))) :
      (h.map Prod.fst).zip (h.map Prod.snd) = h := (List.zip_of_prod rfl rfl).symm
  simp only [zip_projections]
  rw [mass_singleton, RandomSystem.sLaw_apply, ite_eq_left trueTranscript_good]
  cases b <;> norm_num [fixedBit, TypedSystem.ofFunction_mass, bitInterface, trueTranscript]

/-- Guessing the returned hidden bit succeeds with probability one. -/
lemma guessing_correct :
    (observer.guessingLaw (fun b => (fixedBit b).1) (fun b => (fixedBit b).2)).1.mass
      (fun bg => bg.2 = bg.1) = 1 := by
  rw [Domain.Distinguisher.guessingLaw_success, observer_probability, observer_probability]
  norm_num

/-- Swapping the worlds makes the same observer always guess incorrectly. -/
lemma guessing_swapped :
    (observer.guessingLaw (fun b => (fixedBit (!b)).1) (fun b => (fixedBit (!b)).2)).1.mass
      (fun bg => bg.2 = bg.1) = 0 := by
  rw [Domain.Distinguisher.guessingLaw_success, observer_probability, observer_probability]
  norm_num

/-- The operational observer's typed decision view. -/
def observerBehavior : TypedDistinguisher bitInterface := observer.behavior

/-- The operational law realizes the typed guessing score. -/
lemma observerBehavior_guessingProbability :
    observerBehavior.guessingProbability (fixedBit false) (fixedBit true) = 1 := by
  rw [TypedDistinguisher.guessingProbability_eq_mass observerBehavior observer
    (fun _ => rfl) fixedBit]
  exact guessing_correct

/-- Reading the hidden bit distinguishes the two fixed-bit systems with advantage one. -/
example : observerBehavior.advantage (fixedBit false) (fixedBit true) = 1 := by
  rw [TypedDistinguisher.advantage_eq_two_mul_abs_guessingProbability_sub_half,
    observerBehavior_guessingProbability]
  norm_num

#print axioms guessing_correct
#print axioms guessing_swapped

end

end Operational

#print axioms Domain.Distinguisher.decisionLaw_apply
#print axioms Domain.Distinguisher.guessingLaw_success
#print axioms TypedDistinguisher.guessingProbability_eq_mass
#print axioms TypedDistinguisher.advantage_eq_two_mul_abs_guessingProbability_sub_half
#print axioms TypedDistinguisher.abs_sub_eq_two_mul_abs_guessingProbability_sub_half
#print axioms TypedDistinguisher.guessingProbability_absorb

end Tests.Guessing

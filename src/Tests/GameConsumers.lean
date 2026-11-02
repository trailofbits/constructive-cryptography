module

public import Examples.Games
public import RandomSystems.Typed.Guessing
public import Examples.PRGLengthExtension

/-!
# The joint solver in game and distinction proofs

Serial absorption holds for any performance space of `GameAction`, checked at the vector
performance `ℕ × ℕ`. The decision projection of the joint solver feeds the PRG
length-extension proof; both views feed the AE collision-game proof. Absorbing the actual
reduction converters keeps these views tied to the same interaction. The transcript metric
ranges over all compatible stopping decision behaviors.
-/

@[expose] public section

namespace GameConsumerTests

open CategoryTheory ConstructiveCryptography Probability SystemAlgebra
open SystemAlgebra.Interface Commons Examples.PRGLengthExtension
open scoped SystemAlgebra NNReal

-- Serial absorption `W(α ≫ β) = (Wα)β` with vector performance, without real arithmetic.
example {C : Type} [Category C] {Game : C → Type} [Games C Game (ℕ × ℕ)]
    [GameAction C Game (ℕ × ℕ)] {A B D : C} (W : Game A → ℕ × ℕ)
    (α : A ⟶ B) (β : B ⟶ D) :
    Games.absorb (H := Game D) W (α ≫ β) =
      Games.absorb (Games.absorb (H := Game B) W α) β :=
  Games.absorb_comp W α β

-- Decision projection commutes with absorption, `(sα).decision = s.decision α`, so a supplied
-- closure proof for `α` keeps an admitted solver's decision admitted after absorbing `α`.
example
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    {A B : Interface} (s : TypedSolver A) (α : A ⟶ B)
    (closed : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) α)
    (hs : s.decision ∈ AdmissibleDistinguishers.admissible (D := TypedDistinguisher) A) :
    (TypedSolver.absorb s α).decision ∈
      AdmissibleDistinguishers.admissible (D := TypedDistinguisher) B := by
  rw [TypedSolver.decision_absorb]
  exact closed s.decision hs

-- Every decision behavior is the decision view of a joint solver.
example {A : Interface} (d : TypedDistinguisher A) :
    ∃ s : TypedSolver A, s.decision = d :=
  Domain.SolverBehavior.decision_surjective A.domain A.bound A.length_le d

/-- The PRG reduction bounds the extended generator by the two transformed solvers'
advantages: `Adv_s(H G) ≤ Adv_{s𝓡₁}(G) + Adv_{s𝓡₂}(G)`. -/
lemma prg_joint {S : Type} [Fintype S] [Nonempty S] (G : S → S × S)
    (q : Evaluation.Port → ℕ) (s : TypedSolver (Evaluation.perPort Unit (S × S × S) q)) :
    s.decision.advantage (PRGReal.perPort (H G) (budget := q))
        (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤
      (TypedSolver.absorb s (𝓡₁.perPort G)).decision.advantage
          (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) +
      (TypedSolver.absorb s (𝓡₂.perPort S)).decision.advantage
          (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) := by
  let : ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher :=
    ConstructiveCryptography.AdmissibleDistinguishers.all
  -- Under the local `all`, both reductions preserve admission. Use each transformed solver's
  -- advantage as its bound. Projection commutes with both reductions, so
  -- `prg_length_extension` has this conclusion.
  exact prg_length_extension G
    (fun D => D.advantage (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]))
    (fun _ _ => le_rfl) (AdmissibleDistinguishers.all_closedUnder _)
    (AdmissibleDistinguishers.all_closedUnder _) s.decision (Set.mem_univ _)

/-- The PRG reduction preserves the hidden-bit experiment for the same joint solver. -/
example {S : Type} [Fintype S] [Nonempty S] (G : S → S × S)
    (q : Evaluation.Port → ℕ) (s : TypedSolver (Evaluation.perPort Unit (S × S × S) q)) :
    let q' := 𝓡₁.insideBudget G q
    let R := PRGReal.perPort G (budget := q')
    let U := MemorylessSource.perPort (S × S) 𝒰[S × S] (budget := q')
    (s.absorb (𝓡₁.perPort G)).decision.guessingProbability R U =
      s.decision.guessingProbability (𝓡₁.perPort G • R) (𝓡₁.perPort G • U) := by
  dsimp only
  rw [TypedSolver.decision_absorb]
  exact s.decision.guessingProbability_absorb _ _ _

/-- The AE game bound controls the same joint solver's decision view by `q_enc² / |M|`. -/
lemma ae_joint {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)
    (s : TypedSolver (AE.perPort M C q)) :
    |s.decision.1 (AuthenticatedEncryption.Hybrid scheme q) -
      s.decision.1 (AE.Ideal.perPort M C (budget := q) •
        Encryption.system.perPort scheme : TypedSystem (AE.perPort M C q))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M :=
  GameExamples.hybrid_ideal_advantage_le scheme q ⟨s, rfl⟩

-- Transcript distance is the supremum over all compatible stopping decision behaviors.
example {A : Interface} (R S : TypedSystem A) :
    Δ R S = ⨆ D : TypedDistinguisher A, D.advantage R S :=
  RandomSystem.transcriptDistance_eq_iSup_behavior R S

#print axioms Domain.SolverBehavior.decision
#print axioms Domain.SolverBehavior.decision_surjective
#print axioms Domain.SolverBehavior.decision_absorb
#print axioms prg_joint
#print axioms ae_joint

end GameConsumerTests

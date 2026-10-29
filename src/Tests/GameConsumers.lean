import Examples.Games
import Examples.PRGLengthExtension

/-!
# The joint solver in game and distinction proofs

Serial absorption holds for any performance space of `GameAction`, checked at the vector
performance `ℕ × ℕ`. The decision projection of the joint solver feeds the PRG
length-extension proof; both views feed the AE collision-game proof. Absorbing the actual
reduction converters keeps these views tied to the same interaction. The transcript metric
still ranges over all compatible stopping decision behaviors.
-/

namespace GameConsumerTests

open CategoryTheory ConstructiveCryptography Probability SystemAlgebra
open SystemAlgebra.Interface Commons Examples.PRGLengthExtension
open scoped SystemAlgebra NNReal

/-- One distinguisher's paired evaluations on the systems and games of interface `A`. -/
abbrev Solver (A : Interface) :=
  Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le

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
    {A B : Interface} (s : Solver A) (α : A ⟶ B)
    (closed : AdmissibleDistinguishers.ClosedUnder
      (Phi := TypedSystem) (D := TypedDistinguisher) α)
    (hs : s.decision ∈ AdmissibleDistinguishers.admissible (D := TypedDistinguisher) A) :
    (s.absorb B.nonempty_prefix A.nonempty_prefix α).decision ∈
      AdmissibleDistinguishers.admissible (D := TypedDistinguisher) B := by
  rw [Domain.SolverBehavior.decision_absorb]
  exact closed s.decision hs

-- Every existing decision behavior remains available through a joint realization.
example {A : Interface} (d : (TypedDistinguisher A)) :
    ∃ s : Solver A, s.decision = d :=
  Domain.SolverBehavior.decision_surjective A.domain A.bound A.length_le d

/-- The PRG reduction bounds the extended generator by the two transformed solvers' actual
advantages: `Adv_s(H G) ≤ Adv_{s𝓡₁}(G) + Adv_{s𝓡₂}(G)`. -/
lemma prg_joint {S : Type} [Fintype S] [Nonempty S] (G : S → S × S)
    (q : Evaluation.Port → ℕ) (s : Solver (Evaluation.perPort Unit (S × S × S) q)) :
    s.decision.advantage (PRGReal.perPort (H G) (budget := q))
        (MemorylessSource.perPort (S × S × S) 𝒰[S × S × S]) ≤
      (s.absorb (Evaluation.perPort Unit (S × S) (𝓡₁.insideBudget G q)).nonempty_prefix
        (Evaluation.perPort Unit (S × S × S) q).nonempty_prefix (𝓡₁.perPort G)).decision.advantage
          (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) +
      (s.absorb (Evaluation.perPort Unit (S × S) (𝓡₂.insideBudget S q)).nonempty_prefix
        (Evaluation.perPort Unit (S × S × S) q).nonempty_prefix (𝓡₂.perPort S)).decision.advantage
          (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]) := by
  let : ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher :=
    ConstructiveCryptography.AdmissibleDistinguishers.all
  -- Under the local `all`, both reductions preserve admission. Use each transformed solver's
  -- actual advantage as its bound; projection commutes with both reductions, so the existing
  -- PRG theorem has exactly this conclusion.
  exact prg_length_extension G
    (fun D => D.advantage (PRGReal.perPort G) (MemorylessSource.perPort (S × S) 𝒰[S × S]))
    (fun _ _ => le_rfl) (AdmissibleDistinguishers.all_closedUnder _)
    (AdmissibleDistinguishers.all_closedUnder _) s.decision (Set.mem_univ _)

/-- The AE game bound controls the same joint solver's decision view by `q_enc² / |M|`. -/
lemma ae_joint {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)
    (s : Solver (AE.perPort M C q)) :
    |s.decision.1 (AuthenticatedEncryption.Hybrid scheme q) -
      s.decision.1 (AE.Ideal.perPort M C (budget := q) •
        Encryption.Real.perPort scheme : TypedSystem (AE.perPort M C q))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M :=
  GameExamples.hybrid_ideal_advantage_le scheme q ⟨s, rfl⟩

-- Introducing the joint view does not narrow the class characterizing transcript distance.
example {A : Interface} (R S : TypedSystem A) :
    Δ R S = ⨆ D : (TypedDistinguisher A), D.advantage R S :=
  RandomSystem.transcriptDistance_eq_iSup_behavior R S

#print axioms Domain.SolverBehavior.decision
#print axioms Domain.SolverBehavior.decision_surjective
#print axioms Domain.SolverBehavior.decision_absorb
#print axioms prg_joint
#print axioms ae_joint

end GameConsumerTests

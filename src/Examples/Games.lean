import ConstructiveCryptography.InterfaceGame
import Examples.AuthenticatedEncryption.Collision
import RandomSystems.Game.DiscreteMBO

/-!
# Games

The games layer at work. In every compatible solver class, a game argument goes through a
construction: a solver's advantage between a construction on the visible resource of a game and
on a resource conditionally equivalent to the game is at most its winning probability for the
game with the construction attached (`advantage_attach_le_win`). Hardness of a game carries over
to the game with a converter attached, the reduction absorbed into the solver
(`win_attach_le`), through two converters in turn (`win_attach_comp_le`), and through a lossy
reduction that loses a factor `k`, as a reduction guessing one of `k` sessions does
(`win_le_of_reduction`).

On interfaces, the collision game of authenticated encryption is a game: its systems are the
hybrid oracle with the MBO the collision so far (`collision`). Its visible resource is the
hybrid, it is conditionally equivalent to the ideal system, and every solver wins it with
probability at most `q_e² / |M|`. Every solver's advantage between the hybrid and the ideal is
then at most `q_e² / |M|` (`hybrid_ideal_advantage_le`), also inside any construction
(`attach_hybrid_ideal_advantage_le`).

## Main definitions

* `collision`: the collision game on the authenticated-encryption interface

## Main results

* `advantage_attach_le_win`, `advantage_attach_le`: a game hop inside a construction
* `win_attach_le`, `win_attach_comp_le`, `win_le_of_reduction`: hardness through reductions
* `collision_visible`, `collision_conditionallyEquivalent`, `collision_win_le`: the collision
  game
* `hybrid_ideal_advantage_le`, `attach_hybrid_ideal_advantage_le`: the collision step through
  the games layer
-/

universe u v w x

namespace GameExamples

open CategoryTheory ConstructiveCryptography

section Abstract

open GameTheory CompatibleSolverClass

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [GameTheory C Phi Game] [CompatibleSolverClass C Phi Game]

/-- **A game hop inside a construction**: for a game conditionally equivalent to a resource, a
solver's advantage between a construction on the visible resource of the game and on the
resource is at most its winning probability for the game with the construction attached. -/
theorem advantage_attach_le_win {A B : C} (α : A ⟶ B) {G : Game B} {T : Phi B}
    (hc : ConditionallyEquivalent G T) {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    |s.1 (visible (α • G)) - s.1 (α • T)| ≤ s.2 (α • G) := by
  rw [smul_eq_attachGame, visible_attachGame]
  exact advantage_le_win hc (absorb_mem α hs)

/-- **Hardness through a reduction**: if no solver wins a game with probability more than `ε`,
no solver wins it with a converter attached with probability more than `ε`. -/
theorem win_attach_le {A B : C} (α : A ⟶ B) {G : Game B} {ε : ℝ}
    (hG : ∀ s ∈ solvers B, s.2 G ≤ ε) {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    s.2 (α • G) ≤ ε :=
  hG _ (absorb_mem α hs)

/-- **A game hop inside a construction, for a hard game**: the advantage is at most the bound on
winning the game. -/
theorem advantage_attach_le {A B : C} (α : A ⟶ B) {G : Game B} {T : Phi B}
    (hc : ConditionallyEquivalent G T) {ε : ℝ} (hG : ∀ s ∈ solvers B, s.2 G ≤ ε)
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    |s.1 (α • visible G) - s.1 (α • T)| ≤ ε :=
  (advantage_le_win hc (absorb_mem α hs)).trans (hG _ (absorb_mem α hs))

/-- **Hardness through two reductions**: the serial composition of two converters is absorbed
one converter after the other. -/
theorem win_attach_comp_le {A B D : C} (α : A ⟶ B) (β : B ⟶ D) {G : Game D} {ε : ℝ}
    (hG : ∀ s ∈ solvers D, s.2 G ≤ ε) {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    s.2 ((α ≫ β) • G) ≤ ε := by
  have h := hG _ (absorb_mem β (absorb_mem α hs))
  rw [← absorb_comp] at h
  exact h

/-- **Hardness through a lossy reduction**: if every solver wins `G₁` with at most `k` times its
probability of winning `G₂` with a converter attached, and no solver wins `G₂` with probability
more than `ε`, no solver wins `G₁` with probability more than `k * ε`. -/
theorem win_le_of_reduction {A B : C} (α : A ⟶ B) {G₁ : Game A} {G₂ : Game B} {k ε : ℝ}
    (hk : 0 ≤ k) (hred : ∀ s ∈ solvers A, s.2 G₁ ≤ k * s.2 (α • G₂))
    (hG : ∀ s ∈ solvers B, s.2 G₂ ≤ ε) {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    s.2 G₁ ≤ k * ε :=
  (hred s hs).trans (mul_le_mul_of_nonneg_left (win_attach_le α hG hs) hk)

end Abstract

section Collision

open SystemAlgebra Commons AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- The hybrid replies at the queried interface. -/
theorem collisionGame_repliesAtQueriedInterface :
    (PDS.behavior (collisionGame scheme q).underlying
      (PDG.underlying_probability (collisionGame_isProbDist scheme q))).RepliesAtQueriedInterface :=
  hybrid_visible scheme q ▸ (Hybrid scheme q).2

/-- **The collision game** on the authenticated-encryption interface: the hybrid oracle, with
the MBO the collision between the original messages so far and the outer replacement
messages. -/
noncomputable def collision : Interface.Game (AE.perPort M C q) :=
  ⟨⟨(collisionGame scheme q).behavior (collisionGame_isProbDist scheme q),
      PDG.repliesAtQueriedInterface_behavior (collisionGame_isProbDist scheme q)
        (collisionGame_repliesAtQueriedInterface scheme q)⟩,
    PDG.monotoneMBO_behavior (collisionGame_isProbDist scheme q)⟩

/-- The visible resource of the collision game is the hybrid. -/
theorem collision_visible : GameTheory.visible (collision scheme q) = Hybrid scheme q := by
  apply Subtype.ext
  change ((collisionGame scheme q).behavior (collisionGame_isProbDist scheme q)).visible = _
  exact (PDG.visible_behavior _).trans (hybrid_visible scheme q).symm

/-- The collision game is conditionally equivalent to the ideal system. -/
theorem collision_conditionallyEquivalent :
    CompatibleSolverClass.ConditionallyEquivalent (collision scheme q)
      (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        Interface.Resource (AE.perPort M C q)) := by
  change ((collisionGame scheme q).behavior
      (collisionGame_isProbDist scheme q)).ConditionallyEquivalent
    (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
      Interface.Resource (AE.perPort M C q)).1
  exact collisionGame_conditionallyEquivalent scheme q

/-- **Every solver wins the collision game with probability at most `q_e² / |M|`.** -/
theorem collision_win_le {s} (hs : s ∈ CompatibleSolverClass.solvers (AE.perPort M C q)) :
    s.2 (collision scheme q) ≤ (q .enc : ℝ) ^ 2 / Fintype.card M := by
  refine Interface.win_le (fun P => ?_) hs
  change P.winProbability
    ((collisionGame scheme q).behavior (collisionGame_isProbDist scheme q)) ≤ _
  exact P.winProbability_le_of_unsetProbability
    (PDG.repliesAtQueriedInterface_behavior _ (collisionGame_repliesAtQueriedInterface scheme q))
    (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
      Interface.Resource (AE.perPort M C q)).2 (PDG.monotoneMBO_behavior _)
    (collisionGame_conditionallyEquivalent scheme q)
    (PDG.one_sub_le_unsetProbability_behavior _ (AE.perPort M C q).nonempty_prefix
      (collisionGame_badProbability_le scheme q))

/-- **The collision step through the games layer**: every solver's advantage between the hybrid
and the ideal is at most `q_e² / |M|`. -/
theorem hybrid_ideal_advantage_le {s} (hs : s ∈ CompatibleSolverClass.solvers (AE.perPort M C q)) :
    |s.1 (Hybrid scheme q) - s.1 (AE.Ideal.perPort M C (budget := q) •
        Encryption.Real.perPort scheme : Interface.Resource (AE.perPort M C q))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M := by
  rw [← collision_visible]
  exact (CompatibleSolverClass.advantage_le_win (collision_conditionallyEquivalent scheme q)
    hs).trans (collision_win_le scheme q hs)

/-- **The collision step inside any construction**: every solver's advantage between a
construction on the hybrid and on the ideal is at most `q_e² / |M|`. -/
theorem attach_hybrid_ideal_advantage_le {B : Interface} (α : B ⟶ AE.perPort M C q) {s}
    (hs : s ∈ CompatibleSolverClass.solvers B) :
    |s.1 (α • Hybrid scheme q) - s.1 (α • (AE.Ideal.perPort M C (budget := q) •
        Encryption.Real.perPort scheme : Interface.Resource (AE.perPort M C q)))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M := by
  rw [← collision_visible]
  exact advantage_attach_le α (collision_conditionallyEquivalent scheme q)
    (fun _ hs => collision_win_le scheme q hs) hs

end Collision

end GameExamples

import ConstructiveCryptography.InterfaceGame
import Examples.AuthenticatedEncryption.Collision
import RandomSystems.Game.DiscreteMBO

/-!
# Games

The games layer at work, with real performance: winning probabilities in `Games C Game ℝ`.
For games with a converter action (`GameAction C Game ℝ`), hardness of a game carries over
to the game with a converter attached, the reduction absorbed into the winner
(`win_attach_le`), through two converters in turn (`win_attach_comp_le`), and through a lossy
reduction that loses a factor `k`, as a reduction guessing one of `k` sessions does
(`win_le_of_reduction`). With `DistinctionGameAction`, a game argument goes through a
construction: a solver's advantage between a construction on the visible resource of a game
and on a resource conditionally equivalent to the game is at most its winning probability for
the game with the construction attached (`advantage_attach_le_win`).

On interfaces, the collision game of authenticated encryption is the game the collision
discrete game presents (`collision`): the hybrid oracle with the MBO the collision so far. Its
visible typed system is the hybrid, it is conditionally equivalent to the ideal system, and every
winner wins it with probability at most `q_e² / |M|`. Every solver's advantage between the
hybrid and the ideal is then at most `q_e² / |M|` (`hybrid_ideal_advantage_le`), also inside any
construction (`attach_hybrid_ideal_advantage_le`).

## Main definitions

* `collision`: the collision game on the authenticated-encryption interface

## Main results

* `win_attach_le`, `win_attach_comp_le`, `win_le_of_reduction`: hardness through reductions
* `advantage_attach_le_win`, `advantage_attach_le`: a game hop inside a construction
* `collision_visible`, `collision_conditionallyEquivalent`, `collision_win_le`: the collision
  game
* `hybrid_ideal_advantage_le`, `attach_hybrid_ideal_advantage_le`: the collision step through
  the games layer
-/

universe u v w x

namespace GameExamples

open CategoryTheory ConstructiveCryptography

section Abstract

section Reductions

open Games

variable {C : Type u} [Category.{v} C] {Game : C → Type x}
  [Games C Game ℝ] [GameAction C Game ℝ]

/-- **Hardness through a reduction**: if no winner wins a game with probability more than `ε`,
no winner wins it with a converter attached with probability more than `ε`. -/
theorem win_attach_le {A B : C} (α : A ⟶ B) {G : Game B} {ε : ℝ}
    (hG : ∀ w ∈ winners B, w G ≤ ε) {w : Game A → ℝ} (hw : w ∈ winners A) : w (α • G) ≤ ε :=
  -- `w` with the reduction `α` absorbed is a winner on `B` (axiom `closed_attach`), and it
  -- wins `G` as `w` wins `α • G`:
  --
  --   ┌────────────────┐
  --   │ ┌───┐ ── ┌───┐ │ ── ┌───┐
  --   │ │ w │    │ α │ │    │ G │
  --   │ └───┘ ── └───┘ │ ── └───┘
  --   └────────────────┘
  hG _ (absorb_mem α hw)

/-- **Hardness through two reductions**: the serial composition of two converters is absorbed
one converter after the other. -/
theorem win_attach_comp_le {A B D : C} (α : A ⟶ B) (β : B ⟶ D) {G : Game D} {ε : ℝ}
    (hG : ∀ w ∈ winners D, w G ≤ ε) {w : Game A → ℝ} (hw : w ∈ winners A) :
    w ((α ≫ β) • G) ≤ ε := by
  -- Absorb `α` into `w`, then `β`: a winner on `D`, so it wins `G` with probability ≤ ε.
  --
  --   ┌─────────────────────────┐
  --   │ ┌───┐ ── ┌───┐ ── ┌───┐ │ ── ┌───┐
  --   │ │ w │    │ α │    │ β │ │    │ G │
  --   │ └───┘ ── └───┘ ── └───┘ │ ── └───┘
  --   └─────────────────────────┘
  have h := hG _ (absorb_mem β (absorb_mem α hw))
  -- Absorbing `α` then `β` is absorbing `α ≫ β` (`absorb_comp`, from `attachGame_serial`).
  rw [← absorb_comp] at h
  -- `w` with `α ≫ β` absorbed wins `G` as `w` wins `(α ≫ β) • G`, by definition.
  exact h

/-- **Hardness through a lossy reduction**: for `k ≥ 0`, if every winner wins `G₁` with at most
`k` times its probability of winning `G₂` with a converter attached, and no winner wins `G₂`
with probability more than `ε`, no winner wins `G₁` with probability more than `k * ε`. -/
theorem win_le_of_reduction {A B : C} (α : A ⟶ B) {G₁ : Game A} {G₂ : Game B} {k ε : ℝ}
    (hk : 0 ≤ k) (hred : ∀ w ∈ winners A, w G₁ ≤ k * w (α • G₂))
    (hG : ∀ w ∈ winners B, w G₂ ≤ ε) {w : Game A → ℝ} (hw : w ∈ winners A) :
    w G₁ ≤ k * ε :=
  -- The general reduction with `ρ W = Wα` and loss `p ↦ k p`, monotone as `k ≥ 0`:
  --
  --   w G₁ ≤ k · w (α • G₂) = k · (wα) G₂   (the lossy reduction `hred`; absorption, `rfl`)
  --        ≤ k · ε                         (`hG`, as `wα` is a winner by `absorb_mem`)
  Games.win_le_of_reduction (fun W => Games.absorb W α) (fun p => k * p)
    (fun _ _ h => mul_le_mul_of_nonneg_left h hk) (fun _ h => Games.absorb_mem α h)
    hred hG hw

end Reductions

section Distinction

open Games DistinctionGames

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [DistinctionGames C Phi Game] [GameAction C Game ℝ]
  [DistinctionGameAction C Phi Game]

/-- **A game hop inside a construction**: for a game conditionally equivalent to a resource, a
solver's advantage between a construction on the visible resource of the game and on the
resource is at most its winning probability for the game with the construction attached. -/
theorem advantage_attach_le_win {A B : C} (α : A ⟶ B) {G : Game B} {T : Phi B}
    (hc : ConditionallyEquivalent G T) {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    |s.1 (visible (α • G)) - s.1 (α • T)| ≤ s.2 (α • G) := by
  -- The visible resource of `α • G` is `α` attached to `G⁻` (axiom `visible_attachGame`).
  rw [smul_eq_attachGame, DistinctionGameAction.visible_attachGame]
  -- Absorb `α` into `s`: a solver on `B` (axiom `solvers_closed_attach`). Its advantage
  -- between `G⁻` and `T` is `s`'s advantage between `α G⁻` and `α T`, and is at most its
  -- winning probability for `G`, which is `s`'s for `α • G` (axiom `advantage_le_win`):
  --
  --   ┌───┐ ── ┌───┐ ── ┌────┐        ┌───┐ ── ┌───┐ ── ┌───┐
  --   │ s │    │ α │    │ G⁻ │   vs   │ s │    │ α │    │ T │
  --   └───┘ ── └───┘ ── └────┘        └───┘ ── └───┘ ── └───┘
  exact advantage_le_win hc (DistinctionGames.absorb_mem α hs)

/-- **A game hop inside a construction, for a hard game**: the advantage is at most the bound on
winning the game. -/
theorem advantage_attach_le {A B : C} (α : A ⟶ B) {G : Game B} {T : Phi B}
    (hc : ConditionallyEquivalent G T) {ε : ℝ} (hG : ∀ s ∈ solvers B, s.2 G ≤ ε)
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ solvers A) :
    |s.1 (α • visible G) - s.1 (α • T)| ≤ ε :=
  -- With `s'` the solver `s` with `α` absorbed, a solver on `B`:
  --
  --   |s(α G⁻) − s(α T)| = |s'(G⁻) − s'(T)|
  --                      ≤ s' wins G           (`advantage_le_win`, as `G |≡ T`)
  --                      ≤ ε                   (`hG`, as `s'` is a solver)
  (advantage_le_win hc (DistinctionGames.absorb_mem α hs)).trans
    (hG _ (DistinctionGames.absorb_mem α hs))

end Distinction

end Abstract

section Collision

open SystemAlgebra Commons AuthenticatedEncryption

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
  [DecidableEq C] [Nonempty M] (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ)

/-- **The collision game** on the authenticated-encryption interface: the game the collision
discrete game presents, the hybrid oracle with the MBO the collision between the original
messages so far and the outer replacement messages. -/
noncomputable def collision : TypedGame (AE.perPort M C q) :=
  TypedGame.ofPDG (collisionGame scheme q) (collisionGame_isProbDist scheme q)
    (hybrid_visible scheme q)

/-- The visible typed system of the collision game is the hybrid. -/
lemma collision_visible : DistinctionGames.visible (collision scheme q) = Hybrid scheme q :=
  TypedGame.visible_ofPDG _ _ _

/-- The collision game is conditionally equivalent to the ideal system. -/
lemma collision_conditionallyEquivalent :
    DistinctionGames.ConditionallyEquivalent (collision scheme q)
      (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
        TypedSystem (AE.perPort M C q)) :=
  collisionGame_conditionallyEquivalent scheme q

/-- **Every winner wins the collision game with probability at most `q_e² / |M|`.** -/
theorem collision_win_le {w} (hw : w ∈ Games.winners (AE.perPort M C q)) :
    w (collision scheme q) ≤ (q .enc : ℝ) ^ 2 / Fintype.card M := by
  -- It suffices to bound the winning probability of every probabilistic distinguisher `P`
  -- for the game's random system (`Interface.win_le`).
  refine Interface.win_le (fun P => ?_) hw
  -- The game's random system is the behavior of the collision discrete game.
  change P.winProbability
    ((collisionGame scheme q).behavior (collisionGame_isProbDist scheme q)) ≤ _
  -- The systems-level bound by the unset MBO: the game is conditionally equivalent to the
  -- ideal system, and on the queries of each transcript of the ideal its MBO stays unset with
  -- probability at least `1 - q_e² / |M|`. The arguments, in order: the game replies at the
  -- queried interface (its visible systems present the hybrid, which does); so does the ideal;
  -- the MBO once set stays set; the conditional equivalence; the collision bound on each
  -- admitted query sequence, turned into the bound on the unset MBO.
  exact P.winProbability_le_of_unsetProbability
    (PDG.repliesAtQueriedInterface_behavior _ (hybrid_visible scheme q ▸ (Hybrid scheme q).2))
    (AE.Ideal.perPort M C (budget := q) • Encryption.Real.perPort scheme :
      TypedSystem (AE.perPort M C q)).2 (PDG.monotoneMBO_behavior _)
    ((Interface.conditionallyEquivalent_ofPDG_iff _ _ (hybrid_visible scheme q) _).mp
      (collisionGame_conditionallyEquivalent scheme q))
    (PDG.one_sub_le_unsetProbability_behavior _ (AE.perPort M C q).nonempty_prefix
      (collisionGame_badProbability_le scheme q))

/-- **The collision step through the games layer**: every solver's advantage between the hybrid
and the ideal is at most `q_e² / |M|`. -/
theorem hybrid_ideal_advantage_le {s} (hs : s ∈ DistinctionGames.solvers (AE.perPort M C q)) :
    |s.1 (Hybrid scheme q) - s.1 (AE.Ideal.perPort M C (budget := q) •
        Encryption.Real.perPort scheme : TypedSystem (AE.perPort M C q))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M := by
  -- The hybrid is the visible typed system `G⁻` of the collision game `G`.
  rw [← collision_visible]
  -- With `Ideal` the ideal system `AE.Ideal.perPort M C • Encryption.Real.perPort scheme`:
  --
  --   ┌───┐ ── ┌────┐        ┌───┐ ── ┌───────┐
  --   │ s │    │ G⁻ │   vs   │ s │    │ Ideal │
  --   └───┘ ── └────┘        └───┘ ── └───────┘
  --
  --   |s(G⁻) − s(Ideal)| ≤ s wins G         (`advantage_le_win`, as `G |≡ Ideal`)
  --                      ≤ q_e² / |M|       (`collision_win_le`, `s` wins as a winner)
  exact (DistinctionGames.advantage_le_win (collision_conditionallyEquivalent scheme q)
    hs).trans (collision_win_le scheme q (DistinctionGames.solvers_winner hs))

/-- **The collision step inside any construction**: every solver's advantage between a
construction on the hybrid and on the ideal is at most `q_e² / |M|`. -/
theorem attach_hybrid_ideal_advantage_le {B : Interface} (α : B ⟶ AE.perPort M C q) {s}
    (hs : s ∈ DistinctionGames.solvers B) :
    |s.1 (α • Hybrid scheme q) - s.1 (α • (AE.Ideal.perPort M C (budget := q) •
        Encryption.Real.perPort scheme : TypedSystem (AE.perPort M C q)))| ≤
      (q .enc : ℝ) ^ 2 / Fintype.card M := by
  -- The hybrid is the visible typed system `G⁻` of the collision game `G`.
  rw [← collision_visible]
  -- The game hop inside the construction `α` (`advantage_attach_le`), with the bound on
  -- winning `G` by every solver on `AE.perPort M C q` (`collision_win_le`):
  --
  --   ┌───┐ ── ┌───┐ ── ┌────┐        ┌───┐ ── ┌───┐ ── ┌───────┐
  --   │ s │    │ α │    │ G⁻ │   vs   │ s │    │ α │    │ Ideal │
  --   └───┘ ── └───┘ ── └────┘        └───┘ ── └───┘ ── └───────┘
  exact advantage_attach_le α (collision_conditionallyEquivalent scheme q)
    (fun _ hs => collision_win_le scheme q (DistinctionGames.solvers_winner hs)) hs

end Collision

end GameExamples

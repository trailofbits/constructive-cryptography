import ConstructiveCryptography.InterfaceAlgebra
import ConstructiveCryptography.CryptographicAlgebra.Game
import RandomSystems.Game.MBOAttachment

/-!
# Games on interfaces

Interfaces are an instance of `Games`, the abstraction of CR18, §4.4.3, §4.5.1 and §4.7.2, and
of `DistinctionGames`, the abstraction of CR18, §§4.10–4.11; the instance is where these
abstractions meet random systems. Its games are MBO random systems, as CR18 instantiates games
(§3.7.1): a game on `A` is a resource on the interface of `A` with the MBO whose MBO, once set,
stays set (`RandomSystem.MonotoneMBO`). Winners and solvers are probabilistic distinguishers,
through their behaviors `Domain.SolverBehavior`: a winner does not see the MBO
(`DDE.blindMBO`).

For `Games`, the field `attachGame` is the attachment of the MBO-forwarding lift
`PDCBehavior.liftMBO`, and `winners` are the winning probabilities of the solver behaviors.
The axiom `attachGame_identity` is discharged by `PDCBehavior.liftMBO_id`, `attachGame_serial`
by `PDCBehavior.liftMBO_comp`, and `closed_attach` by `Domain.SolverBehavior.absorb`.

For `DistinctionGames`, the field `solvers` is the pairs of the solver behaviors, `visible` is the
visible system `RandomSystem.visible`, and `ConditionallyEquivalent` is
`RandomSystem.ConditionallyEquivalent`. The axiom `solvers_winner` holds by the definition of the
winners, `solvers_closed_attach` is discharged by `Domain.SolverBehavior.absorb`,
`visible_attachGame` by `RandomSystem.visible_attach_liftMBO`, and `advantage_le_win` by
`Domain.Distinguisher.advantage_le_winProbability`.

Conditional equivalence then bounds the distance of the visible resource of a game by the
probability that its MBO is set on fixed queries (CR18, Theorem 4.17), through
`RandomSystem.transcriptDistance_visible_le_of_unsetProbability`.

## Main definitions

* `Interface.withMBO A`: the interface of `A` with the MBO
* `Interface.Game A`: games on `A`
* `Interface.games`, `Interface.distinctionGames`: the instances

## Main results

* `Interface.win_le`: a bound on winning by every distinguisher bounds winning by every winner
* `Interface.dist_visible_le`: conditional equivalence bounds the distance of the visible
  resource
-/

namespace SystemAlgebra.Interface

open CategoryTheory ConstructiveCryptography

/-- The interface of `A` with the MBO: its replies carry the MBO. -/
abbrev withMBO (A : Interface) : Interface where
  I := A.I
  X := A.X
  Y := SystemAlgebra.withMBO A.Y
  domain := A.domain
  nonempty_prefix := A.nonempty_prefix
  bound := A.bound
  length_le := A.length_le

/-- **Games** on `A`: resources on the interface of `A` with the MBO whose MBO, once set,
stays set. -/
def Game (A : Interface) := {G : Resource A.withMBO // G.1.MonotoneMBO}

/-- The MBO-forwarding lift of a converter, between the interfaces with the MBO. -/
noncomputable def liftMBO {A B : Interface} (α : A ⟶ B) : A.withMBO ⟶ B.withMBO :=
  PDCBehavior.liftMBO α

/-- A converter attached to a game: its lift attached to the game's resource. -/
noncomputable def attachGame {A B : Interface} (α : A ⟶ B) (G : Game B) : Game A :=
  -- The lift runs `α` on the replies of `G` without their MBO and tags each outside reply
  -- with the MBO `a` of the latest reply of `G`:
  --
  --   ──x────▶ ┌───────────┐ ──u────▶ ┌───┐
  --            │ liftMBO α │          │ G │
  --   ◀─(y,a)─ └───────────┘ ◀─(v,a)─ └───┘
  --
  -- The result is again a game, its MBO once set stays set
  -- (`RandomSystem.MonotoneMBO.attach_liftMBO`).
  ⟨liftMBO α • G.1,
    G.2.attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.2⟩

/-- The visible resource of a game. -/
noncomputable def Game.visible {A : Interface} (G : Game A) : Resource A :=
  ⟨G.1.1.visible, G.1.2.visible⟩

/-- The winners on `A`: the winning probabilities of the solver behaviors on the input domain of
`A`. -/
def winners (A : Interface) : Set (Game A → ℝ) :=
  Set.range fun s : Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le =>
    fun G => s.1.2 ⟨G.1.1, G.1.2, G.2⟩

/-- The solvers on `A`: the solver behaviors on the input domain of `A`. -/
def solvers (A : Interface) : Set ((Resource A → ℝ) × (Game A → ℝ)) :=
  Set.range fun s : Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le =>
    (fun R => s.1.1 R, fun G => s.1.2 ⟨G.1.1, G.1.2, G.2⟩)

/-- **Interfaces are an instance of `Games`**: attachment is the attachment of the lift, and the
winners are the winning probabilities of the solver behaviors. -/
noncomputable instance games : Games Interface Game where
  -- Field `attachGame`: the systems-level attachment `PDCBehavior.attach` of the lift
  -- `PDCBehavior.liftMBO α` to the game's random system.
  attachGame := attachGame
  -- Axiom `attachGame_identity`, discharged by the systems-level theorems
  -- `PDCBehavior.liftMBO_id` (the lift of the identity PDC is the identity PDC) and
  -- `PDCBehavior.attach_id` (attaching the identity PDC leaves a random system unchanged,
  -- used here as `identity_attach`).
  attachGame_identity G := by
    -- Two games are equal when their resources are.
    apply Subtype.ext
    change liftMBO (𝟙 _) • G.1 = G.1
    -- The lift of the identity converter is the identity converter on `A.withMBO`.
    rw [show liftMBO (𝟙 _) = 𝟙 _ from PDCBehavior.liftMBO_id _]
    -- Attaching the identity converter leaves the game's resource unchanged.
    exact identity_attach G.1
  -- Axiom `attachGame_serial`, discharged by the systems-level theorems
  -- `PDCBehavior.liftMBO_comp` (the lift of `α ≫ β` is the composition of the lifts) and
  -- `PDCBehavior.attach_comp` (attaching a serial composition is nested attachment, used
  -- here as `comp_smul`).
  attachGame_serial α β G := by
    -- Two games are equal when their resources are.
    apply Subtype.ext
    change liftMBO (α ≫ β) • G.1 = liftMBO α • (liftMBO β • G.1)
    -- The lift is functorial: lift (α ≫ β) = lift α ≫ lift β.
    rw [show liftMBO (α ≫ β) = liftMBO α ≫ liftMBO β from PDCBehavior.liftMBO_comp α β]
    -- (lift α ≫ lift β) • G = lift α • (lift β • G): attach the inner converter first.
    exact comp_smul _ _ G.1
  -- Field `winners`: the winning probabilities of the systems-level solver behaviors
  -- `Domain.SolverBehavior` on the input domain.
  winners := winners
  -- Axiom `closed_attach`, discharged by the systems-level construction
  -- `Domain.SolverBehavior.absorb` (a solver behavior with a PDC absorbed).
  closed_attach {A B} α := by
    -- The winner on `A` is the winning probability of a solver behavior `s`.
    rintro _ ⟨s, rfl⟩
    -- Absorb `α` into `s`: a solver behavior on `B`, which wins `G` as `s` wins the lift of
    -- `α` attached to `G`, by definition of the absorbed solver (`rfl`). The winner `s` does
    -- not see the MBO `a`:
    --
    --   ┌───────────────────────────┐
    --   │ ┌───┐ ──x────▶ ┌────────┐ │ ──u────▶ ┌───┐
    --   │ │ s │          │ lift α │ │          │ G │
    --   │ └───┘ ◀─(y,a)─ └────────┘ │ ◀─(v,a)─ └───┘
    --   └───────────────────────────┘
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩

/-- **Interfaces are an instance of `DistinctionGames`**: the solvers are the solver behaviors,
the visible resource is the visible system, and conditional equivalence is that of the game's
random system and the resource. -/
noncomputable instance distinctionGames : DistinctionGames Interface Resource Game where
  toGames := games
  -- Field `solvers`: the pairs (decision probabilities, winning probabilities) of the
  -- systems-level solver behaviors `Domain.SolverBehavior`.
  solvers := solvers
  -- Axiom `solvers_winner`: the second component of a solver behavior is, by the definition
  -- of `winners`, a winner.
  solvers_winner := by
    rintro _ _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  -- Axiom `solvers_closed_attach`, discharged by the systems-level construction
  -- `Domain.SolverBehavior.absorb`: `s` with `α` absorbed decides on `R` as `s` decides on
  -- `α • R`, and wins `G` as `s` wins the lift of `α` attached to `G` (both by `rfl`).
  solvers_closed_attach {A B} α := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩
  -- Field `visible`: the systems-level visible system `RandomSystem.visible` (`S⁻`).
  visible := Game.visible
  -- Axiom `visible_attachGame`, discharged by the systems-level theorem
  -- `RandomSystem.visible_attach_liftMBO`: `(lift α • G)⁻ = α • G⁻`.
  visible_attachGame {A B} α G :=
    Subtype.ext (RandomSystem.visible_attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.1
      G.1.2)
  -- Field `ConditionallyEquivalent`: the systems-level `RandomSystem.ConditionallyEquivalent`
  -- of the game's random system and the resource's random system.
  ConditionallyEquivalent G T := G.1.1.ConditionallyEquivalent T.1
  -- Axiom `advantage_le_win`, discharged by the systems-level theorem
  -- `Domain.Distinguisher.advantage_le_winProbability` for the probabilistic distinguisher
  -- behind the solver behavior.
  advantage_le_win := by
    -- The solver is a solver behavior `s`.
    rintro A G T _ hc ⟨s, rfl⟩
    -- `s` comes from one probabilistic distinguisher `P`: its decisions are `P`'s decision
    -- probabilities (`hP`) and its winning probabilities are `P`'s (`hW`).
    obtain ⟨P, hP, hW⟩ := s.2
    change |s.1.1 (Game.visible G) - s.1.1 T| ≤ s.1.2 ⟨G.1.1, G.1.2, G.2⟩
    -- Rewrite the goal in terms of `P`:
    --   |Pr[P → 1 on G⁻] − Pr[P → 1 on T]| ≤ Pr[P sets the MBO of G]
    rw [hP (Game.visible G), hP T, hW ⟨G.1.1, G.1.2, G.2⟩]
    -- Conditional equivalence `G |≡ T` bounds `P`'s advantage by its winning probability.
    exact P.advantage_le_winProbability G.1.2 T.2 G.2 hc

/-- **Winning by every distinguisher bounds winning by every winner**: a bound on the winning
probability of every distinguisher for the game's system bounds the winning probability of
every winner. -/
theorem win_le {A : Interface} {G : Game A} {ε : ℝ}
    (hW : ∀ P : A.inputDomain.Distinguisher, P.winProbability G.1.1 ≤ ε)
    {winner : Game A → ℝ} (hw : winner ∈ Games.winners A) : winner G ≤ ε := by
  -- The winner is the winning probability of a solver behavior `s`, which is that of one
  -- probabilistic distinguisher `P` (`hP`).
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨P, -, hP⟩ := s.2
  change s.1.2 ⟨G.1.1, G.1.2, G.2⟩ ≤ ε
  -- So the winner wins `G` with `P`'s winning probability, which `hW` bounds.
  rw [hP]
  exact hW P

/-- **Conditional equivalence bounds the distance of the visible resource** (CR18,
Theorem 4.17): a game on an interface conditionally equivalent to a resource `T`, whose MBO stays
unset with probability at least `1 - ε` on the queries of each transcript of `T`, has its
visible resource within `ε` of `T`. -/
theorem dist_visible_le {A : Interface} {G : Game A} {T : Resource A}
    (hc : DistinctionGames.ConditionallyEquivalent G T) {ε : ℝ}
    (hε : ∀ h, T.1 h ≠ 0 → 1 - ε ≤ G.1.1.unsetProbability (h.map Prod.fst)) :
    CryptographicAlgebra.distance (DistinctionGames.visible G) T ≤ ENNReal.ofReal ε := by
  -- The distance of `CompatiblePseudoMetric` (its field `fibreMetric`) on interfaces is the
  -- systems-level transcript distance of the random systems.
  rw [cc_distance_eq]
  -- The systems-level bound: Δ(G⁻, T) ≤ ε when `G |≡ T` and the MBO of `G` stays unset with
  -- probability at least `1 - ε` on the queries of each transcript of `T`.
  exact RandomSystem.transcriptDistance_visible_le_of_unsetProbability G.1.2 T.2 G.2 hc hε

end SystemAlgebra.Interface

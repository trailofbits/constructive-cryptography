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
  attachGame := attachGame
  attachGame_identity G := by
    apply Subtype.ext
    change liftMBO (𝟙 _) • G.1 = G.1
    rw [show liftMBO (𝟙 _) = 𝟙 _ from PDCBehavior.liftMBO_id _]
    exact identity_attach G.1
  attachGame_serial α β G := by
    apply Subtype.ext
    change liftMBO (α ≫ β) • G.1 = liftMBO α • (liftMBO β • G.1)
    rw [show liftMBO (α ≫ β) = liftMBO α ≫ liftMBO β from PDCBehavior.liftMBO_comp α β]
    exact comp_smul _ _ G.1
  winners := winners
  closed_attach {A B} α := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩

/-- **Interfaces are an instance of `DistinctionGames`**: the solvers are the solver behaviors,
the visible resource is the visible system, and conditional equivalence is that of the game's
random system and the resource. -/
noncomputable instance distinctionGames : DistinctionGames Interface Resource Game where
  toGames := games
  solvers := solvers
  solvers_winner := by
    rintro _ _ ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  solvers_closed_attach {A B} α := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩
  visible := Game.visible
  visible_attachGame {A B} α G :=
    Subtype.ext (RandomSystem.visible_attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.1
      G.1.2)
  ConditionallyEquivalent G T := G.1.1.ConditionallyEquivalent T.1
  advantage_le_win := by
    rintro A G T _ hc ⟨s, rfl⟩
    obtain ⟨P, hP, hW⟩ := s.2
    change |s.1.1 (Game.visible G) - s.1.1 T| ≤ s.1.2 ⟨G.1.1, G.1.2, G.2⟩
    rw [hP (Game.visible G), hP T, hW ⟨G.1.1, G.1.2, G.2⟩]
    exact P.advantage_le_winProbability G.1.2 T.2 G.2 hc

/-- **Winning by every distinguisher bounds winning by every winner**: a bound on the winning
probability of every distinguisher for the game's system bounds the winning probability of
every winner. -/
theorem win_le {A : Interface} {G : Game A} {ε : ℝ}
    (hW : ∀ P : A.inputDomain.Distinguisher, P.winProbability G.1.1 ≤ ε)
    {winner : Game A → ℝ} (hw : winner ∈ Games.winners A) : winner G ≤ ε := by
  obtain ⟨s, rfl⟩ := hw
  obtain ⟨P, -, hP⟩ := s.2
  change s.1.2 ⟨G.1.1, G.1.2, G.2⟩ ≤ ε
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
  rw [cc_distance_eq]
  exact RandomSystem.transcriptDistance_visible_le_of_unsetProbability G.1.2 T.2 G.2 hc hε

end SystemAlgebra.Interface

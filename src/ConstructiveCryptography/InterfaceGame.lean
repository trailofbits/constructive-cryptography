import ConstructiveCryptography.InterfaceAlgebra
import ConstructiveCryptography.CryptographicAlgebra.Game
import RandomSystems.Game.MBOAttachment

/-!
# Games on interfaces

Interfaces are an instance of `GameTheory` and of `CompatibleSolverClass`, the abstraction of
games of CR18, Chapter 4; the instance is where that abstraction meets random systems. Its games
are MBO random systems, as CR18 instantiates games (§3.7.1): a game on `A` is a resource on the
interface of `A` with the MBO whose MBO, once set, stays set (`RandomSystem.MonotoneMBO`).

Each field is a systems-level object: `attachGame` attaches the MBO-forwarding lift
`PDCBehavior.liftMBO`, `visible` is the visible system `RandomSystem.visible`, `solvers` are the
solver behaviors `Domain.SolverBehavior`, and `ConditionallyEquivalent` is
`RandomSystem.ConditionallyEquivalent`. Each axiom is discharged by a systems-level theorem:
`attachGame_identity` by `PDCBehavior.liftMBO_id`, `attachGame_serial` by
`PDCBehavior.liftMBO_comp`, `visible_attachGame` by `RandomSystem.visible_attach_liftMBO`,
`closed_attach` by `Domain.SolverBehavior.absorb`, and `advantage_le_win` by
`Domain.Distinguisher.advantage_le_winProbability`.

## Main definitions

* `Interface.withMBO A`: the interface of `A` with the MBO
* `Interface.Game A`: games on `A`
* `Interface.gameTheory`, `Interface.compatibleSolverClass`: the instances

## Main results

* `Interface.win_le`: a bound on winning by every distinguisher bounds winning by every solver
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

/-- **Interfaces are an instance of `GameTheory`**: attachment is the attachment of the lift,
and the visible resource is the visible system. -/
noncomputable instance gameTheory : GameTheory Interface Resource Game where
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
  visible := Game.visible
  visible_attachGame {A B} α G :=
    Subtype.ext (RandomSystem.visible_attach_liftMBO B.nonempty_prefix A.nonempty_prefix α G.1.1
      G.1.2)

/-- The solvers on `A`: the solver behaviors on the input domain of `A`. -/
def solvers (A : Interface) : Set ((Resource A → ℝ) × (Game A → ℝ)) :=
  Set.range fun s : Domain.SolverBehavior (Y := A.Y) A.domain A.bound A.length_le =>
    (fun R => s.1.1 R, fun G => s.1.2 ⟨G.1.1, G.1.2, G.2⟩)

/-- **Interfaces are an instance of `CompatibleSolverClass`**: the solvers are the solver
behaviors, and conditional equivalence is that of the game and the resource. -/
noncomputable instance compatibleSolverClass : CompatibleSolverClass Interface Resource Game where
  solvers := solvers
  closed_attach {A B} α := by
    rintro _ ⟨s, rfl⟩
    exact ⟨Domain.SolverBehavior.absorb B.nonempty_prefix A.nonempty_prefix α s, rfl⟩
  ConditionallyEquivalent G T := G.1.1.ConditionallyEquivalent T.1
  advantage_le_win := by
    rintro A G T _ hc ⟨s, rfl⟩
    obtain ⟨P, hP, hW⟩ := s.2
    change |s.1.1 (Game.visible G) - s.1.1 T| ≤ s.1.2 ⟨G.1.1, G.1.2, G.2⟩
    rw [hP (Game.visible G), hP T, hW ⟨G.1.1, G.1.2, G.2⟩]
    exact P.advantage_le_winProbability G.1.2 T.2 G.2 hc

/-- **Winning by every distinguisher bounds winning by every solver**: a bound on the winning
probability of every distinguisher for the game's system bounds the winning probability of
every solver. -/
theorem win_le {A : Interface} {G : Game A} {ε : ℝ}
    (hW : ∀ P : A.inputDomain.Distinguisher, P.winProbability G.1.1 ≤ ε)
    {solver : (Resource A → ℝ) × (Game A → ℝ)} (hs : solver ∈ CompatibleSolverClass.solvers A) :
    solver.2 G ≤ ε := by
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨P, -, hP⟩ := s.2
  change s.1.2 ⟨G.1.1, G.1.2, G.2⟩ ≤ ε
  rw [hP]
  exact hW P

end SystemAlgebra.Interface

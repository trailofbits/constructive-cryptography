import ConstructiveCryptography.CryptographicAlgebra.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Games

The abstraction of games of CR18, Chapter 4: a game is a problem whose performance is a
winning probability (Definition 4.5). The classes introduce games and solvers only as fields and
axioms, and know nothing about systems.

`GameTheory` assumes games on each interface, an attachment of converters to games,
contravariant in serial composition, and the visible resource of each game, with which
attachment commutes. `CompatibleSolverClass` assumes solvers, each given by its two
performances: its probability of outputting `1` on each resource (Definition 4.7) and its
winning probability for each game (Definition 4.5). The solvers on each interface are closed
under absorbing a converter: a solver with a converter absorbed wins a game as the solver wins
the game with the converter attached. It also assumes a conditional equivalence of games to
resources, under which each solver's advantage between the visible resource of a game and the
resource is at most its winning probability.

CR18 instantiates games as systems with a monotone binary output (§3.7.1); so does the instance
on interfaces, `ConstructiveCryptography.InterfaceGame`.

Sources: CR18, §4.5.1 (Definition 4.5, games and the winning probability), §4.5.2
(Definition 4.7, distinction problems), §4.8.3 (attachment, as used in Definition 4.13 and the
proof of Lemma 4.9, `g(W R) = (R g)(W)`), §4.10.3 (Definition 4.18, the visible system `S⁻`;
Lemma 4.16) and §4.11.1 (Definition 4.19, conditional equivalence; Theorem 4.17).

## Main definitions

* `GameTheory C Φ Game`: games on each interface, attachment, and visible resources
* `CompatibleSolverClass C Φ Game`: solvers closed under absorbing a converter, and
  conditional equivalence of a game to a resource
* `CompatibleSolverClass.absorb`: a solver with a converter absorbed

## Main results

* `CompatibleSolverClass.absorb_mem`: absorbing a converter gives a solver
* `CompatibleSolverClass.absorb_comp`: absorbing a serial composition absorbs its converters
  in turn
-/

namespace ConstructiveCryptography

open CategoryTheory

universe u v w x

/-- **Games over a resource theory** (CR18, §4.5.1 and Definition 4.18): the games on
each interface, attachment of converters, contravariant in serial composition, and the visible
resource of a game, with which attachment commutes. -/
class GameTheory (C : Type u) [Category.{v} C] (Phi : outParam (C → Type w))
    [ResourceTheory C Phi] (Game : outParam (C → Type x)) where
  /-- Attaching a converter to a game, written `R g` where CR18 uses it (Definition 4.13). -/
  attachGame : ∀ {A B : C}, (A ⟶ B) → Game B → Game A
  /-- Attaching the identity converter leaves a game unchanged. -/
  attachGame_identity : ∀ {A : C} (game : Game A), attachGame (𝟙 A) game = game
  /-- Serial converter attachment is nested attachment. -/
  attachGame_serial : ∀ {A B D : C} (first : A ⟶ B) (second : B ⟶ D) (game : Game D),
    attachGame (first ≫ second) game = attachGame first (attachGame second game)
  /-- The visible resource `S⁻` of a game (CR18, Definition 4.18). -/
  visible : ∀ {A : C}, Game A → Phi A
  /-- Attaching a converter to a game attaches it to the visible resource. -/
  visible_attachGame : ∀ {A B : C} (converter : A ⟶ B) (game : Game B),
    visible (attachGame converter game) = ResourceTheory.attach converter (visible game)

namespace GameTheory

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [GameTheory C Phi Game]

/-- Converter attachment to games uses the heterogeneous action notation. -/
instance instHSMulConverterGame {A B : C} : HSMul (A ⟶ B) (Game B) (Game A) where
  hSMul := attachGame

@[simp]
theorem smul_eq_attachGame {A B : C} (converter : A ⟶ B) (game : Game B) :
    (converter • game : Game A) = attachGame converter game :=
  rfl

end GameTheory

/-- **A compatible solver class** (CR18, §§4.5, 4.10–4.11): the solvers on each interface,
each given by its probability of outputting `1` on every resource and its winning probability
for every game, closed under absorbing a converter; and conditional equivalence of a game to
a resource, under which each solver's advantage between the visible resource and the resource
is at most its winning probability (CR18, Lemma 4.16 and the proof of Theorem 4.17). -/
class CompatibleSolverClass (C : Type u) [Category.{v} C] (Phi : outParam (C → Type w))
    [ResourceTheory C Phi] (Game : outParam (C → Type x)) [GameTheory C Phi Game] where
  /-- The solvers at each interface: a decision probability on resources and a winning
  probability for games. -/
  solvers : ∀ A : C, Set ((Phi A → ℝ) × (Game A → ℝ))
  /-- A solver with a converter absorbed is a solver: it decides on a resource as the solver
  decides on the converter attached to it, and wins a game as the solver wins the converter
  attached to it (CR18, proof of Lemma 4.9). -/
  closed_attach : ∀ {A B : C} (converter : A ⟶ B) {solver : (Phi A → ℝ) × (Game A → ℝ)},
    solver ∈ solvers A →
      (fun R => solver.1 (ResourceTheory.attach converter R),
        fun game => solver.2 (GameTheory.attachGame converter game)) ∈ solvers B
  /-- Conditional equivalence `S |≡ T` of a game to a resource (CR18, Definition 4.19). -/
  ConditionallyEquivalent : ∀ {A : C}, Game A → Phi A → Prop
  /-- **Conditional equivalence bounds distinguishing by winning** (CR18, Lemma 4.16 and the
  proof of Theorem 4.17). -/
  advantage_le_win : ∀ {A : C} {game : Game A} {T : Phi A}
    {solver : (Phi A → ℝ) × (Game A → ℝ)}, ConditionallyEquivalent game T →
      solver ∈ solvers A → |solver.1 (GameTheory.visible game) - solver.1 T| ≤ solver.2 game

namespace CompatibleSolverClass

open GameTheory

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [GameTheory C Phi Game]

/-- A solver with a converter absorbed: it decides on a resource as the solver decides on the
converter attached to it, and wins a game as the solver wins the converter attached to it. -/
def absorb {A B : C} (converter : A ⟶ B) (solver : (Phi A → ℝ) × (Game A → ℝ)) :
    (Phi B → ℝ) × (Game B → ℝ) :=
  (fun R => solver.1 (ResourceTheory.attach converter R),
    fun game => solver.2 (attachGame converter game))

theorem absorb_mem [CompatibleSolverClass C Phi Game] {A B : C} (converter : A ⟶ B)
    {solver : (Phi A → ℝ) × (Game A → ℝ)} (h : solver ∈ solvers A) :
    absorb converter solver ∈ solvers B :=
  closed_attach converter h

/-- **Absorbing a serial composition** absorbs its converters in turn. -/
theorem absorb_comp {A B D : C} (first : A ⟶ B) (second : B ⟶ D)
    (solver : (Phi A → ℝ) × (Game A → ℝ)) :
    absorb (first ≫ second) solver = absorb second (absorb first solver) := by
  simp only [absorb, ResourceTheory.attach_serial, attachGame_serial]

end CompatibleSolverClass

end ConstructiveCryptography

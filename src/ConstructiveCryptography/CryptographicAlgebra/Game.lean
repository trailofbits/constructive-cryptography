import ConstructiveCryptography.CryptographicAlgebra.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
# Games

The abstraction of games of CR18, Chapter 4, in two classes. They introduce games, winners and
solvers only as fields and axioms, and know nothing about systems.

`Games` is the abstraction of CR18, §4.4.3, §4.5.1 and §4.7.2. A problem is a set of solvers with
a performance function (Definition 4.2); for a game the solvers are winners, and the performance
of a winner is its winning probability (Definition 4.5), so a winner is given here by its winning
probability for each game. A converter turns a game into a game, contravariantly in serial
composition, and a winner into a winner: the winner with the converter absorbed wins a game as
the winner wins the game with the converter attached, `ω(w c, g) = ω(w, c g)` (equation (4.9)).
Games and winners do not involve resources.

`DistinctionGames` extends it to the abstraction of CR18, §§4.10–4.11, which relates games to
distinction problems. Its solvers are the objects that are both a distinguisher and a winner, as
`D` in Lemma 4.16: each is given by its probability of outputting `1` on each resource and its
winning probability for each game, which is a winner of `Games`; they are closed under absorbing
a converter. It assumes the visible resource of each game, with which attachment commutes
(Definition 4.18), and a conditional equivalence of games to resources (Definition 4.19), under
which each solver's advantage between the visible resource of a game and the resource is at most
its winning probability (Lemma 4.16 and the proof of Theorem 4.17).

CR18 instantiates games as systems with a monotone binary output (§3.7.1); so does the instance
on interfaces, `ConstructiveCryptography.InterfaceGame`.

Sources: CR18, §4.4.3 (Definition 4.2, printed p. 85), §4.5.1 (Definition 4.5, p. 89), §4.7.2
(reductions by a converter, equations (4.9) and (4.10), p. 93), §4.10.3 (Definition 4.18, the
visible system `S⁻`; Lemma 4.16, p. 107) and §4.11.1 (Definition 4.19, conditional equivalence;
Theorem 4.17, p. 109).

## Main definitions

* `Games C Game`: games on each interface, attachment of converters, and winners closed under
  absorbing a converter
* `DistinctionGames C Φ Game`: solvers that are both distinguishers and winners, the visible
  resource of a game, and conditional equivalence of a game to a resource
* `Games.absorb`, `DistinctionGames.absorb`: a winner, and a solver, with a converter absorbed

## Main results

* `Games.absorb_mem`, `DistinctionGames.absorb_mem`: absorbing a converter gives a winner, and a
  solver
* `Games.absorb_comp`: absorbing a serial composition absorbs its converters in turn
-/

namespace ConstructiveCryptography

open CategoryTheory

universe u v w x

/-- **Games** (CR18, §4.4.3, §4.5.1 and §4.7.2): the games on each interface, attachment of
converters to games, contravariant in serial composition, and the winners, each given by its
winning probability for every game, closed under absorbing a converter. -/
class Games (C : Type u) [Category.{v} C] (Game : outParam (C → Type x)) where
  /-- Attaching a converter to a game: the converter turns a game into a game (CR18, §4.7.2). -/
  attachGame : ∀ {A B : C}, (A ⟶ B) → Game B → Game A
  /-- Attaching the identity converter leaves a game unchanged. -/
  attachGame_identity : ∀ {A : C} (game : Game A), attachGame (𝟙 A) game = game
  /-- Serial converter attachment is nested attachment. -/
  attachGame_serial : ∀ {A B D : C} (first : A ⟶ B) (second : B ⟶ D) (game : Game D),
    attachGame (first ≫ second) game = attachGame first (attachGame second game)
  /-- The winners at each interface, each given by its winning probability for every game, its
  performance (CR18, Definitions 4.2 and 4.5). -/
  winners : ∀ A : C, Set (Game A → ℝ)
  /-- A winner with a converter absorbed is a winner: it wins a game as the winner wins the game
  with the converter attached, `ω(w c, g) = ω(w, c g)` (CR18, §4.7.2, equation (4.9)). -/
  closed_attach : ∀ {A B : C} (converter : A ⟶ B) {winner : Game A → ℝ},
    winner ∈ winners A → (fun game => winner (attachGame converter game)) ∈ winners B

namespace Games

variable {C : Type u} [Category.{v} C] {Game : C → Type x} [Games C Game]

/-- Converter attachment to games uses the heterogeneous action notation. -/
instance instHSMulConverterGame {A B : C} : HSMul (A ⟶ B) (Game B) (Game A) where
  hSMul := attachGame

@[simp]
theorem smul_eq_attachGame {A B : C} (converter : A ⟶ B) (game : Game B) :
    (converter • game : Game A) = attachGame converter game :=
  rfl

/-- A winner with a converter absorbed: it wins a game as the winner wins the game with the
converter attached (CR18, §4.7.2, equation (4.10), `C G = G ∘ ρ_C`). -/
def absorb {A B : C} (converter : A ⟶ B) (winner : Game A → ℝ) : Game B → ℝ :=
  fun game => winner (attachGame converter game)

theorem absorb_mem {A B : C} (converter : A ⟶ B) {winner : Game A → ℝ}
    (h : winner ∈ winners A) : absorb converter winner ∈ winners B :=
  closed_attach converter h

/-- **Absorbing a serial composition** absorbs its converters in turn. -/
theorem absorb_comp {A B D : C} (first : A ⟶ B) (second : B ⟶ D) (winner : Game A → ℝ) :
    absorb (first ≫ second) winner = absorb second (absorb first winner) :=
  funext fun game => congrArg winner (attachGame_serial first second game)

end Games

/-- **Games related to distinction problems** (CR18, §§4.10–4.11): the solvers that are both a
distinguisher and a winner, as `D` in Lemma 4.16, closed under absorbing a converter; the visible
resource of a game, with which attachment commutes; and a conditional equivalence of games to
resources, under which each solver's advantage between the visible resource and the resource is
at most its winning probability. -/
class DistinctionGames (C : Type u) [Category.{v} C] (Phi : outParam (C → Type w))
    [ResourceTheory C Phi] (Game : outParam (C → Type x)) extends Games C Game where
  /-- The solvers at each interface that are both a distinguisher and a winner, each given by its
  probability of outputting `1` on every resource and its winning probability for every game
  (CR18, Lemma 4.16). -/
  solvers : ∀ A : C, Set ((Phi A → ℝ) × (Game A → ℝ))
  /-- The winning probability of a solver is a winner. -/
  solvers_winner : ∀ {A : C} {solver : (Phi A → ℝ) × (Game A → ℝ)},
    solver ∈ solvers A → solver.2 ∈ winners A
  /-- A solver with a converter absorbed is a solver: it decides on a resource as the solver
  decides on the converter attached to it, and wins a game as the solver wins the converter
  attached to it (CR18, §4.7.2 and the proof of Lemma 4.9). -/
  solvers_closed_attach : ∀ {A B : C} (converter : A ⟶ B)
    {solver : (Phi A → ℝ) × (Game A → ℝ)}, solver ∈ solvers A →
      (fun R => solver.1 (ResourceTheory.attach converter R),
        fun game => solver.2 (attachGame converter game)) ∈ solvers B
  /-- The visible resource `S⁻` of a game (CR18, Definition 4.18). -/
  visible : ∀ {A : C}, Game A → Phi A
  /-- Attaching a converter to a game attaches it to the visible resource. -/
  visible_attachGame : ∀ {A B : C} (converter : A ⟶ B) (game : Game B),
    visible (attachGame converter game) = ResourceTheory.attach converter (visible game)
  /-- Conditional equivalence `S |≡ T` of a game to a resource (CR18, Definition 4.19). -/
  ConditionallyEquivalent : ∀ {A : C}, Game A → Phi A → Prop
  /-- **Conditional equivalence bounds distinguishing by winning** (CR18, Lemma 4.16 and the
  proof of Theorem 4.17). -/
  advantage_le_win : ∀ {A : C} {game : Game A} {T : Phi A}
    {solver : (Phi A → ℝ) × (Game A → ℝ)}, ConditionallyEquivalent game T →
      solver ∈ solvers A → |solver.1 (visible game) - solver.1 T| ≤ solver.2 game

namespace DistinctionGames

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [DistinctionGames C Phi Game]

/-- A solver with a converter absorbed: it decides on a resource as the solver decides on the
converter attached to it, and wins a game as the solver wins the converter attached to it. -/
def absorb {A B : C} (converter : A ⟶ B) (solver : (Phi A → ℝ) × (Game A → ℝ)) :
    (Phi B → ℝ) × (Game B → ℝ) :=
  (fun R => solver.1 (ResourceTheory.attach converter R), Games.absorb converter solver.2)

theorem absorb_mem {A B : C} (converter : A ⟶ B) {solver : (Phi A → ℝ) × (Game A → ℝ)}
    (h : solver ∈ solvers A) : absorb converter solver ∈ solvers B :=
  solvers_closed_attach converter h

end DistinctionGames

end ConstructiveCryptography

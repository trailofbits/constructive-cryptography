import ConstructiveCryptography.CryptographicAlgebra.Basic
import ConstructiveCryptography.Game

set_option autoImplicit false

/-!
# Converter actions on games

The evaluation classes `Games` and `DistinctionGames` live in `ConstructiveCryptography.Game`
without a category assumption. Here the interface carrier is a category `C`: its objects are
interfaces and a morphism `α : A ⟶ B` is a converter with outside interface `A` and inside
interface `B`. `GameAction C Game Ω` attaches such a converter to a game on `B`, giving a game
`αG` on `A`, with closure under the same converters as the CC algebra, for the performance
space `Ω` (Omega) of `Games C Game Ω`: an absorbed winner `Wα` takes values in the same `Ω`.
`DistinctionGameAction`, over the probability instance `GameAction C Game ℝ` and a resource
family `Phi`, closes the common solvers under absorbing a converter into both views at once,
and commutes attachment with the visible resource.

CR18 §4.7.2 (printed p. 94), equation (4.9), gives `ω(wc, g) = ω(w, cg)`. Absorption keeps
physical order, with the winner first:

```text
W -- α -- β -- G
(Wα)β = W(α ≫ β)        (α ≫ β) • G = α • (β • G)
```

`Games.absorb_mem` uses closure of the admitted winners. `Games.absorb_comp` uses serial
attachment; `DistinctionGames.absorb_mem` preserves the two evaluations of the same solver.
On interfaces (`ConstructiveCryptography.Instances.Game`), the identity and serial laws are
`TypedConverter.identity_attachGame` and `TypedConverter.comp_attachGame`, and both closure
laws are `Domain.SolverBehavior.absorb`.
-/

namespace ConstructiveCryptography

open CategoryTheory

universe u v w x y

/-- Attachment of the CC converters to games, with identity, serial and admission laws.
CR18 §4.7.2 (printed p. 94): “if g is a game, then cg is also a game.” -/
class GameAction
    -- Objects `A : C` are interfaces; `α : A ⟶ B` is a converter from outside `A` to inside
    -- `B`, and `α ≫ β` places `α` outside `β`.
    (C : Type u) [Category.{v} C]
    -- `Game` assigns to each interface `A : C` its type of games `Game A`; attachment runs
    -- against the arrow, `Game B → Game A`.
    (Game : C → Type x)
    -- Ω (Omega) contains the performance values of the winners selected by `Games C Game Ω`;
    -- absorbed winners keep values in Ω. `outParam` is for inference only.
    (Ω : outParam (Type y)) [Preorder Ω] [Games C Game Ω] where
  /-- The attached game `αG` presents the outside interface of `α`. -/
  attachGame : ∀ {A B : C}, (A ⟶ B) → Game B → Game A
  /-- Attaching the identity leaves the game unchanged. -/
  attachGame_identity : ∀ {A : C} (game : Game A), attachGame (𝟙 A) game = game
  /-- Serial attachment groups the wiring from the game end: `(αβ)G = α(βG)`. -/
  attachGame_serial : ∀ {A B D : C} (first : A ⟶ B) (second : B ⟶ D) (game : Game D),
    attachGame (first ≫ second) game = attachGame first (attachGame second game)
  /-- Absorbing an allowed converter preserves admission of the winner: if `W` is admitted
  on `A` and `α : A ⟶ B`, then `G ↦ W(αG)` is admitted on `B`. -/
  closed_attach : ∀ {A B : C} (converter : A ⟶ B) {winner : Game A → Ω},
    winner ∈ Games.winners A →
      (fun game => winner (attachGame converter game)) ∈ Games.winners B

namespace Games

-- Objects `A : C` are interfaces with converters `A ⟶ B`; `Game A` is the type of games on
-- `A`; Ω (Omega) contains performances, with admitted winners `Games.winners A` and
-- attachment `Game B → Game A` from `GameAction C Game Ω`.
variable {C : Type u} [Category.{v} C] {Game : C → Type x} {Ω : Type y} [Preorder Ω]
  [Games C Game Ω] [GameAction C Game Ω]

/-- Converter attachment to games uses the heterogeneous action notation. -/
instance instHSMulConverterGame {A B : C} : HSMul (A ⟶ B) (Game B) (Game A) where
  hSMul := GameAction.attachGame (Ω := Ω)

/-- The action notation `α • G` on a game `G : Game B` unfolds to `attachGame α G`. -/
@[simp]
lemma smul_eq_attachGame {A B : C} (converter : A ⟶ B) (game : Game B) :
    (converter • game : Game A) = GameAction.attachGame converter game :=
  rfl

/-- Absorbing a converter into an admitted winner gives an admitted winner (`closed_attach`). -/
lemma absorb_mem {A B : C} (converter : A ⟶ B) {winner : Game A → Ω}
    (h : winner ∈ winners A) : absorb winner converter ∈ winners B :=
  GameAction.closed_attach converter h

/-- **Absorbing a serial composition** absorbs its converters in turn. For a winner
`W : Game A → Ω`, `first : A ⟶ B` and `second : B ⟶ D`, the winner `W(first ≫ second)` on
`Game D` equals `(W first) second`, absorbing the outer converter `first` before `second`;
it is `attachGame_serial` under `W`. No admission is claimed. -/
lemma absorb_comp {A B D : C} (winner : Game A → Ω) (first : A ⟶ B) (second : B ⟶ D) :
    absorb (H := Game D) winner (first ≫ second) =
      absorb (absorb (H := Game B) winner first) second :=
  funext fun game => congrArg winner (GameAction.attachGame_serial first second game)

end Games

/-- The CC action on a common solver's two evaluations, and on visible resources, over the
probability instance `GameAction C Game ℝ`.
CR18 §4.7.2 (printed p. 94) keeps the MBO “not being seen or affected” by the converter. -/
class DistinctionGameAction
    -- Objects `A : C` are interfaces and morphisms `A ⟶ B` converters, as in `GameAction`.
    (C : Type u) [Category.{v} C]
    -- `Phi A` is the type of resources on `A`; `ResourceTheory C Phi` attaches converters,
    -- `Phi B → Phi A`.
    (Phi : C → Type w)
    [ResourceTheory C Phi]
    -- `Game A` is the type of games on `A`; `DistinctionGames.solvers A` holds pairs `(d, w)`
    -- of an output-1 probability `d` on `Phi A` and a winning probability `w` on `Game A`.
    (Game : C → Type x) [DistinctionGames C Phi Game]
    -- `GameAction C Game ℝ` attaches converters to games, with real (probability) performance.
    [GameAction C Game ℝ] where
  /-- Absorption preserves admission and transforms both views with the same converter:
  `α : A ⟶ B` turns `(d, w)` into `(R ↦ d(αR), G ↦ w(αG))` on `B`. -/
  solvers_closed_attach : ∀ {A B : C} (converter : A ⟶ B)
    {solver : (Phi A → ℝ) × (Game A → ℝ)}, solver ∈ DistinctionGames.solvers A →
      (fun R => solver.1 (ResourceTheory.attach converter R),
        fun game => solver.2 (GameAction.attachGame converter game)) ∈ DistinctionGames.solvers B
  /-- Forgetting the hidden condition commutes with converter attachment: `(αG)⁻ = αG⁻`. -/
  visible_attachGame : ∀ {A B : C} (converter : A ⟶ B) (game : Game B),
    DistinctionGames.visible (GameAction.attachGame converter game) =
      ResourceTheory.attach converter (DistinctionGames.visible game)

namespace DistinctionGames

-- Objects `A : C` are interfaces with converters `A ⟶ B`; `Phi A` and `Game A` are the
-- resources and games on `A`; `solvers A` holds pairs of evaluations on them, and converters
-- act on resources, games and solvers.
variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {Game : C → Type x} [DistinctionGames C Phi Game] [GameAction C Game ℝ]
  [DistinctionGameAction C Phi Game]

/-- A solver with a converter absorbed: it decides on a resource as the solver decides on the
converter attached to it, and wins a game as the solver wins the converter attached to it. -/
def absorb {A B : C} (solver : (Phi A → ℝ) × (Game A → ℝ)) (converter : A ⟶ B) :
    (Phi B → ℝ) × (Game B → ℝ) :=
  (fun R => solver.1 (ResourceTheory.attach converter R), Games.absorb solver.2 converter)

/-- Absorbing a converter into a solver gives a solver (`solvers_closed_attach`). -/
lemma absorb_mem {A B : C} (converter : A ⟶ B) {solver : (Phi A → ℝ) × (Game A → ℝ)}
    (h : solver ∈ solvers A) : absorb solver converter ∈ solvers B :=
  DistinctionGameAction.solvers_closed_attach converter h

end DistinctionGames

end ConstructiveCryptography

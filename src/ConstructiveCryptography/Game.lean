module

public import ConstructiveCryptography.Problem
public import Mathlib.Basic.Real.Basic

/-!
# Games and their performance

`Games I Game Ω` has interfaces `A : I`, games `G : Game A` on each interface, and a
performance space `Ω` (Omega). It selects on each `A` the admitted winners `W : Game A → Ω`,
where `W G` is the performance of `W` on `G`. The game model fixes `Ω`, as it fixes the
family `Game`. [1, Definition 4.2, p. 85]
gives a “performance function” on a solver set into a partially ordered set;
Definition 4.5 (p. 90) specializes ordinary games to winning probabilities in `[0,1]` and
also considers multi-games with several winning events. Three notions stay apart:

* general performance: any preordered `Ω`, including non-total products such as `ℕ × ℕ`;
  the class asserts no range on `Ω`;
* probability performance: the interface instance selects `Ω = ℝ` for winning probabilities;
  `DistinctionGames` uses real-valued evaluations without asserting a range axiom;
* error budgets: the `ℝ≥0` bounds on distances, kept separate from solver evaluations.

`Games.win_le_of_reduction` applies `Problem.performance_le_of_reduction` to the subtypes of
admitted winners, possibly between different game families and performance spaces. It needs
no converters, category or metric. `Games.absorb` is the solver map given by an attachment
action: `(Wα)(G) = W(αG)`. Identity, serial attachment and closure under converters belong to
`ConstructiveCryptography.CryptographicAlgebra.Game`.

`DistinctionGames` adds a resource family `Phi`, with `Phi A` the resources on interface `A`,
and relates the two evaluations of a common solver: its output-1 probability on resources
and its winning probability on games. Conditional equivalence bounds the first
evaluation's absolute difference by the second. The same solver occurs on both sides; the
decision evaluation alone is not assumed to determine the winning evaluation.

## Main definitions

* `Games`: admitted winners in a selected preordered performance space
* `Games.absorb`: a winner with a converter absorbed
* `DistinctionGames`: the common solvers' decision and winning probabilities
* `GameEquivalence`: optional equivalence-as-games contract on `DistinctionGames`

## Main results

* `Games.win_le_of_reduction`: hardness through a reduction between admitted winners

## References

1. U. Maurer. *Cryptography Foundations*. ETH Zürich lecture notes, Spring 2018.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography

universe u v w x y z

/-- Games with a selected set of admitted winners. [1, Definition 4.2, p. 85]
uses a “partially ordered set” of performances; a preorder suffices for the reduction laws.
Definition 4.5 (p. 90) specializes performances to winning probabilities. -/
class Games
    -- `I` is the type whose elements are interfaces at which games are played.
    (I : Type u)
    -- `Game` assigns to each interface `A : I` its type of games `Game A`.
    -- `outParam` lets the selected instance for `I` determine this family during inference.
    (Game : outParam (I → Type x))
    -- Ω (Omega): performance values, higher meaning at least as good; no range is imposed.
    (Ω : outParam (Type w)) [Preorder Ω] where
  /-- Admitted winners on `A`: `W : Game A → Ω` assigns performance `W G` to each game `G`. -/
  winners : ∀ A : I, Set (Game A → Ω)

namespace Games

/-- Absorption groups the winner with a converter: `(Wα)(G) = W(αG)`.
[1, equation (4.9), p. 94]: `ω(wc, g) = ω(w, cg)`.
Only the attachment action is needed; no serial composition or category is assumed. -/
def absorb
    -- `G` is the type of games with a converter attached; `H` is the type of games a
    -- converter attaches to; `Conv` is the type of converters.
    {G : Type w} {H : Type x} {Conv : Type u}
    -- Ω (Omega) contains the performance values of winners.
    {Ω : Type y}
    -- `HSMul Conv H G` attaches `converter : Conv` to `game : H`, giving `converter • game : G`.
    [HSMul Conv H G]
    -- `winner : G → Ω` scores attached games; with `converter : Conv` absorbed, the result
    -- `H → Ω` scores `game : H` as `winner (converter • game)`.
    (winner : G → Ω) (converter : Conv) : H → Ω :=
  fun game => winner (converter • game)

/-- A reduction transfers target hardness to `W G ≤ loss ε` for every admitted source winner.
[1, equation (4.3), p. 87]: `p ≤ λ q ρ`, with `λ` represented by `loss`.
This applies `Problem.performance_le_of_reduction` to the admitted winners. -/
lemma win_le_of_reduction
    -- `I` and `J` are the types of interfaces for the source and target problems.
    {I : Type u} {J : Type v}
    -- `Game` assigns a type of source games to each interface in `I`.
    {Game : I → Type x}
    -- `OtherGame` assigns a type of target games to each interface in `J`.
    {OtherGame : J → Type y}
    -- Ω (Omega) and Λ (Lambda): source and target performances; higher means better.
    {Ω : Type w} {Λ : Type z} [Preorder Ω] [Preorder Λ]
    -- These `Games` instances supply the admitted winners for the two game families.
    [Games I Game Ω] [Games J OtherGame Λ]
    -- `A : I` selects one source interface; `Game A` is the type of games on it.
    {A : I}
    -- `B : J` selects one target interface; `OtherGame B` is the type of games on it.
    {B : J}
    -- ρ (rho) turns a source winner into a target winner.
    (ρ : (Game A → Ω) → (OtherGame B → Λ))
    -- `loss` maps a target performance bound in Λ back to a source bound in Ω.
    (loss : Λ → Ω)
    -- `hloss` says x ≤ y implies loss x ≤ loss y: translating a bound preserves order.
    (hloss : Monotone loss)
    -- `closed` says every admitted source winner W reduces to an admitted target winner ρ W.
    (closed : ∀ W ∈ winners A, ρ W ∈ winners B)
    -- `G` is a source game on A; `H` is a target game on B.
    {G : Game A} {H : OtherGame B}
    -- ε (epsilon) is a uniform target-performance bound, hence an element of Λ.
    {ε : Λ}
    -- `reduction` bounds W's performance on G by loss applied to ρ W's performance on H.
    (reduction : ∀ W ∈ winners A, W G ≤ loss (ρ W H))
    -- `hardness` bounds the performance V H of every admitted target winner V by ε.
    (hardness : ∀ V ∈ winners B, V H ≤ ε)
    -- `W` is a source winner; `admitted` proves it is allowed. Its performance W G is ≤ loss ε.
    {W : Game A → Ω} (admitted : W ∈ winners A) : W G ≤ loss ε :=
  -- The general reduction with solvers the admitted winners, evaluated at `G` and `H`;
  -- `closed` makes `ρ` well typed on these subtypes.
  Problem.performance_le_of_reduction
    (fun W : {W // W ∈ winners A} => W.1 G)
    (fun V : {V // V ∈ winners B} => V.1 H)
    (fun W => ⟨ρ W.1, closed W.1 W.2⟩) loss hloss
    (fun W => reduction W.1 W.2) (fun V => hardness V.1 V.2) ⟨W, admitted⟩

end Games

/-- Games related to distinguishing by a common solver's two performance functions.
[1, Lemma 4.16, p. 107]: `⟨S⁻ | T⁻⟩ ≤ S̄`; conditional equivalence supplies the
game-to-resource form used in Theorem 4.17. No attachment action or metric is required. -/
class DistinctionGames
    -- `I` is the type whose elements are interfaces, as in `Games`.
    (I : Type u)
    -- `Phi` assigns to each interface `A : I` its type `Phi A` of resources, the systems a
    -- solver can distinguish; `outParam` is for inference only.
    (Phi : outParam (I → Type w))
    -- `Game` assigns to each `A : I` its type of games `Game A`; `Games I Game ℝ` takes real
    -- performances, read as probabilities, with no range axiom.
    (Game : outParam (I → Type x)) extends Games I Game ℝ where
  /-- Common solvers on `A`, as pairs `(d, w)` of one solver's two evaluations: `d R` is its
  probability of outputting 1 on a resource `R : Phi A`, and `w G` its winning probability
  on a game `G : Game A`. Neither evaluation is assumed to determine the other. -/
  solvers : ∀ A : I, Set ((Phi A → ℝ) × (Game A → ℝ))
  /-- The winning view of a solver is an admitted winner. -/
  solvers_winner : ∀ {A : I} {solver : (Phi A → ℝ) × (Game A → ℝ)},
    solver ∈ solvers A → solver.2 ∈ winners A
  /-- The visible resource `G⁻`, with the game's hidden condition forgotten
  [1, Definition 4.18, p. 107: “ignoring the MBO”]. -/
  visible : ∀ {A : I}, Game A → Phi A
  /-- Conditional equivalence `G |≡ T` [1, Definition 4.19, p. 108]. -/
  ConditionallyEquivalent : ∀ {A : I}, Game A → Phi A → Prop
  /-- Conditional equivalence bounds this solver's absolute distinguishing advantage by its
  winning probability, `|d G⁻ - d T| ≤ w G` for a solver `(d, w)`, using both directions of
  the signed bound of [1, Lemma 4.16, p. 107]. -/
  advantage_le_win : ∀ {A : I} {game : Game A} {T : Phi A}
    {solver : (Phi A → ℝ) × (Game A → ℝ)}, ConditionallyEquivalent game T →
      solver ∈ solvers A → |solver.1 (visible game) - solver.1 T| ≤ solver.2 game

/-- Equivalent games share winning probabilities and bound visible distinguishing advantage.
[1, Definition 4.16, p. 105]: "their pre-winning behavior is identical." -/
class GameEquivalence
    -- `A : I` selects an interface; `Phi A` and `Game A` carry its resources and games.
    (I : Type u)
    (Phi : outParam (I → Type w))
    (Game : outParam (I → Type x))
    [DistinctionGames I Phi Game] where
  /-- Equivalence as games `G ≡g H` [1, Definition 4.16, p. 105]. -/
  GameEquivalent : ∀ {A : I}, Game A → Game A → Prop
  /-- Equivalence as games is reflexive. -/
  gameEquivalent_refl : ∀ {A : I} (game : Game A), GameEquivalent game game
  /-- Equivalence as games is symmetric. -/
  gameEquivalent_symm : ∀ {A : I} {first second : Game A},
    GameEquivalent first second → GameEquivalent second first
  /-- Equivalence as games is transitive. -/
  gameEquivalent_trans : ∀ {A : I} {first second third : Game A},
    GameEquivalent first second → GameEquivalent second third → GameEquivalent first third
  /-- Admitted winners win game-equivalent games alike [1, Lemma 4.15, p. 106]. -/
  -- `winner` is the winning evaluation of one admitted observer, shared by both games.
  win_eq : ∀ {A : I} {first second : Game A} {winner : Game A → ℝ},
    GameEquivalent first second → winner ∈ Games.winners A → winner first = winner second
  /-- Fundamental lemma for game-equivalent games [1, Lemma 4.16, p. 107]: distinguishing the
  visible resources is bounded by winning either game. -/
  -- `solver.1` evaluates decisions on resources; `solver.2` scores wins on games.
  advantage_le_win : ∀ {A : I} {first second : Game A}
    {solver : (Phi A → ℝ) × (Game A → ℝ)},
    GameEquivalent first second → solver ∈ DistinctionGames.solvers A →
      |solver.1 (DistinctionGames.visible first) - solver.1 (DistinctionGames.visible second)| ≤
        solver.2 first

end ConstructiveCryptography

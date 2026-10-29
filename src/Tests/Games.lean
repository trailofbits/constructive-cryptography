import ConstructiveCryptography.Game

/-!
# Games without categorical assumptions

Checks of the evaluation layer alone. Two solver transformations compose their monotone
losses in an arbitrary preordered performance space. A product performance `ℕ × ℕ`, ordered
coordinatewise and not totally, reduces to a game family with performance `ℕ` through the
diagonal loss. One solver's winning view bounds its decision view, without converter or metric
assumptions. The `#check_failure` guards confirm that neither the CC resource theory nor the
converter action is in scope.
-/

#check_failure ConstructiveCryptography.ResourceTheory
#check_failure ConstructiveCryptography.GameAction

namespace GamesTests

open ConstructiveCryptography

universe u v w x

/-- If `ρ` and `σ` lose `f` and `g` respectively, the original winner loses `f (g ε)`:
`W G ≤ f (ρ W H) ≤ f (g ε)`. The transformations are arbitrary solver maps, not converters, and
`Ω` is any preorder. -/
lemma win_le_of_two_reductions {I : Type u} {Game : I → Type v} {Ω : Type w}
    [Preorder Ω] [Games I Game Ω]
    {A B C : I} (ρ : (Game A → Ω) → (Game B → Ω))
    (σ : (Game B → Ω) → (Game C → Ω)) (f g : Ω → Ω)
    (hf : Monotone f) (hg : Monotone g)
    (hρ : ∀ W ∈ Games.winners A, ρ W ∈ Games.winners B)
    (hσ : ∀ W ∈ Games.winners B, σ W ∈ Games.winners C)
    {G : Game A} {H : Game B} {J : Game C} {ε : Ω}
    (first : ∀ W ∈ Games.winners A, W G ≤ f (ρ W H))
    (second : ∀ W ∈ Games.winners B, W H ≤ g (σ W J))
    (hardness : ∀ W ∈ Games.winners C, W J ≤ ε)
    {W : Game A → Ω} (hW : W ∈ Games.winners A) : W G ≤ f (g ε) :=
  -- Hardness on `J` and the second reduction bound every admitted `V` by `V H ≤ g ε`; the
  -- first reduction then gives `W G ≤ f (g ε)`.
  Games.win_le_of_reduction ρ f hf hρ first
    (fun _ hV => Games.win_le_of_reduction σ g hg hσ second hardness hV) hW

/-- A scalar bound controls both coordinates of a product performance:
`W G ≤ (ρ W H, ρ W H)` and `V H ≤ n` give `W G ≤ (n, n)`. The two game models use different
carriers and performance spaces, `ℕ × ℕ` with the coordinatewise order, not total, and `ℕ`. -/
lemma product_performance_le {I : Type u} {J : Type v} {Game : I → Type w}
    {OtherGame : J → Type x} [Games I Game (ℕ × ℕ)] [Games J OtherGame ℕ]
    {A : I} {B : J} (ρ : (Game A → ℕ × ℕ) → (OtherGame B → ℕ))
    (closed : ∀ W ∈ Games.winners A, ρ W ∈ Games.winners B)
    {G : Game A} {H : OtherGame B} {n : ℕ}
    (reduction : ∀ W ∈ Games.winners A, W G ≤ (ρ W H, ρ W H))
    (hardness : ∀ V ∈ Games.winners B, V H ≤ n)
    {W : Game A → ℕ × ℕ} (admitted : W ∈ Games.winners A) : W G ≤ (n, n) :=
  -- The diagonal loss `n ↦ (n, n)` is monotone: `m ≤ n` gives `m ≤ n` in each coordinate.
  Games.win_le_of_reduction ρ (fun n : ℕ => (n, n)) (fun _ _ h => And.intro h h)
    closed reduction hardness admitted

/-- The game bound uses the same solver's winning view to control its decision view:
`G |≡ T` and `s.2 G ≤ ε` give `|s.1 G⁻ - s.1 T| ≤ ε`.
Only the evaluation class is assumed, with no action, category or metric instance. -/
lemma advantage_le_of_win_le {I : Type u} {Phi : I → Type v} {Game : I → Type w}
    [DistinctionGames I Phi Game] {A : I} {G : Game A} {T : Phi A}
    (hc : DistinctionGames.ConditionallyEquivalent G T) {ε : ℝ}
    (hardness : ∀ s ∈ DistinctionGames.solvers A, s.2 G ≤ ε)
    {s : (Phi A → ℝ) × (Game A → ℝ)} (hs : s ∈ DistinctionGames.solvers A) :
    |s.1 (DistinctionGames.visible G) - s.1 T| ≤ ε :=
  (DistinctionGames.advantage_le_win hc hs).trans (hardness s hs)

-- `Games.absorb` needs only an action: with function application, `(Wα)(g) = W(α g)`; no
-- converter category is involved.
example {G H Ω : Type} (W : G → Ω) (α : H → G) (game : H) :
    letI : HSMul (H → G) H G := ⟨fun f x => f x⟩
    Games.absorb W α game = W (α game) := rfl

#print axioms win_le_of_two_reductions
#print axioms product_performance_le
#print axioms advantage_le_of_win_le

end GamesTests

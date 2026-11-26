module

public import Commons.Definitions.AbstractModel.ExtractionPresentation.Laws
public import RandomSystems.Typed.PresentedGame

/-!
# The extraction game

`extractionGame` presents the retained discrete game through `TypedGame.ofPDG`.
`extractionGame_visible` identifies its visible resource with `extractionSystem`; the hidden
winning condition tests the first submitted guess against the original sampled secret.

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.AbstractModel

open Probability SystemAlgebra

variable
  -- `S` carries register values, `P` model parameters, and `M` their operations.
  -- `ι` indexes registers; `input` selects the register initially containing the secret.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]
  [Fintype S] [Fintype ι] [Fintype M.Operation] [Fintype M.Query]
  [∀ ρ, Fintype (M.Reply ρ)] (input : ι)
  -- `k` bounds ordinary commands; final submission remains separate.
  (k : ℕ)

/-- The sampled system and original-secret condition as a typed game
[1, Figure 1, p. 8]: "The game is won if x' = x". -/
noncomputable def extractionGame
    -- `D` retains the same parameter/secret pair in the visible system and winning condition.
    (D : Distribution.ProbDist (P × S)) :
    TypedGame (M.interface input k) :=
  TypedGame.ofPDG (extractionPDG M input k D).1 (extractionPDG M input k D).2
    (extractionSystem_presents M input k D)

/-- Hiding the winning bit recovers the original composed extraction system. -/
lemma extractionGame_visible (D : Distribution.ProbDist (P × S)) :
    (extractionGame M input k D).visible = M.extractionSystem input k D :=
  TypedGame.visible_ofPDG _ _ (extractionSystem_presents M input k D)

end Commons.AbstractModel

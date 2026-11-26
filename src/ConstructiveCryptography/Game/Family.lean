module

public import ConstructiveCryptography.Game
public import ConstructiveCryptography.Problem.Family

/-!
# Uniform reductions between game families

`Games.Easier` instantiates `Problem.Easier` with admitted winners as solvers and `W G` as
performance. One solver map serves every target game. `easier_of_attach_mem` obtains this map
by absorbing a fixed converter: `(Wα)(H) = W(α • H)`.

Worst-case comparisons use `Problem.Easier.worstCase_le` directly; the game model supplies
admission, family membership and lower bounds on winning performance.

## References

1. U. Maurer, C. Portmann and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace ConstructiveCryptography.Games

universe u v w x y z

/-- A uniform reduction between admitted winners of game families.
[1, Definition 4, p. 6]: "there exists a function α" serving every target game. -/
abbrev Easier
    -- `I` and `J` carry interfaces; `Game A` and `OtherGame B` carry games at `A` and `B`.
    {I : Type u} {J : Type v} {Game : I → Type w} {OtherGame : J → Type x}
    -- Ω orders performance from worse to better; the instances select admitted winners.
    {Ω : Type y} [Preorder Ω] [Games I Game Ω] [Games J OtherGame Ω]
    {A : I} {B : J}
    -- Each target game has a source witness; one map of admitted winners works for all.
    (target : Set (OtherGame B)) (source : Set (Game A)) : Prop :=
  Problem.Easier
    (fun G (W : {W : Game A → Ω // W ∈ winners A}) => W.1 G)
    (fun H (V : {V : OtherGame B → Ω // V ∈ winners B}) => V.1 H)
    target source

/-- A fixed converter taking the target family into the source family gives a uniform
reduction. [1, Lemma 1, p. 21]: "G₂ C ⊆ G₁" implies "G₂ ⊵ G₁".
The source writes attachment on the right; here its `HC` is `α • H`. -/
theorem easier_of_attach_mem
    -- `Game` and `OtherGame` assign games to interfaces in `I` and `J`.
    {I : Type u} {J : Type v} {Game : I → Type w} {OtherGame : J → Type x}
    -- Ω orders performances; the instances supply the admitted winners.
    {Ω : Type y} [Preorder Ω] [Games I Game Ω] [Games J OtherGame Ω]
    -- `A : I` and `B : J` select the source and target interfaces.
    {A : I} {B : J}
    -- `α` attaches to a target game; absorption turns source winners into target winners.
    {Conv : Type z} [HSMul Conv (OtherGame B) (Game A)] (α : Conv)
    (closed : ∀ W ∈ winners A, absorb W α ∈ winners B)
    {target : Set (OtherGame B)} {source : Set (Game A)}
    -- `attached` supplies the source witness `α • H` for each target member `H`.
    (attached : ∀ H ∈ target, α • H ∈ source) : Easier target source := by
  refine ⟨fun W => ⟨absorb W.1 α, closed W.1 W.2⟩, ?_⟩
  exact fun H member => ⟨α • H, attached H member, fun _ => le_rfl⟩

end ConstructiveCryptography.Games

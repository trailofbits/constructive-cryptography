import RandomSystems.System.Basic

/-!
# Deterministic environments

An environment is a query function with prefix-closed domain; it stops where it is
undefined and outputs no decision. Source: Lanzenberger, *A Theory of Random
Systems, Games, and Hardness Amplification*, Definition 2.11.

## Main definitions

* `DDE X Y`: deterministic environments
* `QueryBounded n E`: `E` asks fewer than `n` queries
* `DDE.ofQueries xs`: the environment that asks the fixed queries `xs`
-/

namespace SystemAlgebra

/-- A deterministic environment, as a partial function of received replies. -/
abbrev DDE (X Y : Type) :=
  {e : System Y X // ∀ ys y, (e (ys ++ [y])).Dom → (e ys).Dom}

/-- The environment makes at most `n` queries. -/
def QueryBounded {X Y : Type} (n : ℕ) (E : DDE X Y) : Prop :=
  ∀ ys, (E.1 ys).Dom → ys.length < n

namespace DDE

/-- Issue a fixed list of queries, then stop, independently of the replies. -/
def ofQueries {X Y : Type} (xs : List X) : DDE X Y :=
  ⟨fixedQueries xs, by
    intro ys y hd
    simp [fixedQueries, Part.ofOption_dom] at hd ⊢
    omega⟩

end DDE

end SystemAlgebra

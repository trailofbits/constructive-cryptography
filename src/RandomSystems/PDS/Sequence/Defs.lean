module

public import RandomSystems.PDS.FiniteCuts
public import Probability.Kernel

/-!
# Coherent normalized finite presentations

`PDSSequence D` supplies a probability law on certified deterministic systems at each horizon.
Its compatibility field is exact equality of the pushforward sample laws under `PDS.cutSample`.
Cumulative behavior is induced in `Cumulative.PDSSequence`.
-/

@[expose] public section

namespace SystemAlgebra

open Probability.Distribution

/-- Normalized finite presentations whose adjacent deterministic restrictions agree. -/
structure PDSSequence
    -- `A`, `B` carry queries and replies; `D h x` admits the next query after transcript `h`.
    (A B : Type) (D : List (A × B) → A → Prop) where
  /-- `level n` is a normalized finite law on DDSs answering exactly on the `n`-cut of `D`. -/
  level (n : ℕ) : ProbDist {s : System A B // IsDDS s ∧ HasDomain (cutDomain D n) s}
  /-- Restricting the next level preserves the exact law of deterministic samples. -/
  compatible (n : ℕ) : (level (n + 1)).map (PDS.cutSample D (Nat.le_succ n)) = level n

end SystemAlgebra

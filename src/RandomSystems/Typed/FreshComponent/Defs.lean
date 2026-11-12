module

public import RandomSystems.Typed.Interface

/-!
# Selected fresh components of replies

`TypedSystem.AnswersFresh` is a conditional-mass contract. After each admitted
query, the mass of replies carrying `v` is bounded by `μ v` times the prefix mass. The observer
may return `none`, meaning that the exchange carries no selected value. The inequality also
applies to zero-probability prefixes and uses the existing cumulative system behavior.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

/-- The selected next-reply mass is bounded by `μ` times the preceding transcript mass. -/
def AnswersFresh
    -- `A` selects an interface; `C` carries the selected values.
    {A : Interface} {C : Type} [DecidableEq C]
    -- `X` is the resource; `pick` reads a selected value from a query/reply exchange.
    (X : TypedSystem A) (pick : (Σ i, A.X i) × (Σ i, A.Y i) → Option C)
    -- `μ v` bounds the conditional mass of the selected value `v : C`.
    (μ : Distribution C) : Prop :=
  -- `h` is the preceding transcript and `x` the next admitted query; `v` is the selected value.
  ∀ (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (x : Σ i, A.X i) (v : C),
    A.domain (h.map Prod.fst ++ [x]) →
      ∑ y : A.Y x.1, (if pick (x, ⟨x.1, y⟩) = some v then
        X.1 (h ++ [(x, ⟨x.1, y⟩)]) else 0) ≤ μ v * X.1 h

end SystemAlgebra.TypedSystem

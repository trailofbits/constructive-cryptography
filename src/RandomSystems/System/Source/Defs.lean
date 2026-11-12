module

public import Probability.Distribution

/-!
# Cumulative masses of a fresh source

`sourceMass ν h` is the product of the probabilities of the replies in `h`.
Every query uses the same law `ν` independently, with no bound on the number of queries.
Its normalization and bounded memoryless presentation are proved in `System.Source`.

```text
query x ──▶ [fresh draw y ∼ ν] ──▶ reply y
```
-/

@[expose] public section

namespace SystemAlgebra

open Probability.Distribution

/-- The cumulative mass of a transcript is the product of its fresh reply probabilities. -/
noncomputable def sourceMass
    -- `A` carries query triggers and `B` replies; `ν` is sampled afresh at every trigger.
    {A B : Type} (ν : ProbDist B)
    -- `h` records the successive query/reply pairs.
    (h : List (A × B)) : ℝ :=
  (h.map fun xy => ν.1 xy.2).prod

end SystemAlgebra

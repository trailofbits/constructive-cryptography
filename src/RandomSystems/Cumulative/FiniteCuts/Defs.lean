module

public import RandomSystems.Cumulative.Cumulative

/-!
# Finite observation cuts

`cutDomain D q` admits the queries of `D` before depth `q`; `cutMass p q` retains
cumulative masses through that depth. `RandomSystem.limitMass` reads a family at each
transcript's own depth. The coherence and reconstruction laws are in `FiniteCuts`.

```text
p ── cuts ──▶ family (cut p q) for q ∈ ℕ
▲                         │
└── read at |h| ───────────┘
```
-/

@[expose] public section

namespace SystemAlgebra

-- `A` carries queries, `B` replies; `D h x` admits query `x` after transcript `h`.
variable {A B : Type} (D : List (A × B) → A → Prop)

/-- The observation cut admits `x` exactly when `D h x` and fewer than `q` replies occurred. -/
def cutDomain (q : ℕ) : Domain A B where
  admits h x := D h x ∧ h.length < q
  bound := q
  length_lt _ _ hx := hx.2

/-- Retain the cumulative masses through depth `q` and set later masses to zero. -/
def cutMass
    -- `p h` is the cumulative mass of transcript `h`; `q` is the observation horizon.
    (p : List (A × B) → ℝ) (q : ℕ) (h : List (A × B)) : ℝ :=
  if h.length ≤ q then p h else 0

namespace RandomSystem

variable [Fintype A] [Fintype B]

/-- Read a transcript from a family at the depth of that transcript. -/
noncomputable def limitMass
    -- `R q` supplies the bounded behavior through `q` queries.
    (R : (q : ℕ) → RandomSystem A B (cutDomain D q)) (h : List (A × B)) : ℝ :=
  R h.length h

end RandomSystem

end SystemAlgebra

import Mathlib.Order.Monotone.Defs

set_option autoImplicit false

/-!
# Problems with ordered performance

CR18 Definition 4.2 (printed p. 85) equips a problem with a solver set and a
“partially ordered set” of performance values, higher meaning at least as good a performance.
Here a problem is not a record: its solvers are a type `Solver` and its performance function
an explicit evaluation `p : Solver → Ω` into a performance space `Ω` (Omega). Solvers need not
be functions, and two problems need not share a solver type or a performance space: a second
problem `q : OtherSolver → Λ` has its own solver type `OtherSolver` and performance space `Λ`
(Lambda). The reduction bound needs only preorders on `Ω` and `Λ`, weaker than the source's
partial orders, since antisymmetry is never used.

`Problem.performance_le_of_reduction` transfers an upper bound `ε` (epsilon) on the target
problem `q` back to the source problem `p`. A solver map `ρ : Solver → OtherSolver` (rho)
turns each solver `s` for `p` into a solver `ρ s` for `q`, and a monotone `loss : Λ → Ω`
turns a bound on target performance into a bound on source performance:

```text
solver s ── ρ ──▶ solver ρ s
   │ p                │ q
   ▼                  ▼
  p s  ≤  loss (q (ρ s))  ≤  loss ε
           reduction       monotonicity and hardness
```

A restricted solver set can be supplied as a subtype, so `ρ` maps admitted solvers to admitted
solvers; `Games.win_le_of_reduction` uses this form for its selected winners. No real
arithmetic, metric or category is assumed. The concrete game instance uses real-valued winning
probabilities; the `ℝ≥0` error budgets bounding distances are a separate notion.

## Main results

* `Problem.performance_le_of_reduction`: CR18 equation (4.3) between independent solver types
  and performance spaces
-/

namespace ConstructiveCryptography.Problem

universe u v w x

/-- **Bounding a source solver through a reduction.** If every solver `s` for `p` satisfies
`p s ≤ loss (q (ρ s))` and every solver `t` for `q` satisfies `q t ≤ ε`, then every `s`
satisfies `p s ≤ loss ε`. CR18 equation (4.3), printed p. 87: `p ≤ λ q ρ`; the source's
`λ` (lambda) is `loss` here. Higher performance is better, so each `≤` below bounds how well
a solver performs. -/
theorem performance_le_of_reduction
    -- `Solver` is the type of source solvers and `OtherSolver` the type of target solvers;
    -- they may differ and need not be functions.
    {Solver : Type u} {OtherSolver : Type v}
    -- Ω (Omega) contains source performance values and Λ (Lambda) target values; in each,
    -- higher means at least as good. A preorder suffices where CR18 asks for a partial order,
    -- since antisymmetry is unused.
    {Ω : Type w} {Λ : Type x} [Preorder Ω] [Preorder Λ]
    -- `p s : Ω` is the performance of a source solver `s : Solver`.
    (p : Solver → Ω)
    -- `q t : Λ` is the performance of a target solver `t : OtherSolver`.
    (q : OtherSolver → Λ)
    -- ρ (rho) is the reduction: it turns a source solver `s` into a target solver `ρ s`.
    (ρ : Solver → OtherSolver)
    -- `loss` maps a target performance bound in Λ back to a source bound in Ω; it relates
    -- performance values only, not running time.
    (loss : Λ → Ω)
    -- `hloss` says `x ≤ y` implies `loss x ≤ loss y`: translating a bound preserves order.
    (hloss : Monotone loss)
    -- ε (epsilon) is a uniform target-performance bound, hence an element of Λ.
    {ε : Λ}
    -- `reduction` bounds each `p s` by `loss` applied to the performance `q (ρ s)` of `ρ s`.
    (reduction : ∀ s, p s ≤ loss (q (ρ s)))
    -- `hardness` bounds the performance `q t` of every target solver `t` by ε.
    (hardness : ∀ t, q t ≤ ε)
    -- `s` is the source solver whose performance `p s` is concluded to be at most `loss ε`.
    (s : Solver) : p s ≤ loss ε :=
  -- `p s ≤ loss (q (ρ s))` by the reduction, and `≤ loss ε` by hardness of `ρ s` and
  -- monotonicity of `loss`.
  (reduction s).trans (hloss (hardness (ρ s)))

end ConstructiveCryptography.Problem

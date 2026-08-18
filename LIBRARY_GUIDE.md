# Library guide

`THEORY.md` states the mathematics. This describes how it is rendered in Lean.

## Modules

**`AbstractCryptography/Refinement/`** — MauRen11 §3. `Par`, `HasReduction`,
`Reduces`, and Definition 7's `IsSeriallyComposable`, `IsContextInsensitive`,
`IsGenerallyComposable` — the same composition laws as MauRen16 Lemma 1 and
CR18 Lemma 5.1, so `Basic` is MR16-track. `StepwiseRefinement` adds Appendix
A's construction trees and Theorem 3 (MR11-DEFERRED — see LEDGER PROVENANCE
FENCE). No resources, no metric.

**`AbstractCryptography/Specification/`** — a specification is a `Set Φ`.
`Basic` defines `Constructs π R S :⇔ π • R ⊆ S` and everything needing only a
`MulAction`. `Parallel` holds what additionally needs `‖`. `Relaxation` is the
generic `φ : Φ → 2^Φ` calculus. `Filtered` is the choice-free endpoint-pattern
specialization motivated by MauRen11 §7 and grounded in LiuMau20 §§2.4–2.5, so
it is MR16-track; `ChoiceSetting` is the literal §§4–5, 7 layer and `TwoParty`
is Appendix C (both MR11-DEFERRED — see LEDGER PROVENANCE FENCE).

**`AbstractCryptography/Metric/`** — `Nonexpansion` carries `≈[ε]` and the two
non-expansion mixins (MauRen16 Definition 2); `Epsilon` the scalar ε-relaxation
over a `PseudoEMetricSpace`. Both are MR16-track and are what the random-systems
carrier instantiates. `Distinguisher` (the distinguisher-induced pseudo-metric),
`ReductionRelaxation` (the distinguisher-indexed budgets, split out of `Epsilon`
on 2026-08-17), `Simulation`, and `Behaviour` — which takes the carrier up to
Definition 14's `≈`, a distinguisher class plus the algebra on presentations
yielding `EMetricSpace`, `MulAction`, `Par`, `SMulParClass` and both
non-expansion mixins on the quotient — are MR11-DEFERRED (see LEDGER PROVENANCE
FENCE).

**`AbstractCryptography/Algebra/`** — `Attachment` is MauRen11 Definition 14 at
a fixed interface set. `Indexed` is the interface-indexed algebra, where
parallel composition takes `Res I` and `Res J` to `Res (I ⊕ J)`. `Star` is the
`∗`-relaxation and the right-outbound `⟦`.

**`ConstructiveCryptography/`** — `Multiparty/Basic` is the per-dishonest-set
construction; `Generalizations/ContextRestricted` replaces the quantified
environment by a declared set of admissible contexts, and states every one of
its constructions over a distinguisher class, so it and
`Multiparty/GameMetric` are MR11-DEFERRED (see LEDGER PROVENANCE FENCE) and
the `ConstructiveCryptography` root imports neither.

**`AbstractCryptography/Tactics/`** — automation. Nothing mathematical imports
it. `SemanticRegistry` is separate: it defines the `@[crypto_rule]` attribute
used to tag declarations, which is metadata rather than automation.

## Conventions

Only what Mathlib lacks is declared here. Converters are a `Monoid`,
attachment a `MulAction`, distance a `PseudoEMetricSpace`. The library
contributes `Par`, `SMulParClass`, `IsNonexpandingSMul`, `IsNonexpandingPar`,
and `IndexedPar`.

Distances are `ℝ≥0∞` through `edist`, never `NNReal` — `⊤` must be expressible.
The metric is a *pseudo*-metric: `edist R S = 0` does not force `R = S` unless
the carrier is already quotiented by behavioural equivalence.

Properties are mixins over instance arguments rather than fields of a bundled
structure, so a consumer needing only `‖` need not supply a converter monoid,
and there are no diamonds.

Names are full words. `Foo/Basic.lean` means the core definitions of `Foo`; it
is not a default name for a file with no better one.

## Dependency direction

`Refinement` → `Specification` → `Metric` → `Algebra` → `ConstructiveCryptography`.
No module under `AbstractCryptography/` imports `ConstructiveCryptography`.

## Building

```
lake build
```

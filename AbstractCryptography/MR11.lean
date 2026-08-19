/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Metric.Distinguisher
import AbstractCryptography.Metric.Behaviour
import AbstractCryptography.Metric.ReductionRelaxation
import AbstractCryptography.Metric.Simulation
import AbstractCryptography.Specification.ChoiceSetting
import AbstractCryptography.Specification.TwoParty
import AbstractCryptography.Refinement.StepwiseRefinement

/-!
# The quarantined MauRen11 surface

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

The working discipline is **MR16-only** until an explicit MR11 reconciliation.
This root collects every AbstractCryptography module whose objects are
MauRen11-specific, so that the MR16-track root `AbstractCryptography` can
import none of them and a consumer that genuinely wants the MauRen11 surface
asks for it by name.

Nothing here is deleted, deprecated, or weakened: every declaration keeps its
statement and its proof, and `lake build` keeps compiling it under the
`AbstractCryptographyMR11` target.  What changes is only who may import it.

| module | why it is fenced |
|---|---|
| `Metric.Distinguisher` | `DistinguisherClass` is MauRen11 Definition 15/16; `edistD` is §6.1.  MauRen16 formalizes no distinguisher class — one informal sentence (§3.1) defers it. |
| `Metric.Behaviour` | the carrier taken up to the zero set of `edistD`, i.e. MauRen11 Definition 14 read through the class. |
| `Metric.ReductionRelaxation` | Jost Definition 2.2.9 / JM20 Definition 3 at a budget indexed by `D.tests`, plus the bridge to the scalar ball. |
| `Metric.Simulation` | Jost Definition 2.2.12 stated as `π•ℛ ⊆ D.reductionRelaxation ε (σ•𝒮)`. |
| `Specification.ChoiceSetting` | MauRen11 §§4–5, 7: choice settings, complete factorizable relations, Definitions 8–11 and 18, Theorem 2. |
| `Specification.TwoParty` | MauRen11 Appendix C: Definition 20, equation (5), Theorem 4. |
| `Refinement.StepwiseRefinement` | MauRen11 Appendix A: Definition 19 and Theorem 3. |

The MR16 track keeps the scalar `ε`-ball (`Metric.Epsilon`), the two
non-expansion mixins (`Metric.Nonexpansion`, MauRen16 Definition 2), the
`∗`-relaxation and indifferentiability (`Algebra.Star`, CR18 Definition 5.9 and
MauRen16 Lemma 5), the specification calculus, and the endpoint-pattern
filtered specifications (`Specification.Filtered`).
-/

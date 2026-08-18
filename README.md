# Constructive Cryptography

A Lean 4 formalization of the Maurer-school Constructive Cryptography framework:
the abstract specification calculus, the resource algebra, and the constructive
layer built on them.

## The layers

```
Specification calculus        specifications are sets; a construction is an inclusion
      MauRen16 §2             𝓡 ─π→ 𝓢  :⟺  π𝓡 ⊆ 𝓢

Resource algebra              interfaces, converters, parallel composition,
      MauRen11 §6 Def. 14     and a non-expanding pseudo-metric

Constructive Cryptography     protocols, relaxations, multi-party constructions
      Jost §2.2 · LiuZhang Ch. 3–4
```

`THEORY.md` states the whole thing formally — every definition, axiom and law,
with its source. It is implementation-independent.

## Layout

| directory | contents |
|---|---|
| `AbstractCryptography/Refinement/` | components, constructors, reduction, step-wise refinement |
| `AbstractCryptography/Specification/` | the construction relation and its laws |
| `AbstractCryptography/Metric/` | pseudo-metric, distinguishers, non-expansion, ε-relaxation |
| `AbstractCryptography/Algebra/` | converter attachment, the interface-indexed algebra, `∗`-relaxation |
| `ConstructiveCryptography/` | multi-party constructions, context-restricted constructions |
| `AbstractCryptography/MR11.lean` | the fenced MauRen11 surface — see below |

### The MauRen11 provenance fence (MR11-DEFERRED)

The working discipline is **MR16-only** until an explicit MR11 reconciliation
task, so the `AbstractCryptography` and `ConstructiveCryptography` roots import
no MauRen11-specific module. The distinguisher class and its metric, the
carrier taken up to that metric, the distinguisher-indexed relaxation and the
simulation notion stated over it, the choice-setting layer, the two-party case
and step-wise refinement are collected behind `AbstractCryptography.MR11` and
built by the `AbstractCryptographyMR11` target. Nothing is deleted or weakened;
`scripts/ledgerAudit.sh` fails any MR16-track import of a fenced module. The
rule, the classification and the machine-readable list are in `LEDGER.md`
"PROVENANCE FENCE (MR11-DEFERRED)".

Converters form a `Monoid`, attachment is a `MulAction`, and distance is
Mathlib's `PseudoEMetricSpace`. Only what Mathlib lacks is declared here.

## Building

```
lake exe cache get     # if a Mathlib cache is available
lake build
```

Requires the Lean toolchain pinned in `lean-toolchain`.

## Reading order

Start at `AbstractCryptography/Specification/Basic.lean` for the construction
relation, then `AbstractCryptography/Algebra/Attachment.lean` for the algebra.
`THEORY.md` maps every numbered law to the source it comes from.

## References

- Maurer, Renner. *Abstract Cryptography.* ICS 2011.
- Maurer, Renner. *From Indifferentiability to Constructive Cryptography.* TCC 2016.
- Jost, Maurer. *Overcoming Impossibility Results in Composable Security using
  Interval-Wise Guarantees.* CRYPTO 2020.
- Jost. *Towards Practical and Sound Cryptography from Composable Security.*
  PhD thesis, ETH Zurich, 2020.
- Liu-Zhang. *Multi-Party Computation: Definitions, Enhanced Security Guarantees
  and Efficiency.* PhD thesis, ETH Zurich, 2021.

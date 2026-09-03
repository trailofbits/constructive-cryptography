# Constructive Cryptography in Lean 4

A Lean 4 formalization of the Maurer-school theory of cryptographic systems:
finitely supported probability, Maurer's random systems and their proof
techniques, the abstract specification calculus, and the constructive layer
built on them.

The tree contains no `sorry` and declares no `axiom`. The headline theorems
depend only on `propext`, `Classical.choice` and `Quot.sound`.

## Structure

Four libraries, each with an import root at the top level.

```
Probability               finitely supported signed distributions, expectation,
                          statistical distance, couplings, entropy, divergence

RandomSystems             discrete systems, environments and transcripts,
                          converters, the universe Φ and its metric, games,
                          and the proof techniques

AbstractCryptography      specifications are sets; a construction is an
                          inclusion   𝓡 —π→ 𝒮  :⟺  π𝓡 ⊆ 𝒮
                          with relaxations and a non-expanding pseudo-metric

ConstructiveCryptography  multi-party constructions, one guarantee per
                          dishonest set; context-restricted constructions
```

`Probability` and `AbstractCryptography` depend on nothing else in the
repository. `RandomSystems` imports both. `ConstructiveCryptography` imports
`AbstractCryptography` only.

The abstract layer never names a system. The random-systems layer is a carrier
for it: it defines the universe `Φ` of probabilistic discrete systems, the
converter monoid `Σ` acting on it, and the distinguishing pseudo-metric, and it
discharges the axioms the abstract layer asks for. The abstract theorems then
land on concrete systems by instance resolution. `RandomSystemsReceipts.lean`
is that join written out: one `example` per abstract theorem, stated on the
concrete carrier.

Two documents accompany the code. `THEORY.md` states the mathematics as
implemented, definition by definition, each with its source and any deviation
from it. `LIBRARY_GUIDE.md` gives a reading order and says where each notion
lives.

### Directory map

| path | contents |
|---|---|
| `Probability/` | the signed carrier `Distribution A = A →₀ ℝ`, expectation and conditioning, statistical distance, couplings (pairwise, multi-way, fibered), counting and universal hashing, min-entropy and Shannon entropy, divergence |
| `RandomSystems/System/` | deterministic and probabilistic discrete systems, environments and transcripts, the advantage `Adv⊥`, class distance and its attainment, the behaviour quotient, the universe `Φ`, parallel composition, blocking, filters, attachment, absorption, the pseudo-emetric |
| `RandomSystems/Converter/` | converters in two presentations, cascade and combine with their realization theorems, interface attachment, the generated monoid `Σ` |
| `RandomSystems/Game/`, `RandomSystems/Interface/` | the game relaxation; interfaces |
| `RandomSystems/Technique/` | the proof techniques, listed below |
| `AbstractCryptography/Specification/` | the construction relation and its laws, parallel composition, the relaxation calculus, blocking, the admitted constructor class and its cost bounds, filtered and parameterized specifications, choice settings, the two-party case |
| `AbstractCryptography/Metric/` | non-expansion, the scalar `ε`-relaxation, the distinguisher-induced metric, the behaviour quotient, reduction relaxations, simulation |
| `AbstractCryptography/Algebra/` | converter attachment as a monoid action, the interface-indexed algebra, the `∗`-relaxation, indifferentiability |
| `AbstractCryptography/Refinement/` | components, constructors, reductions, step-wise refinement |
| `AbstractCryptography/Tactics/` | a deterministic proof-language layer and a controlled-natural-language frontend over it |
| `AbstractCryptography/EventAlgebra.lean` | event algebras, an axis orthogonal to the construction ladder |
| `ConstructiveCryptography/` | the multi-party construction notion with per-dishonest-set guarantees, context-restricted constructions, and a game bound |
| `Tests/` | files of checked `example`s: surface smoke tests, `calc`-chain evidence, non-vacuity witnesses, and tests of the proof language |

`ConstructiveCryptographyDemo.lean` is a worked two-step composition, a MAC
followed by encryption to a secure channel, and then an impossibility
calculation. It is written twice, once in ordinary Lean and once in the
controlled language.

## Proof techniques

`RandomSystems/Technique/` collects the reusable arguments. Each module's
header quotes the printed statement it formalizes and names its endpoints.

- **Conditional equivalence.** Two systems that agree while a monotone
  condition holds are distinguishable only through the event that breaks it.
  The fundamental lemma of game playing is
  `PDG.fundamental_lemma_of_game_playing`; the adaptive endpoint is
  `PDG.conditional_equivalence_theorem`, and its counting form
  `PDG.conditional_equivalence_theorem_infWinnability` follows by composing
  with `ν = ω` below.
- **Blind winning.** `PDG.conditional_equivalence_theorem_blind` bounds the
  adaptive advantage by the non-adaptive winning probability. That this is
  strictly stronger is itself a theorem
  (`PDG.exists_blindSupWinProb_lt_supWinProb`), and the environment-side and
  converter-side readings of "blind" are proved to agree in both directions
  (`PDG.supWinProb_blockRepliesGame`).
- **Winnability.** Lanzenberger's `ν = ω`: the adversarial winning probability
  equals the static infimum winnability, and the infimum is attained
  (`PDG.winnability_theorem`).
- **Completeness of the bad-event method.** MPR07 Lemma 5(iv) and its
  footnote 16: for a restricted-equivalent pair whose common not-won law is
  the pointwise minimum, the conditional-equivalence bound is an equality
  (`PDS.winning_probability_attainment_theorem`,
  `PDG.advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min`). A lossy
  application can therefore be told apart from a real gap.
- **Attainment and coupling.** Lanzenberger's `Δ = Adv⊥` and the coupling
  theorem, on the finite shared-domain slice
  (`PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded`,
  `PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded`);
  the inequality `PDS.advFullyDefined_le_classDistance` is unconditional.
- **The H-coefficient technique.** Transcripts factor into an environment
  factor and a system factor. A ratio bound on the system factors over the
  good transcripts, plus a bound on the ideal law's bad mass, gives
  `Adv⊥ ≤ δ_b + ε` (`PDS.h_coefficient_theorem`).

The metric these techniques feed is Mathlib's. `Φ` carries a
`PseudoEMetricSpace` whose `edist` is the symmetrization of `Adv⊥`
(`RandomSystems.edist_def`), converters are non-expanding as an instance, and
MauRen16's two composition lemmas land together as
`RandomSystems.constructs_epsilonRelaxation_trans_at`. On the behaviour
quotient the same distance separates points, giving an `EMetricSpace`
(`RandomSystems.PDS.Behaviour`).

On the probability side, the library adds what Mathlib lacks: min-entropy and
the collision calculus, Shannon entropy with the equality condition of each
bound, and Kullback–Leibler divergence with Pinsker's inequality
(`Probability.statDist_le_sqrt_klDiv_div_two`), checked against Mathlib's
`klDiv` on the `Fintype` probability slice.

## Boundaries

Some headline hypotheses are mathematical, not bookkeeping.

- Attainment, `ν = ω`, and the counting endpoint hold on a slice: a finite
  query alphabet, one common domain, and a query bound. Off the slice the
  equalities are false on this carrier, because a refusal is observable.
- Parallel composition on `Φ` is defined at a splitting of the query alphabet,
  so parallel non-expansion is a conditional theorem with named hypotheses
  (`RandomSystems.smul_parF`, `RandomSystems.edist_parF_parF_le`) rather than
  an instance. The parallel half of the composition corollary is assembled
  from these (`constructs_epsilonRelaxation_parF`).
- There is no computational setting. The admitted constructor class `Γ` and
  its cost-bounded family keep the cost function a parameter. The
  interface-indexed algebra is stated without instances, and the connection
  action at the interface-addressed carrier is the open frontier recorded at
  the end of `RandomSystemsReceipts.lean`.

## The MauRen11 fence

The working discipline is MauRen16-only until an explicit MauRen11
reconciliation. The four import roots therefore import no MauRen11-specific
module. The distinguisher class and its metric, the carrier taken up to that
metric, the distinguisher-indexed relaxation and the simulation notion stated
over it, the choice-setting layer, the two-party case, and step-wise
refinement are collected behind `AbstractCryptography.MR11` and built by the
`AbstractCryptographyMR11` target. Nothing is weakened; a consumer that wants
the MauRen11 surface imports it by name, as the demo and two test targets do.

## Building

Requires the Lean toolchain pinned in `lean-toolchain` and the Mathlib revision
pinned in `lake-manifest.json`.

```
lake exe cache get     # if a Mathlib cache is available
lake build             # the default targets
```

The default targets are the four libraries, `AbstractCryptographyMR11`,
`EventAlgebra`, and `RandomSystemsReceipts`. The test libraries and the demo
are built by name, for example

```
lake build ConstructiveCryptographyDemo AbstractCryptographySelectedSurfaceTests
```

Each test target is a file of `example`s that must elaborate, so a regression
is a build failure. `-KdisableRandomSystems=true` switches off `RandomSystems`
and `RandomSystemsReceipts` for a fast abstract-only build.

## Conventions

Only what Mathlib lacks is declared here. Converters form a `Monoid`,
attachment is a `MulAction`, and distance is Mathlib's `PseudoEMetricSpace`;
the library contributes `Par`, `SMulParClass`, `IsNonexpandingSMul`,
`IsNonexpandingPar` and `IndexedPar`. Distances are `ℝ≥0∞` through `edist`,
never `NNReal`, so that `⊤` is expressible. Properties are mixins over instance
arguments rather than fields of a bundled structure. Names are full words.

## Sources

The source hierarchy is MauRen16 > Jost > LiuMau20 > Lanzenberger. CR18 is a
fallback, cited for provenance and, flagged at each site, as the source of a
few object definitions no primary supplies.

- Maurer, Renner. *Abstract Cryptography.* ICS 2011. (`MauRen11`)
- Maurer, Renner. *From Indifferentiability to Constructive Cryptography (and
  Back).* TCC 2016. (`MauRen16`)
- Jost, Maurer. *Overcoming Impossibility Results in Composable Security using
  Interval-Wise Guarantees.* CRYPTO 2020. (`JM20`)
- Jost. *Towards Practical and Sound Cryptography from Composable Security.*
  PhD thesis, ETH Zurich, 2020.
- Liu-Zhang, Maurer. *Synchronous Constructive Cryptography.* TCC 2020.
  (`LiuMau20`)
- Liu-Zhang. *Multi-Party Computation: Definitions, Enhanced Security Guarantees
  and Efficiency.* PhD thesis, ETH Zurich, 2021.
- Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification.*
  PhD thesis, ETH Zurich (DISS ETH 29554).
- Lanzenberger, Maurer. *Coupling of Random Systems.* TCC 2020.
- Maurer. *Indistinguishability of Random Systems.* EUROCRYPT 2002.
- Maurer. *Conditional Equivalence of Random Systems and Indistinguishability
  Proofs.* ISIT 2013.
- Maurer, Pietrzak, Renner. *Indistinguishability Amplification.* CRYPTO 2007.
  (`MPR07`)
- Matt, Maurer, Portmann, Renner, Tackmann. *Toward an Algebraic Theory of
  Systems.* 2018.
- Gegier, Maurer. *Event algebras.* ePrint 2026/1071.
- Maurer. *Cryptography Foundations.* Lecture notes, ETH Zurich, 2018.
  (`CR18`; fallback)

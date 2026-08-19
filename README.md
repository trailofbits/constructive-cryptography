# Abstract and Constructive Cryptography in Lean 4

A Lean 4 formalization of the Maurer-school theory of cryptographic systems, in
four layers that meet in one repository: finitely supported probability, Maurer's
random systems, the abstract specification calculus, and the constructive layer
built on them.

The abstract layer is carrier-free — it never names a system. The random-systems
layer is a carrier for it: it defines a universe `Φ` of probabilistic discrete
systems, a converter monoid `Σ` acting on it, and a distinguishing pseudo-metric,
and it discharges the axioms the abstract layer asks for, so the abstract
theorems land on concrete systems by instance resolution.
`RandomSystemsReceipts.lean` is that join, written out as one `example` per
abstract theorem.

## The layers

```
Probability                     finitely supported signed distributions, expectation,
  (no system model)             statistical distance, couplings, entropy, divergence

RandomSystems                   Lanzenberger Ch. 2, CR18 Ch. 3: deterministic and
  Φ, Σ, Adv⊥, games,            probabilistic discrete systems, environments and
  proof techniques              transcripts, converters, the universe Φ, the metric,
                                monotone conditions, and the proof techniques

AbstractCryptography            MauRen11 §§3, 6 · MauRen16 §§2-4: specifications are
  carrier-free                  sets, a construction is an inclusion
                                    𝓡 —π→ 𝒮  :⟺  π𝓡 ⊆ 𝒮
                                with relaxations and a non-expanding pseudo-metric

ConstructiveCryptography        LiuMau20 §2.4: one guarantee per dishonest set;
                                Jost §4.2: context-restricted constructions
```

Import direction: `Probability` depends on nothing else in the repository;
`AbstractCryptography` depends on nothing else in the repository;
`RandomSystems` imports both; `ConstructiveCryptography` imports
`AbstractCryptography` only. (Checked by transitive import closure.)

`THEORY.md` states the theory as implemented, definition by definition, with its
sources. `LIBRARY_GUIDE.md` says where each notion lives and in what order to
read it.

## Layout

| path | lines | contents |
|---|---:|---|
| `Probability/` | 11.5k | 16 modules: `Distribution` (signed `A →₀ ℝ`), `Expectation`, `Conditional`, `Lift`, `StatisticalDistance`, `Coupling`, `MultiCoupling`, `FiberCoupling`, `Counting`, `UniversalHash`, `Entropy`, `ShannonEntropy`, `Divergence`, `DistributionMeasure`, and two simp-attribute modules |
| `RandomSystems/System/` | — | 36 modules: DDS/DDE/PDS, transcripts, the class distance and its attainment, the behaviour quotient, the universe `Φ`, parallel composition, blocking, filters, attachment, absorption, the pseudo-emetric, games and winnability |
| `RandomSystems/Converter/` | — | 8 modules: CR18 Definitions 3.8-3.9 converters in two presentations, cascade and combine with their realization theorems, interface attachment, the generated `Σ` |
| `RandomSystems/Technique/` | — | conditional equivalence, blind winning, completeness of the bad-event method, the H-coefficient factorization (plus two empty placeholder modules) |
| `RandomSystems/{Game,Interface}/` | — | the game-relaxation and interface roles (plus four empty placeholder modules) |
| `RandomSystems/` total | 44.2k | 58 modules |
| `AbstractCryptography/Refinement/` | — | MauRen11 §3: components, constructors, reductions, Definition 7's three composability properties, step-wise refinement |
| `AbstractCryptography/Specification/` | — | 11 modules: the construction relation and its laws, parallel, the generic relaxation calculus, blocking and `⟦`, the admitted constructor class `Γ` and its cost-bounded family, interface-indexed attachment, filtered specifications, parameterized resources, choice settings, the two-party case |
| `AbstractCryptography/Metric/` | — | the two non-expansion mixins, the scalar `ε`-relaxation, the distinguisher-induced metric, the behaviour quotient, indexed budgets, simulation |
| `AbstractCryptography/Algebra/` | — | converter attachment (`Monoid`/`MulAction`), the interface-indexed algebra, the `∗`-relaxation, `⟦`, indifferentiability |
| `AbstractCryptography/Tactics/` | — | a deterministic proof-language layer and a controlled-natural-language frontend over it; no mathematics |
| `AbstractCryptography/EventAlgebra.lean` | — | GegMau26's event algebras — an orthogonal axis, not a rung of the ladder |
| `AbstractCryptography/` total | 6.9k | 29 modules |
| `ConstructiveCryptography/` | 1.6k | the multi-party construction notion, LiuMau20 §2.4's per-dishonest-set guarantees, Jost §4.2's context-restricted constructions, and a game bound |
| `Tests/` | 1.5k | 8 non-default modules of checked `example`s: surface smoke tests, `calc`-chain firing evidence, non-vacuity witnesses, proof-language and controlled-language tests |

Root modules: `Probability.lean`, `RandomSystems.lean`, `AbstractCryptography.lean`,
`ConstructiveCryptography.lean` (import roots), `RandomSystemsReceipts.lean` (the
tower at one carrier), and `ConstructiveCryptographyDemo{,Support}.lean` (a
worked two-step composition plus an impossibility calculation).

## Building

Requires the Lean toolchain pinned in `lean-toolchain` (`v4.29.0`) and the
Mathlib revision pinned in `lake-manifest.json`.

```
lake exe cache get     # if a Mathlib cache is available
lake build             # the default targets
```

The default targets are `AbstractCryptography`, `AbstractCryptographyMR11`,
`EventAlgebra`, `ConstructiveCryptography`, `Probability`, `RandomSystems` and
`RandomSystemsReceipts`. The non-default targets are built by name:

```
lake build ConstructiveCryptographyMultipartyComputation
lake build ConstructiveCryptographyDemo
lake build AbstractCryptographySelectedSurfaceTests \
           AbstractCryptographyProofAutomationTests \
           AbstractCryptographyCalcChainTests \
           AbstractCryptographyContextRestrictedTests \
           AbstractCryptographyIndexedRelaxationTests \
           AbstractCryptographyControlledNaturalLanguageTests \
           AbstractCryptographyConstructionWorkflowTests \
           ConstructiveCryptographySelectedSurfaceTests
```

The test targets are Lake libraries over the `Tests.*` modules; each is a file of
`example`s that must elaborate, so a regression shows up as a build failure.

`RandomSystems` and `RandomSystemsReceipts` can be switched off for a fast
abstract-only build with `-KdisableRandomSystems=true`.

## Scope

**Proved.** The tree contains no `sorry` and declares no `axiom`; the headline
results below were checked with `#print axioms` and depend only on `propext`,
`Classical.choice` and `Quot.sound`.

* *The metric and its instances.* `Φ` carries a `PseudoEMetricSpace` whose
  `edist` is the symmetrization of the transcript advantage `Adv⊥`
  (`RandomSystems.edist_def`), agreeing with `Adv⊥` on equal-weight laws
  (`edist_eq_advFullyDefined_of_weight_eq`). MauRen16 Definition 2's
  non-expansion holds for the converter monoid as an instance, so MauRen16
  Lemma 1 composed with Lemma 2 lands as
  `RandomSystems.constructs_epsilonRelaxation_trans_at`. On the behaviour
  quotient the same distance separates points, giving a genuine `EMetricSpace`
  (`RandomSystems.PDS.Behaviour`).
* *Attainment.* Lanzenberger Theorem 2.31 (`Δ = Adv⊥`) and Theorem 2.32 (the
  coupling theorem) are proved on the finite shared-domain slice
  (`PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded`,
  `PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded`);
  `PDS.advFullyDefined_le_classDistance` is unconditional.
* *Games and winnability.* Lanzenberger Theorem 2.37, `ν = ω` — the adversarial
  winning probability equals the static infimum winnability, with the infimum
  attained — is `PDG.winnability_theorem`.
* *Conditional equivalence.* The fundamental lemma of game playing
  (`PDG.fundamental_lemma_of_game_playing`) and the adaptive endpoint
  `PDG.conditional_equivalence_theorem`; the counting form
  `PDG.conditional_equivalence_theorem_infWinnability` obtained by composing
  with `ν = ω`.
* *Blind winning.* `PDG.conditional_equivalence_theorem_blind` bounds the
  *adaptive* advantage by the *non-adaptive* winning probability; that this is
  strictly stronger is a theorem, not a belief
  (`PDG.exists_blindSupWinProb_lt_supWinProb`), and the source's claim that the
  environment-side and converter-side readings of "blind" agree is proved in
  both directions (`PDG.supWinProb_blockRepliesGame`).
* *Completeness of the bad-event method.* MPR07 Lemma 5(iv) and its footnote 16
  (`PDG.advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min`,
  `PDS.winning_probability_attainment_theorem`): a restricted-equivalent pair
  whose common not-won law is the pointwise minimum turns the bound into an
  equality.
* *The H-coefficient technique.* The transcript factorization into an
  environment factor and a system factor, and the endpoint
  `PDS.h_coefficient_theorem`: a ratio on system factors over the good
  transcripts plus a bound on the ideal law's bad mass gives `Adv⊥ ≤ δ_b + ε`.
* *Information theory.* Min-entropy and the collision calculus, the Shannon
  layer with the equality condition of each bound, and Kullback-Leibler
  divergence with Pinsker's inequality
  (`Probability.statDist_le_sqrt_klDiv_div_two`), checked against Mathlib's
  `klDiv` on the `Fintype` probability slice (`Distribution.klDiv_toPMF`).
  Mathlib has no entropy of a distribution and no Pinsker inequality.
* *The converter monoid.* `Σ` is a submonoid of `Function.End Φ` generated by
  relabelling, blocking and attachment, so composition closure and the action
  laws are definitional; the order-invariance axiom the abstract layer asks for
  is discharged (`RandomSystems.Converter.pairwiseOrderInvariant_attach`).

**Conditional by design.** Several headlines carry hypotheses that are not
bookkeeping and cannot be dropped.

* Attainment, `ν = ω`, and the counting endpoint hold on a *slice*: a finite
  query alphabet, one common Definition-2.14 domain, and a query bound. Without
  it the equality is false, not merely unproved — refusal is observable on this
  carrier, so an environment reading refusals separates systems that no static
  pair of representatives separates.
* `conditional_equivalence_theorem_blind` additionally needs a normalized `T`
  and a shared domain; the tree also proves that the *bound* does not
  (`conditional_equivalence_theorem_blind_subsumed`).
* Parallel composition on `Φ` is defined at a splitting of the query alphabet
  and elected from the left argument's own face, so the unconditional
  `SMulParClass` and `IsNonexpandingPar` instances are unobtainable on this
  signed, arbitrary-weight carrier. They are replaced by conditional theorems
  with the hypotheses named (`RandomSystems.smul_parF`,
  `RandomSystems.edist_parF_parF_le`), from which the parallel half of the
  composition corollary is assembled (`constructs_epsilonRelaxation_parF`).

**Not yet.** No computational setting: the admitted constructor class `Γ` and
its cost-bounded family `costBounded γ c` keep the cost function a parameter,
and no performance or efficiency model is built. The interface-indexed algebra
(`Algebra/Indexed.lean`) is stated but has no instances. The pseudo-emetric and
non-expansion instances for the *connection* action at the interface-addressed
carrier `PDS (P × X) Y` do not fire yet — the frontier is written out at the end
of `RandomSystemsReceipts.lean`. Ten modules under `RandomSystems/` are empty
placeholders. No concrete cryptographic scheme is included here.

## The MauRen11 provenance fence

The working discipline is MauRen16-only until an explicit MauRen11
reconciliation, so the `AbstractCryptography`, `ConstructiveCryptography`,
`ConstructiveCryptography.MultipartyComputation` and `RandomSystems` roots import
no MauRen11-specific module. The distinguisher class and its metric, the carrier
taken up to that metric, the distinguisher-indexed relaxation and the simulation
notion stated over it, the choice-setting layer, the two-party case, and
step-wise refinement are collected behind `AbstractCryptography.MR11` and built
by the `AbstractCryptographyMR11` target. Nothing is deleted or weakened; every
declaration keeps its statement and its proof, and a consumer that wants the
MauRen11 surface asks for it by name — as `ConstructiveCryptographyDemo` and two
of the test targets do. (Verified by transitive import closure.)

## Conventions

Only what Mathlib lacks is declared here. Converters form a `Monoid`, attachment
is a `MulAction`, and distance is Mathlib's `PseudoEMetricSpace`; the library
contributes `Par`, `SMulParClass`, `IsNonexpandingSMul`, `IsNonexpandingPar` and
`IndexedPar`. Distances are `ℝ≥0∞` through `edist`, never `NNReal` — `⊤` must be
expressible. Properties are mixins over instance arguments rather than fields of
a bundled structure. Names are full words.

## Sources

The source hierarchy is MauRen16 > Jost > LiuMau20 > Lanzenberger's thesis.
CR18 is a fallback, cited for provenance and — flagged at each site — as the
source of a handful of object definitions that no primary supplies.

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
- Matt, Maurer, Portmann, Renner, Tackmann. *Toward an Algebraic Theory of
  Systems.* 2018.
- Gegier, Maurer. *Event algebras.* ePrint 2026/1071.
- Cachin, Maurer, Renner. *Cryptography Foundations* / *Lecture Notes on
  Cryptography*, ETH Zurich. (`CR18`; fallback)

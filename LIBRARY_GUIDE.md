# Library guide

`THEORY.md` states the mathematics; this says where each piece lives, in what
order to read it, and what to know before extending it.

## Reading order

1. **`Probability/Distribution.lean`** — the signed finitely supported carrier
   `Distribution A = A →₀ ℝ`, and the three layers (signed, `NonNeg`,
   `isProbDist`) that every later hypothesis is measured against.
2. **`Probability/StatisticalDistance.lean`** — `statDist`, the distance every
   system-level bound bottoms out in.
3. **`RandomSystems/System/DiscreteSystem.lean`** and
   **`RandomSystems/System/Environment.lean`** — the DDS, the environment in
   both presentations, the transcript, and `PDS.advFullyDefined` (`Adv⊥`), the
   statement-facing distance.
4. **`RandomSystems/System/Phi.lean`** — the universe `Φ` and the discipline
   that a query carries its own type.
5. **`AbstractCryptography/Specification/Basic.lean`** — `Constructs π 𝓡 𝒮 :⇔
   π • 𝓡 ⊆ 𝒮` and its composition law. This is the whole construction notion.
6. **`AbstractCryptography/Algebra/Star.lean`** — the relaxations whose
   parameter is a converter class, the simulator recipe, indifferentiability.
7. **`RandomSystemsReceipts.lean`** — every abstract theorem restated as an
   `example` on the one concrete carrier, reached by instance resolution alone.
   Read it to see what the join actually buys, and its closing `FRONTIER`
   comment to see what has not landed.
8. **`ConstructiveCryptographyDemo.lean`** — a worked two-step composition
   (MAC then encryption to a secure channel) followed by an impossibility
   calculation, presented twice: once in ordinary Lean, once in the controlled
   language.

For proof techniques, go straight to `RandomSystems/Technique/`; each module's
header quotes the printed statement it formalizes and lists its endpoints.

## Modules

### `Probability/`

Independent of any system model; nothing here mentions a system.

**`Distribution`** the carrier, `weight`, `mass`, `marginal`, `fTransform`,
`uniform`, partial conditioning. **`Expectation`** `𝔼_X[f]` with Markov,
Cauchy-Schwarz, Jensen, variance — deliberately free of measure theory.
**`Lift`** the two moves between layers: the Jordan split (Mathlib's
`posPart`/`negPart` on the `Finsupp` lattice, not re-derived) and normalization.
**`Conditional`** the multiplication rule, Bayes, total probability, and three
chain rules including the input/output-interleaved form an interaction transcript
needs. **`StatisticalDistance`** `δ`, the triangle inequality, the partition
lemma, data processing, the min form without `Fintype`. **`Coupling`**,
**`MultiCoupling`**, **`FiberCoupling`** the pairwise coupling lemma in both
halves, the `n`-ary maximal coupling, and the conditional-independence gluing
that lifts a pointwise construction to laws. **`Counting`** carrier-free
arithmetic: falling factorials, the birthday bound, permutation-consistency
masses, gate sums. **`UniversalHash`** `δ`-almost universality with the digest
relation and the length-dependent bound both parameters. **`Entropy`**,
**`ShannonEntropy`**, **`Divergence`** the information theory, in bits for the
entropy ladder and nats for the divergence, each convention pinned to the
statement that needs it. **`DistributionMeasure`** the one-way `isProbDist →
PMF` bridge, sized to its single customer.

### `RandomSystems/`

Depends on `Probability` and on `AbstractCryptography`; it is the carrier that
instantiates the abstract layer.

**`System/DiscreteSystem`, `System/Environment`, `System/ProbabilisticSystem`**
— the DDS on `PFun`, both environment presentations with their transcripts, and
the PDS with Jost's specification layer read on it. `Adv⊥` is defined in
`Environment`.

**`System/ClassDistance`, `System/Attainment`, `System/Behaviour`,
`System/BehaviourAttainment`, `System/MultiDistance`, `System/Example216`,
`System/SingleQuery`** — the two presentations of the distance and the coding
maps between them; Theorems 2.31/2.32 on the finite one-domain slice; Notation
2.19's quotient, on which the distance is a genuine `EMetricSpace`; the
multi-system distance with its two corrected source displays; the worked example
showing the PDS carrier is strictly finer than behaviour.

**`System/Phi`, `System/Par`, `System/ParFace`, `System/ParFrame`,
`System/Parallel`, `System/Relabel`, `System/Connect`, `System/ConnectPhi`,
`System/FullyDefined`, `System/Absorb`, `System/FilterPhi`,
`System/BlockReplies`, `System/ConnectFullyDefined`,
`System/AttachEngineFully`, `System/MetricFullyDefined`,
`System/StarFullyDefined`, `System/ConverterEntry`, `System/RandomObjects`,
`System/ProbabilisticConverter`, `Interface/Interface`** — the carrier and its
algebra. The pseudo-emetric instance is in `MetricFullyDefined`; the
non-expansion generators are in `Absorb`; the interface-indexed attachment
primitive is in `AttachEngineFully`, and `ConverterEntry` is the crossing an
application uses to enter a typed history function into `Σ`.

**`Converter/`** — CR18 Definitions 3.8-3.9 in two presentations with the
realization theorem joining them (`Converter`, `Cascade`), the cascade and
combine equations (`CascadeRealization`, `CombineRealization`, `CascadeLaw`),
attachment at an interface with the order-invariance axiom discharged
(`Attachment`), authored converter implementations (`ConverterImpl`), and the
generated monoid at the interface-tagged carrier (`Sigma`).

**`System/Game`, `System/Winnability`, `Game/GameRelaxation`** — monotone
conditions as upper sets, the PDG, `ν`, `ω`, Theorem 2.37, and CR18 Definition
5.10's game-relaxation.

**`Technique/`** — `ConditionalEquivalence` (the fundamental lemma and the
adaptive endpoint), `BlindWinning` (the non-adaptive endpoint and the two
readings of "blind"), `Completeness` (MPR07 Lemma 5), `HCoefficient` (the
transcript factorization and its endpoint).

**`Notation`, `PartialFunction`** — goal-state display for the landed notations,
and the two `PFun` facts the converter layer rests on.

Where to look for what a name suggests: games are in `System/Game.lean` and
`System/Winnability.lean`, the advantage in `System/Environment.lean`, couplings
in `Probability/`, and data processing in `Probability/StatisticalDistance.lean`.

### `AbstractCryptography/`

Carrier-free throughout: no module here names a system, and none imports
`RandomSystems`, `Probability` or `ConstructiveCryptography`.

**`Refinement/`** — MauRen11 §3. `Par`, `HasReduction`, `Reduces`, and
Definition 7's `IsSeriallyComposable`, `IsContextInsensitive`,
`IsGenerallyComposable` — the same composition laws as MauRen16 Lemma 1.
`StepwiseRefinement` adds Appendix A's construction trees and Theorem 3 (behind
the MauRen11 fence). No resources, no metric.

**`Specification/`** — a specification is a `Set Φ`. `Basic` defines
`Constructs` and everything needing only a `MulAction`; `Parallel` holds what
additionally needs `‖`; `Relaxation` is the generic `φ : Φ → 2^Φ` calculus,
carrier-free; `Outbound` is blocking, `𝓡⟦` and `Unconstructible`; `Interfaces`
is interface-indexed attachment and the grouping into `attachedWithin`;
`ConstructorClass` and `CostBounded` are the admitted class `Γ` and its
efficiency-bounded family; `Filtered` is the choice-free endpoint pattern and
local-simulator theorem; `Parameterized` is CR18 §5.5. `ChoiceSetting` (§§4-5,
7) and `TwoParty` (App. C) are behind the fence.

**`Metric/`** — `Nonexpansion` carries `≈[ε]` and the two non-expansion mixins
(MauRen16 Definition 2); `Epsilon` the scalar `ε`-relaxation over a
`PseudoEMetricSpace`, with JM20 Theorems 2/3 and Corollary 1. Both are on the
MauRen16 track and are what the random-systems carrier instantiates.
`Distinguisher`, `ReductionRelaxation`, `Simulation` and `Behaviour` are behind
the fence.

**`Algebra/`** — `Attachment` is MauRen11 Definition 14 at a fixed interface
set, as `Monoid` + `MulAction` + independent mixins. `Indexed` is the
interface-varying algebra where `‖` takes `Res I` and `Res J` to `Res (I ⊕ J)`;
it is stated but has no instances. `Star` is the `∗`-relaxation, the
right-outbound `⟦`, and indifferentiability.

**`Tactics/`** — automation. Nothing mathematical imports it.
`ProofAutomation` is a deterministic normalization layer with named leaf rules
and explicit construction assemblers; `ControlledNaturalLanguage` is a
paper-readable syntax over the same assemblers, opened with
`open scoped CryptoControlledNaturalLanguage`. Every sentence expands to one
existing `ac_*` command, so simulators, intermediate specifications and error
budgets stay explicit. `SemanticRegistry` is separate: it defines the
`@[crypto_rule]` attribute, which is metadata on mathematical declarations
rather than automation.

**`EventAlgebra.lean`** — GegMau26's event algebras. **Not a rung of this
ladder**: the paper calls them a priori incomparable to the abstract theory of
systems, compatible only at a concrete level satisfying both axiom sets. E1-E4
are not re-axiomatized — a dual Heyting lattice *is* a `CoheytingAlgebra`, so
only E5 is new — and the module carries the forest-order representation and a
lattice valuation with its union bound.

### `ConstructiveCryptography/`

**`ConstructiveCryptography.lean`** is both the import root and the
implementation: `SecurelyConstructs`, MauRen11 §5.1's fixed-`Z` definition with
availability and security. **`Multiparty/Basic`** is LiuMau20 §2.4's
per-dishonest-set construction, the `∗Z`-calculus, the dishonest closure and
adversary structures. **`Generalizations/ContextRestricted`** is Jost §4.2, and
**`Multiparty/GameMetric`** the one declaration indexed by a distinguisher
class; both are behind the fence, so the root imports neither.
**`MultipartyComputation.lean`** is the public root of the multi-party target.

### `Tests/`

Eight non-default modules of checked `example`s: public-surface smoke tests, the
firing evidence for the construction layer's `Trans` instances (every paper
composition written as one `calc`), a usability gate for the context-restricted
phrases, a non-vacuity witness for the indexed relaxation, and positive,
negative and trace tests for the controlled language. They are separate Lake
targets so their carriers and heartbeat cost stay out of the library build.

## Conventions

Only what Mathlib lacks is declared here. Converters are a `Monoid`, attachment
a `MulAction`, distance a `PseudoEMetricSpace`. The library contributes `Par`,
`SMulParClass`, `IsNonexpandingSMul`, `IsNonexpandingPar` and `IndexedPar`.

Distances are `ℝ≥0∞` through `edist`, never `NNReal` — `⊤` must be expressible.
The metric on `Φ` is a *pseudo*-metric: `edist R S = 0` does not force `R = S`
unless the carrier is already quotiented by behavioural equivalence, which is
exactly what `PDS.Behaviour` does and why it carries an `EMetricSpace`.

Properties are mixins over instance arguments rather than fields of a bundled
structure, so a consumer needing only `‖` need not supply a converter monoid,
and there are no diamonds.

Partiality is by undefinedness. There is no error element and no stop symbol;
a system that will not answer is undefined there, and the total presentation
renders that as an observable answer rather than as a distinguished value in the
alphabet.

Each probabilistic statement carries the *weakest* of the three distribution
layers at which it is true. Do not add `NonNeg` or `isProbDist` for tidiness:
the signed generality is what the successor-system and coupling arguments use.

Names are full words. `Foo/Basic.lean` means the core definitions of `Foo`; it
is not a default name for a file with no better one. Declarations are public —
implementation detail goes in a narrow namespace, not behind Lean's `private`.

## Dependency direction

    Probability ←──── RandomSystems ────→ AbstractCryptography ←──── ConstructiveCryptography

`AbstractCryptography` imports nothing else in the repository; `Probability`
imports nothing else in the repository; no module under `AbstractCryptography/`
imports `ConstructiveCryptography` or `RandomSystems`. Within
`AbstractCryptography`, the order is `Refinement` → `Specification` → `Metric` →
`Algebra`.

## Extending it

**Adding a carrier.** Instantiate `Monoid Sigma`, `MulAction Sigma Φ`,
`PseudoEMetricSpace Φ` and `IsNonexpandingSMul Sigma Φ`, and discharge
`PairwiseOrderInvariant` for your attachment family. Everything in
`Specification/`, `Metric/Epsilon` and `Algebra/Star` then applies verbatim;
`RandomSystemsReceipts.lean` is the worked template.

**Adding a proof technique.** Techniques are definitions over already-landed
observables — the game transcript law, `ν`, `ω`, `Adv⊥`, the conditioning layer
— not new stacks of objects. Before introducing an operator, check whether the
relation you want is already named: "behaves as `T` until the condition fires"
is `EquivalentAsGames`, and "wins blindly" is `supWinProb` with its index set cut
down.

**Working with the fence.** The MauRen16-track roots import no MauRen11-specific
module. To use the distinguisher class, its metric, the indexed relaxation, the
simulation notion, choice settings, the two-party case or step-wise refinement,
import `AbstractCryptography.MR11` explicitly; that keeps the dependency visible
in the import list rather than acquired by accident through a root.

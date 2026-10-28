# Distance and distinguishers

This folder holds the transcript distance of random systems and the ways to bound it:
probabilistic distinguishers and their behaviors, with the transcript distance as the largest
advantage; absorption of converters and systems into distinguishers; couplings; restriction to a
smaller domain; the H-coefficient bound; and the identical-until-bad bound. The systems, PDSs and
converters it uses are those of [RandomSystems](../README.md). Citations refer to the numbered
[references](../../../THEORY.md#references) of THEORY.md.

## Distance and distinguishers

The [**transcript distance**][RandomSystem.transcriptDistance] takes the supremum over environments
$`E`$ [compatible with the domain][Domain.Compatible] and [bounded][QueryBounded] to $`n`$ queries; a
[**probabilistic distinguisher**][Domain.Distinguisher] $`P`$ [1, Definition 9] has an
[advantage][Domain.Distinguisher.advantage]:

```math
\Delta(R, S) = \sup_{E,\, n}\ \delta\big(\mathrm{tr}(R, E, n),\ \mathrm{tr}(S, E, n)\big),
\qquad
\mathrm{Adv}_P(R, S) = \big\lvert \Pr[P(R) = 1] - \Pr[P(S) = 1] \big\rvert .
```

A probabilistic distinguisher is a distribution over
[deterministic distinguishers][IsDDD] [compatible with the domain][Domain.DecisionCompatible], and its
[probability of outputting 1][Domain.Distinguisher.probability] averages their
[decision probabilities][RandomSystem.decisionProbability]. For each $`P`$, $`\mathrm{Adv}_P`$ is a
pseudo-distance: it is [zero on equal systems][advantage_self], [symmetric][advantage_symm], and
[satisfies the triangle inequality][advantage_triangle]. The transcript distance
[is the largest advantage][RandomSystem.transcriptDistance_eq_iSup],
$`\Delta(R, S) = \sup_P \mathrm{Adv}_P(R, S)`$, so
[every advantage is at most the distance][advantage_le_transcriptDistance].

The [**behavior**][Domain.DistinguisherBehavior] of a probabilistic distinguisher is its
probability of outputting 1 on each system, as the behavior of a PDC is its random system; the
transcript distance [is also the largest advantage of a behavior][RandomSystem.transcriptDistance_eq_iSup_behavior].
A behavior has an [advantage][DistinguisherBehavior.advantage], which is
[zero on equal systems][DistinguisherBehavior.advantage_self],
[symmetric][DistinguisherBehavior.advantage_symm], satisfies the
[triangle inequality][DistinguisherBehavior.advantage_triangle], and
[is at most the distance][DistinguisherBehavior.advantage_le_transcriptDistance].

## Initially sampled systems

Choose a component with law $`P`$ and retain it throughout the interaction. For a fixed
compatible distinguisher $`D`$, [the decision probability](Mixture.lean) is an average:

```math
\Pr[D(\operatorname{sample}(P, R)) = 1]
= \sum_k P(k)\,\Pr[D(R_k) = 1].
```

`RandomSystem.decisionProbability_mix` proves this for a deterministic distinguisher by
taking the decision event's mass in the transcript mixture. `Domain.Distinguisher.probability_mix`
then averages over the distinguisher's independent random choice.

For two families on the same interface, the typed
[`transcriptDistance_sample_le`](../Typed/SamplingDistance.lean) derives
$`\Delta(\operatorname{sample}(P, R), \operatorname{sample}(P, S)) \le \varepsilon`$
from $`\Delta(R_k, S_k) \le \varepsilon`$ for every $`k`$. For each distinguisher, the
triangle inequality bounds its advantage by the average of the component advantages;
nonnegative weights summing to one preserve the common bound. The law may be nonuniform,
but it must be the same in both mixtures. Sampling itself does not reveal the component index.

## Couplings

The [transcript][System.tr] $`\mathrm{tr}(s, E, n)`$ of a deterministic system $`s`$
with an environment $`E`$ within $`n`$ rounds is the sequence of their query–reply pairs
[1, Definition 7]. For an environment compatible with the random system $`R`$ of a PDS $`P`$, the
transcript law of $`R`$ [is the transformation][PDS.sLaw_behavior_eq_fTransform] of $`P`$ by
$`\mathrm{tr}(\cdot, E, n)`$ [1, Definition 4 and footnote 9]. A [coupling][IsCoupling] $`J`$ of
$`P`$ and a PDS $`Q`$ with random system $`S`$ therefore bounds the distance of the transcript laws
by the [probability that the transcripts differ][PDS.statDist_sLaw_behavior_le_of_isCoupling], and
the transcript distance by the
[probability that the systems differ][PDS.transcriptDistance_behavior_le_of_isCoupling]:

```math
\delta\big(\mathrm{tr}(R, E, n),\ \mathrm{tr}(S, E, n)\big)
\le \Pr_{(s, t) \sim J}\big[\mathrm{tr}(s, E, n) \ne \mathrm{tr}(t, E, n)\big],
\qquad
\Delta(R, S) \le \Pr_{(s, t) \sim J}[s \ne t] .
```

The second bound holds for every coupling; [1, Theorem 2] states in addition that some
presentations of $`R`$ and $`S`$ have a coupling attaining it.

## Absorption

[Absorbing][DistinguisherBehavior.absorb] a PDC $`\alpha`$ into a behavior $`d`$ gives
$`d \circ \alpha`$, which decides on a system as $`d`$ decides on $`\alpha`$ attached to it,
$`\Pr[(d \circ \alpha)(R) = 1] = \Pr[d(\alpha R) = 1]`$. Absorbing a serial composition
[absorbs its PDCs in turn][DistinguisherBehavior.absorb_comp],
$`d \circ (\beta \circ \alpha) = (d \circ \beta) \circ \alpha`$. On deterministic distinguishers
absorption [connects the distinguisher to the converter's outside][absorbAll]; absorbing a
converter into a probabilistic distinguisher [gives a probabilistic distinguisher][Domain.Distinguisher.exists_absorbAll],
so $`d \circ \alpha`$ is a behavior, and so does absorbing
[a system run beside][Domain.Distinguisher.exists_absorbRight].

## Restriction

The [restriction][RandomSystem.restrict] $`R \restriction D'`$ of a random system on $`D`$
to a smaller domain $`D' \subseteq D`$ keeps the masses of the transcripts $`D'`$ admits and is zero
elsewhere. Restrictions [compose][RandomSystem.restrict_restrict], and an environment compatible
with $`D'`$ [sees the transcript law of the system itself][RandomSystem.sLaw_restrict], so restriction
[does not increase the distance][RandomSystem.transcriptDistance_restrict_le],
$`\Delta(R \restriction D', S \restriction D') \le \Delta(R, S)`$.

## The H-coefficient bound

Under an environment $`E`$, the transcript law of $`R`$ gives each
transcript $`h`$ that $`E`$ produces the probability $`R(h)`$, and the others zero; the restriction
is the same for $`S`$, so a ratio of the two systems' probabilities on the good transcripts is a
ratio of their transcript laws. For $`R`$ and $`S`$ replying at the queried label, the
H-coefficient technique then
[bounds the distance][RandomSystem.transcriptDistance_le_add_of_ratio_on_good] by the error
$`\varepsilon_1`$ of the ratio and the bound $`\varepsilon_2`$ on the bad transcripts under $`S`$:

```math
(1 - \varepsilon_1)\, S(h) \le R(h) \ \text{ for } h \notin \mathrm{Bad}, \quad
\Pr_{\mathrm{tr}(S, E, n)}[\mathrm{Bad}] \le \varepsilon_2 \ \text{ for all } E, n
\quad \Longrightarrow \quad
\Delta(R, S) \le \varepsilon_1 + \varepsilon_2 .
```

For revealed values and multiple transcript classes, use
[`RandomSystem.HCoefficient`](RevealedHCoefficient.lean). Supply the real mixture,
its deterministic reveal, the ideal conditional reveal law, the finite classification,
the pointwise ratio, and the expected class-error bound. Its
`transcriptDistance_le_nnreal` theorem gives the same distance; the instance-layer
`Interface.distance_le_of_hCoefficient` gives the CC distance. `ofGoodBad` assigns
error one to the bad class and the ratio error to the good class.

The [reveal laws](../Cumulative/Revealed.lean) have the original transcript laws as
marginals. `kernelLaw_mass_eq_expect` turns a revealed bad-event mass into the
expectation of its conditional probability. The reveal and the partition remain explicit;
no security choice is made by automation.

## Identical until bad

Two random systems $`R_1`$ and $`R_2`$ have transcript probabilities that both lie above a common
part $`g`$ with $`g([]) = 1`$. A step from a possible transcript $`h`$ by an admitted query $`x`$
loses $`g(h) - \sum_y g(h, x, y)`$ of the common part. If each step loses at most
$`\beta(h, x)\, R_1(h)`$, and the [cost][transcriptCost] of each possible transcript, the sum of
$`\beta`$ over its steps, is at most $`\varepsilon`$, then by the union bound over the steps every
compatible environment [stays in the common part][RandomSystem.one_sub_le_sum_tSupp] with
probability at least $`1 - \varepsilon`$, and the two systems are
[within][RandomSystem.transcriptDistance_le_of_transcriptCost_le] $`\varepsilon`$ of each other:

```math
g(h) - \sum_y g(h, x, y) \le \beta(h, x)\, R_1(h), \qquad
\sum_{k < |h|} \beta(h_1 \cdots h_k,\ x_{k+1}) \le \varepsilon
\quad \Longrightarrow \quad
\Delta(R_1, R_2) \le \varepsilon .
```

Games build on this bound: see [Game](../Game/README.md#identical-until-bad).

<!-- Declarations -->

[RandomSystem.transcriptDistance]: Decision.lean#L228
[Domain.Compatible]: Decision.lean#L165
[Domain.DecisionCompatible]: Decision.lean#L171
[QueryBounded]: ../System/DDE.lean#L24
[IsDDD]: ../System/InterfaceSystem.lean#L968
[RandomSystem.decisionProbability]: Decision.lean#L262
[Domain.Distinguisher]: Distinguisher.lean#L122
[Domain.Distinguisher.probability]: Distinguisher.lean#L126
[Domain.Distinguisher.advantage]: Distinguisher.lean#L132
[advantage_self]: Distinguisher.lean#L141
[advantage_symm]: Distinguisher.lean#L143
[advantage_triangle]: Distinguisher.lean#L146
[RandomSystem.transcriptDistance_eq_iSup]: Distinguisher.lean#L154
[advantage_le_transcriptDistance]: Distinguisher.lean#L196
[Domain.DistinguisherBehavior]: Distinguisher.lean#L207
[DistinguisherBehavior.advantage]: Distinguisher.lean#L218
[DistinguisherBehavior.advantage_self]: Distinguisher.lean#L228
[DistinguisherBehavior.advantage_symm]: Distinguisher.lean#L230
[DistinguisherBehavior.advantage_triangle]: Distinguisher.lean#L233
[DistinguisherBehavior.advantage_le_transcriptDistance]: Distinguisher.lean#L238
[RandomSystem.transcriptDistance_eq_iSup_behavior]: Distinguisher.lean#L246
[System.tr]: Coupling.lean#L50
[IsCoupling]: ../../Probability/Coupling.lean#L46
[PDS.sLaw_behavior_eq_fTransform]: Coupling.lean#L165
[PDS.statDist_sLaw_behavior_le_of_isCoupling]: Coupling.lean#L213
[PDS.transcriptDistance_behavior_le_of_isCoupling]: Coupling.lean#L241
[DistinguisherBehavior.absorb]: Distinguisher.lean#L291
[DistinguisherBehavior.absorb_comp]: Distinguisher.lean#L304
[Domain.Distinguisher.exists_absorbAll]: Distinguisher.lean#L265
[Domain.Distinguisher.exists_absorbRight]: Distinguisher.lean#L330
[absorbAll]: Absorption.lean#L42
[RandomSystem.restrict]: Restriction.lean#L59
[RandomSystem.restrict_restrict]: Restriction.lean#L67
[RandomSystem.sLaw_restrict]: Restriction.lean#L98
[RandomSystem.transcriptDistance_restrict_le]: Restriction.lean#L129
[RandomSystem.transcriptDistance_le_add_of_ratio_on_good]: HCoefficient.lean#L40
[transcriptCost]: UntilBad.lean#L38
[RandomSystem.one_sub_le_sum_tSupp]: UntilBad.lean#L65
[RandomSystem.transcriptDistance_le_of_transcriptCost_le]: UntilBad.lean#L146

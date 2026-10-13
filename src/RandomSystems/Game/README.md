# Games

This folder holds games: random systems whose replies carry a bit, the MBO, which once set stays
set. It defines the visible system, winning, conditional equivalence and equivalence as games;
proves that distinguishing is bounded by winning, the fundamental lemma and the until-bad bound
for games; lifts converters to games; and presents games by discrete games and by sampled
functions with a hidden condition. The random systems, distinguishers and distances it uses are
those of [RandomSystems](../README.md) and [Distance](../Distance/README.md). Citations refer to
the numbered [references](../../../THEORY.md#references) of THEORY.md.

## Games, winning and conditional equivalence

A [**game**][RandomSystem.MonotoneMBO] is a random system whose replies carry a bit, the MBO,
which once set stays set [3, §3.7.1]. Its [**visible system**][RandomSystem.visible] $`G^-`$ ignores
the MBO [3, Definition 4.18]: the probability of a transcript, whatever the MBOs. A distinguisher
used as a winner [does not see the MBO][DDE.blindMBO], and its
[**winning probability**][RandomSystem.winProbability] is the probability that the MBO is set when
it stops [3, Definition 4.5]. A game is [**conditionally equivalent**][RandomSystem.ConditionallyEquivalent]
to a random system $`T`$, $`G \mathrel{|\!\equiv} T`$, when it replies as $`T`$ as long as the MBO is
unset [3, Definition 4.19], [5, Definition 13]. The advantage between the visible system and $`T`$
is then [at most the winning probability][Domain.Distinguisher.advantage_le_winProbability]
[3, Lemma 4.16 and the proof of Theorem 4.17]:

```math
G\big(x^n, (y, 0)^n\big) = \Pr_G[\text{MBO unset} \mid x^n]\ T(x^n, y^n)
\quad \Longrightarrow \quad
\mathrm{Adv}_P(G^-, T) \le \Pr[P \text{ wins } G] .
```

Before the MBO is set, the winner sees the replies of $`T`$, which carry no information about the
MBO. If the MBO is set with probability at most $`\varepsilon`$ on every fixed query sequence,
every winner [wins with probability at most][Domain.Distinguisher.winProbability_le_of_unsetProbability] $`\varepsilon`$.
The transcript distance is the largest advantage ([Distance](../Distance/README.md)), so the
visible system is then
[within][RandomSystem.transcriptDistance_visible_le_of_unsetProbability] $`\varepsilon`$ of $`T`$
[3, Theorem 4.17], [5, Theorem 3], for $`G`$ and $`T`$ replying at the queried label:

```math
G \mathrel{|\!\equiv} T, \quad \Pr_G[\text{MBO set} \mid x^n] \le \varepsilon \ \text{ for every fixed } x^n
\quad \Longrightarrow \quad
\Delta(G^-, T) \le \varepsilon .
```

## Equivalence as games

Two games are [**equivalent as games**][RandomSystem.GameEquivalent], $`G \overset{g}{\equiv} H`$,
when they behave alike as long as the MBO is unset: they give every transcript with every MBO
unset the same probability [3, Definition 4.16], [4, Definition 5]. A distinguisher then
[wins both alike][Domain.Distinguisher.winProbability_eq_of_gameEquivalent] [3, Lemma 4.15], and
by the fundamental lemma its advantage between their visible systems is
[at most its winning probability][Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent]
[3, Lemma 4.16], [4, Lemma 7 and Theorem 1 (i)]: to tell them apart, it must set the MBO. For
games replying at the queried label:

```math
G\big(x^n, (y, 0)^n\big) = H\big(x^n, (y, 0)^n\big)
\quad \Longrightarrow \quad
\mathrm{Adv}_P(G^-, H^-) \le \Pr[P \text{ wins } G] = \Pr[P \text{ wins } H] .
```

## Identical until bad

For games, identical until bad rests on the systems-level bound of
[Distance](../Distance/README.md#identical-until-bad): two random systems whose transcript
probabilities lie above a common part are within $`\varepsilon`$ of each other when each step
loses little of it. On a game $`G`$, the part with every MBO unset lies below the visible
system, and a step loses from it the probability that $`G`$ sets the MBO at that step. Suppose
that, from every transcript with every MBO unset, $`G`$ sets the MBO at the next query $`x`$ with
probability at most $`\beta(h, x)`$ times the probability of the transcript. The mass missing from
the unset part along the transcripts of a winner is the winning probability, so every winner
[wins with probability at most][Domain.Distinguisher.winProbability_le_of_transcriptCost_le]
$`\varepsilon`$. Two games equivalent as games have the same unset part, which is therefore a
common part of their visible systems, and the per-step costs bound its missing mass: the visible
systems are [within][RandomSystem.GameEquivalent.transcriptDistance_visible_le] $`\varepsilon`$ of
each other. Two discrete games are equivalent as games when they are
[coupled][PDG.gameEquivalent_behavior_of_isCoupling]: a joint law of the two [1, Theorem 2] whose
pairs have one condition and systems that answer alike while the condition does not hold.

## Attachment

The library defines the action of a PDC $`\alpha`$ on a game by its
[MBO-forwarding lift][PDCBehavior.liftMBO] $`\hat\alpha`$: the lift runs $`\alpha`$, which does not see
the inside MBOs, and gives each outside reply the MBO of the latest inside reply. The source states
this action informally: a converter turns a game into a game, the MBO being neither seen nor
affected by the converter [3, §4.7.2]. The lift is functorial: it
[preserves identities][PDCBehavior.liftMBO_id], $`\hat{\mathrm{id}} = \mathrm{id}`$, and
[composition][PDCBehavior.liftMBO_comp], $`\widehat{\alpha \beta} = \hat\alpha \hat\beta`$. It
[keeps games games][RandomSystem.MonotoneMBO.attach_liftMBO] and
[commutes with the visible system][RandomSystem.visible_attach_liftMBO],
$`(\hat\alpha G)^- = \alpha\, G^-`$. A winner with $`\alpha`$ absorbed
wins $`G`$ [as the winner wins][RandomSystem.winProbability_attach_liftMBO] $`\hat\alpha G`$
[3, §4.7.2, equation (4.9)]. A [**solver behavior**][Domain.SolverBehavior] pairs a probabilistic
distinguisher's probability of outputting 1 on each random system with its winning probability
for each game, and [absorbing a PDC][Domain.SolverBehavior.absorb] into a solver behavior gives a
solver behavior.

## Discrete games

Discrete games present games, as PDSs present random systems. A [discrete game][PDG] is a
distribution over [deterministic discrete games][DDG], pairs of a DDS and a hidden
[monotone condition][MC] on the queries, on a domain [2, Definitions 2.20–2.22]. Each reply of a
deterministic discrete game [carries the condition on the queries so far][DDG.withMBO] as its MBO,
and a discrete game [presents the game][PDG.behavior] of these systems. Its visible system
[is the behavior of the visible systems][PDG.visible_behavior], and on an admitted query sequence
the MBO [is unset with the probability that the condition does not hold][PDG.unsetProbability_behavior],
so a bound on the condition at the empty and every admitted query sequence
[bounds the probability that the MBO is set][PDG.one_sub_le_unsetProbability_behavior]. The game
is [conditionally equivalent][PDG.conditionallyEquivalent_behavior] to a random system $`S`$ when
the replies with the condition unset factor through $`S`$:

```math
\Pr_G[\,y^n,\ \lnot\mathrm{bad} \mid x^n\,] = \big(1 - \Pr_G[\mathrm{bad} \mid x^n]\big)\, S(x^n, y^n) .
```

A [sampled function with a hidden condition][PDG.ofFunction] is a discrete game, and the game it
presents is [conditionally equivalent to the ideal function][PDG.ofFunction_conditionallyEquivalent]
once, on every fixed query sequence, the answers jointly with the unset condition factor through
the ideal answers.

<!-- Declarations -->

[RandomSystem.MonotoneMBO]: MBO.lean#L305
[RandomSystem.visible]: MBO.lean#L340
[DDE.blindMBO]: MBO.lean#L410
[RandomSystem.winProbability]: MBO.lean#L480
[RandomSystem.ConditionallyEquivalent]: MBO.lean#L523
[RandomSystem.GameEquivalent]: MBO.lean#L537
[Domain.Distinguisher.advantage_le_winProbability]: MBO.lean#L756
[Domain.Distinguisher.winProbability_eq_of_gameEquivalent]: MBO.lean#L860
[Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent]: MBO.lean#L874
[Domain.Distinguisher.winProbability_le_of_unsetProbability]: MBO.lean#L951
[RandomSystem.transcriptDistance_visible_le_of_unsetProbability]: MBO.lean#L976
[Domain.Distinguisher.winProbability_le_of_transcriptCost_le]: UntilBad.lean#L148
[RandomSystem.GameEquivalent.transcriptDistance_visible_le]: UntilBad.lean#L177
[PDG.gameEquivalent_behavior_of_isCoupling]: UntilBad.lean#L209
[PDCBehavior.liftMBO]: MBOAttachment.lean#L455
[PDCBehavior.liftMBO_id]: MBOAttachment.lean#L495
[PDCBehavior.liftMBO_comp]: MBOAttachment.lean#L1515
[RandomSystem.MonotoneMBO.attach_liftMBO]: MBOAttachment.lean#L965
[RandomSystem.visible_attach_liftMBO]: MBOAttachment.lean#L619
[RandomSystem.winProbability_attach_liftMBO]: MBOAttachment.lean#L2079
[Domain.SolverBehavior]: MBOAttachment.lean#L2169
[Domain.SolverBehavior.absorb]: MBOAttachment.lean#L2191
[MC]: DiscreteMBO.lean#L46
[DDG]: DiscreteMBO.lean#L50
[PDG]: DiscreteMBO.lean#L54
[DDG.withMBO]: DiscreteMBO.lean#L103
[PDG.behavior]: DiscreteMBO.lean#L235
[PDG.visible_behavior]: DiscreteMBO.lean#L253
[PDG.unsetProbability_behavior]: DiscreteMBO.lean#L331
[PDG.one_sub_le_unsetProbability_behavior]: DiscreteMBO.lean#L434
[PDG.conditionallyEquivalent_behavior]: DiscreteMBO.lean#L460
[PDG.ofFunction]: FunctionGame.lean#L37
[PDG.ofFunction_conditionallyEquivalent]: FunctionGame.lean#L73

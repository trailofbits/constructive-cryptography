# The theory, layer by layer

This page shows the structure of the library: its layers, the central objects of each, and how
they connect. The systems level holds the concrete objects: **random systems**, and **typed
systems**, the random systems and converters on the alphabets and domain of an interface. The
abstract layers are **classes of assumptions**, up to categories. **Instances** connect the two:
every field of an instance is a systems-level object, and every axiom is discharged by a
systems-level theorem. The layers are used for **constructions**, the **substitution calculus**,
the **DSL** and the **examples**. Each section links its central declarations and points to the
README of its folder for the rest; citations refer to the [references](#references) at the end.

```
Probability ─▶ Random systems ─▶ Typed systems ══ instance ══▶ Classes
                    (§1)              (§2)                      (§3)
                                       ▲                         │
                                       │                         ▼
                                    DSL (§5)      Constructions, substitution (§4)
                                                                 │
                                                                 ▼
                                                           Examples (§5)
```

---

## 1. Random systems

*Systems over finite alphabets, answering exactly on a bounded domain [1], [2, Chapter 2],
[3, Chapter 3]. Laws are finitely supported distributions and $`\delta`$ is the statistical
distance ([Probability](src/Probability/README.md)).*

**Systems.** A [deterministic system][IsDDS] (DDS) is a partial function from input histories to
the next output, whose domain is closed under nonempty prefixes. A [domain][Domain]
$`\mathcal D`$ admits next queries after each transcript, with a bound on the length, and a
[PDS][PDS] is a finite distribution over DDSs with domain $`\mathcal D`$ [1, Definition 8]. A
[**random system**][RandomSystem] is given by its cumulative probabilities $`p`$ on transcripts
[1, after Lemma 5], [normalized][IsRandomSystem] on the domain:

```math
p(\varepsilon) = 1, \qquad p \ge 0, \qquad
\sum_{y} p\big(h \cdot (x, y)\big) =
\begin{cases} p(h) & \text{if } x \text{ is admitted after } h, \\ 0 & \text{otherwise.} \end{cases}
```

A PDS [has a random system][PDS.behavior], and every random system
[has a finite presentation][RandomSystem.exists_presentation]: random systems
[are exactly the classes of equivalent PDSs][RandomSystem.ofPDSClass_bijective].

**Converters and attachment.** A [DDC][IsDDC] is a system on the converter alphabets with a bound
on its consecutive inside queries [3, Definition 3.8]. A [PDC][PDCBehavior.ofPDC] is a distribution
over DDCs, and its [behavior][PDCBehavior] is a random system over the converter domain
[3, Definitions 3.17–3.18]. PDC behaviors [compose][PDCBehavior.comp] associatively, with an
[identity][PDCBehavior.id]. [Attachment][PDCBehavior.attach] $`\alpha R`$ samples the PDC, then
attaches the sample: [the identity leaves a system unchanged][PDCBehavior.attach_id], and
[a composition attaches its inner converter first][PDCBehavior.attach_comp]. Two random systems
run [independently in parallel][RandomSystem.parallel], and so do two
[PDC behaviors][PDCBehavior.tensor]. [RandomSystems](src/RandomSystems/README.md) adds automata,
probabilistic automata, memoryless systems and programs.

**Distance.** The [transcript distance][RandomSystem.transcriptDistance] is the largest
statistical distance of the transcripts that an environment compatible with the domain sees within
$`n`$ queries. It [is the largest advantage][RandomSystem.transcriptDistance_eq_iSup] of a
[probabilistic distinguisher][Domain.Distinguisher] $`P`$ [1, Definition 9]:

```math
\Delta(R, S) = \sup_{E,\, n}\ \delta\big(\mathrm{tr}(R, E, n),\ \mathrm{tr}(S, E, n)\big)
= \sup_P\ \big\lvert \Pr[P(R) = 1] - \Pr[P(S) = 1] \big\rvert .
```

Couplings, restriction, the H-coefficient technique and identical until bad bound the distance:
see [Distance](src/RandomSystems/Distance/README.md).

**Games.** A [game][RandomSystem.MonotoneMBO] is a random system whose replies carry a bit, the
MBO, which once set stays set [3, §3.7.1]. Its [visible system][RandomSystem.visible] $`G^-`$
ignores the MBO [3, Definition 4.18], and the
[winning probability][RandomSystem.winProbability] of a distinguisher is the probability that the
MBO is set when it stops [3, Definition 4.5]. When $`G`$ is
[conditionally equivalent][RandomSystem.ConditionallyEquivalent] to $`T`$,
$`G \mathrel{|\!\equiv} T`$ [3, Definition 4.19], every advantage between $`G^-`$ and $`T`$
[is at most the winning probability][Domain.Distinguisher.advantage_le_winProbability]
[3, Lemma 4.16 and the proof of Theorem 4.17]. For two games
[equivalent as games][RandomSystem.GameEquivalent], this is the
[fundamental lemma][Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent]
[3, Lemma 4.16], [4, Lemma 7 and Theorem 1 (i)]. A converter acts on a game through its
[MBO-forwarding lift][PDCBehavior.liftMBO]. [Game](src/RandomSystems/Game/README.md) adds the
until-bad bound for games and the games presented by discrete games.

---

## 2. Typed systems

*The random systems and converters of §1, typed by interfaces [3, Definitions 3.8, 3.9, 3.17],
[6, §3], [7, Definitions 2.2.1–2.2.2].*

An [**interface**][Interface] $`A = (I, X, Y, D)`$ has finitely many labels, finite alphabets
$`X_i, Y_i`$, and a domain $`D`$ of input histories, prefix-closed, without the empty history, of
bounded length. A [**typed system**][TypedSystem] on $`A`$ is a random system on
$`(\Sigma_i X_i, \Sigma_i Y_i)`$ over $`D`$,
[replying at the queried label][RandomSystem.RepliesAtQueriedInterface]. A
[**typed converter**][TypedConverter] from $`A`$ to $`B`$ is a PDC behavior from $`B`$'s domain
(inside) to $`A`$'s domain (outside). Typed converters compose by the
[serial composition][TypedConverter.comp] of PDC behaviors, with the [identity][TypedConverter.id],
and [attachment][TypedConverter.attach] $`\alpha R`$ is the attachment of PDC behaviors.

[Parallel interfaces][Interface.tensor] put the label sets side by side.
[Parallel typed systems][TypedSystem.parallel] and [parallel typed converters][TypedConverter.parallel]
are the independent parallel compositions, and attachment [is local][TypedConverter.parallel_attach]:

```math
(\alpha \otimes \beta)(R \parallel S) = \alpha R \parallel \beta S .
```

A label-preserving bijection of interfaces gives a [renaming][TypedConverter.rename], and the
renamings regroup parallel compositions. A [**typed game**][TypedGame] on $`A`$ is a typed system
on the interface of $`A`$ with the MBO whose MBO, once set, stays set.
[Typed](src/RandomSystems/Typed/README.md) adds budgets, the coherence laws of parallel
composition, filters, contexts, sources, automata, memoryless and functional systems, and the
typed games presented by discrete games.

---

## 3. Classes and instances

*Each layer is a class of assumptions: it introduces its notions (attachment, parallel
composition, distance, distinguishers, games, winners, solvers) only as fields and axioms, and
knows nothing about systems [3, §§4.4.3, 4.5.1, 4.7.2, 4.10–4.11], [6, §3], [7, §2.2], [8].
Interfaces are an instance of each class: the carrier $`\Phi A`$ is the typed systems on $`A`$,
every field is a systems-level object of §1–2, and every axiom is discharged by systems-level
theorems. Only the classes say "resource", for an element of $`\Phi A`$.*

```
Category ─▶ MonoidalCategory
    │
    ▼
ResourceTheory ─▶ CryptographicAlgebra ─▶ CompatiblePseudoMetric ─▶ CompatibleDistinguisherClass

Distinguishers                            (decision evaluation)
  │
  ▼
DistinguisherAction                       (absorption of converters, over ResourceTheory)
  + AdmissibleDistinguishers              (independently selected tests)
  → ClosedUnder α                         (proof required for the particular converter α)

Games Ω ─▶ DistinctionGames               (evaluation; DistinctionGames fixes Ω = ℝ, probabilities)
  │              │
  ▼              ▼
GameAction Ω ─▶ DistinctionGameAction     (CC converter actions, over Category and
                                           ResourceTheory)
```

General problem reductions use explicit solver types and preordered performance spaces in
`ConstructiveCryptography.Problem` [3, equation (4.3), printed p. 87]. `Games` selects the
performance space $`\Omega`$ with the games; its reduction specializes the general result
to admitted winners. These evaluations and reductions require no category or metric;
`GameAction` adds the categorical converter action. `DistinctionGames` and
the interface instances select $`\Omega = \mathbb R`$, with winning probabilities as values.
Performance values are distinct from the $`\mathbb R_{\ge 0}`$ error budgets bounding distances.

Distinguishers are treated the same way. `Distinguishers` evaluates a distinguisher on a
resource, read as the probability $`p(d, R)`$ that it outputs $`1`$, with advantage
$`\lvert p(d, R) - p(d, S) \rvert`$ [3, Definition 4.7], [9, §2.3.3]; the evaluation is an
abstract real number, with no range axiom. `AdmissibleDistinguishers` independently selects the
tests a security statement quantifies over, with no efficiency or closure claim, and neither
class needs a category or metric. `DistinguisherAction` absorbs converters,
$`p(d\alpha, R) = p(d, \alpha R)`$; closure of the admitted tests under a converter is a proof
supplied for each reduction, not an axiom [6, §4.3]. The closure fields of
`CompatibleDistinguisherClass` concern only the metric.

Canonical interface instances supply the systems objects; admitted tests remain a separate
selection. The arrows of the
category are the typed converters, composed as PDC behaviors, and its monoidal product is their
parallel composition. The carrier $`\Phi A`$ is [`TypedSystem A`][TypedSystem], attachment is
[`TypedConverter.attach`][TypedConverter.attach], and the parallel composition of typed systems
is the [independent parallel composition][RandomSystem.parallel]. The distance
[is, by definition, the transcript distance][Interface.cc_distance_eq] of §1, the distinguishers are the
[distinguisher behaviors][Domain.DistinguisherBehavior], absorbing converters by attachment, and
the games are the
[typed games][TypedGame]. Each axiom is discharged by systems-level theorems, which the abstract
theorem `CompatibleDistinguisherClass.ofClosure` composes for non-expansion; the table below
records the correspondence.

### Interface instance table

The instance modules select existing systems objects and discharge the abstract axioms with
their laws. They define no new system, converter, distance or game carrier; interfaces, typed
systems, typed games and `TypedDistinguisher` remain objects of `RandomSystems`. The import
root is [`ConstructiveCryptography.Instances`](src/ConstructiveCryptography/Instances.lean).
Every row is a global instance (`DominatedByDistance` one for each admitted set) except
`AdmissibleDistinguishers`, which a statement chooses locally and is never installed globally.

| Class | Field | Systems object | Axiom | Systems theorem |
|---|---|---|---|---|
| `Category Interface` ([Category](src/ConstructiveCryptography/Instances/Category.lean)) | `Hom`, `id`, `comp` | `TypedConverter`, `TypedConverter.id`, `TypedConverter.comp` | `id_comp`, `comp_id`, `assoc` | `PDCBehavior.id_comp`, `comp_id`, `comp_assoc` |
| `MonoidalCategory Interface` ([Monoidal](src/ConstructiveCryptography/Instances/Monoidal.lean)) | `tensorObj`, `tensorHom`, `tensorUnit` | `Interface.tensor`, `TypedConverter.parallel`, `Interface.unit` | identity and composition under tensor | `PDCBehavior.tensor_id`, `comp_tensor` |
| `MonoidalCategory Interface` | associator and unitors | `TypedConverter.rename` through the interface regroupings | naturality, pentagon, triangle | `TypedConverter.comp_associator`, `comp_leftUnitor`, `comp_rightUnitor`; `parallel_rename` and `rename_comp` for coherence |
| `ResourceTheory Interface TypedSystem` ([Algebra](src/ConstructiveCryptography/Instances/Algebra.lean)) | `attach` | `TypedConverter.attach` | `attach_identity`, `attach_serial` | `TypedConverter.identity_attach`, `comp_smul` |
| `CryptographicAlgebra Interface TypedSystem` | `laxMonoidal` product and unit | `TypedSystem.parallel`, `TypedSystem.dummy` | naturality | `TypedConverter.parallel_attach` |
| `CryptographicAlgebra Interface TypedSystem` | the same product and unit | typed systems through the regrouping renamings | associativity and unitality | `TypedConverter.rename_mass` with `TypedSystem.parallel_assoc_mass`, `parallel_unit_left_mass`, `parallel_unit_right_mass` |
| `Distinguishers Interface TypedSystem TypedDistinguisher` | `probability` | the output-1 evaluation `d.1 R` of a `TypedDistinguisher` | none; no range axiom | none |
| `DistinguisherAction Interface TypedSystem TypedDistinguisher` | `absorb` | `TypedDistinguisher.absorb` | evaluation, identity, serial absorption | `TypedDistinguisher.probability_absorb`, `absorb_id`, `absorb_comp` |
| `CompatibleDistinguisherClass Interface TypedSystem` | `distinguishers` | all compatible stopping decision behaviors, as functions on typed systems | attachment and ordered-context closure | `Domain.DistinguisherBehavior.absorb`, `Domain.Distinguisher.exists_absorbRight`, `TypedSystem.parallel_swap_mass` |
| `CompatibleDistinguisherClass Interface TypedSystem` | `fibreMetric`, set explicitly | the canonical transcript distance `TypedSystem.transcriptPseudoEMetricSpace`, over all compatible stopping behaviors | `edist_eq` | `RandomSystem.transcriptDistance_eq_iSup_behavior`, via `Interface.transcriptDistance_eq_advantageDistance` |
| `CompatiblePseudoMetric Interface TypedSystem` (parent of the row above) | the same `fibreMetric` | transcript distance | attachment and parallel non-expansion | not a systems theorem: the abstract `CompatibleDistinguisherClass.ofClosure` [8, Lemma 1] applied to the closure row, transferred by `edist_eq` |
| `DistinguisherAdvantage.DominatedByDistance`, for each admitted set | no new metric | decision advantage and the selected transcript distance | `advantage_le_distance` | `Domain.DistinguisherBehavior.advantage_le_transcriptDistance` |
| `AdmissibleDistinguishers Interface TypedDistinguisher` | `admissible`, a **local choice** | a selected set of typed distinguishers at each interface | none; each reduction supplies `ClosedUnder α` for its own converter | none; no global instance, efficiency or universal closure claim |
| `Games Interface TypedGame ℝ` ([Game](src/ConstructiveCryptography/Instances/Game.lean)) | `winners` | the winning views of `Domain.SolverBehavior`; the class is abstract over a preordered $`\Omega`$, here $`\Omega = \mathbb R`$, real winning probabilities | none; no range axiom | none |
| `GameAction Interface TypedGame ℝ` | `attachGame` | `TypedConverter.attachGame`, using the MBO-forwarding lift | identity, serial action, winner closure | `TypedConverter.identity_attachGame`, `comp_attachGame`; `Domain.SolverBehavior.absorb` |
| `DistinctionGames Interface TypedSystem TypedGame` | `solvers`, `visible`, `ConditionallyEquivalent` | joint solver views, `TypedGame.visible`, `RandomSystem.ConditionallyEquivalent` | `solvers_winner`, `advantage_le_win` | membership by definition; `Domain.Distinguisher.advantage_le_winProbability` |
| `DistinctionGameAction Interface TypedSystem TypedGame` | the same joint solvers and game action | one solver absorbed through one converter, preserving both views | solver closure, visibility under attachment | `Domain.SolverBehavior.absorb`, `RandomSystem.visible_attach_liftMBO` |

The [Substitution](src/ConstructiveCryptography/Instances/Substitution.lean) corollary uses
`TypedConverter.rightContext` and `leftContext`, whose attachment laws realize the two ordered
parallel contexts. Explicit closure under these contexts makes a single-substitution relaxation
parallel-compatible. Game distance bounds in the Game module similarly reuse systems-level
conditional-equivalence bounds; neither adds an instance axiom.

The metric's class contains **all** compatible stopping decision behaviors. A computational
security statement separately selects admitted distinguishers, and its reduction proves closure
under the converters it actually uses. Thus the canonical transcript metric neither selects an
efficient class nor assumes that every converter preserves efficiency.

---

## 4. Constructions and the substitution calculus

A [**specification**][Specification] is a set of resources, and a converter $`\pi`$ constructs one
specification from another [6, §§2–4], exactly or within $`\varepsilon`$:

```math
\mathcal R \xrightarrow{\ \pi\ } \mathcal S \;:\iff\; \pi\mathcal R \subseteq \mathcal S,
\qquad
\mathcal R \xrightarrow{\ \pi,\ \varepsilon\ } \mathcal S \;:\iff\;
\forall R \in \mathcal R\ \exists S \in \mathcal S.\ d(\pi R, S) \le \varepsilon .
```

Constructions compose [serially][ConstructsWithin.serial] [6, Lemma 1] and
[in parallel][ConstructsWithin.parallel], with added errors. A [relaxation][Relaxation] enlarges
a specification, and a simulator [gives a construction][constructs_of_simulator] [6, Lemma 5] of
a relaxed one: its star relaxation [6, §3.4, Lemma 3], within the error of the simulation.

The **substitution calculus** [9, Chapter 2 and §4.1.4], [7, Definitions 2.2.6–2.2.9 and
Theorem 2.2.10] is stated over any `ResourceTheory`. An [implication witness][Implication]
derives a target substitution from assumptions by a chain of substitutions in contexts
[9, §2.3.1], and counts the uses of each assumption.
[Substitution within an error function][SubstitutesWithin] [9, §2.3.3], $`S \simeq_\varepsilon T`$
when $`\Delta_D(S, T) \le \varepsilon(D)`$ for every admitted distinguisher $`D`$, transports
through a converter $`\alpha`$ that preserves the admitted tests, with loss
$`D \mapsto \varepsilon(D\alpha)`$ at the actual reduced distinguisher [9, p. 16], and along a
witness the [assumption uses][Implication.substitutesWithin] and the
[statistical steps][Implication.substitutesWithin_of_mixed] add up [7, Theorem 2.2.10]; a
statistical step needs the advantage to be dominated by the distance. The
[decision-derived advantage][Distinguishers.distinguisherAdvantage] supplies the per-test
advantage, on interfaces that of the typed distinguishers, which is dominated by the transcript
distance. Every security notion of Commons is a substitution $`R \simeq_\varepsilon S`$ for it,
against the admitted tests the statement selects. Relaxations, simulators and the rest of the
calculus are in
[ConstructiveCryptography](src/ConstructiveCryptography/README.md).

---

## 5. The DSL, the proof commands and the examples

**DSL.** `interface`, `system`, `converter` and `filter` declarations compile to the typed systems
and typed converters of §2 at every budget ([DSL][DSL]); converters are arrows of the category of
interfaces, so that components assemble with `≫` and `⊗ₘ`. A component compiles to a
deterministic [program][Program] and [sources][TypedSystem.source] of fresh samples, and compiled
components are automata, compared by [bisimulation][automatonSystem_eq_of_bisim]. The syntax and
what each declaration generates are in [GRAMMAR][Grammar].

**Proof commands.** [`cc_normalize`][cc_normalize] rewrites attachments to normal forms,
[`cc_nonexpand`][cc_nonexpand] applies the compatibility laws, [`cc_triangle`][cc_triangle] takes
a hybrid step, [`cc_construct`][cc_construct] reduces a construction to its equality or distance
obligation, and [`cc_calc`][cc_calc] proves substitutions and distances by chains of steps. They
are described in [GRAMMAR](src/ConstructiveCryptography/DSL/GRAMMAR.md#proof-commands).

**Examples.** Authenticated encryption is secure under ind-cca and int-ptxt
[9, Theorem 2.3.10(4)], corrected: a [counted chain][correctedChain] uses each assumption twice,
and a collision bound of $`q_e^2 / \lvert \mathcal M \rvert`$ ends it
([distance form][real_ideal_distance_le]). Games and reductions in every instance of the game
action classes with real performance, substitutions on interfaces, components, AES and an AEAD in the DSL, and PRG length
extension are in [Examples](src/Examples/README.md).

---

## Where the formalization departs from its sources

1. **Everything is finite.** Interfaces carry finite labels and alphabets and a domain of bounded length, so typed systems are finite random systems with [finite presentations][RandomSystem.exists_presentation]. The sources allow infinite alphabets and unbounded interactions.
2. **Randomness enters DSL systems only through sources.** A sampled law must be closed: it may depend on declaration parameters, not on runtime values. A probabilistic encryption is therefore a [sampled table of ciphertexts][SymmetricEncryption.encryptions] ([Encryption][SymEnc]).
3. **[9, Theorem 2.3.10(4)] needs a second [`ind-cca`][AE.INDCCA] step.** The printed chain `int-ptxt`, `ind-cca`, `int-ptxt`, followed by a collision bound, fails when a later message equals an earlier replacement message. The [corrected chain][correctedChain] and an [all-pairs collision bound][collision_mass_le] are in [Security][AESec] and [Collision][AECol].
4. **[2, Theorem 2.29] holds with a [maximum over pairs][exists_pair_one_sub_supAgreement_le], not a minimum.** The minimum form [is refuted][not_supAgreement_disagreement_le_every_pair].

---

## References

1. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
2. D. Lanzenberger. *A Theory of Random Systems, Games, and Hardness Amplification*. Doctoral thesis, ETH Zurich.
3. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
4. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology — EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002.
5. U. Maurer. Conditional Equivalence of Random Systems and Indistinguishability Proofs. In *Proceedings of the 2013 IEEE International Symposium on Information Theory (ISIT)*, pp. 3150–3154, 2013.
6. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back). In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016. Cryptology ePrint Archive, Paper 2016/903.
7. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, Diss. ETH No. 26723, ETH Zurich, 2020.
8. U. Maurer. Constructive Cryptography – A New Paradigm for Security Definitions and Proofs. In *Theory of Security and Applications (TOSCA 2011)*, LNCS 6993, pp. 33–56, Springer, 2012.
9. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis, Diss. ETH No. 29663, ETH Zurich, 2023.

<!-- Files -->

[DSL]: src/ConstructiveCryptography/DSL.lean
[Grammar]: src/ConstructiveCryptography/DSL/GRAMMAR.md
[SymEnc]: src/Commons/Definitions/Encryption.lean
[AECol]: src/Examples/AuthenticatedEncryption/Collision.lean
[AESec]: src/Examples/AuthenticatedEncryption/Security.lean

<!-- Declarations: §1 -->

[IsDDS]: src/RandomSystems/System/Basic.lean#L77
[automatonSystem_eq_of_bisim]: src/RandomSystems/System/Automaton.lean#L89
[Domain]: src/RandomSystems/PDS/PDS.lean#L65
[PDS]: src/RandomSystems/PDS/PDS.lean#L133
[IsRandomSystem]: src/RandomSystems/Cumulative/Cumulative.lean#L39
[RandomSystem]: src/RandomSystems/Cumulative/Cumulative.lean#L53
[RandomSystem.RepliesAtQueriedInterface]: src/RandomSystems/Cumulative/Cumulative.lean#L70
[PDS.behavior]: src/RandomSystems/Cumulative/Cumulative.lean#L216
[RandomSystem.exists_presentation]: src/RandomSystems/Cumulative/Presentation.lean#L302
[RandomSystem.ofPDSClass_bijective]: src/RandomSystems/Cumulative/Presentation.lean#L312
[RandomSystem.parallel]: src/RandomSystems/Cumulative/CumulativeOperations.lean#L130
[IsDDC]: src/RandomSystems/DDC/DDC.lean#L127
[PDCBehavior]: src/RandomSystems/Converter/PDCBehavior.lean#L67
[PDCBehavior.ofPDC]: src/RandomSystems/Converter/PDCBehavior.lean#L171
[PDCBehavior.comp]: src/RandomSystems/Converter/PDCBehavior.lean#L277
[PDCBehavior.id]: src/RandomSystems/Converter/PDCBehavior.lean#L375
[PDCBehavior.attach]: src/RandomSystems/Converter/ConverterAttachment.lean#L157
[PDCBehavior.attach_id]: src/RandomSystems/Converter/ConverterAttachment.lean#L264
[PDCBehavior.attach_comp]: src/RandomSystems/Converter/ConverterAttachment.lean#L277
[PDCBehavior.tensor]: src/RandomSystems/Converter/ConverterTensor.lean#L649
[Program]: src/RandomSystems/Converter/Program.lean#L45
[RandomSystem.transcriptDistance]: src/RandomSystems/Distance/Decision.lean#L245
[Domain.Distinguisher]: src/RandomSystems/Distance/Distinguisher.lean#L122
[RandomSystem.transcriptDistance_eq_iSup]: src/RandomSystems/Distance/Distinguisher.lean#L154
[Domain.DistinguisherBehavior]: src/RandomSystems/Distance/Distinguisher.lean#L207
[RandomSystem.MonotoneMBO]: src/RandomSystems/Game/MBO.lean#L305
[RandomSystem.visible]: src/RandomSystems/Game/MBO.lean#L340
[RandomSystem.winProbability]: src/RandomSystems/Game/MBO.lean#L482
[RandomSystem.ConditionallyEquivalent]: src/RandomSystems/Game/MBO.lean#L525
[RandomSystem.GameEquivalent]: src/RandomSystems/Game/MBO.lean#L539
[Domain.Distinguisher.advantage_le_winProbability]: src/RandomSystems/Game/MBO.lean#L758
[Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent]: src/RandomSystems/Game/MBO.lean#L876
[PDCBehavior.liftMBO]: src/RandomSystems/Game/MBOAttachment.lean#L460

<!-- Declarations: §2 -->

[Interface]: src/RandomSystems/Typed/Interface.lean#L42
[TypedSystem]: src/RandomSystems/Typed/Interface.lean#L94
[TypedConverter]: src/RandomSystems/Typed/Interface.lean#L129
[TypedConverter.comp]: src/RandomSystems/Typed/Interface.lean#L136
[TypedConverter.id]: src/RandomSystems/Typed/Interface.lean#L141
[TypedConverter.attach]: src/RandomSystems/Typed/Interface.lean#L192
[Interface.tensor]: src/RandomSystems/Typed/Parallel.lean#L85
[TypedSystem.parallel]: src/RandomSystems/Typed/Parallel.lean#L153
[TypedConverter.parallel]: src/RandomSystems/Typed/Parallel.lean#L210
[TypedConverter.parallel_attach]: src/RandomSystems/Typed/ParallelAttachment.lean#L23
[TypedConverter.rename]: src/RandomSystems/Typed/Relabel.lean#L48
[TypedSystem.source]: src/RandomSystems/Typed/Source.lean#L51
[TypedGame]: src/RandomSystems/Typed/Game.lean#L42

<!-- Declarations: §3 -->

[Interface.cc_distance_eq]: src/ConstructiveCryptography/Instances/Algebra.lean#L274

<!-- Declarations: §4 -->

[Specification]: src/ConstructiveCryptography/Specification/Defs.lean#L26
[Relaxation]: src/ConstructiveCryptography/Specification/Relaxation/Defs.lean#L42
[constructs_of_simulator]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L363
[ConstructsWithin.serial]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L331
[ConstructsWithin.parallel]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L359
[Implication]: src/ConstructiveCryptography/Substitution/Basic.lean#L270
[SubstitutesWithin]: src/ConstructiveCryptography/Substitution/Reduction.lean#L80
[Implication.substitutesWithin]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L84
[Implication.substitutesWithin_of_mixed]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L157
[Distinguishers.distinguisherAdvantage]: src/ConstructiveCryptography/Distinguisher.lean#L132

<!-- Declarations: §5 and departures -->

[cc_normalize]: src/ConstructiveCryptography/Tactics/Basic.lean#L30
[cc_nonexpand]: src/ConstructiveCryptography/Tactics/Categorical.lean#L166
[cc_triangle]: src/ConstructiveCryptography/Tactics/Categorical.lean#L155
[cc_construct]: src/ConstructiveCryptography/Tactics/Categorical.lean#L42
[cc_calc]: src/ConstructiveCryptography/Tactics/Substitution.lean#L101
[real_ideal_distance_le]: src/Examples/AuthenticatedEncryption/Security.lean#L158
[SymmetricEncryption.encryptions]: src/Commons/Definitions/Encryption.lean#L68
[AE.INDCCA]: src/Commons/Definitions/AEAD.lean#L168
[correctedChain]: src/Examples/AuthenticatedEncryption/Security.lean#L128
[collision_mass_le]: src/Examples/AuthenticatedEncryption/Collision.lean#L54
[exists_pair_one_sub_supAgreement_le]: src/Probability/MultiCoupling.lean#L616
[not_supAgreement_disagreement_le_every_pair]: src/Probability/MultiCoupling.lean#L778

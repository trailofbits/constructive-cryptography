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
every field is a systems-level object of §1–2, and every axiom is discharged by a systems-level
theorem. Only the classes say "resource", for an element of $`\Phi A`$.*

```
Category ─▶ MonoidalCategory
    │
    ▼
ResourceTheory ─▶ CryptographicAlgebra ─▶ CompatiblePseudoMetric ─▶ CompatibleDistinguisherClass
    │
    ▼
Games ─▶ DistinctionGames
```

The table gives each class with its instance on interfaces, each field with the systems-level
object that fills it, and each axiom with the systems-level theorem that discharges it.
[ConstructiveCryptography](src/ConstructiveCryptography/README.md) states the classes, their
derived laws, and the consequences of the instances.

| Class, instance | Field or axiom | Systems level |
|---|---|---|
| `Category` (Mathlib), [`Interface.category`][Interface.category] | objects | [interfaces][Interface] |
| | `Hom A B` | [`TypedConverter A B`][TypedConverter] |
| | `id`, `comp` | [`TypedConverter.id`][TypedConverter.id], [`TypedConverter.comp`][TypedConverter.comp]: the identity and the serial composition of PDC behaviors |
| | `id_comp`, `comp_id`, `assoc` | [`PDCBehavior.id_comp`][PDCBehavior.id_comp], [`PDCBehavior.comp_id`][PDCBehavior.comp_id], [`PDCBehavior.comp_assoc`][PDCBehavior.comp_assoc] |
| `MonoidalCategory` (Mathlib), [`Interface.monoidal`][Interface.monoidal] by `MonoidalCategory.ofTensorHom` on [`Interface.monoidalStruct`][Interface.monoidalStruct] | `tensorObj`, `tensorUnit` | [`Interface.tensor`][Interface.tensor], [`Interface.unit`][Interface.unit] |
| | `tensorHom` | [`TypedConverter.parallel`][TypedConverter.parallel], the parallel composition of PDC behaviors; `whiskerLeft` and `whiskerRight` are it with an identity |
| | `associator`, `leftUnitor`, `rightUnitor` | [`Interface.associator`][Interface.associator], [`Interface.leftUnitor`][Interface.leftUnitor], [`Interface.rightUnitor`][Interface.rightUnitor]: the [isomorphisms][Interface.isoOf] of the regrouping [renamings][TypedConverter.rename], with inverses by [`TypedConverter.rename_comp`][TypedConverter.rename_comp] and [`TypedConverter.rename_refl`][TypedConverter.rename_refl] |
| | `id_tensorHom_id` ([`Interface.id_tensor_id`][Interface.id_tensor_id]) | [`PDCBehavior.tensor_id`][PDCBehavior.tensor_id] |
| | `id_tensorHom`, `tensorHom_id` | the definition of the whiskers |
| | `tensorHom_comp_tensorHom`, interchange ([`Interface.tensor_comp`][Interface.tensor_comp]) | [`PDCBehavior.comp_tensor`][PDCBehavior.comp_tensor] |
| | `associator_naturality` ([`Interface.associator_naturality`][Interface.associator_naturality]) | [`TypedConverter.comp_associator`][TypedConverter.comp_associator] |
| | `leftUnitor_naturality`, `rightUnitor_naturality` ([left][Interface.leftUnitor_naturality], [right][Interface.rightUnitor_naturality]) | [`TypedConverter.comp_leftUnitor`][TypedConverter.comp_leftUnitor], [`TypedConverter.comp_rightUnitor`][TypedConverter.comp_rightUnitor] |
| | `pentagon`, `triangle` ([`Interface.pentagon`][Interface.pentagon], [`Interface.triangle`][Interface.triangle]) | [`TypedConverter.parallel_rename`][TypedConverter.parallel_rename] and [`TypedConverter.rename_comp`][TypedConverter.rename_comp] |
| [`ResourceTheory`][ResourceTheory]: attachment; [`Interface.resourceTheory`][Interface.resourceTheory] | carrier $`\Phi A`$ | [`TypedSystem A`][TypedSystem] |
| | `attach` | [`TypedConverter.attach`][TypedConverter.attach], the [attachment of PDC behaviors][PDCBehavior.attach] |
| | `attach_identity` | [`TypedConverter.identity_attach`][TypedConverter.identity_attach], from [`PDCBehavior.attach_id`][PDCBehavior.attach_id] |
| | `attach_serial` | [`TypedConverter.comp_smul`][TypedConverter.comp_smul], from [`PDCBehavior.attach_comp`][PDCBehavior.attach_comp] |
| [`CryptographicAlgebra`][CryptographicAlgebra]: parallel composition; [`Interface.cryptographicAlgebra`][Interface.cryptographicAlgebra] | `laxMonoidal` | [`Interface.resourcesLaxMonoidal`][Interface.resourcesLaxMonoidal] |
| | its product `μ` | [`TypedSystem.parallel`][TypedSystem.parallel], the [independent parallel composition][RandomSystem.parallel] ([`Interface.cc_parallel_eq`][Interface.cc_parallel_eq]) |
| | its unit `ε` | the [dummy typed system][TypedSystem.dummy] ([`Interface.cc_dummy_eq`][Interface.cc_dummy_eq]) |
| | `μ_natural_left`, `μ_natural_right` | [`TypedConverter.parallel_attach`][TypedConverter.parallel_attach], the locality of attachment |
| | `associativity` ([`Interface.parallel_assoc`][Interface.parallel_assoc]) | [`TypedSystem.parallel_assoc_mass`][TypedSystem.parallel_assoc_mass], through [`TypedConverter.rename_mass`][TypedConverter.rename_mass] |
| | `left_unitality`, `right_unitality` ([left][Interface.parallel_dummy_left], [right][Interface.parallel_dummy_right]) | [`TypedSystem.parallel_unit_left_mass`][TypedSystem.parallel_unit_left_mass], [`TypedSystem.parallel_unit_right_mass`][TypedSystem.parallel_unit_right_mass], through [`TypedConverter.rename_mass`][TypedConverter.rename_mass] |
| [`CompatiblePseudoMetric`][CompatiblePseudoMetric]: distance; through [`Interface.compatibleDistinguisherClass`][Interface.compatibleDistinguisherClass] | `fibreMetric` | the [advantage distance][advantageDistance] of the distinguishers below, which [is the transcript distance][Interface.cc_distance_eq] |
| | `edist_smul_le`, `edist_parallel_le` | [`CompatibleDistinguisherClass.ofClosure`][CompatibleDistinguisherClass.ofClosure] [8, Lemma 1], from the closure axioms below |
| [`CompatibleDistinguisherClass`][CompatibleDistinguisherClass]: distinguishers; [`Interface.compatibleDistinguisherClass`][Interface.compatibleDistinguisherClass] by `ofClosure` | `distinguishers A` | [`Interface.distinguishers`][Interface.distinguishers]: the maps $`R \mapsto \Pr[d(R) = 1]`$ for the [distinguisher behaviors][Domain.DistinguisherBehavior] $`d`$ compatible with $`A`$'s domain |
| | `closed_attach` ([`Interface.distinguishers_attach`][Interface.distinguishers_attach]) | [absorbing a converter][DistinguisherBehavior.absorb] |
| | `closed_parallel_left` ([`Interface.distinguishers_parallel_left`][Interface.distinguishers_parallel_left]) | [absorbing a system run beside][Domain.Distinguisher.exists_absorbRight] |
| | `closed_parallel_right` ([`Interface.distinguishers_parallel_right`][Interface.distinguishers_parallel_right]) | the previous two, through the [swap][Interface.parallel_swap], the [isomorphism][Interface.swap] of the renaming that [exchanges the two components][TypedSystem.parallel_swap_mass] |
| | `edist_eq` | the definition of the metric in `ofClosure` |
| [`Games`][Games]: games and winners; [`Interface.games`][Interface.games] | `Game A` | [`TypedGame A`][TypedGame]: the typed systems on the interface of $`A`$ with the MBO whose MBO stays set ([`RandomSystem.MonotoneMBO`][RandomSystem.MonotoneMBO]) |
| | `attachGame` | [`TypedConverter.attachGame`][TypedConverter.attachGame], the attachment of the [MBO-forwarding lift][PDCBehavior.liftMBO] |
| | `winners A` | [`Interface.winners`][Interface.winners]: the winning probabilities of the [solver behaviors][Domain.SolverBehavior] on $`A`$'s domain |
| | `attachGame_identity` | [`PDCBehavior.liftMBO_id`][PDCBehavior.liftMBO_id], with [`PDCBehavior.attach_id`][PDCBehavior.attach_id] |
| | `attachGame_serial` | [`PDCBehavior.liftMBO_comp`][PDCBehavior.liftMBO_comp], with [`PDCBehavior.attach_comp`][PDCBehavior.attach_comp] |
| | `closed_attach` | [`Domain.SolverBehavior.absorb`][Domain.SolverBehavior.absorb] |
| [`DistinctionGames`][DistinctionGames]: games and distinguishing; [`Interface.distinctionGames`][Interface.distinctionGames] | carrier, games | `TypedSystem A`, `TypedGame A` |
| | `solvers A` | [`Interface.solvers`][Interface.solvers]: the pairs of the solver behaviors on $`A`$'s domain |
| | `visible` | [`TypedGame.visible`][TypedGame.visible], the [visible system][RandomSystem.visible] |
| | `ConditionallyEquivalent` | [`RandomSystem.ConditionallyEquivalent`][RandomSystem.ConditionallyEquivalent] |
| | `solvers_winner` | the definition of the winners |
| | `solvers_closed_attach` | [`Domain.SolverBehavior.absorb`][Domain.SolverBehavior.absorb] |
| | `visible_attachGame` | [`RandomSystem.visible_attach_liftMBO`][RandomSystem.visible_attach_liftMBO] |
| | `advantage_le_win` | [`Domain.Distinguisher.advantage_le_winProbability`][Domain.Distinguisher.advantage_le_winProbability] |

So the metric of the instance is the transcript distance of §1, $`d(R, S) = \Delta(R, S)`$, and
a typed game conditionally equivalent to a typed system $`T`$, whose MBO stays unset with
probability at least $`1 - \varepsilon`$ on fixed queries,
[has its visible typed system within][Interface.dist_visible_le] $`\varepsilon`$ of $`T`$
[3, Theorem 4.17].

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
through a converter by absorbing it into the distinguishers [9, p. 16], and along a witness the
[assumption uses][Implication.substitutesWithin] and the
[statistical steps][Implication.substitutesWithin_of_mixed] add up [7, Theorem 2.2.10]. On
interfaces the [distinguishing advantage][Interface.distinguisherAdvantage] is the systems-level
advantage of distinguisher behaviors, and every security notion of Commons is a substitution
$`R \simeq_\varepsilon S`$ for it. Relaxations, simulators and the rest of the calculus are in
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
([distance form][real_ideal_distance_le]). Games and reductions in every instance of the games
classes, substitutions on interfaces, components, AES and an AEAD in the DSL, and PRG length
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
[PDCBehavior.ofPDC]: src/RandomSystems/Converter/PDCBehavior.lean#L169
[PDCBehavior.comp]: src/RandomSystems/Converter/PDCBehavior.lean#L273
[PDCBehavior.id]: src/RandomSystems/Converter/PDCBehavior.lean#L369
[PDCBehavior.comp_assoc]: src/RandomSystems/Converter/PDCBehavior.lean#L338
[PDCBehavior.id_comp]: src/RandomSystems/Converter/PDCBehavior.lean#L385
[PDCBehavior.comp_id]: src/RandomSystems/Converter/PDCBehavior.lean#L375
[PDCBehavior.attach]: src/RandomSystems/Converter/ConverterAttachment.lean#L156
[PDCBehavior.attach_id]: src/RandomSystems/Converter/ConverterAttachment.lean#L233
[PDCBehavior.attach_comp]: src/RandomSystems/Converter/ConverterAttachment.lean#L246
[PDCBehavior.tensor]: src/RandomSystems/Converter/ConverterTensor.lean#L649
[PDCBehavior.comp_tensor]: src/RandomSystems/Converter/ConverterTensor.lean#L745
[PDCBehavior.tensor_id]: src/RandomSystems/Converter/ConverterTensor.lean#L705
[Program]: src/RandomSystems/Converter/Program.lean#L45
[RandomSystem.transcriptDistance]: src/RandomSystems/Distance/Decision.lean#L228
[Domain.Distinguisher]: src/RandomSystems/Distance/Distinguisher.lean#L122
[RandomSystem.transcriptDistance_eq_iSup]: src/RandomSystems/Distance/Distinguisher.lean#L154
[Domain.DistinguisherBehavior]: src/RandomSystems/Distance/Distinguisher.lean#L207
[DistinguisherBehavior.absorb]: src/RandomSystems/Distance/Distinguisher.lean#L291
[Domain.Distinguisher.exists_absorbRight]: src/RandomSystems/Distance/Distinguisher.lean#L330
[RandomSystem.MonotoneMBO]: src/RandomSystems/Game/MBO.lean#L305
[RandomSystem.visible]: src/RandomSystems/Game/MBO.lean#L340
[RandomSystem.winProbability]: src/RandomSystems/Game/MBO.lean#L480
[RandomSystem.ConditionallyEquivalent]: src/RandomSystems/Game/MBO.lean#L523
[RandomSystem.GameEquivalent]: src/RandomSystems/Game/MBO.lean#L537
[Domain.Distinguisher.advantage_le_winProbability]: src/RandomSystems/Game/MBO.lean#L756
[Domain.Distinguisher.advantage_le_winProbability_of_gameEquivalent]: src/RandomSystems/Game/MBO.lean#L874
[PDCBehavior.liftMBO]: src/RandomSystems/Game/MBOAttachment.lean#L455
[PDCBehavior.liftMBO_id]: src/RandomSystems/Game/MBOAttachment.lean#L495
[PDCBehavior.liftMBO_comp]: src/RandomSystems/Game/MBOAttachment.lean#L1515
[RandomSystem.visible_attach_liftMBO]: src/RandomSystems/Game/MBOAttachment.lean#L619
[Domain.SolverBehavior]: src/RandomSystems/Game/MBOAttachment.lean#L2169
[Domain.SolverBehavior.absorb]: src/RandomSystems/Game/MBOAttachment.lean#L2191

<!-- Declarations: §2 -->

[Interface]: src/RandomSystems/Typed/Interface.lean#L40
[TypedSystem]: src/RandomSystems/Typed/Interface.lean#L92
[TypedConverter]: src/RandomSystems/Typed/Interface.lean#L127
[TypedConverter.comp]: src/RandomSystems/Typed/Interface.lean#L134
[TypedConverter.id]: src/RandomSystems/Typed/Interface.lean#L139
[TypedConverter.attach]: src/RandomSystems/Typed/Interface.lean#L157
[TypedConverter.identity_attach]: src/RandomSystems/Typed/Interface.lean#L171
[TypedConverter.comp_smul]: src/RandomSystems/Typed/Interface.lean#L177
[Interface.tensor]: src/RandomSystems/Typed/Parallel.lean#L85
[TypedSystem.parallel]: src/RandomSystems/Typed/Parallel.lean#L153
[TypedConverter.parallel]: src/RandomSystems/Typed/Parallel.lean#L210
[TypedConverter.parallel_attach]: src/RandomSystems/Typed/ParallelAttachment.lean#L23
[Interface.unit]: src/RandomSystems/Typed/InterfaceCoherence.lean#L90
[TypedConverter.rename]: src/RandomSystems/Typed/Relabel.lean#L48
[TypedConverter.rename_comp]: src/RandomSystems/Typed/Relabel.lean#L80
[TypedConverter.rename_refl]: src/RandomSystems/Typed/Relabel.lean#L67
[TypedConverter.rename_mass]: src/RandomSystems/Typed/SystemParallel.lean#L55
[TypedConverter.comp_associator]: src/RandomSystems/Typed/ConverterCoherence.lean#L158
[TypedConverter.comp_leftUnitor]: src/RandomSystems/Typed/ConverterCoherence.lean#L195
[TypedConverter.comp_rightUnitor]: src/RandomSystems/Typed/ConverterCoherence.lean#L224
[TypedConverter.parallel_rename]: src/RandomSystems/Typed/TensorRename.lean#L128
[TypedSystem.dummy]: src/RandomSystems/Typed/SystemCoherence.lean#L97
[TypedSystem.parallel_assoc_mass]: src/RandomSystems/Typed/SystemCoherence.lean#L85
[TypedSystem.parallel_unit_left_mass]: src/RandomSystems/Typed/SystemCoherence.lean#L103
[TypedSystem.parallel_unit_right_mass]: src/RandomSystems/Typed/SystemCoherence.lean#L128
[TypedSystem.parallel_swap_mass]: src/RandomSystems/Typed/SystemCoherence.lean#L153
[TypedSystem.source]: src/RandomSystems/Typed/Source.lean#L51
[TypedGame]: src/RandomSystems/Typed/Game.lean#L35
[TypedConverter.attachGame]: src/RandomSystems/Typed/Game.lean#L38
[TypedGame.visible]: src/RandomSystems/Typed/Game.lean#L53

<!-- Declarations: §3 -->

[Interface.category]: src/ConstructiveCryptography/InterfaceCategory.lean#L30
[Interface.monoidalStruct]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L71
[Interface.monoidal]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L162
[Interface.isoOf]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L33
[Interface.associator]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L52
[Interface.leftUnitor]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L57
[Interface.rightUnitor]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L61
[Interface.swap]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L66
[Interface.id_tensor_id]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L84
[Interface.tensor_comp]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L87
[Interface.associator_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L92
[Interface.leftUnitor_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L97
[Interface.rightUnitor_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L101
[Interface.pentagon]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L105
[Interface.triangle]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L132
[ResourceTheory]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L50
[CryptographicAlgebra]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L97
[CompatiblePseudoMetric]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L43
[advantageDistance]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L36
[CompatibleDistinguisherClass]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L77
[CompatibleDistinguisherClass.ofClosure]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L102
[Games]: src/ConstructiveCryptography/CryptographicAlgebra/Game.lean#L62
[DistinctionGames]: src/ConstructiveCryptography/CryptographicAlgebra/Game.lean#L112
[Interface.resourceTheory]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L71
[Interface.parallel_assoc]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L77
[Interface.parallel_dummy_left]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L89
[Interface.parallel_dummy_right]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L98
[Interface.parallel_swap]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L107
[Interface.resourcesLaxMonoidal]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L116
[Interface.cryptographicAlgebra]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L142
[Interface.distinguishers]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L148
[Interface.distinguishers_attach]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L152
[Interface.distinguishers_parallel_left]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L158
[Interface.distinguishers_parallel_right]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L173
[Interface.compatibleDistinguisherClass]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L181
[Interface.cc_parallel_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L188
[Interface.cc_dummy_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L192
[Interface.cc_distance_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L196
[Interface.winners]: src/ConstructiveCryptography/InterfaceGame.lean#L58
[Interface.solvers]: src/ConstructiveCryptography/InterfaceGame.lean#L63
[Interface.games]: src/ConstructiveCryptography/InterfaceGame.lean#L69
[Interface.distinctionGames]: src/ConstructiveCryptography/InterfaceGame.lean#L125
[Interface.dist_visible_le]: src/ConstructiveCryptography/InterfaceGame.lean#L186

<!-- Declarations: §4 -->

[Specification]: src/ConstructiveCryptography/Specification/Defs.lean#L18
[Relaxation]: src/ConstructiveCryptography/Specification/Relaxation/Defs.lean#L22
[constructs_of_simulator]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L269
[ConstructsWithin.serial]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L234
[ConstructsWithin.parallel]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L254
[Implication]: src/ConstructiveCryptography/Substitution/Basic.lean#L176
[SubstitutesWithin]: src/ConstructiveCryptography/Substitution/Reduction.lean#L72
[Implication.substitutesWithin]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L49
[Implication.substitutesWithin_of_mixed]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L105
[Interface.distinguisherAdvantage]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L208

<!-- Declarations: §5 and departures -->

[cc_normalize]: src/ConstructiveCryptography/Tactics/Basic.lean#L30
[cc_nonexpand]: src/ConstructiveCryptography/Tactics/Categorical.lean#L166
[cc_triangle]: src/ConstructiveCryptography/Tactics/Categorical.lean#L155
[cc_construct]: src/ConstructiveCryptography/Tactics/Categorical.lean#L42
[cc_calc]: src/ConstructiveCryptography/Tactics/Substitution.lean#L88
[real_ideal_distance_le]: src/Examples/AuthenticatedEncryption/Security.lean#L132
[SymmetricEncryption.encryptions]: src/Commons/Definitions/Encryption.lean#L65
[AE.INDCCA]: src/Commons/Definitions/AEAD.lean#L165
[correctedChain]: src/Examples/AuthenticatedEncryption/Security.lean#L102
[collision_mass_le]: src/Examples/AuthenticatedEncryption/Collision.lean#L54
[exists_pair_one_sub_supAgreement_le]: src/Probability/MultiCoupling.lean#L616
[not_supAgreement_disagreement_le_every_pair]: src/Probability/MultiCoupling.lean#L778

# Constructive cryptography

This library holds the abstract theory and its instances on interfaces. `Problem` states
reductions over ordered performance spaces, and `Game` defines the evaluation classes of
games, without categories or converters; `Distinguisher` defines the decision evaluation of
distinguishers and the selection of admitted tests, likewise without categories or metrics;
`CryptographicAlgebra` defines the classes of assumptions, from resource theories to
distinguisher classes and the converter actions on distinguishers and games;
`Specification` and `Construction` define specifications, constructions and relaxations over any
carrier; `Substitution` is the substitution calculus; `Notation.Basic` gives their generic
notation. The instance files `Instances.Category`, `Instances.Monoidal`, `Instances.Algebra`,
`Instances.Game` and `Instances.Substitution` instantiate the classes on interfaces; the full
`Notation`, the proof commands of `Tactics` and the DSL front end ([GRAMMAR](DSL/GRAMMAR.md))
are built on them. The fields of the instances are the systems-level objects of
[RandomSystems](../RandomSystems/README.md), and the
[instance table in THEORY.md](../../THEORY.md#interface-instance-table) lists each
field and axiom with its systems object and theorem. Citations refer to the numbered
[references](../../THEORY.md#references) of THEORY.md.

## The classes

*The classes are assumptions: each introduces its notions (attachment, parallel
composition, distance, distinguishers, games, winners, solvers) only as fields and axioms, and
knows nothing about systems [3, §§4.4.3, 4.5.1, 4.7.2, 4.10–4.11], [6, §3], [7, §2.2], [8]. Only
the classes say "resource", for an element of $`\Phi A`$.*

### `ResourceTheory C Φ`: attachment

In the class [`ResourceTheory`][ResourceTheory], converters $`\alpha : A \to B`$ act on resources
$`R \in \Phi B`$:

```math
\alpha R \in \Phi A, \qquad \mathrm{id}_A\, R = R, \qquad (\alpha \gg \beta)\, R = \alpha\,(\beta\, R) .
```

Attachment is the [contravariant functor][ResourceTheory.functor]
$`\Phi : C^{\mathrm{op}} \to \mathrm{Type}`$.

### `CryptographicAlgebra C Φ`: parallel composition

The class [`CryptographicAlgebra`][CryptographicAlgebra] is a lax monoidal structure on $`\Phi`$:
resources [compose in parallel][CA.parallel], with the [dummy resource][CA.dummy] as unit.

```math
R \parallel S \in \Phi(A \otimes B), \qquad \mathbf 1 \in \Phi(\mathbb I), \qquad
(\alpha \otimes \beta)(R \parallel S) = \alpha R \parallel \beta S .
```

Derived: [locality][CA.attach_parallel], [associativity][CA.parallel_assoc], and the
[left][CA.parallel_dummy_left] and [right][CA.parallel_dummy_right] unit laws.

### `CompatiblePseudoMetric C Φ`: distance

The class [`CompatiblePseudoMetric`][CompatiblePseudoMetric] adds a pseudo-metric $`d`$, the
[distance][CA.distance], on each $`\Phi A`$ [6, Definition 2], [8, Definition 2]:

```math
d(\alpha R, \alpha S) \le d(R, S), \qquad
d(R \parallel R',\ S \parallel S') \le d(R, S) + d(R', S') .
```

Derived: [attachment is non-expanding][distance_attach_le] and
[parallel composition adds distances][distance_parallel_le].
[Opposite attachment bridges preserve distance][distance_eq_of_mutual_attach] for the
chosen two resources using only their four bridge equations. For interfaces the metric is the
transcript distance, and its compatibility comes from the distinguisher class below.

### `CompatibleDistinguisherClass C Φ`: distinguishers

The class [`CompatibleDistinguisherClass`][CompatibleDistinguisherClass] has a class
$`\mathcal D_A`$ of maps $`\Phi A \to \mathbb R`$, closed under absorbing a converter and under running
a fixed resource beside, whose [advantage distance][advantageDistance] is the metric [8, §4.5]:

```math
d(R, S) = \sup_{D \in \mathcal D_A} \lvert D(R) - D(S) \rvert, \qquad
D \in \mathcal D_A \;\Longrightarrow\; D(\alpha\,\cdot\,) \in \mathcal D_B,\ \ D(\,\cdot \parallel T),\ D(T \parallel \cdot\,) \in \mathcal D .
```

**Closure gives compatibility** [8, Lemma 1]: the advantage distance of a closed class
[is a compatible pseudo-metric][CompatibleDistinguisherClass.ofClosure]. These closure fields
serve the metric; the tests admitted by a computational statement are selected separately,
below, and are not assumed closed.

### Decisions, admitted tests and absorption

The decision layer, in `Distinguisher.lean`, uses no category, converter or metric.
[`Distinguishers I Φ D`][Distinguishers] evaluates a distinguisher $`d \in D_A`$ on a resource
$`R \in \Phi A`$, read as $`p(d, R) = \Pr[d(R) = 1]`$, and the
[advantage][Distinguishers.advantage] is the absolute difference. The source takes the signed
difference [3, Definition 4.7, printed p. 91]; the absolute value follows [9, §2.3.3, p. 16]:

```math
\mathrm{Adv}_d(R, S) = \lvert p(d, R) - p(d, S) \rvert .
```

The evaluation is an abstract real number. Typed distinguishers return probabilities, but the
class asserts no range, and the advantage laws hold for any real evaluation. Independently,
[`AdmissibleDistinguishers I D`][AdmissibleDistinguishers] selects the tests
$`\mathcal D_A \subseteq D_A`$ a security statement quantifies over, with no efficiency or
closure claim. [`AdmissibleDistinguishers.all`][AdmissibleDistinguishers.all] admits every test;
it is a value, not an instance. The [decision-derived distinguisher
advantage][Distinguishers.distinguisherAdvantage] combines the evaluation with an admitted set
for the substitution calculus below.

[`DistinguisherAction C Φ D`][DistinguisherAction], over a resource theory, absorbs a converter
into a distinguisher [9, §2.3.3], [7, Proposition 2.2.17]:

```math
p(d\alpha, R) = p(d, \alpha R), \qquad d\,\mathrm{id}_A = d, \qquad d(\alpha \gg \beta) = (d\alpha)\beta ,
```

so [absorption preserves advantage][DistinguisherAction.advantage_absorb],
$`\mathrm{Adv}_{d\alpha}(R, S) = \mathrm{Adv}_d(\alpha R, \alpha S)`$. Admission is not assumed
closed under converters. A reduction through $`\alpha`$ carries the proof
[`ClosedUnder α`][ClosedUnder] that $`d\alpha`$ is admitted whenever $`d`$ is, as closure is
required only for selected converters [6, §4.3, pp. 12–13]; [closure proofs
compose][ClosedUnder.comp] in category order, following the association of $`\gg`$.
[`DominatedByDistance model`][DominatedByDistance], indexed by the model and the selected
metric, states that every admitted test's advantage between $`R`$ and $`S`$ is at most their
distance; only statistical steps of a substitution chain need it.

### Games, solver evaluations and converter actions

[`Games`][Games] and [`DistinctionGames`][DistinctionGames] are defined in `Game.lean`,
without categories, converters or metrics. `Games I Game Ω` selects admitted winners
$`W : \mathrm{Game}\,A \to \Omega`$; the model fixes the performance space $`\Omega`$, as it
fixes the games. The source orders performances partially [3, Definition 4.2, printed p. 85];
the reduction laws need only a preorder, since they use no antisymmetry. Ordinary games
specialize performance to winning probabilities in $`[0,1]`$, and multi-games have several
winning events [3, Definition 4.5, p. 90]. Three notions are kept apart:

- general performance: any preorder, including non-total products such as $`\mathbb N \times \mathbb N`$; the class asserts no range;
- probability performance: `DistinctionGames`, `Interface.games` and `Interface.gameAction` select $`\mathbb R`$, with winning probabilities as values;
- error budgets: the $`\mathbb R_{\ge 0}`$ bounds on distances, which are not performance values.

The [general reduction theorem][Problem.performance_le_of_reduction] in `Problem.lean`
takes a source solver type `Solver` and a target solver type `OtherSolver`, with ordered
performance spaces $`\Omega`$ and $`\Lambda`$. The evaluations
$`p : \mathrm{Solver} \to \Omega`$ and $`q : \mathrm{OtherSolver} \to \Lambda`$ measure how
well a solver performs on its problem. The solver map $`\rho`$ transforms a source solver
into a target solver. A monotone loss $`\lambda : \Lambda \to \Omega`$ translates a target
performance bound back to a source bound [3, equation (4.3), printed p. 87]:

```math
p(s) \le \lambda(q(\rho(s))),\quad q(\rho(s)) \le \varepsilon
\quad\Longrightarrow\quad p(s) \le \lambda(\varepsilon).
```

[`Games.win_le_of_reduction`][Games.win_le_of_reduction] applies this theorem to the subtypes
of admitted winners. Source and target games may use different performance spaces; closure
ensures the reduction maps admitted winners to admitted winners.

`DistinctionGames I Φ Game` selects paired decision and winning evaluations of a common
solver, with real-valued probabilities, the visible resource $`G^-`$, and conditional equivalence.
It specializes `Games I Game ℝ`. The game bound uses
both views of the same solver [3, Lemma 4.16 and the proof of Theorem 4.17]:

```math
G \mathrel{|\!\equiv} T,\quad (D,W) \in \mathcal S_A
\quad\Longrightarrow\quad |D(G^-)-D(T)| \le W(G).
```

The categorical integration lives in `CryptographicAlgebra/Game.lean`. `GameAction C Game Ω`
supplies attachment, identity and serial laws, and closure of admitted winners under
absorption; absorbed winners keep the performance space $`\Omega`$. `DistinctionGameAction C Φ Game`,
over `GameAction C Game ℝ`, supplies closure of the paired solvers and commutation of visibility
with attachment. These actions use the same converters as the CC
algebra; they do not impose categorical structure on the evaluation classes.

[Absorption][Games.absorb] takes the winner first, `absorb W α`, and only needs an attachment
action: $`\omega(wc,g)=\omega(w,cg)`$ [3, equation (4.9), printed p. 94].
The [serial law][Games.absorb_comp] preserves the physical order:

```text
W -- α -- β -- G
absorb W (α ≫ β) = absorb (absorb W α) β
```

The [joint solver projection][Domain.SolverBehavior.decision] supplies an ordinary decision
behavior. It [commutes with absorption][Domain.SolverBehavior.decision_absorb], so a PRG proof
can use the decision view while a game bound keeps both views of the same solver.

## The instances on interfaces

Interfaces are an instance of each class: the carrier $`\Phi A`$ is the
[typed systems](../RandomSystems/Typed/README.md) on $`A`$, every field is a systems-level object,
and every axiom is discharged by systems-level theorems; non-expansion of the transcript metric
composes them through the abstract [`ofClosure`][CompatibleDistinguisherClass.ofClosure].
The instances are [`Interface.category`][Interface.category], [`Interface.monoidal`][Interface.monoidal],
[`Interface.resourceTheory`][Interface.resourceTheory],
[`Interface.cryptographicAlgebra`][Interface.cryptographicAlgebra],
[`Interface.compatibleDistinguisherClass`][Interface.compatibleDistinguisherClass],
[`Interface.distinguisherEvaluations`][Interface.distinguisherEvaluations],
[`Interface.distinguisherAction`][Interface.distinguisherAction],
[`Interface.distinguisherAdvantageDominated`][Interface.distinguisherAdvantageDominated],
[`Interface.games`][Interface.games], [`Interface.gameAction`][Interface.gameAction],
[`Interface.distinctionGames`][Interface.distinctionGames] and
[`Interface.distinctionGameAction`][Interface.distinctionGameAction]; the
[instance table in THEORY.md](../../THEORY.md#interface-instance-table) maps each field
and axiom to its systems object or theorem. No `AdmissibleDistinguishers` instance is installed on
interfaces: each security statement takes the admitted tests as an instance argument. Import
`ConstructiveCryptography.Instances` for the whole layer, or one of `Instances.Category`,
`Instances.Monoidal`, `Instances.Algebra`, `Instances.Game` and `Instances.Substitution` for the
required part.

Interfaces and typed converters form a category under serial composition, and a monoidal
category under parallel composition. In the notation of the category, the attachment laws read
[`Interface.identity_attach`][Interface.identity_attach] and
[`Interface.comp_smul`][Interface.comp_smul]. The abstract [parallel composition][Interface.cc_parallel_eq]
and [dummy][Interface.cc_dummy_eq] are the systems-level ones, and the metric
[is, by definition, the transcript distance][Interface.cc_distance_eq] of
[Distance](../RandomSystems/Distance/README.md):

```math
d(R, S) = \Delta(R, S) = \sup_P \mathrm{Adv}_P(R, S) .
```

Interfaces instantiate the evaluation classes and their converter actions, and these instances
are the only place where they meet random systems: their games are the [typed games](../RandomSystems/Typed/README.md#typed-games),
MBO random systems as [3, §3.7.1] instantiates games, and their winners and solvers are
probabilistic distinguishers, through their [solver behaviors][Domain.SolverBehavior]. A bound on
the winning probability of every distinguisher
[bounds the winning probability of every winner][Interface.win_le]. A typed game conditionally
equivalent to a typed system $`T`$, $`G \mathrel{|\!\equiv} T`$, whose MBO stays unset with
probability at least $`1 - \varepsilon`$ on fixed queries,
[has its visible typed system within][Interface.dist_visible_le] $`\varepsilon`$ of $`T`$,
$`\Delta(G^-, T) \le \varepsilon`$ [3, Theorem 4.17]. A presented typed game is conditionally
equivalent to a typed system [exactly when][Interface.conditionallyEquivalent_ofPDG_iff] the game
it presents on random systems is; if it is conditionally equivalent to $`S`$ and the condition
holds with probability at most $`\varepsilon`$ on the empty and every admitted query sequence, the
presented typed system $`R`$ is [within][Interface.game_dist_le] $`\varepsilon`$ of $`S`$,
$`\Delta(R, S) \le \varepsilon`$.

## Notation

With `open scoped SystemAlgebra`, `Notation/Basic.lean` defines all the notation over the
abstract classes; it imports only those classes, so instance modules such as `Instances.Game`
use it. Each symbol reads the selected instances and selects none:
[`Δ R S`][notation-distance] for the distance of `CompatiblePseudoMetric`,
[`R ∥ S`][notation-parallel] for the selected parallel composition,
[`R ≃[ε] S`][notation-substitutes] for substitution within $`\varepsilon`$ against the
admitted tests of the `AdmissibleDistinguishers` instance in scope (the substitution calculus,
below), [`𝓡 —[π]→ 𝒮`][notation-constructs] for $`\mathcal R \xrightarrow{\pi} \mathcal S`$ and
[`𝓡 —[π; ε]→ 𝒮`][notation-constructsWithin] for
$`\mathcal R \xrightarrow{\pi,\ \varepsilon} \mathcal S`$ (constructions, below), and
[`G |≡ T`][notation-conditionallyEquivalent] for $`G \mathrel{|\!\equiv} T`$, the field of
`DistinctionGames`.

`Notation.lean`, above the instances and the proof commands, defines no new notation. It
registers the normalization rules for interfaces, including
[`Interface.cc_parallel_eq`][Interface.cc_parallel_eq], which identifies `∥` with
`TypedSystem.parallel`, and adds typed carrier-hint handlers for `Δ` and `∥`: they first read
each operand as a typed system on its own interface, so that the interfaces and budgets of
attachments such as `Δ (α • R) (α • S)` and `α • R ∥ β • S` are inferred, and otherwise restore
the elaboration state and defer to the generic handlers. Both paths produce the same selected
`distance` or `parallel`; on another resource theory `Δ` and `∥` keep that theory's own metric
and parallel operation.

## Specifications and constructions

*A specification is a set of resources; a converter constructs one specification from another
[6, §§2–4]. The carrier-free notions hold for any map; the others are stated on the classes
above.*

```math
\mathcal R \xrightarrow{\ \pi\ } \mathcal S \;:\iff\; \pi\mathcal R \subseteq \mathcal S,
\qquad
\mathcal R \xrightarrow{\ \pi,\ \varepsilon\ } \mathcal S \;:\iff\;
\forall R \in \mathcal R\ \exists S \in \mathcal S.\ d(\pi R, S) \le \varepsilon .
```

A [**specification**][Specification] is a set; [exact][Specification.Constructs] and
[approximate][Specification.ConstructsWithin] construction are as above, for any map. On a
cryptographic algebra the map is attachment, giving [exact][CA.Specification.Constructs] and
[approximate][CA.Specification.ConstructsWithin] construction by a converter. Constructions
compose serially [6, Lemma 1],
$`\mathcal R \xrightarrow{\pi_2} \mathcal S \xrightarrow{\pi_1} \mathcal T \Rightarrow \mathcal R \xrightarrow{\pi_1 \gg \pi_2} \mathcal T`$,
[exactly][Constructs.serial] and [approximately][ConstructsWithin.serial] with added errors, and in
parallel, $`\mathcal R \parallel \mathcal R' \xrightarrow{\pi \otimes \pi'} \mathcal S \parallel \mathcal S'`$,
[exactly][Constructs.parallel] and [approximately][ConstructsWithin.parallel].

A [**relaxation**][Relaxation] maps each $`R`$ to a set $`\mathcal R' \ni R`$, lifted to
specifications by union. A relaxation is [compatible][Relaxation.Compatible] when
[it preserves construction][Relaxation.compatible_iff], and compatible relaxations
[pass through serial constructions][Constructs.relax_serial]. The
[**ε-relaxation**][epsilonRelaxation]
$`\mathcal R^\varepsilon = \lbrace R' \mid \exists R \in \mathcal R.\ d(R, R') \le \varepsilon \rbrace`$
[turns approximate construction into exact construction][constructs_epsilonRelaxation_iff],
$`\mathcal R \xrightarrow{\pi} \mathcal S^\varepsilon \iff \mathcal R \xrightarrow{\pi,\ \varepsilon} \mathcal S`$,
and its errors [add under serial composition][Constructs.serial_epsilonRelaxation].

The [**star relaxation**][CA.star] [6, §3.4, Lemma 3]
$`\mathcal R^{*} = \lbrace \sigma R \mid \sigma \in \Sigma,\ R \in \mathcal R \rbrace`$ is
[idempotent][star_idem], a [closure operator][starClosure], and
[exact construction survives star-relaxing both ends][Constructs.star] for a converter commuting
with the class. A [**simulator**][constructs_of_simulator] [6, Lemma 5] $`\sigma \in \Sigma`$ with
$`d(\pi R, \sigma S) \le \varepsilon`$ gives
$`\lbrace R \rbrace \xrightarrow{\pi} (\lbrace S \rbrace^{*})^{\varepsilon}`$. Other relaxations and
judgments are the [kernel relaxation][kernel] of a map, [test-bounded specifications][gameSpec],
and [constructibility][Constructible] by a class of constructors.

## The substitution calculus

*Stated over any [`ResourceTheory`][ResourceTheory] [9, Chapter 2 and §4.1.4],
[7, Definitions 2.2.6–2.2.9 and Theorem 2.2.10].*

### Substitution relations and implication witnesses

A [**substitution relation**][SubstitutionRelation] $`\simeq`$ relates resources on one
interface [9, Definition 2.3.1]:

```math
S \simeq T \Rightarrow T \simeq S, \qquad S \simeq T \simeq U \Rightarrow S \simeq U, \qquad
S \simeq T \Rightarrow \rho S \simeq \rho T .
```

An [**implication witness**][Implication] from assumptions $`S_i \simeq T_i`$ to a target
$`X \simeq Y`$ is a chain [9, §2.3.1]:

```math
X = \rho_0 S_{i_0}^{b_0} \simeq \rho_0 S_{i_0}^{\lnot b_0} = \rho_1 S_{i_1}^{b_1} \simeq \cdots \simeq \rho_k S_{i_k}^{\lnot b_k} = Y .
```

A witness [counts the uses][Implication.usageCount] of each assumption. The hybrid argument
[9, Lemma 2.3.2] holds [for a substitution relation][substitutes_of_hybrid] and
[for distances][distance_hybrid_le]. A witness [is valid][Implication.substitutes], taking valid
assumptions to its target, and [distances add][Implication.distance_le] along it. Witnesses can be
[transformed by a converter][Implication.map], [reversed][Implication.reverse] and
[appended][Implication.append], and [use counts add][usageCount_append] under appending. The
derivable targets form the [generated relation][generatedRelation], and they
[hold in every substitution relation satisfying the assumptions][derivable_substitutes].

### Distinguisher-indexed substitution

A [**distinguisher advantage**][DistinguisherAdvantage] gives admitted distinguishers
$`\mathcal D_A`$ and an advantage $`\Delta_D`$, a pseudo-distance for each $`D`$.
[Substitution within an error *function*][SubstitutesWithin] [9, §2.3.3]:

```math
S \simeq_{\varepsilon} T \;:\iff\; \forall D \in \mathcal D_A.\ \Delta_D(S, T) \le \varepsilon(D) .
```

Substitution is [symmetric][SubstitutesWithin.symm], and [errors add][SubstitutesWithin.trans]:
$`S \simeq_\varepsilon T \simeq_{\varepsilon'} U \Rightarrow S \simeq_{\varepsilon + \varepsilon'} U`$.
A statistical step gives a substitution within a constant error,
[from a distance bound][SubstitutesWithin.of_distance] $`d(S, T) \le \varepsilon`$ when
$`\Delta_D \le d`$, and more generally
[from any statistical bound dominating the advantage][SubstitutesWithin.of_statistical]. Reduction [9, p. 16],
$`S \simeq_\varepsilon T \Rightarrow \rho S \simeq_{\varepsilon(\cdot \circ \rho)} \rho T`$,
transports substitutions [through one converter][SubstitutesWithin.attach] and
[through a serial composition][SubstitutesWithin.attach_serial]. In mixed chains
[7, Theorem 2.2.10], the [assumption uses][Implication.substitutesWithin] and the
[statistical steps][Implication.substitutesWithin_of_mixed] along a witness add up.

**From decisions.** [`DistinguisherAdvantage`][DistinguisherAdvantage] is a structure with an
arbitrary per-test pseudo-distance. The decision layer supplies one for every admitted set,
[`Distinguishers.distinguisherAdvantage`][Distinguishers.distinguisherAdvantage]: its field
`admissible` is that set, its field `advantage` is the decision advantage
$`\lvert p(d, R) - p(d, S) \rvert`$, and its laws follow from those of the absolute value. For
the `AdmissibleDistinguishers` instance in scope, $`R \simeq_\varepsilon S`$ against this model is
written [`R ≃[ε] S`][notation-substitutes], and every security notion of Commons is stated this
way, on interfaces with the [typed distinguishers][TypedDistinguisher].

A converter $`\alpha`$ absorbed into a distinguisher is the reduction of a security proof [3]. A
substitution [transports through $`\alpha`$][AdmissibleDistinguishers.substitutesWithin_attach]
given the proof `ClosedUnder α`, with its loss read at the actual reduced distinguisher
[9, §2.3.3, p. 16]:

```math
R \simeq_\varepsilon S,\quad \alpha \text{ preserves admission}
\quad\Longrightarrow\quad \alpha R \simeq_{d \mapsto \varepsilon(d\alpha)} \alpha S .
```

[`AdmissibleDistinguishers.substitutesWithin_context`][AdmissibleDistinguishers.substitutesWithin_context]
states the same with the outer systems named. In a chain of contexts the closure proofs of the
named transformations are composed with [`ClosedUnder.comp`][ClosedUnder.comp]; no other
converter needs one. A statistical step needs domination of the decision advantage by the
metric; on interfaces it is
[`Interface.distinguisherAdvantageDominated`][Interface.distinguisherAdvantageDominated], from the
[systems-level bound][DistinguisherBehavior.advantage_le_transcriptDistance]
$`\mathrm{Adv}_d(R, S) \le \Delta(R, S)`$, for every admitted set.

For an unrestricted per-distinguisher statement, select
[`AdmissibleDistinguishers.all`][AdmissibleDistinguishers.all] locally with
`let := AdmissibleDistinguishers.all`; on interfaces it admits every compatible stopping
distinguisher behavior, and
[`AdmissibleDistinguishers.all_closedUnder`][AdmissibleDistinguishers.all_closedUnder] discharges
every closure hypothesis. It is not an instance, so importing it selects no global security
model. Taking each assumption's own advantage for its error gives the explicit reduction
inequalities in [`Tests.AllDistinguishers`](../Tests/AllDistinguishers.lean): the fresh-seed PRG
bound $`\mathrm{Adv}_H(D) \le \mathrm{Adv}_G(D\mathcal R_1) + \mathrm{Adv}_G(D\mathcal R_2)`$
and the corrected AE bound with two `int-ptxt` terms, two `ind-cca` terms and collision error
$`q_{\mathrm{enc}}^2/|M|`$. The bounds are symbolic in the scheme, budgets and $`D`$; no
computational claim is made.

### Substitution relaxations and constructions

The [**substitution image**][substitutionImage] collects the transformed endpoints of a one-use
substitution [9, §4.1.4] and gives a [relaxation][singleSubstitutionRelaxation]. The
[**substitution relaxation**][substitutionRelaxation] of a specification is the resources
substituting for a member; it is [compatible with converters][substitutionRelaxation_compatible]
and [idempotent][substitutionRelaxation_idem]. Constructions with simulators
compose [9, Definition 2.4.3 and Theorem 2.4.4]: a witness
[gives serial simulators][Implication.exists_serial_simulators], and
[derivable constructions compose serially][Constructs.derivable_serial_simulators].

<!-- Declarations: the classes -->

[ResourceTheory]: CryptographicAlgebra/Basic.lean#L64
[ResourceTheory.functor]: CryptographicAlgebra/Basic.lean#L98
[CryptographicAlgebra]: CryptographicAlgebra/Basic.lean#L139
[CA.parallel]: CryptographicAlgebra/Basic.lean#L185
[CA.dummy]: CryptographicAlgebra/Basic.lean#L196
[CA.attach_parallel]: CryptographicAlgebra/Basic.lean#L234
[CA.parallel_assoc]: CryptographicAlgebra/Basic.lean#L266
[CA.parallel_dummy_left]: CryptographicAlgebra/Basic.lean#L284
[CA.parallel_dummy_right]: CryptographicAlgebra/Basic.lean#L302
[CompatiblePseudoMetric]: CryptographicAlgebra/PseudoMetric.lean#L59
[CA.distance]: CryptographicAlgebra/PseudoMetric.lean#L95
[distance_attach_le]: CryptographicAlgebra/PseudoMetric.lean#L127
[distance_eq_of_mutual_attach]: CryptographicAlgebra/PseudoMetric.lean#L177
[distance_parallel_le]: CryptographicAlgebra/PseudoMetric.lean#L218
[advantageDistance]: CryptographicAlgebra/Distinguisher.lean#L56
[CompatibleDistinguisherClass]: CryptographicAlgebra/Distinguisher.lean#L115
[CompatibleDistinguisherClass.ofClosure]: CryptographicAlgebra/Distinguisher.lean#L173
[Games]: Game.lean#L53
[Games.absorb]: Game.lean#L69
[Games.absorb_comp]: CryptographicAlgebra/Game.lean#L92
[DistinctionGames]: Game.lean#L131
[DistinctionGames.absorb]: CryptographicAlgebra/Game.lean#L136

<!-- Declarations: the instances and the notation -->

[Interface.category]: Instances/Category.lean#L30
[Interface.identity_attach]: Instances/Category.lean#L52
[Interface.comp_smul]: Instances/Category.lean#L57
[Interface.monoidal]: Instances/Monoidal.lean#L162
[Interface.resourceTheory]: Instances/Algebra.lean#L79
[Interface.cryptographicAlgebra]: Instances/Algebra.lean#L158
[Interface.transcriptDistance_eq_advantageDistance]: Instances/Algebra.lean#L216
[Interface.compatibleDistinguisherClass]: Instances/Algebra.lean#L238
[Interface.cc_parallel_eq]: Instances/Algebra.lean#L265
[Interface.cc_dummy_eq]: Instances/Algebra.lean#L269
[Interface.cc_distance_eq]: Instances/Algebra.lean#L274
[TypedSystem.transcriptPseudoEMetricSpace]: ../RandomSystems/Typed/Distance.lean#L22
[RandomSystem.transcriptDistance_eq_iSup_behavior]: ../RandomSystems/Distance/Distinguisher.lean#L246
[Interface.games]: Instances/Game.lean#L73
[Interface.distinctionGames]: Instances/Game.lean#L103
[Domain.SolverBehavior]: ../RandomSystems/Game/MBOAttachment.lean#L2174
[Interface.win_le]: Instances/Game.lean#L153
[Interface.dist_visible_le]: Instances/Game.lean#L169
[Interface.conditionallyEquivalent_ofPDG_iff]: Instances/Game.lean#L183
[Interface.game_dist_le]: Instances/Game.lean#L196
[notation-distance]: Notation/Basic.lean#L36
[notation-parallel]: Notation/Basic.lean#L48
[notation-constructs]: Notation/Basic.lean#L82
[notation-constructsWithin]: Notation/Basic.lean#L88
[notation-substitutes]: Notation/Basic.lean#L75
[notation-conditionallyEquivalent]: Notation/Basic.lean#L94

<!-- Declarations: specifications and constructions -->

[Specification]: Specification/Defs.lean#L26
[Specification.Constructs]: Specification/Basic.lean#L41
[Specification.ConstructsWithin]: Specification/Metric.lean#L45
[CA.Specification.Constructs]: CryptographicAlgebra/Basic.lean#L489
[CA.Specification.ConstructsWithin]: CryptographicAlgebra/PseudoMetric.lean#L261
[Constructs.serial]: CryptographicAlgebra/Basic.lean#L579
[ConstructsWithin.serial]: CryptographicAlgebra/PseudoMetric.lean#L331
[Constructs.parallel]: CryptographicAlgebra/Basic.lean#L678
[ConstructsWithin.parallel]: CryptographicAlgebra/PseudoMetric.lean#L359
[Relaxation]: Specification/Relaxation/Defs.lean#L42
[Relaxation.Compatible]: CryptographicAlgebra/Relaxation.lean#L65
[Relaxation.compatible_iff]: CryptographicAlgebra/Relaxation.lean#L132
[Constructs.relax_serial]: CryptographicAlgebra/Relaxation.lean#L197
[epsilonRelaxation]: CryptographicAlgebra/Epsilon.lean#L61
[constructs_epsilonRelaxation_iff]: CryptographicAlgebra/Epsilon.lean#L207
[Constructs.serial_epsilonRelaxation]: CryptographicAlgebra/Epsilon.lean#L274
[CA.star]: CryptographicAlgebra/Star.lean#L85
[star_idem]: CryptographicAlgebra/Star.lean#L124
[starClosure]: Specification/Star.lean#L80
[Constructs.star]: CryptographicAlgebra/Star.lean#L189
[constructs_of_simulator]: CryptographicAlgebra/Star.lean#L363
[kernel]: Specification/Relaxation/Kernel.lean#L25
[gameSpec]: Specification/Game/Basic.lean#L41
[Constructible]: Construction/Defs.lean#L44

<!-- Declarations: the substitution calculus -->

[SubstitutionRelation]: Substitution/Basic.lean#L76
[Implication]: Substitution/Basic.lean#L270
[Implication.usageCount]: Substitution/Basic.lean#L330
[substitutes_of_hybrid]: Substitution/Basic.lean#L135
[distance_hybrid_le]: Substitution/Basic.lean#L200
[Implication.substitutes]: Substitution/Basic.lean#L339
[Implication.distance_le]: Substitution/Basic.lean#L392
[Implication.map]: Substitution/Implication.lean#L177
[Implication.reverse]: Substitution/Implication.lean#L216
[Implication.append]: Substitution/Implication.lean#L273
[usageCount_append]: Substitution/Implication.lean#L349
[generatedRelation]: Substitution/Implication.lean#L402
[derivable_substitutes]: Substitution/Implication.lean#L431
[SubstitutesWithin]: Substitution/Reduction.lean#L80
[SubstitutesWithin.symm]: Substitution/Reduction.lean#L92
[SubstitutesWithin.trans]: Substitution/Reduction.lean#L108
[SubstitutesWithin.of_distance]: Substitution/Reduction.lean#L156
[SubstitutesWithin.of_statistical]: Substitution/Reduction.lean#L130
[SubstitutesWithin.attach]: Substitution/Reduction.lean#L182
[SubstitutesWithin.attach_serial]: Substitution/Reduction.lean#L233
[Implication.substitutesWithin]: Substitution/Quantitative.lean#L84
[Implication.substitutesWithin_of_mixed]: Substitution/Quantitative.lean#L157
[Domain.DistinguisherBehavior]: ../RandomSystems/Distance/Distinguisher.lean#L207
[DistinguisherBehavior.advantage_le_transcriptDistance]: ../RandomSystems/Distance/Distinguisher.lean#L238
[DistinguisherBehavior.absorb]: ../RandomSystems/Distance/Distinguisher.lean#L291
[Interface.distinguisherEvaluations]: Instances/Algebra.lean#L164
[Interface.distinguisherAction]: Instances/Algebra.lean#L170
[Interface.distinguisherAdvantageDominated]: Instances/Algebra.lean#L292
[DistinguisherAdvantage]: Distinguisher.lean#L54
[Distinguishers]: Distinguisher.lean#L89
[AdmissibleDistinguishers]: Distinguisher.lean#L100
[AdmissibleDistinguishers.all]: Distinguisher.lean#L110
[Distinguishers.advantage]: Distinguisher.lean#L125
[Distinguishers.distinguisherAdvantage]: Distinguisher.lean#L132
[DistinguisherAction]: CryptographicAlgebra/DistinguisherAction.lean#L51
[DistinguisherAction.advantage_absorb]: CryptographicAlgebra/DistinguisherAction.lean#L77
[ClosedUnder]: CryptographicAlgebra/DistinguisherAction.lean#L96
[ClosedUnder.comp]: CryptographicAlgebra/DistinguisherAction.lean#L106
[AdmissibleDistinguishers.substitutesWithin_attach]: CryptographicAlgebra/DistinguisherAction.lean#L123
[AdmissibleDistinguishers.substitutesWithin_context]: CryptographicAlgebra/DistinguisherAction.lean#L141
[AdmissibleDistinguishers.all_closedUnder]: CryptographicAlgebra/DistinguisherAction.lean#L158
[DominatedByDistance]: CryptographicAlgebra/DistinguisherAction.lean#L173
[TypedDistinguisher]: ../RandomSystems/Typed/Distinguisher.lean#L37
[TypedDistinguisher.absorb]: ../RandomSystems/Typed/Distinguisher.lean#L43
[TypedDistinguisher.probability_absorb]: ../RandomSystems/Typed/Distinguisher.lean#L49
[TypedDistinguisher.absorb_id]: ../RandomSystems/Typed/Distinguisher.lean#L54
[TypedDistinguisher.absorb_comp]: ../RandomSystems/Typed/Distinguisher.lean#L62
[substitutionImage]: Substitution/Relaxation.lean#L71
[singleSubstitutionRelaxation]: Substitution/Relaxation.lean#L92
[substitutionRelaxation]: Substitution/Relaxation.lean#L232
[substitutionRelaxation_compatible]: Substitution/Relaxation.lean#L258
[substitutionRelaxation_idem]: Substitution/Relaxation.lean#L283
[Implication.exists_serial_simulators]: Substitution/Construction.lean#L69
[Constructs.derivable_serial_simulators]: Substitution/Construction.lean#L154
[Domain.Distinguisher.advantage_le_winProbability]: ../RandomSystems/Game/MBO.lean#L758
[Domain.Distinguisher.exists_absorbRight]: ../RandomSystems/Distance/Distinguisher.lean#L330
[Domain.SolverBehavior.absorb]: ../RandomSystems/Game/MBOAttachment.lean#L2213
[Interface]: ../RandomSystems/Typed/Interface.lean#L42
[Interface.associator]: Instances/Monoidal.lean#L52
[Interface.associator_naturality]: Instances/Monoidal.lean#L92
[Interface.distinguishers]: Instances/Algebra.lean#L179
[Interface.distinguishers_attach]: Instances/Algebra.lean#L184
[Interface.distinguishers_parallel_left]: Instances/Algebra.lean#L190
[Interface.distinguishers_parallel_right]: Instances/Algebra.lean#L207
[Interface.id_tensor_id]: Instances/Monoidal.lean#L84
[Interface.isoOf]: Instances/Monoidal.lean#L33
[Interface.leftUnitor]: Instances/Monoidal.lean#L57
[Interface.leftUnitor_naturality]: Instances/Monoidal.lean#L97
[Interface.monoidalStruct]: Instances/Monoidal.lean#L71
[Interface.parallel_assoc]: Instances/Algebra.lean#L93
[Interface.parallel_dummy_left]: Instances/Algebra.lean#L105
[Interface.parallel_dummy_right]: Instances/Algebra.lean#L114
[Interface.parallel_swap]: Instances/Algebra.lean#L123
[Interface.pentagon]: Instances/Monoidal.lean#L105
[Interface.resourcesLaxMonoidal]: Instances/Algebra.lean#L132
[Interface.rightUnitor]: Instances/Monoidal.lean#L61
[Interface.rightUnitor_naturality]: Instances/Monoidal.lean#L101
[Interface.solvers]: Instances/Game.lean#L67
[Interface.swap]: Instances/Monoidal.lean#L66
[Interface.tensor]: ../RandomSystems/Typed/Parallel.lean#L85
[Interface.tensor_comp]: Instances/Monoidal.lean#L87
[Interface.triangle]: Instances/Monoidal.lean#L132
[Interface.unit]: ../RandomSystems/Typed/InterfaceCoherence.lean#L90
[Interface.winners]: Instances/Game.lean#L62
[PDCBehavior.attach]: ../RandomSystems/Converter/ConverterAttachment.lean#L157
[PDCBehavior.attach_comp]: ../RandomSystems/Converter/ConverterAttachment.lean#L277
[PDCBehavior.attach_id]: ../RandomSystems/Converter/ConverterAttachment.lean#L264
[PDCBehavior.comp_assoc]: ../RandomSystems/Converter/PDCBehavior.lean#L343
[PDCBehavior.comp_id]: ../RandomSystems/Converter/PDCBehavior.lean#L381
[PDCBehavior.comp_tensor]: ../RandomSystems/Converter/ConverterTensor.lean#L745
[PDCBehavior.id_comp]: ../RandomSystems/Converter/PDCBehavior.lean#L391
[PDCBehavior.liftMBO]: ../RandomSystems/Game/MBOAttachment.lean#L460
[PDCBehavior.liftMBO_comp]: ../RandomSystems/Game/MBOAttachment.lean#L1520
[PDCBehavior.liftMBO_id]: ../RandomSystems/Game/MBOAttachment.lean#L500
[PDCBehavior.tensor_id]: ../RandomSystems/Converter/ConverterTensor.lean#L705
[RandomSystem.ConditionallyEquivalent]: ../RandomSystems/Game/MBO.lean#L525
[RandomSystem.MonotoneMBO]: ../RandomSystems/Game/MBO.lean#L305
[RandomSystem.parallel]: ../RandomSystems/Cumulative/CumulativeOperations.lean#L130
[RandomSystem.visible]: ../RandomSystems/Game/MBO.lean#L340
[RandomSystem.visible_attach_liftMBO]: ../RandomSystems/Game/MBOAttachment.lean#L624
[TypedConverter]: ../RandomSystems/Typed/Interface.lean#L129
[TypedConverter.attach]: ../RandomSystems/Typed/Interface.lean#L192
[TypedConverter.attachGame]: ../RandomSystems/Typed/Game.lean#L45
[TypedConverter.comp]: ../RandomSystems/Typed/Interface.lean#L136
[TypedConverter.comp_associator]: ../RandomSystems/Typed/ConverterCoherence.lean#L158
[TypedConverter.comp_leftUnitor]: ../RandomSystems/Typed/ConverterCoherence.lean#L195
[TypedConverter.comp_rightUnitor]: ../RandomSystems/Typed/ConverterCoherence.lean#L224
[TypedConverter.comp_smul]: ../RandomSystems/Typed/Interface.lean#L212
[TypedConverter.id]: ../RandomSystems/Typed/Interface.lean#L141
[TypedConverter.identity_attach]: ../RandomSystems/Typed/Interface.lean#L206
[TypedConverter.parallel]: ../RandomSystems/Typed/Parallel.lean#L210
[TypedConverter.parallel_attach]: ../RandomSystems/Typed/ParallelAttachment.lean#L23
[TypedConverter.parallel_rename]: ../RandomSystems/Typed/TensorRename.lean#L128
[TypedConverter.rename]: ../RandomSystems/Typed/Relabel.lean#L48
[TypedConverter.rename_comp]: ../RandomSystems/Typed/Relabel.lean#L80
[TypedConverter.rename_mass]: ../RandomSystems/Typed/SystemParallel.lean#L55
[TypedConverter.rename_refl]: ../RandomSystems/Typed/Relabel.lean#L67
[TypedGame]: ../RandomSystems/Typed/Game.lean#L42
[TypedGame.visible]: ../RandomSystems/Typed/Game.lean#L86
[TypedSystem]: ../RandomSystems/Typed/Interface.lean#L94
[TypedSystem.dummy]: ../RandomSystems/Typed/SystemCoherence.lean#L97
[TypedSystem.parallel]: ../RandomSystems/Typed/Parallel.lean#L153
[TypedSystem.parallel_assoc_mass]: ../RandomSystems/Typed/SystemCoherence.lean#L85
[TypedSystem.parallel_swap_mass]: ../RandomSystems/Typed/SystemCoherence.lean#L153
[TypedSystem.parallel_unit_left_mass]: ../RandomSystems/Typed/SystemCoherence.lean#L103
[TypedSystem.parallel_unit_right_mass]: ../RandomSystems/Typed/SystemCoherence.lean#L128

[Games.win_le_of_reduction]: Game.lean#L85
[Problem.performance_le_of_reduction]: Problem.lean#L50
[Interface.gameAction]: Instances/Game.lean#L78
[Interface.distinctionGameAction]: Instances/Game.lean#L136
[Domain.SolverBehavior.decision]: ../RandomSystems/Game/MBOAttachment.lean#L2185
[Domain.SolverBehavior.decision_absorb]: ../RandomSystems/Game/MBOAttachment.lean#L2234
[TypedConverter.identity_attachGame]: ../RandomSystems/Typed/Game.lean#L61
[TypedConverter.comp_attachGame]: ../RandomSystems/Typed/Game.lean#L71

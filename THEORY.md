# The theory, layer by layer

This is a cheat-sheet of what the library formalizes. It starts with **random systems** and their
properties, then packages them: first into **interfaces, resources and converters**, then into the
**abstract layers** (classes of assumptions, up to categories), each shown with the instance that
connects it to the systems. It ends with what the layers are used for: **constructions**, the
**substitution calculus**, the **DSL** and the **examples**. Every notion and result is linked, in
the text, to its Lean declaration; citations refer to the [references](#references) at the end.

```
Probability ─▶ Random systems ─▶ Interfaces, resources, converters ══ instance ══▶ Classes
  (App. A)        (§1)                    (§2)                                     (§3)
                                            ▲                                        │
                                           DSL (§6)                                  ▼
                                                               Constructions (§4) ─▶ Substitution (§5)
```

---

## 1. Random systems

*Systems over finite alphabets, answering exactly on a bounded domain [1], [2, Chapter 2],
[3, Chapter 3]. Laws are finitely supported distributions and $`\delta`$ is the statistical
distance (Appendix A).*

### 1.1 Deterministic systems

A [**deterministic system**][IsDDS] (DDS) is a [partial function][System] from input histories to
the next output, $s : \mathcal X^{*} \rightharpoonup \mathcal Y$, [silent at the empty
history][SilentAtEmpty], whose domain is [closed under nonempty prefixes][PrefixClosed]. Systems
are [wired together][interconnect], each output leaving the wiring or returning as an input. A
system [replies][Replies] $y_1 \dots y_n$ to $x_1 \dots x_n$ when it answers each prefix with the
next output, and a DDS [is determined by its completed replies][IsDDS.eq_of_replies_iff]. An
[automaton][automatonSystem] is a transition function started in a state, and
[bisimilar][IsBisim] automata [have the same system][automatonSystem_eq_of_bisim]. An
[environment][DDE] (DDE) chooses the next query from the replies so far.

### 1.2 Probabilistic systems

A [**domain**][Domain] $\mathcal D$ admits next queries after each transcript, with a bound on the
length. A [**PDS**][PDS] is a finite distribution over DDSs [with domain][HasDomain]
$\mathcal D$ [1, Definition 8]. A [**random system**][RandomSystem] is given by its cumulative
probabilities $p$ on transcripts [1, after Lemma 5], [normalized][IsRandomSystem] on the domain:

$$
p(\varepsilon) = 1, \qquad p \ge 0, \qquad
\sum_{y} p\big(h \cdot (x, y)\big) =
\begin{cases} p(h) & \text{if } x \text{ is admitted after } h, \\ 0 & \text{otherwise.} \end{cases}
$$

A PDS [has a random system][PDS.behavior], and [equivalent][Equivalent] PDSs
[have the same one][PDS.behavior_eq_iff]. Every random system
[has a finite presentation][RandomSystem.exists_presentation], so random systems
[are exactly the classes of equivalent PDSs][RandomSystem.ofPDSClass_bijective]. Two random
systems [are equal exactly when][RandomSystem.eq_iff_sLaw] their
[transcript laws][RandomSystem.sLaw] agree in every [compatible][RandomSystem.Compatible]
environment, and on a domain of input histories
[fixed query sequences suffice][RandomSystem.eq_iff_sLaw_fixedQueries] [1, Lemma 5]. Random
systems on one domain form [mixtures][RandomSystem.mix], and two random systems run
[independently in parallel][RandomSystem.parallel] form one on the combined alphabets.

### 1.3 Converters

A [**DDC**][IsDDC] is a system on the converter alphabets (outside queries and inside replies in;
inside queries and outside replies out) with at most $b$ consecutive inside queries
[3, Definition 3.8]. A **DDC from $E$ to $F$** ([`IsDDCFrom`][IsDDCFrom]) answers exactly the
[converter domain][converterDomain] and queries only in $E$; attached to a system with domain $E$
it [gives one with domain][IsDDCFrom.mapsDomain] $F$. A [**PDC**][PDCBehavior.ofPDC] is a distribution over DDCs, and
its [**behavior**][PDCBehavior] is a random system over the converter domain
[3, Definitions 3.17–3.18].

[Serial composition][serialM] $\beta \odot \alpha$ connects the inside of $\beta$ to the outside
of $\alpha$, and [DDCs compose][IsDDC.comp] with the product of their bounds. PDC behaviors have a
[composition][PDCBehavior.comp] and an [identity][PDCBehavior.id], with
[associativity][PDCBehavior.comp_assoc] and the [left][PDCBehavior.id_comp] and
[right][PDCBehavior.comp_id] identity laws. [Attachment][PDCBehavior.attach] samples the PDC, then
attaches the sample deterministically: [presentations attach to
presentations][PDCBehavior.attach_presents], [the identity leaves a system
unchanged][PDCBehavior.attach_id], and [a composition attaches its inner converter
first][PDCBehavior.attach_comp]. [Parallel composition][PDCBehavior.tensor] samples two PDCs
independently and runs them side by side, with [interchange][PDCBehavior.comp_tensor] against
serial composition.

A [**program**][Program] is a deterministic oracle body: from its state, the outside query and the
inside exchanges of the current invocation, it computes the reply or the next inside query. A
program can be [bounded][Program.Bounded] (at most $b$ inside queries per invocation), have
[exact costs][Program.Costs], or [preserve a partial port map][Program.PortPreserving]
$\iota : O \to \mathrm{Option}\ J$: an invocation at $o$ queries the labels in the image of
$\iota$ only at $\iota(o)$, at most once, and none of them when $\iota(o)$ is none, so it
queries $\iota(o)$ [at most as often as it is queried at][DDC.insideQueries_restrict_length_le]
$o$. On an outside domain, a bounded program
[is a DDC from every inside domain containing its inside queries][DDC.ofProgramOn_isDDCFrom].
Attached to an automaton, a program is [inlined][Program.inline] [4, §3.3]: the result is the
[combined automaton][Program.combine] on pairs of states, also
[on domains][Program.trim_apply_ofProgramOn_automaton].

### 1.4 Distance and distinguishers

The [**transcript distance**][RandomSystem.transcriptDistance] takes the supremum over environments
$E$ [compatible with the domain][Domain.Compatible] and [bounded][QueryBounded] to $n$ queries; a
[**probabilistic distinguisher**][Domain.Distinguisher] $P$ [1, Definition 9] has an
[advantage][Domain.Distinguisher.advantage]:

$$
\Delta(R, S) = \sup_{E,\, n}\ \delta\big(\mathrm{tr}(R, E, n),\ \mathrm{tr}(S, E, n)\big),
\qquad
\mathrm{Adv}_P(R, S) = \big\lvert \Pr[P(R) = 1] - \Pr[P(S) = 1] \big\rvert .
$$

A probabilistic distinguisher is a distribution over
[deterministic distinguishers][IsDDD] [compatible with the domain][Domain.DecisionCompatible], and its
[probability of outputting 1][Domain.Distinguisher.probability] averages their
[decision probabilities][RandomSystem.decisionProbability]. For each $P$, $\mathrm{Adv}_P$ is a
pseudo-distance: it is [zero on equal systems][advantage_self], [symmetric][advantage_symm], and
[satisfies the triangle inequality][advantage_triangle]. The transcript distance
[is the largest advantage][RandomSystem.transcriptDistance_eq_iSup],
$\Delta(R, S) = \sup_P \mathrm{Adv}_P(R, S)$, so
[every advantage is at most the distance][advantage_le_transcriptDistance].

**Absorption**: [absorbing][Domain.Distinguisher.absorb] a PDC $\alpha$ into $P$ gives
$P \circ \alpha$, with [the same probability of outputting 1][probability_absorb],
$\Pr[(P \circ \alpha)(R) = 1] = \Pr[P(\alpha R) = 1]$; on deterministic distinguishers it
[connects the distinguisher to the converter's outside][absorbAll]. Absorbing a converter
[gives a distinguisher][Domain.Distinguisher.exists_absorbAll], and so does absorbing
[a system run beside][Domain.Distinguisher.exists_absorbRight].

**Restriction**: the [restriction][RandomSystem.restrict] $R \restriction D'$ of a random system on $D$
to a smaller domain $D' \subseteq D$ keeps the masses of the transcripts $D'$ admits and is zero
elsewhere. Restrictions [compose][RandomSystem.restrict_restrict], and an environment compatible
with $D'$ [sees the transcript law of the system itself][RandomSystem.sLaw_restrict], so restriction
[does not increase the distance][RandomSystem.transcriptDistance_restrict_le],
$\Delta(R \restriction D', S \restriction D') \le \Delta(R, S)$.

### 1.5 Games

A [**game**][PDG] is a distribution over [deterministic games][DDG], pairs of a DDS and a
[monotone condition][MC], on a domain [2, Definitions 2.20–2.22]. An environment
[wins][DDG.Wins] when it stops where the condition holds, and
$\nu(G) = \sup_e \Pr[e \text{ wins } G]$ is the [largest winning probability][PDG.supWinProbability].
[**Blinding**][PDG.blind] replaces every reply by $()$. [**Game equivalence**][GameEquivalent]
bounds distinguishing by blind winning [5, Definition 13 and Theorem 3]:

$$
\Pr_G[\,y^n,\ \lnot\mathrm{bad} \mid x^n\,] = \big(1 - \Pr_G[\mathrm{bad} \mid x^n]\big)\, S(x^n, y^n)
\quad \Longrightarrow \quad
\delta\big(\mathrm{tr}(G, E, n),\ \mathrm{tr}(S, E, n)\big) \le \nu(G^{\mathrm b}) .
$$

Blind winning is the largest probability of the condition on an admitted query sequence: it
[is at least][PDG.badProbability_le_blind] each such probability and
[at most][PDG.supWinProbability_blind_le] any common bound on them. The implication above is the
[game-equivalence bound][GameEquivalent.statDist_le_blind]. A
[sampled function with a hidden condition][PDG.ofFunction] is a game,
[game-equivalent to the ideal function][PDG.ofFunction_gameEquivalent] once, on every fixed query
sequence, the answers jointly with the unset condition factor through the ideal answers.

---

## 2. Interfaces, resources and converters

*The systems of §1, typed by interfaces [3, Definitions 3.8, 3.9, 3.17], [6, §3],
[7, Definitions 2.2.1–2.2.2].*

### 2.1 The objects

An [**interface**][Interface] $A = (I, X, Y, D)$ has finitely many labels, finite alphabets
$X_i, Y_i$, and a domain $D$ of input histories, prefix-closed, without the empty history, of
bounded length. Two domains recur: the [**query budget**][Interface.queryBudget]
$D = \lbrace h \ne \varepsilon \mid \lvert h \rvert \le q \rbrace$ and the
[**per-port budget**][Interface.portBudget]
$D = \lbrace h \ne \varepsilon \mid \forall i.\ \lvert h \restriction i \rvert \le q_i \rbrace$,
where $h \restriction i$ [keeps the inputs at the label][restrict] $i$.

A [**resource**][Interface.Resource] on $A$ is a random system on
$(\Sigma_i X_i, \Sigma_i Y_i)$ over $D$,
[replying at the queried label][RandomSystem.RepliesAtQueriedInterface]. A
[**converter**][Interface.Converter] $A \to B$ is a PDC behavior from $B$'s domain (inside) to
$A$'s domain (outside), and a DDC between the two domains [is one][Interface.ofDDC].
[**Attachment**][Interface.attach] $\alpha R$ is the attachment of the PDC behavior.
[**Parallel interfaces**][Interface.tensor] put the label sets side by side, and
[parallel resources][Interface.parallel] and [parallel converters][Interface.parallelConverter]
are the independent parallel compositions.

### 2.2 Concrete resources and converters

The [**filter**][Interface.filter] admitting $D$ forwards the queries of admitted histories; it is
a converter $(A \restriction D) \to A$ from the [restricted interface][Interface.restrict].
[Attached to a resource][Interface.filter_smul], it is the [restriction][RandomSystem.restrict] of the
resource's random system to the restricted domain, and
[two filters in series][Interface.filter_comp_filter_smul] act as the filter of both conditions. A
[**constant**][Interface.constant] converter ignores its inside resource and exposes a fixed one,
and the fixed [right][Interface.rightContext] and [left][Interface.leftContext] **contexts** run a
resource beside: [attaching][Interface.attach_rightContext] $\mathrm{rightContext}\ A\ S$ to $R$
gives $R \parallel S$, and so does [attaching][Interface.attach_leftContext]
$\mathrm{leftContext}\ R\ B$ to $S$.

A [**source**][Interface.Resource.source] answers with fresh independent samples of a law
[4, Definition 1]. An [**automaton**][Interface.Resource.ofAutomaton] is a transition function with
a sampled initial state [4, Definition 2], and [parallel automata][Interface.parallel_ofAutomaton]
are the automaton running both side by side. **Functional resources** are given by
[reply functions][Interface.Resource.ofFunction], by
[conditional reply laws][Interface.Resource.ofConditional], or by
[sampling once][Interface.Resource.sample] and keeping the sample.

For a game $G$ presenting $R$ and game-equivalent to $S$,
[the distance is at most blind winning][GameEquivalent.game_dist_le],
$\Delta(R, S) \le \nu(G^{\mathrm b})$, and a
[single-label sampled-function game is game-equivalent][PDG.ofSingleFunction_gameEquivalent] to
the resource sampling the ideal function. Parallel composition is commutative: $R \parallel S$ and
$S \parallel R$ [agree][Interface.parallel_swap] through the [swap][Interface.swap] of the two
interfaces.

**Notation** (`open scoped SystemAlgebra`): [`Δ R S`][notation-distance],
[`R ∥ S`][notation-parallel], [`𝓡 —[π]→ 𝒮`][notation-constructs] for
$\mathcal R \xrightarrow{\pi} \mathcal S$ and [`𝓡 —[π; ε]→ 𝒮`][notation-constructsWithin] for
$\mathcal R \xrightarrow{\pi,\ \varepsilon} \mathcal S$.

---

## 3. The abstract layers and their instances

*Each layer is a class of assumptions: it introduces its notions (attachment, parallel
composition, distance, distinguishers) only as fields and axioms, and knows nothing about
systems [6, §3], [7, §2.2], [8]. Interfaces are an instance of each class: every field is a
systems-level object of §1–2, and every axiom is a theorem about it.*

```
Category ─▶ MonoidalCategory
    │
    ▼
ResourceTheory ─▶ CryptographicAlgebra ─▶ CompatiblePseudoMetric ─▶ CompatibleDistinguisherClass
```

### 3.1 The category of interfaces

Interfaces and converters form a category under serial composition, and a monoidal category under
parallel composition.

Interfaces are an instance of Mathlib's `Category` ([`Interface.category`][Interface.category]):
its field `Hom` is the [PDC behavior][PDCBehavior], `id` is the [identity][PDCBehavior.id] and
`comp` is [serial composition][PDCBehavior.comp]; the axioms `id_comp`, `comp_id` and `assoc` are
discharged by the [left identity][PDCBehavior.id_comp], [right identity][PDCBehavior.comp_id] and
[associativity][PDCBehavior.comp_assoc] laws of PDC behaviors.

They are an instance of `MonoidalCategory` ([`Interface.monoidal`][Interface.monoidal], on the
structure [`Interface.monoidalStruct`][Interface.monoidalStruct]): `tensorObj` is the
[parallel interface][Interface.tensor], `tensorHom` is the
[parallel composition][PDCBehavior.tensor] of PDC behaviors, the unit is the
[interface without labels][Interface.unit], and the [associator][Interface.associator] and the
[left][Interface.leftUnitor] and [right][Interface.rightUnitor] unitors are the regrouping
renamings. The axioms are discharged by [interchange][Interface.tensor_comp], from the
[interchange of PDC behaviors][PDCBehavior.comp_tensor]; the
[tensor of identities][Interface.id_tensor_id], from the
[same law for PDC behaviors][PDCBehavior.tensor_id]; the
[naturality of the associator][Interface.associator_naturality], from
[regrouping arbitrary converters][Interface.comp_associator]; the naturality of the
[left][Interface.leftUnitor_naturality] and [right][Interface.rightUnitor_naturality] unitors,
from the [left][Interface.comp_leftUnitor] and [right][Interface.comp_rightUnitor] unit
regroupings of arbitrary converters; and the [pentagon][Interface.pentagon] and
[triangle][Interface.triangle] identities.

### 3.2 `ResourceTheory C Φ`: attachment

In the class [`ResourceTheory`][ResourceTheory], converters $\alpha : A \to B$ act on resources
$R \in \Phi B$:

$$
\alpha R \in \Phi A, \qquad \mathrm{id}_A\, R = R, \qquad (\alpha \gg \beta)\, R = \alpha\,(\beta\, R) .
$$

Attachment is the [contravariant functor][ResourceTheory.functor]
$\Phi : C^{\mathrm{op}} \to \mathrm{Type}$.

Interfaces are an instance of `ResourceTheory`
([`Interface.resourceTheory`][Interface.resourceTheory]): its field `attach` is the
[attachment of converters to resources][Interface.attach], the systems-level
[attachment of PDC behaviors][PDCBehavior.attach]; its axioms `attach_identity` and
`attach_serial` are discharged by [attaching the identity][Interface.identity_attach] and
[attaching a serial composition][Interface.comp_smul], from the systems-level
[identity][PDCBehavior.attach_id] and [serial][PDCBehavior.attach_comp] attachment laws.

### 3.3 `CryptographicAlgebra C Φ`: parallel composition

The class [`CryptographicAlgebra`][CryptographicAlgebra] is a lax monoidal structure on $\Phi$:
resources [compose in parallel][CA.parallel], with the [dummy resource][CA.dummy] as unit.

$$
R \parallel S \in \Phi(A \otimes B), \qquad \mathbf 1 \in \Phi(\mathbb I), \qquad
(\alpha \otimes \beta)(R \parallel S) = \alpha R \parallel \beta S .
$$

Derived: [locality][CA.attach_parallel], [associativity][CA.parallel_assoc], and the
[left][CA.parallel_dummy_left] and [right][CA.parallel_dummy_right] unit laws.

Interfaces are an instance of `CryptographicAlgebra`
([`Interface.cryptographicAlgebra`][Interface.cryptographicAlgebra]): its field `laxMonoidal` is
[`Interface.resourcesLaxMonoidal`][Interface.resourcesLaxMonoidal], whose product is the
[parallel composition of resources][Interface.parallel], the systems-level
[independent parallel composition][RandomSystem.parallel], and whose unit is the
[dummy resource][Interface.dummy]; naturality, associativity and unitality are discharged by
[locality][Interface.parallel_attach], [associativity][Interface.parallel_assoc] and the
[left][Interface.parallel_dummy_left] and [right][Interface.parallel_dummy_right] unit laws of
parallel resources. The abstract [parallel composition][Interface.cc_parallel_eq] and
[dummy][Interface.cc_dummy_eq] are the concrete ones.

### 3.4 `CompatiblePseudoMetric C Φ`: distance

The class [`CompatiblePseudoMetric`][CompatiblePseudoMetric] adds a pseudo-metric $d$, the
[distance][CA.distance], on each $\Phi A$ [6, Definition 2], [8, Definition 2]:

$$
d(\alpha R, \alpha S) \le d(R, S), \qquad
d(R \parallel R',\ S \parallel S') \le d(R, S) + d(R', S') .
$$

Derived: [attachment is non-expanding][distance_attach_le] and
[parallel composition adds distances][distance_parallel_le]. For interfaces the metric comes from
the distinguisher class below.

### 3.5 `CompatibleDistinguisherClass C Φ`: distinguishers

The class [`CompatibleDistinguisherClass`][CompatibleDistinguisherClass] has a class
$\mathcal D_A$ of maps $\Phi A \to \mathbb R$, closed under absorbing a converter and under running
a fixed resource beside, whose [advantage distance][advantageDistance] is the metric [8, §4.5]:

$$
d(R, S) = \sup_{D \in \mathcal D_A} \lvert D(R) - D(S) \rvert, \qquad
D \in \mathcal D_A \;\Longrightarrow\; D(\alpha\,\cdot\,) \in \mathcal D_B,\ \ D(\,\cdot \parallel T),\ D(T \parallel \cdot\,) \in \mathcal D .
$$

**Closure gives compatibility** [8, Lemma 1]: the advantage distance of a closed class
[is a compatible pseudo-metric][CompatibleDistinguisherClass.ofClosure].

Interfaces are an instance of `CompatibleDistinguisherClass`
([`Interface.compatibleDistinguisherClass`][Interface.compatibleDistinguisherClass], built by
`ofClosure`): its field `distinguishers A` is the [set of maps][Interface.distinguishers]
$R \mapsto \Pr[P(R) = 1]$ for the systems-level [probabilistic distinguishers][Domain.Distinguisher]
$P$ compatible with $A$'s domain. Its axiom `closed_attach` is discharged by
[closure under attachment][Interface.distinguishers_attach], from
[absorbing a converter][Domain.Distinguisher.exists_absorbAll]; `closed_parallel_left` by
[closure under a resource on the right][Interface.distinguishers_parallel_left], from
[absorbing a system run beside][Domain.Distinguisher.exists_absorbRight]; and
`closed_parallel_right` by
[closure under a resource on the left][Interface.distinguishers_parallel_right], from the previous
two through the [swap][Interface.parallel_swap]. Its metric
[is the transcript distance][Interface.cc_distance_eq] of §1.4:

$$
d(R, S) = \Delta(R, S) = \sup_P \mathrm{Adv}_P(R, S) .
$$

---

## 4. Specifications and constructions

*A specification is a set of resources; a converter constructs one specification from another
[6, §§2–4]. The carrier-free notions hold for any map; the others are stated on the classes of §3.*

$$
\mathcal R \xrightarrow{\ \pi\ } \mathcal S \;:\iff\; \pi\mathcal R \subseteq \mathcal S,
\qquad
\mathcal R \xrightarrow{\ \pi,\ \varepsilon\ } \mathcal S \;:\iff\;
\forall R \in \mathcal R\ \exists S \in \mathcal S.\ d(\pi R, S) \le \varepsilon .
$$

A [**specification**][Specification] is a set; [exact][Specification.Constructs] and
[approximate][Specification.ConstructsWithin] construction are as above, for any map. On a
cryptographic algebra the map is attachment, giving [exact][CA.Specification.Constructs] and
[approximate][CA.Specification.ConstructsWithin] construction by a converter. Constructions
compose serially [6, Lemma 1],
$\mathcal R \xrightarrow{\pi_2} \mathcal S \xrightarrow{\pi_1} \mathcal T \Rightarrow \mathcal R \xrightarrow{\pi_1 \gg \pi_2} \mathcal T$,
[exactly][Constructs.serial] and [approximately][ConstructsWithin.serial] with added errors, and in
parallel, $\mathcal R \parallel \mathcal R' \xrightarrow{\pi \otimes \pi'} \mathcal S \parallel \mathcal S'$,
[exactly][Constructs.parallel] and [approximately][ConstructsWithin.parallel].

A [**relaxation**][Relaxation] maps each $R$ to a set $\mathcal R' \ni R$, lifted to
specifications by union. A relaxation is [compatible][Relaxation.Compatible] when
[it preserves construction][Relaxation.compatible_iff], and compatible relaxations
[pass through serial constructions][Constructs.relax_serial]. The
[**ε-relaxation**][epsilonRelaxation]
$\mathcal R^\varepsilon = \lbrace R' \mid \exists R \in \mathcal R.\ d(R, R') \le \varepsilon \rbrace$
[turns approximate construction into exact construction][constructs_epsilonRelaxation_iff],
$\mathcal R \xrightarrow{\pi} \mathcal S^\varepsilon \iff \mathcal R \xrightarrow{\pi,\ \varepsilon} \mathcal S$,
and its errors [add under serial composition][Constructs.serial_epsilonRelaxation].

The [**star relaxation**][CA.star] [6, §3.4, Lemma 3]
$`\mathcal R^{*} = \lbrace \sigma R \mid \sigma \in \Sigma,\ R \in \mathcal R \rbrace`$ is
[idempotent][star_idem], a [closure operator][starClosure], and
[exact construction survives star-relaxing both ends][Constructs.star] for a converter commuting
with the class. A [**simulator**][constructs_of_simulator] [6, Lemma 5] $\sigma \in \Sigma$ with
$d(\pi R, \sigma S) \le \varepsilon$ gives
$\lbrace R \rbrace \xrightarrow{\pi} (\lbrace S \rbrace^{*})^{\varepsilon}$. Other relaxations and
judgments are the [kernel relaxation][kernel] of a map, [test-bounded specifications][gameSpec],
and [constructibility][Constructible] by a class of constructors.

---

## 5. The substitution calculus

*Stated over any [`ResourceTheory`][ResourceTheory] [9, Chapter 2 and §4.1.4],
[7, Definitions 2.2.6–2.2.9 and Theorem 2.2.10].*

### 5.1 Substitution relations and implication witnesses

A [**substitution relation**][SubstitutionRelation] $\simeq$ relates resources on one
interface [9, Definition 2.3.1]:

$$
S \simeq T \Rightarrow T \simeq S, \qquad S \simeq T \simeq U \Rightarrow S \simeq U, \qquad
S \simeq T \Rightarrow \rho S \simeq \rho T .
$$

An [**implication witness**][Implication] from assumptions $S_i \simeq T_i$ to a target
$X \simeq Y$ is a chain [9, §2.3.1]:

$$
X = \rho_0 S_{i_0}^{b_0} \simeq \rho_0 S_{i_0}^{\lnot b_0} = \rho_1 S_{i_1}^{b_1} \simeq \cdots \simeq \rho_k S_{i_k}^{\lnot b_k} = Y .
$$

A witness [counts the uses][Implication.usageCount] of each assumption. The hybrid argument
[9, Lemma 2.3.2] holds [for a substitution relation][substitutes_of_hybrid] and
[for distances][distance_hybrid_le]. A witness [is valid][Implication.substitutes], taking valid
assumptions to its target, and [distances add][Implication.distance_le] along it. Witnesses can be
[transformed by a converter][Implication.map], [reversed][Implication.reverse] and
[appended][Implication.append], and [use counts add][usageCount_append] under appending. The
derivable targets form the [generated relation][generatedRelation], and they
[hold in every substitution relation satisfying the assumptions][derivable_substitutes].

### 5.2 Distinguisher-indexed substitution

A [**distinguisher advantage**][DistinguisherAdvantage] gives admitted distinguishers
$\mathcal D_A$ and an advantage $\Delta_D$, a pseudo-distance for each $D$.
[Substitution within an error *function*][SubstitutesWithin] [9, §2.3.3]:

$$
S \simeq_{\varepsilon} T \;:\iff\; \forall D \in \mathcal D_A.\ \Delta_D(S, T) \le \varepsilon(D) .
$$

Substitution is [symmetric][SubstitutesWithin.symm], and [errors add][SubstitutesWithin.trans]:
$S \simeq_\varepsilon T \simeq_{\varepsilon'} U \Rightarrow S \simeq_{\varepsilon + \varepsilon'} U$.
A statistical step gives a substitution within a constant error,
[from a distance bound][SubstitutesWithin.of_distance] $d(S, T) \le \varepsilon$ when
$\Delta_D \le d$, and more generally
[from any statistical bound dominating the advantage][SubstitutesWithin.of_statistical]. Reduction [9, p. 16],
$S \simeq_\varepsilon T \Rightarrow \rho S \simeq_{\varepsilon(\cdot \circ \rho)} \rho T$,
transports substitutions [through one converter][SubstitutesWithin.attach] and
[through a serial composition][SubstitutesWithin.attach_serial]. In mixed chains
[7, Theorem 2.2.10], the [assumption uses][Implication.substitutesWithin] and the
[statistical steps][Implication.substitutesWithin_of_mixed] along a witness add up.

**On interfaces.** [`DistinguisherAdvantage`][DistinguisherAdvantage] is a structure, and for every class of admitted
distinguishers [`Interface.distinguisherAdvantage`][Interface.distinguisherAdvantage] is one: its
field `admissible` is that class, its field `advantage` is the systems-level
[advantage][Domain.Distinguisher.advantage], and its laws `advantage_self`, `advantage_symm` and
`advantage_triangle` are the systems-level [zero][advantage_self], [symmetry][advantage_symm] and
[triangle][advantage_triangle] laws.

The [reduction][Interface.reduction] through $\alpha$ is [absorption][Domain.Distinguisher.absorb],
$P \circ \alpha$. Hence an advantage between attachments
[is the advantage of the reduction][Interface.distinguisherAdvantage_attach],
$\mathrm{Adv}_P(\alpha R, \alpha S) = \mathrm{Adv}_{P \circ \alpha}(R, S)$, by
[absorption][probability_absorb]; every advantage
[is at most the distance][Interface.distinguisherAdvantage_le_distance], $\mathrm{Adv}_P \le \Delta$,
by the [systems-level bound][advantage_le_transcriptDistance]; and substitutions
[transport through converters][Interface.substitutesWithin_attach] when the class is closed under
reduction. The class [`Interface.AdmissibleDistinguishers`][Interface.AdmissibleDistinguishers]
bundles the admitted distinguishers with that closure; for its instance in scope,
$R \simeq_\varepsilon S$ is written [`R ≃[ε] S`][notation-substitutes] (scoped in
`SystemAlgebra`), substitutions
[transport through every converter][AdmissibleDistinguishers.substitutesWithin_attach], and every
security notion of Commons is stated this way.

### 5.3 Substitution relaxations and constructions

The [**substitution image**][substitutionImage] collects the transformed endpoints of a one-use
substitution [9, §4.1.4] and gives a [relaxation][singleSubstitutionRelaxation]. The
[**substitution relaxation**][substitutionRelaxation] of a specification is the resources
substituting for a member; it is [compatible with converters][substitutionRelaxation_compatible]
and [idempotent][substitutionRelaxation_idem]. Constructions with simulators
compose [9, Definition 2.4.3 and Theorem 2.4.4]: a witness
[gives serial simulators][Implication.exists_serial_simulators], and
[derivable constructions compose serially][Constructs.derivable_serial_simulators].

---

## 6. Writing systems: the DSL

*`interface`, `system`, `converter` and `filter` declarations compile to the objects of §2 at every
budget ([DSL][DSL], [GRAMMAR][Grammar]).* A component compiles to a deterministic
[program][Program] and **sources**: every sampling `x ←$ P` [becomes a call][desugarSampling] to
a [source][Interface.Resource.source] of fresh samples of the closed law $P$, and initialization
runs in the first invocation.

An [`interface I`][elabInterface] declaration generates `I q := Interface.queryBudget … q`, the
[query budget][Interface.queryBudget], and `I.perPort q := Interface.portBudget … q`, the
[per-port budget][Interface.portBudget]. A [`system S : I`][elabComponent] generates
`S : Interface.Resource (I q)`, [compiled][elabProgramDecls] to `S.program • S.randomness k`: the
[converter of its program][Interface.Converter.ofProgram] attached to its [sources][sourcesAt]. A
system that samples nothing is the [automaton][Interface.Resource.ofAutomaton] of its program, and
a system without an exact domain [also gets][elabPerPortDecls]
`S.perPort : Interface.Resource (I.perPort q)`.

A [`converter C : I`][elabComponent] with `inside J` generates `C : I q ⟶ J (C.bound * q)`,
compiled to `C.program ≫ Interface.rightContext J (C.randomness k)`: its program with its sources
[beside][Interface.rightContext] the inside interface, or `C.program` when it samples nothing. With
a single inside interface it [also has a per-port typing][elabPerPortDecls] along a partial port
map `C.portMap : I.Port → Option J.Port`, through the
[converter of a port-preserving program][Interface.Converter.ofPreservingProgram], with
`C.preserving` a proof of [`Program.PortPreserving`][Program.PortPreserving]. When `J` is `I` and
each procedure calls its own port, at most once, it is
`C.perPort : I.perPort q ⟶ I.perPort q`. When `J` is another interface, each of whose labels one
procedure calls at most once, it is `C.perPort : I.perPort q ⟶ J.perPort (C.insideBudget q)`: an
inside label has the budget of the procedure calling it, and a procedure calling nothing maps to
`none` and needs no inside budget, as in the [write-through cache][WriteThrough] and in
$\rho^{ctxt}$ and $\rho^{ae}$ of §8. When the converter samples nothing and its number of inside
calls is a function of the input, the elaborator [also generates][elabExactDecls]
`C.exact : (I n).restrict (fun h => (h.map C.cost).sum ≤ q) ⟶ J q`, the
[converter of the costed program][Interface.Converter.ofCostedProgram].

A [`filter F : I domain h ↦ P`][elabFilter] generates `F : (I q).restrict P ⟶ I q`, the
[filter][Interface.filter] admitting `P`.

A compiled component is an automaton with a sampled initial state. Attaching a program to an
automaton [gives the combined automaton][Interface.Converter.ofProgram_smul_ofAutomaton], also
[for port-preserving programs][Interface.Converter.ofPreservingProgram_smul_ofAutomaton], so
compiled systems are compared by [bisimulation][automatonSystem_eq_of_bisim].

---

## 7. Proof commands

[`cc_normalize`][cc_normalize] rewrites attachments to normal forms,
[`cc_nonexpand`][cc_nonexpand] applies the compatibility laws, on interfaces also
[with the concrete parallel composition][cc_nonexpand-interfaces], [`cc_triangle`][cc_triangle]
takes a hybrid step, and [`cc_construct`][cc_construct] reduces a construction to its equality or
distance obligation. [`cc_calc relation`][cc_calc] proves $X \simeq Y$ from `=` and `≃` steps,
and [`cc_calc counted systems`][cc_calc-counted] builds an implication witness, whose uses
[`cc_usage`][cc_usage] counts. [`cc_calc statistical`][cc_calc-statistical] proves
$d(X, Y) \le \sum_j \varepsilon_j$ from `≈[ε]` steps, and
[`cc_calc mixed model using domination`][cc_calc-mixed] proves
$X \simeq_{\sum_j \varepsilon_j} Y$ from `≃[loss]` and `≈[ε]` steps.

---

## 8. Examples

- **Authenticated encryption** ([9, Theorem 2.3.10(4)], corrected; [Security][AESec]). Let $R$ be
  the real system [`AE.Real`][AE.Real], $E$ the encryption oracle
  [`Encryption.Real`][Encryption.Real], and $I = \rho^{ae} E$ the ideal system
  (`AE.Ideal • Encryption.Real`): [`AE.Ideal`][AE.Ideal], like [`AE.CTXT`][AE.CTXT]
  ($\rho^{ctxt}$), is a converter from [`AE M C`][AE] to [`Encryption M C`][Encryption]. Let $P$ and $C$ be the
  [plaintext filter][AE.PTXT] `AE.PTXT` and the [random-message transformation][AE.CCA] `AE.CCA`,
  and $q = (q_e, q_d)$ the budgets per port. The corrected chain uses each assumption twice:

  $$
  R \;\simeq_{\mathrm{ptxt}}\; P R \;\simeq_{\mathrm{cca}}\; P C R \;\simeq_{\mathrm{ptxt}}\; P C P R \;\simeq_{\mathrm{cca}}\; P C P C R \;\approx_{q_e^2 / \lvert \mathcal M \rvert}\; I .
  $$

  The last step is the [collision bound][hybrid_ideal_distance_le], which compares the hybrid
  with `AE.Ideal.perPort • Encryption.Real.perPort` ([Collision][AECol]). The results are the
  [counted witness][correctedChain], with [two uses of ind-cca][correctedChain_cca] and
  [two of int-ptxt][correctedChain_ptxt], the [advantage form][ae_of_ind_cca_int_ptxt], and the
  [distance form][real_ideal_distance_le]
  $\Delta(R, I) \le 2\,\Delta(R, P R) + 2\,\Delta(R, C R) + q_e^2 / \lvert \mathcal M \rvert$.
  The systems and the notions [`AE.INDCCA`][AE.INDCCA], [`AE.INTPTXT`][AE.INTPTXT],
  [`AE.INTCTXT`][AE.INTCTXT] and [`AE.Secure`][AE.Secure] are Commons definitions
  ([AEAD][AEDefs]); int-ctxt and ae read $R \simeq \rho^{ctxt} E$ and $R \simeq \rho^{ae} E$.
  The systems are compared as [oracle automata][oracleStep] ([Oracle][AEOracle],
  [Hybrid][AEHybrid]), each by a bisimulation of its compiled automaton: the
  [real system][real_bisim], the [encryption oracle][encryptionReal_bisim], and the images under
  the [plaintext filter][ptxt_bisim], the [random-message transformation][cca_bisim] and the
  [ideal transformation][aeIdeal_bisim].
- **Substitutions on interfaces** ([Substitution][ExSub]): single substitutions with a context
  [on the right][construction_with_right_context] or [on the left][construction_with_left_context],
  and [two statistical substitutions][constructsWithin_of_two_substitutions] giving
  $\lbrace R \rbrace \xrightarrow{\pi,\ \varepsilon_1 + \varepsilon_2} \lbrace \sigma S \rbrace$.
- **DSL components** ([Components][ExComp]): counters, fresh and persistent randomness, a
  [padding converter][Padding] with an inferred cost, the [write-through cache][WriteThrough]
  typed by a partial port map, and a [filter][FirstRequests].
- **AES and AEAD in the DSL** ([AES][ExAES], [AEAD][ExAEAD]): [AES-256][AES-system] as a system
  with a random key, from the Commons [block cipher][BlockCipher] [AES][AES-blockCipher], with
  converters around it such as [CBC-MAC][CBC]; and [AES-CTR followed by PMAC][EncryptThenMAC],
  from the Commons [CTR][CTR] and [PMAC][PMAC] converters. The proof commands on interfaces are
  exercised in [Usability][ExUse].

---

## Where the formalization departs from its sources

1. **Everything is finite.** Interfaces carry finite labels and alphabets and a domain of bounded length, so resources are finite random systems with [finite presentations][RandomSystem.exists_presentation]. The sources allow infinite alphabets and unbounded interactions.
2. **Randomness enters DSL systems only through sources.** A sampled law must be closed: it may depend on declaration parameters, not on runtime values. A probabilistic encryption is therefore a [sampled table of ciphertexts][SymmetricEncryption.encryptions] ([Encryption][SymEnc]).
3. **[9, Theorem 2.3.10(4)] needs a second [`ind-cca`][AE.INDCCA] step.** The printed chain `int-ptxt`, `ind-cca`, `int-ptxt`, followed by a collision bound, fails when a later message equals an earlier replacement message. The [corrected chain][correctedChain] and an [all-pairs collision bound][collision_mass_le] are in [Security][AESec] and [Collision][AECol].
4. **[2, Theorem 2.29] holds with a [maximum over pairs][exists_pair_one_sub_supAgreement_le], not a minimum.** The minimum form [is refuted][not_supAgreement_disagreement_le_every_pair].

---

## Appendix A. Probability

*Finitely supported laws [1, Definitions 1–4]:*

$$
\mathrm{Distribution}(A) = A \to_0 \mathbb R, \qquad
\delta(X, Y) = \sum_a \max\big(X(a) - Y(a),\ 0\big) .
$$

A [**distribution**][Distribution] is a finitely supported function to $\mathbb R$, and a
[**probability distribution**][ProbDist] one that is [nonnegative with weight one][isProbDist].
Distributions have [masses][mass] of events, [pushforwards][fTransform], [products][prod] of two
laws and of [families][pi], and [uniform][uniform] laws. The [**statistical distance**][statDist]
satisfies the [triangle inequality][statDist_triangle] and [data processing][statDist_fTransform_le],
$\delta(fX, fY) \le \delta(X, Y)$; with [positive parts][statDist_eq_weight_posPart] it is
$\delta(X, Y) = \lvert (X - Y)^{+} \rvert$, and with [overlaps][statDist_eq_weight_sub_weight_inf]
$\delta(X, Y) = \lvert X \rvert - \lvert X \wedge Y \rvert$.

For a [coupling][IsCoupling] of $X$ and $Y$,
[the distance is at most the off-diagonal mass][statDist_le_offDiagonalMass],
$\delta(X, Y) \le \Pr[X \ne Y]$, and [some coupling attains it][exists_coupling_offDiagonalMass_eq].
For the $n$-ary maximal coupling [2, Theorem 2.29], the [largest agreement][supAgreement] of $n$
laws of one weight [is the weight of their overlap][supAgreement_eq_weight_overlapDist].
[**Expectation**][expect] is linear [in the distribution][expect_add_left] and
[in the function][expect_add_right], with [Markov's][mass_ge_le_expect_div],
the [Cauchy–Schwarz][expect_mul_sq_le_sq_mul_sq] and [Jensen's][ConvexOn.map_expect_le]
inequalities. Collision bounds [count][card_function_fiber_finset] the functions $X \to Y$
agreeing with a map on a finite set $S$: there are $\lvert Y \rvert^{\lvert X \rvert - \lvert S \rvert}$.

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
[AEDefs]: src/Commons/Definitions/AEAD.lean
[AEOracle]: src/Examples/AuthenticatedEncryption/Oracle.lean
[AEHybrid]: src/Examples/AuthenticatedEncryption/Hybrid.lean
[AECol]: src/Examples/AuthenticatedEncryption/Collision.lean
[AESec]: src/Examples/AuthenticatedEncryption/Security.lean
[ExSub]: src/Examples/Substitution.lean
[ExComp]: src/Examples/DSL/Components.lean
[ExAES]: src/Examples/DSL/AES.lean
[ExAEAD]: src/Examples/DSL/AEAD.lean
[ExUse]: src/Examples/Usability.lean

<!-- Declarations: §1 -->

[System]: src/RandomSystems/System/Basic.lean#L40
[SilentAtEmpty]: src/RandomSystems/System/Basic.lean#L69
[PrefixClosed]: src/RandomSystems/System/Basic.lean#L72
[IsDDS]: src/RandomSystems/System/Basic.lean#L77
[interconnect]: src/RandomSystems/System/Basic.lean#L225
[restrict]: src/RandomSystems/System/Basic.lean#L794
[Replies]: src/RandomSystems/System/Replies.lean#L33
[IsDDS.eq_of_replies_iff]: src/RandomSystems/System/Replies.lean#L151
[automatonSystem]: src/RandomSystems/System/Automaton.lean#L43
[IsBisim]: src/RandomSystems/System/Automaton.lean#L70
[automatonSystem_eq_of_bisim]: src/RandomSystems/System/Automaton.lean#L89
[DDE]: src/RandomSystems/System/DDE.lean#L20
[QueryBounded]: src/RandomSystems/System/DDE.lean#L24
[Domain]: src/RandomSystems/PDS/PDS.lean#L65
[Equivalent]: src/RandomSystems/PDS/PDS.lean#L50
[HasDomain]: src/RandomSystems/PDS/PDS.lean#L91
[PDS]: src/RandomSystems/PDS/PDS.lean#L133
[IsRandomSystem]: src/RandomSystems/Cumulative/Cumulative.lean#L39
[RandomSystem]: src/RandomSystems/Cumulative/Cumulative.lean#L53
[RandomSystem.RepliesAtQueriedInterface]: src/RandomSystems/Cumulative/Cumulative.lean#L70
[PDS.behavior]: src/RandomSystems/Cumulative/Cumulative.lean#L216
[PDS.behavior_eq_iff]: src/RandomSystems/Cumulative/Cumulative.lean#L225
[RandomSystem.exists_presentation]: src/RandomSystems/Cumulative/Presentation.lean#L302
[RandomSystem.ofPDSClass_bijective]: src/RandomSystems/Cumulative/Presentation.lean#L312
[RandomSystem.sLaw]: src/RandomSystems/Cumulative/CumulativeObservation.lean#L179
[RandomSystem.Compatible]: src/RandomSystems/Cumulative/CumulativeObservation.lean#L197
[RandomSystem.eq_iff_sLaw]: src/RandomSystems/Cumulative/CumulativeObservation.lean#L503
[RandomSystem.eq_iff_sLaw_fixedQueries]: src/RandomSystems/Cumulative/CumulativeObservation.lean#L517
[RandomSystem.mix]: src/RandomSystems/Cumulative/CumulativeOperations.lean#L45
[RandomSystem.parallel]: src/RandomSystems/Cumulative/CumulativeOperations.lean#L130
[IsDDC]: src/RandomSystems/DDC/DDC.lean#L127
[serialM]: src/RandomSystems/DDC/Serial.lean#L55
[IsDDC.comp]: src/RandomSystems/DDC/Serial.lean#L514
[converterDomain]: src/RandomSystems/Converter/ConverterDomain.lean#L234
[IsDDCFrom]: src/RandomSystems/Converter/ConverterDomain.lean#L301
[IsDDCFrom.mapsDomain]: src/RandomSystems/Converter/ConverterDomain.lean#L609
[PDCBehavior]: src/RandomSystems/Converter/PDCBehavior.lean#L67
[PDCBehavior.ofPDC]: src/RandomSystems/Converter/PDCBehavior.lean#L169
[PDCBehavior.comp]: src/RandomSystems/Converter/PDCBehavior.lean#L273
[PDCBehavior.id]: src/RandomSystems/Converter/PDCBehavior.lean#L369
[PDCBehavior.comp_assoc]: src/RandomSystems/Converter/PDCBehavior.lean#L338
[PDCBehavior.id_comp]: src/RandomSystems/Converter/PDCBehavior.lean#L385
[PDCBehavior.comp_id]: src/RandomSystems/Converter/PDCBehavior.lean#L375
[PDCBehavior.attach]: src/RandomSystems/Converter/ConverterAttachment.lean#L156
[PDCBehavior.attach_presents]: src/RandomSystems/Converter/ConverterAttachment.lean#L178
[PDCBehavior.attach_id]: src/RandomSystems/Converter/ConverterAttachment.lean#L233
[PDCBehavior.attach_comp]: src/RandomSystems/Converter/ConverterAttachment.lean#L246
[PDCBehavior.tensor]: src/RandomSystems/Converter/ConverterTensor.lean#L649
[PDCBehavior.comp_tensor]: src/RandomSystems/Converter/ConverterTensor.lean#L745
[PDCBehavior.tensor_id]: src/RandomSystems/Converter/ConverterTensor.lean#L705
[Program]: src/RandomSystems/Converter/Program.lean#L45
[Program.Bounded]: src/RandomSystems/Converter/Program.lean#L70
[Program.Costs]: src/RandomSystems/Converter/Program.lean#L88
[Program.PortPreserving]: src/RandomSystems/Converter/Program.lean#L99
[DDC.insideQueries_restrict_length_le]: src/RandomSystems/Converter/Program.lean#L513
[DDC.ofProgramOn_isDDCFrom]: src/RandomSystems/Converter/Program.lean#L610
[Program.inline]: src/RandomSystems/Converter/ProgramAttachment.lean#L258
[Program.combine]: src/RandomSystems/Converter/ProgramAttachment.lean#L429
[Program.trim_apply_ofProgramOn_automaton]: src/RandomSystems/Converter/ProgramAttachment.lean#L609
[RandomSystem.transcriptDistance]: src/RandomSystems/Distance/Decision.lean#L225
[Domain.Compatible]: src/RandomSystems/Distance/Decision.lean#L162
[Domain.DecisionCompatible]: src/RandomSystems/Distance/Decision.lean#L168
[IsDDD]: src/RandomSystems/System/InterfaceSystem.lean#L968
[RandomSystem.decisionProbability]: src/RandomSystems/Distance/Decision.lean#L247
[Domain.Distinguisher]: src/RandomSystems/Distance/Distinguisher.lean#L110
[Domain.Distinguisher.probability]: src/RandomSystems/Distance/Distinguisher.lean#L114
[Domain.Distinguisher.advantage]: src/RandomSystems/Distance/Distinguisher.lean#L120
[advantage_self]: src/RandomSystems/Distance/Distinguisher.lean#L129
[advantage_symm]: src/RandomSystems/Distance/Distinguisher.lean#L131
[advantage_triangle]: src/RandomSystems/Distance/Distinguisher.lean#L134
[RandomSystem.transcriptDistance_eq_iSup]: src/RandomSystems/Distance/Distinguisher.lean#L142
[advantage_le_transcriptDistance]: src/RandomSystems/Distance/Distinguisher.lean#L171
[Domain.Distinguisher.absorb]: src/RandomSystems/Distance/Distinguisher.lean#L214
[probability_absorb]: src/RandomSystems/Distance/Distinguisher.lean#L223
[Domain.Distinguisher.exists_absorbAll]: src/RandomSystems/Distance/Distinguisher.lean#L189
[Domain.Distinguisher.exists_absorbRight]: src/RandomSystems/Distance/Distinguisher.lean#L245
[absorbAll]: src/RandomSystems/Distance/Absorption.lean#L42
[RandomSystem.restrict]: src/RandomSystems/Distance/Restriction.lean#L59
[RandomSystem.restrict_restrict]: src/RandomSystems/Distance/Restriction.lean#L67
[RandomSystem.sLaw_restrict]: src/RandomSystems/Distance/Restriction.lean#L98
[RandomSystem.transcriptDistance_restrict_le]: src/RandomSystems/Distance/Restriction.lean#L129
[MC]: src/RandomSystems/Game/Game.lean#L41
[DDG]: src/RandomSystems/Game/Game.lean#L45
[DDG.Wins]: src/RandomSystems/Game/Game.lean#L57
[PDG]: src/RandomSystems/Game/Game.lean#L49
[PDG.supWinProbability]: src/RandomSystems/Game/Game.lean#L105
[PDG.blind]: src/RandomSystems/Game/Game.lean#L123
[PDG.badProbability_le_blind]: src/RandomSystems/Game/Game.lean#L189
[PDG.supWinProbability_blind_le]: src/RandomSystems/Game/Game.lean#L201
[GameEquivalent]: src/RandomSystems/Game/GameEquivalence.lean#L55
[GameEquivalent.statDist_le_blind]: src/RandomSystems/Game/GameEquivalence.lean#L88
[PDG.ofFunction]: src/RandomSystems/Game/FunctionGame.lean#L33
[PDG.ofFunction_gameEquivalent]: src/RandomSystems/Game/FunctionGame.lean#L66

<!-- Declarations: §2 -->

[Interface]: src/ConstructiveCryptography/Interface.lean#L43
[Interface.queryBudget]: src/ConstructiveCryptography/Interface.lean#L66
[Interface.portBudget]: src/ConstructiveCryptography/Interface.lean#L77
[Interface.Resource]: src/ConstructiveCryptography/Interface.lean#L93
[Interface.Converter]: src/ConstructiveCryptography/Interface.lean#L128
[Interface.category]: src/ConstructiveCryptography/Interface.lean#L132
[Interface.ofDDC]: src/ConstructiveCryptography/Interface.lean#L141
[Interface.attach]: src/ConstructiveCryptography/Interface.lean#L154
[Interface.identity_attach]: src/ConstructiveCryptography/Interface.lean#L168
[Interface.comp_smul]: src/ConstructiveCryptography/Interface.lean#L173
[Interface.tensor]: src/ConstructiveCryptography/InterfaceParallel.lean#L85
[Interface.parallel]: src/ConstructiveCryptography/InterfaceParallel.lean#L147
[Interface.parallelConverter]: src/ConstructiveCryptography/InterfaceParallel.lean#L202
[Interface.restrict]: src/ConstructiveCryptography/InterfaceFilter.lean#L30
[Interface.filter]: src/ConstructiveCryptography/InterfaceFilter.lean#L43
[Interface.filter_smul]: src/ConstructiveCryptography/InterfaceFilter.lean#L54
[Interface.filter_comp_filter_smul]: src/ConstructiveCryptography/InterfaceFilter.lean#L88
[Interface.constant]: src/ConstructiveCryptography/Context.lean#L78
[Interface.rightContext]: src/ConstructiveCryptography/Context.lean#L102
[Interface.leftContext]: src/ConstructiveCryptography/Context.lean#L107
[Interface.attach_rightContext]: src/ConstructiveCryptography/Context.lean#L111
[Interface.attach_leftContext]: src/ConstructiveCryptography/Context.lean#L116
[Interface.Resource.source]: src/ConstructiveCryptography/Source.lean#L49
[Interface.Resource.ofAutomaton]: src/ConstructiveCryptography/Automaton.lean#L42
[Interface.parallel_ofAutomaton]: src/ConstructiveCryptography/Automaton.lean#L57
[Interface.Resource.ofFunction]: src/ConstructiveCryptography/Functional.lean#L56
[Interface.Resource.ofConditional]: src/ConstructiveCryptography/Functional.lean#L38
[Interface.Resource.sample]: src/ConstructiveCryptography/Functional.lean#L176
[GameEquivalent.game_dist_le]: src/ConstructiveCryptography/GameBound.lean#L89
[PDG.ofSingleFunction_gameEquivalent]: src/ConstructiveCryptography/GameBound.lean#L40
[Interface.swap]: src/ConstructiveCryptography/ResourceCoherence.lean#L177
[Interface.parallel_swap]: src/ConstructiveCryptography/ResourceCoherence.lean#L211
[notation-distance]: src/ConstructiveCryptography/Notation.lean#L22
[notation-parallel]: src/ConstructiveCryptography/Notation.lean#L26
[notation-constructs]: src/ConstructiveCryptography/Notation.lean#L29
[notation-constructsWithin]: src/ConstructiveCryptography/Notation.lean#L33
[notation-substitutes]: src/ConstructiveCryptography/Notation.lean#L39

<!-- Declarations: §3 -->

[Interface.monoidalStruct]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L20
[Interface.monoidal]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L107
[Interface.id_tensor_id]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L33
[Interface.tensor_comp]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L36
[Interface.associator_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L41
[Interface.leftUnitor_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L46
[Interface.rightUnitor_naturality]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L50
[Interface.pentagon]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L54
[Interface.triangle]: src/ConstructiveCryptography/InterfaceMonoidal.lean#L78
[Interface.unit]: src/ConstructiveCryptography/InterfaceCoherence.lean#L91
[Interface.associator]: src/ConstructiveCryptography/InterfaceCoherence.lean#L176
[Interface.leftUnitor]: src/ConstructiveCryptography/InterfaceCoherence.lean#L181
[Interface.rightUnitor]: src/ConstructiveCryptography/InterfaceCoherence.lean#L185
[Interface.comp_associator]: src/ConstructiveCryptography/ConverterCoherence.lean#L71
[Interface.comp_leftUnitor]: src/ConstructiveCryptography/ConverterCoherence.lean#L178
[Interface.comp_rightUnitor]: src/ConstructiveCryptography/ConverterCoherence.lean#L204
[ResourceTheory]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L50
[ResourceTheory.functor]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L69
[CryptographicAlgebra]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L97
[CA.parallel]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L126
[CA.dummy]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L134
[CA.attach_parallel]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L160
[CA.parallel_assoc]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L182
[CA.parallel_dummy_left]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L196
[CA.parallel_dummy_right]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L211
[Interface.resourceTheory]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L63
[Interface.resourcesLaxMonoidal]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L69
[Interface.cryptographicAlgebra]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L94
[Interface.distinguishers]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L100
[Interface.distinguishers_attach]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L104
[Interface.distinguishers_parallel_left]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L112
[Interface.distinguishers_parallel_right]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L126
[Interface.compatibleDistinguisherClass]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L134
[Interface.cc_parallel_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L141
[Interface.cc_dummy_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L145
[Interface.cc_distance_eq]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L149
[Interface.dummy]: src/ConstructiveCryptography/ResourceCoherence.lean#L102
[Interface.parallel_assoc]: src/ConstructiveCryptography/ResourceCoherence.lean#L91
[Interface.parallel_dummy_left]: src/ConstructiveCryptography/ResourceCoherence.lean#L158
[Interface.parallel_dummy_right]: src/ConstructiveCryptography/ResourceCoherence.lean#L167
[Interface.parallel_attach]: src/ConstructiveCryptography/ResourceParallelAttachment.lean#L18
[CompatiblePseudoMetric]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L43
[CA.distance]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L63
[distance_attach_le]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L90
[distance_parallel_le]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L145
[advantageDistance]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L36
[CompatibleDistinguisherClass]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L77
[CompatibleDistinguisherClass.ofClosure]: src/ConstructiveCryptography/CryptographicAlgebra/Distinguisher.lean#L102

<!-- Declarations: §4 -->

[Specification]: src/ConstructiveCryptography/Specification/Defs.lean#L18
[Specification.Constructs]: src/ConstructiveCryptography/Specification/Basic.lean#L31
[Specification.ConstructsWithin]: src/ConstructiveCryptography/Specification/Metric.lean#L23
[CA.Specification.Constructs]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L368
[CA.Specification.ConstructsWithin]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L179
[Constructs.serial]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L443
[ConstructsWithin.serial]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L234
[Constructs.parallel]: src/ConstructiveCryptography/CryptographicAlgebra/Basic.lean#L518
[ConstructsWithin.parallel]: src/ConstructiveCryptography/CryptographicAlgebra/PseudoMetric.lean#L254
[Relaxation]: src/ConstructiveCryptography/Specification/Relaxation/Defs.lean#L22
[Relaxation.Compatible]: src/ConstructiveCryptography/CryptographicAlgebra/Relaxation.lean#L46
[Relaxation.compatible_iff]: src/ConstructiveCryptography/CryptographicAlgebra/Relaxation.lean#L84
[Constructs.relax_serial]: src/ConstructiveCryptography/CryptographicAlgebra/Relaxation.lean#L136
[epsilonRelaxation]: src/ConstructiveCryptography/CryptographicAlgebra/Epsilon.lean#L43
[constructs_epsilonRelaxation_iff]: src/ConstructiveCryptography/CryptographicAlgebra/Epsilon.lean#L165
[Constructs.serial_epsilonRelaxation]: src/ConstructiveCryptography/CryptographicAlgebra/Epsilon.lean#L225
[CA.star]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L59
[star_idem]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L94
[starClosure]: src/ConstructiveCryptography/Specification/Star.lean#L55
[Constructs.star]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L145
[constructs_of_simulator]: src/ConstructiveCryptography/CryptographicAlgebra/Star.lean#L269
[kernel]: src/ConstructiveCryptography/Specification/Relaxation/Kernel.lean#L16
[gameSpec]: src/ConstructiveCryptography/Specification/Game/Basic.lean#L24
[Constructible]: src/ConstructiveCryptography/Construction/Defs.lean#L24

<!-- Declarations: §5 -->

[SubstitutionRelation]: src/ConstructiveCryptography/Substitution/Basic.lean#L45
[Implication]: src/ConstructiveCryptography/Substitution/Basic.lean#L176
[Implication.usageCount]: src/ConstructiveCryptography/Substitution/Basic.lean#L207
[substitutes_of_hybrid]: src/ConstructiveCryptography/Substitution/Basic.lean#L77
[distance_hybrid_le]: src/ConstructiveCryptography/Substitution/Basic.lean#L120
[Implication.substitutes]: src/ConstructiveCryptography/Substitution/Basic.lean#L214
[Implication.distance_le]: src/ConstructiveCryptography/Substitution/Basic.lean#L254
[Implication.map]: src/ConstructiveCryptography/Substitution/Implication.lean#L127
[Implication.reverse]: src/ConstructiveCryptography/Substitution/Implication.lean#L158
[Implication.append]: src/ConstructiveCryptography/Substitution/Implication.lean#L207
[usageCount_append]: src/ConstructiveCryptography/Substitution/Implication.lean#L275
[generatedRelation]: src/ConstructiveCryptography/Substitution/Implication.lean#L309
[derivable_substitutes]: src/ConstructiveCryptography/Substitution/Implication.lean#L335
[DistinguisherAdvantage]: src/ConstructiveCryptography/Substitution/Reduction.lean#L46
[SubstitutesWithin]: src/ConstructiveCryptography/Substitution/Reduction.lean#L72
[SubstitutesWithin.symm]: src/ConstructiveCryptography/Substitution/Reduction.lean#L80
[SubstitutesWithin.trans]: src/ConstructiveCryptography/Substitution/Reduction.lean#L94
[SubstitutesWithin.of_distance]: src/ConstructiveCryptography/Substitution/Reduction.lean#L127
[SubstitutesWithin.of_statistical]: src/ConstructiveCryptography/Substitution/Reduction.lean#L110
[SubstitutesWithin.attach]: src/ConstructiveCryptography/Substitution/Reduction.lean#L145
[SubstitutesWithin.attach_serial]: src/ConstructiveCryptography/Substitution/Reduction.lean#L175
[Implication.substitutesWithin]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L49
[Implication.substitutesWithin_of_mixed]: src/ConstructiveCryptography/Substitution/Quantitative.lean#L105
[Interface.distinguisherAdvantage]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L161
[Interface.reduction]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L172
[Interface.distinguisherAdvantage_attach]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L177
[Interface.distinguisherAdvantage_le_distance]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L222
[Interface.substitutesWithin_attach]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L190
[Interface.AdmissibleDistinguishers]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L204
[AdmissibleDistinguishers.substitutesWithin_attach]: src/ConstructiveCryptography/InterfaceAlgebra.lean#L213
[substitutionImage]: src/ConstructiveCryptography/Substitution/Relaxation.lean#L45
[singleSubstitutionRelaxation]: src/ConstructiveCryptography/Substitution/Relaxation.lean#L59
[substitutionRelaxation]: src/ConstructiveCryptography/Substitution/Relaxation.lean#L164
[substitutionRelaxation_compatible]: src/ConstructiveCryptography/Substitution/Relaxation.lean#L182
[substitutionRelaxation_idem]: src/ConstructiveCryptography/Substitution/Relaxation.lean#L202
[Implication.exists_serial_simulators]: src/ConstructiveCryptography/Substitution/Construction.lean#L44
[Constructs.derivable_serial_simulators]: src/ConstructiveCryptography/Substitution/Construction.lean#L107

<!-- Declarations: §6–7 -->

[desugarSampling]: src/ConstructiveCryptography/DSL/Elaborator.lean#L191
[elabInterface]: src/ConstructiveCryptography/DSL/Elaborator.lean#L348
[elabComponent]: src/ConstructiveCryptography/DSL/Elaborator.lean#L808
[elabProgramDecls]: src/ConstructiveCryptography/DSL/Elaborator.lean#L641
[elabPerPortDecls]: src/ConstructiveCryptography/DSL/Elaborator.lean#L538
[elabExactDecls]: src/ConstructiveCryptography/DSL/Elaborator.lean#L713
[elabFilter]: src/ConstructiveCryptography/DSL/Elaborator.lean#L924
[sourcesAt]: src/ConstructiveCryptography/DSL/Elaborator.lean#L632
[Interface.Converter.ofProgram]: src/ConstructiveCryptography/DSL/Converters.lean#L38
[Interface.Converter.ofCostedProgram]: src/ConstructiveCryptography/DSL/Converters.lean#L50
[Interface.Converter.ofPreservingProgram]: src/ConstructiveCryptography/DSL/Converters.lean#L67
[Interface.Converter.ofProgram_smul_ofAutomaton]: src/ConstructiveCryptography/DSL/Converters.lean#L142
[Interface.Converter.ofPreservingProgram_smul_ofAutomaton]: src/ConstructiveCryptography/DSL/Converters.lean#L152
[cc_normalize]: src/ConstructiveCryptography/Tactics/Basic.lean#L30
[cc_nonexpand]: src/ConstructiveCryptography/Tactics/Categorical.lean#L166
[cc_nonexpand-interfaces]: src/ConstructiveCryptography/Notation.lean#L98
[cc_triangle]: src/ConstructiveCryptography/Tactics/Categorical.lean#L155
[cc_construct]: src/ConstructiveCryptography/Tactics/Categorical.lean#L42
[cc_calc]: src/ConstructiveCryptography/Tactics/Substitution.lean#L88
[cc_calc-counted]: src/ConstructiveCryptography/Tactics/Substitution.lean#L147
[cc_usage]: src/ConstructiveCryptography/Tactics/Substitution.lean#L243
[cc_calc-statistical]: src/ConstructiveCryptography/Tactics/Substitution.lean#L292
[cc_calc-mixed]: src/ConstructiveCryptography/Tactics/Substitution.lean#L295

<!-- Declarations: §8, departures, Appendix A -->

[AE.Real]: src/Commons/Definitions/AEAD.lean#L54
[AE]: src/Commons/Definitions/AEAD.lean#L37
[Encryption]: src/Commons/Definitions/Encryption.lean#L54
[AE.CCA]: src/Commons/Definitions/AEAD.lean#L65
[AE.PTXT]: src/Commons/Definitions/AEAD.lean#L84
[AE.CTXT]: src/Commons/Definitions/AEAD.lean#L98
[AE.Ideal]: src/Commons/Definitions/AEAD.lean#L111
[AE.INDCCA]: src/Commons/Definitions/AEAD.lean#L153
[AE.INTPTXT]: src/Commons/Definitions/AEAD.lean#L161
[AE.INTCTXT]: src/Commons/Definitions/AEAD.lean#L168
[AE.Secure]: src/Commons/Definitions/AEAD.lean#L175
[Encryption.Real]: src/Commons/Definitions/Encryption.lean#L71
[SymmetricEncryption.encryptions]: src/Commons/Definitions/Encryption.lean#L65
[BlockCipher]: src/Commons/Definitions/Cipher.lean#L29
[AES-blockCipher]: src/Commons/Schemes/BlockCipher/AES.lean#L387
[CTR]: src/Commons/Schemes/Stream/CTR.lean#L122
[PMAC]: src/Commons/Schemes/MAC/PMAC.lean#L115
[oracleStep]: src/Examples/AuthenticatedEncryption/Oracle.lean#L39
[real_bisim]: src/Examples/AuthenticatedEncryption/Oracle.lean#L320
[ptxt_bisim]: src/Examples/AuthenticatedEncryption/Oracle.lean#L103
[cca_bisim]: src/Examples/AuthenticatedEncryption/Oracle.lean#L187
[aeIdeal_bisim]: src/Examples/AuthenticatedEncryption/Oracle.lean#L240
[encryptionReal_bisim]: src/Examples/AuthenticatedEncryption/Oracle.lean#L369
[collision_mass_le]: src/Examples/AuthenticatedEncryption/Collision.lean#L50
[hybrid_ideal_distance_le]: src/Examples/AuthenticatedEncryption/Collision.lean#L361
[correctedChain]: src/Examples/AuthenticatedEncryption/Security.lean#L61
[correctedChain_cca]: src/Examples/AuthenticatedEncryption/Security.lean#L84
[correctedChain_ptxt]: src/Examples/AuthenticatedEncryption/Security.lean#L89
[ae_of_ind_cca_int_ptxt]: src/Examples/AuthenticatedEncryption/Security.lean#L97
[real_ideal_distance_le]: src/Examples/AuthenticatedEncryption/Security.lean#L128
[construction_with_right_context]: src/Examples/Substitution.lean#L43
[construction_with_left_context]: src/Examples/Substitution.lean#L70
[constructsWithin_of_two_substitutions]: src/Examples/Substitution.lean#L120
[Padding]: src/Examples/DSL/Components.lean#L86
[WriteThrough]: src/Examples/DSL/Components.lean#L104
[FirstRequests]: src/Examples/DSL/Components.lean#L116
[AES-system]: src/Examples/DSL/AES.lean#L29
[CBC]: src/Examples/DSL/AES.lean#L57
[EncryptThenMAC]: src/Examples/DSL/AEAD.lean#L47
[exists_pair_one_sub_supAgreement_le]: src/Probability/MultiCoupling.lean#L616
[not_supAgreement_disagreement_le_every_pair]: src/Probability/MultiCoupling.lean#L778
[supAgreement]: src/Probability/MultiCoupling.lean#L87
[supAgreement_eq_weight_overlapDist]: src/Probability/MultiCoupling.lean#L397
[Distribution]: src/Probability/Distribution.lean#L54
[ProbDist]: src/Probability/Distribution.lean#L147
[isProbDist]: src/Probability/Distribution.lean#L126
[mass]: src/Probability/Distribution.lean#L215
[fTransform]: src/Probability/Distribution.lean#L547
[prod]: src/Probability/Distribution.lean#L902
[pi]: src/Probability/Distribution.lean#L1543
[uniform]: src/Probability/Distribution.lean#L481
[statDist]: src/Probability/StatisticalDistance.lean#L88
[statDist_triangle]: src/Probability/StatisticalDistance.lean#L243
[statDist_fTransform_le]: src/Probability/StatisticalDistance.lean#L619
[IsCoupling]: src/Probability/Coupling.lean#L46
[statDist_le_offDiagonalMass]: src/Probability/Coupling.lean#L241
[exists_coupling_offDiagonalMass_eq]: src/Probability/Coupling.lean#L320
[expect]: src/Probability/Expectation.lean#L44
[expect_add_left]: src/Probability/Expectation.lean#L66
[expect_add_right]: src/Probability/Expectation.lean#L96
[mass_ge_le_expect_div]: src/Probability/Expectation.lean#L199
[expect_mul_sq_le_sq_mul_sq]: src/Probability/Expectation.lean#L215
[ConvexOn.map_expect_le]: src/Probability/Expectation.lean#L297
[statDist_eq_weight_posPart]: src/Probability/Lift.lean#L89
[statDist_eq_weight_sub_weight_inf]: src/Probability/Lift.lean#L170
[card_function_fiber_finset]: src/Probability/Counting.lean#L47

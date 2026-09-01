# The theory

This document describes the stable mathematical architecture of the library:
the construction calculus before a concrete system model is selected,
fixed-interface Random Systems,
and the optional query-indexed deterministic-converter layer. The
probabilistic-converter category and concrete random-system instantiation of
Constructive Cryptography are deferred. Event algebras, computational
feasibility, and the
deferred MauRen11 theory are outside this architecture.

Maurer--Renner 2016, Section 1 (printed p. 3), records that both names had
been used for the theory, but says that Constructive Cryptography “seems more
natural and captures the goal of the theory better.” This library follows that
recommendation: `ConstructiveCryptography` is the sole public root for
the MR16/Jost/Liu foundation. The name `AbstractCryptography` is reserved for
a future explicit MauRen11 reconciliation and is not a compatibility surface.

## 1. Interface-indexed resource algebra

The public foundation is one interface-indexed resource algebra. Let $\mathbf C$ be a
monoidal category whose objects are interfaces and whose arrows are converters.
The direction

$$
c : A \longrightarrow B
$$

means that $c$ exposes interface $A$ while using a resource at interface $B$.
Resources therefore form a contravariant functor

$$
\Phi : \mathbf C^{\mathrm{op}} \longrightarrow \mathbf{Type},
\qquad
\operatorname{Resource}(A) := \Phi(A^{\mathrm{op}}),
$$

and attachment is exactly its action on arrows:

$$
c \mathbin{\bullet} R
  := \Phi(c^{\mathrm{op}})(R)
  \in \operatorname{Resource}(A)
\qquad
(R \in \operatorname{Resource}(B)).
$$

Maurer--Renner 2016, Section 3.3 (printed p. 7), states: “A converter
$\alpha$, when applied as an interface $i$ of a resource, induces a function
$\Phi \to \Phi : R \mapsto \alpha^i R$.” The category laws express the same
identity and serial-attachment equations at arbitrary interfaces:

$$
1_A \mathbin{\bullet} R = R,
\qquad
(c \mathbin{;} d) \mathbin{\bullet} R
  = c \mathbin{\bullet} (d \mathbin{\bullet} R).
$$

A specification at $A$ is a set

$$
\mathcal R \subseteq \operatorname{Resource}(A).
$$

For $c:A\to B$, attachment maps a source specification at $B$ to its direct
image at $A$. Maurer--Renner 2016, Definition 1 (printed p. 11), states:
“$\mathcal R \xrightarrow{\pi} \mathcal S :\Longleftrightarrow
\pi\mathcal R \subseteq \mathcal S$.” Hence

$$
\operatorname{Constructs}(c,\mathcal R,\mathcal S)
\quad\Longleftrightarrow\quad
\{c\mathbin{\bullet}R \mid R\in\mathcal R\}\subseteq\mathcal S,
$$

where $\mathcal R$ is at $B$ and $\mathcal S$ is at $A$.
Maurer--Renner 2016, Lemma 1 (printed p. 11), states: “This construction
notion is composable.” Functoriality proves identity and serial construction
by direct-image inclusion.

Each resource fibre carries a selected extended pseudo-metric $d_A$.
Attachment is non-expanding when

$$
d_A(c\mathbin{\bullet}R,c\mathbin{\bullet}S)\leq d_B(R,S).
$$

Approximate construction is

$$
\operatorname{ConstructsWithin}(c,\mathcal R,\mathcal S,\varepsilon)
\quad\Longleftrightarrow\quad
\forall R\in\mathcal R,\ \exists S\in\mathcal S,\
d_A(c\mathbin{\bullet}R,S)\leq\varepsilon.
$$

Identity has error zero, bounds may be weakened, and serial composition adds
errors by one triangle inequality and attachment non-expansion.

`ConstructiveCryptography/Categorical.lean` proves these direct-image and metric
lemmas for an arbitrary covariant functor $F:\mathbf D\to\mathbf{Type}$.
`ResourceAlgebra` applies that theorem library with
$\mathbf D=\mathbf C^{\mathrm{op}}$ and $F=\Phi$; it is not a second resource
model. Jost's interface-changing converter attachment requires this heterogeneous shape but
does not require the categorical packaging. Liu--Maurer's fixed-carrier
presentation is recovered by fixing one interface and using its endomorphisms.
Lanzenberger supplies fixed-interface random-system fibres and their distance,
not further axioms for this abstract layer.

The production surface includes Jost's typed attachment, ordered parallel,
and context-insensitivity laws. It excludes Jost's separate
context-restricted construction theory from Section 4.2; that theory is a
distinct extension of this interface-indexed algebra.

### Parallel composition as routed decomposition

Parallel composition is the operation by which the resource algebra exposes a
larger resource as independent addressed components. Maurer--Renner 2016,
Section 3.5 (printed p. 10), observes that “Any computational resource can be
modeled as a (parallel) resource,” but does not impose a parallel algebra on
every carrier.

Jost, Section 2.2.2 (printed pp. 17--18), makes the addresses explicit and
states: “A finite set of resources with disjoint interface sets can be viewed
as a single one.” Parallel takes the union of the component interface sets,
and “the resource consisting of the dummy interface only is called the
(canonical) dummy resource.” Proposition 2.2.3 states attachment locality;
Theorem 2.2.5 obtains parallel construction from that equation. Jost does not
require a swap for this result. Section 4.2.2 (printed p. 51) instead says that
“the parallel composition property is just associativity.” Accordingly,
symmetry is not an axiom of `ResourceAlgebra`.

An interface-indexed presentation exposes the addressing that the fixed
carrier notation hides. Write an interface as

$$
A=(Q_A,R_A), \qquad R_A : Q_A \to \mathbf{Type},
$$

where the answer type is selected by the query. For
$B=(Q_B,R_B)$, ordered parallel is

$$
A \otimes B
  := \left(Q_A \sqcup Q_B,\;
      q \mapsto
      \begin{cases}
        R_A(a) & q=\operatorname{inl}(a),\\
        R_B(b) & q=\operatorname{inr}(b).
      \end{cases}\right),
$$

so the query tag routes both the query and its possible answer to one
component. This is the concrete Random Systems tensor; abstractly the class
only requires the selected ordered tensor $A\otimes B$. Resource parallel has
type

$$
\mu_{A,B}:\operatorname{Resource}(A)\times\operatorname{Resource}(B)
  \longrightarrow\operatorname{Resource}(A\otimes B).
$$

In particular, two resources at the same boundary compose as

$$
R,S\in\operatorname{Resource}(A)
\quad\Longrightarrow\quad
R\parallel S\in\operatorname{Resource}(A\otimes A).
$$

No identification $A\otimes A=A$ is required: the left and right tags are the
addressing mechanism. Associativity and the unit laws hold through the
canonical routing equivalences. The base theory assumes no symmetry law.
Parallel composition of converters is tensor on morphisms, and compatibility
with attachment is the naturality equation

$$
(c\otimes d)\bullet(R\parallel S)
= (c\bullet R)\parallel(d\bullet S).
$$

Together with parallel non-expansion, this supports componentwise replacement
inside complex systems. Iterating the binary operation gives, for example,

$$
d(R_1\parallel\cdots\parallel R_n,
  S_1\parallel\cdots\parallel S_n)
\leq \sum_{i=1}^{n} d(R_i,S_i).
$$

Parallel provides routed juxtaposition; assembling a network additionally
uses the appropriate connection or attachment morphisms. The sum-tag encoding
is a Lean representation of the papers' addressing discipline, not an extra
claim that the papers define interfaces as sum types.

Maurer--Renner 2016, Section 3.4 (printed p. 8), defines
$\mathcal R^* := \mathcal R\Sigma
= \{R\beta \mid R \in \mathcal R,\ \beta \in \Sigma\}$. At one object, Lean
represents $\Sigma$ by a submonoid of endomorphisms and forms this direct-image
closure. A simulator is an explicit witness used to establish membership in
the closure. It is not part of the definition of construction. This material
is owned by `ConstructiveCryptography/Categorical/Star.lean`.

## 2. Fixed-interface Random Systems

The root `RandomSystems` is independent of converters and Constructive
Cryptography. Every object in this layer has fixed query and answer alphabets
$(X,Y)$.

### Deterministic systems and environments

Lanzenberger, Definition 2.9 (printed p. 13), defines a DDS as “a partial
function” with “prefix-closed domain.” Lean represents it as

$$
\operatorname{System.DDS}(X,Y)
  = \{s : X^+ \rightharpoonup Y \mid
       \operatorname{dom}(s)\text{ is prefix-closed}\}.
$$

The value at a history is the entire stateful behavior. No state machine or
execution object belongs to the definition.

Definition 2.9 (printed p. 13) calls a DDS finite when “$X$ is finite and
$\operatorname{dom}(s) \subseteq \bigcup_{i \leq n} X^i$ for some
$n \in \mathbb N$.” Lean does not store those conditions in the generic DDS
carrier; theorems require finiteness only where their statement uses it.

Lanzenberger, Definition 2.11 (printed p. 14), defines a DDE as “a partial
function” “with prefix-closed domain.” Lean uses

$$
\operatorname{System.DDE}(Y,X)
  = \{e : Y^* \rightharpoonup X \mid
       \operatorname{dom}(e)\text{ is prefix-closed}\}.
$$

Definition 2.12 (printed p. 14) calls the transcript “the sequence of pairs.”
`System.trExtend`, `System.trN`, and `System.tr` define that sequence from the
two partial functions. Compatibility means that the environment never queries
outside the DDS domain; stopping means that the transcript reaches a fixed
stage.

### Probabilistic systems and observation

Lanzenberger, Definition 2.14 (printed p. 15), defines a PDS as “a distribution
over $(X,Y)$-DDS” and requires that supported systems “have the same domain.”
The lower Lean carrier

$$
\operatorname{PDS}(X,Y)
  = \operatorname{Distribution}(\operatorname{System.DDS}(X,Y))
$$

is a signed finite-support algebra. Nonnegativity, normalization, and a common
domain are explicit predicates or structures rather than hidden assumptions.
Immediately before Definition 2.14 (printed p. 15), Lanzenberger says: “we do
not assume that the corresponding distributions are probability
distributions.”
`CommonDomain.Presentation` packages nonnegative arbitrary mass and an explicit
domain; `CommonDomain.ProbabilityPresentation` packages a normalized law with
a common domain.

Lanzenberger, Definition 2.15 (printed p. 15), says a PDE “is a distribution
over $(Y,X)$-DDE.” Observation pushes a PDS forward through the deterministic
transcript function.

### Equivalence, quotient, and distance

Lanzenberger, Definition 2.17 (printed p. 16), requires equivalent PDSs to
“have the same domain” and to agree “for all compatible $(Y,X)$-DDE.” The Lean
relation also records stopping because `System.tr` is partial. Quotienting
`Presentation` gives the arbitrary-mass `RandomSystem`; quotienting
`ProbabilityPresentation` gives `ProbabilityRandomSystem`.

Lanzenberger, Definition 2.26 (printed p. 18), begins “For two random
$(X,Y)$-systems $S$ and $T$ with the same domain” and takes the supremum over
DDEs compatible with both. `CommonDomain.Presentation.Adv` enforces that
clause by taking two presentations in one fixed-domain fibre. The broader
`PDS.advantage` is the same pair-specific formula before the common-domain
condition is packaged. `PDS.advantageOnDomain` is a separate auxiliary restricted to
DDEs that are compatible with a named domain and globally halting; it is not
Definition 2.26. The normalized quotient metric is added after the
common-domain presentation has been embedded into the ambient cumulative
random-system carrier.

### Parallel composition and H-coefficient bounds

Lanzenberger, Definition 2.13 (printed p. 14), begins: “The parallel
composition of a family of $(X_i,Y_i)$-DDS.” `RandomSystems/Parallel.lean`
implements the ordered binary specialization with ordinary sum tags. Query
and answer projections determine component behavior. Reassociation,
commutation, and units require the explicit relabelings proved by the library;
they are not definitional equalities.

`RandomSystems/TranscriptFactor.lean` owns the exact factorization of a fixed
transcript into its environment and system conditions, including evaluation
of the system factor for prefix-closed domain-filtered function evaluators.
`RandomSystems/Technique/HCoefficient.lean` consumes that neutral semantic
surface and owns the finite-support ratio and partition bounds for partial,
compatible, stopping DDEs. The transcript cells, cellwise ratio, and cell-mass
bound remain explicit. These theorems are fixed-interface RS results and
require no converter or CC import.

## 3. Query-indexed converter extension

Import `RandomSystems.Converter` for query-indexed DDSs, branch-finite DDCs,
deterministic attachment, and the ambient cumulative random-system carrier.
The fixed-interface layer remains an independent import; the common-domain
embedding below relates the two carriers.

### Ambient attempted-history carrier

For an interface $A=(Q_A,R_A)$, the optional layer uses the attempted-history
presentation

$$
\operatorname{Ambient.DDS}(A)
  = (h : \operatorname{History}(Q_A))
      \to \operatorname{Option}(R_A(\operatorname{last}(h))),
$$

where a history is a nonempty list. `some y` is an answer and `none` is a
rejected query. Rejected attempts remain in later histories.

A received history for a converter from inner $B$ to outer $A$ alternates
outer queries with dependent inner replies. At a received history $h$, a raw
converter is a partial function with response type

$$
\operatorname{Response}_{A,B}(h)
  = Q_B \sqcup \operatorname{Option}
      (R_A(\operatorname{lastOuter}(h))).
$$

Thus the output is an inner query or an outer reply in the type selected by
the latest outer query. `Complete` states that the graph is defined on the
alternating tree that it generates, and canonicalization removes off-tree
values. `BranchFinite` says that every legal chain of consecutive inner
queries is well-founded. Jost,
immediately before Definition 2.2.2 (printed p. 17), says a converter is
“allowed to make a bounded number of queries to the inside interfaces.” The
bounded-inner-query constructors carry a numerical bound; the general Lean carrier
uses the weaker pointwise-finite condition needed by the attachment theorem.
This is an explicit generalization of Jost's bounded presentation, not a claim
that Jost states branch-finiteness.

`DDC` contains only the canonical function and its branch-finiteness proof.
Attachment and serial composition are external operations on that carrier.

### Attachment and algebraic laws

For

$$
C : \operatorname{DDC}(U,V,X,Y),
\qquad
S : \operatorname{Ambient.DDS}(X,Y),
$$

attachment creates

$$
C * S : \operatorname{Ambient.DDS}(U,V).
$$

At an outer history, the compatible full transcript is the unique finite graph
whose converter entries are values of $C$ and whose inner answers are values of
$S$ on the induced complete inner histories. `applySystem` returns its final
outer answer. Branch-finiteness proves existence; graph equations prove
uniqueness. Stateless function composition is the one-query special case of
this definition, not a separate attachment operation.

Maurer--Renner 2016, Section 3.3 (printed p. 7), states
“$(\beta \circ \alpha)^iR = \beta^i(\alpha^iR)$.” The DDC layer proves

$$
\operatorname{applySystem}(C;D,S)
  = \operatorname{applySystem}(C,\operatorname{applySystem}(D,S)).
$$

Forwarding is the identity. Serial composition is associative on canonical DDC
graphs. Routed parallel and probabilistic-converter structure are outside this
release boundary.

`DDS.ofFunction`, `DDC.ofInnerQueryBound`, `DDC.ofBoundedInnerQueries`, and
`DDC.filter` provide pure-function constructors. A user may define a
bounded-inner-query function by pattern matching or recursion and obtain a DDC
from the constructor's generic closing proof; there is no public evaluator or
mutable-state semantics.

### Observation and random-system action

`Ambient.RandomSystem(A)` is the cumulative mass function on finite attempted
query-and-reply histories at $A$. Its flow law is the probability law of the
next optional reply. A normalized finite-support law over ambient DDSs is one
presentation of this carrier, not a second resource type.

`RandomSystems/Converter/RandomSystemAction.lean` compiles every finite outer
observation through a branch-finite DDC and defines
`RandomSystem.applyDDC`. Finite DDE observation factorization and
statistical-distance data processing prove that this action is non-expanding.
The forwarding and serial theorems are the identity and composition laws for
the action, while `applyDDC_ofPDS_eq` states that finite PDS interpretation
commutes with attachment. The scoped categorical action makes
`converter.asHom • system` notation for the same function.

### Common-domain bridge

`RandomSystems/Converter/CommonDomainEmbedding.lean` embeds normalized
common-domain partial systems into the cumulative query-indexed carrier.
`embedDDS` is a coding map; it does not replace partial DDS semantics.

`RandomSystems.CommonDomain.DDC` is an ambient DDC together with the statement
that its action preserves the embedded image. Attachment in the common-domain
carrier is the unique preimage under the injective embedding:

$$
\operatorname{toAmbient}(C * R)
= \operatorname{Ambient.RandomSystem.applyDDC}
    (C,\operatorname{toAmbient}(R)).
$$

Identity, serial closure, equality, and non-expansion follow from this
commuting equation and injectivity. This fixed-interface presentation installs
neither a converter category nor a second `ResourceAlgebra`.

## 4. Scoped deterministic category boundary

`RandomSystems.Ambient.Interface` is a query type together with the answer type
selected by each query. For interfaces $A$ and $B$,

$$
\operatorname{Hom}(A,B)
  = \operatorname{Ambient.DDC}
      (A,B).
$$

Forwarding, serial identity, and serial associativity make these interfaces a
category. `Interface.ddcCategory` and `DDC.category` own the scoped instance;
`DDC.asHom` is the explicit readable boundary from a concrete DDC to a
categorical morphism. `DDC.homAction` supplies the matching scoped action on
cumulative random systems. Opening `RandomSystems.Ambient.DDC` therefore makes
ordinary `𝟙`, `≫`, and `•` notation available without installing a global
category or a duplicate global scalar instance.

No monoidal converter category or concrete `ResourceAlgebra` instance is
exported by this release boundary.

## 5. Ownership summary

| Layer | Objects | Operations and laws | Owner |
|---|---|---|---|
| Constructive Cryptography | interface category, contravariant resource functor, specifications | exact/approximate construction, serial and ordered parallel composition, context-insensitivity, finite parallel, star closure | `ConstructiveCryptography.Categorical`, `ConstructiveCryptography.Categorical.ResourceAlgebra` |
| Fixed-interface RS | partial DDS/DDE, PDS, common-domain quotients | transcript, equivalence, distance, parallel, H-coefficient | `RandomSystems` |
| Converter extension | query-indexed DDS, branch-finite DDC, cumulative ambient random system | attachment, forwarding, serial composition, observation factorization, DPI, scoped categorical action | `RandomSystems.Converter` |

All public semantic statements are equations or relations between functions,
graphs, distributions, observations, quotients, distances, and specification
images. Recursive definitions and induction are proof mechanisms, not an
additional operational semantics.

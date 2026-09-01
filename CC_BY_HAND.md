# CC by hand

This guide gives a dependency-ordered route for reconstructing the
interface-indexed Constructive Cryptography and Random Systems development by
hand. It is a study
plan. The current release boundary supplies Stages 0--10 and the embedding
part of Stage 11; the later probabilistic-converter and adapter stages remain
the target architecture rather than exported modules.

The goal is understanding and ownership, not fewer lines. Pure functions,
pattern matching, inductive types, and structural or well-founded recursion are
all appropriate. Public semantics should still be expressed as functions,
graphs, distributions, observations, distances, and specification images.

## Working method

Create a separate worktree from one known-good commit:

```sh
git rev-parse HEAD
git worktree add ../abstract-crypto-by-hand -b codex/cc-by-hand COMMIT
```

For each stage, use two passes.

1. **Declaration pass.** Write the objects, operations, theorem statements,
   notation, and intended module imports. Bodies may be temporarily omitted in
   personal exercises, but the complete types must be fixed before consulting
   a proof.
2. **Proof pass.** Prove the statements in dependency order. Put auxiliary
   recursion and induction in a public `Internal` namespace unless they express
   a reusable mathematical fact.

For each declaration:

1. identify the paper statement and inspect the cited printed page;
2. write its complete Lean type;
3. list the earlier declarations on which it may depend;
4. implement it without reading the reference body;
5. build the smallest owning module;
6. inspect the declaration with `#check` or `#print`;
7. use `#print axioms` for a major endpoint;
8. only then compare with the reference implementation.

The source quotation belongs in the declaration docstring. Explain only the
Lean representation or a library-specific modeling choice in your own words;
do not repeat a paper quotation as a paraphrase.

Inside a proof, place one concise comment immediately before every
paper-level step, including routine steps, so the mathematical shape is visible
from top to bottom. Do not replace those local comments with one large opening
summary; Lean-only bookkeeping needs no commentary.

## Rules that remain fixed

- `RandomSystems` is fixed-interface RS and imports no converter or
  Constructive Cryptography layer.
- `RandomSystems.Converter` is optional and owns DDC attachment.
- `RandomSystemsCC` will own the concrete categorical adapters and
  construction judgments once that deferred boundary is exported.
- A DDS or DDC is a mathematical function on complete histories. A public
  `run`, `exec`, mutable state, scheduler, reset, rollback, or fuel object is
  not part of the model.
- Rejection is an `Option.none` value in the ambient attempted-history model;
  raw DDC partiality is reserved for malformed histories.
- DDC equality is equality of canonical function graphs, not equality after
  attachment to one chosen system.
- `DDC` uses branch-finiteness. Finite-dialogue constructors may establish it
  from an explicit numerical bound, but no uniform-bound field belongs to the
  carrier.
- Common-domain DDCs preserve the entire embedded image. Do not replace this
  by total-completion absorption.
- Parallel composition is ordered and tagged. Use only the explicit
  relabeling, reassociation, and empty laws already proved.
- Do not introduce a universal `DDS(*,*)`, manual interface coercions, or a
  second monoidal structure.
- Use Maurer terminology: resource, converter, DDS, DDC, PDS, DDE, PDC, PDE,
  attachment, serial, parallel, observation, equivalence, and distance.

## Stage 0: record the target surface

Use the public roots and final owners, not superseded paths or implementation
details:

```sh
lake env lean --src-deps ConstructiveCryptography/Categorical.lean
lake env lean --src-deps RandomSystems.lean
lake env lean --src-deps RandomSystems/Converter.lean
```

Record the public declarations in each owning module. Classify them as object,
operation, or law. Auxiliary factorization relations and induction lemmas are
reconstructed only if your proof needs them.

Gate: every public declaration has one owner, and no stage depends on a later
owner.

## Stage 1: abstract specifications

Owner: `ConstructiveCryptography/Categorical.lean`.

Start with an arbitrary category $\mathbf C$ and functor
$F : \mathbf C \to \mathbf{Type}$.

Write the objects and operations first:

- `Specification F A` as a set in `F.obj A`;
- direct image under `f : A \to B`;
- exact construction as direct-image inclusion;
- approximate construction using the metric in the target fibre;
- `IsNonexpanding F`.

Maurer--Renner 2016, Definition 1 (printed p. 11), states
“$\mathcal R \xrightarrow{\pi} \mathcal S :\Longleftrightarrow
\pi\mathcal R \subseteq \mathcal S$.” Use that statement directly.

Then prove:

- identity and serial direct-image equations;
- identity and serial exact constructions;
- approximate identity and weakening;
- approximate serial composition with error addition.

Gate: the approximate serial theorem uses only functor composition, one
triangle inequality, and non-expansion.

## Stage 2: endomorphism-family closure

Owner: `ConstructiveCryptography/Categorical/Star.lean`.

At one object $A$, define a selected submonoid of `End A`, its action through
$F$, and the direct-image closure of a specification. Prove membership,
inclusion, and idempotence. Finally prove the exact and approximate lemmas that
use an explicitly supplied simulator equation or distance bound.

Maurer--Renner 2016, Section 3.4 (printed p. 8), defines
$\mathcal R^* := \mathcal R\Sigma
= \{R\beta \mid R \in \mathcal R,\ \beta \in \Sigma\}$. Use the submonoid
only as Lean's representation of this composition-closed family.

Gate: simulation appears only as a proof witness. The construction relation
from Stage 1 is unchanged.

## Stage 3: fixed-interface deterministic systems

Owners: `RandomSystems/DDS.lean` and `RandomSystems/DDE.lean`.

Lanzenberger, Definition 2.9 (printed p. 13), defines a DDS as “a partial
function” with “prefix-closed domain.” Write `System.Raw`, `System.Valid`,
`System.DDS`, `System.dom`, and `System.output`. Add ordinary-function and
complete-history constructors.

Definition 2.9 (printed p. 13) calls a DDS finite when “$X$ is finite and
$\operatorname{dom}(s) \subseteq \bigcup_{i \leq n} X^i$ for some
$n \in \mathbb N$.” Keep those conditions as theorem hypotheses rather than
fields of the generic DDS.

Lanzenberger, Definition 2.11 (printed p. 14), defines a DDE as “a partial
function” “with prefix-closed domain.” Write its partial function, halting
predicate, and the transcript types. Definition 2.12 calls a transcript “the
sequence of pairs.” Define
`trExtend`, `trN`, `Stops`, `tr`, compatibility, and compatibility with a named
domain.

Prove the transcript invariants only after the function definitions are clear:

- one stage is unchanged or appends one query-answer pair;
- once stalled, all later stages agree;
- compatible transcripts cannot stall because of a system-side domain error;
- fixed queries produce the expected transcript.

Gate: all state is dependence on complete histories. No separate transition
machine appears in a public type.

## Stage 4: fixed-interface probabilistic systems

Owners: `RandomSystems/PDS.lean`, `Observation.lean`, `RandomSystem.lean`, and
`Distance.lean`.

Define the broad finite-support distribution algebra over DDSs. Keep
nonnegativity, normalization, and common domain explicit. Then write:

- deterministic transcript pushforward;
- PDE observation;
- common-domain arbitrary-mass and normalized presentations;
- observational equivalence;
- the two quotient carriers;
- Lanzenberger's `CommonDomain.Presentation.Adv`, the broader auxiliary
  `PDS.advantage`, and the globally halting auxiliary `PDS.advantageOnDomain`.

Immediately before Definition 2.14 (printed p. 15), Lanzenberger says: “we do
not assume that the corresponding distributions are probability
distributions.” Preserve the nonnegative arbitrary-mass presentation and add
the normalized presentation as a separate specialization.

Lanzenberger, Definition 2.14 (printed p. 15), says supported DDSs “have the
same domain.” Definition 2.17 (printed p. 16) quantifies over “all compatible
$(Y,X)$-DDE.” Definition 2.26 (printed p. 18) begins “For two random
$(X,Y)$-systems $S$ and $T$ with the same domain” and says “the supremum ranges
over all compatible $(Y,X)$-DDE.” Preserve those scopes exactly.

Prove reflexivity, symmetry, and transitivity before forming the quotients.
Prove `Adv_self`, `advantage_self`, `advantageOnDomain_self`,
`advantageOnDomain_triangle`, and `advantageOnDomain_le_advantage` in the
fixed-interface distance layer. The normalized quotient metric is installed
only after the ambient embedding in Stages 10--11.

Gate: `Adv` is defined only on one fixed-domain fibre. `advantageOnDomain` is the
separate globally halting auxiliary and must not be presented as Definition
2.26.

## Stage 5: fixed-interface parallel and H-technique

Owners: `RandomSystems/Parallel.lean` and
`RandomSystems/Technique/HCoefficient.lean`.

Implement ordered binary parallel DDSs by sum-tagged queries and answers.
Lift the operation to the common-domain presentations and quotients. Prove the
component equations, equivalence congruence, and the exported distance bounds.

For the H-technique, define the transcript system factor, finite cells, the
cellwise ratio, and cell-mass bounds explicitly. Prove
`trLaw_partition_finiteSupport_le`, then `advantage_le_weighted_cells`. An application
may specialize the cell type to a good/bad partition.

Gate: importing `RandomSystems` now suffices for a fixed-interface proof; no DDC
or construction judgment is present.

## Stage 6: ambient DDS and raw DDC functions

Owner: `RandomSystems/Converter/DDC.lean`.

Define:

```text
Interface             = (query : Type, answer : query -> Type)
History A             = nonempty finite lists over A.query
Ambient.DDS A         = (h : History A) -> Option (A.answer h.last)
DDC.History.Input A B = A.query + Sigma q : B.query, Option (B.answer q)
DDC.History A B       = a received history with its nonempty outer projection
DDC.Response h        = B.query + Option (A.answer h.lastOuter)
DDC.Raw A B           = (h : DDC.History A B) -> Part (DDC.Response h)
```

Then define the exact legal alternating tree, `Complete`, canonicalization,
`InnerContinuation`, `BranchFinite`, and `DDC`.

Jost, immediately before Definition 2.2.2 (printed p. 17), says the converter
is “allowed to make a bounded number of queries to the inside interfaces.”
Use an explicit numerical bound in the finite-dialogue constructors and prove
that it constructs a branch-finite DDC. The general carrier keeps the weaker
pointwise-finite condition, and its docstring records that this generalizes
Jost's bounded presentation.

Gate: the DDC structure contains the canonical function, its exact-domain
equation, and branch-finiteness—not attachment or serial operations.

## Stage 7: ergonomic function constructors

Owners: `RandomSystems/Converter/DDS.lean`, `Filter.lean`, and
`BoundedInnerQueries.lean`.

Build reusable constructors for:

- ordinary-function DDSs;
- bounded response tables;
- finite dialogues;
- complete-history filters.

Define examples as ordinary Lean functions, by equations, pattern matching,
or recursion. The constructor should discharge the generic graph and closing
facts once; each new DDC should prove only its mathematical response equation
and any bound not carried by the constructor.

Gate: a user can define a nontrivial system or converter without constructing
an evaluator object.

## Stage 8: attachment

Owner: `RandomSystems/Converter/ApplySystem.lean`.

Define full transcripts and their outer-input and inner-query projections.
State compatibility as equations between:

- each DDC response and the converter's complete received prefix;
- each inner reply and the DDS value on its complete attempted-query prefix;
- the requested outer history and its projection.

Prove existence by well-founded induction on `InnerContinuation`, uniqueness
from graph equations, and define `applySystem` from the unique transcript.

Gate: the public characterization of attachment is an equality of function
values. The one-query stateless case reduces to ordinary function composition
without a separate definition.

## Stage 9: deterministic converter algebra

Owner: `Serial.lean` under `RandomSystems/Converter/`.

Write forwarding and prove that it acts identically. Define serial composition
by canonical graph factorization and prove:

$$
(C;D)*S = C*(D*S),
$$

both forwarding identities, and associativity.

Gate: arbitrary serial chains use associativity; no theorem is specialized to
three converters. Routed parallel and relabeling are deferred with the selected
probabilistic category.

## Stage 10: cumulative random systems and deterministic action

Owners: `RandomSystems/Converter/Observation.lean`, `RandomSystem.lean`,
and `RandomSystemAction.lean`.

Factor every finite outer observation through:

1. an induced inner DDE;
2. a finite inner transcript;
3. a deterministic transcript projection.

Define the ambient random system directly as a normalized cumulative mass
function on finite attempted histories, with the one-query extension law.
Define its finite observations and observational distance. Map a normalized
finite-support PDS into this carrier without identifying the ambient carrier
with a quotient of presentations.

Compile every finite outer observation through a DDC into an inner observation.
Use this factorization and statistical-distance data processing to define
`applyDDC` and prove deterministic attachment is non-expanding.

Gate: every branch-finite DDC acts on the cumulative carrier without an
absorption field or representative-specific witness.

## Stage 11: common-domain bridge (partly deferred)

Owners: `RandomSystems/Converter/CommonDomainEmbedding.lean`,
`CommonDomain.lean`, and `CommonDomainParallel.lean`.

Define the completion embedding of partial DDSs, lift it to normalized
presentations, and prove observation, equivalence, distance, and injectivity
bridges. Then define:

$$
\operatorname{PreservesImage}(C)
\quad\Longleftrightarrow\quad
\forall R,\ C*\operatorname{toAmbient}(R)
\text{ has a common-domain preimage}.
$$

Package `RandomSystems.CommonDomain.DDC` as an ambient DDC plus this property.
Define its attachment by the unique preimage and prove the commuting equation,
non-expansion, identity, serial closure, and the ordered-parallel bridge. Keep
this as a fixed-interface presentation; do not install another category.

Gate: no stronger DDE-absorption condition has entered the restricted DDC.

## Stage 12: the sole converter category and CC judgments (deferred)

Owners: `RandomSystems/Converter/PDC/Category.lean`,
`RandomSystems/Converter/PDC/RandomSystemFunctor.lean`, and
`RandomSystemsCC/ResourceAlgebra.lean`.

Define `Interface` from query-indexed answer alphabets. Use cumulative PDCs as
arrows, forwarding as identity, and serial composition as categorical
composition; embed DDCs as the deterministic specialization. Then define

$$
\operatorname{randomSystems} :
\mathbf{Interface}^{\mathrm{op}} \to \mathbf{Type}
$$

from cumulative PDC attachment. Instantiate the sole ambient `ResourceAlgebra`,
including specifications, exact and approximate construction, non-expansion,
and ordered parallel.

Retain common-domain image-preserving DDCs only as a presentation bridge into
this carrier.

Gate: there is exactly one interface category, one ordered parallel, and one
ambient `ResourceAlgebra` instance.

## Stage 13: resource algebra, finite parallel, and star

Owners: `ConstructiveCryptography/Categorical/ResourceAlgebra.lean`,
`ResourceAlgebra/Finite.lean`, `Star.lean`, and
`RandomSystemsCC/ResourceAlgebra.lean`.

Lift ordered parallel to specifications and prove the exact and approximate
binary construction theorems. Derive finite routed resources, converters,
specifications, error sums, construction, and non-expansion by recursion.
Instantiate endomorphism-family star closure from Stage 2.

Gate: the ambient interface category supplies the one proved ordered
`MonoidalCategory`; no symmetry is assumed and no second parallel class is
declared.

## Final verification

Run focused builds while reconstructing. At the end run:

```sh
lake build ConstructiveCryptography
lake build ConstructiveCryptography
lake build RandomSystems
lake build RandomSystemsConverter
lake build ConstructiveCryptographyTests
lake build RandomSystemsTests
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' \
  ConstructiveCryptography RandomSystems
rg -n 'maxHeartbeats|maxRecDepth|native_decide' \
  ConstructiveCryptography RandomSystems
git diff --check
```

Check axioms for at least:

- exact and approximate serial construction;
- DDC serial associativity and serial attachment;
- ambient and common-domain non-expansion;
- the concrete category functor laws;
- parallel exact and approximate construction.

The accepted envelope is no larger than `propext`, `Classical.choice`, and
`Quot.sound`. Also inspect root dependencies: `RandomSystems` must remain free
of Converter and Constructive Cryptography imports, and no production theory
module may import a
test module.

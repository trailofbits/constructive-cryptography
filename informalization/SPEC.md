# Semantic informalization backend specification

Status: **authoritative design specification**
Version: 0.3
Date: 2026-08-28

> **Experimental language baseline.** This document remains authoritative for
> the backend trust boundary and pipeline. The accepted switching passage is a
> prose regression contract for the implemented slice; other sentence/event
> examples remain proposals until their breadth passages are accepted.
> [`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md) governs the
> non-regression passages and breadth gate for both `/verbose` and
> `/informalization`. The breadth gate still blocks production promotion.

This document specifies the generic Lean-to-natural-language backend used by
`abstract-crypto`.  It replaces the earlier output-driven approach in which
particular theorem names, tactic spellings, or local hypothesis names selected
sentences.

The independent controlled-language authoring frontend is specified in
[`VERBOSE_SPEC.md`](VERBOSE_SPEC.md). Both modules share
[`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md), but neither implements the other.

The specification is based on:

- Kyle Miller and Patrick Massot's InformalLean architecture, especially the
  [ICERM talk](https://kmill.github.io/informalization/icerm_talk.pdf), the
  [Rudin Lean source](https://kmill.github.io/informalization/rudin.lean.txt),
  and its [generated document](https://kmill.github.io/informalization/rudin.html);
- CR18's conditional-equivalence proofs, especially Theorem 4.17, the
  URP--URF switching lemma, and CBC-MAC Theorem 6.1 in
  [`../../random-systems/papers/CR18_LN.pdf`](../../random-systems/papers/CR18_LN.pdf);
- conventional game-hopping proofs, checked against
  [`../../random-systems/papers/BonehShoup.pdf`](../../random-systems/papers/BonehShoup.pdf);
- the checked declarations and proof-language conventions of this repository.

The deployed Miller examples are behavioral references, not source-code
dependencies.  InformalLean's core implementation is not public, and the talk
explicitly describes its ontology and describer specifications as ongoing
work.

## Implementation conformance (2026-08-28)

This table separates the contract in this document from the implementation
that currently exists.  `Partial` never means that an acceptance gate passes.

| Item | Status | Current evidence / missing work |
| --- | --- | --- |
| I1 checked evidence | Partial | Semantic nodes retain exact `Expr`/declaration provenance, and the proof-evidence tree retains proof terms, expected propositions, local contexts, and every proof-valued premise. The reader bridge now deliberately omits raw expressions, proof-step labels, and evidence trailers from public JSON/HTML. A first-class internal node-to-evidence index, separate from the reader schema, is still pending. |
| I2 semantic before surface | Partial | The Random Systems profile now decodes operand-bearing canonical systems, games, conditions, bounds, claims, formula schemas, rule applications, non-proof operands, and proof obligations before discourse or surface realization. The switching and CBC slices have a recursive mathematical-content tree and a capture-avoiding scoped symbol table for checked operands; theorem-shaped predicate/string tables are absent. Generalization of the content vocabulary and notation policy across the acceptance corpus remains. |
| I3 name invariance | Partial | Local-name triggers are removed. Tests cover alpha-renaming and two registered aliases with the same rule role; the full acceptance corpus is not covered. |
| I4 proof-refactoring invariance | Passing for the implemented slice | Checked proof applications and semantic fingerprints are invariant in tests under `exact`/`apply`, inline proof versus a local `have`, registered macro expansion, `rw`/`simpa`/`calc`, independent routine-premise reordering, and explicit versus automated routine derivations. Broader corpus coverage remains. |
| I5 domain separation | Passing for the implemented slice | The typed core is domain-neutral; Random Systems has its own catalog and LeanTeX module, topology has its own language module, and tests reject domain vocabulary in the neutral profile. The legacy Random Systems English adapter remains quarantined behind an explicit profile. |
| I6 relation precision | Partial | Typed roles and distinct plan genres exist for exact forgetting, CR18 conditional equivalence, non-adaptive blind winning, collision/birthday counting, H-technique, hybrid, and game hop; tests prevent CE/game-hop and H/counting collapse. The full relation corpus listed in I6 is not implemented. |
| I7 root content | Passing for the switching target | The selected root is the genuine internal [`RandomSystems.Switching.urf_urp_switching`](../RandomSystems/Technique/Switching.lean#L391). Its report recovers an advantage bound between query-restricted URF and URP systems, while an arithmetic inequality is rejected by the root gate. |
| I8 graceful fallback | Partial | Unregistered proof regions remain exact deduplicated leaves with stable internal references. Raw kernel expressions are no longer copied into the semantic reader. A safe mathematical fallback and a separate developer-facing provenance view are still required for unsupported regions. |
| V1 build and soundness | Passing for the switching slice | `lake build` and `lake run test` pass. The switching theorem contains no `sorry`/`admit`, and its axiom report lists `propext`, `Classical.choice`, and `Quot.sound`. Semantic JSON and semantic HTML are generated from the genuine theorem. The regenerated page was inspected live with KaTeX loaded; the browser console was empty and the document had no horizontal page overflow. |
| V2 evidence completeness | Partial | Realized moves retain internal evidence references, while reader-facing HTML/JSON suppresses evidence IDs and checked-expression dumps. A complete, machine-checkable node-to-evidence coverage map that remains outside the reader surface is still pending. |
| V3 semantic invariance | Passing for the implemented slice | Alpha-renaming, registered aliases, `exact`/`apply`, `rw`/`simpa`/`calc`, inline/named helpers, independent routine-premise reordering, and explicit/automated routine derivations are tested. Transparent helper insertion below an expanded CBC-style endpoint is also invariant. The broader corpus remains. |
| V4 negative classification | Partial | `List -> transcript`, local `Bad -> bad event`, arithmetic roots, partially applied registered rules, and CE/game-hop confusion are tested. The complete V4 matrix is not yet encoded. |
| V5 statement quality | Passing for the switching slice | The Random Systems profile aggregates the carrier as a nonempty finite alphabet, presents `q` as a natural-number query budget, and displays the checked sharp bound `\(\operatorname{Adv}_{\bot}([q]\mathsf{URF}_{X,X},[q]\mathsf{URP}_X) \le q(q-1)/(2|X|)\)`. Domain notation suppresses the Lean declaration spelling `advFullyDefined`, `fTransform`, `ENNReal.ofReal`, and `Fintype.card` without collapsing fully-defined advantage into class distance; the generic profile remains unchanged. |
| V6 proof-plan quality | Passing for the switching and CBC slices | The switching report recovers exact forgetting, conditional equivalence, blind/non-adaptive collision analysis, and the final combination. The genuine CBC report continues below `realPDS_advantage_le` and `cbcPDS_advantage_le` through block-count restriction identities, conditional uniformity, terminal-input separation, collision mass/walk counting, scalar closure, the ambient PDS-to-random-system distance bridge, and serial construction. Premise and bounded-expansion edges form checked recursive support forests; semantic depth is diagnostic only. The rest of the corpus remains. |
| V7 corpus language | Partial | Switching formulas are produced from canonical operands and registered rule schemas, including the quantifier-sensitive supremum step. CBC now has a genuine theorem-driven semantic-language acceptance case covering its construction-to-scalar proof spine, checked attachment and probability identities, terminal-input separation, call-site walk, collision mass, and scalar closure without private-helper or tactic prose. Hybrid, reduction, and H-coefficient language acceptance cases remain. |
| V8 interaction quality | Partial | Proof-depth disclosure and proof-state inspection are separate interactions, as in Miller's reader. The genuine switching page has five independently nested replacement nodes: CE restriction contains base collision CE, while non-adaptive reduction contains fixed-query and collision branches and collision contains birthday counting. It has one root checkpoint when collapsed and four additional checked, reader-safe checkpoints inside expansions. Live browser QA opened the branches one level at a time and verified the reader-safe checkpoints. The live CBC page expands to the output-factorization, terminal-input, and collision-mass nodes without tactic text, private helper names, console errors, or horizontal overflow. Two exact low-level switching states still fail closed, CBC proof-state checkpoints remain incomplete, and the broader corpus remains. |
| V9 forbidden patterns | Passing for the switching slice | `lake run test` scans production modules for local-name/tactic triggers and the removed `hasUrfUrpSwitchingShape`/`switchingMoveText` templates. The public expand-all surface rejects declaration paths, generated identifiers, proof-step IDs, and raw kernel syntax. Wider corpus coverage remains part of V7. |

The conformance table must be updated in the same change that advances any
status.  A preview or successful build alone does not advance V2--V8.

The current integration artifacts are
[`preview/switching.semantic.json`](preview/switching.semantic.json) and its
Miller-style interactive rendering
[`preview/switching.html`](preview/switching.html). Both are generated from the
genuine switching declaration; the former exposes the typed graph and plan,
while the latter exposes the recursive switching proof and nested semantic
details. Its nested details are projected from checked premise/macro edges, not
from a flat depth counter. Checked expressions and evidence identifiers belong
to the internal semantic report and are not reader content.

## 1. Objective

Given a checked Lean declaration and its elaboration evidence, generate an
interactive, hierarchically expandable mathematical explanation whose visible
content:

1. states the same theorem;
2. presents the proof's mathematical argument rather than its tactic script;
3. uses the conventional language and discourse structure of the relevant
   mathematical domain;
4. keeps every mathematical assertion traceable to checked Lean evidence; and
5. remains stable under semantically irrelevant proof refactorings.

For cryptography, the backend must be able to say what systems are compared,
under which access model, by which proof method, where the error enters, and
how the final bound follows.

## 2. Non-goals

The backend is not:

- a store of hand-written informal proofs synchronized with Lean;
- a collection of theorem-specific paragraph templates;
- a tactic-to-English pretty-printer;
- an LLM that is trusted to invent mathematical assertions;
- a replacement for proving the system-level theorem in Lean;
- a Verso-specific renderer; or
- a claim that arbitrary Lean code can already be rendered as publication-
  quality mathematics without domain extensions.

An LLM may eventually rank stylistic alternatives after the symbolic backend
has fixed their meaning.  It must not add, delete, or alter mathematical
content on the trusted path.

## 3. Fundamental invariants

### I1. Checked-evidence invariant

Every mathematical proposition in the semantic document must carry one or more
evidence references to an elaborated expression, local declaration, theorem
application, proof-term fragment, or goal transition.

This is an internal trust invariant, not a presentation requirement. Evidence
references must be available in the semantic report or provenance index, but
their identifiers, raw expressions, and proof terms must not appear in the
reader-facing document.

Pure discourse connectives such as "therefore" may lack independent evidence,
but their relation to adjacent messages must be represented in the discourse
plan.

### I2. Semantic-before-surface invariant

No extraction or planning component may return final prose.  The trusted
pipeline must construct typed semantic values before surface realization.

### I3. Name-invariance invariant

Renaming local variables, hypotheses, theorem aliases, or tactic-generated
names must not change the semantic proof plan.  A preferred displayed symbol
may change when the author explicitly changes it.

### I4. Proof-refactoring invariant

Replacing a proof step by a semantically equivalent `exact`, `apply`, `refine`,
`rw`, `simpa`, `calc`, or named helper must not change the collapsed argument
when the same registered mathematical rules and obligations are used.

### I5. Domain-separation invariant

The generic backend owns elaboration evidence, semantic data structures,
planning interfaces, grammar, and presentation conversion.  A domain package
owns its entities, relations, proof-rule roles, terminology, and notation.

Random Systems declarations must not be embedded in a generic Mathlib
language module.

### I6. Relation-precision invariant

Distinct formal relations remain distinct in the semantic representation.
In particular:

- exact system equivalence;
- exact game equivalence;
- one-sided conditional equivalence;
- symmetric agreement-until-bad/game-playing relations;
- H-technique ratio or equality hypotheses;
- reductions and data-processing inequalities; and
- coupling or representative-selection arguments

must not be collapsed into a generic phrase such as "identical until bad"
without a checked bridge.

### I7. Root-content invariant

The backend may only informalize the content of the selected declaration.  An
arithmetic birthday inequality cannot be presented as a URF/URP
indistinguishability theorem.  Supporting scalar lemmas appear as expandable
leaves below a genuine system-level root theorem.

### I8. Graceful-fallback invariant

Unrecognized content must remain correct and traceable.  It may be rendered as
safe LeanTeX when the notation layer can express it, or retained only in the
developer-facing provenance report until a reader-safe rendering exists. It
must not be assigned a guessed cryptographic interpretation, silently dropped
from evidence coverage, or exposed as a raw kernel-expression dump.

## 4. Architecture

```text
Lean source module
  |
  v
frontend: declaration + InfoTrees + proof terms + source ranges
  |
  v
semantic decoding
  |- entity and object decoding
  |- proposition decoding
  |- applied-rule decoding
  `- proof evidence graph
  |
  v
domain proof-plan extraction
  |
  v
discourse planning and microplanning
  |
  v
surface realization + LeanTeX expressions
  |
  v
Explanation document
  |
  +--> standalone HTML reader
  `--> future Verso adapter
```

`Explanation` is a presentation document language.  It is not the semantic
intermediate representation.

### 4.1 External development topology

During development, the language tooling lives in one ordinary sibling Lake
project rather than in an `abstract-crypto` worktree.  That project has a local
path dependency on the live `abstract-crypto` checkout:

```lean
require AbstractCryptography from "../abstract-crypto"
```

Its logical libraries are:

```text
LanguageDesign       shared ontology, rule/role identifiers, relation frames,
                     discourse vocabulary, and annotation schema
Verbose              controlled-language syntax and deterministic lowering
Informalization      frontend evidence, semantic recovery, planning, and output
```

`Verbose` and `Informalization` are independent consumers of
`LanguageDesign`; neither imports the other as an implementation layer.  Their
required interaction is checked Lean.  Optional presentation metadata uses
the shared annotation schema and must also be available to ordinary Lean
source.

The local dependency deliberately follows the current working tree of
`abstract-crypto`, including in-progress source changes.  Development output
must record the dependency commit and whether that checkout is dirty.  CI or a
release may replace the local dependency with a pinned revision, but local
development must not require synchronizing a second worktree branch.

The sibling project uses the same `lean-toolchain` as `abstract-crypto` and has
a gate that reports a mismatch before building.  It does not independently pin
a second Mathlib version when the dependency already supplies it.

The existing implementation is migrated, not redesigned wholesale:

- the current canonical semantic types, evidence extraction, planner,
  renderer, CLI, reader, and tests move under `Informalization` with minimal
  namespace churn;
- only genuinely shared declarative language data moves into
  `LanguageDesign`; and
- existing AC/CC controlled-language commands remain working while `Verbose`
  acquires Random Systems sentences incrementally.

## 5. Frontend evidence

The existing frontend remains responsible for:

- elaborating the selected source in its own Lake workspace;
- retaining declaration types and values;
- retaining `InfoTree`, `TacticInfo`, local contexts, and metavariable states;
- associating proof fragments with source ranges;
- reconstructing tactic/side-goal ownership when useful; and
- decompiling proof terms into smaller checked steps as a technical fallback.

Tactic syntax is evidence about source organization, not by itself evidence of
a mathematical discourse role.

### 5.1 Imported declarations versus source re-elaboration

The project has live path dependencies on both `abstract-crypto` and the
sibling `cbc-mac-cc` consumer. They make the latest declarations and compiled
proof terms available. That is sufficient for
statement decoding and proof-term-only fallback, but it is not sufficient for
the full interactive explanation: imported `.olean` files do not provide the
original source `InfoTree`, tactic checkpoints, or source ranges.

For a source-aware explanation, the frontend therefore continues to
re-elaborate the selected source file in memory under its owning Lake setup,
with the informalization instrumentation imported.  This does not modify the
source file.  A future build-time evidence artifact could avoid repeated
elaboration, but a path dependency by itself cannot replace this step.

The current CBC path is:

1. resolve `CBCMAC/Main.lean` in the sibling `cbc-mac-cc` project with
   `lake setup-file`;
2. prepend the instrumentation imports to an in-memory copy;
3. run the Lean frontend and retain the final environment, `InfoTree`s,
   proof terms, contexts, source ranges, and goal states;
4. locate `CBCMAC.cbc_randomness_expander`;
5. validate the explicitly selected CBC registry/profile against that
   environment;
6. decode the query-restricted real CBC system, ideal VIL random function,
   and distance bound;
7. recover and classify the recursive proof evidence;
8. construct the proof plan, evidence-compression coverage, discourse, and
   typed mathematical content;
9. bridge the discourse to the `Explanation` document; and
10. emit diagnostic semantic JSON, public `Explanation` JSON, and/or the
   standalone interactive HTML reader.

This CBC extension may name only CBC-specific declarations. General distance,
advantage, converter, game, conditional-equivalence, and blind-winning
declarations belong to the reusable Random Systems profile. A compile-time
disjointness check rejects an application overlay that repeats a shared
declaration. A later CC construction theorem composes the shared CC and Random
Systems ontologies with this same thin CBC vocabulary; it does not require a
second CBC informalizer.

Mathematical notation is also profile data. An application overlay may attach
a checked declaration to a notation form and semantic operand slots. A
notation may be atomic, applied, bracketed, or a typed template whose literal
pieces and named operand references are validated by
`DecoderProfile.hasWellFormedDeclarationNotations`; the
generic renderer consumes that data without matching application namespaces or
pretty-printed Lean text. Query-limit converters are decoded as query
restrictions, so the reader sees `[q] R` rather than an implementation-level
converter application. Other converters applied to games retain their exact
converter identity: a block restriction must never be reconstructed as a
query restriction merely because both carry a numerical operand. The CBC
acceptance test requires `CBC[B]`, `θ[B,q]`, `[q]R`, `R`, and `V` while
rejecting `CBCMAC.` from reader-facing prose.

## 6. Semantic intermediate representation

The exact Lean names below are illustrative.  The implementation may refine
the constructors while preserving their separation and invariants.

### 6.1 Evidence

```lean
structure EvidenceRef where
  declaration? : Option Name
  expression?  : Option Lean.Expr
  sourceRange? : Option Lean.Syntax.Range
  goalBefore?  : Option Lean.MVarId
  goalAfter    : Array Lean.MVarId
```

Every semantic node contains one or more `EvidenceRef`s, except structural
nodes whose children carry the evidence.

### 6.2 Mathematical entities and roles

The generic layer distinguishes at least:

- carrier, set, function, number, proposition, and generic mathematical object;
- domain-specific entity kind;
- semantic role within the current theorem; and
- presentation salience.

The crypto extension supplies roles including:

- input/output alphabet and message space;
- random system/resource and converter/construction;
- real system and ideal system;
- game, monotone binary output, and bad condition;
- environment, distinguisher, winner, and simulator;
- transcript and fixed query schedule;
- query, block, or horizon budget; and
- error or advantage bound.

Carrier declarations and typeclass instances are aggregated into mathematical
objects.  For example, a type together with finite group structure should be
presented as a finite group, not as a type followed by unrelated assumptions.
`DecidableEq`, universe levels, coercion instances, and implementation-only
normalization facts are normally hidden from the collapsed statement.

### 6.3 System expressions

The crypto extension represents system syntax structurally, including:

- named system;
- uniform random function;
- uniform random permutation;
- converter application;
- query/block restriction;
- enhancement of a system with an MBO;
- ignoring a game's MBO;
- parallel/cascade composition when supported; and
- explicitly unknown system expression.

The structural representation is separate from its notation and English
description.

### 6.4 Propositions and relations

The semantic proposition language includes generic logic plus domain relations
such as:

- distinguishing-advantage bound;
- construction within error;
- exact equivalence;
- conditional equivalence;
- game equivalence;
- bad-event or winning-probability bound;
- transcript-factor equality or ratio;
- query-schedule property;
- collision/freshness/distinctness statement; and
- numerical/counting bound.

Unknown propositions retain the original `Expr` internally. They render in the
reader only when the notation layer can produce safe mathematical content;
otherwise they remain visible in the developer-facing coverage report without
leaking kernel syntax into the proof.

### 6.5 Proof moves

Proof moves describe mathematical consequences, not tactic execution.  The
initial crypto vocabulary includes:

- define an MBO and enhance a system with it to obtain a game;
- identify the real system after ignoring the game's MBO;
- establish conditional equivalence;
- establish agreement outside a bad event;
- apply a conditional-equivalence-to-blind reduction;
- apply an H-technique theorem;
- establish a good-transcript equality or ratio;
- establish a bad-mass bound;
- introduce a hybrid or triangle decomposition;
- apply data processing or a reduction;
- fix a nonadaptive schedule;
- cover a bad event by collisions;
- apply a counting/birthday bound; and
- combine prior bounds and conclude.

Each move records instantiated arguments, generated obligations, cited
declarations, evidence, and child moves.

### 6.6 Applied declarations and premise slots

The extractor must not reduce a theorem application to its head name.  It
records the instantiated telescope in a representation equivalent to:

```lean
structure AppliedArgument where
  binderName : Name
  binderInfo : BinderInfo
  value : Expr
  instantiatedType : Expr
  isProof : Bool

structure AppliedDeclaration where
  evidence : EvidenceRef
  declaration : Name
  application : Expr
  expected : Expr
  arguments : Array AppliedArgument
```

A registered rule decoder maps those arguments to stable semantic slots such
as `real`, `ideal`, `game`, `condition`, `goodRatio`, `badMass`, or
`blindWinningBound`.  Slot names come from the declaration registration, not
from local hypotheses or the author's choice of binder spelling.  Proof-valued
arguments remain linked as premise evidence and become candidate child nodes.

The semantic fingerprint used by evidence audits erases evidence IDs, source
ranges, and local names, and alpha-normalizes expressions.  It does not erase
relations, instantiated systems, bounds, premise slots, proof-rule roles, or
the internal receipt for absorbed routine evidence.  Reader-output invariance
uses the narrower presentation fingerprint: it retains the complete
mathematical proof spine and fallback status but erases that routine-evidence
receipt.  Thus a `rw` proof may record different internal normalization work
without changing the informalization.

## 7. Semantic declaration registry

Domain knowledge is registered in the elaboration environment through stable
declaration metadata.  A registration maps a fully qualified Lean declaration
to:

- a semantic category;
- the roles of its explicit and relevant implicit arguments;
- a decoder that constructs a typed semantic value;
- optional theorem/proof-rule role;
- optional notation renderer; and
- optional lexical realization data.

Using a fully qualified declaration as a registry key is correct and mirrors
Miller's `@[english_param const.TopologicalSpace]` design.  The following are
forbidden as semantic discriminants:

- local user names such as `Bad`, `h_real`, or `h_ideal`;
- substring tests on tactic source;
- short unqualified theorem names;
- proof order without dependency/evidence analysis; and
- manually inserted replacement paragraphs.

Aliases may share a semantic role through registration.  Unregistered aliases
fall back safely rather than inheriting meaning from spelling.

### 7.1 Standalone-workspace boundary

Environment extensions are only visible to code compiled against the module
that declares their metadata type.  The standalone executable therefore
cannot pretend to discover an application-specific extension merely by its
name.  The supported designs are:

1. a small shared semantic-metadata package imported by both the target
   workspace and this backend; or
2. a statically compiled domain profile, optionally supplemented by a neutral
   exported registration manifest.

The first Random Systems slice may use a statically compiled profile.  It must
still produce the same typed registry entries and must not turn those entries
directly into prose.

## 8. Statement planning

The statement planner performs content selection before grammatical
realization.

For a security theorem it should normally foreground:

1. the real construction/system;
2. the ideal system;
3. the access model or restriction;
4. the claimed distance/advantage; and
5. the quantitative bound and substantive hypotheses.

It should subordinate or hide implementation parameters while keeping them
available in an expanded formal statement.

"Let `X` and `Y` be types" is not categorically forbidden: it is appropriate
for some generic theorems.  It is invalid when domain knowledge says that the
carriers are merely interfaces of already identified cryptographic systems or
can be aggregated into more informative mathematical entities.

### 8.1 Executable theorem-presentation contract

The normative data model is
[`LanguageDesign/Presentation.lean`](LanguageDesign/Presentation.lean).
A theorem presentation contains a reader-facing title and an ordered sequence
of introduction paragraphs. Each mathematical reference in those paragraphs
must name either a binder in the checked theorem telescope or a declaration in
the elaborated environment, and carries its displayed notation and a short
reader description. Empty titles, introductions, references, or descriptions
are rejected.

The presentation profile cannot restate the conclusion. The conclusion is
always rendered from the canonical checked claim and appended after the
introductions. This permits author control over terminology and exposition
without allowing presentation metadata to change the theorem. The same typed
reference becomes an accessible hover/focus target in the interactive reader.
The profile supplies only the paper notation and optional reader description.
While the elaborated environment is available, the backend automatically
captures the stable information used by a Lean editor hover: the checked name,
type, explicit expression, and declaration docstring. The renderer may locate
the explicitly supplied atomic notation in the typeset formula; it never
infers semantic identity from KaTeX text or a pretty-printed Lean name. The
theorem heading, theorem binders, registered declaration notations, and scoped
paper symbols all use this common mechanism.

Hover content must not create a scrollport or be clipped by the theorem pane.
It is rendered in a viewport-level floating layer, expands to the height
required by its Lean-derived description, signature, explicit expression, and
documentation, and is placed above or below its reference within the visible
window. Hover and keyboard focus expose the same content; neither requires
scrolling inside the hover surface.

## 9. Proof evidence graph and plan extraction

The extractor builds a dependency graph from:

- the theorem's elaborated proof term;
- instantiated registered theorem applications;
- goal transitions and local-context deltas;
- meaningful source boundaries such as named `have`s and `calc` steps; and
- optional controlled-language traces or semantic author annotations.

A source `have` is a useful candidate expansion boundary, but does not define
its discourse role.  Conversely, one application of a packaged theorem may
represent multiple paper-level obligations and must be expandable into them.

For each constant application, extraction telescopes the declaration type in
lockstep with the elaborated application arguments.  It retains binder
information, instantiated types, proof-valued premises, and the expected
conclusion.  Registered applications form semantic boundaries; casts,
rewrites, and normalization remain absorbed formal evidence unless a domain
rule assigns them mathematical meaning.

Before classifying a proof head, the extractor contracts consecutive head
beta-redexes. This covers elaborated `apply`, `simpa`, and local-helper
packaging in which an immediately applied lambda otherwise hides the same
registered theorem application. The normalization unfolds no declaration and
therefore cannot invent a new semantic step. A focused integration test must
show that the CBC collision conditional-equivalence theorem still exposes its
checked collision-free output-law lemma at the next disclosure level.

A promoted causal summary may mention collision-free distinct inputs and the
uniform consistent output law only when those registered checked descendants
are present in its own support subtree. An outer conditional-equivalence or
restriction theorem is not, by itself, evidence for either assertion.

Every collapsed plan node has primary evidence. Evidence hidden as an
implementation detail is listed as absorbed evidence in the semantic report.
Reader expansion shows semantic child claims, calculations, and definitions;
it never falls through to tactic text, proof-term `repr`, generated declaration
names, or raw checked propositions. The union of visible, child, and absorbed
evidence must cover all proof obligations reachable from the selected root,
and that coverage is validated outside the reader surface.

### 9.1 CR18 conditional-equivalence plan

```text
SecurityClaim(real, ideal, budget, epsilon)
  DefineGame(game, real, badCondition)
  ForgetsTo(game, real)
  EstablishCondEquiv(game, ideal)
    EstablishFreshnessOrDistinctness(...)
    EstablishConditionedOutputLaw(...)
  ApplyCondEquivToBlind(...)
  FixNonadaptiveSchedule(...)
  BoundBlindWinning(...)
    CoverByCollisions(...)
    ApplyBirthdayBound(...)
  ConcludeAdvantage(...)
```

Not every theorem contains every node.  The selected Lean endpoint and its
instantiated obligations determine the plan.

### 9.2 H-technique plan

```text
SecurityClaim(real, ideal, budget, epsilon)
  ApplyHTechnique(...)
  EstablishGoodTranscriptRatioOrEquality(...)
    SubstituteTranscriptFactors(...)
    ApplyRatioOrCountingBound(...)
  EstablishBadMassBound(...)
  CombineHTechniqueBounds(...)
```

### 9.3 Game-hop plan

```text
SecurityClaim(game0, gameN, epsilon)
  IntroduceHybridSequence(...)
  RelateAdjacentGames(...)
    EstablishAgreementOutsideBad(...)
    ApplyDifferenceLemma(...)
    BoundBadEvent(...)
  SumHopBounds(...)
  ConcludeAdvantage(...)
```

This plan is related to, but not identified with, CR18 conditional
equivalence.

### 9.4 Generic hybrid/reduction plan

The planner must also represent exact reshaping, triangle/hybrid steps,
post-processing/data processing, simulator reductions, coupling disagreement,
and numerical closure as distinct moves.

## 10. Discourse and surface realization

The discourse planner chooses:

- which semantic nodes appear in the collapsed proof;
- their rhetorical order and relation;
- paragraph and expansion boundaries;
- aggregation of compatible introductions or assumptions;
- references such as "the real system", "the ideal system", and "this game";
- when to repeat notation rather than use anaphora; and
- the level at which implementation details become expandable.

Surface realization handles articles, number agreement, conjunction,
subjunctive forms, punctuation, and domain lexemes.  LeanTeX handles embedded
mathematical expressions.

The collapsed proof should use corpus-attested cryptographic transitions such
as:

- "Define the following collision game."
- "Conditioned on this event not occurring, ..."
- "Applying the conditional-equivalence bound gives ..."
- "It remains to bound the blind winning probability."
- "For a fixed query schedule, ..."
- "The birthday bound therefore gives ..."

These are realization frames selected by semantic moves.  They must never be
selected because a tactic or local variable has a particular spelling.

### 10.1 Typed mathematical content

Surface realization must produce a typed content tree rather than an opaque
string. At minimum the tree distinguishes prose, inline mathematics, display
mathematics, definitions, equations, aligned calculations, and references to
previously introduced objects. Mathematical leaves are `MathExpr` values, not
preassembled LaTeX fragments embedded in sentences.

Each proof move therefore carries typed operands such as `real`, `ideal`,
`game`, `condition`, `budget`, `querySet`, and `bound`. A realization frame may
choose connective prose, but every formula must be assembled from those
operands by reusable constructors and the notation renderer. A branch that
recognizes a complete proof shape and returns a complete switching-specific
paragraph or formula string does not satisfy this requirement.

### 10.2 Scoped notation and symbol table

The discourse plan owns a scoped symbol table that maps semantic object
identities to display symbols such as \(R\), \(P\), \(\widehat R\), \(S\),
\(k\), and \(N\). It must:

- introduce a symbol before first use;
- keep the same object-symbol mapping in the statement, collapsed proof, and
  every expansion;
- avoid capture and collisions in nested claims;
- distinguish semantic equality from two objects that merely share a preferred
  spelling; and
- allow a renderer to choose Unicode, HTML, TeX, or Verso output from the same
  mathematical expression.

Retained proof contexts may contain fresh free-variable identifiers for a
copy of a theorem binder. The symbol key therefore keeps both exact expression
identity and the binder's stable user name. Exact identity governs ordinary
locals; matching theorem-binder identities reuse the root symbol and install
an exact local alias. This prevents spurious symbols such as \(q_1\) while
preserving capture avoidance.

The planner orders independent root moves by semantic discourse function, not
by the textual order of unrelated `have` declarations. In a conditional-
equivalence route it introduces the goal and system identities, performs the
comparison and conditional-equivalence reduction, states the residual blind-
winning obligation, proves that estimate, and returns to the root conclusion.
The residual obligation also establishes the foreground game, which later
estimates must reuse instead of introducing an unexplained generic \(G\).

### 10.3 Recursive claim and disclosure tree

The presentation projection is built from a recursive claim tree. Each node
contains a concise mathematical claim, zero or more semantic child claims, and
internal provenance. Children may themselves have children. A flat array of
detail phrases is not an adequate proof representation.

The collapsed proof, one-click expansions, and fully expanded proof are three
projections of this same tree. Consequently:

- the collapsed projection states the proof spine with its principal equations;
- each click replaces or augments one node with a coherent mathematical
  subargument, including symbols or equations when they carry the idea; and
- expanding all yields a readable proof at greater granularity, not a list of
  labels, backend identifiers, or formal-expression dumps.

### 10.4 Full concrete-proof refinement

The semantic proof and the concrete proof are two presentations of the same
elaborated declaration.  The semantic proof is the default paper view.  The
frontend's complete re-parented `TacticTree`, including proof-term
decompilation where a source tactic does not expose its children, remains a
second recursive `Explanation` tree.  Replacing the default proof with semantic
prose must never discard this concrete tree.

The theorem proof carries one `withConcreteProof` wrapper.  Its visual control
is a small unlabeled symbol at the right edge; it must not announce an
implementation language or introduce a card, panel, or developer-facing box.
Activating the symbol switches between the semantic and concrete trees.  Both
use the ordinary Massot--Miller replacement, indentation, calculation, and
goal-state vocabulary.

The web renderer imposes no depth bound on the serialized concrete tree.
The global `Expand all` control selects the concrete tree and recursively opens
every replacement and trailer supplied by the frontend; `Collapse all` closes
both trees and restores the semantic paper view.  The local disclosure controls
continue to expand only their semantic or concrete subtree.  Any
defensive bound used while decompiling a malformed or cyclic proof term must
produce an explicit opaque leaf; the HTML layer must never silently truncate
the tree.  `visibleText` continues to project only the semantic branch so
linguistic acceptance tests do not confuse concrete elaboration detail with
the generated paper proof.

### 10.5 Current switching checkpoint

The current switching renderer is the first recursive development slice. It
uses typed proof-plan roles and canonical operands to produce a symbolic
CR18-shaped proof, retains the complete concrete proof as a second recursive
view, assigns checked objects scoped symbols, and projects five local replacement
controls from the same recursive support tree. Its diagnostic JSON retains premise versus
macro-expansion ancestry even though the reader only needs the resulting local
claim hierarchy.

This validates the architecture for switching; it does not establish corpus-
wide completeness. Some connective prose is still realized by domain rule
frames, two low-level switching states deliberately fail closed in the goal
inspector, and CBC, hybrid, reduction, and H-coefficient language acceptance cases
remain.

## 11. Author control

Reusable domain registrations are the primary control mechanism.  Optional
per-declaration or per-proof controls may specify:

- preferred mathematical label or noun;
- real/ideal or other discourse role when genuinely ambiguous;
- proof genre when several checked plans are available;
- salience or collapsed/expanded level;
- aggregation and paragraph boundary;
- preferred citation label; and
- non-semantic reader notes.

Controls attach to semantic nodes or evidence references.  They cannot assert
an unproved proposition, replace a generated proof with arbitrary prose, or
change the formal theorem.

Controlled-language sentence traces may carry stable presentation anchors or
author guidance.  They are not semantic authority and are not required:
ordinary Lean with the same checked evidence must remain fully
informalizable, and equivalent guidance must be expressible outside Verbose
syntax.

## 12. Presentation boundary

The existing `Explanation` document and reader remain suitable for:

- short/detailed replacement;
- calculations;
- nested claims and lists; and
- source highlighting.

The conversion from discourse plan to `Explanation` preserves an internal
mapping from presentation nodes to semantic nodes and evidence references.
That mapping belongs in the semantic report or a developer view, not in
reader-visible labels, tooltips, or trailers. The public document must contain
only reader-oriented mathematical content. A future Verso emitter consumes the
same content/claim tree; Verso is not part of semantic extraction.

Reader-facing payloads must not contain generated proof-step IDs, declaration
paths used only by the backend, unique-name suffixes, tactic states, proof-term
representations, or raw kernel expressions. In particular, expanding the proof
must never reveal artifacts such as `RandomSystems.System...`, `_uniq`,
`Nat.cast`, `Subtype.val`, or synthesized instance names.

The complete concrete tree renders every proposition as mathematical content.
It first asks the selected semantic profile for registered relation and entity
notation.  If the proposition is not registered, an environment-independent
structural printer renders its Lean expression as conservative LaTeX.  This
fallback preserves application, projection, binding, and operator structure
without assigning a guessed cryptographic meaning.  Reader output must never
replace a proposition by a monospaced source fragment merely because the source
module was elaborated without importing presentation attributes.  Exact source
and kernel expressions remain available only in developer provenance.

Proof-valued `let` bindings are rendered as named facts with their checked
propositions; their proof terms must not be printed as mathematical values.

## 13. Validation requirements

### V1. Build and soundness

- All changed Lean modules compile under the pinned toolchain.
- No delivered theorem contains `sorry`, `admit`, or an unintended `sorryAx`.
- Headline system theorems receive a recorded `#print axioms` check.
- Generated JSON parses and the HTML reader loads without console errors.

### V2. Evidence completeness

- Every visible mathematical sentence maps internally to a semantic node ID;
  the ID is not reader-facing content.
- Every semantic assertion has at least one checked evidence reference.
- Reader expansion reaches semantic child claims, while exact formal evidence
  remains available in the semantic report or provenance index.
- The system never silently drops an unrecognized proof obligation.

### V3. Semantic invariance

The test suite must verify that the reader-facing semantic plan is unchanged
under:

1. alpha-renaming `Bad`, `h_real`, `h_ideal`, and all ordinary locals;
2. replacing `rw` by an equivalent `simpa` or `calc` proof;
3. inserting or removing a semantically transparent helper lemma;
4. using two declarations registered with the same proof-rule role; and
5. reordering independent implementation-only hypotheses.

Surface symbols may change only when the renamed object is deliberately shown.
Source-aware elaboration for semantic profiles must use the source module's own
imports. Importing the informalizer, a notation package, or an ontology adapter
into the source before elaboration is forbidden: even a harmless-looking import
may add simp lemmas, instances, or macros and change whether the original proof
elaborates.

Consequently, canonical notation must be recovered from checked structure, not
from source-environment pretty-printer extensions. In particular, query
restrictions and the standard quadratic collision term `q² / (2 |X|)` retain
their typed operands in the canonical AST and render identically whether or not
a notation module was imported by the source project.

### V4. Negative classification

- An unrelated `List A` is never called a transcript solely because it is a
  list.
- An arbitrary predicate named `Bad` is not automatically a bad event.
- An arithmetic theorem is not classified as an indistinguishability theorem.
- A generic equality is not classified as conditional equivalence.
- CR18 conditional equivalence is not rendered as a symmetric game-hop claim.
- Unregistered constants use a reader-safe mathematical fallback when one is
  available and otherwise remain explicit in the developer coverage report.

### V5. Statement quality

The query-count filter is CR18 Definition 3.10's `[q]S`. It is semantically
and typographically distinct from CBC's `\theta_r`, which restricts admissible
messages by their encoded block budget. A renderer must select between these
notations from the registered converter role; a generic "filter" label is not
enough.

For a system-level security theorem, the collapsed statement must identify:

- the compared real and ideal systems;
- the restriction/access model;
- the distance or advantage endpoint; and
- the bound.

Raw universes, decidability dictionaries, coercion instances, and carrier-type
introductions must be absent unless marked mathematically salient.

### V6. Proof-plan quality

For each supported genre, the generated semantic plan must contain the
expected mathematical moves, regardless of source tactic spelling.

For CR18 switching, the minimum plan is:

1. system-level security claim;
2. collision game/condition;
3. conditional equivalence to URP;
4. reduction to blind winning;
5. fixed-schedule collision analysis;
6. birthday bound; and
7. final advantage conclusion.

For CBC, the conditional-equivalence expansion must expose the two source
ideas: distinct terminal round-function inputs on the good event, and uniform
consistent outputs conditioned on that event.

### V7. Corpus-based language review

Generated collapsed prose is reviewed against primary cryptographic sources,
using this rubric:

| Criterion | Pass condition |
| --- | --- |
| Content selection | Foregrounds the security claim and mathematical hops, not Lean plumbing |
| Terminology | Uses the registered domain meaning of systems, games, restrictions, and advantage |
| Rhetorical order | Follows the proof dependency and conventional paper discourse |
| References | Uses stable symbols and unambiguous anaphora |
| Granularity | Collapsed proof states the argument; expansions expose details without repetition |
| Faithfulness | Every assertion has checked evidence and no stronger relation is claimed |

Exact byte-for-byte agreement with a paper is not an acceptance criterion.
The paper is a discourse corpus and semantic reference, not a prose fixture.

### V8. Interaction quality

- The collapsed view states the theorem and proof spine using mathematical
  notation, rather than replacing every mathematical relationship with prose.
- Short and expanded views are projections of the same recursive semantic
  claim node.
- Every individual disclosure adds a coherent mathematical claim, definition,
  or equation; it never adds only an evidence label or backend phrase.
- Expanding all yields a readable mathematical proof without empty controls,
  generated identifiers, declaration paths, kernel terms, or duplicated
  low-level expressions.
- Every displayed formula is assembled from typed semantic operands through
  the mathematical-content and notation layers, not stored as an opaque final
  formula string in a theorem- or proof-shape-specific branch.
- Proof-state checkpoints and proof-depth disclosures are independent:
  `⊕`/`⊖` changes how much of a claim's proof is narrated, while `⬭` selects
  the checked state immediately before a visible proof move.
- The collapsed proof contains exactly one root checkpoint immediately after
  `Proof.`. Checkpoints owned by a detailed claim become visible only when that
  claim is expanded; collapsing it removes those checkpoints and clears any
  selection that is no longer visible.
- Selecting a checkpoint opens a separate proof-state pane. It shows
  humanized mathematical context above a rule and the exact symbolic target
  below it. It never shows declaration paths, proof-step IDs, generated names,
  instance arguments, or kernel expressions.
- A checkpoint is emitted only when both its context and target can be rendered
  safely. Unsupported states fail closed and remain recorded in the internal
  provenance/coverage report rather than leaking diagnostic syntax to readers.
- Mathematical notation has consistent quality across the statement,
  collapsed proof, and every expansion.

#### CBC collapsed-proof acceptance

The CBC page is a stress test of the reusable Random Systems language, not a
separate informalizer.  Its collapsed projection must preserve this causal
spine, regardless of the order of independent `have` declarations in Lean:

1. introduce the block former, real and ideal systems, CBC converter, and
   total-block restriction before the theorem formula;
2. explain that the total-block restriction bounds calls to the underlying
   system and therefore makes the query restriction redundant;
3. introduce the collision game by saying what its MBO records;
4. state that, outside collision, prefix-freeness gives distinct final
   round-function inputs and hence uniform, consistent replies;
5. preserve that statement under the total-block restriction and reduce the
   comparison to blind winning;
6. explain that blindness fixes the message list before replies and that the
   next fresh round-function value is uniform until collision; and
7. apply the collision estimate and substitute it into the reduction.

The collapsed projection must not foreground common-domain conversion,
normalized-PDS presentation, coercion removal, or the equality obtained by
forgetting an MBO.  Those checked steps remain available through semantic
expansion, concrete-proof disclosure, or provenance.  Conversely, terminal
input separation, the uniform consistent output law, and the fixed-list
collision argument are substantive mathematics and must not be expansion-only
details.

For this slice, the executable wording and hole order live in
`LanguageDesign.SurfaceContract`; the CBC theorem presentation and declaration
roles live in `Informalization.Semantics.CBC`; and `Tests.SemanticHtml` checks
both required and forbidden collapsed phrases.  This Markdown section records
the rationale, but is not a second executable contract.

Hover decoration must be a light dotted underline at rest and may darken on
hover or keyboard focus; it must not resemble a solid hyperlink underline.
The proof-state inspector must consume no document width until a state is
selected, and it must disappear again when the selection is cleared.

### V9. Forbidden-pattern gate

The production backend must contain no:

- tests of tactic strings for local names such as `h_ideal` or `h_real`;
- tests of a free variable's displayed name for `Bad`;
- theorem-specific final proof paragraphs;
- byte-for-byte copied paper proof fixtures used as generated output;
- complete proof paragraphs or formulas returned by a theorem- or whole-proof-
  shape branch instead of being composed from typed operands;
- global `List -> transcript` classification; or
- proof refactor whose only purpose is to trigger a prose template; or
- reader-visible evidence labels, generated backend identifiers, or raw kernel
  expressions.

An automated scan enforces the concrete forbidden spellings while code review
enforces the semantic rule.

## 14. Acceptance corpus

The minimum regression corpus is:

1. a neutral theorem such as injective composition;
2. the topology/Rudin shape or an equivalent ontology test;
3. a genuine query-restricted URF/URP switching theorem;
4. CR18 CBC-MAC conditional equivalence and final advantage bound;
5. an H-technique proof with good-ratio and bad-mass obligations;
6. a triangle/hybrid proof;
7. a game-hop agreement-until-bad proof; and
8. a simulator or data-processing reduction.

Each corpus entry stores three independently reviewed artifacts:

- semantic plan/provenance JSON, kept separate from the reader;
- collapsed generated prose; and
- recursive reader expansion tree.

Tests primarily compare semantic plans and invariants.  Surface golden tests
cover deterministic grammar and notation, not a manually substituted proof.

## 15. Genuine switching validation target

The switching example is accepted only when its selected root declaration
contains, directly or through transparent registered notation:

- `PDS.urf`;
- `PDS.urp`;
- the query restriction/filter on both systems;
- `PDS.advFullyDefined` or the agreed equivalent distance endpoint; and
- the birthday bound.

The root must compile and have a clean axiom check.  The scalar switching
ratio and birthday inequalities are supporting leaves, not substitutes for
this theorem.

## 16. Migration plan

### Stage 0: quarantine the failed output-driven slice

- Mark the current switching preview as non-acceptance output.
- Remove local-name and tactic-substring prose triggers.
- Remove domain rules from generic notation modules.
- Re-evaluate proof refactors made solely for the renderer.

### Stage 1: semantic core

- Add evidence references, typed semantic entities, propositions, system
  expressions, and proof-rule roles.
- Add an environment-backed semantic registration mechanism.
- Add neutral registry and fallback tests.

### Stage 2: Random Systems language package

- Register RS objects, relations, and proof rules.
- Add system-expression decoding and notation.
- Add statement planning for security endpoints.

### Stage 3: proof-plan extraction

- Extract applied registered rules and obligations from checked proof
  evidence.
- Implement CR18 CE, H-technique, hybrid, and game-hop plan constructors.
- Add semantic-invariance tests.

### Stage 4: discourse realization

Implemented for the switching slice; corpus-wide language and notation
coverage remains.

- Implement content selection, rhetorical ordering, aggregation, anaphora,
  and expansion policies.
- Add the typed mathematical-content tree and scoped notation/symbol table.
- Build recursive semantic claim trees for collapsed, per-click, and expand-all
  projections.
- Convert discourse plans to `Explanation` while retaining provenance only in
  an internal mapping/report.

### Stage 5: genuine switching vertical slice

- Finish or land the system-level URF/URP theorem.
- Generate and visually inspect its statement, collapsed proof, expansions,
  and goal states.
- Pass all V1--V9 gates.

### Stage 6: CBC vertical slice

- Apply the same generic RS language and CE planner to CBC.
- Add only reusable semantic roles required by the proof.
- Validate against CR18's argument and the checked CBC theorem.

## 17. First vertical-slice definition of done

The first backend milestone is complete when:

1. the genuine URF/URP theorem has a clean Lean build and axiom check;
2. the generated statement identifies URF, URP, query budget, advantage, and
   bound without raw type plumbing;
3. the semantic plan contains the seven CR18 switching moves in V6;
4. renaming locals and changing tactic spelling leave that plan unchanged;
5. formulas in the statement, collapsed proof, and expansions are assembled
   from typed operands under one scoped notation table;
6. every collapsed claim expands recursively to mathematical child claims and
   remains internally traceable to checked evidence;
7. expand-all contains no evidence labels, generated backend identifiers, or
   kernel-expression dumps;
8. no forbidden output trigger remains; and
9. the standalone HTML is visually and interactively inspected in collapsed,
   individual-expansion, and fully expanded states.

Until all nine conditions hold, `preview/switching.html` is a development
fixture rather than a successful informalization of the switching lemma.

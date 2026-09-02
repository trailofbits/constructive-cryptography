# Informalization desiderata

This is the durable design contract for the informalization project. It records
what the system should eventually do, without serving as a progress ledger or
duplicating the implementation detail in [`SPEC.md`](SPEC.md). When the two
documents differ, `SPEC.md` remains the technical authority.

[`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md) expands the ontology, cross-level
bridge relations, occurrence contexts, clause/discourse grammar, and the
CR18 linguistic stress test required to make the generated prose idiomatic.
The independent controlled-language implementation is specified in
[`VERBOSE_SPEC.md`](VERBOSE_SPEC.md).

[`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md) is the
non-regression authority for complete proof passages. Its `Fact NAME:` decision
and switching passage now govern the experimental implementation. Switching is
only the first composition fixture: production promotion remains blocked until
the corpus also covers system and converter definitions, games and probability,
an MR16-track construction proof, and a proof that crosses between construction
and Random Systems registers.

## 1. Foundational contract

- The explanation is derived from checked Lean evidence. It must never assert
  more than the elaborated declaration and proof justify.
- Informalization is compositional: specify how small mathematical concepts and
  relations are understood, then assemble them into claims, arguments, and a
  document.
- The system describes the mathematics, not the syntax of the proof script.
  Tactic names, local identifiers, generated declarations, and pretty-printed
  kernel terms are not a semantic vocabulary.
- Specifications attach to stable declarations, head constructors, relations,
  and argument roles. Unsupported material is retained exactly and handled
  conservatively rather than assigned a guessed meaning.

### 1.1 Source hierarchy and Jost assessment

The repository source hierarchy applies to the language design: Maurer-Renner
2016 is primary, followed by Jost, Liu-Maurer 2020, and Lanzenberger; CR18 is
used only for items in the repository's fallback register and must be marked as
such. A CBC or switching stress test does not make CR18 the ontology owner.

Jost is not merely optional background here. In Thesis Section 2.2 (printed
pp. 15-20), specifications are sets of resources, resources and converters
form the system algebra, and a protocol constructs one specification from
another when its action maps the source specification into the target. Thus
Jost requires the specification/resource/converter/construction structure that
the cross-level ontology exposes; it also confirms that the Random Systems
register and the construction register must be able to meet in one argument.
It does not justify replacing the MR16-track construction model with a
CBC-specific or tactic-specific presentation.

## 2. Relationship to Kyle's architecture

This project does not merely reproduce or modify Kyle Miller's InformalLean
architecture. It keeps his Lean frontend, ontology/explainer, structured
`Explanation`, and interactive-reader ideas, while inserting a semantic middle
layer for domain-sensitive mathematical proofs.

```text
Kyle's architecture:
Lean proof -> tactic/entity/proposition explainers -> Explanation -> webapp

This project's extension:
Lean proof -> checked evidence -> typed semantics -> mathematical proof plan
           -> semantic compression -> discourse -> Explanation -> reader
```

The inserted layers are our design, not interfaces specified by Kyle. In
particular, the checked evidence graph, canonical cryptographic AST, proof
genres, operand-bearing fingerprints, fail-closed semantic compression, and
routine-evidence coverage is a project extension.

Kyle's ontology must remain visible as its own architectural component. It
models common mathematical entities, concepts, properties, and relations and
supplies vocabulary to entity and proposition explainers. It is a cross-cutting
service rather than merely one more proof-processing step. Our canonical
cryptographic semantics extends this concern but must not be presented as
Kyle's ontology interface.

This changes the generated result in useful but costly ways:

- proof-script refactorings can preserve the same mathematical explanation;
- collapsed prose can follow the paper-level argument instead of narrating
  tactics; and
- unsupported mathematics can be retained and exposed safely instead of being
  assigned guessed prose.

The cost is a need for domain registries, canonical semantic models, and
evidence-coverage checks. Until those are complete, coverage and expansion may
be narrower than in a direct tactic-describer approach. A faulty or incomplete
semantic bridge could also hide evidence, so coverage must be established
before compression.

Design discussions and documentation must distinguish among:

- **Kyle:** directly stated or implemented in Kyle's architecture;
- **current implementation:** behavior verified in this package; and
- **proposed extension:** a requirement or design choice introduced here.

Do not attribute a project extension to Kyle without a precise source.

### 2.1 Independent modules with shared language design

`/verbose` concerns how Lean is written; `/informalization` concerns how a
checked development is presented.  They are independent modules that share a
neutral language design: ontology identifiers, mathematical rule identities,
argument roles, relation frames, register/discourse vocabulary, and an
annotation schema.  `/verbose` uses it to parse rigid Random Systems CNL and
lower each sentence to a deterministic proof step.  `/informalization` uses it
to recognize checked mathematics and plan reader prose.

The required interaction is ordinary elaborated Lean.  Optional presentation
metadata may pass between them through the shared annotation schema, but the
same facility must work for handwritten Lean.  The informalizer must not
depend on Verbose syntax or trust a source sentence as semantic evidence.

### 2.2 Optional presentation guidance

Authors may guide the presentation through comments, labels, and options
attached to stable semantic anchors.  Layout and wording hints may influence
paragraphs, registered terminology, safe reference forms, licensed
connectives, and expansion defaults without changing the proof or semantic
fingerprint.  Proposed semantic labels must be validated against checked
evidence.  Arbitrary prose remains an explicitly marked author note and never
replaces compiler-justified mathematics.  Stale or incompatible guidance must
fail visibly rather than silently changing the explanation.

## 3. Conceptual layers

1. **Lean frontend:** elaborate the source declaration and retain its checked
   expression, proof term, metadata, and information tree.
2. **Evidence graph:** recover theorem applications, proof-valued premises,
   local obligations, and fallback regions without losing provenance.
3. **Ontology and domain vocabulary:** map recognized Lean concepts to stable
   mathematical entities, properties, relations, and linguistic information.
   In Kyle's architecture this directly supports entity and proposition
   explainers; in this project it is also consumed by canonical semantics and
   realization.
4. **Canonical semantics:** decode expressions into typed mathematical objects,
   relations, quantities, and claims.
5. **Proof plan:** organize the evidence into the mathematical dependency tree
   and recognize a known argument form only when its checked structure warrants
   that recognition.
6. **Semantic compression:** absorb routine proof mechanics while preserving
   every substantive mathematical step.
7. **Discourse:** select the claims that belong in the collapsed argument and
   order them as mathematical prose.
8. **Explanation document:** realize the same recursive claim tree as text,
   formulas, local expansions, and optional checked proof-state checkpoints.
9. **Interactive reader:** project that document into collapsed, selectively
   expanded, and fully expanded views.

Each layer has one job. In particular, the reader does not invent explanations,
and the prose layer does not infer semantics from tactic spellings.

## 4. Inspectability and disclosure

- There should be no arbitrary reader-imposed depth limit. A meaningful claim
  may be expanded recursively for as long as the backend has a checked semantic
  decomposition.
- The currently visible expansion depth is therefore not the intended limit.
  It reflects which semantic children have been generated, not a fundamental
  restriction of the interaction model.
- Semantic disclosure and proof-state inspection are separate controls. One
  explains *why the mathematical claim follows*; the other shows the checked
  local context and target at a selected point.
- Every checked obligation must end in one of three reader contracts:
  1. a substantive, recursively expandable mathematical claim;
  2. a checked routine-evidence coverage summary that is compact by default; or
  3. a safe symbolic fallback that does not guess domain meaning.
- Exact expressions and evidence identifiers remain available in a developer
  diagnostic report. They must not leak into ordinary reader prose.
- Broad or expensive decompositions may eventually be produced lazily when the
  reader asks for them. Laziness may change when work is performed, but not the
  semantic result.

Thus “inspect everything” means that all meaningful mathematical structure and
all evidence coverage can be audited. It does not mean dumping kernel syntax or
turning every elaborator operation into prose.

## 5. Routine-proof compression

Compression must be fail-closed and justified by checked goal transformation,
not by recognizing `simp`, `rw`, `omega`, `ring`, `nlinarith`, or any other
tactic name.

This is distinct from Verbose proof synthesis. A bounded Verbose registry may
construct a missing routine proof; the informalizer only classifies evidence
that Lean has already checked. Neither registry authorizes the other, and they
have separate soundness, coverage, and resource-bound tests.

Likely routine classes are:

- definitional rewriting, coercion removal, and normalization;
- singleton and specification bookkeeping;
- `Subtype`, support, and probability-distribution packaging;
- propositional normalization; and
- elementary arithmetic closure once the mathematical inequality has already
  been exposed.

The full evidence remains internally accounted for. If the classifier cannot
prove that a region is routine, that region stays visible or falls back safely.
A mathematically meaningful change of bound must remain visible even when its
last arithmetic verification is routine.

## 6. CBC semantic target

The current integration target is the Random Systems distance theorem
`CBCMAC.cbc_randomness_expander` in the sibling `cbc-mac-cc` project. Its
canonical vocabulary must cover:

- converter attachment and serial converter application;
- CBC and the block-restriction converter `theta_r`;
- the restricted URF and ideal VIL-URF systems;
- the CBC collision game, bad condition, and collision mass; and
- Random-Systems distance, distinguishing advantage, and blind winning.

A later Constructive Cryptography consumer may place a construction judgment
above this theorem. That layer belongs to the reusable CC ontology; it must not
be baked into the CBC profile or fabricated when the selected root is only a
Random Systems distance statement.

The source dialect is part of the contract.  In CR18 a game is *obtained by
enhancing a system with an MBO*; the underlying system is obtained by
*ignoring the MBO*.  “Monitoring a system for collisions” is not an allowed
paraphrase: it conflates the collision predicate, the MBO, the game
construction, and the event that the MBO has value `1`.  Every reader-facing
proof rule must therefore carry a source attestation (or state only an exact
checked Lean relation), and an unattested rule must fail catalog validation.

The collapsed/expandable proof spine should recover the CR18 argument:

1. define the collision game and bad condition;
2. show that outside collision, distinct messages reach distinct final
   round-function inputs;
3. conclude the uniform consistent output law under that condition;
4. preserve the statement under `theta_r`;
5. reduce the distinguishing advantage to blind winning;
6. fix the non-adaptive message list;
7. apply the CBC collision bound; and
8. conclude the distance bound.

The results represented by `not_cbcBad_implies_uniform_outputs` and
`mass_cbcBad_le` are substantive semantic nodes, not routine proof noise. Their
internal expansions may be optional, but their mathematical roles must be
visible. Stable public declarations should expose these proof boundaries to
the semantic registry; generated or private implementation names are not a
sound integration seam.

The selected endpoint is `CBCMAC.cbc_randomness_expander`. The application
profile is deliberately thin: reusable Random Systems entities and rules must
remain available to every project, while only CBC-specific vocabulary and
lemmas are added here.

## 7. Evidence accounting and semantic identity

- Every proof wrapper, premise, macro edge, and unsupported region must be
  accounted for before compression. A fallback node with its own payload must
  not disappear merely because it has children.
- The internal report should contain a first-class evidence-coverage map connecting
  each semantic node or compression entry to the checked evidence it covers.
- A semantic fingerprint must retain alpha-normalized canonical operands and
  the root claim: systems, converters, specifications, budgets, events, and
  bounds. Tree shape and generic roles alone are insufficient.
- Source refactorings that preserve the argument should preserve the semantic
  output; changing a mathematical operand should change it.

## 8. Required invariances

Equivalent checked proofs should yield the same semantic result under:

- alpha-renaming and registered declaration aliases;
- `exact` versus `apply`;
- `rw` versus `simpa` versus `calc`;
- an inline derivation versus a named helper;
- reordering independent premises; and
- elementary automation versus an explicit routine derivation.

These tests compare operand-bearing semantic fingerprints and reader content,
not only prose strings or proof-tree shape.

## 9. Acceptance condition

The CBC slice is ready only when:

- the standalone package and the target CBC source build;
- the construction root and every substantive proof-spine node are present and
  reachable in semantic JSON and HTML;
- collapsed, individually expanded, and expand-all views are projections of
  the same recursive explanation;
- routine evidence is fully covered but unobtrusive;
- unsupported material fails safely;
- invariance and semantic-change tests both pass;
- browser inspection is coherent in light and dark themes; and
- the important public endpoints have an acceptable axiom report, with no
  `sorry`, `admit`, or `sorryAx`.

## 10. Suggested dependency order

1. Make evidence coverage and operand-bearing fingerprints fail-closed.
2. Complete canonical construction and CBC vocabulary.
3. Expose stable CBC declarations and register their semantic roles.
4. Add checked routine-proof classification and compression.
5. Realize the recursive CBC discourse and reader expansion.
6. Add the complete invariance, artifact, browser, build, and axiom gates.

## Sources

- Kyle Miller, [*Informalizing formal mathematics*](https://kmill.github.io/informalization/icerm_talk.pdf).
- [`SPEC.md`](SPEC.md), the detailed architecture and validation specification.
- [`CR18_LN.pdf`](../../random-systems/papers/CR18_LN.pdf), especially the CBC
  argument around Theorem 6.1. Its use remains subject to the repository's
  CR18-fallback provenance rules.

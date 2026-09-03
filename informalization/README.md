# Generic informalization backend

This directory is a standalone Lean package for turning checked declarations
from **any Lake workspace** into the structured `Explanation` document used by
the Massot–Miller InformalLean interface.  The generic core has no dependency
on AbstractCryptography or Random Systems; domain adapters provide the
additional ontology and proof genres needed for cryptography.

[`SLIDES.md`](SLIDES.md) is the self-contained Verso slide-authoring guide for
the Swiss Crypto Day deck, including syntax, custom directives, TikZ, styling,
build commands, and visual verification.

[`SPEC.md`](SPEC.md) is the authoritative architecture, trust, and validation
specification.  In particular, the intended production pipeline is semantic:
it does not select prose from tactic spellings, local variable names, or a
manually synchronized informal proof.

[`DESIDERATA.md`](DESIDERATA.md) records the shorter, durable design contract
for compositional semantics, inspectability, routine-proof compression, and the
CBC vertical slice. It is intentionally not a progress ledger.

[`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md) is the detailed ontology and
linguistic architecture: it inventories formal, AC/CC, Random Systems, game,
probability, and CBC entities; specifies cross-register inference rules; and
stress-tests those rules against the CR18 CBC proof as a linguistic corpus.

[`VERBOSE_SPEC.md`](VERBOSE_SPEC.md) is the implementation contract for the
independent `/verbose` authoring frontend. It shares the neutral language
design with this informalizer, lowers rigid sentences to checked deterministic
proof steps, and specifies its source-accurate acceptance suite. CBC
informalization is now a separate application overlay; it does not depend on a
CBC proof having been written through the Verbose frontend.
Its canonical surface is not duplicated in prose: the typed
`LanguageDesign.SurfaceContract.forms` catalog is authoritative, and the
specification's displayed surface block is a checked generated projection.

The switching passage in
[`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md) is the active
experimental non-regression baseline. Its implementation does not promote the
whole frontend to production: the breadth corpus for systems, converters,
games, MR16 constructions, and cross-register proofs is still required.

The boundary is deliberate:

```text
external Lean source + declaration names
  → Lake setup for that source's own workspace
  → Lean frontend elaboration with retained InfoTrees
  → checked evidence graph (InfoTrees + proof terms)
  → typed mathematical entities, relations, and applied rules
  → domain proof plan
  → discourse planning and realization
  → public Explanation JSON
  → optional HTML reader
```

## Verbose authoring frontend

The same Lake package now contains an independent `Verbose` library. Its path
dependency points at the live sibling `abstract-crypto` checkout, so it follows
that evolving library rather than a copied worktree. A source opts into the
grammar explicitly:

```lean
import Verbose
import Verbose.English.Statements
open scoped CryptoVerbose

Theorem queryBudgetReflexive "A query budget bounds itself"
  Given:
    Let q ∈ ℕ
  Conclusion:
    q ≤ q
  Proof:
    exact le_rfl
  QED
```

`Fact NAME:` is available only around an assertion whose descriptor has a
checked isolated-claim constructor. In the accepted switching fixture those
are the conditional law and the MBO-forgetting identity; it is not a spelling
for arbitrary `have`.

Every successful sentence is executed transactionally, checked against a
shared `RuleSchema`, checked again against its declared goal transition, and
recorded as a typed custom InfoTree event. The sentence catalog is a persistent
environment registry; canonical renderings are parser-checked, and exact
suggestions are dry-elaborated before they are shown. Reader notes such as
`proof noted "why this fact matters"` and `With presentation ... in ...` are
retained as presentation guidance but never become proof evidence.

Backends are capabilities generated from one fixed function head, so an
elaborator cannot label an arbitrary closure as a trusted backend. `Fact`
events are privately authenticated with a fresh envelope nonce; their public
payloads can be inspected but cannot be replayed as authorization. Routine
receipts are accepted only as direct premises of a registered root proof
combinator.

The implementation includes parser/backend prototypes for the small structural kernel; exact,
metric, filtered, relaxed, serial, parallel, simulator, and context AC
workflows; distinct PDS and game relations; typed common-domain and
query-indexed carrier schemas; domain and query filtering;
conditional-equivalence reduction to blind winning; the current common-domain
`edist` data-processing rule; reusable transformation,
collision-mass, and H-coefficient proof-spine steps. The public
catalog and public umbrella import are deliberately narrower: only
source-licensed generic forms are discoverable. Pending Random Systems parser
modules require an explicit module import and still fail at elaboration unless
an exact declaration/profile license applies; checked-library metadata alone
cannot authorize their English. Application-only or pending frames remain
absent from help and generic canonical rendering. The application-scoped
rewrite form likewise lives in `Verbose.English.Rewriting` and is not exported
by `import Verbose`. The rejected multi-act fixed-schedule clause
has no public syntax. The genuine
URF/URP switching theorem compiles as a complete frontend proof. Its routine
nonnegativity and equal-weight premises are discharged by a fixed, fail-closed
registry and retained as typed proof receipts reachable from the assertion's
checked proof root rather than as reader-facing facts. Contextual
assistance is available through `crypto_help`, `crypto_help hypothesis`,
`crypto_suggest`, `#crypto_verbose_sentences`, and
`#print_crypto_verbose_config`.

The reusable Random Systems catalog contains no CBC declaration. CBC is an
explicit overlay selected by `--profile=random-systems-cbc`; its executable
contract is [`Informalization/Semantics/CBC.lean`](Informalization/Semantics/CBC.lean).
The project imports the `cbc-mac-cc` package, a git dependency pinned in
`lake-manifest.json`, and tests the
public `CBCMAC.cbc_randomness_expander` theorem. The reusable profile already
decodes its Random Systems distance, converter application and composition,
conditional equivalence, blind game, and generic reductions. The thin CBC
extension adds only CBC, its block restriction and query limit, the collision
game, the real and ideal named systems, and CBC-specific mathematical lemmas.
It also supplies the paper notation `CBC[B]` and `θ[B,q]` as profile data;
the shared renderer contains no CBC declaration-name cases.

The backend currently implements the pipeline through interactive HTML for the
Random Systems profile:
declaration metadata is recovered into a compositional statement graph,
registered proof applications and all proof-valued premises are retained as a
checked evidence tree, and a recursive canonical proof plan plus a semantic
fingerprint that erases source-specific evidence are derived from it. The
fingerprint is tested for alpha-renaming, registered aliases, `exact`/`apply`,
`rw`/`simpa`/`calc`, local-`have`, independent routine-premise reordering, and
explicit-versus-automated routine derivations. A typed discourse planner now
selects and orders proof moves, preserves premise and bounded-macro edges as a
recursive support forest, and realizes a cryptographic proof with symbolic
Random-Systems notation. A generic bridge converts that document to
Massot–Miller `Explanation` nodes: the collapsed proof contains the paper-level
argument, while each local expansion reveals only that claim's recursive
semantic subargument. Proof-state
checkpoints are a separate interaction: the root checkpoint is visible in the
collapsed proof, and expanding a claim reveals the checked states for its
internal moves. Selecting one opens a Miller-style context/goal inspector. A
small unlabeled symbol at the right of the proof switches to the complete
concrete proof tree captured from elaboration. That tree uses the same recursive
reader vocabulary and has no additional HTML depth limit; the global `Expand
all` control selects that tree and reaches every supplied concrete node, while
`Collapse all` restores the paper view. The diagnostic report still carries the stable
evidence graph and identifiers used to construct the semantic view.

This is not yet the completed corpus-wide realization architecture. The switching
slice now decodes canonical claims, systems, games, conditions, non-proof rule
operands, and proof obligations, and its displayed formulas are assembled from
those typed values under a scoped symbol table rather than selected by a
theorem-shaped string table. Registered CBC formula schemas retain the exact
proved proposition and typed operands for attachment, conditional-product,
terminal-input, call-site-walk, collision-mass, and scalar-closure notation.
Application-specific attachment equations are not grouped by a generic
theorem-name convention; the current common-domain rule is direct `edist`
non-expansion. Collapsed, per-click, and expand-all views now
come from the same recursive claim tree. The next backend layer must generalize
these content and notation rules across the acceptance corpus and extend safe
goal rendering to currently unsupported proof leaves. The acceptance gates for
that work are in [`SPEC.md`](SPEC.md).

The existing tactic describers and direct English handlers are retained only
as an internal checked fallback for declarations with no semantic plan.
Unrecognized expressions are not assigned a guessed cryptographic meaning.
They reach the reader only when the notation layer can render safe mathematical
content; raw kernel terms remain in the developer-facing diagnostic path.

## Build and test

From this directory:

```sh
lake build
lake run provenance
lake run test
```

The live CBC source gate is also available separately:

```sh
lake exe cbcExternalTests
lake exe cbcIntegrationTests
```

The ordinary semantic contract imports the genuine
`CBCMAC.cbc_randomness_expander` declaration. The source gate additionally
re-elaborates `CBCMAC/Main.lean` under the owning project's Lake setup so that
source ranges, tactic checkpoints, and goal states remain available. The
integration executable additionally builds the semantic discourse and
standalone interactive reader, and rejects raw CBC namespaces on its prose
surface. Set
`INFORMALIZATION_CBC_ROOT` only to override the materialized dependency under
`.lake/packages/cbc-mac-cc`.

## Swiss Crypto Day presentation

The Verso/reveal.js deck now lives in [`slides/`](slides/). Its proof slide
embeds the generated public explanation document as a native Verso block and
mounts it with the same renderer as the standalone reader. It contains no
copied CBC proof and no hand-authored substitute proof tree. Slide selection,
speaker notes, the ToB theme, and the CBC construction diagram remain
presentation assets.

For visual work against the existing reader artifact:

```sh
cd slides
lake exe swiss-crypto-day
```

For a presentation build, run the fail-closed end-to-end command:

```sh
./scripts/build-swiss-crypto-day.sh
```

It first checks the live downstream theorem, regenerates all CBC reader
artifacts, and only then builds the deck. If the CBC proof is incomplete, the
command stops without replacing checked evidence with authored slide content.

For live work on either the proof presentation or the deck, run:

```sh
./scripts/watch-swiss-crypto-day.sh --serve --port 8766
```

The watcher distinguishes dependency classes. A change to `cbc-mac-cc`,
`abstract-crypto`, the semantic compiler, or the shared reader regenerates the
informalization and then the deck. A change confined to the Verso sources,
styles, or TikZ rebuilds only the deck. Successful builds update a localhost
reload stamp; failed builds retain the last valid page and the watcher remains
active. The standalone reader and the proof slide use the same reload
mechanism.

`lake run provenance` verifies that this package, the enclosing library
checkout, and the `cbc-mac-cc` dependency use the same Lean toolchain, then
reports the library checkout, its commit, and its clean/dirty state. `lake run test` performs the same gate before
building either frontend.

The test suite includes neutral-fallback and domain-separation checks, catalog
and semantic-graph checks, negative root classification, checked proof-evidence
extraction, distinct proof-genre classification, and semantic-fingerprint
tests for alpha-renaming, registered aliases, `exact`/`apply`,
`rw`/`simpa`/`calc`, inline/named helpers, independent routine-premise
reordering, and explicit/automated routine proofs. The complete corpus gates in
`SPEC.md` are still larger than the implemented suite.

## Command line

```sh
lake exe informalize \
  /absolute/path/to/Project/Proof.lean \
  Project.final_theorem \
  --lake-root=/absolute/path/to/Project \
  --semantic-json=/tmp/proof-semantics.json \
  --json=/tmp/proof.json \
  --html=/tmp/proof.html \
  --profile=random-systems
```

`--html` produces a standalone file with the renderer, CSS, and explanation
data embedded. It also writes extractable `massot-miller.css` and
`massot-miller.js` sidecars. Other controls are shown by `lake exe informalize`.
The default profile is domain-neutral. `--profile=random-systems` selects the
reusable typed Random Systems catalog and uses semantic discourse for both
public JSON and HTML. `--profile=random-systems-cbc` adds the explicit CBC
application overlay. Both profiles use a reader-safe fallback for unsupported
or linguistically unattested declarations, with exact checked evidence
retained only in diagnostics.  Proposition rendering first uses the selected
semantic profile and then a conservative structural Lean-to-LaTeX printer, so
an unregistered expression remains proportional mathematical notation rather
than becoming an oversized source-code box.  This works even when the source
proof is deliberately elaborated without presentation imports. The
rejected direct-English prototype is available only as
`--profile=random-systems-legacy`; its output is not an acceptance result.

`--semantic-json` exercises the new typed path.  It reports the recovered
semantic root, security genre, compositional entity graph, argument roles, and
formal provenance, together with classified proof-plan steps, their recursive
support forest, and retained fallback evidence counts. It also includes the
role-driven discourse realization, with top-level sentences, recursive details,
support origins, and internal evidence references. It is the developer-facing
diagnostic companion to the interactive HTML output, not reader content.

The repository's genuine integration target is
[`RandomSystems.Switching.urf_urp_switching`](../RandomSystems/Technique/Switching.lean#L391),
an internal `abstract-crypto` theorem comparing query-restricted URF and URP
systems at the `PDS.advFullyDefined` endpoint. Its generated diagnostic report
is [`preview/switching.semantic.json`](preview/switching.semantic.json). The
report recovers the system-level statement and classifies the checked proof as
the conditional-equivalence/blind-winning route. Its checked plan exposes
exact forgetting, the filtered and base collision-conditional-equivalence
steps, reduction to blind winning, an arbitrary non-adaptive schedule,
collision counting, and the birthday bound. The CE and blind-winning branches
are rendered as independently expandable recursive mathematical arguments.

## Domain extension points

The generic fallback can mechanically run against a finished CBC proof, but it
is not by itself enough to produce Miller-quality cryptographic prose. The
required extension points and acceptance criteria are specified in
[`SPEC.md`](SPEC.md). The typed path uses a fully qualified declaration catalog
to supply entity, system, converter, quantity, relation, argument, salience,
and proof-rule roles. Unknown declarations retain exact checked fallback
evidence internally instead of receiving a guessed meaning.

The explicitly selected CBC application overlay records only CBC-specific
systems, converters, games, conditions, and lemma roles. Distance, advantage,
restriction application, conditional equivalence, blind winning,
non-adaptive reduction, and common-domain data processing remain in the
reusable Random Systems layer. Checked helper bodies are
traversed only inside an explicitly expanded public rule and only within that
rule's source module; private helper identities never become semantic keys.
The genuine distance root is accepted by both the imported contract and the
source-aware semantic gate. This
does not manufacture prose for private proof helpers: only public declarations
with exact profile entries can introduce CBC-specific semantic nodes, and
unlicensed proof material remains checked fallback content.

The quarantined legacy renderer also exposes two lower-level extension points:

- `English.Config` adds ontology handlers and proposition renderers for domain
  concepts such as random systems, converters, conditional equivalence, and
  collision events.
- `Describe.documentWith` accepts a priority-ordered tactic-describer registry.
  Application describers can be placed before `Describe.defaultRegistry` while
  retaining the generic proof-term fallback.

Presentation-specific wording copied from a paper, slide selection, and Verso
layout do not belong in this package. They consume its semantic/document
output.

`examples/SwitchingProof.lean` remains an arithmetic unit fixture; it is not
the integration target and must not be presented as the URF/URP theorem.

## Modules

- `MassotMiller/InfoTree.lean`: external source elaboration and exact InfoTree
  capture.
- `MassotMiller/Decompiler.lean`: checked proof-term fallback.
- `MassotMiller/Ontology.lean` and `English.lean`: configurable linguistic
  rendering.
- `MassotMiller/Topology.lean`: optional Rudin/topology vocabulary, kept out of
  the domain-neutral default registry.
- `MassotMiller/Describe.lean`: hierarchical explanation generation.
- `MassotMiller.lean`: public document/JSON schema.
- `MassotMillerWeb.lean`: inert HTML shell and local renderer assets.
- `Semantics/IR.lean`: prose-free typed semantic nodes, argument edges, and
  exact expression/declaration provenance.
- `Semantics/Registry.lean`: persistent and profile-owned declaration catalogs,
  signature validation, typed recovery, and compositional graph construction.
- `Semantics/Canonical.lean`: domain-neutral operand-bearing systems, games,
  conditions, bounds, claims, rule applications, operands, and obligations.
- `Semantics/CanonicalProof.lean`: complete recursive canonical proofs with
  stable premise, macro-expansion, and fallback edges.
- `Semantics/CanonicalRandomSystems.lean`: the reusable Random Systems decoder
  and the separately selected CBC decoder overlay.
- `Semantics/RandomSystems.lean`: the reusable `abstract-crypto` Random Systems
  catalog plus an explicit CBC catalog overlay; neither contains English templates.
- `Semantics/Validation.lean`: system-level security-root classification.
- `Semantics/ProofEvidence.lean`: fully applied theorem telescopes, recursive
  proof-premise evidence, and exact fallback regions.
- `Semantics/Plan.lean`: distinct crypto proof genres, recursive support
  forests, compatibility step views, and semantic fingerprints.
- `Semantics/Discourse.lean`: paper-level move selection, typed system
  descriptions, hierarchy, and evidence references.
- `Semantics/Realize.lean`: role-driven cryptographic prose, canonical
  mathematical-content rendering, recursive support ancestry, and compact
  semantic JSON.
- `Semantics/Symbols.lean`: capture-avoiding scoped names for checked semantic
  objects such as query budgets, queried sets, and counting parameters.
- `Semantics/GoalState.lean`: fail-closed projection of checked local contexts
  and targets into reader-safe Miller-style proof-state checkpoints.
- `Semantics/Explanation.lean`: generic conversion of realized discourse to
  interactive Massot–Miller replacements, semantic details, and proof-state
  markers while retaining the complete concrete proof as a second recursive
  view.
- `Semantics/Report.lean`: machine-readable statement graph and proof-plan
  report, including the first semantic discourse realization.
- `ExprLatex.lean`: environment-independent structural LaTeX fallback for
  checked expressions not handled by a semantic profile.
- `LeanTeX/RandomSystemsSyntax.lean`: domain notation for systems, query
  restriction, distinguishing advantage, and finite-alphabet bounds.
- `CLI.lean`: domain-neutral external-workspace command.

See [`preview/README.md`](preview/README.md) before opening generated artifacts.

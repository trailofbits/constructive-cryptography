# Verbose authoring layer specification

> **Experimental implementation baseline.** The named-assertion decision is
> fixed as `Fact NAME:` around one registered assertion. The switching passage
> in [`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md) is the
> current whole-proof regression fixture. The breadth gate still blocks a
> production language claim and all pending definition frames.

This document explains the implementation contract for the `/verbose` library. It
specifies a controlled, paper-facing way to write Lean proofs about Abstract
Cryptography, Constructive Cryptography, and Random Systems.  It is deliberately
separate from [`SPEC.md`](SPEC.md), which specifies the `/informalization`
pipeline, and from [`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md), which owns the
ontology and linguistic design shared by both libraries.

Executable surface requirements live in the typed value
`LanguageDesign.SurfaceContract.forms`. The grammar, ontology registry,
lowering fixtures, renderer, and generated block below are checked against
that value. Editing prose elsewhere in this document does not change the
language; a surface change begins by changing the Lean contract and then
making all conformance gates pass.

`LanguageDesign/Corpus.lean` and the sentence registry remain implementation
metadata rather than independent linguistic authority. `Fact NAME:` is a project-controlled
composition of Massot's named-claim layout with a domain assertion; the removed
generic `structuralNamedFact` rule is not a substitute for that assertion.

<!-- GENERATED_VERBOSE_SURFACE_BEGIN -->
This block is generated from `LanguageDesign.SurfaceContract.forms`; edit the Lean contract, not this projection.
```text
Let NAME ∈ ℕ
Let NAME be the system SYSTEM
Let NAME be the MBO given by ASSIGNMENT, which is set on a query history exactly when two distinct queries in that history receive the same answer, as shown by PROOF
Fact NAME: ASSERTION by PROOF
```
<!-- GENERATED_VERBOSE_SURFACE_END -->

### Executability invariant

A canonical surface change is incomplete until the following checks agree:

1. the typed `SurfaceContract.Form` changes;
2. its parser witness parses in the declared grammar context;
3. its sentence owner, bindings, operands, and ontology concepts equal the
   registered `SentenceDescriptor`;
4. a complete checked fixture emits the declared rule in its lowering trace;
5. canonical rendering is produced through the contract constructor; and
6. this generated projection is current.

`tests/VerboseTests/SpecConformance.lean` checks items 2, 3, and 6 by iterating
the contract value. The rendering and complete-passage tests check items 4 and
5. Negative fixtures retain superseded syntax so accidental backward drift is
also visible. Thus the Markdown is reviewable documentation, not a second
grammar specification that can silently diverge from Lean.

The complete file also has a Lean-side review digest. Any edit outside the
generated block fails conformance until its implementation impact has been
reviewed and the digest is deliberately renewed. The digest is only a change
detector; executable surface meaning remains in the typed contract above.

The intended dependency shape is:

```text
                         LanguageDesign
                    ontology, rules, roles
                         /             \
                    Verbose       Informalization
                       |                 ^
                       v                 |
                  checked Lean ----------
```

Verbose affects how a proof is authored.  Informalization affects how any
checked proof is presented.  Neither is an implementation layer of the other,
and no byte-for-byte equality of their prose is required.

Normative words such as **must**, **should**, and **may** describe the intended
implementation.  Sentence forms marked **existing** are already present in
`AbstractCryptography.Tactics.ControlledNaturalLanguage`; forms marked
**required** belong to the first complete Random Systems implementation; forms
marked **later** are part of the architecture but must not be exposed before a
deterministic backend and a representative proof exist.

These implementation-status labels do not license public English. A form
marked **pending-attestation** may be retained as migration input or design
evidence, but cannot be emitted, suggested, or imported by the public frontend
until its own predicate frame has an exact source locator.

No implementation yet conforms to this complete specification. The AC
repository supplies a valuable first controlled-language slice; the sibling
Random Systems repository supplies experimental Condition-C, H-coefficient,
and construction forms. Both are migration inputs. In particular, there is no
complete family of deterministic `rs_*` proof backends covering the semantic
catalog below. The implemented switching slice supplies only its exact
relations, comparison, blind-winning bound, and three bounded routine closers.

Section 6 of [`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md) is normative for the
mathematical grammar.  Every public Verbose sentence must instantiate one of
its indexed entity, relation, definition, or inference schemas.  This document
specifies the rigid Lean-facing spelling and lowering contract; it may narrow
the shared grammar, but it may not invent a local ontology or merge distinctions
that the shared grammar preserves.

## 1. Product contract

The product is a rigid Lean frontend whose successful files read like a
mathematical proof and whose failures teach the author what mathematical step
is expected.  It is not a natural-language parser and it is not a prose
generator.

The core promises are:

1. Every controlled sentence denotes one explicit mathematical act.
2. Every sentence lowers to one deterministic, independently testable proof
   backend.
3. Lean's kernel remains the only authority for correctness.
4. Non-canonical cryptographic choices remain explicit in source: in
   particular the ideal system, simulator, intermediate system, restriction,
   reveal, bad event, coupling, schedule, and proof route.
5. Ordinary Lean may be used before, between, or inside controlled sentences.
6. Opening the language scope must not make common mathematical words unusable
   as identifiers.
7. Unsupported or ambiguous situations fail with a local diagnostic; they do
   not trigger broad proof search.
8. The author can ask for relevant, copyable sentence suggestions without
   surrendering the semantic choices of the proof.
9. A sentence never states an obligation as proved when that obligation is
   merely created as a new goal.

“Comprehensive” means that the recurring *substantive proof moves* in the
acceptance corpus have a coherent frontend.  It does not mean manufacturing an
English synonym for every Lean tactic.  In particular, ordinary `have`,
`show`, `calc`, `cases`, induction, local definitions, and term proofs remain
available and are often already the clearest notation.

### 1.1 Intended users

The first users are authors who know Lean and the Random Systems development.
They should not need metaprogramming knowledge or memorized backend tactic
names.  A reader who knows the mathematics but little Lean should still be
able to follow the proof spine, while recognizing embedded Lean propositions
and terms as mathematical notation.

### 1.2 Non-goals

Verbose is not:

- free-form English;
- an automatic proof search language;
- a second mathematical API competing with theorems and deterministic
  `ac_*`, `cc_*`, or `rs_*` backends;
- a way to hide the selection of a simulator, bad event, coupling, hybrid, or
  intermediate resource;
- a requirement that whole declarations use controlled syntax;
- a tactic-to-prose translation layer; or
- evidence that the informalizer may trust without inspecting checked Lean.

## 2. Source principles retained from Verbose Lean

Patrick Massot's Verbose Lean supplies the following design lessons:

- separate language-independent proof operations from language-specific
  syntax and messages;
- distinguish bound objects, hypotheses, claims, and goals in the grammar;
- support forward reasoning, backward reasoning, witness introduction, and
  explicit goal reminders;
- make risky or creative proof decisions visible while automating only the
  routine steps a paper normally omits;
- offer contextual help and editor suggestions using typed syntax objects;
- make configuration explicit and inspectable; and
- treat a posteriori informalization as a separate problem.

This project changes the audience and domain.  Massot's teaching grammar is a
source of interaction principles, not a vocabulary to copy indiscriminately.
The crypto wording must be attested in the Maurer-style corpus and evaluated
inside complete AC/CC/RS proofs.

## 3. Library architecture

The sibling Lake package should expose these logical libraries:

```text
LanguageDesign
  Ontology             stable concept and relation identifiers
  Rules                mathematical rule identifiers and premise roles
  Grammar              predicate frames and discourse vocabulary
  Annotations          proof-independent presentation hints

Verbose
  Core                  intents, references, goal effects, events, registry API
  English.Core          shared English fragments and diagnostics
  English.Structural    small, justified structural sentence set
  AbstractCryptography deterministic `ac.*` sentence registrations
  ConstructiveCryptography
  RandomSystems         `rs.*` sentence registrations
  RandomSystems.CBC     application vocabulary only when actually reusable
  Help                  help and suggestion-provider protocols
  Widget                optional editor UI
  All                   deliberate aggregate import
```

The physical development tree has one Lake root and a unique package name:

```text
CryptoLanguage/
  lakefile.lean
  lean-toolchain
  LanguageDesign/
  Verbose/
  Informalization/
```

The present nested/copied worktree layout is not the target topology and must
not be preserved accidentally during migration.

The dependency rules are:

- `LanguageDesign` contains no tactic implementation, English strings, Lean
  proof-state mutation, or Informalization code.
- `Verbose.Core` knows stable rule and argument-role identifiers but no
  concrete carrier declarations.
- AC owns common construction sentences and infrastructure.
- CC and Random Systems extend the same scoped language from their owning
  modules; AC must not import their vocabulary.
- `Verbose.RandomSystems.CBC` may contain only reusable CBC concepts.  A
  theorem-specific script or phrase table belongs in a test fixture, not a
  public grammar module.
- The current controlled-language commands must keep working during migration
  through compatibility macros or direct re-registration.

During external development `LanguageDesign` is downstream of
`abstract-crypto`. Existing AC and Random Systems declaration registries are
adapted into its typed IDs and validated there; main-library declarations
cannot carry attributes defined only in the external package. If the main
repository later needs to emit shared annotations directly, the small
dependency-neutral ID/annotation contract must first be adopted explicitly by
both repositories. No reverse dependency may be smuggled in through an
attribute.

### 3.1 External-project contract

During the current CBC stage this library lives in the same sibling Lake
package as the informalizer and follows the live `abstract-crypto` checkout
directly:

```lean
require AbstractCryptography from "../../abstract-crypto"
```

This is the chosen executable profile because the present CBC construction is
`Applications.CBCMAC.Construction` in that checkout and still imports its
bundled `RandomSystems.*` implementation. The manifest must not simultaneously
require the sibling `random-systems` package: that package disables the bundled
modules in its `AbstractCryptography` dependency, so mixing both graphs would
make module ownership ambiguous. When the functional Random Systems rewrite
moves the CBC application to the sibling repository, a separately tested
manifest replaces this profile; the language core and source grammar stay the
same.

The current private CBC helpers are not externally writable proof seams.
Before Stage 5, the owning repository must expose a small public semantic
interface for the node contracts used in Section 10: the collision game and
its filtered form, their conditional-equivalence laws, the blind collision
bound, and the two `theta` application equalities. One public theorem or
structure may satisfy several contracts; this is not a private-name-for-name
export requirement. It is a source API change, not grammar dispatch by private
declaration name. Until that interface exists, the CBC frontend reports the
acceptance fixture as unreachable and does not substitute a copied model or a
theorem-specific macro.

The live dependency's ambient-carrier CBC probability and construction
endpoints compile. The ordinary language suite still keeps CBC reachability
and signature files in the explicit `CBCVerboseTests` gate because those files
track the evolving application boundary. That gate now freezes
`cbc_constructs_within`, `cbc_distance_le`, the two PDS advantage endpoints,
and the public combinatorial lemmas. It establishes reachability and signature
stability, not permission to dispatch on private proof helpers.

The projects use the same `lean-toolchain`; the external build reports a
mismatch before elaboration and does not pin a competing Mathlib. Local
development follows the live working tree, while CI records and tests its
specific revision and dirty state.

The initial implementation adapts Massot's architecture rather than importing
his current `master` wholesale: it presently targets a later Lean/Mathlib
toolchain, and its teaching widget and broad anonymous reasoning are not our
semantic contract. A matching historical tag may be used for source-level
comparison or a narrow compatibility probe, but adding it as a dependency
requires a separate Lake/toolchain/import-conflict experiment first.

## 4. Shared and Verbose-specific data

The shared language design identifies mathematical meaning. It includes a
language-neutral derivation schema—the mathematical act, input/output roles,
and obligations—but not a parser or tactic. The Verbose layer adds source
syntax and proof-state behavior.

Illustrative core types are:

```lean
structure RuleId where
  layer : Name             -- ac, cc, rs
  family : Name            -- construction, conditionalEquivalence, ...
  rule : Name              -- compose, preserveRestriction, ...

structure SentenceFormId where
  language : Name          -- en, fr, ...
  family : Name            -- stable surface family
  form : Name              -- canonical, legacy, forward, backward, ...

inductive ProvisionPolicy
  | requireExplicit        -- written in the source sentence
  | inferCanonical         -- uniquely fixed by goal/operands or typeclass
  | selectionOnly          -- assistance may use only an explicit editor selection

structure ReferenceSyntax where
  term : Lean.Syntax
  readerNote? : Option String

structure OperandSyntax where
  role : ArgumentRole
  value : ReferenceSyntax

structure BindingSyntax where
  role : ArgumentRole
  name : Name
  declaredType? : Option Lean.Syntax

structure FactBindingSchema where
  role : ArgumentRole
  type : ClaimPattern

inductive SortConstraint
  | proposition
  | data
  | anySort

structure TypePattern where
  builder : TypePatternId
  operandRoles : Array ArgumentRole
  expectedSort : SortConstraint

structure LocalBindingSchema where
  role : ArgumentRole
  type : TypePattern

inductive SurfaceGoalEffectSchema
  | closeMain
  | replaceMain (residualRoles : Array ObligationRole)
  | addLocalFact (binding : FactBindingSchema)
  | introduce (bindings : Array LocalBindingSchema)
  | guardUnchanged

inductive SentenceEffectSchema
  | fixed (effect : SurfaceGoalEffectSchema)
  | assertion (conclusion : ClaimPattern)

inductive SentenceEnvelope
  | bare
  | fact (name : Name)

structure SentenceFormSchema where
  id : SentenceFormId
  rule : RuleId
  writtenOperandRoles : Array ArgumentRole
  writtenBindingRoles : Array ArgumentRole
  effect : SentenceEffectSchema
  attestations : NonemptyArray SourceAttestation

structure SentenceDescriptor where
  formId : SentenceFormId
  ruleId : RuleId
  act : SpeechAct
  effect : SentenceEffectSchema
  schema : RuleSchema
  backendDeclaration : Name
  sourceAttestation : SourceAttestation
  supportingSourceAttestations : Array SourceAttestation
  routineClosures : Array Name
  routineRootCombinators : Array Name
  fixedProofCombinators : Array Name
  supportsNamedFact : Bool

structure SentenceIntent where
  formId : SentenceFormId
  operands : Array OperandSyntax
  bindings : Array BindingSyntax
  envelope : SentenceEnvelope
  source : Lean.Syntax
  guidance : Array PresentationAnnotation

structure ElaboratedOperand where
  role : ArgumentRole
  expr : Lean.Expr
  type : Lean.Expr
  note? : Option String

structure RuleInvocation where
  ruleId : RuleId
  operands : Array ElaboratedOperand

structure CheckedEvidenceRoot where
  proof : Lean.Expr
  inferredType : Lean.Expr
  routineSupport : Array RoutineEvidenceAnchor

structure CheckedAssertion where
  invocation : RuleInvocation
  exactConclusion : Lean.Expr
  evidenceRoot : CheckedEvidenceRoot
  proofSurface? : Option ProofSurface

inductive AssertionDestination
  | closeMain
  | localFact (name : Name)

structure AssertionOccurrence where
  assertion : CheckedAssertion
  destination : AssertionDestination

structure AssertionOccurrenceSummary where
  invocation : RuleInvocation
  exactConclusion : Lean.Expr
  destination : AssertionDestination
  evidenceAnchor : EvidenceAnchor
  proofSurface? : Option ProofSurface

structure ResidualGoalEvent where
  role : ObligationRole
  tag : Name
  mvarId : Lean.MVarId
  target : Lean.Expr

inductive GoalEffect
  | closeMain
  | replaceMain (obligations : Array ResidualGoalEvent)
  | addLocalFact (role : ArgumentRole) (name : Name) (exactType : Lean.Expr)
  | introduce (bindings : Array (ArgumentRole × Name × Lean.Expr))
  | guardUnchanged

structure GoalSnapshot where
  mvarId : Lean.MVarId
  target : Lean.Expr

structure LocalBindingEvent where
  role : ArgumentRole
  name : Name
  fvarId : Lean.FVarId
  exactType : Lean.Expr

structure SentenceEvent where
  schemaVersion : Nat
  formId : SentenceFormId
  ruleId : RuleId
  invocation : RuleInvocation
  operands : Array ElaboratedOperand
  assertion? : Option AssertionOccurrenceSummary
  intrinsicEffect : GoalEffect
  outerEffect : GoalEffect
  goalsBefore : Array GoalSnapshot
  goalsAfter : Array GoalSnapshot
  residualGoals : Array ResidualGoalEvent
  localsAdded : Array LocalBindingEvent
  sourceRange? : Option Lean.Syntax.Range
  guidance : Array PresentationAnnotation
  sourceAttestation : SourceAttestation
  supportingSourceAttestations : Array SourceAttestation
  source : Lean.Syntax

structure SentenceTraceEntry where
  declaration : Name
  ruleId : RuleId
  backendDeclaration : Name
  operandFingerprints : Array (ArgumentRole × UInt64 × UInt64)
  exactConclusionHash? : Option UInt64
  assertionDestination? : Option AssertionDestination
  routineProducers : Array Name
  routineProofHashes : Array UInt64
  sourceAttestation : SourceAttestation
  supportingSourceAttestations : Array SourceAttestation
  sourceText : String
```

`fixedProofCombinators` licenses only a result-bearing evidence spine. A proof
operand must be the checked evidence root or an immediate premise reached
through registered outer combinators. A registered theorem hidden inside an
ignored argument of an unrelated wrapper does not authenticate that operand.

The concrete representation may differ, but these separations are binding:

```text
fixed English syntax
  -> SentenceIntent
  -> registry lookup and role-checked operands
  -> one RuleInvocation and deterministic backend
  -> checked assertion occurrence or fixed-effect occurrence
  -> verified outer GoalEffect
  -> successful SentenceEvent
```

`CheckedAssertion` is the authoritative transient result of checked lowering.
`SentenceEvent` stores only an `AssertionOccurrenceSummary` for observability
and optional presentation metadata. Its evidence anchor is not authority and
cannot authorize a later informalization claim. Informalization may use the
associated claim only after independently recovering or revalidating the
checked evidence root against the exact conclusion.

Every explicit assertion operand must occur structurally in either the exact
conclusion or the checked proof root. Every accepted routine receipt must occur
in that proof root as well. Thus a parser cannot attach correct-looking
metadata to an unrelated proof, and a routine proof established on a scratch
goal cannot be presented as support for the assertion that follows.

`SentenceFormSchema` is only a linguistic adapter to the shared
`InferenceSchema`. Registration checks that its written roles are exactly the
explicitly provisioned roles of that inference. A fixed-effect form must have
the same residual roles and tags as the inference. An assertion form must have
one exact conclusion, intrinsically close the current main goal, and create no
residual goals or bindings. It cannot redefine the conclusion, premises,
obligations, move kind, or provenance of the mathematical rule.

The envelope supplies only the assertion destination. A bare assertion has
outer effect `closeMain`. `Fact name:` changes that outer effect to
`addLocalFact name exactConclusion`; it does not change the assertion's
`RuleInvocation` or intrinsic effect. The evidence root is elaborated before
the local declaration is introduced, and the inferred type of its proof must
be definitionally equal to `exactConclusion`. A realized local binding exists
if and only if the destination is `localFact name`; its name is exactly `name`
and its type is definitionally equal to `exactConclusion`.

For a bare occurrence, the instantiated conclusion must be definitionally
equal to the current target and the assertion backend closes that target. For a
`Fact` occurrence, the same schema first constructs its exact conclusion from
the written and canonically inferable operands, creates an isolated proof goal
of that conclusion, and runs the same assertion backend there. The isolated
run must close exactly that goal and create no locals or residual goals before
its proof is inserted into the unchanged outer goal as the named local fact.
An assertion whose conclusion cannot be constructed without mining the outer
target for a noncanonical mathematical choice is ineligible for the envelope.

Eligibility is an explicit descriptor capability, `supportsNamedFact`; being
an assertion is necessary but not sufficient. After the assertion event is
emitted, the envelope compares its recorded before/after goal snapshots with
the actual final state. Any additional clearing, introduction, or closure
inside the envelope rejects the entire transaction and restores the proof
state and metadata.

`TypePattern` is a general dependent local-type schema, not an entity-only
pattern. Its registered builder constructs the expected type from the listed
role operands and may produce either a data type or a proposition according to
`expectedSort`. It therefore covers `e : DDE.Total`, `n : ℕ`, a witness
`L : List X`, and a hypothesis such as `nonAdaptive : NonAdaptive e`. The
transaction records and compares the fully elaborated `Lean.Expr`; the pattern
does not replace that exact check.

The implementation treats `builder`, `operandRoles`, `expectedSort`, and the
ontology concept as checked data.  With no operand roles, `builder` names the
nominal ontology class.  With operand roles, it names a Lean type constructor:
the frontend applies that constructor to the exact elaborated expressions at
those roles and definitionally compares the result with the candidate type.
Missing roles and ill-typed constructor applications fail closed.  For
example, a pattern with builder `RandomSystems.PDS` and roles
`inputAlphabet, outputAlphabet` constructs and checks the exact expected type
`PDS X Y`.

Direct carrier classes also reject outer collections, products, subtypes, and
function spaces: `List (PDS X Y)`, `Option (PDS X Y)`,
`PDS X Y × Nat`, `{S : PDS X Y // p S}`, and `Nat → PDS X Y` are not
themselves PDS operands.  Positive and negative elaboration tests exercise
both the direct-head gate and the role-indexed constructor comparison.

Canonical sentence structure is rendered from mathematical meaning, not by
echoing the surface form that happened to be parsed. Proof surface belongs to
the wrapped assertion, not to the `Fact` heading. Canonical rendering first
renders the registered assertion from its domain rule and preserved proof
surface. When its destination is `localFact name`, it prefixes `Fact name:`.
A generic legacy `We have name : proposition` cannot be converted to `Fact`
unless checked semantic recovery independently identifies a registered
assertion. Otherwise it remains ordinary Lean or legacy syntax. This gives one
normalization direction for recoverable forms:

```text
legacy or canonical source
  -> SentenceIntent -> RuleInvocation
  -> canonical language renderer -> canonical source
```

Three contracts are deliberately distinct:

- the source-preserving formatter retains `ProofSurface` and guarantees that
  the rendered sentence elaborates to the same invocation, local binding, and
  before/after goals;
- help renders an insertable skeleton with explicit operand and proof holes,
  and makes no round-trip claim until the author fills those holes; and
- the informalization renderer consumes checked semantic evidence and emits a
  clause plan, not reconstructible Lean tactic text.

Thus canonical rendering never manufactures a domain assertion from a generic
local proposition and never pretends to regenerate a tactic derivation. The
Stage 3 migration adds the assertion envelope only after bare/wrapped identity,
eligibility, and rollback tests pass.

The renderer must refuse when a required explicit operand has no printable
reference or a required introduced fact has no author-supplied name. It may
not recover missing choices by pretty-printing arbitrary elaborated terms.

The implementation records the successful event as a typed custom `InfoTree`
node, not only a transient string trace. Its versioned payload contains at
least the surface-form ID, mathematical rule ID, role-labelled elaborated
operands, before/after goal propositions, role-labelled residual metavariables,
source range, and presentation guidance. The node is recovered during source
re-elaboration and need not survive in an imported `.olean`.

The public event is an observation, not an authorization token. Its internal
wrapper is private and each `Fact NAME:` envelope mints a fresh nonce; copying
or modifying an earlier genuine public event does not satisfy the envelope.
Likewise, a backend action is a capability generated from one syntactically
fixed function head. Parser code cannot pair a trusted declaration name with
an arbitrary tactic closure.

Routine receipts and fixed-effect proof operands have an additional relevance
gate. A routine receipt must be an immediate premise of a registered root
proof combinator, and a fixed-effect operand literally playing the `proof`
role must be consumed by a registered fixed-proof combinator. Occurrence under
an opaque wrapper is insufficient. Empty combinator registries fail closed.

The persistent declaration trace is deliberately smaller but not merely a
list of rule names. It retains the enclosing declaration and backend identity,
role-labelled expression/type fingerprints, assertion conclusion and
destination, routine producers and proof hashes, the effective source
attestation, and the original sentence text. Whole-proof acceptance tests use
this trace to freeze the proof passage rather than accepting any sequence with
the same number of sentences.

The parser does not restate the speech act, rule, or expected goal effect in
`SentenceIntent`; those are authoritative registry data selected by
`SentenceFormId`. After elaboration the implementation constructs a
`RuleInvocation`. This prevents an English parser and its backend contract
from silently disagreeing about what the sentence claims to do.

Names written in output positions are different from semantic input operands.
The parser records ordinary introductions as role-labelled `BindingSyntax` and
a `Fact` name in `SentenceEnvelope.fact`. Registry lookup instantiates the
concrete outer `GoalEffect`; the transaction validator compares it with the
locals Lean actually added. Thus a static registration never pretends to know
the name in `Fact claim`, `Fix environment`, or `From existence, choose
witness`.

### 4.1 Sentence registry

Each public sentence registration must contain:

- one stable `SentenceFormId` and one allowed mathematical-rule family;
- one owning semantic module;
- the expected relation and ontology classes of its operands;
- a `ProvisionPolicy` for every operand;
- the exact goal shapes it accepts;
- its ordered obligation roles;
- one backend entry point;
- the exact routine side conditions that backend may close;
- whether the assertion has a checked isolated-claim constructor and may be
  wrapped by `Fact NAME:`;
- whether method-specific wording requires applying the registered theorem or
  validating the cited proof application's `RuleId`;
- English diagnostic constructors;
- suggestion eligibility and required selected operands;
- a source-attestation note; and
- positive, negative, grammar, event-trace, and complete-proof tests.

A sentence may dispatch among multiple theorem variants only when the variants
have the same mathematical meaning and intrinsic goal effect, such as exact
versus scalar construction closure. An assertion envelope may then change only
the outer destination as specified above. Dispatch must use the checked goal
shape and a small curated registry. More than one applicable semantic rule is
an error.
`checkedLibrary` records a machine-checked mathematical relation but never
licenses public English by itself. Application-only source evidence is selected
only for an exact enclosing declaration, rule, and backend under an explicit
application profile; it cannot leak into the generic sentence catalog. This
gate runs before backend execution, not only during catalog rendering. Pending
parser prototypes are absent from the public umbrella import and remain
fail-closed even when their implementation module is imported directly.
The S1 rewrite surface is one such explicit application module,
`Verbose.English.Rewriting`; `import Verbose` does not expose it, and its
project-controlled license is resolved only in the registered switching
declaration/profile.
IDs must be checked for duplicates across the adapted AC, CC, and Random
Systems registries, not merely within each source registry.

The ideal system, simulator, intermediate system, restriction, reveal, bad
event, coupling, environment/schedule, and proof route are
`requireExplicit`. Selection-aware help may copy such a term only when it is
already selected and must still print it in the generated sentence.
`inferCanonical` is reserved for implicit type parameters, canonical ambient
structure, or an operand uniquely visible in the current goal. Help and
lowering both enforce the same policy; it is not merely documentation.

Parser elaborators call typed backend functions directly. Persistent
registries contain serializable schemas, source attestations, canonical-render
data, diagnostic IDs, and backend declaration names for inspection; they do
not store tactic closures. A public backend has a fixed checked function type
in `Verbose.Backend` and is called by its owning elaborator. Dynamic `evalConst`
dispatch is outside the first implementation. Each parser call also supplies
that backend declaration identity to the lowering transaction; a mismatch with
the descriptor is rejected before the backend runs. The in-memory action is
not treated as sealed merely because its declaration name matches: after it
runs, the transaction validates the exact goal transition and requires every
fixed-effect operand to be connected to the target, residual goals, introduced
types, or the checked proof assignment. Operand classification is
performed without modifying elaborator state, so it cannot constrain
metavariables before the registered backend checks the exact relation.

### 4.2 Input-facing ontology requirements

Before a domain sentence is public, its schema must distinguish every formal
kind that affects applicability or truth. The Random Systems profile needs at
least:

- `DDS X Y`, signed `PDS X Y`, signed `PDG X Y`, `PDS.Behaviour`,
  `PDG.GameBehaviour`, `PDS.GamesFor S`, literal common-domain
  `Presentation`/`RandomSystem`, normalized common-domain
  `ProbabilityPresentation`/`ProbabilityRandomSystem`, normalized partial
  laws `Distribution.ProbDist (System.DDS X Y)`, normalized ambient
  `Ambient.PDS`/`Ambient.RandomSystem`, specifications, and construction
  judgments as different carrier roles;
- fixed-interface RS converters with typed outer/inner query and answer
  boundaries, distinguished from multi-interface AC/CC attachment sites;
- ambient attempted-history presentations versus literal common-domain
  presentations and their checked embedding/forgetting bridges;
- presentation equality, `PDS.equivalent`, strict-distinguisher
  `PDS.Equivalent`, `Ambient.PDS.Equivalent`, quotient equality, full
  game-transcript equivalence, all-nonempty-list not-won equivalence,
  per-list not-won-law equality, conditional equivalence,
  observational distance, coupling, and construction as different relations;
- `PDS.IsProbability` evidence for an existing PDS, nonnegativity,
  normalization, equal weight, totality, shared domain,
  prefix-closure, support membership, applicability, and query admission as
  different premise roles;
- partial DDE, total DDE, signed partial `RandomSystems.PDE`, normalized total
  `Ambient.PDE`, strict distinguisher, non-adaptive property, fixed-query
  environment, horizon, induced query list, transcript, answered queries,
  refusal, kept prefix, event, and winner role as different entries;
- support of a presentation and answering domain of a system as different
  relations; unconditional ambient action, global common-domain image
  preservation, and specification-local `ApplicableTo` as different action
  regimes, none replaced by total-completion absorption;
- `Real`, `NNReal`, and `ENNReal` scalar roles and explicit cast/embedding
  bridges; and
- `Adv`, fixed-domain `AdvD`, `Adv⊥`, ambient advantage, class distance
  `Δ`, strict-test `maxEDist`, carrier-indexed quotient `edist`, adaptive
  winning, blind winning, and static winnability as different quantities and
  proof targets.

Words such as “system,” “game,” “resource,” and “bound” are surface heads, not
permission to erase these distinctions. Selectional restrictions in each
schema reject the wrong carrier or relation before its backend runs.

### 4.3 Transactional lowering

Lowering must be transactional.  Operand elaboration, applicability checks,
the backend, and goal-effect validation either all succeed or restore the
original tactic state.  The event is emitted only after success.

The backend must validate more than “the tactic did not throw.”  For example:

- a closing sentence closes the current main goal;
- a reduction sentence produces exactly the documented obligations, in their
  documented order and with stable case tags;
- a named-claim sentence adds a local declaration of the stated type; and
- a goal reminder leaves the proof state unchanged after confirming the
  target's canonical relation and operands.

Validation compares the full ordered goal list and expected local-context
delta. Unless a schema explicitly says otherwise, goals other than the main
goal are preserved by identity and in order. Every residual target must match
its declared `GoalPattern`, and every introduced local must match its declared
name, role, and type. These checks occur before the event is committed.

## 5. Lexical and parser contract

The new syntax is enabled by:

```lean
open scoped CryptoVerbose
```

Importing a module does not silently open the scope.

Legacy commands remain in their existing scope during migration. The new and
legacy aggregate scopes are not opened together by a default import. Because
token reservation occurs on import rather than `open scoped`, new aggregate
modules import narrow semantic/backend modules and never import legacy grammar
modules. If a compatibility file must import both grammars, its legacy prose
atoms must first be migrated to non-reserving `&"word"` syntax.

### 5.1 Fixed prose and Lean holes

The grammar is controlled English around ordinary Lean syntax holes.  It
controls the relation among mathematical terms; it does not attempt to parse
English descriptions of arbitrary terms.

```text
The construction follows from firstLeg
With context as the right parallel context, the construction follows from baseConstruction
The game collisionGame is conditionally equivalent to idealSystem by cbcLaw
```

Terms, propositions, binders, and names retain Lean syntax and notation.

### 5.2 Keyword discipline

Every alphabetic prose literal in the new grammar uses Lean's non-reserving
parser form `&"word"`. Identifiers occur only in genuine name or term slots.
The existing `ident`-then-`expectWord` workaround is not a sufficient new
architecture: another imported grammar can reserve the same word first and
make the sentence unparsable.

Opening all AC, CC, and Random Systems language modules together must not
prevent declarations or locals named `real`, `ideal`, `protocol`,
`construction`, `system`, `game`, `simulator`, `bound`, or `condition`. The
regression is differential: every prose atom that parses as a bare identifier
before importing Verbose must still do so afterward. Lean's intrinsic keywords
such as `by`, `in`, `with`, and `have` are excluded from that claim and are
tested only in escaped form, for example `«have»`. A static lint rejects
alphabetic prose atoms written as newly reserving tokens, and a combined-import
test runs the differential corpus.

### 5.3 Sentence boundaries and layout

- The end of the tactic line terminates a sentence; no final full stop is
  required.
- A comma introduces a continuation only in a grammar that explicitly expects
  one.
- Indented continuation lines must parse identically to one-line spelling.
- Term holes that contain commas or words used by the grammar must remain
  unambiguous through Lean's existing term categories or parentheses.
- The formatter should break before subordinate consequence clauses, as in
  the existing parallel-context sentence.
- Error ranges should point to the rejected word or operand, not the entire
  tactic block.

### 5.4 References and author notes

A new-style reference uses the exact syntax category:

```lean
declare_syntax_cat verboseReference
syntax term:max (&"noted" str)? : verboseReference
```

Compound or lower-precedence terms must be parenthesized before `noted` or
before following prose. Only `term` is elaborated as proof input. The string is presentation-only and
must be retained in the successful event.  Structured annotations from
`LanguageDesign.Annotations` may later provide stable terminology, paragraph,
or expansion hints.  They must never alter the proof term or compensate for a
missing premise.

The existing parenthesized string form remains accepted only by compatibility
syntax. It is not extended: visually it is too easy to confuse with ordinary
term application.

The general presentation wrapper, usable around ordinary Lean or a controlled
sentence in a source that imports the external package, has the shape:

```lean
With presentation (label := "the collision game",
    paragraphBefore := true) in
  proofStep
```

It executes `proofStep` unchanged, captures its checked before/after goals,
and emits a typed `InfoTree` hint anchored to that transition. A free author
note is a different constructor and remains visibly non-checked prose. While
the package is external, an unmodified main-library source that does not
import this wrapper cannot use it; informalization must still handle that
ordinary source without metadata.

### 5.5 Names

Long cryptographic proofs require stable human-chosen names.  Any sentence
that produces a fact or witness used later must require the author to name it.
The frontend must not invent names such as `h_1` in public source.

Named and nameless dialects are not both enabled by default.  The research
profile uses named forms.  A nameless teaching profile may exist separately,
but it must not introduce hidden search into the research grammar.

### 5.6 Grammar combinators and prefixes

The tables below use these grammar metavariables:

```text
name           ::= ident
proposition    ::= Lean term
type           ::= Lean term
value          ::= Lean term
reference      ::= Lean term:max [ noted string ]
references     ::= reference
                 | reference and reference
                 | reference, ... , and reference
assertion      ::= registered domain assertion
                 | registered formula assertion
namedAssertion ::= Fact name . assertion
```

Square brackets here denote an optional grammar component, not literal Lean
tokens. Concrete syntax uses non-reserving `&"..."` atoms for every prose word.
Lists have one canonical English spelling; synonyms and alternate comma rules
are not added casually.

Canonical sentence families diverge early:

| Prefix | Family |
| --- | --- |
| `Fact` | named local mathematical result |
| `Fix` / `Assume` | introduction |
| `From` | structural elimination |
| `By` | a registered mathematical method and its consequence |
| `To prove` / `It remains` | reduction or checked goal announcement |
| `Conditional equivalence` | advantage consequence |
| `Attaching` / `Adjoining` / `Forgetting` / `Restricting` | system/game transformation |
| `Outside` / `Conditioned on` | conditional structural or law claim |
| `For` | fixed-schedule mass claim |
| `The construction` / `The systems` / `The games` | relation-specific closure |

Within a prefix, the next mathematical head noun selects the schema before a
large term is parsed. The parser test suite includes every pair of competing
prefixes and every term-boundary stress case.

## 6. Structural sentence kernel

The structural kernel is intentionally small.  These sentences are useful
only when they expose a paper-level step more clearly than ordinary Lean.

| Status | Controlled form | Mathematical act | Goal effect |
| --- | --- | --- | --- |
| canonical/required | `Fact name: ASSERTION by PROOF`, where `ASSERTION by PROOF` is one registered assertion sentence | give that mathematical assertion a paper-style local anchor | run the assertion with destination `localFact(name)` |
| rejected as canonical | `Fact name: proposition by ...` / `from proof` using a generic proposition rather than a registered assertion | replaces the assertion ontology by a generic proposition wrapper | use ordinary Lean `have` unless a registered assertion form exists |
| legacy/replace | `We have name : proposition by ...` / `from proof` | migration spelling for a generic local proof | parse only where compatibility requires it; never canonicalize it to `Fact` |
| required | `It remains to prove proposition` | confirm and foreground the current obligation | guard unchanged |
| required | `Fix name` / `Fix name with hypothesis : property` | introduce an explicitly quantified object and, if present, its condition | introduce named locals |
| required | `Assume name : proposition` | introduce the antecedent of an implication | introduce named local |
| required | `From hExists, choose x such that hx : P x` | eliminate the supplied existential and name both witness and property | introduce named locals |
| required | `From hAnd, obtain hP : P and hQ : Q` | eliminate the supplied conjunction with stated component types | introduce named facts |
| rejected as public syntax | `By rule applied to arguments using premises, ...` | implementation meta-language rather than a mathematical sentence | use a domain-specific consequence or ordinary Lean |
| rejected as public syntax | `Using fact, we conclude the goal` | adds no mathematical information beyond `exact fact` | use ordinary Lean; a domain relation may say “The conclusion follows from fact” only when that relation is registered |

Domain-specific forward and backward forms never search for a rule, argument,
or mathematical premise.  Missing implicit type parameters may be inferred by
ordinary elaboration; missing mathematical premises may not be synthesized by
broad search.  Canonical typeclass structure remains ordinary Lean instance
inference.

Witness and conjunction forms perform only structural elimination of the
explicitly cited proof. The announced names and propositions must match the
elaborated existential or conjunction exactly after permitted definitional
normalization; they do not run anonymous fact search.

There are no generic wrappers for `calc`, rewriting, case analysis, induction,
contradiction, or arbitrary local definitions. Ordinary `let` remains the
fallback when the ontology has no established noun phrase. Standard domain
objects normally use their registered mathematics: for example,
`Let restrictedFunction be the system [q] URF(X)` and
`Let restrictedPermutation be the system [q] URP(X)`. The renderer must not turn an
expression into “the restriction of the uniform random ...” merely because a
constructor name was recognized. A prose declaration is allowed only when a
source-attested operational definition communicates more than the standard
notation. Each form retains the exact typed term and has positive, negative,
grammar, and trace tests; this is not a general English spelling of `let`.

A characterized definition is one generic schema, not a branch on a known
declaration name. It first binds an explicit exact term, then validates a
separate registered characterization theorem and records that theorem as a
support edge of the definition. The characterization does not close the main
goal or introduce a local fact. The definition-plus-equivalent-characterization
frame is attested independently of Switching by Liu–Maurer 2020, Definition 6,
pp. 9–10. The exact Lean-facing composition remains project-controlled and
must still pass the breadth and lowering gates.

Canonical invariants of registered objects are normally discharged by the
owning domain backend and omitted from the controlled source sentence.  They
remain present in checked proof evidence and diagnostic expansion.  If an
invariant is mathematically material—for example, nonnegativity of an
arbitrary-mass law passed to an H theorem—the author uses ordinary Lean `have`
or a registered domain assertion whose mathematical subject and relation are
independently justified. The `Fact name:` envelope may wrap the latter but does
not create it.

There is no sentence of the form “... by construction; call this fact ...”.
The proposition is the mathematical claim; a source name is only a binding
anchor.  Routine nonnegativity of a normalized restricted URP should produce
no declaration at all, while nonnegativity of an arbitrary-mass PDS may be a
visible premise.  Constructor recognition alone does not decide salience.

The accepted switching regression form is S1 in
[`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md). In particular,
`conditionalLaw` and `forgettingIdentity` wrap their Random Systems assertions,
while the formulaic nonnegativity and equal-weight premises remain in the
checked support graph. The notation nodes elaborate to exact registered terms;
they are not recognized from identifier spelling.

The authoring layer would benefit from one deliberately small routine backend.
This is a **proof-synthesis** facility for Verbose: it constructs a proof of a
missing Lean obligation. It is governed by a typed registry rather than
tactic-name permission:

```text
structure RoutineRewriteRule where
  id : RoutineRuleId
  owner : ModuleId
  theorem : DeclName
  beforePattern : PropositionPattern
  afterPattern : PropositionPattern
  orientation : Forward | Backward
  shrinkingMeasure : CheckedTerm -> Nat
  permittedGoalClass : GoalClass
  cost : Nat
  soundness : forall substitution,
    Matches substitution beforePattern afterPattern ->
      TheoremRelates theorem orientation
        (instantiate beforePattern substitution)
        (instantiate afterPattern substitution)
  decreases : forall substitution,
    Matches substitution beforePattern afterPattern ->
      shrinkingMeasure (instantiate afterPattern substitution) <
      shrinkingMeasure (instantiate beforePattern substitution)

structure RoutineCloser where
  id : RoutineCloserId
  owner : ModuleId
  goalPattern : PropositionPattern
  permittedGoalClass : GoalClass
  proofProducer : RegisteredProofProducer
  cost : Nat
  soundness : forall substitution,
    MatchesGoal substitution goalPattern ->
      ProducesProofOf proofProducer (instantiate goalPattern substitution)
```

Rewrite registration is accepted only with the checked uniform `decreases`
receipt; a sample reduction is insufficient. Closers do not pretend to shrink:
they must return a proof of the matched goal through their registered producer
and its soundness receipt. `rs_routine` has fixed per-goal and total-cost bounds.
Its permitted goal classes are closed enums:
definitional/coercion normalization, canonical sign/weight projection,
subtype and support packaging, propositional normalization, Presburger-linear
closure, and normalized polynomial identity. “Elementary arithmetic” means
one of these registered closers; it is not an invitation to search or to pass
through unrecorded non-shrinking intermediate states.

The corresponding tools are:

- a curated `rs_simp` set for restriction, forgetting, pushforward
  nonnegativity/weight, subtype projections, and coercion packaging;
- `rs_routine`, a bounded closer that uses only those shrinking rewrites,
  canonical instances, propositional normalization, and elementary arithmetic;
- `rs?`, which reports the single matching registered theorem or routine
  normalization without applying broad environment search; and
- typed trace output recording the before/after proposition and every consumed
  lemma, so informalization can collapse the step by semantic effect.

This automation never chooses a game, event, ideal system, converter, proof
route, or bound. Conditional equivalence, a forgetting identity that changes
the proof register, and any noncanonical probability premise remain available
as named facts even when their proof terms are short. In particular,
`rs_routine` cannot establish `PDG.CondEquiv`, collision-freeness, uniformity,
or a collision bound. Negative tests make each of those attempts fail, and
also reject any rule that does not shrink, exceeds the resource budget, or
would instantiate a semantic-choice metavariable. The typed routine trace may
propose an informalization compression boundary, but the informalizer uses a
separate bounded **classification** registry over already checked evidence.
That classifier cannot invoke `proofProducer`, construct a missing premise, or
authorize Verbose lowering. The two registries have separate positive,
negative, coverage, and resource-bound tests.

### 6.1 Proof-status invariant

The grammar distinguishes three statuses:

- **assertion:** the sentence supplies or constructs proof of the proposition;
- **reduction:** the sentence applies a checked rule and creates explicitly
  named obligations; and
- **announcement:** the sentence checks the current goal without changing it.

An assertion uses “we have,” “we obtain,” “is,” or “is at most” only when the
claim is discharged in that sentence. A reduction uses “it suffices to
prove” or “it remains to establish.” An announcement uses “it remains to
prove” and is checked against the unchanged goal.

For example, an H-coefficient opening must not say that the bad mass *is at
most* `delta` if it creates that estimate as a goal. It instead has the form:

```lean
By the H-coefficient theorem, it suffices to prove the good-ratio and
  bad-mass bounds for Bad using realNonnegative, idealNonnegative,
  equalWeight, and idealWeightAtMostOne
case goodRatio =>
  ...
case idealBadMass =>
  ...
```

Every multi-goal backend assigns stable semantic case tags. Anonymous bullet
sequences are permitted by Lean but are not the canonical generated form in
help or acceptance proofs.

### 6.2 Method-name integrity

A method-specific sentence—“by conditional equivalence,” “by Condition C,”
“by the H-coefficient theorem,” or “by the birthday estimate”—normally applies
the registered method theorem itself to explicit premises. A summary form may
instead accept a cited proof only when its elaborated application head is a
declaration registered for that `RuleId`, with role-correct operands. Merely
having the final proposition as a local hypothesis is not enough.

Recognition is fail-closed. It strips only source metadata, lets, and a
documented whitelist of reducible semantic wrappers, then requires the head
constant and selected arguments to match the registered signature. It does not
unfold an arbitrary named helper or inspect a local hypothesis's provenance.
Unregistered helpers therefore use ordinary Lean even when a human knows how
they were proved.

An arbitrary term of the final target type cannot be relabelled as a named
method. When only type correctness is known, ordinary `exact proof` is the
canonical source; the controlled language does not wrap it in content-free
English.

One registered exception is canonical scalar lifting. A method assertion may
have a fixed, typed lift skeleton such as `ENNReal.ofReal_le_ofReal`, provided
the outer proof root closes the exact lifted conclusion and its checked
evidence graph contains the role-correct registered method theorem at the
unique scalar-premise edge. Method integrity validates both nodes and their
types. It does not strip or ignore the lift, and no arbitrary wrapper or
transitive inequality is admitted by this exception.

## 7. AC and CC sentence families

The following catalog preserves and completes the deterministic construction
workflow.  Wording can be refined only with corpus evidence and without
changing the `RuleId` or mathematical effect.

| Status | Controlled form | Backend contract |
| --- | --- | --- |
| migration-existing / pending-attestation | `The construction follows from fact` | close an exact or scalar construction from the supplied equality, inclusion, distance bound, or construction |
| proposed / pending-attestation | `To prove the construction, it suffices to bound the distance between real and ideal by error using characterization` | apply the explicit construction characterization and create one tagged system-distance goal |
| migration-existing / pending-attestation | `The equality follows from fact` | close a typed converter-attachment or construction equality from the supplied converter equality |
| migration-existing / pending-attestation | `Replacing the converter in construction using equation, we obtain the required construction` | replace only the converter of the supplied typed construction |
| migration-existing / pending-attestation | `The construction follows by composing first and second` | serially compose in the written execution order |
| project-canonical / AGENTS-attested | `We use sigma to prove the construction` | apply the simulator rule and expose tagged membership and distance obligations |
| project-canonical / AGENTS-attested | `With context as the right parallel context, the construction follows from base` | extend by the fixed right resource/context |
| project-canonical / AGENTS-attested | `With context as the left parallel context, the construction follows from base` | extend by the fixed left resource/context |
| proposed / pending-attestation | `The construction follows by relaxing first through second using compatibility` | apply the explicit relaxation composition rule |
| proposed / pending-attestation | `The filtered construction follows from fact using commutation and simulatorAdmission` | apply the filtered construction rule with explicit commutation, admitted-simulator membership, and equality-or-distance evidence |
| proposed / pending-attestation | `The distance bound follows through intermediate using firstBound and secondBound` | close by the triangle rule from two already proved legs |
| proposed / pending-attestation | `By the triangle inequality through intermediate, it suffices to bound the two legs` | introduce the explicit intermediate and create tagged first- and second-leg goals; do not assert the bound yet |
| proposed / pending-attestation | `The construction follows in parallel from left and right` | combine two explicit component constructions in public order |
| proposed / pending-attestation | `The construction follows by composing the simulators in first and second using commutation` | compose simulator-target constructions with explicit commutation evidence |
| MR11-deferred | `For class, the defining test test accepts real with value at least 1 - error using admitted, idealSatisfies, and close` | this would apply `one_tsub_le_test_of_close`, but `DistinguisherClass` is behind the repository's MR11 provenance fence and is not imported by the MR16 research profile |
| proposed / pending-attestation | `Using security, it suffices to prove that simulator is idle and protocol commutes with availabilityFilter` | apply the security-to-availability rule and create tagged idleness and commutation goals |

Serial direction is a hard safety property.  The parser records the written
order, the backend checks the expected converter product, and negative tests
swap the two operands.  Reader annotations must not obscure this order.

“Filtered,” “parallel,” “simulator,” and “property” are distinct semantic
subjects.  They must not be collapsed into a generic sentence that asks the
backend to infer the proof route.

## 8. Random Systems sentence families

The Random Systems layer speaks about systems, games, laws, and scalar bounds.
It does not add generic carrier vocabulary to the AC module.

### 8.1 Exact system and game relations

| Status | Controlled form | Required explicit operands and effect |
| --- | --- | --- |
| required | `For every total environment and every horizon, P and Q induce the same transcript law using h` | exact `PDS.equivalent P Q`; do not accept strict-distinguisher equivalence |
| required | `Every strict distinguisher accepts P and Q with the same mass using h` | exact `PDS.Equivalent P Q`; do not accept `PDS.equivalent` without a bridge |
| required | `The common-domain presentations P and Q are equivalent using h` | exact `CommonDomain.Presentation.Equivalent P Q`; do not accept PDS equivalence or quotient equality |
| required | `The normalized common-domain presentations P and Q are equivalent using h` | exact `CommonDomain.ProbabilityPresentation.Equivalent P Q`; do not merge it with arbitrary-weight presentation equivalence |
| required | `For every total environment and every horizon, the ambient presentations P and Q induce the same attempted-history law using h` | exact `MultiInterface.PDS.equivalent P Q` |
| ordinary formula | `R = S` | equality on the exact ambient or common-domain quotient; do not lexicalize the carrier taxonomy |
| pending-attestation; exact-formula fallback | `Applying alpha to any embedded normalized common-domain system yields a system in the embedded image using h` | exact field `CommonDomain.DDC.preserves`; this is part of the converter value, not a later inferred fact |
| pending-attestation; exact-binder fallback | `Let alpha be a common-domain-preserving converter from (X,Y)-systems to (U,V)-systems` | binder for `CommonDomain.DDC U V X Y`, whose fields are a multi-interface DDC and its image-preservation proof; all four query/answer signature boundaries remain typed operands |
| pending-attestation; exact-formula fallback | `The converter alpha is applicable to specification Rcal using h` | exact `CommonDomainApplicable.ApplicableTo Rcal alpha`; concrete use separately requires resource membership |
| required | `Applying alpha to R gives S using h` | fixed-interface converter with matching boundaries and exact application equality; ambient action has no applicability premise |
| required | `Enhancing S with the MBO assignment A gives the game G over S using h` | exact equality `PDS.adjoin S A = G`, checked with `G : PDS.GamesFor S`; the phrase “over S” expresses the mathematical role without exposing subtype plumbing |
| ordinary formula | `(PDS.adjoin S A).1 = G` | exact equality to a `G : PDG X Y`; prefer the formula to “the PDG underlying ...” |
| required | `For every environment and every horizon, G and H induce the same game-transcript law using h` | exact `PDG.gameEquivalent G H` |
| required | `For every nonempty fixed query list, the not-won laws of G and H agree using h` | exact `PDG.EquivalentAsGames G H`; never accept full-game prose or one-list equality |
| required | `Ignoring the MBO of G yields S by h` | exact presentation equality `PDG.forget G = S` only |
| required | `The presentation obtained from G by ignoring its MBO is equivalent to S by h` | exact registered behavioral equivalence only |
| ordinary formula | `P.toAmbient = P'` | explicit common-domain random system, multi-interface image, and checked equality; carrier plumbing remains symbolic unless it is itself the mathematical point |
| ordinary formula; semantic node required | `edist (alpha R) (alpha I) ≤ edist R I` | exact `CommonDomain.ProbabilityRandomSystem.edist_apply_le alpha R I`; the current theorem has only converter, left-system, and right-system operands and no attachment-equality premises |
| required | `The game G is conditionally equivalent to S by h` | exact two-operand `PDG.CondEquiv G S`; no normalized-conditioning paraphrase |
| required | `Applying gameTransform to G and systemTransform to S preserves conditional equivalence using absorption and h` | distinct transforms, the exact absorption witness, and prior CE; match `condEquiv_fTransform` |
| required | `Restricting G and S to histories admitted by p preserves conditional equivalence using prefixClosed, gameNeverRefuses, systemNeverRefuses, and h` | exact domain predicate, prefix-closure, both never-refusal witnesses, and prior CE |
| required | `Restricting G and S to q queries preserves conditional equivalence using gameAnswersEveryQuery, systemAnswersEveryQuery, and h` | exact query bound, total-answer witnesses for both supports, and prior CE |

The preservation sentences must confirm the registered correspondence between
the game and system transforms. A type-correct but unsupported asymmetric
transform is rejected. “Equivalent
until bad” is not a synonym for `CondEquiv`, `EquivalentAsGames`, or a coupling;
each relation has its own grammar and backend.

These equality-shaped sentences are optional in a proof where an ordinary
named equality or `calc` step reads better. Their purpose is to make a
construction/system/game register transition explicit, never to paraphrase
low-level execution or quotient code.

### 8.2 Conditional equivalence and winning

| Status | Controlled form | Required explicit operands and effect |
| --- | --- | --- |
| S1 application-scoped | `The conditional equivalence in hCE gives Adv⊥(forget(G), S) ≤ νᴺᴬ[G]` | close the exact blind comparison; the displayed game, forgotten game, target system, and winning game are separate checked operands, and routine mass premises remain reachable evidence |
| pending generic form | adaptive or blind conditional-equivalence comparison outside a registered application profile | the Lean relation is checked, but a generic English frame requires independent attestation |
| pending generic form | a conditional-equivalence sentence saying that it suffices to prove a winning bound | replace the main goal with one tagged winning obligation only after the exact adaptive/blind form is separately licensed |
| required | `It remains to prove ν[G] ≤ ε` | guard the exact adaptive-winning goal |
| required | `It remains to prove νᴺᴬ[G] ≤ ε` | guard the exact blind-winning goal |
| required | `Fix an arbitrary total environment E and a horizon n, under assumption nonAdaptive that E is non-adaptive` | apply the universal blind-winning bound and introduce the exact environment, named non-adaptivity proof, and horizon |
| required | `Let xs be the fixed query list issued by E against R for n rounds, as witnessed by schedule` | check the induced-list equality and `nonAdaptive`; introduce or identify only `xs` |
| domain definition | `Let xs_adm be the subsequence of xs admitted by p` | exact equation `xs_adm = filterAdmit p xs` is retained as a selectable expansion together with source list and predicate |
| required | `For the fixed list xs_adm, the winning mass of E against G in n rounds is μ(Bad xs_adm), as shown by massIdentity` | exact game, environment, horizon, law, event, list, and mass identity |
| required | `Fix an arbitrary query list queries, under assumption admission that queries is admitted by p` | only inside a separately stated per-list collision lemma; introduce both list and named admission premise |
| required | `For the fixed list queries, μ(Bad queries) ≤ ε using hbound` | close one per-list event-mass estimate with its law and admission data retained in the event node |
| required | `The fixed-list bounds give νᴺᴬ[G] ≤ ε using hbound` | lift the uniform per-list estimate through the supplied blind-winning theorem |

The exact comparison
`Adv⊥(PDG.forget G, S) ≤ ENNReal.ofReal (PDG.blindSupWinProb G)` and the
transitive reduction from `Adv⊥(PDG.forget G, S) ≤ ε` to
`PDG.blindSupWinProb G ≤ ε` are different inference schemas. The former closes
one calculation rung; the latter replaces the main goal. They never share one
`RuleId` merely because both use the same conditional-equivalence theorem.

If the current real system is not definitionally `forget game`, the author
must provide an explicit forgetting equality and use an equality-guided
replacement step. The environment-to-list transition must expose why the list
is fixed: the backend checks the non-adaptive or blind premise. The induced
list is defined with an ordinary `let` from an explicit reference system,
environment, and horizon, and the admitted list is `filterAdmit predicate
messages`. It must not silently replace an unrestricted strategy by an
arbitrary list.  Schedule identification, list filtering, and the mass
identity are deliberately separate mathematical acts.

Every theorem premise has a catalog `ProvisionPolicy` and visibility class.
For registered normalized URF/URP-derived objects, canonical nonnegativity and
weight facts may be inferred and suppressed.  For arbitrary-mass PDS/PDG
arguments, those premises remain explicit named operands; the
arbitrary-mass surface appends their exact role-labelled names and never
uses an opaque operand named `premises`.

### 8.3 Collision and counting

| Status | Controlled form | Required explicit operands and effect |
| --- | --- | --- |
| later/extract theorem | `If Bad has not occurred, distinct messages have distinct terminal inputs using h` | expose only after a stable theorem has this exact scoped conclusion |
| required | `On collision-free histories, the CBC output law factors as formula using h` | `formula` is the exact mass-factorization conclusion of `not_cbcBad_implies_uniform_outputs` or its public replacement; do not generate stronger uniformity prose |
| required | `For the fixed list queries, law.mass (Bad queries) ≤ ε using h` | exact list, law, event, and bound; reject a merely query-dependent inequality |
| required | `Counting the possible witness pairs gives law.mass Bad ≤ ε using h` | explicit witness/index family and counting lemma |
| required | `For the fixed list queries, the birthday bound gives law.mass (Bad queries) ≤ ε using admission and size` | exact list, law, budget/admission proof, and alphabet-size data |

The frontend may explain fresh-output uniformity and repeated-output
consistency only after genuine checked lemmas with those exact schemas exist.
Until then it states the factorization law above and may attach the intuitive
interpretation only as a visibly non-checked author note.

`not_cbcBad_implies_uniform_outputs` and `mass_cbcBad_le`, or their eventual public
counterparts, are substantive mathematics.  They receive visible sentences
and are never absorbed as routine automation.

### 8.4 H-technique, couplings, reductions, and hybrids

These families are **later** until their theorem-level backends and complete
acceptance proofs exist.  They are specified now to prevent the first grammar
from hard-coding conditional equivalence as the only proof route.

| Route | Controlled form | Explicit semantic choices |
| --- | --- | --- |
| Condition C | `By Condition C using hCE, hGame, hIdeal, and hWeight, it suffices to prove ν[G] ≤ ε` | exact game/system pair, CE witness, and noncanonical mass premises; create the tagged comparison `Compare(WinningProbability(G, adaptive), atMost, ε)` |
| H-technique | `By the H-coefficient theorem, it suffices to prove the good-ratio and bad-mass bounds for Bad using realNonnegative, idealNonnegative, equalWeight, and idealWeightAtMostOne` | exact real/ideal laws, bad predicate, losses, and noncanonical mass premises; create tagged `goodRatio` and `idealBadMass` goals |
| H-technique | `For every transcript t outside Bad, idealLaw t ≥ (1 - ε) * realLaw t using hratio` | exact good predicate, transcript laws, and ratio/equality loss; a registered theorem may use an equivalent division-free orientation |
| H-technique | `idealLaw.mass Bad ≤ δ using hbad` | exact bad predicate, law, and bound |
| H-technique | `Combining the good-ratio and bad-mass bounds gives statDist(realLaw, idealLaw) ≤ ε + δ using hH` | both budgets and the named H theorem; exact orientation and loss expression come from its registered conclusion |
| coupling | `Using the joint law κ, it suffices to prove its two marginal identities and the disagreement bound` | exact joint law; create tagged left-marginal, right-marginal, and disagreement goals |
| coupling | `Under κ, the executions disagree with probability at most ε using hdisagree` | exact disagreement event and bound |
| reduction | `Using the reduction ρ from the comparison (R,S) to game G, it suffices to prove reductionCorrect ρ R S G and ν[G] ≤ ε` | explicit source comparison, target game, reduction object, exact registered correctness relation, and tagged game-bound obligation |
| hybrid | `It suffices to bound the two legs through H` | explicit intermediate system; create tagged real-to-intermediate and intermediate-to-ideal goals |
| representative selection | `Let R' be the representative of R selected by hsel` | representative and exact selection theorem |

The opening sentence of a route must expose named, ordered
obligations matching that route; it may not search among routes.  If a direct
paper theorem already packages the route, the proof may instead use an
explicit `... follows from fact` closing sentence.

In the table, every opening saying `it suffices` has
`GoalEffect.replaceMain` with the stated tagged obligations. Every line saying
`is at most`, `satisfies`, or `follows from` has `GoalEffect.closeMain` and must
carry the proof named after `by`, `using`, or `from`. `Let R' be ... selected`
has `GoalEffect.introduce` only when the supplied selection theorem directly
produces that witness; otherwise assistance emits an explicit existential
template rather than an assertive sentence.

The public H-coefficient endpoint has no reveal/transcript-extension operand
and no independent good predicate: “good” means `¬ Bad`. If an application
first constructs a reveal, representative, or transcript factorization, that
is a preceding named claim with its own schema or ordinary Lean proof, not an
extra hidden argument to the H-coefficient sentence.

### 8.5 Normative provenance assignment

Every controlled form above has a stable `SentenceFormId`; every form marked
public must additionally have at least one exact locator in its catalog entry.
The table below assigns the present source class per form. A grouped row is an
implementation inventory only and never licenses its forms by analogy.
`checkedLibrary` validates the exact proposition
and backend but is not, by itself, evidence that invented English is idiomatic.
`proposedPendingAttestation` is design-only and cannot be imported by the
public frontend. `projectControlled` identifies a reviewed composition of
independently licensed mathematical clauses and Lean-facing delimiters; it is
not a claim that a source uses the exact syntax.

| Sentence form IDs | Source class |
| --- | --- |
| `struct.factEnvelope` | `projectControlled`; the wrapped assertion keeps its own domain attestation; `struct.factBy` and `struct.factFrom` are rejected migration artifacts, not Massot-derived public forms |
| `struct.theoremDeclaration` | `projectControlled`; binder and conclusion clauses retain their own ontology/source records, and the full declaration must pass the differential contract |
| `struct.characterizedDefinition` | split provenance: `projectControlled` exact syntax; `primaryJost`, printed pp. 33–34, for MBO/event ontology; `primaryLiuMau20`, Definition 6, pp. 9–10, for definition plus equivalent characterization; `checkedLibrary` validates the exact relation |
| `struct.remains`, `struct.fix`, `struct.fixWith`, `struct.assume`, `struct.choose`, `struct.obtainConjunction` | `projectControlled`, with separate exact locators in this specification; Massot motivates the controlled-language architecture but is not falsely cited as the verbatim source of every form |
| `ac.construction.from`, `ac.construction.distanceReduction`, `ac.equality.from`, `ac.protocol.replace`, `ac.construction.serial`, `ac.simulator.use`, `ac.context.right`, `ac.context.left`, `ac.relaxation.compose`, `ac.filtered.from`, `ac.distance.triangleClose`, `ac.distance.triangleOpen`, `ac.construction.parallel`, `ac.simulators.compose`, `ac.availability.reduce` | `projectControlled` from the repository's deterministic AC proof-language contract, with `checkedLibrary` backend semantics; this is not a claim that MauRen16 or Jost uses the exact surface wording |
| `mr11.property.transfer` | MR11-deferred; no MR16 public registration |
| `rs.pds.transcriptEquivalent` | `primaryLanzenberger` plus `checkedLibrary` |
| `rs.pds.strictDistinguisherEquivalent` | `primaryJost` plus `checkedLibrary` |
| `rs.commonDomain.equivalent`, `rs.commonDomain.probabilityEquivalent` | `primaryLanzenberger` plus `checkedLibrary` |
| `rs.ambient.equivalent`, `rs.quotient.equal`, `rs.embedding.equal`, `rs.application.equal`, `rs.application.advantageBound` | `checkedLibrary`; public prose requires a separately attested domain frame, while exact-formula surfaces need none |
| `rs.commonDomain.preservesImage`, `rs.commonDomain.morphismBinder`, `rs.commonDomain.applicable` | `checkedLibrary` exact relations only; each English predicate frame remains `proposedPendingAttestation` until separately sourced |
| `rs.game.adjoinSubtype`, `rs.game.adjoinPDG`, `rs.game.forgetEqual`, `rs.game.forgetEquivalent` | exact relations are `checkedLibrary`; CR18 licenses only explicitly registered application occurrences, while every generic English frame remains `proposedPendingAttestation` until independently sourced |
| `rs.game.transcriptEquivalent` | `primaryLanzenberger` plus `checkedLibrary` |
| `rs.game.fixedListEquivalent`, `rs.game.conditionalEquivalent`, `rs.game.conditionalTransform`, `rs.game.conditionalDomainRestriction`, `rs.game.conditionalQueryRestriction` | exact relations are `checkedLibrary`; only application-scoped occurrences may use `cr18Fallback`, and generic public forms remain `proposedPendingAttestation` |
| `rs.conditionC.adaptiveClose`, `rs.conditionC.adaptiveReduce`, `rs.conditionC.blindClose`, `rs.conditionC.blindReduce` | exact inference schemas are `checkedLibrary`; CR18 licenses only registered application instances, not a generic public family; adaptive/blind and close/reduce forms have distinct `RuleId`s |
| `rs.winning.remainsAdaptive`, `rs.winning.remainsBlind` | `projectControlled` for the exact goal announcement and `checkedLibrary` for the exact quantity entry |
| `rs.blind.fixEnvironment`, `rs.blind.identifySchedule`, `rs.blind.defineAdmittedSchedule`, `rs.blind.winningMass`, `rs.blind.fixAdmittedList`, `rs.blind.listMassBound`, `rs.blind.liftListBound` | exact schemas are `checkedLibrary`; CR18 licenses only application-scoped occurrences, and these are not public general-RS vocabulary unless separately re-attested |
| `rs.collision.distinctTerminals`, `rs.collision.factorization`, `rs.collision.listMass`, `rs.collision.countWitnesses`, `rs.collision.birthday` | application-specific `checkedLibrary`; `cr18Fallback` is allowed only for the CBC/switching instances, never as a public concept name |
| `rs.route.conditionC` | exact route schema is `checkedLibrary`; CR18 licenses only an application-scoped route occurrence, while a generic public form remains `proposedPendingAttestation` |
| `rs.route.hCoefficientOpen`, `rs.route.hCoefficientRatio`, `rs.route.hCoefficientBadMass`, `rs.route.hCoefficientClose` | `checkedLibrary` for exact theorem signatures; the controlled forms remain `proposedPendingAttestation` until each has a source locator |
| `rs.route.couplingOpen`, `rs.route.couplingDisagreement` | `primaryLiuMau20` where the registered construction matches that route, otherwise `proposedPendingAttestation` |
| `rs.route.reductionOpen`, `rs.route.hybridOpen`, `rs.route.representativeSelect` | `primaryMauRen16` or `primaryJost` only when the registered rule has the cited shape; otherwise `proposedPendingAttestation` |

An implementation entry stores the exact work, page or section, and excerpt
fingerprint behind each source-class label.  The class table is therefore a
review index, not a substitute for those locators.

Registry reconciliation must also correct the current migration locator:
conditional equivalence itself is CR18 Definition 4.19, whereas Theorem 4.17 is
the advantage consequence. Those entries may not share the latter locator.

## 9. Statement and proposition layer

The comprehensive frontend includes theorem statements, but the declaration
syntax is downstream of the abstract binder and claim grammar.  A theorem
declaration has this semantic record:

```text
structure DeclarationPlan where
  kind : definition | lemma | theorem
  declarationName : Name
  readerTitle? : Option String
  universeBinders : Array UniverseBinder
  binders : Array TypedBinder
  assumptions : Array AnchoredClaim
  conclusion : Claim
  attributes : Array AttributeSyntax
  visibility : Visibility
  documentation? : Option String
```

`TypedBinder` retains explicit/implicit/instance status, dependencies, the
exact elaborated type, and its abstract-grammar entity kind.  The English
surface may group compatible binders—“Given a finite nonempty alphabet `X`
with decidable equality, and a query budget `q`”—only when it elaborates to the
same telescope as the ordinary declaration.  Otherwise it uses a more exact
typed form.  A word such as “resources” never licenses erasing the differences
among `DDS`, `PDS`, `PDG`, quotient systems, specifications, or converters
with typed boundaries.

The theorem-root conclusion is compiled from a typed relation schema.  Exact
notation is preferred when it makes the claim clearer; in particular,
`Adv⊥(S,T) ≤ ε` is not expanded into a long qualified Lean expression and is
never replaced by `Δ(S,T) ≤ ε`.  A canonical declaration layout may use
`Theorem`, `Given`, `Assuming`, `Conclusion`, `Proof`, and `QED`, but these are
surface delimiters around the semantic record, not the source of its meaning.

The opt-in `Theorem ... Given ... Conclusion ...` command now retains the exact
elaborated declaration type, telescope, conclusion, input presentations, title,
and assumption count. It supports exact Lean binders plus the checked
finite-nonempty-alphabet and natural-query-budget profiles used by switching.
It remains outside the root `Verbose` import until differential tests also
cover dependent binder groups, attributes, visibility, source navigation, and
asynchronous elaboration behavior. Ordinary Lean headers remain the fallback
outside the accepted experimental passage.

Readable proof bodies also require scoped notation for central propositions;
natural connective phrases around raw fully qualified terms are not enough.

### 9.1 Scoped Random Systems term grammar

The standard RS object notation is a standalone scoped term grammar, not a
branch inside a switching theorem command. In the `CryptoRandomSystems` scope
the first implementation has these exact parser productions:

```lean
scoped syntax:max "URF(" term "," term ")" : term
scoped syntax:max "URF(" term ")" : term
scoped syntax:max "URP(" term ")" : term
scoped syntax:65 "[" term "]" term:66 : term
```

They elaborate respectively to `PDS.urf X Y`, `PDS.urf X X`, `PDS.urp X`, and
`Switching.limit q S`. Restriction is deliberately non-associative at its own
precedence: a nested restriction requires parentheses. Elaboration checks that
the operand has the exact homogeneous PDS type required by `Switching.limit`;
the parser does not coerce an arbitrary system or infer a constructor from a
local name. The unexpander emits a notation only when the head constant and
arguments match one of these expansions and the result re-elaborates to the
same typed term. Otherwise it prints the qualified Lean expression.

Combined-import tests cover list literals, array/index notation, term
application on both sides, nested restrictions, explicit type ascriptions,
heterogeneous `URF(X,Y)`, and the homogeneous abbreviation `URF(X)`. Positive
round trips include the standalone terms `[q] URF(X)` and `[q] URP(X)`; negative
tests reject a heterogeneous restriction and any parse of `PDS.advFullyDefined`
as `Delta`/`Δ`.

### 9.2 Exact notation manifest

The first release freezes the following profile against the live declarations:

| Meaning | Exact declaration | Canonical source surface | Constraint |
| --- | --- | --- | --- |
| deterministic discrete-system presentation | `RandomSystems.System.DDS X Y` | `System.DDS X Y` | never call the DDS itself a law or abbreviate it to an untyped “system” binder |
| signed PDS presentation | `RandomSystems.PDS X Y` | `PDS X Y` | no nonnegativity, normalization, or common-domain witness is implied |
| subprobability property | `PDS.IsProbability P` | `PDS.IsProbability P` | nonnegative with weight at most one; not weight exactly one |
| game law | `RandomSystems.PDG X Y` | `PDG X Y` | signed law over `(DDS, MonotoneCondition)` pairs; the Boolean appears in `gameTrLaw`, not ordinary answers |
| game for a system | `PDS.GamesFor S` | `PDS.GamesFor S` | membership carries behavioral equivalence of `PDG.forget G` with `S`; it is not representative equality |
| fixed-interface behavior quotient | `PDS.Behaviour X Y` | `PDS.Behaviour X Y` | quotient by `PDS.equivalent` |
| game behavior quotient | `PDG.GameBehaviour X Y` | `PDG.GameBehaviour X Y` | quotient by full game-transcript equivalence |
| common-domain presentation | `RandomSystems.CommonDomain.Presentation X Y` | `CommonDomain.Presentation X Y` | nonnegative arbitrary-weight law with an explicit fixed domain |
| common-domain quotient | `RandomSystems.CommonDomain.RandomSystem X Y` | `CommonDomain.RandomSystem X Y` | quotient of nonnegative arbitrary-weight common-domain presentations |
| normalized common-domain presentation | `RandomSystems.CommonDomain.ProbabilityPresentation X Y` | `CommonDomain.ProbabilityPresentation X Y` | normalized law plus a fixed-domain witness |
| normalized common-domain quotient | `RandomSystems.CommonDomain.ProbabilityRandomSystem X Y` | `CommonDomain.ProbabilityRandomSystem X Y` | quotient of normalized common-domain presentations |
| normalized partial-system law | `Probability.Distribution.ProbDist (RandomSystems.System.DDS X Y)` | `Distribution.ProbDist (System.DDS X Y)` | used by `CommonDomain.embedPDS`; no dedicated PDS alias or common-domain witness |
| normalized query-indexed PDS presentation | `RandomSystems.MultiInterface.PDS (Interface.single X Y)` | exact qualified term | normalized law over query-indexed attempted-history DDSs |
| normalized query-indexed carrier | `RandomSystems.MultiInterface.RandomSystem (Interface.single X Y)` | exact qualified term | ambient quotient into which a normalized common-domain random system is embedded by `toAmbient` |
| uniform random function PDS | `RandomSystems.PDS.urf X Y` | `URF(X,Y)`; `URF(X)` only when both interfaces are definitionally `X` | notation elaborates directly to this constructor; never recover it from a local name or generated English |
| uniform random permutation PDS | `RandomSystems.PDS.urp X` | `URP(X)` | notation elaborates directly to this constructor |
| homogeneous query restriction | `RandomSystems.Switching.limit q S` | `[q] S` | only for the exact homogeneous PDS restriction; hence `[q] URF(X)` and `[q] URP(X)` are ordinary mathematical terms, not prose templates |
| signed partial PDE | `RandomSystems.PDE Y X` | `RandomSystems.PDE Y X` | `Distribution (System.DDE Y X)`; preserve this argument order and do not imply normalization |
| normalized ambient total PDE | `RandomSystems.Ambient.PDE X Y` | `Ambient.PDE X Y` | opt-in normalized law over total DDEs; preserve its distinct argument order |
| strict distinguisher | `RandomSystems.PDS.Distinguisher X Y` | `PDS.Distinguisher X Y` | a Unit-to-Bool converter protocol satisfying `IsDDC`, not a DDE plus an external test |
| total-environment transcript equivalence | `PDS.equivalent P Q` | `PDS.equivalent P Q` | fixed-interface presentation relation underlying `PDS.Behaviour` |
| strict-distinguisher equivalence | `PDS.Equivalent P Q` | `PDS.Equivalent P Q` | equality of acceptance mass for every strict distinguisher; not `PDS.equivalent` |
| query-indexed transcript equivalence | `MultiInterface.PDS.equivalent P Q` | exact qualified term | normalized attempted-history presentation relation |
| arbitrary-weight common-domain equivalence | `CommonDomain.Presentation.Equivalent P Q` | exact term or registered notation | common domain plus equality of transcript laws for every jointly compatible, stopping partial DDE |
| normalized common-domain equivalence | `CommonDomain.ProbabilityPresentation.Equivalent P Q` | exact term or registered notation | separate normalized-presentation relation; do not coerce it to the arbitrary-weight relation implicitly |
| conditional equivalence | `PDG.CondEquiv G T` | `G |≡ T` | game on the left, PDS on the right |
| full game-transcript equivalence | `PDG.gameEquivalent G H` | `PDG.gameEquivalent G H` | equality of observable game transcript laws for every total environment and horizon |
| fixed-list not-won equivalence | `PDG.EquivalentAsGames G H` | `G ≡ᵍ H` | agreement of not-won laws for every nonempty fixed query list; weaker than full game equivalence |
| compatible/stopping PDS advantage | `PDS.Adv S T` | `Adv(S, T)` | `ENNReal`; supremum over partial DDEs compatible with and stopping on both presentations; the observer family depends on `S` and `T` |
| fixed-domain PDS advantage | `PDS.AdvD D S T` | `PDS.AdvD D S T` | `ENNReal`; supremum over `e` satisfying `System.CompatibleD e D ∧ System.DDE.Halts e`; the definition does not itself assert that `S` and `T` present `D` |
| query-indexed PDS advantage | `MultiInterface.PDS.advantage S T` | exact qualified term | keep the qualified name; normalized attempted-history carrier |
| fully-defined advantage | `PDS.advFullyDefined S T` | `Adv⊥(S, T)` | `ENNReal`; do not collapse into `Adv` |
| static class distance | `PDS.classDistance S T` | `Δ(S, T)` | `ENNReal`; not interactive advantage |
| quotient distance | `edist S T` on a registered quotient carrier | `edist S T` | retain the carrier and defining metric: `PDS.Behaviour` symmetrizes `Adv⊥`, ambient systems use ambient advantage, and normalized common-domain systems use their embedding metric; the arbitrary-weight common-domain quotient has no registered `edist` |
| adaptive winning | `PDG.supWinProb G` | `ν(G)` / `ν[G]` | round parentheses are `Real`; brackets are `ENNReal.ofReal` |
| blind winning | `PDG.blindSupWinProb G` | `νᴺᴬ(G)` / `νᴺᴬ[G]` | distinct from adaptive winning |
| static winnability | `PDG.infWinnability G` | `ω(G)` / `ω[G]` | distinct from either winning supremum |
| DDS converter application | `RandomSystems.Converter.DDC.apply α S` | `α ·ᶜ S` | typed boundaries and application order remain visible |
| signed PDS law pushforward | `RandomSystems.PDS.applyLaw α P` | `PDS.applyLaw α P` | deterministic partial DDC pushed through a possibly signed PDS law |
| query-indexed PDS application | `RandomSystems.MultiInterface.PDS.apply α P` | exact qualified term | normalized attempted-history presentation; do not overload `·ᶜ` across carriers yet |
| global common-domain quotient application | `CommonDomain.ProbabilityRandomSystem.apply α R` | exact qualified term | `α : CommonDomain.DDC U V X Y` packages global preservation of the embedded normalized common-domain image |
| specification-local common-domain application | `RandomSystemsCC.CommonDomainApplicable.apply α applicable R admitted` | exact qualified term | retains the source-specific applicability and resource-membership witnesses; its ambient image is related by `toAmbient_apply` |
| query-limit converter | `RandomSystems.Converter.DDC.queryLimit q` | `[q]ᶠ` and `[q]ᶠ ·ᶜ S` | distinguish the converter from a filtered PDS |
| MBO enhancement | `PDS.adjoin S A` | `PDS.adjoin S A` | `A : DDS X Y → MonotoneCondition X`; result is `GamesFor S`, with underlying PDG `(PDS.adjoin S A).1` |
| forget the monotone condition | `PDG.forget G` | `PDG.forget G` | project a law on `(DDS, MonotoneCondition)` to its DDS law; no bit is removed from ordinary answers |
| not-won law | `PDG.notWonLaw e n G` | `PDG.notWonLaw e n G` | unnormalized transcript law on the false-MBO slice; retain environment and horizon |
| AC approximate construction | `AbstractCryptography.ApproximatelyConstructs π ε R S` | `R —[π; ε]→ S` | keep distinct from RSCC categorical construction |
| ambient categorical RS construction | `AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin ...` with `Phi := Interface.randomSystems` | registered construction notation or exact term | converter comes first in the checked relation; distinguish it from common-domain and non-categorical AC construction relations |
| RSCC common-domain morphism construction | `RandomSystemsCC.CommonDomainCategorical.ConstructsWithin source morphism target error` | registered construction notation or exact term | converter operand is a global common-domain `Morphism` |
| RSCC specification-local construction | `RandomSystemsCC.CommonDomainApplicable.ConstructsWithin source converter applicable target error` | registered construction notation or exact term | retains the separate `ApplicableTo` witness; never merge it with the morphism relation |

This is a manifest, not a wish list. Stage 0 records each notation's owning
module, scope, precedence, pretty-printer/unexpander behavior, and one source
round-trip receipt. Stage 3 cannot begin until combined-import parsing and
negative ambiguity tests freeze it. Any added notation must be a transparent
alias for one exact existing predicate or term; it must not merge relations or
hide a stronger assumption. Carrier/interface types remain explicit in
binders until a proposed binder grammar can infer them uniquely and passes
ambiguity tests.

## 10. CBC acceptance proof

CBC is an acceptance case, not a source of theorem-specific grammar. It is a
suite of nested proofs with different formal conclusions; flattening them into
one attractive paragraph would be mathematically false. The section records
the semantic contracts that the migrated public endpoints must satisfy. It
is checked against the currently elaborating `Applications.CBCMAC.Probability`
and `Applications.CBCMAC.Construction` sources.

The accessibility ledger records what can currently be named, but it is not
the signature authority:

| Live declaration | Access from sister project | Expected semantic node |
|---|---|---|
| `CBCCombinatorics.not_cbcBad_implies_uniform_outputs` | public | collision-free mass factorization |
| `CBCMAC.collisionCondition` / `CBCMAC.collisionGamePDS` | source-private | collision-event assignment and game object contract |
| `CBCMAC.collisionGame_condEquiv` | source-private | base `CondEquiv` application; requires a public semantic seam for a complete Verbose proof |
| `CBCMAC.filterDDS` / `CBCMAC.restrictedCollisionGamePDS` | source-private | admitted-history restriction and filtered game object contract |
| `CBCMAC.restrictedCollisionGame_condEquiv` | source-private | domain-restriction preservation; requires a public semantic seam |
| `CBCMAC.blindSupWinProb_restrictedCollisionGamePDS_le` | source-private | non-adaptive schedule reduction; requires a public semantic seam |
| `CBCCombinatorics.mass_cbcBad_le` | public | fixed-list collision-mass comparison |
| `CBCMAC.restricted_advFullyDefined_le_blind` | source-private | CE-to-blind comparison; requires a public semantic seam |
| `CBCMAC.applySystem_theta` | public; manifest-checked | exact block-count restriction/application equation |
| `CBCMAC.cbc_distance_le` | public; manifest-checked | ambient random-system distance bound obtained from the PDS advantage bound |
| `CBCMAC.cbc_constructs_within` | public; manifest-checked | categorical construction through serial `theta`/CBC attachment |

Private entries are not dispatched by discovered names. Stage 5 is blocked
until stable public endpoints satisfy every semantic-node contract in the
ledger. A smaller public interface is sufficient only if its checked result
and registered eliminators entail all required nodes and role assignments.

The opt-in fixture `tests/VerboseTests/CBCSignatureManifest.lean` records the
current compiled public surface and is regenerated against the live sibling
checkout. For every accessible endpoint, it checks a generated
Meta snapshot of the declaration owner, visibility, universe arity, full
elaborated telescope, result head, normalized proposition fingerprint, and one
stable semantic role label for every telescope position. The snapshot fails on
binder reordering, changed implicit assumptions, scalar/carrier drift, a
changed owner or visibility, or a changed result proposition. The ordinary
Lean examples below it independently check the readable propositions.
A private endpoint has no sister-project manifest entry: its required public
replacement is instead a hard missing row. The prose in Sections 10.1--10.6 is
explanatory and cannot override these compiled checks. The Stage 5 entry gate
therefore remains unsatisfied only for the rows that still lack public semantic
paths, not for missing signature machinery.

### 10.1 Base conditional law

The public substantive endpoint is
`CBCCombinatorics.not_cbcBad_implies_uniform_outputs`.  The compiled manifest
stores its full proposition.  In paper notation, its mass identity is

```text
mass_uniform(X→X)(CBC answers ∧ ¬ cbcBad)
  = mass_uniform(M→X)(the same message answers)
      * mass_uniform(X→X)(¬ cbcBad).
```

The private caller `collisionGame_condEquiv` has conclusion
`PDG.CondEquiv (collisionGamePDS blockForm) (PDS.urf M X)`.  Its realizable
branch uses that factorization; the non-realizable branch and distribution
bookkeeping remain ordinary Lean.  Factorization and conditional equivalence
are separate semantic nodes.

The terminal-input injectivity/freshness argument is currently internal to the
CBC combinatorics proof. It may be visible in an optional deeper expansion of
the factorization node, but it cannot receive its own controlled sentence until
a stable theorem with that exact conclusion is extracted.

### 10.2 Domain restriction

`restrictedCollisionGame_condEquiv` is a distinct proof. It defines the
total-block predicate and uses `PDG.condEquiv_filterDom`, not `theta`.  Its
conclusion is

```text
PDG.CondEquiv
  (restrictedCollisionGamePDS blockForm limit)
  (Distribution.fTransform (filterDDS blockForm limit) (PDS.urf M X)).
```

The semantic application records the total-block predicate, its prefix-closure
proof, the two side-specific never-refusal witnesses, and the base `CondEquiv`
premise.  A licensed surface says that restricting the game and ideal system
to admitted histories preserves conditional equivalence.  `theta blockForm
limit` does not occur at this stage.

### 10.3 Blind winning and the fixed list

The generic blind bound begins with the actual universal eliminator and hence
introduces a total environment `E`, a proof `hE : NonAdaptive E`, and a horizon
`n`.  Against the explicit filtered constant reference system, the checked
transcript determines `messages`; the admitted list is exactly
`PDG.Plumbing.filterAdmit predicate messages`.  The checked local identity is
not yet an external contract; its abbreviated shape is

```text
PDG.winningMass E n (restrictedCollisionGamePDS blockForm limit)
  = (uniform (X → X)).mass
      (fun f => cbcBad f blockForm (filterAdmit predicate messages)).
```

The public per-list endpoint `CBCCombinatorics.mass_cbcBad_le` is frozen by the
compiled signature manifest; in abbreviated paper notation its conclusion is

```text
(uniform (X → X)).mass (fun f => cbcBad f blockForm messages)
  ≤ limit * (limit - 1) / (2 * |X|)
```

under `totalBlocks blockForm messages ≤ limit`.  The reference system,
transcript, schedule identification, admission filter, mass identity, and
collision estimate remain distinct semantic acts.  The frontend may not jump
from a blind environment to an arbitrary list.

### 10.4 Ambient distance and converter application

The live CBC proof uses the ambient attempted-history carrier. The substantive
probability argument concludes at `realPDS_advantage_le`; `cbc_distance_le`
then uses `RandomSystem.edist_ofPDS_eq` to identify quotient distance with the
already established PDS advantage. The categorical endpoint uses
`RandomSystem.apply_ofPDS_eq` and `PDS.apply_serial_eq` to expose CBC followed
by the public block-count restriction. These equalities are checked carrier
and serial-application bridges; they do not introduce a common-domain
data-processing theorem into this proof.

### 10.5 Distance and construction

The migrated distance theorem must state its bound directly on the selected
normalized quotient. The construction theorem then performs singleton
membership and serial converter application bookkeeping before using that
distance theorem. Its exact root types remain a compiled-manifest question;
the pre-migration shapes below are illustrative only and may not license a
backend:

```text
edist (RandomSystem.ofPDS (realPDS blockForm limit))
      (RandomSystem.ofPDS (idealPDS blockForm limit))
  ≤ CBCCombinatorics.cbcEpsilon X limit
```

and
`AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin`
with `Phi := Interface.randomSystems`, from the singleton
restricted-round-function specification, through
`DDC.serial (theta blockForm limit) (cbc blockForm)`, to the singleton ideal
PDS specification within the same error.  The controlled proof must expose
singleton source membership, the ideal witness, and serial application order.
Ordinary `exact cbc_distance_le ...` closes the final distance goal; no generic
English wrapper is added.  A construction-specific sentence is licensed only
if its backend checks the complete `ConstructsWithin` characterization.

Across the suite, the visible mathematical spine is therefore:

```text
collision-free CBC mass factorization
  -> base conditional equivalence
  -> common-domain filtering on both sides
  -> fully-defined advantage bounded by blind winning
  -> non-adaptive environment and reference-induced admitted list
  -> CBC collision mass bound
  -> PDS advantage bound
  -> ambient random-system distance
  -> serial construction
```

`not_cbcBad_implies_uniform_outputs`, `mass_cbcBad_le`, and
the PDS-to-ambient distance conclusion remain visible. No step may
describe `filterDDS` as `theta`, factorization as conditional equivalence, or
an arbitrary admitted list as the list induced by a blind environment.

No public sentence may mention `rw`, `simpa`, `grind`, `omega`, theorem
telescope positions, `Subtype` packaging, or internal helper names as the
mathematical subject.

## 11. Backend discipline

### 11.1 Named theorem before sentence

A recurring obligation must first have a stable mathematical theorem or
deterministic backend.  A sentence is added only when applying that result is
itself a conventional paper step.  The grammar must not become a workaround
for a missing semantic API.

### 11.2 Permitted automation

A backend may:

- elaborate explicitly supplied terms;
- infer implicit parameters fixed uniquely by those terms and the goal;
- use canonical typeclass instances;
- apply one supplied theorem or one rule from a unique curated registry;
- perform small, named, shrinking normalization required to match the rule;
- introduce binders whose roles are fixed by the current goal; and
- close routine side conditions from a documented, local registry when the
  sentence's contract says so.

A backend may not:

- select a cryptographic proof route or mathematical object;
- run unrestricted `simp`, `aesop`, `grind`, environment search, or theorem
  search;
- try a long ordered list of semantically different theorems;
- use typeclass search for non-canonical proof witnesses;
- silently unfold a public specification or complete system implementation;
- solve a different goal and coerce the result into the intended one; or
- create names used later in the proof.

### 11.3 Normalization boundary

Small reconciliation rewrites are registered by semantic owner and oriented
toward one documented normal form.  Each rewrite needs a firing-site test and
a termination argument by syntactic shrinking or a simple measure.  A
sentence diagnostic reports when its semantic rule matches but normalization
does not; it does not fall back to broader simplification.

## 12. Diagnostics

Good errors are part of the frontend, not optional polish.  Every failure is
classified as one of:

1. **Grammar:** after a sentence family has been recognized, an expected fixed
   word, delimiter, or operand is wrong.
2. **Operand elaboration:** a named term is unknown or has the wrong type.
3. **Role mismatch:** a system, game, converter, condition, or scalar appears
   in the wrong semantic position.
4. **Goal mismatch:** the sentence's conclusion does not match the current
   goal after permitted normalization.
5. **Missing premise:** the chosen deterministic rule needs an explicit
   premise not supplied by the sentence.
6. **Ambiguous rule:** more than one registered rule with different semantics
   applies.
7. **Postcondition:** the backend produced a goal shape different from its
   declared `GoalEffect`.
8. **Stale guidance:** a presentation annotation no longer matches its
   semantic anchor.
9. **Inactive scope:** the likely sentence is recognized lexically but its
   owning language scope is not open.
10. **Name collision:** a produced name is already bound or would shadow a
    protected declaration.

An ordinary diagnostic should state:

- the mathematical act attempted;
- the relevant supplied operand;
- the expected relation or goal shape;
- the actual goal or type in reader notation; and
- one concrete next action, normally a corrected sentence skeleton or the
  missing explicit premise.

It should not lead with the backend tactic name, metavariable IDs, parser
internals, or a raw kernel term.  A debug option may reveal those details.

There is an implementation boundary: a spelling that fails before Lean
recognizes any controlled prefix receives Lean's ordinary expected-token
parser error. Likewise, syntax from an unopened scope cannot diagnose itself;
inactive-scope advice belongs to editor assistance or an always-imported
diagnostic command. A lower-priority catch-all parser may be added only if
ambiguity and performance tests show that it does not steal valid Lean syntax.

Example shape:

```text
Cannot filter conditional equivalence by `predicate`.
The current goal filters only the game; this rule requires matching
`filterDom predicate` transformations on the game and the system. State the
asymmetric transformation as an ordinary Lean lemma or prove a matching
preservation theorem first.
```

## 13. Help and editor assistance

Massot's implementation demonstrates that an easy frontend needs more than
syntax.  The first usable release therefore includes contextual help rather
than postponing it until after the grammar is large.

### 13.1 Commands

The public interface includes:

```text
crypto_help                    explain the current goal and relevant families
crypto_help hypothesisName     explain useful deterministic uses of one fact
crypto_suggest                 list copyable sentences for the current goal
#crypto_verbose_sentences      browse canonical forms grouped by layer, family, and act
#print_crypto_verbose_config   print the active profile and registries
```

Names may change to avoid an upstream collision, but the functions may not.

### 13.2 Suggestions

A suggestion or template contains typed syntax, not only display text:

```lean
structure InsertableSuggestion where
  formId : SentenceFormId
  syntax : Lean.Syntax
  summary : MessageData
  expectedEffect : GoalEffect
  confidence : SuggestionConfidence

structure SentenceTemplate where
  formId : SentenceFormId
  syntaxWithHoles : Lean.Syntax
  summary : MessageData
  missingOperands : Array ArgumentRole
```

Every `InsertableSuggestion` must be dry-elaborated transactionally in a copy
of the proof state from which it was generated. A `SentenceTemplate` is not
advertised as insertable; its holes are visible and it names every missing
semantic role. Suggestions may use the current goal,
local context, explicit editor selection, and curated rule indices.  They may
not choose an ideal system, simulator, condition, reveal, coupling, schedule,
or intermediate resource.

When several rules are mathematically distinct, assistance groups them by
route and asks the author to choose; it does not rank one as the intended
proof.

### 13.3 Selection

Editor selection may populate explicit terms for theorem application,
construction legs, contexts, restrictions, or bounds.  Selection is a data
entry aid only.  The same generated sentence must pass ordinary elaboration
after insertion.

### 13.4 Configuration

Configuration is persistent, inspectable, and module-owned.  It may control:

- active language and domain profile;
- help/widget enablement;
- curated normalization and routine side-condition registries;
- suggestion providers;
- whether optional unfolding suggestions are shown; and
- debug traces.

The research profile does not permit configuration to enable unrestricted
search or to make non-canonical choices implicit.  Source files that depend on
non-default semantic behavior should configure it explicitly near their
imports.

## 14. Interoperability

- Any tactic sequence can mix controlled sentences and ordinary Lean.
- A controlled sentence may contain an ordinary tactic block in the proof of
  an explicitly stated named claim.
- Ordinary `calc` is the preferred notation for a heterogeneous or long
  equality/inequality chain unless a domain sentence captures a higher-level
  theorem application.
- Ordinary `cases` and induction are preferred when the case split or
  induction principle is itself the mathematical exposition.
- Routine arithmetic may use the project's accepted tactics inside a named
  scalar lemma; public domain sentences describe the resulting bound, not the
  tactic.
- Opening `CryptoVerbose` must coexist with the existing AC notations and with
  terms named by ordinary English words.
- The compiled proof has no runtime dependency on the editor widget.

The informalizer may consume successful sentence events as presentation
provenance, but it must reconstruct and validate their mathematical meaning
from the elaborated proof.  An ordinary Lean proof with the same canonical
derivation remains fully supported.  Source-specific sentence boundaries and
annotations may legitimately cause different presentation choices.

## 15. Test contract

Each sentence family is incomplete until all applicable test classes pass.

### 15.1 Per-sentence tests

- **positive:** the sentence proves every documented goal variant;
- **negative:** wrong relation, operand role, converter order, restriction
  side, event, bound, or missing premise fails locally;
- **grammar:** misspelled fixed words and malformed continuations produce the
  controlled diagnostic;
- **trace/event:** exactly one stable successful event is emitted after
  lowering;
- **transaction:** each failure leaves the original goal and local context;
- **scope:** the sentence is unavailable before opening the scope;
- **identifier:** all common prose words remain usable as names;
- **prefix:** sentence alternatives diverge at the earliest stable token and
  do not create grammar garden paths;
- **term boundary:** terms containing commas, `and`, `using`, `from`, strings,
  applications, and prose-like identifiers parse in every operand slot;
- **annotation:** reader notes do not affect elaboration or the proof term;
- **performance:** on a fixed fixture, record the direct-backend heartbeat
  baseline; controlled success and each classified failure must stay below
  `max 50000 (2 * baseline)` without a local `maxHeartbeats` override.

### 15.2 Backend-equivalence tests

For every sentence, a paired ordinary proof invokes the documented backend or
theorem directly.  Both proof the same proposition and expose the same ordered
obligations.  Important endpoints receive `#print axioms` checks.

### 15.3 Assistance tests

- every displayed insertable suggestion is parser-valid;
- insertion into the captured proof state elaborates successfully;
- suggestions never fill a non-canonical semantic choice;
- ambiguous routes are grouped and left to the author;
- the help text names the mathematical consequence, not the implementation;
- selecting a term cannot change which goal is active; and
- assistance disabled by configuration has no elaboration effect.

### 15.4 Complete-proof acceptance corpus

Isolated sentences are insufficient.  The suite includes complete, genuine
proofs for:

1. exact and approximate AC construction closure;
2. serial, parallel, context, simulator, filtered, and property-transfer
   composition;
3. URF/URP switching through conditional equivalence and blind winning;
4. the CBC construction through the proof spine in Section 10;
5. one H-technique proof;
6. one coupling or representative-selection proof;
7. one hybrid or game-hop proof; and
8. one proof that deliberately mixes controlled sentences with ordinary
   `have`, `calc`, cases, and arithmetic.

For each complete proof, review both source and editor behavior:

- the proof spine is visible without reading backend tactic names;
- the sentence subjects stay in the correct construction, system, game, law,
  and scalar registers;
- repeated sentence openings do not make the paragraph wooden;
- references and pronouns are unambiguous;
- formulas remain recognizable Lean rather than faux English;
- diagnostics recover from at least three realistic author mistakes; and
- an experienced author can discover the intended sentence with help rather
  than reading implementation source.

### 15.5 Mutation and forbidden-pattern tests

Mutate each acceptance proof by swapping serial converters, changing real and
ideal systems, removing prefix-freeness, weakening non-adaptivity, changing the
bad condition, applying a restriction to one side only, or changing the
budget.  The corresponding controlled step must fail or produce a genuinely
different checked proposition.

Production grammar and backends are scanned for:

- theorem-specific declaration-name branches;
- local-variable-name triggers;
- tactic-spelling interpretation;
- unrestricted search tactics;
- hidden heartbeat increases;
- automatically invented cryptographic objects; and
- raw English strings in the language-independent core.

The test suite enforces two distinct round trips:

- canonical rendering of a `RuleInvocation`, verified outer `GoalEffect`, and
  role-indexed reference/name plan—and, for an assertion, its destination,
  exact conclusion, evidence root, and preserved `ProofSurface`—reparses to a
  `SentenceIntent` that elaborates back to the same occurrence; and
- legacy and canonical surface forms that intentionally share a rule elaborate
  to the same `RuleId`, role-labelled operands, and intrinsic effect. A legacy
  generic local proposition acquires a `Fact` envelope only when semantic
  recovery proves that it is the same registered assertion.

English may ship first, but the core stores no English word order or
prepositions. A later language pack is complete only when every public
`RuleId` has a parser, canonical renderer used by help, and diagnostic
implementation.

## 16. Usability and readability gates

A build is not a usability result.  Before a sentence family becomes public:

1. **Corpus attestation:** its mathematical terminology and predicate frame
   occur in the governing literature. The exact Lean-facing scaffold may be
   new when term holes or proof status require it; a coincidental full sentence
   match is neither required nor sufficient.
2. **Whole-proof reading:** it has been judged in a complete proof, not as an
   isolated slogan.
3. **Information gain:** it communicates a mathematical relation or goal shift
   more clearly than the ordinary Lean it replaces.
4. **Predictability:** two authors given its documentation can predict the
   accepted goal shape and resulting obligations.
5. **Discoverability:** `crypto_help` or the widget can produce a usable
   skeleton from a realistic stuck state.
6. **Failure recovery:** a wrong operand produces a correction the author can
   act on without opening the backend source.
7. **Composability:** it reads naturally immediately before and after ordinary
   Lean and other controlled sentences.
8. **No false fluency:** the sentence cannot read as a true crypto claim while
   proving only a weaker or structurally different Lean goal.

The review unit is a page-sized proof.  Reviewers record concrete awkward or
misleading passages and proposed corrections; a bare numerical naturalness
score is not sufficient.

## 17. Implementation stages

### Stage 0: freeze the abstract grammar and migration audit

- Treat [`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md), especially Section 6, as
  the normative catalog contract.
- Accept the complete passages required by the breadth gate in
  [`LANGUAGE_REFERENCE_CORPUS.md`](LANGUAGE_REFERENCE_CORPUS.md); isolated
  sentence examples do not freeze a grammar.
- Map every existing `ConceptId`, `RelationId`, `RuleId`, sentence form, and
  notation to **retain**, **refine**, **replace**, or **remove**.
- Move the raw named-proposition `Fact`, “call this fact,” unattested generic
  game-equivalence, and multi-act fixed-schedule forms out of active imports;
  keep negative fixtures for the false distinctions they exposed. Evaluate the
  proposed theorem header only through its differential declaration contract.
- Run a narrow source/API probe against Massot's implementation and the live
  RS declarations, but copy no grammar whose semantic record is incomplete.

Gate: the breadth corpus is accepted, and every active or migration-target form
has one catalog entry, exact carrier and relation indices, source attestation,
and an owning backend contract. Deferred forms need an exact source endpoint
and semantic schema; their backend contract is a gate of their own route stage.

### Stage 1: implement the typed shared catalog

- Retain the existing stable IDs, operand roles, canonical semantic terms, and
  checked evidence structures.
- Implement `ConceptEntry`, constructor schemas, indexed relation frames,
  context predicates, inference schemas, and source-attestation metadata.
- Validate all entries at registration: result indices, valency, selectional
  restrictions, permitted contexts, and duplicate IDs.
- Add exact entries for presentation levels, environments, games and game
  relations, laws, events, all distance/advantage quantities, specifications,
  and constructions before adding surface syntax.
- Implement a total `CatalogView` for every constructor of every existing
  canonical term. Unsupported/opaque nodes retain their exact source, type,
  and original constructor instead of being coerced into a known index.

Gate: constructor-by-constructor tests prove `CatalogView` totality, round-trip
the retained source and type, and preserve the old semantic fingerprint before
the stored representation changes. Catalog tests also reject every deliberate
carrier, domain, mass, game-law, strategy, and quantity mismatch in Sections
4.2 and 9.

### Stage 2: adapt the existing lowering and observability architecture

- Retain transactional lowering, explicit operand provisioning, goal effects,
  and typed events; refine them to point to the new catalog schemas.
- Adapt accepted AC sentences through compatibility registrations; change or
  retire public spelling when it violates the shared grammar.
- Emit typed custom `InfoTree` nodes and move English diagnostics out of the
  language-independent layer.
- Replace reserving prose atoms with `&"word"` and add combined-import parser
  and rollback tests.

Gate: retained workflows compile, rejected legacy forms fail deliberately,
and every successful event records one verified semantic act.

### Stage 3: structural, statement, and assistance surfaces

- Implement only the structural forms in `VERBOSE_SPEC.md` Section 6 that
  survive whole-proof review; the accepted set is enumerated there.
- Implement the declaration layer in Section 9 only after its differential
  declaration-contract tests pass; until then ordinary headers remain active.
- Implement `crypto_help`, typed suggestions, canonical rendering, and printed
  configuration early enough to drive usability tests.

Gate: a theorem with dependent binders, instances, attributes, documentation,
and a notation-rich conclusion elaborates identically to its ordinary Lean
counterpart, and an author can discover each accepted sentence without reading
backend code. The structural gate additionally requires the `Fact NAME:`
envelope to compose with every admitted assertion destination, to reject every
non-assertion rule, and to preserve the wrapped assertion's semantic identity.
Help emits a fillable anchor plus an assertion-specific skeleton; it never
rewrites a generic `We have` into `Fact`.

### Stage 4: reusable Random Systems slices

- Implement carrier/presentation declarations and bridges first; then typed
  converter application; then exact system/game relations; then laws, events,
  quantities, and proof moves.
- Freeze the Section 9 notation manifest before prose refers to its symbols.
- Reuse public RS theorems; add deterministic `rs_*` backends only when
  applying a stable theorem is itself a conventional paper step.
- Use switching as a cross-cutting acceptance proof, not as vocabulary.

Gate: switching reads as a coherent proof; standalone `[q] URF(X)` and
`[q] URP(X)` parse, elaborate, unexpand, and reparse; `Adv⊥` is never printed as
`Δ`; and the old theorem-specific `Δ = PDS.advFullyDefined` shortcut is rejected.
Routine canonical properties are absent, while positive and negative
`rs_routine` boundary tests prove that every successful run consists only of
uniformly decreasing sound registered rewrites followed, when needed, by one
sound registered closer, all within the fixed cost budget. It cannot establish
conditional equivalence, choose semantic objects, or discharge
collision/uniformity mathematics. All negative semantic mutations fail for the
intended reason.

### Stage 5: CBC acceptance slice

Entry gate: every required semantic-node contract in Section 10 has a
manifest-checked public derivation path owned by the appropriate semantic
module. A path may use one direct public replacement or a smaller public
interface whose checked eliminators entail several nodes; private declaration
discovery is never a path. The compiled CBC signature manifest must match each
path's full telescope, result, role assignment, and proposition fingerprint.
Until all rows pass, Stage 5 does not start.

- Add reusable collision-free factorization, common-domain filtering,
  blind-list, application-bridge, and mass-bound forms only through generic RS
  schemas.
- Add a terminal-input form only after the stable theorem required by Section
  10.1 exists.
- Do not introduce paper numbers, author names, or CBC theorem names into
  generic grammar dispatch.

Gate: the genuine construction proof exposes every transition in Section 10,
`not_cbcBad_implies_uniform_outputs` and `mass_cbcBad_le` remain visible, and the
whole proof passes source-grounded linguistic review.

### Stage 6: additional proof routes

- Add H-technique, coupling, reduction, representative selection, hybrids,
  signed expansion, and counting one route at a time.

Gate for each route: exact theorem-level backend, role-labelled residual
obligations, representative complete proof, negative route-confusion tests,
usable help, and source-corpus review.

## 18. Definition of done

The first comprehensive release is done only when:

- the architecture and module boundaries in Sections 3--4 are implemented;
- every public family has its complete test contract and source attestation;
- switching and CBC compile as genuine complete proofs in the frontend;
- the H-technique, coupling/representative-selection, and hybrid/reduction
  route families have each passed their Stage 6 gate;
- help and suggestions are available for all public families;
- no sentence asserts an obligation that remains as a residual goal;
- no frontend sentence chooses a non-canonical cryptographic object or proof
  route;
- all public sentences have passed page-sized readability review;
- the external project builds against the current supported
  `abstract-crypto` revision with the matching toolchain;
- public endpoints pass build, forbidden-pattern, and axiom checks; and
- `/informalization` remains able to process equivalent ordinary Lean without
  importing `/verbose`.

## 19. Source map

- Patrick Massot, *Teaching Mathematics Using Lean and Controlled Natural
  Language*, ITP 2024, especially the separation of language syntax from
  tactic implementation, explicit forward/backward steps, goal reminders,
  contextual help, typed suggestions, and configurable anonymous routines.
- Patrick Massot, `verbose-lean4`, especially `Verbose/Tactics`,
  `Verbose/English`, `Verbose/Infrastructure/Multilingual.lean`,
  `HelpInfrastructure.lean`, and the configuration and widget modules.
- Maurer--Renner 2016, then Jost, Liu--Maurer 2020, and Lanzenberger, in the
  repository's binding source order, for construction, Random Systems, events,
  games, adaptive winning, winnability, advantage, and distance language.
- The checked library and Coretti--Rösler 2018 only as the fallback corpus for
  the MBO-enhancement/forgetting, conditional-equivalence, blind-winning, CBC,
  and switching slice, subject to the repository's provenance fence.
- [`LANGUAGE_DESIGN.md`](LANGUAGE_DESIGN.md) for shared ontology, registers,
  bridge relations, predicate frames, and proof-independent author guidance.
- [`SPEC.md`](SPEC.md) for the separate semantic informalization pipeline.

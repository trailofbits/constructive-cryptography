# Ontology and language design

This document specifies the semantic and linguistic contract for generating
idiomatic mathematical prose from checked Lean.  It is deliberately broader
than the CBC example: the same paragraph may move from a constructive-
cryptography statement to random systems, games, probability laws, and a
scalar estimate.  Those changes of level must be represented rather than left
for the surface renderer to guess.

This is a reusable architecture document, not a progress report.  It refines
the shorter requirements in [`DESIDERATA.md`](DESIDERATA.md); implementation
details and acceptance gates remain in [`SPEC.md`](SPEC.md).
The author-facing use of this shared design is specified separately in
[`VERBOSE_SPEC.md`](VERBOSE_SPEC.md); it is not a stage of informalization.

## 1. Provenance labels

Every claim in this design should be read with one of these labels:

- **KYLE:** directly visible in Kyle Miller's ICERM talk: an ontology of
  concepts, properties, and relations; theorem-paragraph entities with nouns,
  adjectives, and accessories; entity and proposition explainers; tactic-tree
  describers; and a structured, expandable `Explanation` document.
- **KYLE-DERIVED:** behavior reproduced by this package's Massot--Miller path,
  including two-pass entity construction, introduction aggregation, agreement,
  and exact-expression fallback.
- **MASSOT-VERBOSE:** facts about Patrick Massot's separate Verbose Lean
  authoring project.  Verbose Lean concerns how a user writes Lean; it is not a
  stage of this informalization pipeline.
- **PRIMARY:** vocabulary and semantic relations taken from the repository's
  binding source hierarchy: Maurer--Renner 2016, then Jost, Liu--Maurer 2020,
  and Lanzenberger.  These govern AC/CC, random systems, games, and winning
  probability in that order of authority.
- **CR18-FALLBACK/CORPUS:** CBC-specific content and examples of mathematical
  exposition from Coretti--Rösler 2018.  This is fallback-only mathematical
  provenance under the repository rules, but it is also a valuable linguistic
  test corpus.
- **LEAN:** objects and proof boundaries present in the checked libraries,
  especially `Applications.CBCMAC` and `RandomSystems`.
- **PROPOSED:** a new representation or inference rule required by this
  informalization project.

Kyle's talk does **not** specify the checked evidence graph, canonical crypto
AST, proof genres, evidence-compression coverage, or the clause/discourse grammar below.
Those are project extensions.  The talk also presents a specification for
tactic describers as future work, so it must not be treated as a complete
published rulebook for proof prose.

Kyle Miller's informalization work and Patrick Massot's Verbose Lean must not
be conflated.  The former explains a checked development for a reader; the
latter offers controlled natural language as one way to author Lean.  A proof
written with Verbose Lean is ordinary checked Lean by the time this project
receives it.

## 2. The main linguistic problem

The proof does not remain at one descriptive level.  A typical CBC paragraph
crosses the following registers:

```text
construction claim
  -> attached real and ideal systems
  -> game obtained by enhancing the real system with a collision MBO
  -> conditional transcript/output law
  -> blind or non-adaptive winning probability
  -> fixed message list
  -> collision probability
  -> numerical bound
  -> construction claim
```

These are not merely different names for one object.  Each register licenses
different predicates, subjects, and natural sentence forms.  For example, a
converter *constructs a resource*, a game *is won*, a distribution *assigns
mass*, and an advantage *is bounded*.  A renderer that knows only the nouns
will still produce unnatural text because it does not know which relations
connect the registers.

The language architecture therefore has five distinct responsibilities:

1. **Ontology:** what mathematical and formal objects and relations exist.
2. **Lexical grammar:** how each concept or relation can be expressed in a
   clause, including argument order, voice, agreement, and selectional
   restrictions.
3. **Discourse planning:** why one clause follows another: definition,
   elaboration, cause, consequence, reduction, preservation, calculation, or
   conclusion.
4. **Reference management:** whether an object is new, given, contrasted, or
   reintroduced, and whether a noun phrase, symbol, or anaphor is safe.
5. **Evidence control:** which checked Lean evidence licenses each semantic
   statement and which routine transformations may be omitted.

Kyle's theorem-paragraph ontology addresses a substantial part of (1), (2),
and (4) for introductions and elementary propositions.  His structured
`Explanation` addresses presentation and disclosure.  Crypto needs the typed
relations and cross-register discourse in (2)--(5) as an additional layer.

## 3. Registers and bridge relations

`Register` records the mathematical viewpoint of a clause, not its visual
nesting depth.

| Register | Typical subject | Typical predicate | Supplies to the next register |
|---|---|---|---|
| Formal Lean | declaration, proof term, goal, application | has type, applies, discharges | checked evidence and provenance |
| Construction | specification, resource, converter, protocol | constructs, realizes, composes | concrete systems to compare |
| System | random system, interface, attached converter | answers, restricts, transforms, is equivalent | an experiment or a game enhancement |
| Game | game, MBO, event, winner | is obtained by enhancement, is won, has its MBO ignored, is restricted | winning event and strategy class |
| Law | transcript law, output law, distribution | is uniform, is consistent, agrees conditionally | a probability identity or equivalence |
| Scalar | distance, advantage, mass, winning probability | equals, is at most, is bounded by | a numerical obligation |
| Algebra | cardinality, sum, product, polynomial expression | simplifies, counts, is nonnegative | the final bound |

The bridges are first-class semantic relations:

| Bridge | Domain -> codomain | Reader meaning |
|---|---|---|
| `presents` | PDS/DDS -> random system | this concrete distribution/system represents that behavioral object |
| `attach` | converter × system -> system | the converter is connected to the stated interface |
| `serialAttach` | converter × converter × system -> system | converters act in application order |
| `realizes` | construction data -> real/ideal system pair | the construction goal is reduced to a system comparison |
| `enhanceWithMBO` | system × monotone condition -> game | the condition defines the game's monotone binary output |
| `ignoreMBO` | game -> system | the MBO is ignored while the ordinary outputs are retained |
| `restrict` | converter/transform × system/game -> system/game | a query or block budget is imposed |
| `inducesLaw` | system/game × environment × rounds -> distribution | interaction determines a transcript or output law |
| `conditionOn` | law × event -> law | only non-winning/good executions are considered |
| `measures` | system pair -> distance/advantage | a semantic comparison becomes a scalar quantity |
| `reducesToWin` | conditional equivalence -> advantage bound | distinguishing is controlled by winning a game |
| `fixesSchedule` | non-adaptive strategy -> query/message list | blindness permits a fixed list analysis |
| `boundsMass` | event × distribution -> scalar bound | a counting/probability lemma supplies the estimate |
| `establishesConstruction` | system bound -> construction | the scalar estimate closes the original CC relation |

These bridges are the backbone of a natural paragraph.  They also prevent an
invalid jump: for example, a collision probability cannot directly prove a
construction without the intervening game, advantage, system, and
construction relations being checked or supplied by registered theorems.

## 4. Entity inventory

The inventory is intentionally typed.  A name can play more than one role,
but it must do so through an explicit relation, not by an accidental string
match.

### 4.1 Formal Lean and evidence entities

These objects are needed for trust and inspectability.  Most are diagnostic,
not reader-facing nouns.

| Entity | Important fields/relations | Ordinary reader treatment |
|---|---|---|
| workspace, module, namespace | ownership and imports | normally omitted |
| declaration | name, telescope, type, value, source range | source anchor; name only when mathematically useful |
| definition, theorem, lemma | declaration kind and checked proposition | realized by mathematical role, not declaration kind alone |
| binder/local declaration | name, type, binder information, dependencies | introduces a mathematical referent |
| hypothesis/typeclass instance | proposition, evidence, salience | assumption or implicit capability; routine instances usually omitted |
| expression/application | head declaration and elaborated arguments | input to semantic decoding |
| proof term | inferred proposition and subterms | provenance; never narrated verbatim |
| tactic event/term event | before/after goals, source range, children | disclosure checkpoint; tactic spelling is not semantics |
| information tree | nested elaborator events and goals | evidence recovery only |
| metavariable/goal | local context and target | optional proof-state inspection |
| theorem application | rule, operands, premises, conclusion | a candidate mathematical inference |
| proof obligation | stable slot, proposition, evidence, salience | support edge or explicit subclaim |
| evidence region | covered expressions and checkpoints | compression accounting |
| source boundary | `have`, `calc`, named helper, macro edge | weak discourse hint, never sufficient semantics |

Tactics such as `rw`, `simpa`, `calc`, `omega`, `ring`, and `nlinarith` belong
here as **implementation events**.  They may help recover a checked before/after
transformation, but they must not map directly to phrases such as “we rewrite”
or “by arithmetic.”

### 4.2 Generic mathematical entities

| Family | Entities |
|---|---|
| Sortal | type, carrier, finite type, nonempty type, subtype |
| Collection | set, specification set, list, sequence, finite set, support, fiber |
| Functional | function, map, predicate, relation, transformation, injection, bijection |
| Logical | proposition, assumption, conjunction, disjunction, implication, equivalence, equality |
| Numeric | natural number, real, extended nonnegative real, cardinality, index, budget, error |
| Probabilistic | outcome, distribution, law, mass, weight, support, expectation |

These entries need Kyle-style noun, article, plural, adjective, accessory, and
dependency data.  Relation entries additionally need verbal frames; “a
distribution,” for example, is not enough to choose among *samples*, *assigns
mass to*, *is supported on*, and *is the law of*.

### 4.3 Abstract and Constructive Cryptography entities

This vocabulary is primarily from Maurer--Renner 2016, Sections 2--3.

| Entity | Semantic role and common relations |
|---|---|
| object/resource | an interactive object exposed at interfaces; belongs to a specification |
| specification | a set/property of acceptable resources; source or target of construction |
| interface | named access point of a resource or converter |
| party/role | owner or user of an interface when the model provides one |
| constructor | operation transforming one or more resources |
| converter | one-interface constructor with outside and inside interfaces |
| protocol | tuple/family of converters attached to specified interfaces |
| simulator | converter used at an ideal/adversarial interface |
| identity/blocking converter | neutral or access-limiting converter |
| attachment | application of a converter to a resource at an interface |
| serial composition | ordered converter composition; after `pi`, then `pi'`, the label is `pi' * pi` |
| parallel composition | combination of resources with ordered public interfaces |
| context | outer constructor used for composability/non-expansion |
| relaxation/error ball | specification enlarged by an error budget |
| construction relation | source specification, protocol/converter, target specification, error |
| exact construction | zero-error construction |
| composability/monotonicity | transport of constructions through valid contexts or relaxed specifications |

Lexically, *resource*, *system*, and *specification* are not interchangeable.
A theorem can say that a converter constructs a target **resource** from a
source **resource**, while Lean may encode both endpoints as singleton
**specifications** whose members are represented by random **systems**.

### 4.4 Random-system entities

The carrier vocabulary follows Liu--Maurer 2020 and the checked
`RandomSystems` library.

| Entity | Semantic role and common relations |
|---|---|
| input/output alphabet | query and answer types of a system |
| query/answer | one interaction step; answers may include rejection |
| input history | nonempty sequence of queries |
| interaction history/transcript | sequence of query/optional-answer pairs |
| deterministic discrete system (DDS) | history-dependent partial answer behavior |
| probabilistic discrete system (PDS) | distribution over DDS presentations |
| random system | observational/behavioral object represented by a PDS |
| presentation quotient | passage from a concrete PDS to the normalized carrier |
| environment/DDE | interactive strategy producing future inputs from observed replies |
| distinguisher | environment with a final decision/output test |
| transcript law | distribution induced by a system, environment, and round count |
| domain/refusal | histories on which the system answers or stops |
| deterministic converter (DDC) | two-sided system transforming one interface |
| converter application | action of a DDC/converter on a DDS/PDS/random system |
| transform/relabel/cascade | system-level operations with typed input/output behavior |
| query restriction/filter | converter or transform limiting admitted histories |
| parallel system | jointly exposed systems with routed interfaces |
| URF/URP | uniform random function/permutation system |
| VIL-URF | consistent uniform function on variable-length messages |
| real/ideal system | contextual roles in a comparison, not intrinsic system types |
| distance/advantage | optimal observational separation of systems |

The distinction between **object** and **presentation** must remain visible to
the semantic layer even when prose suppresses it.  Liu--Maurer define a random
system by conditional behavior while allowing pseudocode, diagrams, or
distributions over deterministic systems as descriptions.  Lean likewise has
several carrier levels whose coercions are often routine but whose semantics
are not identical.

### 4.5 Games and security entities

This register combines several explicitly labelled sources; Lanzenberger does
not own the later conditional-equivalence/blind vocabulary.

| Entity | Semantic role and common relations | Provenance |
|---|---|---|
| event/condition | predicate on histories or inputs | Jost-primary for named events and event histories; Lanzenberger-primary for monotone conditions |
| bad/good condition | security interpretation of an event and its complement | application/check-library role, not a primitive universal polarity |
| deterministic game/DDG | pair of a deterministic system and monotone condition | Lanzenberger-primary |
| probabilistic game/PDG | signed distribution over deterministic games | Lanzenberger-primary plus checked carrier |
| game transcript | ordinary transcript together with the final condition result | Lanzenberger-primary |
| winning transcript/event | transcript ending with the condition true | Lanzenberger-primary |
| winner role | a total environment interacting with the game; no separate `Winner` type | Lanzenberger-primary plus checked carrier |
| winning mass | mass that one fixed environment wins after a fixed horizon | Lanzenberger-primary |
| supremum winning probability | supremum over the registered environment family | Lanzenberger-primary |
| game equivalence | equality of observable game transcript laws | Lanzenberger-primary |
| winnability | infimum/supremum quantity over the exact registered game class | Lanzenberger-primary |
| statistical distance/advantage | exact quantities over their registered law, environment, or quotient carriers | Lanzenberger-primary plus checked refinements |
| MBO enhancement and forgetting | checked `PDS.adjoin`/`PDG.forget` relations and their answer-bit presentation | checked-library; CR18-fallback for the relevant discourse |
| blind/non-adaptive environment | proved independence of the query schedule from ordinary replies | checked-library; CR18-fallback for the reduction rhetoric |
| blind winning probability | supremum over the formal non-adaptive family | checked-library; CR18-fallback |
| conditional equivalence | two-operand division-free product identity over every fixed query list | checked-library; CR18-fallback |
| freshness/collision | application event predicates used to establish conditional behavior | application-specific; CR18-fallback only where registered |

The environment does not observe the monotone-condition bit in the thesis
model.  “Blind” must therefore be grounded in the selected formal carrier; it
must not be realized as an invented paper object called a blinder.

### 4.6 CBC entities

These entries come from the checked CBC modules and the CR18 fallback slice.

| Entity | Operands/definition | Natural relations |
|---|---|---|
| message | member of the outer input type `M` | is encoded, is queried, repeats |
| block alphabet | finite additive carrier `X` | supplies CBC blocks and round-function values |
| block former/encoding | `M -> List X` | encodes messages; is prefix-free; has total block count |
| block sequence | encoded list for one message | has a position/prefix/last block |
| CBC state | round function × block prefix -> chaining value | evolves block by block |
| round-function input | state plus current block | is queried; collides; is terminal |
| terminal round input | last input arising from a message | is distinct outside collision |
| CBC converter | outside messages/MACs, inside round-function calls/replies | digests an encoding and returns final state |
| `theta_r` block restriction | block former × total block limit | admits histories within the block budget and stops otherwise |
| inner query restriction | round-query limit | restricts the URF resource |
| random round function | URF on `X` | supplies consistent uniform round outputs |
| ideal message function | URF/VIL-URF on `M` | supplies consistent uniform message outputs |
| real CBC system | `theta_r` after CBC after the restricted round function | represents the construction's real side |
| ideal CBC system | `theta_r` after the ideal message function | represents its ideal side |
| CBC call site | message prefix and block position | has a parent and a round input |
| nontrivial collision | distinct call-site prefixes with equal round inputs | triggers `cbcBad` |
| CBC collision MBO/game | the MBO is 1 exactly when `cbcBad` has occurred | the game can be restricted and won; the system obtained from it by ignoring its MBO is the underlying system |
| uniform-consistent output law | uniform on fresh messages, equal on repeated messages | holds outside collision |
| fixed message list | schedule selected by a blind environment | satisfies the total-block budget |
| collision mass | uniform-function mass of `cbcBad` for that list | is bounded by the birthday expression |
| CBC epsilon | `r(r-1)/(2|X|)` or the library's chosen relaxed square bound | bounds advantage/distance/construction |

The checked proof boundaries `not_cbcBad_implies_uniform_outputs` and
`mass_cbcBad_le` denote substantive ideas.  Their internal fiber-counting and
site-forest arguments may be expandable, but neither theorem may be compressed
into generic automation.

### 4.7 Proof and discourse entities

| Entity | Function |
|---|---|
| claim | checked proposition selected for exposition |
| premise/conclusion | typed ends of an inference |
| derivation rule | mathematical transition licensed by a theorem application |
| obligation | one proof-valued premise in a stable semantic slot |
| proof plan | dependency structure among substantive claims |
| evidence coverage | map from claims/compression entries to checked regions |
| definition move | introduces an object, predicate, operation, or notation |
| elaboration move | restates a claim more precisely or supplies an equation |
| causal move | premise presented as the reason for a consequence |
| preservation move | transports an already established relation through a common operation |
| reduction move | replaces the current goal with a sufficient subordinate goal |
| instantiation move | fixes an arbitrary object or applies a general result to current operands |
| calculation move | chains equalities or inequalities |
| conclusion move | returns to and closes the foreground theorem |
| expansion | optional semantic subargument in the reader |
| routine evidence | checked but collapsed proof mechanics |
| symbolic fallback | exact unsupported content without guessed meaning |

### 4.8 Linguistic entities

The ontology must provide more than nouns.

| Linguistic object | Required data |
|---|---|
| lexical entry | lemma, part of speech, inflection, article, plural, domain/register |
| concept entry | noun forms, adjectives, notation, aliases, permissible modifiers |
| relation frame | predicate, semantic arguments, grammatical roles, valency, prepositions, voice options |
| selectional restriction | allowed subject/object ontology classes |
| referring expression | symbol, full noun phrase, short noun phrase, pronoun/anaphor |
| information status | new, given, contrastive, reintroduced |
| clause plan | speech act, subject, predicate frame, complements, polarity, tense/aspect, theme/rheme |
| discourse relation | definition, elaboration, cause, result, preservation, reduction, instantiation, bound, conclusion |
| paragraph plan | ordered clauses, aggregation choices, equation placement, expansion boundaries |
| register transition | explicit bridge connecting two mathematical viewpoints |

For example, the relation `attach(converter, system, interface)` needs frames
such as “attach CBC to the round-function interface of R” and “the system
obtained by attaching CBC to R.”  Merely declaring *CBC* to be a converter
cannot generate either clause reliably.

## 5. Occurrence contexts

The same entity must be realized differently according to its context.

| Context | Input structure | Expected language behavior |
|---|---|---|
| object definition | new symbol, sort, operands, body | “Let/Define … to be …”; introduce a stable referent |
| predicate/event definition | new predicate and iff condition | “The condition holds exactly when …”; expose temporal scope |
| operational definition | component plus interface behavior | say what inputs it accepts, calls it makes, and outputs it returns |
| notation declaration | symbol and established object | “Write … for …”; avoid pretending to define new mathematics |
| model exposition | object plus behavioral clauses | present mechanism in causal/temporal order |
| theorem assumptions | binders, capabilities, hypotheses | group compatible entities; foreground only assumptions used to understand the claim |
| theorem statement | root relation and primary operands | choose the semantic head—construction, equivalence, or bound—as the main clause |
| proof opening | theorem goal and selected route | orient the reader to the comparison or reduction, not to Lean syntax |
| local proof step | rule application, premises, conclusion | select a causal, inferential, or calculational frame |
| equation introduction | exact claim after prose paraphrase | use an elaboration relation and display the formula |
| equation reference | prior discourse anchor plus inference | “Using the preceding identity…”; preserve the referenced proposition |
| preservation under context | established relation plus common transform | “This remains true after restricting both systems by …” |
| goal shift | current goal and residual obligation | “It remains to bound …”; make the new foreground explicit |
| witness/schedule fixing | universal or supremum argument | “Fix an arbitrary …”; introduce scoped symbols and constraints |
| probabilistic estimate | event, law, and bound | identify the random source, event, and numerical estimate |
| calculation | compatible equality/inequality chain | aggregate without repeating unchanged terms |
| conclusion | discharged residual plus root claim | return to the theorem's original register |
| routine proof | effect-equivalent checked transformation | omit from prose, retain evidence coverage |
| unsupported region | exact expression/evidence | safe math rendering or explicit unsupported expansion |

Definition, theorem statement, and proof step are therefore not surface
templates over the same record.  They are different discourse contexts with
different information structure.

## 6. Abstract Random Systems grammar

This section is the normative abstract grammar shared by `/verbose` and
`/informalization`.  It consolidates the inventory in Section 4 and the
occurrence contexts in Section 5.  It is not an English phrase table and it is
not a second encoding of the Random Systems library.

It also supersedes the incomplete parts of the current prototype.  The policy
is consolidation, not a green-field rewrite:

| Existing element | Decision | Required change |
|---|---|---|
| `ConceptId`, `RelationId`, `RuleId`, operand and obligation roles | retain | make them keys into the typed catalog below rather than treating an ID as a complete ontology entry |
| canonical semantic terms and checked evidence graph | retain | add the missing RS carrier, strategy, game, law, and quantity distinctions |
| Kyle-style noun/adjective/accessory aggregation | retain | use it only after typed reference and clause planning |
| carrier-notation manifest and occurrence-context inventory | retain | connect each entry to exact semantic indices and permitted contexts |
| flat registers and generic predicate labels | replace | use indexed entities, role-labelled valency, selectional restrictions, and bridge relations |
| constructor-specific English declarations | refine | derive them from constructor schemas plus definition mode; do not accumulate one-off macros |
| Lean names embedded in propositions, such as “call this fact” | remove | keep names as optional discourse anchors outside mathematical content |
| tactic-name paraphrases and large multi-act sentences | remove | recover mathematical moves from checked goal changes and split independent discourse acts |
| CBC- or switching-shaped public grammar | remove | use switching and CBC only as acceptance tests for reusable RS rules |

No existing implementation behavior is preserved merely because it compiles.
It survives only if it inhabits this grammar and passes its truth-conditional
and whole-proof readability tests.

The grammar follows the central source distinction between a mathematical
object and a description of that object.  A random system is a behavior; a PDS,
pseudocode block, state machine, or sequence of conditional distributions can
describe or present that behavior.  Likewise, a converter is not identified
with the syntax of the program used to describe it, and a proof move is not
identified with the Lean tactic that produced it.

The grammar is **indexed** by mathematical kind and occurrence context.  The
same symbol therefore cannot be rendered from one context-free template.  For
example, a system can be introduced, defined operationally, compared in a
theorem, transformed in a proof, or mentioned anaphorically.  These are
different grammatical constructions over the same semantic referent.

### 6.1 Judgments and indices

The shared design uses four conceptual judgments:

```text
Gamma |- e : Entity K
Gamma |- p : Claim
Gamma ; p |- m : Move => obligations
discourse ; context |- node => clause-or-formula plan
```

`K` is an `EntityKind`; `context` is an `OccurrenceContext`.  The first three
judgments are semantic and must be recovered from checked declarations,
expressions, propositions, and proof applications.  The fourth chooses a
licensed presentation without adding mathematical content.

Application notation is compositional data, not a project-specific finished
string. A declaration profile supplies a notation constructor together with
named semantic operands; templates may interleave literal mathematical
syntax with references to those operands. Every referenced operand must be
declared, and every declared operand must occur. Thus a CBC game can be shown
as `widehat CBC[B; R]` while retaining the checked block encoding and round
function, whereas an unrecognized converter application remains explicit and
cannot silently acquire query-restriction notation.

Discourse state also carries the current mathematical foreground. A residual
obligation such as “It remains to bound the blind winning probability of this
game” introduces a referent that the following estimate reuses, even when the
checked helper theorem was stated for a generic game. This is controlled
anaphora over an already decoded operand, not replacement of formal evidence.
Independent proof declarations are ordered by their move roles and
dependencies; their accidental source order is not a prose contract.

Occurrence context is a product of independent axes.  A flat enum would force,
for example, every definition to have the same information status and every
proof assertion to have the same disclosure policy.

```text
EntityKind
  = carrier | interface | history | system | converter | game
  | strategy | law | event | quantity | specification | construction
  | proofObject | formalArtifact

structure OccurrenceContext where
  phase : Phase
  act : DiscourseAct
  definitionMode? : Option DefinitionMode
  binderMode? : Option BinderMode
  claimMode? : Option ClaimMode
  proofPosition? : Option ProofPosition
  informationStatus : InformationStatus
  visibility : DisclosureMode

Phase
  = declaration | theoremStatement | proof | exposition | diagnostic

DiscourseAct
  = introduce | define | describe | assume | assert | derive | preserve | reduce
  | instantiate | split | calculate | estimate | conclude | refer

DefinitionMode
  = abstract | denotational | operational | derived | predicate
  | representational | notation | roleAssignment

BinderMode
  = given | assumed | fixedArbitrary | chosenWitness | implicitCapability

ClaimMode
  = theoremRoot | localResult | sideCondition | displayedEquation

ProofPosition
  = opening | derivation | preservation | reduction | instantiation
  | caseAnalysis | induction | calculation | estimate | closure

InformationStatus
  = new | given | active | contrastive | reintroduced

DisclosureMode
  = collapsed | expanded | diagnostic
```

These are semantic distinctions, not instructions to print the constructor
names.  For instance, one occurrence may have
`phase := proof`, `act := instantiate`, `binderMode := fixedArbitrary`, and
`visibility := collapsed`; it may be realized as “Fix an arbitrary
environment.”  Another occurrence of the same environment in an expanded
formula has a different context record without becoming a different entity.

### 6.2 Entity kinds and subkinds

The following table is the closed core of the Random Systems grammar.  Domain
profiles may add named subkinds, but they may not merge the distinctions shown
here.

| Kind | Required subkinds or features | Distinctions that must survive |
|---|---|---|
| carrier | type, finite alphabet, nonempty alphabet, subtype, state space | finiteness, nonemptiness, decidable equality, and algebraic structure are properties, not synonyms for “alphabet” |
| interface | input/output signature, named port, inside/outside port, party-indexed port, dependent interface family, routed sub-interface | direction, ownership, dependency, and attachment site |
| history | query, answer, input history, attempted history, transcript, prefix, fixed query list, encoded block list, call site | queries versus query/answer transcripts; fixed versus adaptively induced schedules |
| system | DDS, signed PDS, normalized `ProbDist` presentation, common-domain presentation, ambient presentation, behavioral quotient/random system, resource, real/ideal role | presentation versus behavior; signed versus nonnegative versus normalized law; common-domain versus ambient carrier; intrinsic kind versus contextual real/ideal role |
| converter | deterministic/randomized converter, identity, blocking converter, query restriction, domain filter, block restriction, relabelling, serial/parallel composite, protocol component, simulator role | outside/inside signatures, application order, attachment interface, applicability |
| game | deterministic/probabilistic game, game belonging to `GamesFor S`, MBO-enhanced game, restricted/transformed game, game with ignored MBO | game law versus forgotten ordinary system; full interactive equivalence versus fixed-list not-won equivalence versus conditional equivalence |
| strategy | partial environment, total environment, signed partial PDE, normalized ambient total PDE, strict distinguisher, winner role, non-adaptive property, fixed-query environment, fixed schedule | accepted-versus-attempted histories; interaction strategy versus strict converter test; unrestricted versus proved non-adaptive/fixed query behavior |
| law | source distribution, transcript law, output law, not-won law, conditioned law, pushforward, extended law, honest joint/coupling law, marginal, signed expansion | law versus system; support versus domain; honest nonnegative joint versus signed identity |
| event | predicate, monotone condition, MBO, bad/good event, collision, freshness, winning, disagreement, support/domain event | truth scope on histories or outcomes; monotonicity; complement; temporal boundary |
| quantity | weight, mass, probability, `Adv`, `AdvD`, `Adv⊥`, ambient advantage, class distance `Δ`, quotient `edist`, adaptive/blind winning probability, winnability, cardinality, error budget | scalar carrier, orientation, observer class, normalization, carrier level, and supremum domain |
| specification | set/property of resources, singleton, image under a constructor, relaxation, filtered specification, parallel specification | object versus set of acceptable objects; exact versus relaxed membership |
| construction | constructor, protocol, simulator-bearing construction, exact/approximate construction, composition/context application | source specification, target specification, converter/protocol, interface/corruption pattern, error |
| proofObject | theorem application, equality witness, coupling, reduction, representative selection, simulator, counting witness, proof obligation | mathematical evidence type and premise slots; never the generic reader noun “certificate” |
| formalArtifact | declaration, binder, proof term, tactic event, goal, InfoTree node, coercion, elaboration wrapper | checked provenance only; no default mathematical noun phrase |

`real`, `ideal`, `restricted`, `uniform`, `blind`, and `bad` are normally roles
or properties applied to one of these kinds.  They are not untyped entities.

Stable `ConceptId`s remain registry keys, but the semantic grammar additionally
requires indices equivalent to the following:

```text
SystemCarrierLevel
  = deterministicDDS
  | pdsPresentation
  | partialProbDistLaw
  | commonDomainPresentation
  | probabilityCommonDomainPresentation
  | pdsBehaviourQuotient
  | commonDomainBehaviourQuotient
  | probabilityCommonDomainQuotient
  | ambientAttemptedHistoryDDS
  | ambientPDSPresentation
  | ambientRandomSystemQuotient

GameCarrierLevel
  = deterministicDDG | pdgPresentation | gamesForSubtype
  | gameBehaviourQuotient

HistorySemantics = retainedPartialHistory | attemptedHistoryWithRejection
SupportDomain = notApplicable | unconstrained | common(domain)

structure DomainIndex where
  history : HistorySemantics
  support : SupportDomain

SignStatus = signedAllowed | nonnegative
WeightStatus = unrestricted | atMostOne | exactlyOne

structure LawMassIndex where
  sign : SignStatus
  weight : WeightStatus

structure SystemIndex where
  carrier : SystemCarrierLevel
  queryType : TypeRef
  answerType : TypeRef
  domain : DomainIndex
  mass? : Option LawMassIndex
  admissible : SystemCarrierAdmits carrier domain mass?

structure ConverterIndex where
  carrier : ConverterCarrier
  outerQuery : TypeRef
  outerAnswer : TypeRef
  innerQuery : TypeRef
  innerAnswer : TypeRef

ConverterCarrier
  = partialDDC | ambientDDC | normalizedAmbientPDC
  | commonDomainMorphism

ActionRegime
  = partialDDSUnconditional
  | signedPDSLawPushforward
  | ambientUnconditional
  | ambientRandomizedConverter
  | commonDomainGlobalPreserver
  | commonDomainSpecificationLocal

AttachmentSite = fixedBoundary | namedInterface(interface)

ConditionVisibility = hiddenMBO | observableEvent | transcriptPredicate

structure GameIndex where
  carrier : GameCarrierLevel
  queryType : TypeRef
  answerType : TypeRef
  conditionVisibility : ConditionVisibility
  domain : DomainIndex
  mass? : Option LawMassIndex
  admissible : GameCarrierAdmits carrier domain mass?

StrategyCarrier
  = partialDDE | totalDDE | signedPartialPDE
  | normalizedAmbientTotalPDE | strictDistinguisher

Adaptivity = unrestricted | nonAdaptive | fixedQueryList

structure StrategyIndex where
  carrier : StrategyCarrier
  queryType : TypeRef
  answerType : TypeRef
  mass? : Option LawMassIndex

structure StrategyProperties where
  strategy : StrategyIndex
  adaptivity : Adaptivity
  refusalObservation : acceptedOnly | attemptedQueries
  admissible : StrategyAdmits strategy.carrier adaptivity refusalObservation

structure LawIndex where
  sampleType : TypeRef
  mass : LawMassIndex
  observation : source | transcript | output | extended | joint

EventScope
  = inputHistory | attemptedHistory | transcript | gameTranscript
  | output | jointOutcome | callSiteFamily

structure EventIndex where
  sampleType : TypeRef
  scope : EventScope
  temporalBoundary? : Option TemporalBoundary
  monotonicity : notApplicable | arbitraryPredicate | monotoneCondition
  visibility : hiddenDuringInteraction | visibleOutcome | internalPredicate

HistoryKind = input | attempted | transcript | gameTranscript | encodedBlocks

structure HistoryIndex where
  kind : HistoryKind
  entryType : TypeRef
  recordsRefusal : Bool

ScheduleOrigin
  = explicitList | inducedBy(strategy, referenceSystem, horizon)

BudgetUnit = queries | rounds | encodedBlocks | callSites

structure ScheduleIndex where
  queryType : TypeRef
  origin : ScheduleOrigin
  adaptivity : Adaptivity
  budget? : Option (BudgetUnit × ScalarExpr)
  admissible : ScheduleAdmits origin adaptivity budget?

AdvantageKind
  = compatibleStoppingOnBothPresentations   -- `Adv`
  | fixedDomainHalting(domain)               -- `AdvD(D, -, -)`
  | allTotalEnvironmentsAndHorizons          -- `Adv⊥`
  | fixedAmbientPDE(environmentLaw)           -- `Ambient.PDE.advantage E - -`
  | ambientAllTotalEnvironmentsAndHorizons   -- ambient advantage

DistanceKind
  = lawStatisticalDistance
  | honestRepresentativeClassDistance   -- `classDistance` / `Δ`
  | staticStrictDistinguisherDistance    -- `maxEDist`
  | quotientMetric(carrier, definingMetric) -- carrier-specific `edist`

WinningKind = adaptive | nonAdaptive

WinningScope(adaptive, game) = allTotalEnvironmentsAndHorizons
WinningScope(nonAdaptive, game) = allNonAdaptiveTotalEnvironmentsAndHorizons

WinnabilityFamilyKind = honestGameTranscriptEquivalentRepresentatives
WinnabilityObservable = sourceLawMassOfSystemWinnable

structure WinnabilityIndex where
  root : GameIndex
  rootIsPDG : root.carrier = pdgPresentation
  family : WinnabilityFamilyKind
  representativeCarrier : GameCarrierLevel
  representativeIsPDG : representativeCarrier = pdgPresentation
  representativeQueryType : TypeRef
  sameQueryType : representativeQueryType = root.queryType
  representativeAnswerType : TypeRef
  sameAnswerType : representativeAnswerType = root.answerType
  observable : WinnabilityObservable

QuantityIndex
  = weight(law : LawIndex, scalar : Real)
  | mass(law : LawIndex, event : EventIndex, scalar : Real)
  | probability(law : LawIndex, event : EventIndex,
      normalized : IsNormalizedLaw law, scalar : Real | ENNReal)
  | advantage(kind : AdvantageKind, left : SystemIndex, right : SystemIndex,
      scalar : ENNReal, orientation : Orientation)
  | distance(kind : DistanceKind, left : EntityIndex, right : EntityIndex,
      scalar : ScalarOfDistance kind, orientation : Orientation)
  | winning(kind : WinningKind, game : GameIndex,
      scope : WinningScope kind game, scalar : Real | ENNReal)
  | winnability(index : WinnabilityIndex, scalar : Real | ENNReal)
  | cardinality(collectionType : TypeRef, scalar : Nat)
  | error(scalar : NNReal | ENNReal)

Orientation
  = leftMinusRight | rightMinusLeft | absoluteDifference | symmetric
  | symmetrizedBySup

ScalarOfDistance(lawStatisticalDistance) = Real
ScalarOfDistance(honestRepresentativeClassDistance) = ENNReal
ScalarOfDistance(staticStrictDistinguisherDistance) = ENNReal
ScalarOfDistance(quotientMetric(_, _)) = ENNReal
```

`SystemCarrierAdmits`, `GameCarrierAdmits`, `StrategyAdmits`, and
`ScheduleAdmits` are closed validation relations.
For example, a DDS/DDG has no law-mass index; a raw PDS/PDG admits signed or
proved-nonnegative law mass; `PDS.IsProbability` is nonnegative with weight at
most one; and a `Distribution.ProbDist` or probability presentation is
nonnegative of weight exactly one.  Common-domain packaging constrains
`support`, not merely sign or weight.  Thus impossible products cannot inhabit
the semantic index.

The indices record mathematical properties, never how their witnesses were
obtained.  Structural versus explicit evidence, proof terms, source locations,
and premise visibility live in `PropertyEvidence`/provenance metadata on the
checked edge.  Likewise, `StrategyIndex` does not say “environment,”
“distinguisher,” or “winner”: those are intrinsic only where fixed by the
carrier (for example `strictDistinguisher`) or otherwise supplied by a
`RoleAssignment` or relation.

These indices are selectional restrictions.  They prevent the grammar from
calling an arbitrary-mass PDS a probability distribution, attaching a
converter across incompatible boundaries, treating a fixed schedule as
adaptive, or interchanging `Adv`, `Adv_bot`, ambient advantage, and class
distance.

`Adv`, `AdvD`, `Adv⊥`, and class distance use one-sided statistical distance
on the signed carrier and therefore default to `leftMinusRight`; equal weight
may later license a symmetry theorem.  An `edist` quantity records both its
quotient carrier and installed metric: `PDS.Behaviour` uses a supremum
symmetrization of `Adv⊥`, the ambient quotient uses ambient advantage, and the
normalized common-domain quotient uses its embedding metric.  No generic
“normalized quotient distance” entry is permitted.

Stable IDs alone are not the grammar.  Each ID indexes a catalog entry with a
formal signature and its permissible linguistic uses:

```text
SourceClass
  = projectControlled | languageDesignMassot
  | primaryMauRen16 | primaryJost | primaryLiuMau20
  | primaryLanzenberger | checkedLibrary
  | proposedPendingAttestation | cr18Fallback

structure SourceAttestation where
  sourceClass : SourceClass
  work : SourceId
  locator : SectionOrPage
  excerptFingerprint? : Option String

structure ConceptEntry where
  id : ConceptId
  parentKinds : NonemptyArray EntityKind
  indexSchema : IndexSchema
  constructors : Array ConstructorId
  lexicalForms : Array LexicalForm
  referenceForms : Array ReferenceForm
  permittedContexts : ContextPredicate
  attestations : NonemptyArray SourceAttestation

structure ConstructorSchema where
  id : ConstructorId
  resultKind : EntityKind
  operandRoles : NonemptyArray TypedRole
  resultIndex : IndexComputation
  definitionFrames : Array DefinitionFrame
  referenceFrames : Array ReferenceFrame
  permittedModes : Set DefinitionMode
  constraints : Array RoleConstraint
  attestations : NonemptyArray SourceAttestation

structure RelationSchema where
  id : RelationId
  argumentRoles : NonemptyArray TypedRole
  selection : Array OntologyConstraint
  resultSort : proposition
  clauseFrames : Array PredicateFrame
  formulaPolicy : FormulaPolicy
  permittedContexts : ContextPredicate
  bridge? : Option RegisterBridge
  constraints : Array RoleConstraint
  attestations : NonemptyArray SourceAttestation

structure InferenceSchema where
  id : RuleId
  operands : Array InferenceOperandSchema
  premises : Array PremiseSchema
  conclusion : ClaimPattern
  residuals : Array ResidualSchema
  move : MoveKind
  constraints : Array RoleConstraint
  declarations : NonemptyArray DeclarationBinding
  permittedContexts : ContextPredicate
  attestations : NonemptyArray SourceAttestation

structure InferenceOperandSchema where
  role : ArgumentRole
  expected : EntityPattern
  provision : ProvisionPolicy
  constraints : Array RoleConstraint

structure DeclarationBinding where
  declaration : Name
  signatureFingerprint : SignatureFingerprint
  operandSelectors : Array (ArgumentRole × StableOperandSelector)
  premiseSelectors : Array (ArgumentRole × StablePremiseSelector)

structure PremiseSchema where
  role : ArgumentRole
  expected : ClaimPattern
  provision : ProvisionPolicy
  visibility : PremiseVisibilityPolicy
  evidenceClass : EvidenceClass

structure ResidualSchema where
  role : ObligationRole
  tag : Name
  expected : ClaimPattern
  visibility : ObligationVisibilityPolicy

RoleConstraint
  = indexEqual(leftRolePath, rightRolePath)
  | hasConstructor(rolePath, constructorId)
  | refinesCarrier(rolePath, carrierClass)
  | resultIndexEquals(indexComputation)
  | eventDomainEqualsLawSample(eventRole, lawRole)
  | boundaryMatches(converterBoundary, systemBoundary)
```

A `LexicalForm` contains lemma, part of speech, inflection, article behavior,
register, and source attestation.  A `PredicateFrame` contains valency,
grammatical function for every semantic role, voice, polarity, and theme/rheme
options. Language-specific prepositions and word order belong to the language
pack. `FormulaPolicy` says whether ordinary realization
prefers prose, notation, or prose followed by a displayed formula.  A context
predicate ranges over the product in Section 6.1; it is not another flat list
of sentence types.

Registration validates these constraints against the formal declaration
signature.  Instantiation validates them against the actual operands.  This
is how the grammar states, rather than merely hopes, that two systems share a
signature, a converter boundary matches its attached interface, a game and
target system have compatible carriers, and a law and event have the same
sample type.

For every `DeclarationBinding`, registration resolves each stable selector in
the live declaration telescope, checks its exact type against the corresponding
operand or premise pattern, and recomputes the signature fingerprint. A
missing, duplicated, reordered-without-updated-selector, or ill-typed slot is a
registration error rather than a best-effort decode.

`cr18Fallback` is never inferred merely because a declaration or example is
about CBC.  It is an explicit provenance value permitted only for concepts in
the repository's fallback register.  `proposedPendingAttestation` may appear in
the design catalog but cannot back public syntax until it receives a primary
or explicitly allowed fallback locator.

This catalog is the reusable abstract grammar.  `/verbose` selects rigid
source forms whose operands elaborate to one catalog entry.
`/informalization` recovers the same entry from checked Lean and chooses among
its licensed clause and discourse plans.  Neither consumer may define the
meaning of a concept by installing an isolated English string.

### 6.3 Entity-expression grammar

Entity expressions are compositional.  The constructors below retain their
typed operands even when a later realization uses a short name.

This notation specifies the target shape of the **existing** canonical layer;
it does not introduce a parallel AST.  Migration is explicit:

| Current implementation type | Abstract-grammar destination | Migration |
|---|---|---|
| `Canonical.SystemTerm` | `SystemExpr` plus `SystemIndex` | retain constructors; add carrier/signature indices and missing presentation/parallel/domain forms |
| `Canonical.GameTerm` | `GameExpr` plus `GameIndex` | retain enhancement/transform/restriction; add exact game-carrier indices |
| `Canonical.ConverterTerm` | `ConverterExpr` plus `ConverterIndex` | retain named/restriction/serial forms; make first-applied order and typed boundaries explicit |
| `Canonical.TransformationTerm` | registered transformation entity or `CatalogView.unsupported` | retain exact source/type and the transformation's input/output index computation |
| `Canonical.ConditionTerm` | `EventExpr`/condition entity or `CatalogView.unsupported` | retain exact source/type, sample scope, monotonicity kind, and temporal boundary |
| `Canonical.SpecificationTerm` | `SpecificationExpr` or `CatalogView.unsupported` | retain singleton; map every opaque constructor to a structured fallback with exact source and type; extend by registered specification constructors |
| `Canonical.BoundTerm` | `QuantityExpr` plus `QuantityIndex` | refactor, preserving exact source expressions; distinguish every advantage/distance/winning kind |
| `Canonical.Claim` / `CanonicalProposition` | `CanonicalClaim` in Section 6.5 | refactor recognized bound-specific constructors into the unique `Compare` form; map every `.opaque source` to `OpaqueClaim` without guessing a relation |
| `Canonical.CanonicalOperand` | `TypedCheckedOperand` | retain role, value, original optional type annotation, inferred exact type, and source ordering |
| `Canonical.ProofObligation` | `CheckedPremise` or `ResidualObligation` according to proof state | retain `ObligationKey`, slot/role, salience, exact proposition, proof/evidence when present, decoded claim when available, and provenance |
| `Canonical.DerivationApplication` and `Canonical.FormulaTerm` | the lossless `DerivationApplication` below | retain typed operands, consumed premises, residual obligations, conclusion, exact source/type, provenance, evidence anchor, and optional formula; derive the sole rhetorical `MoveKind` from the registered rule |

During migration, a total `CatalogView` maps each old node into the new indexed
view.  A node that cannot inhabit a validated closed index maps to
`CatalogView.unsupported`, retaining its exact expression, exact type, original
canonical constructor, and optional kind hint; it is never forced into an
incorrect catch-all carrier.  Round-trip/source retention,
semantic-fingerprint preservation, and constructor-by-constructor tests are
gates for changing the stored type.  No consumer may bypass that map by
building a second independent semantic tree.

```text
structure CatalogView(K) where
  source : Expr
  exactType : Expr
  originalConstructor : Name
  node : CatalogNode K

CatalogNode(K) =
    known(index : IndexFor K, value : ExprFor K index)
  | unsupported(kindHint? : Option EntityKind)
```

```text
SystemExpr ::=
    SystemAtom(id, signature, carrierKind)
  | UniformRandomFunction(inputAlphabet, outputAlphabet)
  | UniformRandomPermutation(alphabet)
  | IdealFunctionality(id, signature)
  | PresentedBy(presentation)
  | QuotientOf(presentation, quotientKind)
  | EmbedCommonDomain(presentation)
  | NormalizePresentation(presentation)
  | ApplyConverter(converter, attachmentSite, actionRegime, system)
  | RestrictQueries(system, budget)
  | RestrictDomain(system, predicate)
  | TransformSystem(transform, system)
  | ParallelSystems(orderedSystems, router)
  | ForgetMBO(game)

ConverterExpr ::=
    ConverterAtom(id, outsideSignature, insideSignature)
  | IdentityConverter(signature)
  | BlockingConverter(interface)
  | QueryRestriction(budget)
  | DomainFilter(predicate)
  | BlockRestriction(encoding, blockBudget)
  | Relabelling(inputMap, outputMap)
  | SerialConverters(firstApplied, secondApplied)
  | ParallelConverters(orderedConverters)

GameExpr ::=
    GameAtom(id, signature)
  | EnhanceWithMBO(system, conditionAssignment)
  | RestrictGame(game, restriction)
  | TransformGame(transform, game)

TypedGameExpr(index) = ExprFor game index

StaticWinnability(root : TypedGameExpr(index)) =
  sInf {
    Mass(GameSourceLaw(representative),
      GameSystemWinnable(index.queryType, index.answerType)) |
      checked index.carrier = pdgPresentation,
      representativeIndex : GameIndex,
      checked representativeIndex.carrier = pdgPresentation,
      checked representativeIndex.queryType = index.queryType,
      checked representativeIndex.answerType = index.answerType,
      representative : TypedGameExpr(representativeIndex),
      checked NonNeg representative,
      checked PDG.gameEquivalent representative root
  }

This is the expression contract for `PDG.infWinnability`: the quantified
objects are typed game expressions, not `GameIndex` metadata, and the
observable is the source-law mass of the lifted `System.Winnable` event. It is
not an environment/horizon supremum.

StrategyExpr ::=
    PartialEnvironment(id, acceptedHistorySignature)
  | TotalEnvironment(id, attemptedHistorySignature)
  | SignedPartialPDE(id, partialEnvironmentLaw)
  | NormalizedAmbientTotalPDE(id, totalEnvironmentLaw)
  | StrictDistinguisher(id, unitToBoolConverterProtocol)

ScheduleExpr ::=
    ExplicitSchedule(queryList)
  | InducedSchedule(strategy, referenceSystem, horizon)
  | AdmittedSchedule(schedule, predicate)

HistoryExpr ::=
    Query(value) | Answer(value) | InputHistory(entries)
  | AttemptedHistory(entries) | Transcript(entries)
  | Prefix(history, length) | InducedQueries(strategy, system, horizon)
  | EncodedBlocks(message, encoding) | CallSite(message, blockPosition)

LawExpr ::=
    SourceLaw(systemPresentation)
  | GameSourceLaw(gamePresentation)
  | TranscriptLaw(system, environment, horizon)
  | OutputLaw(system, inputs)
  | NotWonLaw(game, environment, horizon)
  | ConditionedLaw(law, event)
  | Pushforward(transform, law)
  | ExtendedLaw(law, reveal)
  | JointLaw(leftLaw, rightLaw)
  | Marginal(jointLaw, side)

EventExpr ::=
    EventAtom(id, domain, scope)
  | GameSystemWinnable(queryType, answerType)
  | HoldsBy(history, horizon, predicate)
  | Complement(event)
  | Union(events) | Intersection(events)
  | Collision(objects, equalityCriterion)
  | Freshness(query, history)
  | Winning(game, strategy, horizon)
  | Disagreement(jointLaw)

QuantityExpr ::=
    Weight(law)
  | Mass(law, event)
  | Probability(law, event)
  | Distance(distanceKind, leftSystem, rightSystem, observerScope)
  | Advantage(advantageKind, leftSystem, rightSystem, observerScope)
  | WinningProbability(game : TypedGameExpr(gameIndex), winningKind,
      scope : WinningScope winningKind gameIndex)
  | Winnability(game : TypedGameExpr(gameIndex),
      index : WinnabilityIndex with index.root = gameIndex)
  | Cardinality(collection)
  | OpaqueQuantity(source, exactScalarType, unsupportedHead)

SpecificationExpr ::=
    SpecificationAtom(id, carrier)
  | SingletonSpecification(entity)
  | ImageSpecification(constructor, specification)
  | RelaxedSpecification(specification, error)
  | FilteredSpecification(specification, condition)
  | ParallelSpecification(orderedSpecifications)
```

Contextual roles and proof properties do not construct new entity identities.
A converter becomes a simulator through `RoleAssignment`; a game belongs to
`GamesFor S` through `belongsGameFor`; an environment is a winner or is
non-adaptive through `wins` or `isNonAdaptive`; and a fixed schedule is a
separate `ScheduleExpr`.  Likewise, embedding, normalization, joint-law, and
applicability witnesses live on checked derivation/evidence edges.  They are
not operands of denotational entity terms, so proof irrelevance is not needed
to stabilize semantic fingerprints.

`Weight` consumes a `LawExpr`; the weight of a system presentation first uses
its registered `SourceLaw` projection, while a PDG uses `GameSourceLaw`.
`GameSystemWinnable(X,Y)` is the registered lift of `System.Winnable` to the
sample type of a `PDG X Y`; it is not an inferred generic event coercion.
Quotient distance is `Distance(quotientMetric(...), ...)`, and static
winnability uses the distinct `Winnability` constructor and the
`StaticWinnability` contract above; there are no duplicate constructors.
Scalar arithmetic is represented by the separate typed `ScalarExpr` grammar.
`OpaqueQuantity` is only a lossless fallback and never competes with a
recognized quantity constructor.

Constructing `ConditionedLaw(law,event)` requires a separate checked edge whose
premise schema supplies the nonzero-mass proof. That witness is never part of
the law identity or fingerprint. `StrategyAdmits` rules out attempted-history
observation for partial accepted-history DDEs. `ScheduleAdmits` forces an
explicit list to be fixed-query rather than unrestricted. `WinningScope`
derives observer and horizon quantification from `WinningKind`, so invalid
cross-products are uninhabited.

The registered `PDS.adjoin S A` constructor has result index `gamesForSubtype`
and retains both its underlying PDG projection and the `PDS.equivalent
(PDG.forget G) S` membership edge.  `EnhanceWithMBO` alone never invents a
representative equality, and `A` is a DDS-indexed monotone-condition assignment
rather than necessarily one fixed condition.

`SerialConverters(firstApplied, secondApplied)` records execution order rather
than the printed multiplication order.  A concrete profile may print the
library's composition notation only after validating that order.

The grammar deliberately has no constructors named `rw`, `simp`, `calc`,
`omega`, or `ring`.  Those are `formalArtifact`s from which a semantic equality,
bound, or routine region may be recovered.

### 6.4 Definition and description grammar

Definitions are typed discourse objects, not arbitrary English versions of
`let` or `def`.

```text
EntityDefinition ::=
    AbstractDeclaration(name, kind, signatures, properties)
  | DenotationalDefinition(name, entityExpression)
  | CharacterizedDefinition(name, entityExpression, characterizationClaim)
  | OperationalDefinition(name, signatures, behaviorClauses)
  | DerivedDefinition(name, constructor, operands)
  | PredicateDefinition(name, domain, scope, iffCondition)
  | RepresentationDefinition(name, presentation, representedObject)
  | NotationDefinition(symbol, establishedEntity)
  | RoleAssignment(entity, discourseRole, comparisonScope)

EntityDescription ::=
    DenotationalDescription(entity, mathematicalExpression, correspondence)
  | OperationalDescription(entity, signatures, behaviorClauses, correspondence)
  | PseudocodeDescription(entity, programArtifact, correspondence)
  | DiagramDescription(entity, diagramArtifact, correspondence)

BehaviorClause ::=
    Accepts(input, interface, guard?)
  | Sends(value, innerInterface)
  | Receives(value, innerInterface)
  | Returns(value, outerInterface)
  | Updates(stateBefore, stateAfter)
  | Refuses(input, condition)
  | Triggers(event, condition)
  | Samples(value, law)
  | Reuses(value, earlierOccurrence)
```

`CharacterizedDefinition` binds the exact `entityExpression`; it never
reconstructs an entity from prose. Its characterization is a separate checked
claim with an evidence/support edge whose proof type must match that claim.
The entity fingerprint follows the exact expression, while changing the
characterization changes the definition-discourse fingerprint and evidence
identity.

The definition mode is selected from semantic evidence:

- **Abstract declaration:** only the kind, interfaces, and assumptions are
  supplied.  Example: “Let `R` be an `(X,Y)`-random system.”
- **Denotational definition:** an exact mathematical expression is the most
  informative description.  Example: “Define `G` by adjoining condition `A`
  to `R`.”
- **Operational definition:** interface behavior or state evolution is the
  point of the definition.  A converter normally needs its outside input,
  inner calls, inner replies, and outside output, rather than the empty clause
  “`alpha` is a converter.”
- **Derived definition:** a standard constructor already has an established
  interpretation.  Example: “Let `[q]R` denote `R` restricted to `q` queries.”
- **Predicate definition:** the defining content is an iff with explicit
  history or time scope.  Example: “`A` holds on history `h` exactly when a
  collision has occurred by the end of `h`.”
- **Representation definition:** a concrete PDS/presentation and its
  behavioral random-system object are related without identifying their
  carriers.  Example: “Let `R` be the random system represented by `P`.”
- **Notation definition:** a symbol is introduced for an already established
  object; no new mathematical object is asserted.
- **Role assignment:** an existing object receives a contextual role such as
  real system, ideal system, simulator, or intermediate.  The role holds only
  in the stated comparison or construction.

Definition and description are not identical.  A system may be *defined* by
its conditional response laws yet *described* by pseudocode or an operational
state machine.  The grammar records both as presentations of the same
referent, linked by checked equivalence when the correspondence is not
definitional.  Every non-definitional description carries that checked
correspondence.  Without one, it is an explicitly marked author note rather
than compiler-justified mathematical prose.

### 6.5 Claim and relation grammar

Claims are built from typed relations.  Logical composition is represented
explicitly, but final prose may aggregate compatible conjuncts or display a
formula.

```text
Claim ::=
    Atomic(propositionalRelation, roleIndexedArguments)
  | Compare(quantity, comparator, scalar)
  | Quantified(quantifier, binders, claim)
  | Conditional(assumptions, claim)
  | Conjunction(claims) | Disjunction(claims)
  | Implication(cause, consequence) | Biconditional(left, right)
  | OpaqueClaim(source, exactType)

Comparator ::= equal | atMost | atLeast | strictLess | subset
```

`CanonicalClaim` is this sum together with its exact elaborated source and type;
recognized and opaque claims therefore share one lossless envelope. This is
the sole canonical representation of scalar comparisons. A mass,
advantage, distance, winning, winnability, weight, cardinality, or error bound
is always a `Compare(QuantityExpr, comparator, scalar)`.  Names such as `massBound` and
`advantageBound` may identify clause-frame families or inference conclusions,
but they are not competing `Atomic` claim constructors.

The relation inventory is grouped by selectional signature:

| Family | Relations and principal roles |
|---|---|
| classification | `hasKind(entity, kind)`, `hasSignature(entity, interfaces)`, `hasProperty(entity, property)` |
| presentation | `presents(presentation, system)`, `hasBehavior(system, lawFamily)`, `inducesLaw(system, strategy, horizon, law)` |
| membership | `belongs(entity, specification)`, `belongsGameFor(game, system)`, `supportedOn(law, set)`, `hasDomain(system, domain)`, `answersOn(system, domain)`, `refusesOutside(system, domain)` |
| converter | `preservesCommonDomainCarrier(converter)`, `applicableToSpecification(sourceSpecification, converter)`, `attachmentEquals(converter, attachmentSite, actionRegime, source, attached)`, `serialEquals(first, second, composite)`, `commutesAtDistinctInterfaces(left, right, system)` |
| system comparison | `presentationEqual(left, right)`, `pdsTranscriptEquivalent(left, right)`, `strictDistinguisherEquivalent(left, right)`, `ambientTranscriptEquivalent(left, right)`, `commonDomainPresentationEquivalent(left, right)`, `probabilityCommonDomainPresentationEquivalent(left, right)`, `quotientEqual(left, right)` |
| game | `enhancementSubtypeEqual(system, conditionAssignment, gameForSystem)`, `enhancementPDGEqual(system, conditionAssignment, game)`, `forgettingEquals(game, system)`, `forgettingEquivalent(game, system)`, `gameTranscriptEquivalent(left, right)`, `equivalentAsGames(left, right)`, `conditionallyEquivalent(game, system)`, `wins(strategy, game, horizon)` |
| law | `lawEqual(left, right)`, `notWonLawEqual(leftGame, rightGame, environment, horizon)`, `notWonLawEqualAtList(leftGame, rightGame, nonemptyQueries)`, `conditionedLawEqual(source, event, target)`, `uniformOn(law, freshInputs)`, `consistentOnRepeats(law, repeatedInputs)`, `isMarginal(joint, side, law)`; a normalized-conditioning inference carries nonzero mass as a separate premise |
| event | `occurs(event, outcomeOrHistory)`, `eventIff(event, condition)`, `eventImplies(left, right)`, `eventCovers(event, pieces)`, `eventsDisjoint(events)`, `isMonotone(event)` |
| probability/scalar properties | `nonnegative(law)`, `normalized(law)`, `equalWeight(left, right)`; numerical equalities and bounds use `Compare` |
| construction | `constructs(converterOrProtocol, sourceSpecification, targetSpecification, error)`, `preservesConstruction(context, construction)`, `composes(firstConstruction, secondConstruction, result)` |

Equality, PDS equivalence, quotient equality, full interactive game
equivalence, all-nonempty-fixed-list not-winning equivalence, conditional equivalence,
distance zero, and construction are different relation constructors.  No
surface synonym licenses coercion among them.

Likewise, `supportedOn(P, D)` and `hasDomain(S, D)` are not paraphrases.  The
first constrains which presentations carry mass; the second describes where a
system answers.  Ambient converter application is unconditional.  A
normalized common-domain `Morphism` instead asserts global preservation of the
embedded image, while `CommonDomainApplicable.ApplicableTo source converter`
is local to a source specification and also requires membership of the
concrete resource.  None of these may be rendered from a total-completion or
support-wise absorption hypothesis.

For specification-local common-domain application, a resource
`R : CommonDomainApplicable.Resource inner` is sent to
`CommonDomainApplicable.apply alpha applicable R admitted`. Its ambient image
is identified by the checked `CommonDomainApplicable.toAmbient_apply` bridge
with `Ambient.RandomSystem.apply alpha
(ProbabilityRandomSystem.toAmbient R)`. `ApplicableTo source alpha`,
`R ∈ source`, and their witnesses belong to this checked application edge;
the source specification and witnesses are not part of the resulting
resource's semantic identity or fingerprint.

The core relation frames are fixed at the semantic-role level.  Quoted text is
an English realization example, not the stored grammar:

| Relation | Semantic roles | Licensed clause plans | Formula policy |
|---|---|---|---|
| `presents` | presentation, behavior | definition: “Let `R` be the random system represented by `P`”; assertion: “`P` represents `R`” | prose; exact bridge expandable |
| `hasBehavior` | system, input/history, response law | operational definition ordered by input, state/history, response | prose plus equations when the law is central |
| `belongs` | resource, specification | “`R` belongs to `Rcal`” or “`R` satisfies specification `Rcal`” | notation for dense quantified statements |
| `preservesCommonDomainCarrier` | ambient DDC | property: “Applying `alpha` to any embedded normalized common-domain system yields a system in the embedded image”; a `Morphism` binder packages `alpha` with this property | no corresponding sentence for unconditional ambient action |
| `applicableToSpecification` | source specification, converter | “`alpha` is applicable to specification `Rcal`” | concrete use also retains the resource-membership premise |
| `attachmentEquals` | converter, attachment site/action regime, source, result | fixed-interface RS: “Applying `alpha` to `R` yields `S`”; multi-interface AC: “Attaching `alpha` at `i` yields `S`” | prefer equation when operands are large |
| `serialEquals` | first applied, second applied, composite | “`gamma` applies `alpha` first and `beta` second” | show library notation as an elaboration |
| `enhancementSubtypeEqual` | system, MBO assignment, `GamesFor` value | “Enhancing `R` with the MBO assignment `A` gives the game `G` over `R`” | exact equation `PDS.adjoin R A = G` expandable |
| `enhancementPDGEqual` | system, MBO assignment, PDG | prefer the exact equation `(PDS.adjoin R A).1 = G` | no machine-oriented “PDG underlying the enhancement” clause |
| `forgettingEquals` | game, underlying presentation | “Ignoring the MBO of `G` yields `R`” | exact presentation equality only |
| `forgettingEquivalent` | game, underlying presentation | “The presentation obtained from `G` by ignoring its MBO is equivalent to `R`” | exact registered equivalence only |
| `inducesLaw` | system/game, strategy, horizon/inputs, law | “Interaction of `E` with `R` for `n` rounds induces law `mu`” | prose before any displayed density/mass formula |
| `gameTranscriptEquivalent` | left game, right game | “The games have the same observable transcript law in every environment and horizon” | exact relation preferred in theorem roots |
| `equivalentAsGames` | left game, right game | “For every nonempty fixed query list, the two not-won laws agree” | `G ≡ᵍ H`; this is one global relation, not a relation carrying one list |
| `conditionallyEquivalent` | game, target system | “`G` is conditionally equivalent to `S`” | prefer `G |≡ S`; normalized-conditioning prose requires a separate nonzero-mass bridge |
| `lawEqual` | left law, right law, observation scope | “The two transcript laws agree” | equation for nontrivial laws |
| `uniformOn` / `consistentOnRepeats` | law, input class/history | coordinated clauses under one checked condition | prose plus optional exact law equation |
| mass comparison | law, event, comparator, scalar | “Under `mu`, event `A` has mass at most `eps`” | canonical AST is `Compare(Mass(mu,A), atMost, eps)` |
| advantage comparison | exact advantage kind, real, ideal, observer scope, comparator, scalar | theorem root or reduction consequence | canonical AST is `Compare(Advantage(...), comparator, scalar)` and uses the exact registered notation |
| winning comparison | game, exact strategy class, horizon scope, comparator, scalar | “The blind winning probability of `G` is at most `eps`” | canonical AST is `Compare(WinningProbability(...), comparator, scalar)` |
| `preservesRelation` | established relation, common operation, transformed operands | “This relation remains valid after restricting both sides to admitted histories” | elide repeated operands only when anaphora is safe |
| `constructs` | protocol/converter, source specification, target specification, error | “`pi` constructs `Scal` from `Rcal` within `eps`” | construction notation preferred for theorem roots |

A frame is unavailable when even one role fails its selectional restriction.
For example, the mass-comparison frame cannot accept a system in the law role, and
the `conditionallyEquivalent` frame cannot accept an ordinary system in the
game role merely because both have the same query and answer types.

`PDG.CondEquiv G T` is registered exactly as a two-operand, division-free
product identity over every fixed query list.  Its safe short form is “`G` is
conditionally equivalent to `T`.”  Its safe expanded form states that the
not-won law of `G` and the transcript law of `T` satisfy that product identity.
Only the guarded `condEquiv_iff_condProb` bridge, with its nonzero-mass
hypotheses, licenses prose about equality of normalized conditional laws.

### 6.6 Occurrence contexts and anchors

An occurrence context determines information structure, not truth.  The same
entity or claim can therefore have several valid realizations.

| Context | Abstract form | Presentation obligation |
|---|---|---|
| abstract declaration | `AbstractDeclaration` | introduce kind and interfaces; omit behavior not supplied |
| denotational definition | `DenotationalDefinition` | name the defining constructor or display the equation |
| operational definition | `OperationalDefinition` | order clauses by input, internal calls/state, then output |
| predicate definition | `PredicateDefinition` | preserve iff and temporal/history scope |
| representation definition | `RepresentationDefinition` | relate presentation and behavior without identifying their carrier types |
| role assignment | `RoleAssignment` | establish real, ideal, simulator, or intermediate only within the stated comparison |
| theorem binder | `Binder(given/assumed, entity/property)` | aggregate compatible independent binders; retain dependencies |
| theorem root | `Claim(theoremRoot)` | foreground the root relation and its principal operands |
| local result | `AnchoredClaim(localResult)` | state mathematical content; expose a label only if later reference needs it |
| side condition | `Claim(sideCondition)` | show only when non-canonical or mathematically explanatory |
| proof opening | `Orient` | orient the reader to the system comparison and selected route |
| preservation | `Apply(.preserve, ...)` | refer to the established relation and state the common operation |
| reduction | `Apply(.reduce, ...)` | state the mathematical consequence and new foreground obligation |
| instantiation | `Apply(.instantiate, ...)` | fix an arbitrary entity with all scope-changing restrictions |
| case analysis | `Split` | state the mathematical partition and retain exhaustive/disjoint coverage |
| induction | `Induct` | identify the parameter and invariant; aggregate routine base/step mechanics only after coverage is checked |
| calculation | `Calculate` | use a displayed homogeneous chain; narrate conceptual register changes |
| estimate | `Apply(.estimate, ...)` | identify law, event, quantifier scope, and bound |
| closure | `Conclude` | return to the theorem-root register |
| repeated reference | `Reference(active/reintroduced)` | choose symbol, short noun phrase, or anaphor only when unambiguous |
| diagnostic disclosure | `formalArtifact` | show exact Lean expression, theorem, or goal without pretending it is prose |

Proof anchors are separate from claims:

```text
structure AnchoredClaim where
  anchor? : Option SemanticAnchor
  claim : Claim
```

An anchor exists so later proof nodes can refer to a checked claim.  It is not
part of the proposition and must not be rendered as “call this fact …”.  A
Verbose language may display an author-required anchor typographically, for
example as a `Fact` or `Claim` label.  Informalization may omit the Lean name,
use a mathematical short description, or display the label in an expansion.

Single-use claims normally remain unlabelled.  A source identifier such as
`idealNonnegative` is never itself evidence that the fact deserves a sentence.
`OccurrenceContext.claimMode?` is the sole owner of theorem-root,
local-result, side-condition, and displayed-equation status; an anchor cannot
override it.

### 6.7 Entity-context realization matrix

The examples below are canonical *frames*, not fixed strings.  Mathematical
notation and registered terminology may replace prose when clearer.

#### Carriers, interfaces, and histories

| Entity | Definition or binder context | Statement context | Proof and later-reference context |
|---|---|---|---|
| carrier/type | “Let `X` be a type.” | usually a dependent modifier, not the theorem subject | use the symbol `X`; do not repeat “the type” |
| finite alphabet | “Let `X` be a finite alphabet.” | “The system has input alphabet `X`.” | “Since `X` is finite …” only when finiteness drives counting |
| input/output signature | “Let the input and output alphabets be `X` and `Y`.” | “`R` is an `(X,Y)`-system.” | refer to “the input alphabet” only when contrasting interfaces |
| interface/port | “Let `i` be an interface of `R`.” | “`alpha` is attached at interface `i`.” | “At this interface …”; never erase a material attachment site |
| dependent interface family | introduce the index and the type of each indexed interface | state attachment or routing with its index | retain dependencies; never aggregate binders as though all ports had one homogeneous type |
| query/answer | introduced by an operational clause | “On query `x`, the system returns `y`.” | use `x` and `y`, or “this query/answer” with a unique antecedent |
| input history | “Let `xs` be an input history.” | “`A` holds on `xs` exactly when …” | “on this history” within the same scope |
| attempted history | introduce explicitly when refusal is observable | “The attempted history records accepted and refused queries.” | do not shorten to “transcript” if refusal information matters |
| transcript | “Let `t` be the transcript induced by `R`, `E`, and `n` rounds.” | “The two transcript laws agree.” | “for every good transcript `t` …” |
| fixed query/message list | introduced by non-adaptive fixation | “The list contains at most `q` admitted queries.” | “for this fixed list”; never imply one universal list for all strategies |
| encoded blocks/call site | operational or predicate definition | “The call site has round-function input `z`.” | use message and block position when collision identity matters |

#### Systems and presentations

| Entity | Definition or binder context | Statement context | Proof and later-reference context |
|---|---|---|---|
| abstract random system | “Let `R` be an `(X,Y)`-random system.” | “The systems `R` and `S` are equivalent/at distance at most `eps`.” | “the source system,” “the target system,” or the symbols after roles are established |
| behaviorally defined system | “Define `R` by the conditional response laws …” | state the resulting behavior, not the implementation | refer to “the system `R`” |
| operationally described system | “The system behaves as follows: on …” | an operational correctness claim relates this description to the behavior | later use the mathematical system, not the pseudocode block |
| DDS | “Let `s` be a deterministic discrete-system presentation.” | “`s` answers `y` after history `h`.” | remain presentation-level unless a quotient bridge is supplied |
| signed PDS | “Let `P` be a PDS law over DDS presentations.” | “`P` is nonnegative/has weight `w`/is equivalent to `Q`.” | do not call `P` a probability distribution without an exact normalization property |
| subprobability PDS | introduce `P : PDS X Y` together with explicit `PDS.IsProbability P` evidence | state only the property actually needed | this means nonnegative weight at most one, not unit weight or a new carrier |
| normalized law over DDSs | introduce `P : Distribution.ProbDist (System.DDS X Y)` | state its presentation/embedding relation | structural nonnegativity and unit weight may be suppressed on this actual weight-one carrier |
| presentation/behavior pair | “Let `R` be the random system represented by `P`.” | state the exact representation or quotient bridge | later prose may say `R`; expanded detail retains `P` and the bridge |
| common-domain presentation | introduce the shared domain explicitly | “The presentations are equivalent on the common domain.” | preserve the fixed-domain witness across the argument |
| ambient presentation | name the total attempted-history carrier when material | “Applying `alpha` gives the ambient presentation `P'`.” | do not conflate with the common-domain carrier |
| quotient/random system | “Let `R` be the random system presented by `P`.” | use equality/distance on the correct quotient | hide representative plumbing only through a checked bridge |
| `PDS.equivalent` | relation between fixed-interface PDS presentations | state equality of every total-environment transcript law | do not merge with strict-distinguisher `PDS.Equivalent` |
| `PDS.Equivalent` | relation tested by strict `Unit`-to-`Bool` distinguisher protocols | state equality of acceptance mass for every such distinguisher | use only the checked bridge when converting to transcript equivalence |
| `Ambient.PDS.Equivalent` | relation between normalized attempted-history presentations | state ambient transcript equivalence | do not coerce it to either fixed-interface relation by shared spelling |
| resource | “Let `R` be a resource with interfaces `I`.” | “`R` belongs to specification `Rcal`.” | use “resource” in construction register and “system” in behavior register, connected explicitly |
| real/ideal system | establish by the construction/model bridge | use the exact registered advantage or distance quantity for the theorem | “the real system” and “the ideal system” only after validated role assignment; these roles never license `Δ`, which is reserved for `PDS.classDistance` |
| URF/URP/ideal function | prefer a checked symbolic definition such as `R := URF(X,Y)` or `P := [q] URP(X)` | use conventional symbols or short names | prose is reserved for operational behavior that the notation does not already express; never manufacture “the uniform random ...” from a Lean name |
| restricted/transformed system | “Let `[q]R` denote `R` restricted to `q` queries.” | “Restricting both systems preserves …” | “the restricted system” only when unique |
| parallel system | define from an ordered family and routing convention | state componentwise behavior or a parallel relation | retain order and shared-bus/interface structure |

#### Converters and attachment

| Entity | Definition or binder context | Statement context | Proof and later-reference context |
|---|---|---|---|
| abstract converter | “Let `alpha` be a converter with outside signature `U` and inside signature `X`.” | “Attaching `alpha` to `R` yields `S`.” | “the converter” only when no simulator/protocol converter competes for salience |
| operational converter | define outside input, inside calls, replies, state update, and outside output | state a checked application or behavior theorem | later use its mathematical name; do not repeatedly narrate its implementation |
| identity/blocking converter | derived definition from the standard constructor | state identity or access-blocking effect | normally short symbolic reference |
| query/domain restriction | “Let `[q]` be the converter admitting at most `q` queries.” | “Applying the restriction yields `[q]R`.” | “after restricting both sides …” |
| block restriction | define admitted histories using encoding and total block budget | state applicability/preservation under the restriction | use “the block restriction,” not an unexplained `theta` on first mention |
| serial composite | “Let `gamma` apply `alpha` first and `beta` second.” | display the library notation after checking its order | “the composite converter”; never infer order from multiplication typography |
| parallel composite | define ordered components and interfaces | state the parallel application law | preserve routing and component order |
| simulator | introduce as a converter at the ideal/adversarial interface | “Using `sigma` as simulator, …” only in a simulation construction | do not call an arbitrary converter a simulator from its name |
| protocol | introduce the interface-indexed converter family | “The protocol constructs `Scal` from `Rcal`.” | refer to components only when the proof descends to an interface |
| attachment/application | derived entity or exact equation | “Attaching `alpha` at `i` gives `S`.” | equality replacement may refer to “this attachment identity” |
| common-domain global preserver | property of an ambient fixed-interface DDC | “Applying `alpha` to any embedded normalized common-domain system yields a system in the embedded image.” | `PreservesImage alpha` is the property; a `Morphism` is a separate structure that packages `alpha` with its proof |
| specification-local applicability | relation between source specification and converter | “`alpha` is applicable to specification `Rcal`.” | concrete application also retains `R ∈ Rcal`; do not restate unconditional ambient action as applicability |

#### Games, strategies, laws, events, and quantities

| Entity | Definition or binder context | Statement context | Proof and later-reference context |
|---|---|---|---|
| monotone condition/MBO assignment | define the history predicate or DDS-indexed condition assignment and prove monotonicity separately | “The condition has occurred by history `h`.” | “outside the collision event”; never use the vague phrase “monitored for collisions” |
| game | “Define `G` from the DDG/PDG data …” | state the exact full-game, not-won, or conditional relation | “the collision game” only after that role is established |
| game over a fixed system | introduce `G : GamesFor R`, whose membership is `PDS.equivalent (PDG.forget G) R` | state properties that depend on sharing the underlying behavior | do not strengthen membership to representative equality |
| game with ignored MBO | define through `ForgetMBO(G)` or an exact identity | “Ignoring the MBO of `G` yields `R`.” | use the identity as a bridge, not as game equivalence |
| restricted/transformed game | derived from game plus restriction/transform | “The conditional equivalence remains valid after …” | “the restricted game” only when unique |
| partial environment | “Let `E` be an environment compatible with the accepted-history interface.” | appears in domain-sensitive interaction and `Adv` | do not silently totalize it or switch to attempted histories |
| total environment | introduce the attempted-history signature | appears in fully-defined/ambient interaction and winning | retain that refusal is observable |
| partial or ambient PDE | introduce its exact environment carrier and signed/normalized law | appears in the matching randomized interaction quantity | never merge signed partial `RandomSystems.PDE` with normalized total `Ambient.PDE` |
| strict distinguisher | introduce the `Unit`-to-`Bool` strict converter protocol | state its acceptance-mass difference | do not model it as a DDE plus a separate decision rule |
| winner role | assign a total environment the role relative to one game/horizon | “`E` wins `G` after `n` rounds.” | preserve game and horizon; do not create a `Winner` entity |
| blind/non-adaptive strategy | assume or prove the exact non-adaptivity relation | “Its query schedule is fixed before replies are observed.” | then introduce the strategy-dependent fixed list |
| fixed-query environment | define it from the exact list and stopping convention | state the corresponding fixed-list law or mass | do not identify it with every non-adaptive environment without the registered bridge |
| source/transcript/output law | define by the inducing system, strategy, inputs, and horizon | state equality, support, uniformity, consistency, or mass | “under this law” only with one salient law |
| normalized conditioned law | define law plus event and a nonzero normalizing mass | state the exact guarded equality | keep condition scope over all coordinated output clauses |
| not-won law | define the unnormalized false-MBO slice from game, total environment, and horizon | use for `EquivalentAsGames` or `CondEquiv` product identities | call it a slice/law, not a probability law; signedness requires a separate premise |
| coupling/joint law | define joint plus both marginals | “The executions disagree with probability at most `eps`.” | call it a coupling only after nonnegativity and marginals are checked |
| signed expansion | define algebraic law difference | state the signed identity and norm bound | never use coupling vocabulary |
| collision/freshness event | define exact witnesses and equality criterion | state implication, cover, or mass bound | “this event” only inside the same visible scope |
| good event | define as the complement of the registered bad event | state laws conditioned on it | avoid introducing an independent good predicate when the theorem fixes `not Bad` |
| weight/mass/probability | normally derived quantity, not an entity paragraph | display `mass_mu(A) <= eps` or state the experiment in prose | canonical packaging may be hidden; the law and event remain recoverable |
| `Adv`, `AdvD`, `Adv⊥`, ambient advantage | define only when introducing the theory or a local abbreviation | foreground the exact comparison, normally with notation | retain environment class, carrier, totality, output test, and orientation through every proof hop |
| class distance `Δ` | define as the honest-equivalent-representative infimum when the theory is being introduced | use `Δ(S,T)` on its exact PDS carrier | retain one-sided orientation unless equal weight supplies symmetry |
| quotient `edist` | identify the quotient carrier and its installed defining metric | use `edist S T` | `PDS.Behaviour`, ambient, and normalized common-domain quotients have different metrics; every bridge is explicit |
| adaptive/blind winning probability | identify the game and the exact total-environment/horizon class | state the exact bound/equality | distinguish unrestricted from non-adaptive observers |
| static winnability | identify the honest `NonNeg`, `PDG.gameEquivalent` representative family and the source-law mass of `System.Winnable` | state the exact infimum bound/equality | never introduce a strategy/environment class or conflate it with adaptive/blind winning |
| budget/error/cardinality | introduce parameters or named formulas | prefer conventional mathematics | mention cast/normalization only in expanded formal detail |

#### Specifications, constructions, proofs, and formal artifacts

| Entity | Definition or binder context | Statement context | Proof and later-reference context |
|---|---|---|---|
| specification | “Let `Rcal` be the specification of resources satisfying …” | membership, inclusion, relaxation, or construction | do not silently replace a resource by its singleton specification |
| construction | introduce source, target, converter/protocol, interfaces, and error | foreground “`pi` constructs `Scal` from `Rcal` within `eps`” or established notation | descend through an explicit realization bridge and return in the conclusion |
| bad event/reveal/hybrid/coupling | explicit proof choice, introduced before use | appears in the selected proof-route schema | never inferred merely because one could make the proof work |
| theorem application | not ordinarily introduced as an entity | its conclusion is a claim with typed premise roles | state the mathematical consequence, not “apply theorem `foo`” |
| named local claim | canonical Verbose source wraps a registered assertion as `Fact name: ASSERTION by PROOF` | mathematical proposition independent of its source name | the anchor changes the assertion destination, not its ontology rule; use it only when later references require it; never print “call this fact” |
| proof term | no reader-facing definition | licenses a claim through its inferred type and application structure | available in diagnostic expansion |
| tactic event | no mathematical entity form | before/after goals may decode to a move | never translate the tactic name into prose |
| coercion/packaging goal | formal side condition | normally no ordinary sentence | retain evidence coverage and show in diagnostic expansion |
| unsupported expression | exact formal artifact | safe symbolic claim only | mark unsupported rather than inventing fluent language |

### 6.8 Proof-move grammar

Proof prose is generated from checked derivations and their effect on the
foreground claim.

```text
structure DerivationApplication where
  rule : RuleId
  operands : Array TypedCheckedOperand
  consumedPremises : Array CheckedPremise
  residualObligations : Array ResidualObligation
  conclusion : CanonicalClaim
  formula? : Option FormulaTerm
  exactSource : Expr
  exactType : Expr
  provenance : Provenance
  evidence : EvidenceAnchor

structure TypedCheckedOperand where
  role : ArgumentRole
  value : Expr
  exactType : Expr
  originalType? : Option Expr

structure CheckedPremise where
  key : ObligationKey
  schema : PremiseSchema
  salience : Salience
  proposition : CanonicalClaim
  exactProposition : Expr
  proof : Expr
  provenance : Provenance

structure ResidualObligation where
  key : ObligationKey
  schema : ResidualSchema
  salience : Salience
  proposition : CanonicalClaim
  exactProposition : Expr
  evidence? : Option EvidenceAnchor

MoveKind
  = establish | preserve | substitute | reduce | instantiate | estimate | lift

structure CalculationLink where
  left : QuantityExpr | EntityExpr
  relation : comparator | equalityRelation
  right : QuantityExpr | EntityExpr
  derivation : DerivationApplication
  conclusionMatches :
    derivation.conclusion = relationClaim(left, relation, right)

Move ::=
    Orient(rootClaim, comparisonSpine, selectedRoute)
  | Apply(application : DerivationApplication)
  | Split(currentClaim, partition, branches)
  | Induct(parameter, motive, baseCases, stepCases)
  | Calculate(nonemptyCheckedLinks : Array CalculationLink)
  | Conclude(rootClaim, establishedRoot : EstablishedClaimRef)
  | Expand(claim, subargument)
  | RecordRoutine(before, after, coverage)
```

`MoveKind` is read from the unique registered `InferenceSchema` selected by
`DerivationApplication.rule`; `Move.Apply` does not accept a second freely
chosen kind.  In particular, one bound theorem cannot independently become
`establish`, `derive`, and `estimate`.  Every calculation link carries a
checked equality between the derivation conclusion and its displayed relation.
`Conclude` references an already established proof of the root claim; it does
not infer the root from a loose array of supporting claims.

The principal Random Systems proof routes are schemas over these moves:

| Route | Required explicit choices | Principal derivation shape | Typical visible consequence |
|---|---|---|---|
| exact reshaping | systems, equality/equivalence or deterministic map | `Apply`; schema kind `preserve` or `substitute` | the same comparison after a checked representation change |
| data processing/context | observation or converter/context and exact regime premises | `Apply`; schema kind `preserve` | applying the common operation cannot increase the chosen distance |
| conditional equivalence | game, target system, CE proof, exact theorem premises | `Apply`; schema kind `reduce` | advantage is bounded by the appropriate winning probability |
| H-technique | real/ideal laws, transcript predicate, ratio/equality loss, bad-mass loss | reducing `Apply`, then estimating `Apply` nodes for its obligations | the distance is bounded by the combined losses |
| coupling | honest joint law and both marginals | establishing/estimating `Apply` nodes under one route schema | distance is bounded by disagreement probability |
| representative selection | equivalence class and explicit selection theorem | instantiating/substituting `Apply` nodes | the same system comparison is represented by selected laws |
| winnability | exact game and theorem hypotheses | `Apply`; schema kind `establish` | winning probability is identified with or bounded by winnability in the theorem's scope |
| hybrid/game hop | explicit intermediate systems or games | reducing `Apply` plus `Calculate` | the comparison splits into named legs |
| reduction | explicit reduction object, source comparison, target game/problem | `Apply`; schema kind `reduce` | it suffices to solve the target problem and correctness obligations |
| signed expansion | exact signed identity and norm/positive-part bridge | establishing `Apply`, then `Calculate` | cancellation yields a valid scalar bound; no coupling claim is made |
| counting | law, event, quantifier scope, cover/fibers, finite estimate | estimating `Apply`, then `Calculate` | the event mass is at most the numerical expression |
| construction lifting | system comparison and realization/CC bridge | lifting `Apply`, then `Conclude` | the scalar bound proves the original construction |

Proof-route names never replace their mathematical consequences.  “Apply the
H-coefficient theorem” is incomplete unless the generated move exposes the
good-transcript and bad-mass obligations.  Conversely, a direct registered
theorem may package a route into one `Apply` move when its exact operands and
premises are retained in the evidence graph.

Premises carry a visibility class independent of their Lean syntax:

| Visibility | Criterion | Treatment |
|---|---|---|
| defining choice | simulator, ideal system, bad event, coupling, reveal, hybrid, restriction, route | always explicit |
| substantive premise | changes the mathematical argument or may fail for the object at hand | visible claim or visible condition of the inference |
| canonical invariant | uniquely follows from the registered constructor and has no independent choice | may be absorbed into the domain inference while remaining expandable |
| routine formal premise | coercion, packaging, propositional normalization, elementary scalar closure after the mathematical estimate | omitted from ordinary prose with evidence coverage |
| implicit ambient capability | canonical typeclass structure not needed to understand the claim | normally omitted; available in theorem context/detail |

Nonnegativity illustrates why this classification is contextual.  For a
registered normalized URP presentation, nonnegativity is a canonical invariant
and should not become a sentence.  For an arbitrary-mass law used by an H or
coupling theorem, nonnegativity may be a material hypothesis and must remain
visible.  The word `nonnegative` alone does not determine salience.

### 6.9 Composition and naturalness constraints

1. **No untyped noun substitution.**  Resource, behavioral random system, PDS
   presentation, game, and specification can share a symbol only through
   explicit presentation or register bridges.
2. **No name-as-content.**  Lean identifiers and proof anchors support
   reference; they are not clauses.  Generated mathematics never says “call
   this fact `h`.”
3. **No one-use bureaucracy.**  A claim used once is normally embedded as the
   premise of the inference it supports rather than introduced and immediately
   cited by name.
4. **Given before new.**  Introduce given carriers, systems, and assumptions
   before derived games, events, laws, and bounds.  Dependencies block unsafe
   aggregation.
5. **Operation before result for definitions.**  Operational descriptions
   follow interaction order: outside input, inside calls/replies, state change,
   outside output.
6. **Result before mechanics for proofs.**  Proof sentences lead with the
   mathematical consequence; the theorem name, detailed premises, and formal
   transformations belong in subordinate or expanded material.
7. **Formula/prose complementarity.**  Use formulas for exact equalities,
   inequalities, construction notation, and long typed relations.  Use prose
   for operational behavior, causal structure, proof orientation, and register
   transitions.  When both are useful, the formula elaborates the prose claim
   rather than duplicating it.
8. **Scope preservation.**  Conditions such as “outside collision,” “by round
   `i`,” “for every environment,” and “for this fixed list” dominate exactly
   the clauses justified by the checked proposition.
9. **Register continuity.**  A paragraph may move from construction to system,
   game, law, scalar, and algebra only along registered bridges, and must return
   to the theorem-root register at closure.
10. **Reference safety.**  Anaphora is allowed only with one compatible visible
    antecedent in the current disclosure scope.
11. **Aggregation by truth conditions.**  Merge introductions, premises, or
    estimates only when the semantic arguments, quantifier scope, polarity,
    and discourse relation remain unchanged.
12. **Fail closed.**  Unsupported semantics yield exact notation or a marked
    formal expansion, never plausible invented crypto prose.

### 6.10 Typed language representation

The current canonical semantic layer should remain the mathematical source of
truth.  Between it and final `String` realization, add a genuinely linguistic
representation along these lines:

```lean
inductive Register
  | formal | construction | system | game | law | scalar | algebra

inductive InformationStatus
  | new | given | contrastive | reintroduced

inductive DiscourseRelation
  | definition | elaboration | cause | result | preservation
  | reduction | instantiation | bound | combination | conclusion

structure ReferencePlan where
  referent : SemanticId
  status : InformationStatus
  form : ReferenceForm        -- symbol, full NP, short NP, safe anaphor

structure PredicateFrame where
  id : PredicateFrameId
  relation : RelationId
  subjectRole : ArgumentRole
  complementRoles : Array ArgumentRole
  voice : Voice
  complementFunctions : Array (ArgumentRole × GrammaticalFunction)
  selection : Array OntologyConstraint

structure LanguagePredicateFrame where
  language : LanguageId
  semanticFrame : PredicateFrameId
  lexicalHead : LexemeId
  prepositions : Array (ArgumentRole × SurfaceToken)
  linearization : LinearizationTemplate

inductive ClauseContent
  | definition (value : EntityDefinition)
  | description (value : EntityDescription)
  | claim (value : AnchoredClaim)
  | move (value : Move)
  | formalFallback (source : Expr)

structure ClausePlan where
  semanticAnchor : SemanticId
  content : ClauseContent
  occurrenceContext : OccurrenceContext
  register : Register
  frame? : Option ValidatedFrameSelection
  arguments : Array ReferencePlan
  connective? : Option DiscourseRelation
  polarity : Polarity
  formula? : Option MathObject

structure ParagraphPlan where
  clauses : Array ClausePlan
  discourseEdges : Array DiscourseEdge
  expansionChildren : Array ParagraphPlan
```

The discourse act is derived by
`actOfContentAndContext content occurrenceContext`; the same claim can thus be
an assumption, assertion, or conclusion without a contradictory mutable act
field. A `ValidatedFrameSelection` proves that the semantic frame
belongs to the content relation and that every argument satisfies its role.
Language-specific prepositions and word order occur only in
`LanguagePredicateFrame`, never in the neutral plan.

`ClausePlan.semanticAnchor` identifies the semantic node. It is not the
author's optional proof anchor and cannot replace `AnchoredClaim.anchor?`.

The exact types may differ, but the separation is binding:

```text
checked expression
  -> canonical mathematical object/relation
  -> clause plan with grammatical roles
  -> paragraph plan with discourse relations
  -> surface strings and formulas
```

`Sentence.text` is the final product, not a place to store semantics.
`MoveKind` is useful for proof planning, but it is too coarse to serve as a
sentence grammar.

The predicate frame is selected *from* `content`; it does not replace it.  A
clause therefore retains a quantified or conditional claim, a definition, an
operational description, or a proof move even when the English surface uses
the same finite verb.

### 6.11 Independent modules with a shared language design

`/verbose` and `/informalization` are independent modules with different jobs,
but both should consume a neutral shared language design.

```text
                         shared language design
                    ontology, rules, roles, frames
                         /                 \
                    /verbose         /informalization
                        |                   ^
                        v                   |
ordinary Lean ------> elaborated, checked Lean
generated proof ----/
```

The shared design contains:

- ontology concept and relation identifiers;
- mathematical derivation-rule identities;
- semantic argument and obligation roles;
- predicate valency and selectional restrictions;
- register and discourse-relation vocabulary; and
- the schema for optional presentation annotations.

The modules do not share their operational machinery.  `/verbose` owns rigid
CNL syntax, parsing, diagnostics, and lowering to deterministic `rs_*` proof
steps.  `/informalization` owns evidence recovery, canonicalization, proof
planning, compression, reference management, and final realization.  Neither
module is a stage inside the other.

Informalization starts on the right of that diagram.  It must not depend on
which source syntax produced the proof, and it must not trust a CNL sentence
identifier in place of checked semantic evidence.  Ordinary tactics, proof
terms, macros, and a Verbose-style frontend must all be accepted as input.  If
their checked evidence canonicalizes to the same derivation, the core semantic
fingerprint should agree; this does not require identical proof-plan
granularity or surface presentation.

A Random Systems CNL uses the shared design to name the same mathematical
subjects, relations, and consequences that the informalizer later recognizes.
Its rigid sentences should lower to deterministic `rs_*` proof steps.  That
frontend has its own criteria:
unambiguous parsing, predictable elaboration, good errors, and explicit
non-canonical choices.  Reader prose has different criteria: aggregation,
reference management, paragraph rhythm, and selective detail.  Textual
round-tripping between those two surfaces is neither required nor desirable.
Verbose-specific names, sentence boundaries, annotations, and elaboration
shape may therefore lead to legitimate presentation differences.  Those
differences should be visible in presentation provenance rather than erased or
mistaken for changes in mathematical meaning.

This separation also follows Massot's stated scope: Verbose Lean is a
teaching-oriented, rigid input language, not a proposed universal replacement
for ordinary Lean, while a posteriori natural-language presentation is a
different goal.

The required interaction between the modules is ordinary checked Lean.  An
optional second interaction is shared presentation metadata: `/verbose` may
emit an annotation, and `/informalization` may consume it, but the same
annotation facility must also be available to handwritten Lean.  Such metadata
remains advisory and never substitutes for checked evidence.

### 6.12 Proof-independent author guidance

Authors should be able to guide the presentation regardless of whether the
proof was written in Verbose Lean or ordinary Lean.  Comments, labels, and
options therefore form an optional **presentation side channel** attached to
stable semantic anchors after checked semantics have been recovered:

```text
checked Lean -> canonical semantics -> proof/discourse plan
                                             +
                              validated presentation guidance
                                             |
                                             v
                                      surface realization
```

Four strengths of guidance should be distinguished.

1. **Layout controls** may request a paragraph break, choose the initial
   expansion state, label an expansion, or order independent supporting
   claims.
2. **Constrained realization hints** may choose a registered short name,
   active/passive voice, symbol/full/short reference form, or a connective
   already licensed by the discourse graph.
3. **Semantic-role proposals** may suggest an ontology role, argument role, or
   proof-rule role, but take effect only if validated against the elaborated
   expression, declaration signature, operands, and goal transformation.
4. **Verbatim author prose** may add motivation or commentary.  Because it is
   not kernel-checked, it must remain visibly and structurally marked as an
   author note and must not replace a generated mathematical claim.

The current controlled-language reference annotation is one small example:

```text
construction ("authentication leaves the encryption key unchanged")
```

Its string is ignored by Lean but may be retained for the reader.  The general
facility must not be confined to controlled-language syntax: an ordinary Lean
proof needs an equivalent declaration annotation, command, or structured
comment form.

Useful presentation controls for CBC include:

- label this claim as “the collision game” for later reference;
- prefer “block restriction” as the first description of `theta_r`;
- place a paragraph break before the blind-winning estimate;
- realize a checked preservation edge with “this remains true after …”; and
- attach an author note explaining why the collision game is the conceptual
  pivot of the proof.

The following controls are forbidden:

- changing a formula, operand, converter order, event, system, or bound;
- hiding a substantive node required by evidence coverage;
- forcing a causal connective when no checked causal edge exists;
- assigning real/ideal or other mathematical roles without validation; or
- presenting arbitrary author prose as compiler-justified mathematics.

Presentation-only guidance does not affect the semantic fingerprint.  A
separate presentation fingerprint records it.  An invalid or stale anchor must
produce a diagnostic rather than silently moving the annotation to a nearby
proof step.  Semantic annotations affect the plan only after validation; if
validation fails, the checked interpretation wins.

## 7. Inference rules from Lean to compiled sentences

Use three explicit judgments:

```text
Gamma ; profile |- expression => semantic object
discourse ; context |- semantic object => clause plan
discourse |- clause plans => paragraph plan
```

The first judgment is checked and fail-closed.  The latter two may choose among
licensed stylistic variants, but may not add mathematical content.

### R1. Registered grounding

If the elaborated head declaration has a profile entry with checked argument
selectors, decode it to the registered concept or relation and retain the exact
operands and source expression.

```text
head(e) = h    profile(h) = (relation k, selectors sigma)
all selectors match the declaration telescope
--------------------------------------------------------
Gamma ; profile |- e => k(sigma(e))
```

If a selector or declaration signature fails, do not guess from the printed
name.

### R2. Structural composition

Recursively decode registered constructors such as converter application,
serial composition, restriction, enhancement with an MBO, ignoring an MBO, and scalar
measurement.  Preserve opaque children exactly when a known outer constructor
contains an unsupported operand.

This rule produces the compositional meaning of expressions such as the real
CBC system; it does not yet choose a sentence.

### R3. Formal-evidence normalization

Two proof fragments with the same checked conclusion and the same canonical
rule/operands/obligations produce the same semantic application even if one is
written using `rw`, another with `simpa`, and another as a `calc` chain.

Tactic identity is erased only after evidence coverage is recorded.

### R4. Entity introduction

When a semantic referent is new in a definition or theorem context, realize a
full noun phrase using its concept entry, modifiers, dependencies, and symbol.
Compatible independent introductions may be aggregated using Kyle's merging
and agreement rules.  Dependent or contrastive referents may not be merged.

### R5. Relation-to-clause realization

Select a predicate frame whose selectional restrictions match the ontology
classes of all operands.  Assign the semantic arguments to grammatical roles
before choosing words.

```text
relation = constructs
roles = converter, target resource, source resource, error
----------------------------------------------------------
“CBC constructs the ideal resource from the round-function resource
 within error epsilon.”
```

No generic subject--verb--object template is used for relations with different
valency.

### R6. Root foregrounding

The semantic head of the theorem becomes the main clause.  In particular, a
`ConstructsWithin` root is stated as a construction even when its Lean proof
immediately unfolds to an `edist` inequality.

The lower-level inequality becomes supporting discourse reached through the
`realizes`/`establishesConstruction` bridges.

### R7. Operational definition

For a new converter, use its typed inside/outside interfaces and behavior
relations to build one or more clauses: accepted outside inputs, calls at the
inside interface, and returned outside outputs.  A bare copular sentence (“CBC
is a converter”) is insufficient when the behavior is available.

### R8. Representation and role assignment

When a checked bridge relates a presentation `P` to behavioral object `R`,
introduce `R` as represented by `P`; do not make them grammatically co-referential
without that bridge.  When an existing system becomes the real side, ideal
side, or an intermediate of a comparison, record a scoped role assignment.
The role expires with that comparison and is never inferred from an identifier.

### R9. Predicate/event definition

For a new condition whose definition is an equivalence, use an iff frame and
retain temporal/history scope:

```text
A_i holds exactly when a nontrivial collision has occurred by round i.
```

Do not flatten `by round i`, `before the next query`, or `on the current
history` into an unscoped adjective such as *bad*.

### R10. Causal inference

When a checked application uses premise `P` to derive `Q`, and the rule profile
marks `P` as the mathematical cause rather than bookkeeping, link the clauses
with a causal relation:

```text
Since the encoding is prefix-free, distinct messages have distinct terminal
round-function inputs outside the collision event.
```

This requires the intermediary claim to be decoded; theorem application alone
does not license a fabricated explanation.

### R11. Conditioning and exception scope

When a law is asserted under the complement of a bad event, realize the event
as a condition on the law.  Coordinate uniformity and consistency with the
correct scope:

```text
On the collision-free slice, the output law satisfies the checked
factorization in Fact outputLaw. Repeated-message consistency is stated
separately when it is present in the checked theorem.
```

Do not paraphrase the factorization as normalized conditioning or uniformity
unless those properties occur explicitly in the checked theorem.

The exception is a second positive law, not an informal afterthought.

### R12. Precision elaboration

When a prose claim and an exact equality/conditional-equivalence proposition
have the same semantic content, place the intuitive clause first and attach
the formula as an elaboration.  Do not output two unrelated peer sentences.

This models the common mathematical rhythm “informal interpretation; more
precisely, equation.”

### R13. Preservation under a common operation

Given a registered preservation theorem whose operands expose a common
restriction, transform, or context, refer anaphorically to the established
relation and name only the new operation:

```text
Restricting the game and the ideal system to admitted histories preserves
their conditional equivalence.
```

Do not restate both large systems unless reference resolution would be
ambiguous.

### R14. Equality-guided substitution

If a checked equality rewrites one operand of the current claim, introduce the
equality as a discourse bridge and state the resulting claim.  Whether Lean
used `rw`, `simpa`, or `calc` is irrelevant.

For a previously displayed equation, use an equation reference; otherwise
name the mathematical identity itself.

### R15. Registered theorem application

When a named paper-level rule is applied and its conclusion is not already
obvious from the preceding causal relation, state the rule and result:

```text
The conditional-equivalence theorem therefore bounds the advantage by the
blind winning probability of the collision game.
```

Mention a theorem number only when source-oriented exposition calls for it and
the citation is registered.  Internal Lean declaration names are not prose.

### R16. Goal shift/reduction

Once the current claim has been reduced to a scalar or subordinate game bound,
make the new foreground explicit:

```text
It remains to bound the blind winning probability of the restricted collision
game.
```

This is a discourse inference from the proof plan, not a theorem in Lean.

### R17. Non-adaptive schedule fixation

When the selected strategy is checked to be non-adaptive, introduce an
arbitrary strategy and the query/message list determined before replies are
seen.  Carry its budget as an explicit modifier or following assumption.

This rule bridges the game register to fixed-list combinatorics.

### R18. Per-schedule estimate

Instantiate the event-mass theorem with the fixed list, name the random source,
and state the bound.  Then lift the uniform per-schedule bound to the supremum
using the registered blind-winning rule.

The list, admissibility condition, event, distribution, and numerical bound
must all remain operands of the derivation.

### R19. Bound chaining

Aggregate a chain of compatible equalities/inequalities, eliding only repeated
terms whose identity is checked.  Choose causal prose for conceptually
different bounds and a displayed chain for homogeneous scalar calculations.

### R20. Construction closure

When the system comparison is the registered realization obligation of the
root construction, return to the construction register and state that the
bound establishes the original construction.

This final bridge prevents a proof from ending abruptly at a number.

### R21. Reference safety

Use “this,” “the former,” “the game,” or omitted repeated material only when
there is exactly one compatible salient antecedent in the current expansion
scope.  Otherwise repeat a short noun phrase or symbol.

Expansion boundaries create child discourse scopes; they may inherit symbols
but not unsafe anaphora to hidden text.

### R22. Routine compression

A checked region may disappear from ordinary prose only when its before/after
semantic content differs by a registered routine equivalence: definitional or
coercion normalization, singleton/specification bookkeeping, packaging,
propositional normalization, or elementary closure of an already stated
scalar fact.

The tactic name is neither necessary nor sufficient.  Every omitted region
receives an evidence-coverage entry.

### R23. Safe fallback

If semantic grounding, relation framing, reference resolution, or evidence
coverage fails, retain the exact checked expression and expose a symbolic or
explicitly unsupported expansion.  Never choose fluent but unlicensed crypto
prose.

Reader-visible propositions have a two-stage mathematical rendering contract.
The selected semantic profile first renders recognized relations and entities
with its registered notation.  Otherwise a structural Lean-expression printer
produces conservative LaTeX while preserving the checked expression's
application and operator structure.  Raw Lean or kernel source belongs only in
developer provenance; it is not a reader-facing fallback.  The source proof is
not required to import presentation modules or notation attributes.

## 8. CBC paragraph generated by the improved rules

The target is not a fixed golden paragraph, but the rules above should support
a paragraph of this shape:

> CBC, followed by the block restriction `theta_r`, constructs the restricted
> ideal message function from the `r`-query random round function within the
> CBC collision bound.  To prove this, compare the attached real system with
> the restricted ideal system.  Define an MBO on the real system that is 1 if
> and only if two nontrivial CBC call sites reach the same round-function
> input; enhancing the real system with this MBO gives the collision game.
> On collision-free transcripts, the output law factors into the ideal output
> law and the mass of avoiding the collision event.  This factorization
> establishes that the collision game is conditionally equivalent to the ideal
> system.
> Restricting the game and the ideal system to admitted
> message histories preserves this conditional equivalence.  The
> conditional-equivalence theorem therefore bounds the
> distinguishing advantage by the blind winning probability of the restricted
> collision game.  A blind strategy fixes its message list in advance, and the
> restriction ensures that the list contains at most `r` blocks in total.  The
> CBC collision estimate bounds the bad-event mass for every such list by the
> stated birthday term.  Embedding the two restricted systems and applying
> `theta_r` then gives the attached real and ideal systems.  The resulting distance
> bound proves the construction.

Each sentence is licensed by a different semantic rule.  No sentence is
selected from the spelling of a Lean tactic.  The exact product identity may
be shown in an expansion.  Fresh-output uniformity and repeated-message
consistency may become separate generated claims only after stable checked
lemmas expose those propositions; this compiler policy is not prose in the
mathematical paragraph.

## 9. Linguistic comparison with Kyle and CR18

### 9.1 What Kyle gets right

Kyle's examples, including the Rudin-style statements, benefit from several
sound linguistic decisions:

- mathematical referents are explicit entities rather than accidental Lean
  substrings;
- concepts, properties, and relations are ontology entries;
- noun phrases carry articles, plurality, inline forms, and dependent
  accessories;
- compatible introductions are aggregated;
- proposition rendering is recursive;
- tactic descriptions produce structured proof steps rather than one flat
  paragraph; and
- the `Explanation` document keeps text, formulas, goal states, and expandable
  detail distinct.

This is why theorem introductions such as “Let `X` be a compact topological
space…” can sound natural: the ontology supplies a stable head noun and
properties, and English agreement combines them into a conventional noun
phrase.

### 9.2 Why this is insufficient for crypto

From a linguistic standpoint, Rudin-style theorem prose is often
**entity-descriptive**: introduce spaces, sets, functions, and hypotheses, then
assert a relation among them.  CBC proof prose is strongly **eventive and
discourse-dependent**:

- objects change role as the exposition moves between construction, system,
  game, law, and scalar registers;
- converters have interface-sensitive behavior and ordered attachment;
- events have history and temporal scope;
- conditional laws require careful exception structure;
- reductions change the current foreground goal;
- later sentences refer to established equations and propositions with
  anaphora; and
- the same mathematical object is described first operationally, then
  probabilistically, then extensionally by a bound.

A noun/adjective ontology can say what CBC *is*.  It cannot by itself say why
prefix-freeness leads to distinct terminal inputs, why that yields a uniform
consistent law, or why the remaining task is a non-adaptive collision bound.
Those require predicate valency, typed bridge relations, information status,
and discourse structure.

### 9.3 CR18 stress test

The following table tests the first plausible realization rule against the CBC
proof around Theorem 6.1, then records the correction.

| CR18 discourse move | Naive/Kyle-style result | Failure | Improved rule | Verdict |
|---|---|---|---|---|
| introduce the CBC converter by its outside and inside behavior | “Let CBC be a converter.” | grammatically sound but informationally empty | R7 operational definition with interface roles | handles the content if interface behavior is registered |
| define the collision bit through what has happened by query `i` | “Let `A_i` be bad.” | loses iff structure and temporal scope | R9 predicate definition | handles the definition |
| clarify which equalities count as nontrivial collisions | attach “nontrivial” as an adjective | adjective does not encode the exclusion criterion | event subtype/refinement plus elaboration edge | requires a decoded collision-site relation |
| infer distinct terminal inputs from prefix-freeness outside collision | output two separate claims | loses the causal relation and proof direction | R10 causal inference | handles it when the intermediary claim is present in evidence |
| describe outputs as uniform but consistent on repeated messages | “outputs are uniform except repeats” | exception scope is vague and may be mathematically false | R11 coordinated positive laws | handles distinct/fresh and repeated cases explicitly |
| follow intuition with an exact conditional-law equation | emit duplicate peer sentences | misses precision/elaboration structure | R12 precision elaboration | handles the rhetorical relation |
| say the established equivalence survives restriction to admitted histories | repeat the full large formula | correct but heavy and unnatural | R13 preservation plus safe anaphora | handles it compactly; `theta_r` appears only at the later common-domain-to-ambient application bridge |
| use a prior converter identity to rewrite the real system | narrate `rw` or silently change terms | tactic-dependent or creates a logical jump | R14 equality-guided substitution | handles `rw`/`simpa`/`calc` uniformly |
| apply the conditional-equivalence theorem | “apply theorem X” | states an action but not its mathematical consequence | R15 names the rule and resulting bound | handles the reduction |
| announce that only the winning estimate remains | no sentence because no theorem proves it | loses proof orientation | R16 goal shift | requires discourse planning beyond proposition rendering |
| explain blindness as choosing messages in advance | “fix an environment” | does not convey non-adaptivity or fixed schedule | R17 schedule fixation | handles the game-to-combinatorics bridge |
| estimate collision for every fixed admitted list | show only the inequality | hides the random experiment and quantified schedule | R18 per-schedule estimate | handles it if list/admissibility operands are retained |
| conclude the CC construction | stop at the scalar inequality | loses the theorem's original shape | R20 construction closure | handles the return to the top register |

### 9.4 Honest assessment after the stress test

The rules are strong enough to reproduce the **argument structure** and most
of CR18's local rhetorical moves, but they do not make naturalness automatic.
The following remain genuine hard problems:

1. **Granularity selection.**  Lean may expose several small lemmas where CR18
   uses one causal sentence, or one large theorem where the paper gives an
   intuitive sentence and a precise equation.  The proof plan needs registered
   semantic macro boundaries.
2. **Exception scope.**  Uniformity together with consistency for repeated
   messages is easy to phrase misleadingly.  The ontology must distinguish
   fresh-message uniformity from repeated-input equality.
3. **Equation deixis.**  “Using the preceding identity” requires stable
   discourse anchors that survive interactive expansion and reordering.
4. **Anaphora across hidden detail.**  A collapsed paragraph cannot use “this
   event” if the event was introduced only inside a closed expansion.
5. **Information packaging.**  Whether to state an intuitive explanation, an
   equation, or both is a discourse choice not recoverable from proposition
   syntax alone.
6. **Source rhetoric.**  Words such as “obvious,” “of course,” and “easily” in
   papers express author stance, not checked mathematical content.  The system
   should not generate them.
7. **Domain knowledge.**  Operational descriptions of CBC and `theta_r`
   require registered interface and state-machine facts; they cannot be
   inferred safely from arbitrary unfolded code.
8. **Stylistic variation.**  The rules license natural clauses, but preventing
   monotony across a long proof requires controlled aggregation and lexical
   choice without changing semantic identity.

Accordingly, the correct claim is not that these rules “solve natural
language.”  They provide the missing typed basis on which natural paragraph
planning can be tested.  CR18 should remain an adversarial corpus: every
generated sentence must be checked for truth conditions, reference clarity,
register continuity, and idiomaticity by comparison with the source argument.

## 10. Required changes to the current implementation

The present system already has valuable typed operands and provenance, but its
linguistic boundary is too coarse:

- `EntityRole` lacks many construction, game, law, and CBC-specific concepts;
- `RelationRole` and `DerivationRule` do not yet expose all bridge relations;
- `Discourse.MoveKind` mixes mathematical planning with prospective wording;
- `Realize.Sentence.text` and `Detail.text` are opaque strings rather than the
  realization of clause plans; and
- reference status, predicate valency, register, and discourse relations are
  not first-class.

The audit also found concrete prototype behavior that must not be carried
forward:

- `LanguageDesign/Grammar.lean` currently provides only a small register and
  predicate-label vocabulary; it needs the indexed catalog in Section 6, not
  more untyped labels;
- `LanguageDesign/Corpus.lean` now separates checked formal relations from
  public linguistic licenses. Generic unattested prose remains pending, while
  switching and CBC fallback evidence is keyed by the exact application or
  declaration; the remaining task is to extend exact locators across the
  breadth corpus;
- several Random Systems relation forms collapse presentation equivalence,
  quotient equality, not-won game equivalence, and conditional equivalence
  into generic equality/equivalence prose;
- the canonical-property form that prints “by construction; call this fact”
  confuses proof anchoring with a declarative mathematical sentence and is
  rejected by Sections 6.6 and 6.9;
- the fixed-schedule prototype sentence combines non-adaptivity, transcript
  extraction, filtering, and a mass identity in one clause; these are separate
  `Apply` moves whose registered inference schemas classify them respectively
  as instantiation, establishment, and estimation, with separate failure
  points;
- the registered `proofThetaPreservation` entry is misnamed: public
  `CBCMAC.applySystem_theta` is an exact complete-history attachment equation
  at the ambient bridge, not the admitted-history preservation theorem. Retain
  its operand decoding, rename the rule accordingly, and give it
  checked-library/fallback provenance distinct from `condEquiv_filterDom`;
- the rejected provisional theorem-header macro printed `Δ([q] URF,[q] URP)`
  while elaborating `PDS.advFullyDefined`; the implemented canonical bound
  now retains the advantage kind and prints `Adv⊥`, reserving `Δ` for class
  distance; and
- the production `Theorem`/`Given`/`Conclusion`/`Proof`/`QED` command now
  preserves the elaborated declaration type, telescope, conclusion, title, and
  detailed sentence trace; additional binder profiles remain breadth work.

The extension should therefore:

1. retain the existing checked evidence and canonical semantic layers;
2. expand ontology profiles with concepts, relation frames, and bridge
   relations rather than theorem-shaped prose strings;
3. add `Register`, `InformationStatus`, `ReferencePlan`, `PredicateFrame`,
   `ClausePlan`, and `DiscourseRelation` between `Discourse` and `Realize`;
4. make paragraph aggregation and anaphora operate on semantic identifiers,
   not repeated text;
5. compile final strings and formulas only after the clause/paragraph plan is
   complete; and
6. preserve fail-closed fallback and full evidence coverage throughout.

This is an adaptation plan for the current architecture.  It is not license
to retain experimental syntax until a replacement exists: semantically false
or linguistically rejected forms are removed from the active surface and may
survive only as negative fixtures.

## 11. Acceptance tests for the language layer

String snapshots alone are not sufficient.  The suite should test:

- **ontology coverage:** every CBC spine operand has a typed concept and every
  cross-register step has a registered bridge;
- **frame well-typedness:** relation frames reject subjects or complements of
  the wrong ontology class;
- **clause-plan goldens:** semantic inputs produce the expected speech act,
  register, roles, references, and discourse link before surface realization;
- **source invariance:** `rw`/`simpa`/`calc`, inline/named helper, premise
  reorder, and routine explicit/automated variants yield the same paragraph
  plan and semantic fingerprint;
- **authoring-language independence:** ordinary Lean and
  Verbose/controlled-language proofs are both supported without frontend
  coupling; when they canonicalize to the same derivation their semantic
  fingerprints agree, while source-sensitive discourse and surface text may
  legitimately differ;
- **presentation noninterference:** layout and realization hints do not change
  formulas, evidence coverage, or the semantic fingerprint;
- **guidance validation:** incompatible terminology, discourse connectives,
  semantic-role proposals, and stale anchors fail explicitly;
- **provenance distinction:** verbatim author notes remain structurally
  distinct from compiler-justified sentences;
- **semantic sensitivity:** changing a system, converter order, event, query
  budget, or bound changes the relevant plan;
- **reference safety:** ambiguous anaphora is rejected; collapsed and expanded
  views each have self-contained antecedents;
- **content preservation:** every assertion in prose is entailed by a checked
  claim or licensed discourse relation, and every substantive CBC claim is
  represented;
- **CR18 move coverage:** the stress-test rows in Section 9.3 have fixtures at
  the clause and paragraph level;
- **register continuity:** the complete CBC paragraph has explicit checked
  paths from construction to scalar analysis and back;
- **routine-compression coverage:** every hidden formal region has an evidence-coverage entry
  and neither uniformity nor collision mass is classified routine; and
- **humanity review:** compare complete generated paragraphs, not isolated
  sentences, for referential clarity, rhythm, redundancy, and mathematical
  emphasis.

## 12. Source map

- Kyle Miller, *Informalizing formal mathematics*, ICERM talk, especially the
  slides on general architecture, ontologies, theorem-paragraph entities,
  grammar, tactic describers, `Explanation`, and proof-term decompilation.
- Patrick Massot, *Teaching Mathematics Using Lean and Controlled Natural
  Language*, ITP 2024, and the `verbose-lean4` repository.  These sources
  describe a separate controlled-language authoring interface and explicitly
  distinguish that goal from a posteriori natural-language presentation.
- Maurer--Renner 2016, Sections 2--3: specifications, constructions,
  composability, systems, interfaces, converters, and attachment.
- Jost's thesis: discrete systems, environments, monotone binary outputs,
  events, game relations, and the source-level proof vocabulary joining them.
- Liu--Maurer 2020, Definitions 3--6: random systems, resources, parallel
  composition, converters, and the distinction between behavior and its
  descriptions.
- Lanzenberger, thesis Chapter 2, Definitions 2.20--2.28: monotone conditions,
  deterministic/probabilistic games, hidden condition bits, winning
  probability, and random-system distance.
- Coretti--Rösler 2018, Theorem 4.17 and Section 6.2.3/Theorem 6.1: the
  conditional-equivalence/blind-winning reduction and CBC proof discourse.
  This remains **CR18-FALLBACK/CORPUS** under repository provenance rules.
- Checked Lean modules:
  `Applications/CBCMAC/Objects.lean`, `Applications/CBCMAC/Probability.lean`,
  `Applications/CBCMAC/Construction.lean`,
  `Applications/CBCCombinatorics.lean`, and the relevant `RandomSystems`
  game/conditional-equivalence modules.

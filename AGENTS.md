# Working in abstract-crypto

This file is the operational guide for coding agents and human contributors.
It applies to the entire repository. Read `THEORY.md`, the owning module's
documentation, and the cited primary source before changing a public
mathematical declaration.

## Mission and boundaries

The repository implements the carrier-agnostic layers of Maurer-style
Abstract and Constructive Cryptography. Keep the dependency direction strict:

```text
Applications -> ConstructiveCryptography.MultipartyComputation
             -> ConstructiveCryptography -> AbstractCryptography
RandomSystemsCC -> AbstractCryptography
RandomSystems core -/-> abstract-crypto
```

`AbstractCryptography.EventAlgebra` is orthogonal and Mathlib-only. Do not pull it
into the AC/CC root merely because one application uses both theories.

The source hierarchy is binding: MauRen16, then Jost, LiuMau20/Liu-Zhang,
then Lanzenberger. CR18 is fallback-only: consult it only for a concept none
of those primary sources addresses, and say so explicitly.

The current CR18 fallback register is deliberately narrow:

- finite i.i.d. and clone powers of distributions;
- the bounded-query random-system filter;
- almost-universal and 2-universal hashing;
- the bounded-functional statistical-distance exercise;
- collision and Shannon entropy results not developed by the primary sources;
- the CBC-MAC construction statement of CR18 Theorem 6.1, while Maurer 2002
  remains the source for its probability and distance bound.

Other surviving CR18 citations are historical provenance, not semantic
authority. Extending this register requires a source audit against Jost and
the other primary sources.

Every theory-level modeling review must assess Jost explicitly, not merely
list it in the bibliography. State whether Jost requires the proposed
structure, derives the needed theorem from weaker hypotheses, treats it as an
optional specialization, or rules it out. A conclusion reached from MauRen16
alone remains provisional until this comparison is recorded.

The working discipline is MR16-only until an explicit MR11 reconciliation
task. MauRen11-specific choice-setting, distinguisher-indexed metric,
simulation, two-party, and step-wise-refinement modules are not part of the
current production tree. Do not recreate them piecemeal or describe
`filteredAt` as MauRen11 choice setting.

## Read before acting

1. Read `README.md` for module ownership and build targets.
2. Read `THEORY.md` and the owning module's documentation for modeling
   invariants, notation, and the canonical proof shape.
3. Read the live declaration and its surrounding docstring.
4. For mathematical changes, read the original PDF pages cited by the
   declaration. PDFs in the sibling `random-systems/papers/` tree are the
   authority; notes and plans are secondary evidence.
5. If the task is MPC/FROST or sponge-specific, read the corresponding active
   plan. Do not revive a deleted completion ledger.

## Non-negotiable modeling rules

- AC equality assumes an already-quotiented resource carrier.
- Raw converter equality is not justified by equality of on-tree behavior.
  Off-tree values can break identity and associativity; canonicalize the
  complete-history function, or quotient by the corresponding trace relation,
  before exposing a DDC.
- Paper-level partial attachment must be restricted or totalized before it is
  exposed as a `MulAction`.
- Serial converters compose in category order; contravariant attachment then
  applies the inner converter before the outer converter.
- Zero pseudo-distance is not generic equality. Separation must be an explicit
  property of the selected quotient or metric.
- Do not assume parallel associativity, commutativity, flattening, or
  `π ∥ 1 = π`. Use the ordered public laws actually available.
- A type-correct action on the ambient heterogeneous RS carrier does not prove
  preservation of a restricted subcarrier.
- Keep scalar error budgets and bounded test outputs conceptually separate.
  `ENNReal` error addition is not silently truncated at one.
- Generic AC/CC statements remain polymorphic in the interface type. Add
  finiteness only where the modeled object is genuinely finite.
- Every branch-finite attempted-history DDC acts automatically on the ambient
  normalized random-system quotient. Do not require a per-converter
  congruence or absorption witness for that default action.
- Literal common-domain equivalence quantifies over DDEs that are compatible
  with the shared domain and stop. A morphism of that source-specific carrier
  is an ambient DDC whose ambient action preserves the embedded common-domain
  image; attachment is the unique preimage under the injective embedding.
  Never replace this with a stronger total-completion or support-wise
  absorption condition.

If a proposed proof needs to violate one of these rules, stop and revisit the
model rather than forcing Lean to accept the statement.

## Change protocol

For each public mathematical change, establish these facts before editing:

1. **Source contract:** paper, section/page, hypotheses, and exact conclusion.
2. **Modeling delta:** quotient versus raw carrier, equality versus
   equivalence, total versus partial action, homogeneous versus typed
   interfaces, and any stronger Lean assumption.
3. **Consumer probe:** one awkward intended AC, CC, or RS use case.
4. **Name and owner:** the declaration belongs in the semantic module that
   owns its principal concept.
5. **Small change:** one declaration or one dependency seam plus immediate
   consumers. Avoid opportunistic theorem-family rewrites.
6. **Verification:** focused build, representative downstream build, axiom
   check for important endpoints, and forbidden-pattern scans.

Prefer a short compilable probe to speculative API design. Remove temporary
probes after the result is captured in a durable test or docstring.

## Proof workflow

Start at the outermost stable theorem and work inward.

1. State the final construction, distance, or property endpoint.
2. Choose the proof route explicitly: direct metric, simulator, conditional
   equivalence, coupling, H-coefficient, hybrid, or reduction.
3. Name the intermediate systems, transcript/reveal, bad event, and budgets.
4. Use the AC proof language for deterministic assembly.
5. Prove program equivalence, probability, coupling, counting, or algebra in
   the owning lower layer.

Use these commands instead of unfolding specifications and relaxations:

```lean
ac_construct using distanceBound
ac_transport using converterEquality
ac_transport construction using converterEquality
ac_simulator simulator
ac_filtered using simulatorSupport, distanceBound
ac_compose firstLeg, secondLeg
ac_parallel leftLeg, rightLeg
ac_context_left context using construction
ac_context_right context using construction
ac_transfer_property D using admitted, ideal, close, test
```

Use `ac?`, `ac_normalize?`, or
`trace.AbstractCryptography.ProofAutomation.rule` to inspect deterministic rule
selection. These diagnostics do not license broader proof search.

### Controlled-language extensions

The scoped controlled language follows the canonical workflows documented by
its owning tactic modules; it is not a second proof API. Each sentence must:

- use a sentence form attested by the Maurer-style source corpus;
- name the mathematical subject and consequence, not the underlying tactic;
- lower to one existing deterministic `ac_*`, `cc_*`, or `rs_*` backend;
- keep every non-canonical cryptographic choice as an explicit Lean term; and
- have positive, negative, grammar, and sentence-trace tests.

Use the controlled-language module documentation as the vocabulary authority.
In particular, use phrases such as `The construction follows
from ...`, `Replacing ... using ..., we obtain ...`, and `The construction
follows by composing ...`. The simulator and context workflows use `We use
simulator to prove the construction` and `With context as the right parallel
context, the construction follows from baseConstruction`. Do not call a generic
proof a certificate, and do not describe ordinary equality replacement as
transport in controlled prose.

Use `We have name : statement by ...` for a named intermediate construction.
This is a real local fact, modeled on Verbose Lean's named `Fact`/`Claim`
forms. Do not let automation invent names in long cryptographic proofs.
Controlled references may carry a quoted reader annotation,
`construction ("why this leg has this meaning")`; its text is ignored by Lean
and must never contain evidence needed by the proof. Elsewhere, use ordinary
Lean comments for non-semantic prose.
In this literature, `certificate` denotes a concrete cryptographic object;
`transport` is implementation terminology rather than Maurer-style argument.

Do not manufacture English wrappers for `have`, `show`, `calc`, cases, or
induction when Lean already reads like the paper. Judge a new sentence in the
context of a complete representative proof, not as an isolated tactic slogan.

The tactic line terminates the sentence; do not add a final full stop. Parse
ordinary prose words as identifiers and validate them with
`CryptoControlledNaturalLanguage.expectWord`, so the language does not reserve
common mathematical names.

AC owns shared syntax infrastructure and `ac.*` sentences. CC and
`RandomSystemsCC` extend the same `CryptoControlledNaturalLanguage` scope in
their own modules with `cc.*` and `rs.*` trace identifiers. Never add concrete
carrier vocabulary to
`AbstractCryptography.Tactics.ControlledNaturalLanguage`.

### H-coefficient and transcript proofs

Use this section order:

```text
Model
Representatives
TranscriptExtension
BadEvent
GoodRatio
BadMass
MainLemma
ConstructionOrReduction
```

The general workflow is mechanical: define systems, define the extended
transcript laws, partition good/bad transcripts, apply the ratio/bad-mass
theorem, and discharge the remaining combinatorics. The reveal, partition, and
bad event remain explicit. If `MainLemma` contains the scheme's full collision
case tree, refactor the recurring bounds and counting lemmas first.

## Automation policy

Be ambitious about deterministic automation and conservative about semantic
choices.

Good automation:

- shrinking normalization with a concrete firing-site test;
- applying one named paper theorem;
- assembling explicitly named construction proofs and bounds;
- adding errors and normalizing action order;
- replacing a converter using a supplied equality;
- applying a supplied support, commutation, or non-expansion proof.

Bad automation:

- selecting an ideal resource, simulator, reveal, bad event, corruption
  pattern, or proof route;
- unrestricted `simp`, `aesop`, `grind`, or environment search in public
  tactics;
- typeclass search for proof witnesses that are not canonical capabilities;
- finite enumeration used to conceal a symbolic theorem;
- a tactic that becomes a second semantic API.

When a recurring obligation has a stable mathematical statement, add the
named theorem first. Add a tactic only when applying that theorem is itself a
deterministic paper step.

The public AC tactic implementation may use only curated registries and small,
named reconciliation rewrites. New rules require positive, negative, and trace
tests in the proof-language test module.

## Typeclasses and instances

Use typeclasses for canonical ambient structure:

- monoids and actions;
- non-expansion laws;
- one selected parallel operation;
- one selected probability/totality capability;
- closure of an explicitly chosen feasible model.

Keep non-canonical choices and their proofs as explicit terms or structures. A
proof-bearing class is acceptable only when its index contains every choice
and the instance is installed locally after those choices are fixed.

Never register `mulActionOfAttach`, a concrete tuple action, or a metric chosen
from a non-canonical observation class globally on types that may receive
another such instance. Use `letI` or a wrapper carrier.

## Performance and computability

Routine CC proofs should almost never hit heartbeat limits.

- Do not raise `maxHeartbeats` or `maxRecDepth` to make an ordinary proof pass.
- Do not introduce `Fintype I` or enumerate `Fin n` merely to compose a short
  proof.
- Prefer `Nat`-indexed traces and explicit finite-support witness sets for long
  hybrids.
- Keep dependent transcript/reveal values out of instance search.
- Use `simp only` with rules known to shrink the expression.
- Profile failure paths as well as successful elaboration.

Executable cryptographic code and security proofs are separate layers. Do not
unfold a complete hash or curve implementation in a security theorem.

- Prefer structurally recursive executable definitions.
- For small kernel-reducible test vectors, use `decide +kernel`.
- Use `native_decide` only in a quarantined non-default test target when
  compiled evaluation is necessary, and record its trust implication.
- A heartbeat bump is a symptom to diagnose, not a normal optimization.

## Cross-repository work

This repository owns the standalone fixed-interface `RandomSystems` layer,
the optional DDC extension, and the `RandomSystemsCC` adapter. When touching
an integration seam with a sibling consumer:

- keep pure `RandomSystems` independent of AC/CC;
- put abstract instances only under `RandomSystemsCC`;
- establish one fixed interface before adding typed sums or parallel routers;
- prove behavior/action congruence rather than relying on stale quotient
  artifacts;
- coordinate before editing files being changed by another RS worker;
- do not count a stale `.olean`, a smoke action, or a default mismatch branch
  as a validated instantiation.

RS integration is accepted only after quotient, action, metric,
non-expansion, restricted-carrier preservation, and every used parallel law
have separate proofs. For the default ambient carrier, quotient congruence and
non-expansion come from branch-finite DDC observation factorization. For a
literal common-domain subcarrier, the converter must preserve the embedded
image; total-completion DDE absorption is not a substitute.

## Proof-widget changes

`CCWidget.lean` is the single theory-free rendering engine shared with the RS
repository. Keep it independent of AC/CC theory. Semantic libraries register
declaration roles at optional adapter/import boundaries; do not teach the
renderer by matching fragile pretty-printed text.

Preserve these visual invariants:

- abstract named interfaces remain undirected unless the owning semantic
  adapter provides a direction;
- serial converters stay on one interface in application order;
- parallel resources visibly share a bus/grouping;
- real and ideal views use stable mirrored ports;
- adversarial/simulator interfaces have one consistent role;
- distance, winning, and construction notation remains selectable Lean code;
- dark and light themes are both checked.

Parser guards prove recognition only. A widget change also requires building
the registered adapter surfaces and visually inspecting representative
renderings. Do not
register a semantic role when there is no actual view delta, and never
resurrect a deleted algebra merely to improve a diagram.

## Naming and ownership

- Theorem names use `snake_case`; structures/classes use `UpperCamelCase`;
  data and function declarations use `lowerCamelCase` where appropriate.
- Public Random Systems vocabulary uses DDS, DDC, DDE, and PDS. Avoid
  operational names such as `run`, `exec`, `step`, `fuel`, `scheduler`, and
  `reset` for mathematical objects and operations.
- Preserve an existing declaration name as one atom inside theorem names, for
  example `mem_filteredAt_iff` and `edistD_self`.
- State the principal operation and formal conclusion: `_iff`, `_eq`, `_le`,
  `_subset`, `_mono`, `_of_`, or `_comp`.
- Do not use paper numbers, task numbers, author initials, or proof-method
  words in public theorem names.
- Source citations belong in docstrings, not public identifiers.
- Avoid compatibility aliases unless a real external consumer needs a
  deprecation period.

## Documentation policy

Documentation describes the current library and active unresolved work.

- A paper-derived definition, theorem, or proof step carries a concise verbatim
  quotation with the exact source definition or theorem and printed page.
  Paraphrase only the Lean representation or a repository-specific modeling
  choice; never repeat a quotation as a paraphrase.
- In proofs, use short local comments to expose every paper-level mathematical
  step, including routine steps. Omit comments only for Lean bookkeeping; do
  not replace the local proof outline with one large introductory block.
- Remove conversational design iterations, progress reports, and internal
  planning labels from permanent source and documentation.
- Do not create completion ledgers, percentage reports, chronological audit
  dumps, or one-file-per-audit notes.
- Put theorem-specific source and modeling facts in its docstring.
- Put reusable mathematical architecture in `THEORY.md` and proof guidance in
  the owning module documentation or this file.
- Put contributor rules and recurring failure modes here.
- Keep a plan file only while the work is genuinely active; delete completed
  stages instead of preserving a victory log.
- Update or remove every live reference when a document is renamed or deleted.

Repository cleanup is preservation-first. A file is not deletion material
merely because it has no current consumer, is untracked, is small, or has an
awkward name. Delete only material proved temporary or superseded, or material
whose removal was explicitly approved. Every intentional module must be
reachable from its proper public root or from a named focused build target.

## Verification recipes

For an AC semantic or proof-language change:

```bash
lake build AbstractCryptography
lake build AbstractCryptographyProofAutomationTests
lake build AbstractCryptographyConstructionWorkflowTests
lake build ConstructiveCryptography ConstructiveCryptographyMultipartyComputation Applications.Frost
```

For public-boundary changes, also build the sibling consumers:

```bash
cd ../ccprover && lake build CCProver
cd ../random-systems && lake build RandomSystems
```

Run the relevant static checks:

```bash
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' AbstractCryptography
rg -n 'maxHeartbeats|maxRecDepth|native_decide' AbstractCryptography
lake env lean --src-deps AbstractCryptography.lean
git diff --check
```

Important public endpoints should receive a `#print axioms` check. The normal
accepted envelope is no larger than `propext`, `Classical.choice`, and
`Quot.sound`; an unexpected project axiom or `sorryAx` is a failure.

## Active plans

- `MPC_TSS_PLAN.md`: unresolved ConstructiveCryptography.MultipartyComputation/FROST carrier and reduction work.
- `SPONGE_PROOF_PLAN.md`: unfinished concrete sponge indifferentiability proof.
- `FUNCTIONAL_RS_REWRITE_PLAN.md`: the pending acceptance gate for the unified
  `ResourceAlgebra`, Random Systems instantiation, and CBC application.

If a plan has no unresolved work, remove it and migrate any lasting lesson to
source documentation, `THEORY.md`, or this file.

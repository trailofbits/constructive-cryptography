# Working in abstract-crypto

This file is the operational guide for coding agents and human contributors.
It applies to the entire repository. Read `LIBRARY_GUIDE.md` before changing a
public mathematical declaration.

## Mission and boundaries

The repository implements the carrier-agnostic layers of Maurer-style
Abstract and Constructive Cryptography. Keep the dependency direction strict:

```text
Applications -> ConstructiveCryptography.MultipartyComputation
             -> ConstructiveCryptography -> AbstractCryptography
RandomSystemsCC -> selected abstract layer
RandomSystems core -/-> abstract-crypto
```

`AbstractCryptography.EventAlgebra` is orthogonal and Mathlib-only. Do not pull it
into the AC/CC root merely because one application uses both theories.

The literal MauRen11 choice-setting/CFR layer is
`AbstractCryptography.Specification.ChoiceSetting` (MR11-DEFERRED — see LEDGER
PROVENANCE FENCE). Do not silently advertise `filteredAt` as
that construction: `filteredAt` is the choice-free endpoint-pattern
specialization, and the two are separate endpoints.

**The source hierarchy is binding** (LEDGER.md top; PHI-SPEC R8): MauRen16,
then Jost, LiuMau20, Lanzenberger; **CR18 is fallback-only** (consult it only
for concepts in LEDGER's CR18-FALLBACK register, and flag the use).

**The working discipline is MR16-only** until an explicit MR11 reconciliation
task. Every MauRen11-specific module — the distinguisher class and its metric,
the carrier taken up to that metric, the distinguisher-indexed relaxation and
the simulation notion over it, the choice-setting layer, the two-party case,
step-wise refinement — is behind the provenance fence and collected under
`AbstractCryptography.MR11`. Nothing is deleted and everything still compiles;
what is forbidden is an MR16-track file importing a fenced module, and
`scripts/ledgerAudit.sh` fails on it. Read `LEDGER.md` "PROVENANCE FENCE
(MR11-DEFERRED)" before adding an import or a module.

## Read before acting

1. Read `README.md` for module ownership and build targets.
2. Read the relevant part of `LIBRARY_GUIDE.md` for modeling invariants,
   notation, and the canonical proof shape.
3. Read the live declaration and its surrounding docstring.
4. For mathematical changes, read the original PDF pages cited by the
   declaration. PDFs in the sibling `random-systems/papers/` tree are the
   authority; notes and plans are secondary evidence.
5. If the task is MPC/FROST or sponge-specific, read the corresponding active
   plan. Do not revive a deleted completion ledger.

## Non-negotiable modeling rules

- AC equality assumes an already-quotiented resource carrier.
- Raw converter equality is not justified by equality of on-tree behavior.
  Off-tree junk can break identity and associativity; use a trace/action
  quotient in concrete carriers.
- Paper-level partial attachment must be restricted or totalized before it is
  exposed as a `MulAction`.
- Constructor multiplication is function-composition order: after `π`, then
  `π'`, the label is `π' * π`.
- Zero distinguisher distance is not generic equality. Require explicit
  `Set.SeparatesPoints` only for an observationally complete class.
- Do not assume parallel associativity, commutativity, flattening, or
  `π ∥ 1 = π`. Use the ordered public laws actually available.
- A type-correct action on a heterogeneous RS carrier does not prove protocol
  applicability or output-signature preservation.
- Keep scalar error budgets and bounded test outputs conceptually separate.
  `ENNReal` error addition is not silently truncated at one.
- Generic AC/CC statements remain polymorphic in the interface type. Add
  finiteness only where the modeled object is genuinely finite.

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
ac_transport using protocolEquality
ac_transport construction using protocolEquality
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

The scoped controlled language follows the canonical workflows in
`LIBRARY_GUIDE.md`; it is not a second proof API. Each sentence must:

- use a sentence form attested by the Maurer-style source corpus;
- name the mathematical subject and consequence, not the underlying tactic;
- lower to one existing deterministic `ac_*`, `cc_*`, or `rs_*` backend;
- keep every non-canonical cryptographic choice as an explicit Lean term; and
- have positive, negative, grammar, and sentence-trace tests.

Use the discourse-role table in `LIBRARY_GUIDE.md` as the vocabulary
authority. In particular, use phrases such as `The construction follows
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
carrier vocabulary to `AbstractCryptography.ControlledNaturalLanguage`.

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
- replacing a protocol using a supplied equality;
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

Never register `mulActionOfAttach`, a concrete tuple action, or a
distinguisher-induced metric globally on types that may receive another such
instance. Use `letI` or a wrapper carrier.

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

The sibling `random-systems` repository owns concrete carrier mathematics.
When touching an integration seam:

- keep pure `RandomSystems` independent of AC/CC;
- put abstract instances only under `RandomSystemsCC`;
- use one fixed signature before adding typed sums or parallel routers;
- prove behavior/action congruence rather than relying on stale quotient
  artifacts;
- coordinate before editing files being changed by another RS worker;
- do not count a stale `.olean`, a smoke action, or a default mismatch branch
  as an instantiation receipt.

RS integration is accepted only after quotient, action, applicability, metric,
non-expansion, and any used parallel/feasibility laws have separate proofs.

## Proof-widget changes

`CCWidget.lean` is the single theory-free rendering engine shared with the RS
repository. Keep it independent of AC/CC theory. Semantic libraries register
declaration roles at optional adapter/import boundaries; do not teach the
renderer by matching fragile pretty-printed text.

Preserve these visual invariants:

- anonymous PFun systems show directed query/answer lanes, while abstract
  named interfaces remain undirected unless the semantics provides a
  direction;
- serial converters stay on one interface in application order;
- parallel resources visibly share a bus/grouping;
- real and ideal views use stable mirrored ports;
- adversarial/simulator interfaces have one consistent role;
- distance, winning, and construction notation remains selectable Lean code;
- dark and light themes are both checked.

Parser guards prove recognition only. A widget change also requires building
both demo surfaces and visually inspecting representative renderings. Do not
register a semantic role when there is no actual view delta, and never
resurrect a deleted algebra merely to improve a diagram.

## Naming and ownership

- Theorem names use `snake_case`; structures/classes use `UpperCamelCase`;
  data and function declarations use `lowerCamelCase` where appropriate.
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

- Do not create completion ledgers, percentage reports, chronological receipt
  dumps, or one-file-per-audit notes.
- Put theorem-specific source/modeling facts in its docstring.
- Put reusable architecture and proof guidance in `LIBRARY_GUIDE.md`.
- Put contributor rules and recurring failure modes here.
- Keep a plan file only while the work is genuinely active; delete completed
  stages instead of preserving a victory log.
- Update or remove every live reference when a document is renamed or deleted.

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
- sibling `random-systems/RS_AC_ROADMAP.md`: concrete RS/AC integration.

If a plan has no unresolved work, remove it and migrate any lasting lesson to
source documentation, `LIBRARY_GUIDE.md`, or this file.

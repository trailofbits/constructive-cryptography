# Working in this repository

This file is the operational guide for coding agents and human contributors.
It applies to the entire repository. Before changing a public mathematical
declaration, read [README.md](README.md), the owning module's documentation,
the live declaration with its docstring, and the sources it cites.

## Scope and layering

The repository formalizes Constructive Cryptography on a theory of random
systems with declared domains. Its libraries, under `src/`, form strict layers:

```text
Probability
  -> RandomSystems                         (systems, converters, distances, games)
    -> ConstructiveCryptography            (interfaces, arrows, resources, action,
                                            distance; the classes of cryptographic
                                            algebras and their instance on interfaces;
                                            specifications, constructions, substitution;
                                            the DSL and the proof commands)
      -> Commons                           (ideal systems, security definitions,
                                            schemes and their known-answer tests)
        -> Examples
Tests  (audits of every layer)
```

No module imports a higher layer. `RandomSystems` knows systems and
converters, not interfaces or resources. `ConstructiveCryptography` proves the
laws of resources and converters on the concrete objects, with the transcript
distance. The abstract theory (`ConstructiveCryptography.CryptographicAlgebra`,
`ConstructiveCryptography.Specification` and `ConstructiveCryptography.Construction`)
uses only Mathlib: its classes are assumptions, and `ConstructiveCryptography.InterfaceAlgebra`
instantiates them on interfaces with the concrete objects. The notation and the proof commands
are built on laws already proved below them, and nothing below them imports them. The downstream
ChaCha20-Poly1305 development (`chachapoly-cc`) imports modules of this repository; changes to
public declarations it uses must keep it building.

## Sources

There is no fixed authority ranking among the reference papers. For each
modeling question, compare every relevant source: Maurer–Renner, Jost,
Liu-Zhang–Maurer, Lanzenberger–Maurer, the Cryptography Foundations lecture
notes, Banfi, and the system-algebra literature where applicable. Compare
their exact definitions, hypotheses, abstraction levels and conclusions, and
distinguish a genuine disagreement from different notation or a
specialization of a more general model. Existing Lean definitions and ease of
implementation do not settle a mathematical question.

If the relevant sources are in substantive contention, stop the affected
modeling and implementation work, present the disagreement and candidate
resolutions, and agree on the mathematical solution before proceeding. Do not
silently choose a preferred source, strengthen assumptions, or merge
incompatible definitions.

Reference PDFs are in the sibling `random-systems/papers/` tree; notes and plans
are secondary evidence.

## Modeling rules

- A resource is its cumulative behavior on its interface's domain. Equality of
  resources is equality of all cumulative probabilities; observers
  characterize this relation, they do not define it. Do not introduce a
  second quotient.
- On normalized PDSs, equivalence is equivalently equality of the partial
  next-reply probabilities.
- A converter is an arrow only with its domain guarantee (`MapsDomain`). A
  type-correct action on the ambient carrier does not prove preservation of a
  restricted domain.
- Raw DDC equality is not justified by equality of on-tree behavior. Off-tree
  values can break identity and associativity; canonicalize the
  complete-history function before exposing a DDC.
- Serial converters compose in category order; contravariant attachment then
  applies the inner converter before the outer converter.
- Zero pseudo-distance is not equality. Separation must be an explicit property
  of the selected metric.
- Do not assume parallel associativity, commutativity, flattening, or
  `π ∥ 1 = π`. Use the ordered laws and the explicit associators and unitors.
- Keep scalar error budgets and bounded test outputs separate. `ENNReal` error
  addition is not silently truncated at one.
- Generic CC statements remain polymorphic in the interface. Add finiteness
  only where the modeled object is genuinely finite.
- The observational characterization of distance quantifies over environments
  compatible with the domain that stop. Keep this condition explicit when
  comparing a source's advantage with the library's distance.

If a proposed proof needs to violate one of these rules, stop and revisit the
model rather than forcing Lean to accept the statement.

## Change protocol

For each public mathematical change, establish these facts before editing:

1. **Source comparison:** the relevant sources, sections and printed pages,
   hypotheses, and exact conclusions; resolve substantive disagreements first.
2. **Modeling delta:** raw versus behavioral carrier, equality versus
   equivalence, total versus partial action, homogeneous versus typed
   interfaces, and any stronger Lean assumption.
3. **Consumer probe:** one awkward intended CC or random-systems use.
4. **Name and owner:** the declaration belongs in the module that owns its
   principal concept. Extend the existing carriers and operations; do not
   build a parallel foundation.
5. **Small change:** one declaration or one dependency seam plus its immediate
   consumers.
6. **Verification:** focused build, downstream build, axiom check for
   important endpoints, and the static checks below.

Prefer a short compilable probe to speculative API design, and remove it once
the result is captured in a test or docstring.

## Modeling workflow

Start with the agreed mathematical model and its correspondence to the
sources: their parties, symbols, interfaces, resources, converters, equations
and timing. Describe what each object does on paper before choosing its Lean
representation. For a new construction, make the interfaces and object
signatures explicit, then implement their internals, then state the complete
construction. Only then plan the proof.

Add an encoding, record, wrapper or generalization only when a concrete
requirement of the current object calls for it, and explain its meaning.
Prefer a direct equation or input/output rule where the source defines the
object that way.

Primitive models, application proofs and examples use domain types and
operations such as `≫` and `•` directly. Categorical packaging and inference
plumbing stay in the foundation.

## Proof workflow

Start at the outermost stable theorem and work inward.

1. State the final construction, distance or property endpoint.
2. Choose the proof route explicitly: direct metric, simulator, conditional
   equivalence, coupling, H-coefficient, hybrid, or reduction.
3. Name the intermediate systems, transcript or reveal, bad event and budgets.
4. Use the proof commands for deterministic assembly.
5. Prove program equivalence, probability, coupling, counting or algebra in
   the owning lower layer.

The proof commands (`ConstructiveCryptography.Tactics.Categorical` and
`ConstructiveCryptography.Tactics.Basic`) replace unfolding specifications and relaxations:

```lean
cc_construct using distanceBound
cc_transport using converterEquality
cc_transport construction using converterEquality
cc_simulator simulator
cc_relax using inner, outer with compatibility
cc_compose firstLeg, secondLeg
cc_compose_simulators inner, outer using commutation
cc_parallel leftLeg, rightLeg
cc_context_left context using construction
cc_context_right context using construction
cc_triangle via intermediate
cc_nonexpand
```

`cc?` and `cc_normalize?` show deterministic rule selection; they do not
license broader proof search. Substitution arguments use `cc_calc`,
`cc_substitute` and `cc_substitution_chain`
(`ConstructiveCryptography.Tactics.Substitution`).

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

Define the systems, define the extended transcript laws, partition good and
bad transcripts, apply the ratio and bad-mass theorem, and discharge the
remaining combinatorics. The reveal, partition and bad event remain explicit.
If `MainLemma` contains the scheme's full collision case tree, factor out the
recurring bounds and counting lemmas first.

## Automation policy

Be ambitious about deterministic automation and conservative about semantic
choices.

Good automation:

- shrinking normalization with a concrete firing-site test;
- applying one named paper theorem;
- assembling explicitly named construction proofs and bounds;
- adding errors and normalizing action order;
- replacing a converter using a supplied equality;
- applying a supplied support, commutation or non-expansion proof.

Bad automation:

- selecting an ideal resource, simulator, reveal, bad event, corruption
  pattern or proof route;
- unrestricted `simp`, `aesop`, `grind` or environment search in public
  tactics;
- typeclass search for proof witnesses that are not canonical capabilities;
- finite enumeration used to conceal a symbolic theorem;
- a tactic that becomes a second semantic API.

When a recurring obligation has a stable mathematical statement, add the named
theorem first. Add a tactic only when applying that theorem is itself a
deterministic paper step. New rules need positive and negative tests.

## Typeclasses and instances

Use typeclasses for canonical ambient structure: monoids and actions,
non-expansion laws, one selected parallel operation, one selected probability
capability, and closure of an explicitly chosen feasible model. Keep
non-canonical choices and their proofs as explicit terms or structures. A
proof-bearing class is acceptable only when its index contains every choice
and the instance is installed locally after those choices are fixed. Never
register an action or a metric chosen from a non-canonical observation class
globally; use `letI` or a wrapper carrier.

## Performance and computability

- Do not raise `maxHeartbeats` or `maxRecDepth` to make a proof pass; a
  heartbeat limit is a symptom to diagnose.
- Do not use `decide` or `native_decide` in new proofs or checks. For small
  test vectors, use ordinary kernel-checked equality and simplification proofs.
- Do not introduce `Fintype I` or enumerate `Fin n` merely to shorten a proof.
- Prefer `Nat`-indexed traces and explicit finite-support witness sets for long
  hybrids. Keep dependent transcript values out of instance search.
- Use `simp only` with rules known to shrink the expression.
- Keep executable cryptographic code and security proofs in separate layers;
  do not unfold a complete cipher or hash implementation in a security theorem.

## Naming and ownership

- Do not mark a declaration `private` unless that exact exception was approved.
  Use stable, collision-free public names instead.
- Theorem names use `snake_case`; structures and classes use `UpperCamelCase`;
  data and functions use `lowerCamelCase`.
- Public names use the terminology of the sources, not implementation
  mechanisms. Random-systems vocabulary is DDS, DDC, DDE and PDS; avoid
  operational names such as `exec`, `step`, `fuel`, `scheduler` and `reset`
  for mathematical objects.
- Preserve an existing declaration name as one atom inside theorem names, and
  state the operation and conclusion: `_iff`, `_eq`, `_le`, `_subset`, `_mono`,
  `_of_`, `_comp`.
- Do not use paper numbers, task numbers, author initials or proof-method words
  in public names. Source citations belong in docstrings.
- Propose renames of public declarations as a table before making them. Avoid
  compatibility aliases.
- Source files carry no copyright or license header; `LICENSE` is the only
  license statement.

## Documentation policy

- A paper-derived definition, theorem or proof step carries a concise verbatim
  quotation of the source statement with its printed page. Paraphrase only the
  Lean representation or a repository-specific modeling choice.
- In proofs, short local comments expose each paper-level step; omit them only
  for Lean bookkeeping.
- Put theorem-specific source and modeling facts in the docstring,
  representation and proof guidance in the owning module's documentation, and
  contributor rules in this file.
- Remove design iterations, progress reports and planning labels from
  permanent source and documentation. Do not create completion ledgers or audit
  dumps. Active plans live in the ignored `Scratch/` directory.
- Update or remove every live reference when a document is renamed or deleted.

Cleanup is preservation-first: delete only material proved temporary or
superseded, or whose removal was approved. Every module must be reachable from
its library root.

## Verification

```bash
lake build
rg -n '\bsorry\b|\badmit\b|^\s*axiom\b' src
rg -n 'maxHeartbeats|maxRecDepth|native_decide|bv_decide|decide \+native' src
git diff --check
```

The audit files `src/Tests/Axioms/Systems.lean`, `src/Tests/Axioms/CC.lean`,
`src/Tests/Axioms/Commons.lean`, `src/Tests/DSL/Axioms.lean`,
`src/Tests/Substitution/Axioms.lean` and `src/Tests/AuthenticatedEncryption.lean` print the
axioms of the important endpoints (`lake env lean <file>`). The accepted envelope is `propext`,
`Classical.choice` and `Quot.sound`; any other axiom, including `sorryAx`, is a
failure. For changes to public declarations used downstream, also build
`chachapoly-cc`.

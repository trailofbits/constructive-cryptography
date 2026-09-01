# Constructive Cryptography modeling subworkflow

Use this subworkflow when the requested CC construction is known but the
current resource, converter, random system, carrier, equality, quotient,
interface, action, ownership boundary, or public theorem shape may be wrong.
Its job is to fix the CC semantic contract before proof convenience hardens an
accidental representation into an API.

## Inputs

Collect only evidence relevant to the proposed change:

- the user's functional contract and any exact signature constraint;
- repository instructions and dependency boundaries;
- the live declarations, docstrings, imports, and immediate consumers;
- the owning mathematical source when the declaration is source-derived; and
- one awkward but intended downstream consumer.

Do not treat a current declaration as authority merely because other unfinished
proofs were built around it. Do not treat a desired theorem as evidence that
its present statement is sound.

## Write the source and model contract

For a public mathematical change, record:

1. the source statement, hypotheses, and exact conclusion;
2. the functionality that must survive a representation change;
3. the proposed exact Lean root;
4. the difference between the source object and its Lean representation; and
5. every extra assumption introduced by Lean.

When repository policy requires comparison among several authorities, perform
that comparison explicitly. A secondary note or existing code comment is
navigation evidence, not a substitute for the required source.

## Decide the model before proving it

Make each relevant choice explicit:

| Axis | Questions |
| --- | --- |
| CC role | Which objects are resources, converters, systems, distinguishers, simulators, or interface families? |
| Carrier | Raw values, canonical representatives, subtype, or quotient? |
| Equality | Definitional, extensional, observational, setoid, or metric? |
| Domain | Total, partial, restricted, embedded, or completed? |
| Interfaces | Homogeneous, dependent, typed, summed, or erased? |
| Composition/action | What is the application order, variance, and closure obligation? |
| Construction meaning | Is the root equality, realization, construction within error, simulation, or an RS comparison leaf? |
| Parallel structure | Which ordered laws are actually available, and which tempting symmetry or flattening laws are absent? |
| Structure | Is an instance canonical, or should the choice remain explicit/local? |
| Ownership | Which lowest semantic module owns the declaration without reversing dependencies? |
| Computability | Is this executable data, proof-only structure, or a quotient boundary? |

Reject a model that makes the intended laws true only by ignoring off-domain
behavior, confusing zero distance with equality, globalizing a non-canonical
choice, or moving a downstream theorem upstream together with downstream
dependencies.

Keep the layer boundary explicit: deterministic converter/resource assembly
belongs in the CC spine; behavioral equality, distance, probability, and
counting belong in their owning lower layer. A type-correct ambient action does
not by itself establish preservation of the restricted resource carrier used
by the construction.

Do not salvage a representation merely because it already has many helpers.
Preserve requested functionality, not sunk-cost modeling choices.

## Probe one real consumer

Before building a theorem family, make the smallest compilable probe that
exercises the awkward intended use:

- state the proposed root at the public boundary;
- instantiate or apply it in the consumer's natural notation;
- check coercions, implicit types, instances, composition order, and imports;
- confirm that the owning layer can prove it without a dependency inversion;
  and
- keep the probe in ignored scratch storage unless it becomes a durable test.

A toy `rfl` example that avoids the difficult consumer is not a consumer probe.
A stale `.olean` is not evidence that the new boundary works.

## Create the modeling receipt

Before handing off to proof routing, record:

```text
functional contract:
formal root(s):
source authority:
representation and equality choice:
domain and interface choice:
ownership and dependency direction:
consumer probe:
modeling delta from the current tree:
discarded alternative and concrete failure:
remaining uncertainty:
```

The receipt belongs in temporary task state unless the modeling decision is
durable repository architecture, in which case distill the stable conclusion
into the repository's owning documentation. Do not publish the work log.

## Return conditions

Proceed to proof routing only when the formal root and consumer meaning are
stable enough to state exactly. Return here when Lean exposes an obligation
that is really a representation defect rather than missing mathematics.

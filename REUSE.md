# Finding and composing existing objects

Choose the mathematical objects before their implementations. For each object and probability
law in a construction, identify its declaration, owner, parameters, domain and sampling scope.
Use the live declaration to check the fit. The map below supplies starting points, not a list
of interchangeable objects.

Ideal systems are in the `Commons` namespace; typed systems and converters are in
`SystemAlgebra`. The probability operations below are in `Probability.Distribution`.

| Needed object | Declaration and module |
| --- | --- |
| Random function | `URF` in [Ideal] |
| Random permutation | `URP` in [Ideal] |
| Forward and inverse queries to one permutation | `StrongURP` in [Ideal] |
| Independent permutation per tweak | `TweakableURP`, `TweakableStrongURP` in [Ideal] |
| Fresh samples | `TypedSystem.source` in [Source]; `MemorylessSource` in [Ideal] |
| Fresh query-dependent replies | `TypedSystem.ofMemoryless` in [Memoryless] |
| Fresh reply families | `TypedSystem.parallelAll_ofMemoryless` in [FamilyMemoryless] |
| Retained key, fresh replies | `TypedSystem.keyed` in [Keyed] |
| Retained state | `TypedSystem.sample` in [Functional]; `ofAutomaton` in [Automaton] |
| Retained state with fresh transitions | `TypedSystem.ofProbAutomaton` in [ProbAutomaton] |
| Retained key as an automaton | `TypedSystem.ofProbAutomaton_eq_keyed` in [KeyedAutomaton] |
| Program with fresh inside transitions | `TypedConverter.ofProgram_smul_ofProbAutomaton` in [ProbProgramAttachment] |
| Independent joint law | `prodProbDist` in [Distribution] |
| Independent finite family of draws | `ProbDist.pi` in [Distribution] |
| Independent draws with different outcome types | `ProbDist.piDep` in [DependentProduct] |
| Transformed or dependent law | `ProbDist.map`, `ProbDist.bind`, `ProbDist.jointLaw` in [Kernel] |
| Independent initialized laws | `prodProbDist_map`, `ProbDist.map_map` in [Kernel] |
| Root blinding | `ProbDist.blindRootSolver`, `ProbDist.rootSuccessLaw` in [Group] |
| RSA unit-root blinding | `Commons.RSA.blinding_success_eq` in [RSA] |
| Nonce-unique encryption inputs | `nonceRestricted` in [Nonce] |
| Restricted interface | `TypedConverter.filter` in [Filter] |
| Relabeled interface | `TypedConverter.rename` in [Relabel] |
| One-query input and reply translation | `TypedConverter.routing` in [QueryRouting] |
| Shared access by tagged callers | `routing` in [QueryRouting], `smul_sample` in [Functional] |

[Ideal]: src/Commons/Definitions/Ideal.lean
[Source]: src/RandomSystems/Typed/Source.lean
[Keyed]: src/RandomSystems/Typed/Keyed.lean
[Memoryless]: src/RandomSystems/Typed/Memoryless.lean
[FamilyMemoryless]: src/RandomSystems/Typed/ParallelAllMemoryless.lean
[Functional]: src/RandomSystems/Typed/Functional.lean
[Automaton]: src/RandomSystems/Typed/Automaton.lean
[ProbAutomaton]: src/RandomSystems/Typed/ProbAutomaton.lean
[KeyedAutomaton]: src/RandomSystems/Typed/KeyedAutomaton.lean
[ProbProgramAttachment]: src/RandomSystems/Typed/ProbProgramAttachment.lean
[Distribution]: src/Probability/Distribution.lean
[DependentProduct]: src/Probability/DependentProduct.lean
[Kernel]: src/Probability/Kernel.lean
[Group]: src/Probability/Group.lean
[RSA]: src/Commons/Definitions/RSA.lean
[Nonce]: src/Commons/Definitions/Nonce.lean
[Filter]: src/RandomSystems/Typed/Filter.lean
[Relabel]: src/RandomSystems/Typed/Relabel.lean
[QueryRouting]: src/RandomSystems/Typed/QueryRouting.lean

Search both names and mathematical vocabulary, including the owning layer's dependencies:

```sh
rg -n 'StrongURP|URP|permutation' src/Commons src/RandomSystems src/Probability
rg -n 'jointLaw|prodProbDist|ProbDist\.(map|pi)' src/Probability src/RandomSystems
```

Read the declaration and its documentation, then use `#check` or `#print` in the assembly probe
to inspect its complete signature. An interface mismatch calls for explicit routing, renaming
or restriction, or an extension in the owning module. Keep the domain guarantee in that bridge.

## Before implementation

The client supplies the mathematical inputs to existing objects:

| Input | Existing boundary | Local obligation |
| --- | --- | --- |
| A retained draw | `TypedSystem.sample` | Which operations share it. |
| Fresh reply laws | `TypedSystem.ofMemoryless` | Interface and admitted queries. |
| Random transitions | `RandomSystem.ofProbAutomaton` | Domain, invariant or simulation. |
| Uniform functions or permutations | [Ideal] | Interface and sharing. |
| Independent families | `∥ k, R k`, `⨂ₘ k, α k` | Component contracts and call allowances. |
| Relabeling or restriction | [Relabel], [Filter] | Wiring or admission. |
| A standard scheme | e.g. `PKE.system` | Algorithms and their contracts. |
| A common context | `≫`, `•`, `∥`, `cc_normalize`, `cc_substitute` | Local equality or bound. |

Keep types and domains in shared declarations, and explain parameters beside their binders.
Use construction names for objects; real/ideal labels identify their roles in an experiment.
Choose the standard object before writing its implementation or introducing another wrapper.
The [PKE correspondence](src/Commons/Definitions/PublicKeyEncryption/Keyed.lean) exposes
`TypedSystem.keyed` under the existing CCA converter, with one pair and fresh encryption replies.

1. Map the intended objects and laws to existing declarations. For each gap, state the missing
   capability. Put this short mapping in the task update or ignored `Scratch/` working notes.
2. Write the system assembly using these declarations. Identify the owner of every retained
   draw, its callers, and the domain and budget at each interface.
3. Compare constructions under their common context. Compile the assembly with component
   contracts as hypotheses, then instantiate it with the chosen existing objects.
4. Implement the missing components and their contracts. Keep reusable laws in the model's
   owning module, available to every world and proof that uses them.

Check a changed boundary with the smallest relevant integration probe:

- A retained parameter shared by several operations, with fresh replies on each call.
- A finite parallel family and a shared component, preserving their different sampling scopes.
- A standard construction assembled from named components and supplied contracts.

Inspect the definition and elaborated goals. Routine normalization, wiring and transport should
leave the stated local mathematics. A difficult local claim can remain an explicit hypothesis
while the surrounding conditional theorem is checked; discharge it for an unconditional result.
Add another example only when it exercises a different capability.

Consumer projects must adopt this workflow in their own contributor instructions and link to
this guide at their dependency version. Importing the library does not apply its `AGENTS.md`
to that checkout.

The [compiled examples](src/Examples/Usability.lean) include a canonical permutation inside
different surrounding assemblies. The
[general comparison test](src/Tests/ProofErgonomics.lean) normalizes two different wirings and
then uses only the supplied component equation.

For a retained-state component, use `ProbDist.map init P`; name `P` when it is a nontrivial
law shared by several statements. The
[AE assembly contracts](src/Examples/AuthenticatedEncryption/Hybrid.lean) compose named sources
and programs before opening their transition rules. `inline` supplies the combined automaton;
`prodProbDist_map` and `ProbDist.map_map` normalize its initial law, preserving independent draws.

For each draw, `automatonSystem_eq_of_bisim` turns the local bisimulation into equality of
deterministic systems. `TypedSystem.ofAutomaton_map_congr` lifts this equality when both
representations use the same law `P`. Compose these component equations to obtain `hybrid_system`
or `ideal_system`, then read transcript masses.

The [PRG example](src/Examples/PRGLengthExtension.lean) defines its real world with
`MemorylessSource` and the mapped seed law. Its converter contracts use explicit equalities
`R = TypedSystem.ofMemoryless A ν`; `inline using` leaves only the reply-law calculation.

## Reuse preserves sampling scope

Three cases differ:

- **One definition, separate experiments.** Two worlds can use `α • StrongURP X` and
  `β • StrongURP X`. They reuse one definition, and each experiment samples its own permutation.
- **Independent copies in one system.** `StrongURP X ∥ StrongURP X` holds two independent
  permutations. `URP` on a two-label interface likewise samples an independent permutation at
  each label.
- **One permutation shared by several callers.** Route the callers to one component.
  `StrongURP X` samples one `π` and answers `forward` with `π` and `inverse` with `π.symm`.
  `Interface.queryBudget_domain_map` checks the callers' aggregate bound against the inside
  budget. The [shared-routing test](src/Tests/SharedRouting.lean) uses this certificate and
  distinguishes one retained permutation from independent copies by cross-caller inversion.

Similarly, define a construction's joint law once as `ProbDist Ω`. Worlds, transcript laws
and counting lemmas refer to that declaration or take it as an explicit parameter. Reuse its
normalization proof through `.2`; unfold its product or kernel only where a probability
argument needs it. A different representation gets a correspondence lemma in the owning layer.

Build normalized laws directly: `ProbDist.pi μ` samples independent coordinates with laws
`μ i`, and `ProbDist.pi (fun _ : Fin q => ν)` samples `q` independent values from `ν`.
Use `ProbDist.piDep μ` when coordinate `i` has its own outcome type. Combine these laws with
`prodProbDist`, `ProbDist.map` and `ProbDist.bind`; their normalization proofs travel with them.
`TypedSystem.source`, `TypedSystem.parallelAllPDS` and `tensorAllPDC` use these operations.
A table sampled once keeps its entries, so repeated reads agree. `TypedSystem.source` reads
each entry once, giving fresh samples; sampling inside a procedure draws anew on each call.

## Review and automation

From the repository being reviewed, run the aid against the current commit or the branch's base:

```sh
scripts/review-reuse.sh
scripts/review-reuse.sh <base-commit>
```

It reports added definition heads and common probability-construction sites in tracked changes
and untracked Lean files. It scans the current Git checkout, including Lean modules outside
`src/`. Inspect each site against the object map: reuse an existing object, extend its owner,
or explain the distinct mathematical object. The scan is lexical: it can flag
comments and proof rewrites and misses other spellings, so it neither finds every semantic
duplicate nor certifies their absence. CI does not run it.

`cc_normalize` and the [proof commands](src/ConstructiveCryptography/DSL/GRAMMAR.md#proof-commands)
assemble supplied equations and bounds. They preserve the chosen sampling scope and leave
component mathematics explicit. They do not choose the objects, their ownership or their laws.
Compile the focused probes, run the changed-file linters, then the full build and source/axiom
checks in [AGENTS.md](AGENTS.md). These checks establish the Lean claims; reuse and modeling
still require reading the definitions.

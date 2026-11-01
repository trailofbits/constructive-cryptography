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
| Retained state | `TypedSystem.sample` in [Functional]; `ofAutomaton` in [Automaton] |
| Independent joint law | `prodProbDist` in [Distribution] |
| Transformed or dependent law | `ProbDist.map`, `ProbDist.bind`, `ProbDist.jointLaw` in [Kernel] |
| Restricted interface | `TypedConverter.filter` in [Filter] |
| Relabeled interface | `TypedConverter.rename` in [Relabel] |

[Ideal]: src/Commons/Definitions/Ideal.lean
[Source]: src/RandomSystems/Typed/Source.lean
[Functional]: src/RandomSystems/Typed/Functional.lean
[Automaton]: src/RandomSystems/Typed/Automaton.lean
[Distribution]: src/Probability/Distribution.lean
[Kernel]: src/Probability/Kernel.lean
[Filter]: src/RandomSystems/Typed/Filter.lean
[Relabel]: src/RandomSystems/Typed/Relabel.lean

Search both names and mathematical vocabulary, including the owning layer's dependencies:

```sh
rg -n 'StrongURP|URP|permutation' src/Commons src/RandomSystems src/Probability
rg -n 'jointLaw|prodProbDist|ProbDist.map' src/Probability src/RandomSystems
```

Read the declaration and its documentation, then use `#check` or `#print` in the assembly probe
to inspect its complete signature. An interface mismatch calls for explicit routing, renaming
or restriction, or an extension in the owning module. Keep the domain guarantee in that bridge.

## Before implementation

In a consumer project, put these discovery and assembly requirements in that project's
contributor instructions and link to this guide at the dependency version being used. Importing
the library does not apply its `AGENTS.md` to the consumer's checkout.

1. Map the intended objects and laws to existing declarations. For each gap, state the missing
   capability. Put this short mapping in the task update or ignored `Scratch/` working notes.
2. Write the system assembly using these declarations. Identify the owner of every retained
   draw, its callers, and the domain and budget at each interface.
3. Compare constructions under their common context. Compile the assembly with component
   contracts as hypotheses, then instantiate it with the chosen existing objects.
4. Implement the missing components and their contracts. Keep reusable laws in the model's
   owning module, available to every world and proof that uses them.

The [compiled examples](src/Examples/Usability.lean) include a canonical permutation inside
different surrounding assemblies. The
[general comparison test](src/Tests/ProofErgonomics.lean) normalizes two different wirings and
then uses only the supplied component equation. The
[authenticated-encryption contracts](src/Examples/AuthenticatedEncryption/Hybrid.lean) show the
next step: named normalized laws, component equations, whole-system equations, then transcript
probabilities.

## Reuse preserves sampling scope

Three cases differ:

- **One definition, separate experiments.** Two worlds can use `α • StrongURP X` and
  `β • StrongURP X`. They reuse one definition, and each experiment samples its own permutation.
- **Independent copies in one system.** `StrongURP X ∥ StrongURP X` holds two independent
  permutations. `URP` on a two-label interface likewise samples an independent permutation at
  each label.
- **One permutation shared by several callers.** Route the callers to one component.
  `StrongURP X` samples one `π` and answers `forward` with `π` and `inverse` with `π.symm`.

Similarly, define a construction's joint law once as `ProbDist Ω`. Worlds, transcript laws
and counting lemmas refer to that declaration or take it as an explicit parameter. Reuse its
normalization proof through `.2`; unfold its product or kernel only where a probability
argument needs it. A different representation gets a correspondence lemma in the owning layer.

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

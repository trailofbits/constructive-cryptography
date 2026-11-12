# Finding and composing existing objects

Choose the mathematical objects before their implementations. For each object and probability
law in a construction, identify its declaration, owner, parameters, domain and sampling scope.
Use the live declaration to check the fit. The map below supplies starting points, not a list
of interchangeable objects.

Ideal systems, schemes and constructions are in `Commons`; typed systems, converters and games
are in `SystemAlgebra`. The probability operations below are in `Probability.Distribution`.

| Needed object | Declaration and module |
| --- | --- |
| Random function | `URF`, `URF.lazy_eq` in [Ideal] |
| Random permutation | `URP` in [Ideal]; `URP.lazy_eq` in [LazyPermutation] |
| Forward and inverse queries to one permutation | `StrongURP` in [Ideal] |
| Independent permutation per tweak | `TweakableURP`, `TweakableStrongURP` in [Ideal] |
| Unlimited fresh replies | `sourceMass` in [UnlimitedSource] |
| Bounded source adapter | `TypedSystem.source_eq_cutMass` in [SourceCuts] |
| Conditional table presentations | `presentation`, `cutSystem_realization_choiceAt` in [tables] |
| Presentation existence | `IsRandomSystem.exists_pdsSequence` in [coherent tables] |
| Independent cumulative parallel | `parallelMass`, `cutMass_parallelMass` in [parallel cuts] |
| Certified converter cuts | `IsDDCFrom.filterDom_of_insideQueriesBounded` in [converter cuts] |
| Converter horizon bounds | `InsideQueriesBounded` in [query bounds] |
| Retained mixtures of behaviors | `mixMass`, `cutMass_mixMass` in [cumulative mixtures] |
| Coherent finite presentations | `PDSSequence`, `cut_behavior` in [PDSSequence] |
| Deterministic observation cuts | `cutSystem` in [DeterministicCuts] |
| Finite observation cuts | `IsRandomSystem.cut`, `RandomSystem.limitMass` in [FiniteCuts] |
| Fresh samples | `TypedSystem.source` in [Source]; `MemorylessSource` in [Ideal] |
| Fresh query-dependent replies | `TypedSystem.ofMemoryless` in [Memoryless] |
| Ordered tuple collection | `TypedConverter.collect` in [Collector] |
| Family hybrid | `parallelAllImplication`, `distance_smul_parallelAll_le_sum` in [FamilyHybrid] |
| Fixed finite-family context | `TypedConverter.parallelAllContext` in [FamilyContext] |
| Fresh reply families | `TypedSystem.parallelAll_ofMemoryless` in [FamilyMemoryless] |
| Retained key, fresh replies | `TypedSystem.keyed` in [Keyed] |
| Signature oracle | `SignatureScheme.system.eq_keyed` in [Signature] |
| Retained state | `TypedSystem.sample` in [Functional]; `ofAutomaton` in [Automaton] |
| Hidden condition on initial draw and inputs | `TypedGame.ofAutomaton` in [AutomatonGame] |
| URF distinct-input collision game | `URF.collisionGame` in [CollisionGame] |
| Adaptive URF collision bound | `URF.collisionGame_win_le` in [CollisionBound] |
| Retained state with fresh transitions | `TypedSystem.ofProbAutomaton` in [ProbAutomaton] |
| Retained key as an automaton | `TypedSystem.ofProbAutomaton_eq_keyed` in [KeyedAutomaton] |
| Program attachment | `TypedConverter.ofProgram_smul_ofProbAutomaton` in [ProgramAttachment] |
| Sufficient inside horizon | `replies_apply_cutSystem_iff` in [inside cuts] |
| Independent joint law | `prodProbDist` in [Distribution] |
| Selected independent coordinates | `ProbDist.map_pi_comp` in [Kernel] |
| Independent finite family of draws | `ProbDist.pi` in [Distribution] |
| Independent draws with different outcome types | `ProbDist.piDep` in [DependentProduct] |
| Transformed or dependent law | `ProbDist.map`, `ProbDist.bind`, `ProbDist.jointLaw` in [Kernel] |
| Independent initialized laws | `prodProbDist_map`, `ProbDist.map_map` in [Kernel] |
| Root blinding | `ProbDist.blindRootSolver`, `ProbDist.rootSuccessLaw` in [Group] |
| RSA unit-root blinding | `Commons.RSA.blinding_success_eq` in [RSA] |
| Nonce-unique encryption inputs | `nonceRestricted` in [Nonce] |
| KEM–DEM composition | `KEMDEM.scheme` in [KEMDEM]; `KEMDEM.correct` in [KEMDEMCorrectness] |
| Encrypt-then-MAC | `encryptThenMAC.system` in [EncryptThenMAC]; [roundtrip][EtMCorrectness] |
| Hash-and-sign | `hashAndSign.system` and its correctness contract in [HashAndSign] |
| Recorded-reply rejection | `TypedConverter.recordingGuard` in [RecordingGuard] |
| Hidden-bit guessing | `TypedDistinguisher.guessingProbability` in [Guessing] |
| Nonce/AD encrypt-then-MAC | `nonceEncryptThenMAC` in [NonceEncryptThenMAC] |
| Restricted interface | `TypedConverter.filter` in [Filter] |
| Relabeled interface | `TypedConverter.rename` in [Relabel] |
| One-query input and reply translation | `TypedConverter.routing` in [QueryRouting] |
| Shared access by tagged callers | `routing` in [QueryRouting], `smul_sample` in [Functional] |

[UnlimitedSource]: src/RandomSystems/System/Source.lean
[SourceCuts]: src/RandomSystems/Typed/SourceCuts.lean
[inside cuts]: src/RandomSystems/Converter/InsideCuts.lean
[converter cuts]: src/RandomSystems/Converter/FiniteCuts.lean
[query bounds]: src/RandomSystems/Converter/QueryBound.lean
[parallel cuts]: src/RandomSystems/Cumulative/Parallel.lean
[cumulative mixtures]: src/RandomSystems/Cumulative/Mixture.lean
[coherent tables]: src/RandomSystems/Cumulative/Presentation/Sequence.lean
[tables]: src/RandomSystems/Cumulative/Presentation.lean
[PDSSequence]: src/RandomSystems/Cumulative/PDSSequence.lean
[DeterministicCuts]: src/RandomSystems/PDS/FiniteCuts.lean
[FiniteCuts]: src/RandomSystems/Cumulative/FiniteCuts.lean
[LazyPermutation]: src/Commons/Definitions/LazyPermutation.lean
[Signature]: src/Commons/Definitions/Signature/Keyed.lean
[EncryptThenMAC]: src/Commons/Constructions/EncryptThenMAC.lean
[EtMCorrectness]: src/Commons/Constructions/EncryptThenMAC/Correctness.lean
[HashAndSign]: src/Commons/Constructions/HashAndSign.lean
[RecordingGuard]: src/RandomSystems/Typed/RecordingGuard.lean
[AutomatonGame]: src/RandomSystems/Typed/AutomatonGame.lean
[CollisionGame]: src/Commons/Definitions/CollisionGame.lean
[CollisionBound]: src/Commons/Definitions/CollisionBound.lean
[Guessing]: src/RandomSystems/Typed/Guessing.lean
[KEMDEM]: src/Commons/Constructions/KEMDEM.lean
[KEMDEMCorrectness]: src/Commons/Constructions/KEMDEM/Correctness.lean
[Ideal]: src/Commons/Definitions/Ideal.lean
[Source]: src/RandomSystems/Typed/Source.lean
[Keyed]: src/RandomSystems/Typed/Keyed.lean
[Memoryless]: src/RandomSystems/Typed/Memoryless.lean
[Collector]: src/RandomSystems/Typed/FiniteFamilyCollect.lean
[FamilyHybrid]: src/ConstructiveCryptography/Substitution/FiniteFamily.lean
[FamilyContext]: src/RandomSystems/Typed/ParallelAllContext.lean
[FamilyMemoryless]: src/RandomSystems/Typed/ParallelAllMemoryless.lean
[Functional]: src/RandomSystems/Typed/Functional.lean
[Automaton]: src/RandomSystems/Typed/Automaton.lean
[ProbAutomaton]: src/RandomSystems/Typed/ProbAutomaton.lean
[KeyedAutomaton]: src/RandomSystems/Typed/KeyedAutomaton.lean
[ProgramAttachment]: src/RandomSystems/Typed/ProbProgramAttachment.lean
[Distribution]: src/Probability/Distribution.lean
[DependentProduct]: src/Probability/DependentProduct.lean
[Kernel]: src/Probability/Kernel.lean
[Group]: src/Probability/Group.lean
[RSA]: src/Commons/Definitions/RSA.lean
[Nonce]: src/Commons/Definitions/Nonce.lean
[NonceEncryptThenMAC]: src/Commons/Constructions/NonceEncryptThenMAC.lean
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

## Client workflow

1. Import the owning modules. At the CC layer, use `ConstructiveCryptography.Notation` and
   `open scoped SystemAlgebra NNReal`. Find the stock system, interface or converter and check its
   domain, query costs and sampling scope.
2. Define a short named assembly with `•`, `≫`, `∥` and `⨂ₘ`. Keep retained draws in their
   owning components and make interface rewirings explicit.
3. State the component contracts. Apply a named correctness law or normalize the common
   context, then carry the supplied local equality or bound through it.
4. Prove the remaining local claim in its owning layer. A difficult claim can stay an explicit
   hypothesis while the surrounding conditional theorem is checked.

The [three compiled clients](src/Tests/AuthoringWorkflows.lean) import these owning modules
together:

```lean
import Commons.Definitions.PublicKeyEncryption.Keyed
import Commons.Constructions.EncryptThenMAC
import RandomSystems.Typed.FiniteFamilyCollect
```

- **Retained oracle:** [retainedOracle_snoc](src/Tests/AuthoringWorkflows.lean). Use
  `PKE.system.perPort (budget := q) scheme`, where `q : PKE.Port → ℕ` bounds each port.
  Write `h` for the prior history, `m` for the next plaintext, and `c` for its candidate reply;
  `ν keys` is the supplied reply law at key pair `keys`. Publication, encryption and decryption
  share the pair; each encryption reply is fresh conditional on it. After supplying admission
  of the next query after `h`, rewriting with `PKE.system.perPort_eq_keyed` and
  `TypedSystem.keyed_snoc` leaves `scheme.enc keys.1 m = ν keys` at generated pairs.
  The extended-history mass sums `scheme.gen keys` times that pair's likelihood of `h` and
  `ν keys c`.
- **Shared value and independent sources:**
  [collectedSharedSources_eq](src/Tests/AuthoringWorkflows.lean). `retainedDrawClient` defines
  `collector • TypedSystem.sample P (fun s => ∥ k, R s k)`, with one retained `s ∼ P`;
  here `collector` abbreviates the client's `TypedConverter.collect` expression.
  Supply `R s k = TypedSystem.source (μ s k) q` for every `s` and `k`.
  `TypedConverter.smul_sample` and `collect_smul_parallelAll_source` give
  `TypedSystem.sample P (fun s => TypedSystem.source (ProbDist.piDep (μ s)) q)`.
  Replies are independent conditional on `s`; the shared draw stays outside the family.
  The collector's explicit order visits each component once, so `q` outside triggers fit
  each component's allowance of `q`.
- **Construction bound:**
  [encryptThenMAC_component_bound](src/Tests/AuthoringWorkflows.lean).
  `encryptThenMACClient` defines
  `context • encryptThenMAC.system scheme mac q`. `rw [encryptThenMACClient]` followed by
  `cc_normalize` exposes the assembly.
  `cc_nonexpand` transports a bound through the fixed MAC and both attachments, leaving exactly
  `Δ (AE.system scheme) cipher' ≤ ε`, supplied as `hlocal`. The replacement `cipher'` has
  interface `AE M C (2 * q)`, the declared inside allowance. Here `ε : ℝ≥0` bounds this
  cipher hybrid; the MAC keeps its own independent key.

Keep a difficult obligation as a named theorem parameter, such as the last client's `hlocal`,
and finish the conditional proof using it. Prove the obligation separately to apply that
theorem. [Contract checks](src/Tests/ContractApplication.lean) pin the elaborated local goals.
Key support, domain admission and supplied component contracts remain explicit premises.

Use neutral names such as `PKE.system`; real/ideal names describe roles in a comparison.
Share ambient types and instances in a short section. Explain unfamiliar symbols beside their
binders, and use named contracts instead of nested representation projections. Before implementing
an internal program, compile its intended assembly and endpoint using explicit component contracts.

For representation changes, use the existing boundary once: `TypedSystem.ofProbAutomaton_eq_keyed`
for retained-key transitions, `TypedSystem.ofProbAutomaton_eq_of_simulation` for conditional state
laws, or `TypedSystem.ofAutomaton_map_congr` for representations initialized from one draw law
`P` whose deterministic systems agree at every draw. Clients then rewrite that component equation.
Stock constructions also supply property contracts:
`encryptThenMAC.system.enc_dec_eq_of_correct` uses encryption and MAC correctness;
`hashAndSign.system.sign_verify_eq_of_correct` uses signing correctness for any hash `H : M → D`.
Their budget hypotheses admit both queries of the roundtrip.

Consumer projects adopt this workflow in their own contributor instructions and link to this
guide at their dependency version. The library's `AGENTS.md` applies to this checkout.

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

It reports added definitions and common sampling sites in tracked changes and untracked Lean
files, including modules outside `src/`. Inspect each site against the object map: reuse an
existing object, extend its owner, or explain the distinct mathematical object. This lexical
index includes comments and can miss other spellings; semantic reuse requires reading the
definitions. CI does not run it.

`cc_normalize` and the [proof commands](src/ConstructiveCryptography/DSL/GRAMMAR.md#proof-commands)
assemble supplied equations and bounds. They preserve the chosen sampling scope and leave
component mathematics explicit. They do not choose the objects, their ownership or their laws.
Compile the focused probes, run the changed-file linters, then the full build and source/axiom
checks in [AGENTS.md](AGENTS.md). These checks establish the Lean claims; reuse and modeling
still require reading the definitions.

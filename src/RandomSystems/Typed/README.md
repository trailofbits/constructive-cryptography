# Typed systems

This folder holds the random systems and converters of [RandomSystems](../README.md), typed by
interfaces [3, Definitions 3.8, 3.9, 3.17], [6, §3], [7, Definitions 2.2.1–2.2.2]: interfaces and
their budgets, typed systems and typed converters, attachment, parallel composition and renaming
with their coherence laws, the transcript pseudo-metric, filters, contexts, sources, automata, memoryless and functional
systems, typed games and the typed games presented by discrete games. Its `DSL` folder holds the
part of the DSL below the front end: the surface syntax, the laws that components sample from,
program bodies and their typed converters, and the tactics for the generated obligations
([GRAMMAR](../../ConstructiveCryptography/DSL/GRAMMAR.md)).
Every object here is a systems-level object; the instances of the classes in
[ConstructiveCryptography](../../ConstructiveCryptography/README.md) use them as their fields.
Citations refer to the numbered [references](../../../THEORY.md#references) of THEORY.md.

## Interfaces, typed systems and typed converters

An [**interface**][Interface] $`A = (I, X, Y, D)`$ has finitely many labels, finite alphabets
$`X_i, Y_i`$, and a domain $`D`$ of input histories, prefix-closed, without the empty history, of
bounded length. Two domains recur: the [**query budget**][Interface.queryBudget]
$`D = \lbrace h \ne \varepsilon \mid \lvert h \rvert \le q \rbrace`$ and the
[**per-port budget**][Interface.portBudget]
$`D = \lbrace h \ne \varepsilon \mid \forall i.\ \lvert h \restriction i \rvert \le q_i \rbrace`$,
where $`h \restriction i`$ [keeps the inputs at the label][restrict] $`i`$.

A [**typed system**][TypedSystem] on $`A`$ is a random system on
$`(\Sigma_i X_i, \Sigma_i Y_i)`$ over $`D`$,
[replying at the queried label][RandomSystem.RepliesAtQueriedInterface]. A
[**typed converter**][TypedConverter] from $`A`$ to $`B`$ is a PDC behavior from $`B`$'s domain
(inside) to $`A`$'s domain (outside), and a DDC between the two domains
[is one][TypedConverter.ofDDC]. Typed converters compose by the [serial composition][TypedConverter.comp]
of PDC behaviors, with the [identity][TypedConverter.id] PDC behavior.
[**Attachment**][TypedConverter.attach] $`\alpha R`$ is the attachment of the PDC behavior:
[the identity leaves a typed system unchanged][TypedConverter.identity_attach], and
[a serial composition attaches its inner converter first][TypedConverter.comp_smul].
A DDC equal to the trimmed serial wiring of $`\alpha`$ (outside) and $`\beta`$ (inside)
[gives their composition][TypedConverter.ofDDC_eq_comp] as typed converters, even when its own
query bound is not the product of theirs.

[**Parallel interfaces**][Interface.tensor] put the label sets side by side, and
[parallel typed systems][TypedSystem.parallel] and [parallel typed converters][TypedConverter.parallel]
are the independent parallel compositions; attachment [is local][TypedConverter.parallel_attach],
$`(\alpha \otimes \beta)(R \parallel S) = \alpha R \parallel \beta S`$.
The [finite tagged interface family][Interface.tensorAll], its
[independent system family][TypedSystem.parallelAll], and its
[independent converter family][TypedConverter.parallelAll] extend these objects to
heterogeneous component interfaces. A fixed function on the combined interface
[assembles from its component functions][TypedSystem.ofFunction_parallelAll].
Independent deterministic component presentations combine through
[parallelAllPDS][TypedSystem.parallelAllPDS], which presents the
[same typed system][TypedSystem.parallelAll_ofPDS] as the n-ary parallel behavior.
[General locality][TypedConverter.parallelAll_attach] attaches independently sampled
converters to independently sampled resources component by component:

```text
(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k)
```

The theorem applies to arbitrary stochastic components. Its
[functional corollary][TypedConverter.parallelAll_attach_ofFunction] assembles supplied
component realization equalities without revisiting their internal transcripts.
[The binary bridge][TypedSystem.parallelAll_option_mass] uses an explicit alphabet
equivalence; regrouping does not identify different interface types implicitly.
A sample shared outside the whole family remains shared, and an aggregate budget remains
an aggregate restriction rather than a separate full budget for every component.
A label-preserving
bijection of interfaces gives a [**renaming**][TypedConverter.rename], which
[relabels the transcripts][TypedConverter.rename_mass] of the typed system it is attached to;
renamings [compose][TypedConverter.rename_comp], and the renaming by the identity
[is the identity][TypedConverter.rename_refl]. Regrouping three parallel typed systems
[keeps the probabilities][TypedSystem.parallel_assoc_mass] of the regrouped transcripts, the
[dummy system][TypedSystem.dummy] on the [interface without labels][Interface.unit] beside a typed
system keeps its probabilities, on the [left][TypedSystem.parallel_unit_left_mass] and on the
[right][TypedSystem.parallel_unit_right_mass], and [exchanging the two components][TypedSystem.parallel_swap_mass]
of a parallel composition exchanges the labels of its transcripts. The regrouping renamings are
natural for typed converters: [associativity][TypedConverter.comp_associator] and the
[left][TypedConverter.comp_leftUnitor] and [right][TypedConverter.comp_rightUnitor] unit
regroupings commute with parallel typed converters, and the parallel composition of two renamings
[is the renaming of their union][TypedConverter.parallel_rename].

## Distance

The [**transcript pseudo-metric**][TypedSystem.transcriptPseudoEMetricSpace] on $`A`$ is the
[transcript distance](../Distance/README.md) of the random systems,
$`d(R, S) = \Delta(R, S)`$, with its laws from the supremum over compatible stopping distinguisher
behaviors [1, Definition 11]. Zero distance is not equality. It is an explicit structure, not a
global instance; the [CC instance](../../ConstructiveCryptography/README.md#the-instances-on-interfaces)
selects it as its metric.

## Typed distinguishers

A [**typed distinguisher**][TypedDistinguisher] on $`A`$ is the decision behavior
$`R \mapsto \Pr[d(R) = 1]`$ of a stopping distinguisher compatible with $`A`$'s domain: an
abbreviation of the existing distinguisher behaviors, with no new carrier or equivalence.
[Absorbing][TypedDistinguisher.absorb] a typed converter $`\alpha : A \to B`$ gives the
distinguisher $`d\alpha`$ on $`B`$ with
[$`(d\alpha)(R) = d(\alpha R)`$][TypedDistinguisher.probability_absorb]; absorbing the identity
[changes nothing][TypedDistinguisher.absorb_id], and absorbing a serial composition
[absorbs its converters in turn][TypedDistinguisher.absorb_comp], $`d(\alpha\beta) = (d\alpha)\beta`$.
These are laws of the action only: a selected set of typed distinguishers need not be closed
under absorption.

## Filters, contexts, sources and functional systems

The [**filter**][TypedConverter.filter] admitting $`D`$ forwards the queries of admitted histories;
it is a typed converter $`(A \restriction D) \to A`$ from the [restricted interface][Interface.restrict].
[Attached to a typed system][TypedConverter.filter_smul], it is the
[restriction][RandomSystem.restrict] of the system's random system to the restricted domain, and
[two filters in series][TypedConverter.filter_comp_filter_smul] act as the filter of both
conditions. A [**constant**][TypedConverter.constant] converter ignores its inside system and
exposes a fixed one, and the fixed [right][TypedConverter.rightContext] and
[left][TypedConverter.leftContext] **contexts** run a typed system beside:
[attaching][TypedConverter.attach_rightContext] $`\mathrm{rightContext}\ A\ S`$ to $`R`$
gives $`R \parallel S`$, and so does [attaching][TypedConverter.attach_leftContext]
$`\mathrm{leftContext}\ R\ B`$ to $`S`$.

A [**source**][TypedSystem.source] answers with fresh independent samples of a law: a
memoryless source [3, Definition 3.1] (the sources of [4, Definition 1] may have memory). An
[**automaton**][TypedSystem.ofAutomaton] is a transition function with a sampled initial state
[4, Definition 2], and [parallel automata][TypedSystem.parallel_ofAutomaton] are the automaton
running both side by side from the independent initial law `prodProbDist P Q`. If two
automata initialized from a common draw $`\omega \sim P`$ give
the same deterministic system for every $`\omega`$, then
[their sampled automata are equal typed systems][TypedSystem.ofAutomaton_map_congr] on the
interface's domain. A bisimulation for each draw thus yields an equation of typed systems, which
rewrites under attachment and parallel composition.
A [**probabilistic automaton**][TypedSystem.ofProbAutomaton] starts from a normalized law
`init` and, at each admitted `i(x)`, draws `(s', y)` from the normalized kernel `step s i x`,
retains `s'`, and returns `y` at `i`. Its state type may be infinite; each law has finite support.
The constructor uses the existing cumulative random system on the interface's domain.
[A kernel simulation][TypedSystem.ofProbAutomaton_eq_of_simulation] preserving an input-history
invariant at admitted queries gives equality of typed systems.
[Point transitions][TypedSystem.ofProbAutomaton_ofDeterministic] recover `ofAutomaton`.
A [**memoryless system**][TypedSystem.ofMemoryless] answers each admitted query `i(x)`
with a fresh draw from `ν i x`. In `TypedSystem.ofMemoryless A ν`, `A` selects the
interface and its declared domain. The [source][TypedSystem.source_eq_ofMemoryless] and
[parallel][TypedSystem.parallel_ofMemoryless] equations rewrite assemblies directly as typed
systems. A [bounded program][TypedConverter.ofProgram_smul_ofMemoryless],
[port-preserving program][TypedConverter.ofPreservingProgram_smul_ofMemoryless] or
[costed program][TypedConverter.ofCostedProgram_smul_ofMemoryless] attached to `ofMemoryless B ν`
gives `ofMemoryless A κ` when its one-invocation reply law is `κ` in every program state. Supply
inside memorylessness as an explicit typed equality. For an own source beside the inside system,
[parallel certificates][TypedSystem.parallel_eq_ofMemoryless] combine their reply laws;
[the own-source contract][TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless]
gives the cumulative form.
For [finite independent families](ParallelAllMemoryless.lean), the tagged port selects its
component's fresh reply law; the domain remains `Interface.tensorAll` of the component domains.
A [**keyed system**](Keyed.lean) retains `k ∼ P` and replies freshly from `ν k i x`.
In `TypedSystem.keyed P ν`, all ports share the retained key; reply draws are independent
conditional on it. `keyed_snoc` averages the fixed-key transcript/reply products, and
`keyed_single` gives the existing retained-function presentation.
[An automaton retaining its key](KeyedAutomaton.lean) and drawing each reply from `ν k i x`
is equal to that keyed system. [Program attachment](ProbProgramAttachment.lean) combines
a bounded program with a probabilistic automaton, retaining both states.
**Functional systems** are given by [reply functions][TypedSystem.ofFunction], by
[conditional reply laws][TypedSystem.ofConditional], or by
[sampling once][TypedSystem.sample] and keeping the sample.
The sample is drawn once and shared by all queries, never redrawn: sampling a pushforward
[samples once and keeps the image][TypedSystem.sample_fTransform],
$`\mathrm{sample}(f(P), R) = \mathrm{sample}(P, R \circ f)`$, and attachment
[commutes with the single draw][TypedConverter.smul_sample],
$`\alpha\, \mathrm{sample}(P, R) = \mathrm{sample}(P, k \mapsto \alpha R_k)`$.
Two independent initial choices can be [grouped as a product][TypedSystem.sample_prod] or
[sampled in either order][TypedSystem.sample_comm]: the second sampling law is fixed,
independently of the first value. The laws may be nonuniform and the sample types infinite;
only their supports are finite. Product regrouping follows from the product-weighted sum,
and reordering follows by swapping the product coordinates and applying `sample_fTransform`.

A fixed left system in parallel with a sampled right system
[retains the right-side choice][TypedSystem.parallel_sample_right]:

```math
R \parallel \operatorname{sample}(P,S)
= \operatorname{sample}(P, k \mapsto R \parallel S_k).
```

The draw is retained for the whole interaction and used only to select $`S_k`$. The same
left system $`R`$ is used for every $`k`$, with its own independent randomness. An environment
may still adapt queries using either component's replies.

The [finite-family collector](FiniteFamilyCollect.lean) sends one query to each tagged component
in a supplied order `Fin n ≃ K`, then returns a function of the dependent reply tuple. Its domain
condition checks each component's mapped outside history. The functional law collects the component
functions; the source law returns fresh independent tuples, also on repeated invocations and for
an empty family. The [tuple client](../../Tests/FiniteFamilyCollect.lean) exhibits these contracts.

The [component context](ParallelAllContext.lean) exposes one selected component of a tagged family:
`parallelAllContext R k • S = ∥ j, Function.update R k S j`. All fixed components retain their
independent state. An explicit renaming identifies the single active interface with the family
whose other members are empty units, preserving the component domains. This equation transports
local replacements through a finite assembly; a selected observer class supplies its own closure
under the context.

For a certified [direct call rule][callRule], query and return equations against a fixed inside
function $`f`$ yield the
[outside functional system][TypedConverter.ofDDC_callConverter_smul_ofFunction]; later inside
queries of an invocation may depend on its earlier replies.
An [input-dependent router][routingConverter] can move a payload field into the inside port label;
its [typed attachment][TypedConverter.ofDDC_routingConverter_smul_ofFunction] returns the explicitly
translated inside answer at the original outside port.
Writing $`\operatorname{request}(u) = (j,x)`$, the outside function is

```math
g(u) = \operatorname{answer}\bigl(u,(j,f_j(x))\bigr).
```

The input $`u`$ is retained until the inside reply arrives. For outside domain $`F`$ and
inside domain $`E`$, the domain guarantee follows from
$`F(us) \Rightarrow E(\operatorname{map}(\operatorname{request},us))`$.
The typed constructor [**`routing`**][TypedConverter.routing] takes precisely this certificate.
It spends one inside query per outside input, including a pending invocation. For fresh replies
with law $`\nu_j(x)`$, its [memoryless attachment law][TypedConverter.routing_smul_ofMemoryless]
pushes that law forward through $`y \mapsto \operatorname{answer}(u,(j,y))`$.
The [input-encoding and output-projection clients](../../Tests/QueryRouting.lean) use this law
on a restricted inside domain.

To share one component among tagged callers, erase the caller tag in `request` and attach the
router to that single system. `smul_sample` preserves its retained draw. The domain certificate
checks all callers together: `Interface.queryBudget_domain_map` admits the mapped history when
the outside interface's aggregate bound fits the inside query budget. The
[two-caller permutation test](../../Tests/SharedRouting.lean) checks the sum of caller bounds and
cross-caller inverse consistency, and distinguishes independent parallel copies.

## Typed games

A [**typed game**][TypedGame] on $`A`$ is a typed system on the [interface][Interface.withMBO] of
$`A`$ with the MBO whose MBO, once set, stays set: a game in the sense of
[Game](../Game/README.md). A typed converter [attaches][TypedConverter.attachGame] to it through its
[MBO-forwarding lift][PDCBehavior.liftMBO], and its [visible typed system][TypedGame.visible] is its
visible system. A discrete game whose visible systems present a typed system $`R`$
[presents a typed game][TypedGame.ofPDG] on the interface of $`R`$, with
[visible typed system][TypedGame.visible_ofPDG] $`R`$. A single-label sampled function with a
hidden condition [presents a typed game][TypedGame.ofSingleFunction] whose random system is
[conditionally equivalent][TypedGame.ofSingleFunction_conditionallyEquivalent] to that of the
typed system sampling the ideal function, under the fixed-query factorization.

<!-- Declarations -->

[Interface]: Interface.lean#L47
[Interface.queryBudget]: Interface.lean#L70
[Interface.portBudget]: Interface.lean#L97
[restrict]: ../System/Basic.lean#L798
[TypedSystem]: Interface.lean#L115
[RandomSystem.RepliesAtQueriedInterface]: ../Cumulative/Cumulative.lean#L74
[TypedConverter]: Interface.lean#L150
[TypedConverter.ofDDC]: Interface.lean#L166
[TypedConverter.comp]: Interface.lean#L157
[TypedConverter.id]: Interface.lean#L162
[TypedConverter.attach]: Interface.lean#L213
[TypedConverter.identity_attach]: Interface.lean#L227
[TypedConverter.comp_smul]: Interface.lean#L233
[TypedConverter.ofDDC_eq_comp]: Interface.lean#L195
[Interface.tensor]: Parallel.lean#L89
[TypedSystem.parallel]: Parallel.lean#L157
[TypedConverter.parallel]: Parallel.lean#L214
[TypedConverter.parallel_attach]: ParallelAttachment.lean#L27
[Interface.tensorAll]: ParallelAll.lean#L63
[TypedSystem.parallelAll]: ParallelAll.lean#L160
[TypedConverter.parallelAll]: ParallelAll.lean#L244
[TypedSystem.ofFunction_parallelAll]: ParallelAll.lean#L272
[TypedSystem.parallelAllPDS]: ParallelAllPresentation.lean
[TypedSystem.parallelAll_ofPDS]: ParallelAllPresentation.lean
[TypedConverter.rename]: Relabel.lean#L52
[TypedConverter.rename_comp]: Relabel.lean#L84
[TypedConverter.rename_refl]: Relabel.lean#L71
[TypedConverter.rename_mass]: SystemParallel.lean#L59
[TypedSystem.parallel_assoc_mass]: SystemCoherence.lean#L89
[TypedSystem.dummy]: SystemCoherence.lean#L101
[Interface.unit]: InterfaceCoherence.lean#L94
[TypedSystem.parallel_unit_left_mass]: SystemCoherence.lean#L107
[TypedSystem.parallel_unit_right_mass]: SystemCoherence.lean#L132
[TypedSystem.parallel_swap_mass]: SystemCoherence.lean#L157
[TypedConverter.comp_associator]: ConverterCoherence.lean#L162
[TypedConverter.comp_leftUnitor]: ConverterCoherence.lean#L199
[TypedConverter.comp_rightUnitor]: ConverterCoherence.lean#L228
[TypedConverter.parallel_rename]: TensorRename.lean#L132
[TypedSystem.transcriptPseudoEMetricSpace]: Distance.lean#L26
[TypedDistinguisher]: Distinguisher.lean#L41
[TypedDistinguisher.absorb]: Distinguisher.lean#L47
[TypedDistinguisher.probability_absorb]: Distinguisher.lean#L53
[TypedDistinguisher.absorb_id]: Distinguisher.lean#L58
[TypedDistinguisher.absorb_comp]: Distinguisher.lean#L66
[Interface.restrict]: Filter.lean#L38
[TypedConverter.filter]: Filter.lean#L64
[TypedConverter.filter_smul]: Filter.lean#L74
[TypedConverter.filter_comp_filter_smul]: Filter.lean#L128
[RandomSystem.restrict]: ../Distance/Restriction.lean#L64
[TypedConverter.constant]: Context.lean#L82
[TypedConverter.rightContext]: Context.lean#L113
[TypedConverter.leftContext]: Context.lean#L120
[TypedConverter.attach_rightContext]: Context.lean#L126
[TypedConverter.attach_leftContext]: Context.lean#L131
[TypedSystem.source]: Source.lean#L55
[TypedSystem.ofAutomaton]: Automaton.lean#L55
[TypedSystem.ofAutomaton_map_congr]: Automaton.lean#L76
[TypedSystem.parallel_ofAutomaton]: Automaton.lean#L100
[TypedSystem.ofProbAutomaton]: ProbAutomaton.lean
[TypedSystem.ofProbAutomaton_eq_of_simulation]: ProbAutomaton.lean
[TypedSystem.ofProbAutomaton_ofDeterministic]: ProbAutomaton.lean
[TypedSystem.ofMemoryless]: Memoryless.lean#L57
[TypedSystem.source_eq_ofMemoryless]: Memoryless.lean#L151
[TypedSystem.parallel_ofMemoryless]: Memoryless.lean#L231
[TypedSystem.parallel_eq_ofMemoryless]: Memoryless.lean#L241
[TypedConverter.ofProgram_smul_ofMemoryless]: Memoryless.lean#L350
[TypedConverter.ofPreservingProgram_smul_ofMemoryless]: Memoryless.lean#L368
[TypedConverter.ofCostedProgram_smul_ofMemoryless]: Memoryless.lean#L389
[TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless]: Memoryless.lean#L321
[TypedSystem.ofFunction]: Functional.lean#L62
[TypedSystem.ofConditional]: Functional.lean#L44
[TypedSystem.sample]: Functional.lean#L183
[TypedSystem.sample_fTransform]: Functional.lean#L197
[TypedConverter.smul_sample]: Functional.lean#L242
[TypedSystem.sample_prod]: SamplingAlgebra.lean#L41
[TypedSystem.sample_comm]: SamplingAlgebra.lean#L57
[TypedSystem.parallel_sample_right]: SamplingAlgebra.lean#L87
[callRule]: ../Converter/Calls.lean#L395
[TypedConverter.ofDDC_callConverter_smul_ofFunction]: CallRuleFunctional.lean#L35
[routingConverter]: ../Converter/QueryRouting.lean#L73
[TypedConverter.ofDDC_routingConverter_smul_ofFunction]: QueryRouting.lean#L62
[TypedConverter.routing]: QueryRouting.lean
[TypedConverter.routing_smul_ofMemoryless]: QueryRouting.lean
[Interface.withMBO]: Game.lean#L35
[TypedGame]: Game.lean#L46
[TypedConverter.attachGame]: Game.lean#L49
[PDCBehavior.liftMBO]: ../Game/MBOAttachment.lean#L464
[TypedGame.visible]: Game.lean#L90
[TypedGame.ofPDG]: PresentedGame.lean#L45
[TypedGame.visible_ofPDG]: PresentedGame.lean#L55
[TypedGame.ofSingleFunction]: PresentedGame.lean#L92
[TypedGame.ofSingleFunction_conditionallyEquivalent]: PresentedGame.lean#L105

[TypedConverter.parallelAll_attach]: ParallelAllAttachment.lean
[TypedConverter.parallelAll_attach_ofFunction]: ParallelAllAttachment.lean
[TypedSystem.parallelAll_option_mass]: ParallelAllRegroup.lean#L53

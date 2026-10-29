# Typed systems

This folder holds the random systems and converters of [RandomSystems](../README.md), typed by
interfaces [3, Definitions 3.8, 3.9, 3.17], [6, §3], [7, Definitions 2.2.1–2.2.2]: interfaces and
their budgets, typed systems and typed converters, attachment, parallel composition and renaming
with their coherence laws, filters, contexts, sources, automata, memoryless and functional
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
$`(\alpha \otimes \beta)(R \parallel S) = \alpha R \parallel \beta S`$. A label-preserving
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
running both side by side. A source [is memoryless][TypedSystem.source_eq_memoryless],
memoryless systems [side by side are memoryless][TypedSystem.parallel_eq_memoryless], and the
converter of a program [maps a memoryless system to the memoryless system of its reply
law][TypedConverter.ofProgram_smul_memoryless], also
[for port-preserving programs][TypedConverter.ofPreservingProgram_smul_memoryless] and
[with its own sources beside its inside interface][TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless]:
the composition law of [converters](../README.md#converters) on their random systems.
**Functional systems** are given by [reply functions][TypedSystem.ofFunction], by
[conditional reply laws][TypedSystem.ofConditional], or by
[sampling once][TypedSystem.sample] and keeping the sample.
The sample is drawn once and shared by all queries, never redrawn: sampling a pushforward
[samples once and keeps the image][TypedSystem.sample_fTransform],
$`\mathrm{sample}(f(P), R) = \mathrm{sample}(P, R \circ f)`$, and attachment
[commutes with the single draw][TypedConverter.smul_sample],
$`\alpha\, \mathrm{sample}(P, R) = \mathrm{sample}(P, k \mapsto \alpha R_k)`$.

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

[Interface]: Interface.lean#L42
[Interface.queryBudget]: Interface.lean#L65
[Interface.portBudget]: Interface.lean#L76
[restrict]: ../System/Basic.lean#L794
[TypedSystem]: Interface.lean#L94
[RandomSystem.RepliesAtQueriedInterface]: ../Cumulative/Cumulative.lean#L70
[TypedConverter]: Interface.lean#L129
[TypedConverter.ofDDC]: Interface.lean#L145
[TypedConverter.comp]: Interface.lean#L136
[TypedConverter.id]: Interface.lean#L141
[TypedConverter.attach]: Interface.lean#L192
[TypedConverter.identity_attach]: Interface.lean#L206
[TypedConverter.comp_smul]: Interface.lean#L212
[TypedConverter.ofDDC_eq_comp]: Interface.lean#L174
[Interface.tensor]: Parallel.lean#L85
[TypedSystem.parallel]: Parallel.lean#L153
[TypedConverter.parallel]: Parallel.lean#L210
[TypedConverter.parallel_attach]: ParallelAttachment.lean#L23
[TypedConverter.rename]: Relabel.lean#L48
[TypedConverter.rename_comp]: Relabel.lean#L80
[TypedConverter.rename_refl]: Relabel.lean#L67
[TypedConverter.rename_mass]: SystemParallel.lean#L55
[TypedSystem.parallel_assoc_mass]: SystemCoherence.lean#L85
[TypedSystem.dummy]: SystemCoherence.lean#L97
[Interface.unit]: InterfaceCoherence.lean#L90
[TypedSystem.parallel_unit_left_mass]: SystemCoherence.lean#L103
[TypedSystem.parallel_unit_right_mass]: SystemCoherence.lean#L128
[TypedSystem.parallel_swap_mass]: SystemCoherence.lean#L153
[TypedConverter.comp_associator]: ConverterCoherence.lean#L158
[TypedConverter.comp_leftUnitor]: ConverterCoherence.lean#L195
[TypedConverter.comp_rightUnitor]: ConverterCoherence.lean#L224
[TypedConverter.parallel_rename]: TensorRename.lean#L128
[Interface.restrict]: Filter.lean#L32
[TypedConverter.filter]: Filter.lean#L49
[TypedConverter.filter_smul]: Filter.lean#L60
[TypedConverter.filter_comp_filter_smul]: Filter.lean#L94
[RandomSystem.restrict]: ../Distance/Restriction.lean#L59
[TypedConverter.constant]: Context.lean#L78
[TypedConverter.rightContext]: Context.lean#L109
[TypedConverter.leftContext]: Context.lean#L116
[TypedConverter.attach_rightContext]: Context.lean#L122
[TypedConverter.attach_leftContext]: Context.lean#L127
[TypedSystem.source]: Source.lean#L51
[TypedSystem.ofAutomaton]: Automaton.lean#L42
[TypedSystem.parallel_ofAutomaton]: Automaton.lean#L57
[TypedSystem.source_eq_memoryless]: Memoryless.lean#L47
[TypedSystem.parallel_eq_memoryless]: Memoryless.lean#L146
[TypedConverter.ofProgram_smul_memoryless]: Memoryless.lean#L241
[TypedConverter.ofPreservingProgram_smul_memoryless]: Memoryless.lean#L262
[TypedConverter.ofPreservingProgram_comp_rightContext_smul_memoryless]: Memoryless.lean#L279
[TypedSystem.ofFunction]: Functional.lean#L58
[TypedSystem.ofConditional]: Functional.lean#L40
[TypedSystem.sample]: Functional.lean#L178
[TypedSystem.sample_fTransform]: Functional.lean#L192
[TypedConverter.smul_sample]: Functional.lean#L237
[Interface.withMBO]: Game.lean#L24
[TypedGame]: Game.lean#L35
[TypedConverter.attachGame]: Game.lean#L38
[PDCBehavior.liftMBO]: ../Game/MBOAttachment.lean#L455
[TypedGame.visible]: Game.lean#L53
[TypedGame.ofPDG]: PresentedGame.lean#L41
[TypedGame.visible_ofPDG]: PresentedGame.lean#L51
[TypedGame.ofSingleFunction]: PresentedGame.lean#L88
[TypedGame.ofSingleFunction_conditionallyEquivalent]: PresentedGame.lean#L101

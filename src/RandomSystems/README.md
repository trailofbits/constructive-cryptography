# Random systems

This library holds the concrete objects and their laws: deterministic systems, automata and
environments (`System`), distributions over deterministic systems (`PDS`), random systems given by
their cumulative probabilities, with their presentations (`Cumulative`), deterministic converters
and their compositions (`DDC`), probabilistic converters, programs, attachment and parallel
composition (`Converter`), the transcript distance and distinguishers
([`Distance`](Distance/README.md)), games ([`Game`](Game/README.md)), and typed systems on
interfaces ([`Typed`](Typed/README.md)). It knows nothing of the classes of
[ConstructiveCryptography](../ConstructiveCryptography/README.md), whose instances on interfaces
take their fields from here. Citations refer to the numbered
[references](../../THEORY.md#references) of THEORY.md.

*Systems over finite alphabets, answering exactly on a bounded domain [1], [2, Chapter 2],
[3, Chapter 3]. Laws are finitely supported distributions and $`\delta`$ is the statistical
distance ([Probability](../Probability/README.md)).*

## Deterministic systems

A [**deterministic system**][IsDDS] (DDS) is a [partial function][System] from input histories to
the next output, $`s : \mathcal X^{*} \rightharpoonup \mathcal Y`$, [silent at the empty
history][SilentAtEmpty], whose domain is [closed under nonempty prefixes][PrefixClosed]. Systems
are [wired together][interconnect], each output leaving the wiring or returning as an input. A
system [replies][Replies] $`y_1 \dots y_n`$ to $`x_1 \dots x_n`$ when it answers each prefix with the
next output, and a DDS [is determined by its completed replies][IsDDS.eq_of_replies_iff]. An
[automaton][automatonSystem] is a transition function started in a state, and
[bisimilar][IsBisim] automata [have the same system][automatonSystem_eq_of_bisim]. An
[environment][DDE] (DDE) chooses the next query from the replies so far.

## Probabilistic systems

A [**domain**][Domain] $`\mathcal D`$ admits next queries after each transcript, with a bound on the
length. A [**PDS**][PDS] is a finite distribution over DDSs [with domain][HasDomain]
$`\mathcal D`$ [1, Definition 8]. A [**random system**][RandomSystem] is given by its cumulative
probabilities $`p`$ on transcripts [1, after Lemma 5], [normalized][IsRandomSystem] on the domain:

```math
p(\varepsilon) = 1, \qquad p \ge 0, \qquad
\sum_{y} p\big(h \cdot (x, y)\big) =
\begin{cases} p(h) & \text{if } x \text{ is admitted after } h, \\ 0 & \text{otherwise.} \end{cases}
```

A PDS [has a random system][PDS.behavior], and [equivalent][Equivalent] PDSs
[have the same one][PDS.behavior_eq_iff]. Every random system
[has a finite presentation][RandomSystem.exists_presentation], so random systems
[are exactly the classes of equivalent PDSs][RandomSystem.ofPDSClass_bijective]. Two random
systems [are equal exactly when][RandomSystem.eq_iff_sLaw] their
[transcript laws][RandomSystem.sLaw] agree in every [compatible][RandomSystem.Compatible]
environment, and on a domain of input histories
[fixed query sequences suffice][RandomSystem.eq_iff_sLaw_fixedQueries] [1, Lemma 5]. Random
systems on one domain form [mixtures][RandomSystem.mix], and two random systems run
[independently in parallel][RandomSystem.parallel] form one on the combined alphabets.
For a finite tagged family, [the n-ary product][RandomSystem.parallelAll] multiplies component
transcript masses on consistent interleavings and keeps each component's input domain.
Independent deterministic component presentations
[present the same joint cumulative law][RandomSystem.parallelAll_mass_of_presentations].
The [n-ary converter][tensorAllL] canonicalizes its complete-history rule and combines
component domain certificates; [stochastic converter families][PDCBehavior.tensorAll]
sample their components independently.

[Aggregate serial accounting][IsDDCFrom.comp_query_charge_le] uses costs of actual
intermediate query values. The inner component's partial-transcript bound includes pending
calls. An input-only composite budget additionally requires the outer weighted sum to be
bounded on every reply trace; consecutive-query bounds alone do not provide this result.
[Direct call rules][callConverter_query_count] supply their aggregate bound from the
arbitrary-reply phase contract.

A [**probabilistic automaton**][RandomSystem.ofProbAutomaton] answers a query from its state with a
law on the next state and the reply, a [probabilistic step][ProbStep]; its random system follows
the [sub-law of the states][ProbStep.belief] reached with the replies of a transcript, whose weight
is the probability of the transcript. On an input domain, two probabilistic automata
[have the same random system][RandomSystem.ofProbAutomaton_eq_of_simulation] along a
[simulation][ProbStep.SimulatesAt], a kernel between their states through which their steps
commute. A deterministic automaton with a random initial state
[is the probabilistic automaton of its point steps][RandomSystem.ofProbAutomaton_ofDeterministic_apply],
and a probabilistic automaton
[is a deterministic automaton reading pre-sampled draws][RandomSystem.ofProbAutomaton_eq_drawStep],
sampled once with the initial state: a random automaton [4, Definition 2].

A random system is [**memoryless**][RandomSystem.memoryless] when the law of its reply depends only
on the current query, never on the history: a source "can be memoryless or have memory"
[3, Definition 3.1], and a single-input system given by a conditional distribution is a "discrete
memoryless channel" [3, §3.6.1]. With the reply law $`\nu`$, its probabilities obey the chain rule

```math
p\big(h \cdot (x, y)\big) = p(h)\, \nu_x(y) \qquad \text{for every query } x \text{ admitted after } h,
```

and [a random system obeying it is the memoryless system][RandomSystem.eq_memoryless_of_snoc].
A probabilistic automaton whose step [replies from every state with the same
law][ProbStep.Memoryless] $`\nu`$ [is the memoryless system of this law][RandomSystem.ofProbAutomaton_eq_memoryless].
Two memoryless systems [side by side are memoryless][RandomSystem.parallel_memoryless]: a query
to either system is answered with the reply law of that system.

## Converters

A [**DDC**][IsDDC] is a system on the converter alphabets (outside queries and inside replies in;
inside queries and outside replies out) with at most $`b`$ consecutive inside queries
[3, Definition 3.8]. A **DDC from $`E`$ to $`F`$** ([`IsDDCFrom`][IsDDCFrom]) answers exactly the
[converter domain][converterDomain] and queries only in $`E`$; attached to a system with domain $`E`$
it [gives one with domain][IsDDCFrom.mapsDomain] $`F`$. A [**PDC**][PDCBehavior.ofPDC] is a distribution over DDCs, and
its [**behavior**][PDCBehavior] is a random system over the converter domain
[3, Definitions 3.17–3.18].
A DDC from $`E`$ to $`F`$ whose transcripts are transcripts of a DDC $`r`$, not necessarily
responsive, [is a filter][IsDDCFrom.eq_filterDom_of_replies_le] of $`r`$ [3, §3.4.3]: the
restriction of $`r`$ to the input histories whose outside queries lie in $`F`$.

[Serial composition][serialM] $`\beta \odot \alpha`$ connects the inside of $`\beta`$ to the outside
of $`\alpha`$, and [DDCs compose][IsDDC.comp] with the product of their bounds. When the run of
$`\alpha`$ in an invocation at the intermediate port $`m`$ is at most $`\mathrm{cost}(m)`$, and
the outer converter carries a charge, raised by $`\mathrm{cost}(m)`$ with each query at $`m`$ and
at most $`B`$, the composite [is bounded by the charge][IsDDC.comp_of_query_cost]: at most
$`B`$ consecutive inside queries. This bounds one run, not the total over invocations.

PDC behaviors have a [composition][PDCBehavior.comp] and an [identity][PDCBehavior.id], with
[associativity][PDCBehavior.comp_assoc] and the [left][PDCBehavior.id_comp] and
[right][PDCBehavior.comp_id] identity laws. [Attachment][PDCBehavior.attach] samples the PDC, then
attaches the sample deterministically: [presentations attach to
presentations][PDCBehavior.attach_presents], [the identity leaves a system
unchanged][PDCBehavior.attach_id], and [a composition attaches its inner converter
first][PDCBehavior.attach_comp]. [Parallel composition][PDCBehavior.tensor] samples two PDCs
independently and runs them side by side, with [interchange][PDCBehavior.comp_tensor] against
serial composition.

A [**direct call rule**][callRule] reads from the complete history the current invocation, the
latest outside query $`u`$ with the inside replies $`r_1 \dots r_k`$ received since, and either
returns at the label of $`u`$ or issues the next inside query [7, Definition 2.2.2]. It depends
on $`u`$ and $`r_1 \dots r_k`$ only. The one-way phase condition, an inside query only when
$`k < \mathrm{cost}(u)`$, gives [responsiveness][callRule_isResponsiveDDC] and the
[query count][callRule_query_count] $`\#\text{inside queries} \le \sum_u \mathrm{cost}(u)`$,
including pending and interrupted invocations; the biconditional gives the
[exact length][callRule_completed_exact_length] of a completed call. Canonicalization followed by
[outside-domain restriction][callConverter] yields a certified
[DDC from an inside domain][callConverter_isDDCFrom]; any further inside-domain predicate is
proved on the actual transcripts. A rule following a
[schedule against a fixed function][replies_callConverter_of_schedule] has the completed
transcripts, and [attached to that function][ofDDC_callConverter_smul_ofFunction] it computes
the indicated outside function through the existing deterministic attachment.
A [query router][routingConverter] specializes this call to one input-dependent inside request.
Its [query history][routingCall_queries] is the exact request-map image of the outside history,
including a pending call; an explicit answer map translates the inside reply.

A [**program**][Program] is a deterministic oracle body: from its state, the outside query and the
inside exchanges of the current invocation, it computes the reply or the next inside query. A
program can be [bounded][Program.Bounded] (at most $`b`$ inside queries per invocation), have
[exact costs][Program.Costs], or [preserve a partial port map][Program.PortPreserving]
$`\iota : O \to \mathrm{Option}\ J`$: an invocation at $`o`$ queries the labels in the image of
$`\iota`$ only at $`\iota(o)`$, at most once, and none of them when $`\iota(o)`$ is none, so it
queries $`\iota(o)`$ [at most as often as it is queried at][DDC.insideQueries_restrict_length_le]
$`o`$. On an outside domain, a bounded program
[is a DDC from every inside domain containing its inside queries][DDC.ofProgramOn_isDDCFrom].
Attached to an automaton, a program is [inlined][Program.inline] [4, §3.3]: the result is the
[combined automaton][Program.combine] on pairs of states, also
[on domains][Program.trim_apply_ofProgramOn_automaton].

Run against a probabilistic automaton, a program is the probabilistic automaton
[on pairs of states][Program.probCombine] whose step runs one invocation, the automaton answering
the inside queries with fresh steps; it [respects simulations][RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation].
[**Attaching the program's converter to a probabilistic automaton is the program run against
it**][PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton], the combined system $`C(F)`$ of a
system $`C(\cdot)`$ invoking $`F`$ [4, §3.3]; for point steps it is the
[combined automaton][PDCBehavior.attach_ofDDC_ofProgramOn_ofDeterministic]. Against memoryless
replies of the laws $`\nu`$, a program [replies memorylessly][Program.memoryless_probCombine] when
its [reply law][Program.memorylessReplyLaw] $`\kappa`$, the law of one invocation whose inside
queries are answered by fresh samples of $`\nu`$, is the same from every program state. So
[the composition law][PDCBehavior.attach_ofDDC_ofProgramOn_memoryless] holds, whatever the number
of the program's inside queries:

```math
\alpha_P\, \mathrm{mem}(\nu) = \mathrm{mem}(\kappa).
```

<!-- Declarations -->

[System]: System/Basic.lean#L40
[SilentAtEmpty]: System/Basic.lean#L69
[PrefixClosed]: System/Basic.lean#L72
[IsDDS]: System/Basic.lean#L77
[interconnect]: System/Basic.lean#L225
[Replies]: System/Replies.lean#L33
[IsDDS.eq_of_replies_iff]: System/Replies.lean#L151
[automatonSystem]: System/Automaton.lean#L43
[IsBisim]: System/Automaton.lean#L70
[automatonSystem_eq_of_bisim]: System/Automaton.lean#L89
[DDE]: System/DDE.lean#L20
[Domain]: PDS/PDS.lean#L65
[Equivalent]: PDS/PDS.lean#L50
[HasDomain]: PDS/PDS.lean#L91
[PDS]: PDS/PDS.lean#L133
[IsRandomSystem]: Cumulative/Cumulative.lean#L39
[RandomSystem]: Cumulative/Cumulative.lean#L53
[PDS.behavior]: Cumulative/Cumulative.lean#L216
[PDS.behavior_eq_iff]: Cumulative/Cumulative.lean#L225
[RandomSystem.exists_presentation]: Cumulative/Presentation.lean#L302
[RandomSystem.ofPDSClass_bijective]: Cumulative/Presentation.lean#L312
[RandomSystem.sLaw]: Cumulative/CumulativeObservation.lean#L179
[RandomSystem.Compatible]: Cumulative/CumulativeObservation.lean#L197
[RandomSystem.eq_iff_sLaw]: Cumulative/CumulativeObservation.lean#L534
[RandomSystem.eq_iff_sLaw_fixedQueries]: Cumulative/CumulativeObservation.lean#L548
[RandomSystem.mix]: Cumulative/CumulativeOperations.lean#L45
[RandomSystem.parallel]: Cumulative/CumulativeOperations.lean#L130
[RandomSystem.parallelAll]: Cumulative/ParallelAll.lean#L193
[RandomSystem.parallelAll_mass_of_presentations]: Cumulative/ParallelAllPresentation.lean#L60
[tensorAllL]: Converter/ParallelAll.lean#L104
[PDCBehavior.tensorAll]: Converter/ParallelAll.lean#L699
[RandomSystem.ofProbAutomaton]: System/ProbAutomaton.lean#L197
[ProbStep]: System/ProbAutomaton.lean#L58
[ProbStep.belief]: System/ProbAutomaton.lean#L160
[ProbStep.SimulatesAt]: System/ProbAutomaton.lean#L260
[RandomSystem.ofProbAutomaton_eq_of_simulation]: System/ProbAutomaton.lean#L400
[RandomSystem.ofProbAutomaton_ofDeterministic_apply]: System/ProbAutomaton.lean#L535
[RandomSystem.ofProbAutomaton_eq_drawStep]: Converter/ProbProgramAttachment.lean#L943
[RandomSystem.memoryless]: System/Memoryless.lean#L65
[RandomSystem.eq_memoryless_of_snoc]: System/Memoryless.lean#L84
[RandomSystem.parallel_memoryless]: System/Memoryless.lean#L146
[ProbStep.Memoryless]: System/Memoryless.lean#L237
[RandomSystem.ofProbAutomaton_eq_memoryless]: System/Memoryless.lean#L273
[IsDDC]: DDC/DDC.lean#L127
[serialM]: DDC/Serial.lean#L55
[IsDDC.comp]: DDC/Serial.lean#L514
[converterDomain]: Converter/ConverterDomain.lean#L236
[IsDDCFrom]: Converter/ConverterDomain.lean#L303
[IsDDCFrom.mapsDomain]: Converter/ConverterDomain.lean#L678
[IsDDCFrom.eq_filterDom_of_replies_le]: Converter/ConverterDomain.lean#L465
[IsDDC.comp_of_query_cost]: DDC/SerialCost.lean#L209
[callRule]: Converter/Calls.lean#L391
[callRule_completed_exact_length]: Converter/CallRuleTranscript.lean#L92
[callRule_isResponsiveDDC]: Converter/Calls.lean#L433
[callRule_query_count]: Converter/Calls.lean#L481
[callConverter]: Converter/Calls.lean#L499
[callConverter_isDDCFrom]: Converter/Calls.lean#L514
[replies_callConverter_of_schedule]: Converter/CallRuleTranscript.lean#L168
[ofDDC_callConverter_smul_ofFunction]: Typed/CallRuleFunctional.lean#L31
[routingConverter]: Converter/QueryRouting.lean#L69
[routingCall_queries]: Converter/QueryRouting.lean#L108
[PDCBehavior]: Converter/PDCBehavior.lean#L67
[PDCBehavior.ofPDC]: Converter/PDCBehavior.lean#L169
[PDCBehavior.comp]: Converter/PDCBehavior.lean#L273
[PDCBehavior.id]: Converter/PDCBehavior.lean#L369
[PDCBehavior.comp_assoc]: Converter/PDCBehavior.lean#L338
[PDCBehavior.id_comp]: Converter/PDCBehavior.lean#L385
[PDCBehavior.comp_id]: Converter/PDCBehavior.lean#L375
[PDCBehavior.attach]: Converter/ConverterAttachment.lean#L156
[PDCBehavior.attach_presents]: Converter/ConverterAttachment.lean#L207
[PDCBehavior.attach_id]: Converter/ConverterAttachment.lean#L262
[PDCBehavior.attach_comp]: Converter/ConverterAttachment.lean#L275
[PDCBehavior.tensor]: Converter/ConverterTensor.lean#L649
[PDCBehavior.comp_tensor]: Converter/ConverterTensor.lean#L745
[Program]: Converter/Program.lean#L45
[Program.Bounded]: Converter/Program.lean#L70
[Program.Costs]: Converter/Program.lean#L112
[Program.PortPreserving]: Converter/Program.lean#L123
[DDC.insideQueries_restrict_length_le]: Converter/Program.lean#L537
[DDC.ofProgramOn_isDDCFrom]: Converter/Program.lean#L634
[Program.inline]: Converter/ProgramAttachment.lean#L258
[Program.combine]: Converter/ProgramAttachment.lean#L429
[Program.trim_apply_ofProgramOn_automaton]: Converter/ProgramAttachment.lean#L609
[Program.probCombine]: Converter/ProbProgramAttachment.lean#L187
[RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation]: Converter/ProbProgramAttachment.lean#L507
[PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton]: Converter/ProbProgramAttachment.lean#L1102
[PDCBehavior.attach_ofDDC_ofProgramOn_ofDeterministic]: Converter/ProbProgramAttachment.lean#L1016
[Program.memorylessReplyLaw]: System/Memoryless.lean#L313
[Program.memoryless_probCombine]: System/Memoryless.lean#L400
[PDCBehavior.attach_ofDDC_ofProgramOn_memoryless]: System/Memoryless.lean#L431

[IsDDCFrom.comp_query_charge_le]: Converter/SerialAccounting.lean
[callConverter_query_count]: Converter/Calls.lean

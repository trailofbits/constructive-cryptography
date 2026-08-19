# The theory, as implemented

This document states the theory the library formalizes. It is
implementation-independent in style, but every notion below corresponds to a
declaration in the tree, named in `code font`, and every deviation from a source
is stated. Sources follow the hierarchy MauRen16 > Jost > LiuMau20 >
Lanzenberger's thesis; CR18 is a fallback, marked where it is the cited source.

---

## 1. Probability

The carrier is the **signed, finitely supported** law

    Distribution A := A →₀ ℝ,        |X| := ∑ₐ X(a)          `Probability.Distribution`, `weight`

Non-negativity and normalization are *predicates*, not structure
(`Distribution.NonNeg`, `Distribution.isProbDist`), and each statement carries
the weakest of the three layers at which it is true. This follows
Lanzenberger's own preamble — "even though we use the term *probabilistic*, we
do not assume that the corresponding distributions are probability
distributions" — and is what the successor-system arguments of §5 need. The two
moves between layers are the Jordan split and normalization
(`Probability/Lift.lean`).

    δ(X, Y) := ∑ₐ max(X(a) − Y(a), 0)                        `Probability.statDist`

is the statistical distance (LanMau20 Definition 3), one-sided on the signed
carrier and symmetric at equal weight. Landed: the triangle inequality, the
partition lemma, the data-processing inequality `δ(f X, f Y) ≤ δ(X, Y)`
(`statDist_fTransform_le`), the optimal-test identity, and the min form
`δ(P, Q) = |P| − ∑ min(P, Q)` without a `Fintype` hypothesis
(`statDist_eq_weight_sub_sum_min_of_support_subset`, MPR07 eq. (3)).

**Couplings.** A coupling of `X` and `Y` is a joint law with those marginals
(`IsCoupling`). Lanzenberger Lemma 2.8 in both halves: `δ(X, Y) ≤ Pr(X ≠ Y)`
for any coupling (`statDist_le_offDiagonalMass`), and a coupling attaining it
exists (`exists_coupling_offDiagonalMass_eq`). The `n`-ary maximal coupling is
`supAgreement_eq_weight_overlapDist`. The fiber coupling
(`exists_coupling_of_fTransform_eq`) joins two laws with a common pushforward,
which is what lifts a pointwise gluing construction to the level of laws.

**Information theory.** Mathlib has no entropy of a distribution and no Pinsker
inequality, so both are built here on `Distribution`. Guessing probability,
collision probability and distance from uniform, with min-entropy and collision
entropy in bits; conditional min-entropy in its guessing formulation, with
MauRen16's chain rule `H_∞(X|Y) ≥ H_∞(X) − log₂|𝒴|`. Shannon entropy,
conditional entropy, mutual information and conditional mutual information, each
inequality with its equality condition. Kullback-Leibler divergence in nats, with
Gibbs' inequality and Pinsker

    δ(X, Y) ≤ √(D(X ‖ Y)/2)                                  `statDist_le_sqrt_klDiv_div_two`

in a weight-general form as well as the textbook one. That the native divergence
*is* Mathlib's `InformationTheory.klDiv` is checked, not assumed, on the
`Fintype` probability slice (`Distribution.klDiv_toPMF`); the agreement is
scoped, because Mathlib's carries a total-mass correction term the native sum
does not.

**Counting.** Falling factorials, the birthday bound, permutation-consistency
masses and gate sums — carrier-free and metric-free, the arithmetic concrete
bounds bottom out in (`Probability/Counting.lean`).

---

## 2. Systems

`Lanzenberger Ch. 2 (primary) · CR18 Ch. 3 (secondary, for the total presentation)`

| object | definition | Lean |
|---|---|---|
| DDS | a partial function `s : 𝒳⁺ ⇀ 𝒴` with prefix-closed domain (Lanz 2.9) | `System.DDS` |
| DDE | a partial function `e : 𝒴* ⇀ 𝒳` with prefix-closed domain, active at `ε`; stopping is undefinedness — no stop symbol, no verdict bit (Lanz 2.11) | `System.DDE` |
| PDS | a distribution over DDS (Lanz 2.14) | `PDS X Y := Distribution (DDS X Y)` |
| PDE | a distribution over DDE (Lanz 2.15) | `PDE` |
| transcript | `x_i = e(y^{i−1})`, `y_i = s(x^i)`, with compatibility and stopping by stabilization (Lanz 2.12) | `System.tr`, `Compatible`, `Stops` |
| random system | the `≡`-class of a PDS (Lanz 2.17, Notation 2.19) | `PDS.Behaviour` |

Definition 2.14's common-domain clause is a **mixin**, imposed where it is
needed, exactly as the source keeps it a separate predicate.

**Two presentations of the environment, and one deviation.** Lanzenberger's DDE
stops by undefinedness. CR18 Definitions 3.6/3.7 give a *total* presentation in
which a refused query is answered by a distinguished symbol and the interaction
continues; that is the presentation the tree computes with
(`System.DDE.Total`, `PDS.trLawFullyDefined`), and it is where this development
**departs from the papers' usual reading: refusal is an observable answer.**
The consequence is not cosmetic (§4).

The statement-facing distance is the transcript advantage on that presentation:

    Adv⊥(S, T) := sup_{e, n} δ( tr(S, e, n), tr(T, e, n) )    `PDS.advFullyDefined`

— Lanzenberger Definition 2.26 read over total environments, with the
interaction length a second index of the supremum rather than a stopping
hypothesis. The supremum is over *deterministic* environments, which suffices in
the information-theoretic setting (Lanz 2.25's remark).

The output-bit distance (Jost Definition 2.2.8: a distinguisher is a system
into a one-shot Boolean signature) is also present as `PDS.maxEDist`, and
relating the two is a *theorem* about the two index sets, not a second
definition. Lanzenberger's own `Adv` — indexed by compatible, stopping
environments — is a third index set, and the coding maps between all three are
proved: `PDS.Adv_le_advFullyDefined` unconditionally,
`PDS.advFullyDefined_eq_Adv_of_dom_eq` on the shared-domain slice, and
`PDS.AdvD_eq_Adv` / `PDS.advFullyDefined_eq_AdvD` for the domain-indexed reading
the thesis actually uses.

**Equivalence and the class distance.**

    S ≡ T  :⟺  ∀ e. tr(S, e) = tr(T, e)                       `PDS.equivalent`   (Lanz 2.17)
    Δ(S, T) := inf over honest equivalent representatives of δ  `PDS.classDistance` (Lanz 2.28)

Non-adaptive environments already decide equivalence
(`PDS.equivalent_iff_nonAdaptive`, Lanz Lemma 2.18). `Adv⊥ ≤ Δ` is unconditional
(`PDS.advFullyDefined_le_classDistance`), so a coupling of *any* convenient
equivalent pair bounds the advantage — the static presentation is where bounds
are cheap, and `Adv⊥` is what endpoint statements read.

**Attainment.** On the slice where the query alphabet is finite, every
deterministic system in either support presents one common domain `D`, `D`
answers at most `q` queries, and both laws are honest:

    Δ(S, T) = Adv⊥(S, T)                    `PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded`   (Lanz 2.31)
    ∃ equivalent S′, T′ and a coupling with Pr(S′ ≠ T′) = Adv⊥(S, T)                                        (Lanz 2.32)

**The bundle is not bookkeeping.** Because refusal is observable, an environment
that reads refusals off the transcript separates systems that no static pair of
representatives separates; without the slice the equality is *false*, and a
witness at `PDS Bool PUnit` with `Adv⊥ = ½` against `δ = 1` for every equivalent
pair is on record.

**The quotient.** `PDS.Behaviour X Y` is Notation 2.19's `𝐒`, and the three
invariants descend to it. On the quotient `Adv⊥` separates points, so what is
installed is a genuine `EMetricSpace`, not a pseudo one; the attainment theorems
are restated there (`RandomSystems/System/BehaviourAttainment.lean`), which is
where the thesis states them.

**Multi-system distance.** Definition 2.27 and Theorem 2.29 are landed, with two
kernel-checked source errata: the printed `inf` over representatives must be a
`sup` (the verbatim display is kept as `printedMultiSystemDistance` and
*refuted*), and Theorem 2.29's `min` over pairs in the upper bound must be a
`max`.

---

## 3. Converters, the universe, and the algebra

**A converter is a system.** CR18 Definition 3.8: "a deterministic discrete
converter converting an `(X,Y)`-DDS into a `(U,V)`-DDS is just a DDS over the
converter alphabets", with a finite bound on consecutive inner requests. Two
presentations are carried and identified: the Definition 3.8 object itself
(`Converter.DDC`) and the converter as a single partial history function
(`Converter.ProtocolFn`), joined by the realization theorem
`Converter.apply_toDDC`. Serial composition is `Converter.apply_comp`; the
cascade and output-combine operators of CR18 Definitions 3.11/3.12 have their own
realization theorems against Definition 3.9 application.

**The universe.** MauRen16 §2.3 works over "a universe `Φ` of objects", and
specifications are its subsets. Here

    Uni := Σ X : Type u, X          Φ := PDS Uni Uni                `RandomSystems.Uni`, `Phi`

A query carries its own type, so an element's signature is not data on it:
`support` derives the queries a system answers, and "speaks `(X, Y)`" is
membership in a specification. Resources, converters and environments are all
elements of `Φ` — the roles are positional. Partiality is by undefinedness; there
is no error element.

**The converter monoid has no carrier.** A converter *is* its action:

    Σ ≤ Function.End Φ,   generated by relabelling, blocking/filtering, attachment

so composition closure and the action laws are definitional, and every
substantive law is proved per generator and extended by closure induction. The
metric-facing monoid is `RandomSystems.converterMonoidAt`, generated by
interface-indexed attachment of engines that are inner-total and answer within a
uniform request budget, by prefix-closed domain filters (which subsume MauRen16
§3.4's blocking `⊣` and CR18 Definition 3.10's query limit `[q]`), and by the two
parallel frames. Both hypotheses on the attachment family are load-bearing rather
than convenient: non-expansion is proved for exactly this family
(`converterMonoidAt_le_nonexpandingConverters`) and is deliberately not claimed
for the unmigrated attachment, whose composite can refuse *after* inner traffic
and so turns the deletion of a refused query into a rewind, nor for the family
budgeted only history by history. The design record for both is kept at the
definitions.

**Attachment at an interface.** MauRen16 §3.3's `αⁱ` is a primitive here, not
whole-face application wrapped in a relay engine. The commutation of disjoint
attachments is a theorem for the primitive (`System.attachEngineFully_comm`); the
relay design fails it, because a relayed round has already issued its request
when the completion refuses and must therefore *render* the refusal, and the
rendering is observable on both faces — the counterexample constructions are
recorded at the definition. The one axiom the abstract layer asks of an
attachment family is that attachments at distinct interfaces commute *in their
action* (never in the monoid: the monoid is free):

    i ≠ j  ⟹  αⁱ ∘ βʲ = βʲ ∘ αⁱ        `PairwiseOrderInvariant`, discharged by
                                        `Converter.pairwiseOrderInvariant_attach`

From it, disjoint interface sets give order-invariant honest/dishonest
attachment groups (`attachedWithin`, `orderInvariant_attachedWithin`), which is
MauRen16 §7's grouping and what every corruption split consumes.

**Parallel composition.** Inside a single universe there is no tagging step, so
composition is parameterized by a splitting `c` of the query alphabet
(`RandomSystems.par`), and each component sees only the sub-history of the
queries it owns. The `Par Φ` instance elects the splitting from the left
argument's own face (`parF`), and that election is canonical rather than
arbitrary: *every* separating splitting computes the same system
(`par_eq_parF_of_separating`).

---

## 4. The metric

    edist L M := Adv⊥(L, M) ⊔ Adv⊥(M, L)              `PseudoEMetricSpace Phi`

`Adv⊥` is one-sided on the signed carrier and symmetric exactly at equal weight,
so the installed distance is its symmetrization; on any two probability laws the
two coincide (`edist_eq_advFullyDefined_of_weight_eq`). Reflexivity, symmetry and
the triangle inequality are the `Adv⊥` laws read under `⊔`.

**Non-expansion** is MauRen16 Definition 2,

    d(αR, αS) ≤ d(R, S)      and      d(Rβ, Sβ) ≤ d(R, S)

as two independent `Prop` mixins over `edist` (`IsNonexpandingSMul`,
`IsNonexpandingPar`). On `Φ` the first is an *instance*: a converter is
**absorbed** when everything an environment learns by interacting with the
converted system it could have learnt from the bare system under a different
strategy, and each generator family discharges that by a re-simulation argument.
This is the hypothesis MauRen16 Lemma 2 consumes, not Lemma 2 itself.

The parallel half is **not** an unconditional instance and cannot be: this
carrier is signed and of arbitrary weight, and `parF` is parallel composition
only on separated faces. It is replaced by conditional theorems with the
hypotheses named (`smul_parF`, `edist_parF_parF_le`).

**Unbounded ideal objects are handled by a bounded slice, not by a bound in the
type.** `List X` is infinite even at finite `X`, so no finiteness lives on the
carrier; the finiteness the sources assume is carried by predicates
(`PDS.HasDomain`, `QBounded`, `HaveCommonDomainAndBounded`) attached to the
statements that need it, and CR18 §5.5's parameterized resources
(`Specification/Parameterized.lean`) are the abstract counterpart: a family
`{φ_r R}` of filtered restrictions of one *a priori* unbounded `R`, with a
single quantified protocol.

---

## 5. Specifications and constructions

`MauRen16 §§2-4 · JM20 §2.2 · CR18 §5.2`

    Specification Φ := Set Φ                                  `AbstractCryptography.Specification`
    𝓡 —π→ 𝒮  :⟺  π • 𝓡 ⊆ 𝒮                                   `Constructs`

The carrier has already absorbed behavioural equivalence, so membership is
exact. **Composition is transitivity of `⊆`** plus the action laws
(`Constructs.trans` — MauRen16 Lemma 1, CR18 Lemma 5.1, JM20 Theorem 1).
Simulators are a proof device, not part of the definition: employing one is just
one way of writing an ideal specification.

The generic layer beneath is `Refinement.Basic` — MauRen11 §3's Definition 5
(component and constructor sets), Definition 6 (reductions, `HasReduction`,
`Reduces`, `—[π]→`) and Definition 7 (`IsSeriallyComposable`,
`IsContextInsensitive`, `IsGenerallyComposable`). Nothing there mentions
resources or a metric.

**Relaxations.** A relaxation weakens a specification to an almost-as-good one,
so statistical error, no-guarantee interfaces and assumptions are all
*relaxations* rather than clauses hard-coded into the construction notion. CR18
and JM20 do not define the same thing — CR18's is a map on specifications,
JM20's a map on single resources lifted by union — and the tree records the
inclusion `JM20 pointwise lifts ⊆ Relaxation ⊆ CR18 extensive maps`.

| relaxation | definition | Lean |
|---|---|---|
| `ε`-ball | `𝓡ᵋ := ⋃_{R ∈ 𝓡} {R′ ∣ d(R, R′) ≤ ε}` | `Relaxation.epsilonRelaxation` |
| star | `𝓡^{∗H} := {αR ∣ α ∈ H, R ∈ 𝓡}` (CR18 Def 5.9) | `Relaxation.star` |
| right-outbound hull | `𝓡⟦ := {S ∣ S right-outbound, S⊣ ∈ 𝓡⊣}` (MauRen16 §3.4) | `Relaxation.outboundHull`, `outboundCompatible` |

Their compatibility with construction is the content of MauRen16 Lemmas 3-5 —
Lemmas 3 and 4 are stated in the source without proof — and all three are proved
here (`constructs_star`, `constructs_outboundHull`, `star_construct` and its
`ε`-form `star_construct_eps`). Errors add along a chain — JM20 Corollary 1.1,
MauRen16 Lemma 1 composed with Lemma 2 — as
`Constructs.epsilonRelaxation_trans`, which consumes exactly
`IsNonexpandingSMul`; on `Φ` that instance exists, so the corollary lands
(`constructs_epsilonRelaxation_trans_at`).

**Correction to MauRen16 eq. (2).** The paper claims `𝓡 ⊆ 𝓡⟦ = (𝓡⟦)⟦`. The
equality is a theorem (`outboundCompatible_idem`); the *inclusion* holds exactly
when every resource of `𝓡` is right-outbound (`subset_outboundCompatible_iff`),
which is the paper's implicit standing assumption at its use sites, and the
missing hypothesis cannot be dropped (`outboundHull_eq_empty_of_top`). On the
query-driven carrier `Φ` the hypothesis is itself a theorem: every resource is
right-outbound at single-interface blocking.

**Simulators and indifferentiability.**

    ∃ σ ∈ H.  d(πR, Sσ) ≤ ε   ⟹   R —π→ (S^{∗H})ᵋ           `constructs_of_simulator`
    Indifferentiable H ε R S                                  MauRen11 App. D Def 23
    Indifferentiable.construct                                MauRen16 Lemma 5

**The admitted constructor class.** MauRen16 §2.1's `Γ` restricts *which*
constructors count, on the possibility side as well as the impossibility side:

    Constructible Γ 𝓡 𝒮   ⟷   ¬ (𝓡 ↛ 𝒮)                      `unconstructible_iff_not_constructible`

§3.5's four converter-set models are instantiations of that parameter; the one
built here is the efficiency-bounded family `costBounded γ c`, with the
monotonicity chain the budget carries. **The cost function stays a parameter** —
no computational model is fixed and no performance function is built, following
CR18 §4.4.7's own refusal to fix one.

**Filtered specifications.** MauRen11 §§7.2-7.4's filters and local simulators:
`filteredAt` is the choice-free endpoint pattern, and Theorem 2's conclusion —
that simulation may be performed *locally* rather than jointly — is
`filteredAt_constructs_of_local_simulators`, with its `ε`-form.

---

## 6. Games and winnability

`Lanzenberger §§2.3.3, 2.4.3`

A **monotone condition** for a DDS is a monotone predicate on histories
(Definition 2.20). The carrier here is the *upper set* of histories, so
monotonicity is the closure property of the object rather than a side condition:
conditions form a complete lattice — `⊔` is the union every bad-event union bound
takes — and pull back along prefix-monotone maps. The thesis's `{0,1}`-predicate
form is kept as a certified view, by an equivalence.

A **game** is a distribution over pairs (system, condition) — Definition 2.22's
PDG, with the system and the condition *jointly* distributed. Its observables:

    ν(S^A) := sup_{e,n} Pr( tr(S^A, e, n) is winning )        `PDG.supWinProb`   (Def 2.25)
    ω(S^A) := inf over representatives of Pr( winnable )      `PDG.infWinnability` (Def 2.36)

`ν` is adversarial; `ω` is static — *winnable* means there is a query sequence
in the domain at which the condition already holds, with no environment and no
strategy involved. Theorem 2.37 says they are the same number and the infimum is
attained:

    ν(S^A) = ω(S^A)                                           `PDG.winnability_theorem`

on the finite one-domain query-bounded slice. Read operationally: a game with
maximal winning probability `δ` is, on some equivalent representative,
unwinnable on `1 − δ` of its own randomness. The proof taken is the thesis's own
*alternative* proof, reducing to Theorem 2.31.

CR18 Definition 5.10's **game-relaxation** `T̂^⊢` — "the set of PDS that behave
as `T` as long as the MBO is `0` and behave arbitrarily once the MBO is `1`" —
is made rigorous with the landed observables: membership is the existence of an
MBO making the enhanced game agree with `T̂` on the not-won slice.

---

## 7. The technique layer

Everything here is a definition over already-landed observables. No `S⁻`, `S⊣` or
`Γᵇ` operator is introduced, and no second stack of objects.

**Restricted equivalence.** Two games are *equivalent as games* when their
not-won transcript slices agree at every fixed query list (Maurer13b Definition
11, `PDG.EquivalentAsGames`). The definition's `i ≥ 1` is taken literally; that
quantifying over the empty history too would be strictly stronger is proved
(`exists_equivalentAsGames_notWonLaw_nil_ne`).

**The fundamental lemma of game playing** (Maurer13b Lemma 2, MPR07 Lemma 4):

    G ≡ᵍ H,  |G| = |H|   ⟹   Adv⊥(G⁻, H⁻) ≤ ν(G)              `PDG.fundamental_lemma_of_game_playing`

**Conditional equivalence** (Maurer13b Definition 13) is stated in the paper's
own division-free product form, so it carries no positivity guard; the guarded
quotient form is a theorem, and *is* the source's footnote that two conditional
distributions count as equal where both are defined
(`PDG.condEquiv_iff_condProb`).

    Ŝ|𝒜 ≡ T   ⟹   Adv⊥(Ŝ⁻, T) ≤ ν(Ŝ)                          `PDG.conditional_equivalence_theorem`

— Maurer02 Theorem 1(i), the first half of Maurer13b Theorem 3, with the
**adaptive** right-hand side. Its hypotheses are non-negativity and equal weight,
satisfied by any pair of probability laws: no query bound, no `Fintype`, no
totality clause. Composing with `ν = ω` replaces the supremum over environments
by a counting quantity (`conditional_equivalence_theorem_infWinnability`); that
is the same number written differently, not a smaller bound.

**Blind winning.** CR18 Definition 4.20 asserts that winning "blindly" — behind a
converter that forwards queries and discards replies — is the same as winning
*non-adaptively*. That assertion is a theorem here, proved in both directions
(`PDG.supWinProb_blockRepliesGame`), the converter side being the reply-erasing
engine and the environment side being the supremum restricted to non-adaptive
environments. `ν` is stated once: the blind quantity is Definition 2.25's own
supremum with its index set cut down, not a second operator. Then

    Ŝ|𝒜 ≡ T   ⟹   Adv⊥(Ŝ⁻, T) ≤ νᴺᴬ(Ŝ)                        `PDG.conditional_equivalence_theorem_blind`

is Maurer13b Theorem 3's "in particular" clause / CR18 Theorem 4.17: the
*adaptive* advantage bounded by the *non-adaptive* winning probability. The
chain `νᴺᴬ ≤ ν = ω` is strict in general, and *strict* is a theorem, not a
belief — a normalized two-query game over `Bool` has `νᴺᴬ ≤ ½ < 1 ≤ ν`
(`exists_blindSupWinProb_lt_supWinProb`). The paper's route to the bound goes
through an enhanced game and pays two extra clauses; the tree also proves the
bound without them (`conditional_equivalence_theorem_blind_subsumed`), so a
reader cannot mistake the proof's hypotheses for the statement's.

*Citation correction.* CR18's eq. (4.39) is the *conclusion* `Ŝ ≡ᵍ T̂`, not the
unnumbered enhancement display above it; the number is carried by
`equivalentAsGames_enhance`, and `PDG.enhance` cites the unnumbered display.

**Completeness of the bad-event method** (MPR07 Lemma 5). The bound above can be
made tight: for a restricted-equivalent pair whose common not-won law is the
pointwise minimum `min(p^S, p^T)`,

    Adv⊥(S, T) = ν(Ŝ) = ν(T̂)      `PDG.advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min`

and that minimum is not one choice among many but the *only* not-won law such a
pair can have (`winningMass_eq_statDist_iff_notWonLaw_eq_min`). The tight pair
exists at any fixed environment and interaction length
(`exists_gamesFor_notWonLaw_eq_min`), and uniformly on the equivalent corner.
`PDS.winning_probability_attainment_theorem` is the footnote-16 form. The gap
MPR07 flags between `Δ` and `δ` does not arise here, because `Adv⊥` is by
definition the supremum of the `δ`'s.

**The H-coefficient technique.** The system-facing half is one identity: the
probability a transcript is realized factors as an **environment factor** times a
**system factor**,

    tr(S, e, n)(t) = η(e, n, t) · σ(S, t)                     `transcriptEnvironmentFactor`, `transcriptSystemFactor`

resting on the *iff* that `tr(s, ē) = t̂` exactly when `s(x̂ⁱ) = ŷᵢ` and
`ē(ŷ^{i−1}) = x̂ᵢ` for all `i` (`System.DDE.Total.transcript_eq_iff`). The
environment factor does not mention the system, so it cancels from any *ratio*
of two transcript laws at the same transcript, and a hypothesis about that ratio
may be checked with the adversary deleted. The endpoint:

    (∀ t ∉ Bad. (1 − ε)·σ(T, t) ≤ σ(S, t))  ∧  (∀ e n. Pr_{tr(T,e,n)}(Bad) ≤ δ_b)
      ⟹  Adv⊥(S, T) ≤ δ_b + ε                                 `PDS.h_coefficient_theorem`

with the `ε = 0` and `Bad = ∅` specializations. The division of labour is the
method's integration contract: the ratio hypothesis mentions no environment and
no horizon at all, and the bad-mass hypothesis is the technique's sole adaptive
residue. A counting receipt must be length-indexed — constant `σ`-hypotheses are
degenerate, because `σ(S, [])` is the whole weight of `S`
(`transcriptSystemFactor_nil`).

---

## 8. The constructive layer

**Multi-party constructions** (LiuMau20 §2.4). A protocol is a tuple of
converters, one per interface, and one guarantee is stated per subset `Z` of
dishonest parties: if the assumed resource satisfies `𝓡_Z`, then the parties
outside `Z` applying their converters yields a resource satisfying `𝒮_Z`. The
converter monoids may differ per interface; the paper's single `Σ` is the
constant-family case.

MauRen11 §5.1's fixed-`Z` definition, with both clauses, is

    SecurelyConstructs Z simulators π ⊥ ε R S  :⟺
        d( π^{Zᶜ}(⊥^Z R),  ⊥^Z S ) ≤ ε                        (availability)
      ∧ ∃ σ ∈ simulators.  d( π^{Zᶜ} R,  σ S ) ≤ ε             (security)

**Context-restricted constructions** (Jost §4.2). The universally quantified
environment is replaced by a declared set of admissible contexts, a context being
a filter converter applied by the honest party together with an auxiliary
parallel resource, with one simulator and one budget per context. Definition
4.2.2 and its asymptotic form, the closure of a context set (Definition 4.2.4),
Proposition 4.2.5, both composition rules of Theorem 4.2.6, and Proposition
4.2.7's collapse to the ordinary notion at the identity context are all landed.
"Negligible" is abstracted to a budget class, and the paper's implicit `∥ 1`
extensions are written out.

---

## 9. Where this deviates from its sources

1. **Refusal is an observable answer.** The tree computes on CR18's total
   presentation of the environment, so a refused query is a visible answer and
   the interaction continues. This is why the attainment theorems need a slice,
   and why the deletion property has to be proved as a theorem rather than
   assumed (`keptPrefix_delete`, `fullyDefined_delete`).
2. **Unbounded ideal objects are handled by hypotheses, not by the type.**
   Finiteness lives in predicates on statements, and in the parameterized-resource
   calculus, never on the carrier.
3. **The converter monoid is generated, not carried.** A converter is an element
   of `Function.End Φ`; converter identity is equality of action, which is the
   right notion in the information-theoretic setting and would not be in a
   computational one.
4. **MauRen16 eq. (2)'s inclusion needs a hypothesis** (§5).
5. **Lanzenberger Definitions 2.27/2.28's `inf` over representatives must be a
   `sup`, and Theorem 2.29's `min` must be a `max`** (§2). Both printed forms are
   kept and refuted rather than argued away.
6. **Maurer13b Definition 11 is read literally at `i ≥ 1`** (§7).
7. **CR18 eq. (4.39) labels the conclusion, not the enhancement display** (§7).
8. **MauRen11 constructs are fenced.** The distinguisher class and everything
   indexed by it, the choice-setting layer, the two-party case and step-wise
   refinement are collected behind `AbstractCryptography.MR11`; the MauRen16-track
   roots import none of them. Nothing is deleted, and the fenced modules are kept
   compiling by their own build target.
9. **The computational setting is deferred.** The admitted constructor class is a
   parameter and the cost function is a parameter; no efficiency model, and no
   computational `Σ` or distinguisher class, is built.

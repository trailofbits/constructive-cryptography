# Carrier ledger — the validation gate

*(Commit hashes cited in this file resolve on branch
`archive/pre-squash-2026-08-18`; `main` is the squashed two-commit
history.)*

**SOURCE HIERARCHY (Marc, 2026-08-18; binding for every brief and ruling).**
Primary sources, in order: **MauRen16**, then **Jost thesis**, **LiuMau20 /
Liu-Zhang**, **Lanzenberger thesis**.  **CR18 is DEMOTED**: consult it ONLY
for a concept none of the primaries addresses (enumerated below), and say so
explicitly when doing it.  Never cite CR18 as the semantic authority for a
concept a primary covers — the 2026-08-18 defect this prevents: the par
output-alphabet question was argued from CR18 Def 3.4 as if it took a stance
(it does not; the paper never treats addressing), when MR16 §2.1-2.2 + Jost
are the governing sources.

CR18-FALLBACK register (load-bearing today; each flagged for re-grounding
review against Jost's formal system layer before extension):
  - the ⊥-completion semantics (fullyDefined/keptPrefix, "CR18 Def 3.3") and
    the total-environment transcript (DDE.Total, "Defs 3.6/3.7") — the
    Lanz-primary compatible-environment presentation EXISTS in-tree and the
    L1 coding map CONNECTS them; new metric statements prefer the primary
    presentation where both serve;
  - the converter budget (AnswersWithinBudget, "Def 3.8");
  - the concrete converter application (DDC.apply/connectFully, "Def 3.9") —
    MR16 §3.3 is the abstract authority; CR18 only realizes it;
  - filters ("Def 3.10", A8, deferred); memoryless attachment ("Def 3.13",
    PARTIAL-ONLY).
Existing NAMES citing CR18 definitions stay (renames are churn); their
docstring citations are historical provenance, not authority.
REGISTER ADDITIONS (CR18 sweep, 2026-08-18 — already in-tree, cited by
number): Def 4.9 iidPow / Def 4.10 clonePow (Distribution.lean), Def 6.2
δ-AUH + Def 7.2 2-universal (UniversalHash.lean), Exercise 4.4
(StatisticalDistance.lean), Def 5.9 (Algebra/Star.lean, CITATION-ONLY).
Also: Converter/Cascade.lean is converter SERIAL composition, NOT system
cascade Def 3.11 — Def 3.11 itself IS in the tree as `System.cascade`
(Converter/Converter.lean, `⊲ₚ`), PARTIAL-ONLY; see S-02 in the STRETCH
REGISTER ASSESSMENT (2026-08-18); "free interface" (§5.3.1, a ROLE)
collides with Algebra/Indexed.lean's exposed-index usage — disambiguate on
any future use.

**Rule (binding).** Every `def`/`abbrev`/`structure`/`instance` in
`RandomSystems/System/` and `RandomSystems/Converter/` must appear in this
file, classified. The gate `scripts/ledgerAudit.sh` extracts the inventory
from disk and FAILS listing any unclassified name. Run it before dispatching
any pipeline task and in every task's final gates. Rows are derived from the
tree, never from memory — that is the point of this document (defect record:
the 2026-08-17 B4 refutation was discoverable at planning time; the Phase-A
checklist was written from memory and missed `connect`).

Classifications:
- **RECEIPT** — carrier endomorphism with an s ↦ s⊥ homomorphism receipt
  (status PROVEN / PENDING / REFUTED). Metric work may consume PROVEN only.
- **METRIC** — the fully defined metric layer itself (migrated by construction).
- **PARTIAL-ONLY** — algebra on the partial carrier; receipts intact at their
  own level; NO metric claims may consume them before A6-style migration.
- **PRIMITIVE** — carrier plumbing/proof machinery; no receipt applicable.

## RECEIPT rows

| op | status | receipt / action |
|---|---|---|
| par, parRaw, historyAt | PROVEN | `fullyDefined_par` |
| blockSet | PROVEN | `fullyDefined_blockSet` |
| parallel, parallelDom, restrict, optionSigma | PROVEN | `parallel_fullyDefined` (output-agreement form) |
| emptySystem | PROVEN | trivial |
| par-partner endo (B6) | PROVEN | `exists_absorb_par` (B6), since A7 an instance of the general relay (`exists_absorb_relay`) |
| ofTyped, ofTypedRaw | PROVEN (A7), and as an ISOMETRY | crux `keptPrefix_ofTyped` (an undecodable query is refused by a condition on the HISTORY, so refusal precedes all traffic — `not_mem_dom_ofTyped_of_decodeOption_none`), `answer_ofTyped_none`/`_some`, `exists_absorb_ofTyped` (outwards, the relay at `decodeOption`) and `exists_absorb_ofTyped_typed` (inwards, the encoding environment `encodeEnv`, no replay needed); metric endpoint `PDS.advFullyDefined_ofTyped : Adv⊥(ofTyped RL, ofTyped SL) = Adv⊥(RL, SL)` |
| relabel | PROVEN (A7) | crux `keptPrefix_relabel` (pointwise, no window), `answer_relabel`, `exists_absorb_relabel`; metric: `PDS.advFullyDefined_relabelLaw_le` at arbitrary alphabets and `relabelLaw_mem_nonexpandingConverters` at `Uni`, where `relabelLaw` IS an endomorphism of Φ |
| block (Resource-level, Set P) | PROVEN (A7) | `fullyDefined_block` (the `s⊥` receipt) and `exists_absorb_block` (the absorption receipt), both the `blockSet` row read at the tag cylinder through `block_eq_blockSet` |
| filterDom, filterQueries | PENDING (CR18 Def 3.10 filters; O8/Budget) | A8 |
| connectFully (A6) | PROVEN (B4-RESUME, 2026-08-17) | refusal-first: `connectFully_refusal_first` under `InnerTotal` + `AnswersWithinBudget`; absorption: `exists_absorb_connectFully` under `InnerTotal` + `AnswersWithinBudget` + a **uniform** bound on the budget (CR18 Def 3.8's own "finite upper bound on consecutive requests"; the uniformity is load-bearing — see the def's docstring for why a merely well-founded budget admits no single inner length) |
| attachEngineFully (DRIFT-REPAIR legs a+b) | PROVEN (leg b, 2026-08-17) | refusal-first at the owned face `attachEngineFully_refusal_first` (InnerTotal + AnswersWithinBudget); transparency at the foreign face `attachEngineFully_transparent` — one equation of partial values (domain, answer, refusal all pass through; neither G1 relay witness applies); frontier receipts off `attachEngineFully_concat_round`; demotion bridge `attachEngineFully_univ`; **absorption `exists_absorb_attachEngineFully`** (InnerTotal + AnswersWithinBudget + uniform bound) at the mixed count `m := n * max K 1` — an owned round costs ≤ K, a foreign round exactly one, and `n * K` is wrong at `K = 0`; resource histories agree up to CR18 Def 3.3 deletion, invisible to rounds (`exists_mem_resolve_of_keptPrefix_eq`).  Metric endpoint `attachEngineFully_mem_nonexpandingConverters` (no `RequestsWithin` — absorption does not consume it) |
| idEngineFully | PROVEN | `connectFully_idEngineFully : connectFully idEngineFully R = R⊥` — the migrated identity IS the completion; not a Φ endomorphism (outer answers land in `Option Uni`) |
| connect, serve, runAux, lift, liftImpl, liftEvent, connectPhi (System), validate | REFUTED for attach-nonexpansion (B4 witness): serve makes inner refusal fatal → rewind | PARTIAL-ONLY: superseded for metric work by `connectFully` (A6); the old layer keeps its own §3.3/§3.4 receipts |
| toTyped, toTypedRaw | REFUTED-genre (decodes after inner traffic) | NOT touched by A6 (which is additive and leaves the old layer alone); belongs with A7's inclusion receipts, restated on `connectFully`.  A7 delivered the `ofTyped` isometry INSTEAD — which is the honest half: the inclusion transports in both directions, the projection does not, and `PDS.advFullyDefined_ofTyped` is what the `ℕ ⊆ ℝ` discipline needs |
| attachFully | PROVEN | `attachFully_mem_nonexpandingConverters` (InnerTotal + budget + uniform bound), via `exists_absorb_connectFully` and the pushforward reduction |
| converterMonoidFullyBudgeted | PROVEN | `converterMonoidFullyBudgeted_le_nonexpandingConverters` — the metric-facing Σ: uniformly budgeted attachments ∪ blocks ∪ par frames.  `AnswersWithinUniformBudget` is CR18 Def 3.8's request bound verbatim |
| converterMonoidFully | NOT CLAIMED (documented delta) | its attachment family asks only `∃ β, AnswersWithinBudget E β`, which absorption does not support; the budgeted sub-closure is what the metric consumes, and `converterMonoidFullyBudgeted_le_converterMonoidFully` records the relation.  `converterMonoid` is NOT changed |
| attach, block (Φ), connectPhi (Φ), converterMonoid, relabelLaw, blockLaw, connectLaw, attachEngineLaw, applyLaw, General.attachAtLaw | inherit their System rows; `converterMonoid` stays as it is (B4 witness inside it); the re-based Σ is `converterMonoidFully` (A6-M4) |
| fullyDefinedSpec, ofPhi | slice bookkeeping on Φ | done (A3/B4-M5) |

## METRIC layer (migrated by construction)

T2 winnability additions (`RandomSystems/System/Winnability.lean`; Lanz
§2.4.3 Defs 2.35/2.36 + Thm 2.37, printed pp. 23-26 read visually; all
axiom-clean): `System.Winnable` (Def 2.35 verbatim on the pair),
`PDG.gameEquivalent` (Def 2.22 — the T3.3 open half, coarser than
PDS.equivalent per Rem 2.23), `PDG.infWinnability` (ω, Def 2.36, honest
reps per R9; = 0 off the honest carrier, empty sInf in ℝ),
`System.SawBit` (COINAGE — 𝒯_w on the derived view; sawBit_iff = the
run-structure identity), `System.gameView` (COINAGE — Def 2.21's
observable as one map), `PDG.HasDomain` (COINAGE — Def 2.14 at the game;
ONE clause, the twin derived), `PDG.gameEquivalentSetoid`/`GameBehaviour`/
`toGameBehaviour` (Rem 2.24's random game) with descended
`GameBehaviour.weight`, `GameBehaviour.supWinProb`,
`GameBehaviour.infWinnability`, `GameBehaviour.forget` (forget's fibre =
PDS.GamesFor — the R10 pattern at its stated level).  ENDPOINTS:
`supWinProb_le_infWinnability` (trivial direction),
**`PDG.winnability_theorem`** (ν = ω, via the thesis p. 26 alternative
proof reducing to Thm 2.31 — NOT the p. 25 induction, which rebuilds the
successor calculus; matches T3.8's REUSE-ARCH note),
`exists_unwinnable_representative` (the p. 24 operational reading),
`GameBehaviour.supWinProb_eq_infWinnability` (at the quotient).
NECESSITY RECEIPT: the empty-history clause (∀ g ∈ support, [] ∉ g.2.1)
is PROVED necessary — supWinProb_ne_infWinnability_single_emptySystem_top
(ν = 1, ω = 0 at ⊤ over emptySystem); any T3/T4 statement over games must
carry or discharge it (DomainSupported implies it).  RETIRED from the
reference repository: zeroMBO (= adjoin ⊥), blindize/IsBlind (~1400 lines
— blinding = DDE.Total.relabelOut (·,false)); playQueries reused.
Probability additions: apply_le_mass, not_of_mass_eq_zero_of_mem_support,
mass_and_add_mass_not_and, statDist_fTransform_le_mass_of_eq_off
(identical-until-bad, distributional); [Fintype] dropped from
mass_{tsub,sub}_mass_le_statDist (unused).

T1 game-layer additions (`RandomSystems/System/Game.lean`; Lanz §2.3.3
Defs 2.20-2.25, printed pp. 16-17 read visually; all axiom-clean):
`IsPrefixUpperSet` (COINAGE — Def 2.20 fn. 7 as closure), `MonotoneCondition`
(the MC as the upper set of satisfying histories; mathlib UpperSet unusable
— no prefix Preorder on List X, lex LE occupies the slot — so R10-v2's
flagged fallback subtype, ordered by INCLUSION so ⊔ = bad-event union) with
Lattice/OrderBot/OrderTop/CompleteLattice (⊥ = never won — the thesis's
always-losing system; ⊤ = won at []), `PrefixMonotone`/`BoolCondition`/
`toPred`/`ofPred`/`boolEquiv` (the CERTIFIED Def 2.20 equivalence, both
round trips), `PrefixMonotoneMap`/`comap` (COINAGES; condition transport, a
lattice hom, receipts at historyAt and keptPrefix), `DDG` (the pair),
`gameTranscript` (Def 2.21; carrier delta: the condition evaluates at
answeredQueries = comap keptPrefix), `Won`, `toBitSystem`/`ofBitSystem`/
`MonotoneBit`/`DomainSupported` (Maurer13b Def 9 as the DERIVED view, both
round trips; DomainSupported = exactly the bit view's image — ⊤ has no bit
position, now a THEOREM), `DDE.Total.relabelOut`/`mapOutputs`/`lastBit`
(Rem 2.23 for the derived view via the existing relabel id Prod.fst — no
IsBlind machinery, ~1400 reference-repository lines not transplanted),
`PDG` (Def 2.22: a distribution over PAIRS — the joint law), `gameTrLaw`/
`winningMass`/`supWinProb` (ν, Def 2.25; environments cannot read the
condition BY TYPE), `toBitLaw`/`ofBitLaw`, `forget` (= CR18 Def 4.18's S⁻
per the recast policy), `GamesFor` (Def 2.20's preposition; membership IS
the forgetting law, at the class), `adjoin` (Rem 2.24; forget_adjoin an
equality of laws).  Obligation 1 = the MonotoneCondition subtype;
obligation 2 = the GamesFor subtype; no proof fields.  DELTA vs the
reference repository: its game carrier is the bit form (GameWinnability
.lean:16-40); R10 makes the pair primitive — the difference is a theorem,
not style.  T2 inherits: supWinProb's lub facts carry NonNeg
(bddAbove_range_winningMass), the thesis's ω discipline.

R9 + DEF-2.14 FAITHFULNESS additions (2026-08-18; ClassDistance.lean,
Environment.lean, Behaviour.lean; audit: all six claims HOLD, incl. the
probed Δ(S,S)=⊤ edge and the degenerate-D congruence): `HasDomain` (Def
2.14's attribute at a named D), `CompatibleD` (Def 2.12's clause at the
domain), `Halts` (COINAGE — environment-only round bound; a D-indexed
stopping clause cannot carry the congruence), `AdvD` (COINAGE — Def 2.26
indexed by the domain; `AdvD_congr` NO HYPOTHESIS), `Behaviour.AdvD`
(COINAGE — the descent, a Quotient.lift₂).  classDistance now infimizes
over HONEST representatives (R9); Δ(S,S)=⊤ off the honest carrier (empty
infimum — thesis-correct, `classDistance_self` carries NonNeg, no simp);
Def 2.28's pair identity is the EQUALITY
`classDistance_eq_ofReal_multiSystemDistance`; couplings supply honesty
free (`IsCoupling.nonNeg_left/_right`).  G-6 addition (ParFace.lean):
`instParConverterMonoidAt` — MauRen11 §6.2's α∣β at the metric-facing Σ.

DRIFT-REPAIR leg (c) additions (`AttachEngineFully.lean` Φ-level section,
`MetricFullyDefined.lean`): `attachAt` — MauRen16 §3.3's αⁱ at the Φ level,
pushforward of `System.attachEngineFully`; receipt
`attachAt_mem_nonexpandingConverters`; supersedes `attachFully` = its
`i = Set.univ` case (`attachAt_univ`).  `converterMonoidAt` — THE metric-facing
Σ, interface-indexed (coinage, flagged): attachments at InnerTotal +
AnswersWithinUniformBudget ∪ blocks ∪ both parallel frames (last three
verbatim from `converterMonoidFullyBudgeted`); receipts
`converterMonoidAt_le_nonexpandingConverters` + S4 endpoints
`edist_apply_le_of_mem_converterMonoidAt`, `edist_mul_smul_le_of_edist_le_at`,
`constructs_epsilonRelaxation_trans_at`, derived IsNonexpandingSMul instance.
`converterMonoidAtWeakBudget` — the A6-budget variant (coinage, flagged), no
nonexpansion receipt, delta `converterMonoidAt_le_converterMonoidAtWeakBudget`.

DRIFT-REPAIR leg (d) addition: `ProtocolWithin` — MauRen16 §7's tuple of
converters, one per party, confined per-index (`RequestsWithin`) and in the
Σ-admitted class; abbrev, coinage flagged; packaging only — the mathematics
is `attachAt_comm`, stated with no packaging.

Lanzenberger L1 additions (`RandomSystems/System/ClassDistance.lean`): the
rejection-pruning machine for the coding map — `pruneStep`, `Blocked`,
`pruneRun`, `prunedNext` (house-continuation of the quarry's names, not
paper names), `prunedEnv` (coinage, quarry `prunedPartialDDE`),
`markAnswers` (coinage, quarry `someMap`).  Endpoints:
`PDS.equivalent_iff_nonAdaptive` (Lanz Lemma 2.18),
`PDS.equivalent_ofTyped_iff`, `PDS.Adv_le_advFullyDefined` (unconditional),
`PDS.advFullyDefined_eq_Adv_of_dom_eq` (the coding map — shared-domain
clause ONLY; no finiteness).  NOTE: `PDS.HasFixedDomain` is unusable for
two-system statements (one-system existential; two instances need not share
the domain, and the theorem is FALSE across distinct domains) — L2/L3
statements carry the explicit two-support `D` bundle until a two-argument
form exists.

Lanzenberger L2a/L3 additions (`RandomSystems/System/Attainment.lean`):
Notation 2.34's successor calculus (System.DDS.successor,
System.DDE.Total.successor, PDS.successorTransform — paper names) and its
inverse (System.DDS.prepend, PDS.prependTransform — quarry-continuation);
the finite shared-domain slice as a HYPOTHESIS BUNDLE
PDS.HaveCommonDomainAndBounded (coinage; no subtype — List X is infinite at
finite X) with the first-answer carriers PDS.firstQueries,
PDS.firstAnswerImage, PDS.firstAnsweredValues (coinages); Lemma 2.33's
apparatus System.DDS.glue, System.glueProfile, System.sliceOf, System.contOf,
System.profileOf, PDS.classChoiceDist, PDS.choiceOf, PDS.overlapOf,
PDS.trimOf, PDS.crossJointOf (coinages), System.successorDomain, and its
output PDS.FiniteClassJointWitness; the induction invariant
PDS.BoundedAttainmentWitness.  ENDPOINTS: Lemma 2.33
(exists_finiteClassJointWitness_of_common_side_weights); **Theorem 2.31**
(classDistance_eq_advFullyDefined_of_commonDomain_bounded + attainment +
classDistance_eq_Adv_of_commonDomain_bounded via the L1 coding map);
**Theorem 2.32** (exists_equivalent_coupling/probCoupling_offDiagonalMass_
eq_advFullyDefined_of_commonDomain_bounded).  Domain clause = explicit
two-support condition per the L1 HasFixedDomain note.

Lanzenberger L2b additions (`RandomSystems/System/MultiDistance.lean`):
Def 2.27's multi-system distance `multiSystemDistance` (COINAGE,
errata-corrected — printed outer inf over representatives is a sup), the
verbatim printed display `printedMultiSystemDistance` (COINAGE; erratum
target only), its supremum set `agreementValues` (COINAGE).  ENDPOINTS:
Def 2.28 eliminators at a pair (multiSystemDistance_le_statDist_of_
equivalent, le_multiSystemDistance); classDistance_le_ofReal_
multiSystemDistance (always-true direction ONLY — the unrestricted-vs-
probability-representatives question is OPEN and load-bearing, see pin
list); Thm 2.29 lower (classDistance_le_ofReal_multiSystemDistance_of_mem,
inf'_classDistance_le_multiSystemDistance) and upper
(exists_pair_multiSystemDistance_le, corrected max form).  Distribution
layer = Probability/MultiCoupling.lean (IsJointOf, agreementMass,
supAgreement, overlapDist, supportUnion, selectPair, Distribution.pi;
Lemma 2.30 = exists_pair_sum_min_le_of_forall_column_zero; the kernel-
checked printed_min_form_counterexample re-proved on this carrier).

Lanzenberger 2.19 additions (`RandomSystems/System/Behaviour.lean`):
`equivalentSetoid`, `Behaviour` (COINAGE; thesis writes bold S),
`toBehaviour`, descended `Behaviour.weight`, `Behaviour.advFullyDefined`, `Behaviour.classDistance`;
the metric is an **EMetricSpace** (quotient separates points:
equivalent_iff_advFullyDefined_eq_zero) — a strengthening over the pseudo
instance at Phi.  MR16-clean; the fenced MR11 Metric/Behaviour.lean is a
different object.

Lanzenberger U1 additions (`RandomSystems/System/SingleQuery.lean`):
`singleQueryDomain` (COINAGE), `DDS.singleQuery`, `singleQueryEquiv`;
endpoints eq_of_qBounded_one_of_answer_eq ((Option Y)^n reading at
QBounded-at-D) and singleQueryEquiv + card_singleQuerySubtype (the thesis's
Y^n reading at total single-query domain; the thesis never sees refusal).

R7'' additions (`RandomSystems/System/ParFace.lean`): `faceT` (typed
interface set), `parF` (RECEIPT/PROVEN — rides `par`'s `fullyDefined_par`),
`instParPhi` (the `Par Phi` registration), `copy` (RECEIPT/PROVEN —
composite of `relabel` + `blockSet`, both PROVEN; law level =
`blockLaw ∘ relabelLaw`, `copy_eq_blockLaw_relabelLaw`), `parUnit`,
`parTuple`, `tupleOn`, `tuple`, `parTyped` (surface; binary at an explicit
`ULift (Fin 2)` index list — `Finset.toList` order is unprovable).
Endpoints: two-splitting canonicity `par_eq_of_separating` +
`par_eq_parF_of_separating`; `parF_comm`/`parF_assoc` (separated faces);
`parF_absorb` (H1's documented off-regime theorem, `ofPhi` scalar; audit
D3: absorption CAN fire on copies when the right leg's face is EMPTY —
disjointness does not exclude `support M ⊆ support L` at empty faces; the
"unreachable from the surface" claim is corrected to "unreachable for
nonempty-faced legs", side condition never stated in-tree);
`face_copy_disjoint` + `parF_copy_comm` (surface separation by
construction); metric: `edist_parF_left_le` — unconditional in the VARYING argument only
(the fixed frame carries nonneg + weight ≤ 1 hypotheses; audit D2), `edist_parF_right_le`
conditional, `edist_parF_parF_le` the four-point conditional form (the
bare IsNonexpandingPar class stays unobtainable, G6.f); consumers:
`contextInsensitive_par_left` (§2.2, with `Par Sigma` + `SMulParClass`
carried as NAMED instance hypotheses, not hidden),
`constructs_star_par_converterMonoidWithin` (G7 carrier home; lives in
ParFace because StarFullyDefined is imported by it).

Lanzenberger 2.31/2.32-at-the-quotient additions
(`RandomSystems/System/BehaviourAttainment.lean`, NEW FILE — keeps
Behaviour.lean's import surface): `Behaviour.HaveCommonDomainAndBounded`
(COINAGE, ∃-form over toBehaviour fibres — the bundle constrains a
presentation, not a behaviour, so it does not descend; conclusions
choice-independent).  Endpoints: Thm 2.31 on classes
(`Behaviour.classDistance_eq_advFullyDefined_of_commonDomain_bounded`),
attainment as a MINIMUM over the fibre product, the EMetricSpace reading
(`Behaviour.edist_eq_classDistance_of_commonDomain_bounded` — the quotient
distance IS Δ on the slice), the Def-2.26 reading at representatives (strict Adv NOT DESCENDED —
shape observation, not a non-descent theorem.  TAXONOMY (Marc-probed, twice):
the theory NEVER READS the support — the thesis's Adv is indexed by
dom(S), a single attribute Def 2.14 equips every PDS with and Def 2.17
fixes classwide (supports differ freely, Example 2.16, and nothing
notices).  OUR PDS deliberately carries NO domain attribute (R1/R2,
partiality per-atom, no Def 2.14 constraint), so the strict Compatible
had to be rendered per-atom over the SUPPORT — presentation data — and
the signed carrier makes that data non-observable (canceling atoms).
The descent question is entirely an artifact of that substitution; same
root as the coding map's explicit D-bundle and unusable HasFixedDomain:
wherever the thesis says "the domain of S", our carrier must say
something per-presentation.  No counterexample produced; open micro-question whether
HONEST classes are Adv-invariant (refusal-pattern law plausibly pins the
domains present); priced at zero by R4′ — Adv⊥ reads nothing
presentation-bound and descends), Thm 2.32 both forms.  `Behaviour.ind` unused; no new induction.  Figure 2.1 closure:
`figure_2_1_single_query/_answers/_exhaustive/_exhaustive_dds`
(Example216.lean; the figure's 0 is `false`).  U5: convention recorded at
the bundle's docstring (q is a property of the SYSTEM; the tree has no
environment-side budget object); residue = A8-blocked bridge + pin-3/L5
construction half.  QBounded call-site claim now stale (SingleQuery.lean,
Attainment.lean).

Lanzenberger 2.16 artifact (`RandomSystems/System/Example216.lean`, worked
example): zeroFn, oneFn, idFn, flipFn, atom, V, extremes, classPair;
equivalent_V via successor transformations (α-independent — no behaviour
function needed); statDist_V_zero_V_half = 1 with V_zero_ne_V_half;
definition_2_28_printed_displays_disagree + corrected_display_agrees_at_V
(the Def 2.27/2.28 erratum, kernel-checked in-tree).

RS-DISCHARGE #77 additions (`RandomSystems/System/StarFullyDefined.lean`):
`converterMonoidWithin A` — MR16 §3.4's admitted converter class AT ONE
INTERFACE (coinage, flagged): the sub-class of `converterMonoidAt` generated
by attachments with interface and requests inside `A`; blocks/par-frames
deliberately excluded (⊣ is RightOutbound's separate blk; frames act outside
the interface).  `blockConverterAt A` — §3.4's ⊣ as an element of the
metric-facing Σ (coinage; NOT named blockAt — `Converter.blockAt` is an
unrelated PARTIAL-ONLY object and check 1 matches bare names).  Key carrier
theorem: `System.attachEngineFully_eq_blockSet_of_dom_eq_empty` — ⊣ IS an
interface-local attachment (block A = attachAt A at the silent engine), so
block inherits `attachAt_comm` with no new induction, and ⊣ lies inside the
class at A.

DDE, EnvValid, Total, PDE, Compatible, Stops, Transcript, trStep, trN, tr,
trLaw, transcript, transcriptInputs, transcriptOutputs, answeredEntries,
answeredQueries, Complete, total, trLawFullyDefined, advFullyDefined, Adv,
maxEDist, nonexpandingConverters, absorb, answer, Distinguisher,
distinguishers, Equivalent, verdict, sysAnswer, sysAnswers

A7 generalization (2026-08-17): the block and par replays were the same
machine, and are now ONE — `relayReplayStep, relayReplay, relayNeed,
absorbRelay` (the re-simulation for any construction whose outer round costs at
most one inner query), with `exists_absorb_blockSet`, `exists_absorb_par`,
`exists_absorb_relabel` and `exists_absorb_ofTyped` derived from
`exists_absorb_relay` at their own relay data.  The names `blockReplay*,
blockNeed, absorbBlock, parReplay*, parNeed, absorbPar` are GONE, not renamed;
the theorem statements they served are unchanged.

A7 inclusion plumbing: decodeOption (decoding as a total function — the
`Option` form of `decode`, one named term so every use site elaborates the same
decidability instance), encodeEntry, encodeEnv (the encoding environment for
the inward direction).

B4-RESUME additions (the engine's re-simulation machinery, same genre one layer
deeper — a round issues several inner queries, so it cannot be a relay):
move, roundReplay, fullyReplayStep, fullyNeed, fullyReplay, absorbFully.
`move` is the engine's move as a total function (general infrastructure,
coinage, stated at the point of use as `answer` is).

R4' additions (`ClassDistance.lean`, the second thesis presentation of the
distance, first-class alongside `advFullyDefined`): equivalent (Lanzenberger
Definition 2.17 over the CR18 total presentation — the domain clause is
subsumed, refusals being observable answers) and classDistance (Definition
2.28, `Δ(S,T)` = the infimum of `δ` over pairs of equivalent representatives).
`equivalent` is not to be confused with `Equivalent` above, which is Jost's
strict-test relation.

## PARTIAL-ONLY algebra (no metric claims before A6-style migration)

liftAt, liftAtRaw, attachEngine, attachEngineAt, tagAt, AttachState, eProj,
eProjStep, lastTag, idEngine, cascade, cascadeAccess, cascadeAccessStep,
cascadeConverter, cascadeLeftHistory, cascadeMiddle, cascadeRightHistory,
cascadeViaConverter, combine, combineConverter, combineViaConverter, comp,
compAt, compGo, connStep, attachAt, attachDefined, attachDrive, attachEntry,
attachEntryD, attachEntryStep, attachFamily, attachHistory, attachOutput,
attachRaw, attachResolve, attachStep, relabelAt, blockAt, monoid, act,
connectionAct, instMulAction, instMulActionConnection, instSMul, moveOf,
drive, driveFrom, driveOuter, apply, applyRaw, applyRawAt, DDC, IsDDC,
IsDDCEventually, idDDC, blkDDC, toDDC, toDDCRaw, toNu, fromCOut, CIn, COut,
ConverterImpl, Protocol, ProtocolFn, engine, engineRaw, run, state, step,
stepOutput, botReactive, BotFree, JunkFree, ParsesTo, ParsesToAux,
AnswersEventually, AnswersInY, AnswersWithin, AnswersWithinAt,
AnswersWithinDepth, TraceEquiv, Rel, normalize, pair, replay, resolve,
queryLimit, queryLimitApply, queryLimitFn, queryLimitOutputFrom,
queryLimitTrace, growBudget, answerGrowthFn, roundGrowthFn, roundsInner,
roundsInputs, roundsMiddle, roundsOutputs, roundsTrace, restrictionFn,
simpleFn, simpleFnJunk, outputOne, Filter

## PRIMITIVE (carrier plumbing; no receipt applicable)

DRIFT-REPAIR leg (a) additions (the ownership-dispatch plumbing and the
interface-indexed converter class; `RandomSystems/System/AttachEngineFully.lean`):
RequestsWithin, attachEngineFullyRound, attachEngineFullyDrive,
attachEngineFullyRaw, ReachedAt.  `RequestsWithin` is the engine-side clause
owed by an interface-local attachment — the engine's requests carry addresses
in `i` — orthogonal to `InnerTotal` / `AnswersWithinBudget` /
`AnswersWithinUniformBudget`, which say how the engine reacts, not where it
reaches; it is the clause leg (d)'s commutation consumes.
`attachEngineFullyRound` is the dispatch itself (a query in `i` is a CR18
Def 3.9 round against `R⊥`, a query outside `i` is the resource's own step,
undefined exactly where the resource declines); `attachEngineFullyDrive` is the
outer iteration and `attachEngineFullyRaw` its last-answer projection.
`ReachedAt` is `ReachedState` made `i`-aware, and stays a relation for the same
reason `ReachedState` is one: an owned round is a least fixed point, so no
total scan computes the reached state.

DRIFT-REPAIR leg (b) additions (the interface-indexed re-simulation machinery,
`RandomSystems/System/AttachEngineFully.lean`): attachEngineFullyReplayStep,
attachEngineFullyNeed, attachEngineFullyReplay, absorbAttachEngineFully.  The
B4-RESUME block one dispatch deeper: `attachEngineFullyReplayStep` routes an
owned outer query into `roundReplay` (an owned round IS the same engine round,
so A38 is reused verbatim) and a foreign one into the relay genre — one inner
answer, returned unchanged, which is what `attachEngineFully_transparent` buys;
`attachEngineFullyNeed` reports the round replay's request inside `i` and the
foreign query itself outside it; `attachEngineFullyReplay` is the iterate and
`absorbAttachEngineFully` the absorbed environment, which depends on the outer
environment, the length, the interface, the engine and the budget — never on
the resource.

A6 additions (label plumbing and the converter-class predicates; not
endomorphisms, so no receipt applies): ofEngine, unlabel, ReachedState,
InnerTotal, AnswersWithinBudget, AnswersWithinUniformBudget (B4-RESUME: the
same clause with the bound uniform over histories, which is how CR18 Def 3.8
states it and what absorption needs).  `InnerTotal` is a flagged REPLACEMENT for
CR18 Def 3.8's input-alphabet clause (`Converter.AnswersInY`, which demands the
opposite and is the B4 pathology in the definition); `AnswersWithinBudget` is
Def 3.8's finite-bound clause in well-founded form.

DDS, Raw, Valid, PDS, Phi, Uni, Resource, TypedAt, typed, dom, output,
toPFun, support, encode, decode, decodeList, keptPrefix, fullyDefined, ofDDS,
functionEvaluator, historyEvaluator, ioTranscript, QBounded, QExtensible,
PrefixClosed, inputInterface, interfaceAlphabet, parAddr, parAlphabet,
parAns, parLaw, paperAlphabet, paper1, paper2, paper3, paper4

# MR16 OBLIGATION MATRIX

**LAYERING RULE (Marc, 2026-08-17).** The work order follows MauRen16's own
architecture: the ABSTRACT theory ((Phi, Sigma, d) axioms and the
specification calculus proven from them) completes FIRST; RS-DISCHARGE
receipts (the Random Systems model verifying each axiom) follow.  Every gap
below is tagged ABSTRACT or RS-DISCHARGE; no RS-discharge leg is dispatched
while an ABSTRACT gap of the same section is open.

**Purpose.**  Certify that the *generic core* of MauRen16 — the crypto algebra
that Liu-Zhang, Jost and Lanzenberger layers will all depend on — is formalized
abstractly and instantiable at the RandomSystems level.  Applications are out
of scope.  This section turns "is MR16 done?" from an assertion into a
checkable artifact.

**Rule (binding).**  *Every* GENERIC-CORE row must reach
**DONE-ABSTRACT+INSTANTIATED** before the "MR16 basics are done" claim may be
made anywhere in this repository.  APPLICATION rows are explicitly out of
scope and are never a reason to hold the claim.  A row whose only home is a
module behind the provenance fence below counts as a **gap**, not as done.

**Status vocabulary.**

| status | meaning |
|---|---|
| `D+I` | DONE-ABSTRACT+INSTANTIATED — an abstract declaration *and* a RandomSystems instantiation, both named |
| `DA` | DONE-ABSTRACT-ONLY — the abstract statement exists and is proved; no RandomSystems carrier instantiates it |
| `PARTIAL` | present but incomplete; the row says exactly what is missing |
| `MISSING` | no declaration anywhere |
| `FENCE-ONLY` | the only home is a fenced module — a gap by the rule above |
| `PROSE` | modeling discipline with no formal content; no obligation |

**The two RandomSystems carriers.**  The MR16 obligations are split across two
distinct carriers, and this split is itself the largest finding (gap G5).

* **RS-A** — `Φ := PDS (P × X) Y`, `Σ := FreeMonoid (P × Converter.DDC X Y X Y)`
  acting by `Converter.attachFamily`.  Home of §3.3, §3.4 and §7.  Carries
  `PDS.maxEDist` but **no** `PseudoEMetricSpace` instance.  The receipts file
  `RandomSystemsReceipts.lean` is stated here, and its closing FRONTIER comment
  is an in-tree admission of the missing metric joins.
* **RS-B** — `Φ := Phi.{u} = PDS Uni Uni`, `Σ := converterMonoidAt` — the
  interface-indexed attachments `attachAt i E` (InnerTotal + CR18 Def 3.8
  uniform bound) ∪ blocks ∪ both parallel frames.  `converterMonoidFullyBudgeted`
  is the whole-face sub-closure `i = Set.univ`, still valid
  (`converterMonoidFullyBudgeted_le_converterMonoidAt`), no longer the Σ new
  statements name
  (a `Submonoid (Function.End Phi)`).  Home of the metric: `edist` = the
  symmetrization of `PDS.advFullyDefined`, MauRen16 Definition 2, and the
  ε-relaxation calculus.  Carries **none** of §3.4's relaxations.
* **RS-A′** — `Phi` under the older `attach` / `connectPhi` action
  (`converterMonoid`).  Classified PARTIAL-ONLY above (the B4 witness lives
  inside it), so its receipts may not be consumed by metric work.

**Enumeration.**  MauRen16 (TCC 2016-B, pp. 1–22) read visually in full.
**69 items** enumerated: **48 GENERIC-CORE**, **21 APPLICATION**.
GENERIC-CORE status tally (2026-08-17, after G8/G12): **28 `D+I`**, 8 `DA`,
9 `PARTIAL`, 1 `MISSING`, 1 `FENCE-ONLY`, 1 `PROSE`.
**28 of 48 — the "basics done" claim was not yet supported (superseded — see MATRIX CENSUS).**

## GENERIC-CORE rows

| # | item | p. | abstract home | RandomSystems instantiation | status |
|---|---|---|---|---|---|
| 1 | §2.1 construction `𝓡 —γ→ 𝓢` | 4 | `Constructs` (`Specification/Basic.lean`), `HasReduction` instance | RS-A `RandomSystemsReceipts.lean` §2; RS-B via `constructs_singleton_epsilonRelaxation_iff` | `D+I` |
| 2 | §2.1 constructor set `Γ`, possibly cost-restricted | `Constructible` (Specification/ConstructorClass.lean); `Unconstructible` = its negation | RS-B ParFace.lean §ConstructorSet (d6f07c3), TWO readings: Γ = the metric-facing Σ in Function.End Phi (generic entry constructible_of_constructs_converterMonoidAt; constructible_attachAt; fn.6 closure constructible_trans_attachAt; §4.2 constructible_star_epsilonRelaxation_of_simulator_at; constructible_parF_left; unconstructible_converterMonoidAt_iff puts rows 2/3 over ONE Γ) and Γ = converterMonoidWithin B inside Σ (Lemma 3 constructible_star_converterMonoidWithin; Cor 1.1 constructible_epsilonRelaxation_trans_converterMonoidWithin; mono). HONEST: the ε-calculus exists only in the subtype reading — IsNonexpandingSMul is FALSE at Function.End Phi | — | `D+I` (2026-08-18, d6f07c3) |
| 3 | §2.1 non-constructibility `𝓡 ↛ 𝓢` | 4 | `Unconstructible` (`Specification/Outbound.lean`) | RS-A `RandomSystemsReceipts.lean` §4 | `D+I` |
| 4 | §2.1 tuple specification `[𝓡₁,𝓡₂,𝓡₃]` | 4 | `Par` class (`Refinement/Basic.lean`), `instance Par (Specification Φ)` | `RandomSystems.par`, `parLaw`, `par_comm`, `par_assoc` exist — but **no `Par Phi` instance is registered** | `D+I` (rescore 2026-08-18, audit-verified: instParPhi + parTuple/PDS.tuple/parTyped (R7'', cad5da1..b0a6265)) |
| 5 | §2.2 composability `𝓡—γ→𝓢 ∧ 𝓢—γ′→𝓣 ⟹ 𝓡—γ′∘γ→𝓣` | 4 | `Constructs.trans`, `IsSeriallyComposable` instance | RS-A `RandomSystemsReceipts.lean` §2 | `D+I` |
| 6 | §2.2 context-insensitivity `[𝓤,𝓡,𝓥] —γ→ [𝓤,𝓢,𝓥]` (+ fn. 1 addressing) | 5 | `IsContextInsensitive` instance, `Constructs.par_left`, `red_one_par` | `attachEngine_par` (`Par.lean`) is the concrete content, not presented as `IsContextInsensitive`; needs row 4 | `D+I` (rescore 2026-08-18, audit-verified: constructs_parF_left/constructs_parF + smul_parF (G-6, 5471084)) |
| 7 | §2.3 specification = subset of a universe `Φ` | 5 | `Specification Φ := Set Φ` | `Phi` (`Phi.lean`), `fullyDefinedSpec : Set Phi` | `D+I` |
| 8 | §2.3 ε-ball at a point `Rᵋ = {R′ \| R′ ≈ᵋ R}` | 5 | `Relaxation.epsilonRelaxation`, `WithinEDistance` | RS-B `instance : PseudoEMetricSpace Phi`, `edist_def` | `D+I` |
| 9 | §2.3 ε-ball at a specification `𝓡ᵋ = ⋃_{R∈𝓡} Rᵋ` | 5 | `epsilonRelaxation` (built by `ofPointwise`, the union lift), `mem_epsilonRelaxation_iff` | RS-B, same instance | `D+I` |
| 10 | §2.3 monotonicity `𝓡′⊆𝓡, 𝓢⊆𝓢′ ⟹ 𝓡′—γ→𝓢′` | 5 | `Constructs.mono` | fires at both carriers by instance | `D+I` |
| 11 | §2.3 impossibility duality `𝓡⊆𝓡′, 𝓢′⊆𝓢 ⟹ 𝓡′↛𝓢′` | 6 | `Unconstructible.anti` | RS-A `RandomSystemsReceipts.lean` §4 | `D+I` |
| 12 | §3.1 multi-interface resources; two-interface (Alice left / Eve right) | 6 | `Specification/Interfaces.lean` (`attachedWithin`), `Outbound.lean`'s `eL`/`eR` hom pair | interface address in the query: `P × X` (RS-A), tags on `Uni` (RS-B) | `D+I` |
| 13 | §3.1 metric = optimal distinguishing advantage of a class `𝓓` (informal; the paper defers it) | 6 | MR16 track has only `PseudoEMetricSpace`; the class-indexed object `DistinguisherClass` / `edistD` is fenced | RS-A `PDS.maxEDist`; RS-B `advFullyDefined` / `edist` — **two different distances** | `PARTIAL` (gaps G5, G10) |
| 17 | §3.3 converter set `Σ`, `αⁱ : Φ → Φ` | 7 | `Monoid Sigma` + `MulAction Sigma Φ`, `mulActionOfAttach`, `attachedWithin` | RS-A `Converter.attachFamily` action; RS-B `converterMonoidFullyBudgeted` | `D+I` |
| 18 | §3.3 `(β∘α)ⁱR = βⁱ(αⁱR)` | 7 | `attach_mul`, `mul_smul` | action laws by construction at both carriers (`Function.End` composition at RS-B) | `D+I` |
| 19 | §3.3 `id ∈ Σ`, `id∘α = α∘id = α` | 7 | `attach_one`, `one_smul` | RS-A `Converter.attachFamily_idDDC_smul`; RS-B `idEngineFully`, `connectFully_idEngineFully`, `connectPhi_id` | `D+I` |
| 20 | §3.3 `Σ∘Σ = Σ` (closure; equality because `id ∈ Σ`) | 8 | `Submonoid Sigma`, `supportedOn`, `nonexpandingEnd` | `converterMonoid`, `converterMonoidFully`, `converterMonoidFullyBudgeted`, `Converter.monoid` — all `Submonoid` | `D+I` |
| 21 | §3.3 two-interface notation `αR`, `Rβ` | 8 | `eL : SigmaL →* Sigma`, `eR : SigmaR →* Sigma` (`Outbound.lean`) | RS-A `attachedWithin e Z₁` / `attachedWithin e Z₂` | `D+I` |
| 22 | **§3.3 commutation `(αR)β = α(Rβ)`** | 8 | `OrderInvariant`, `PairwiseOrderInvariant`, `orderInvariant_attachedWithin`, `actCommute_of_disjoint` | RS-A `Converter.pairwiseOrderInvariant_attach`, `Converter.orderInvariant_attach`; RS-A′ `ConnectPhi.pairwiseOrderInvariant_attach`, `orderInvariant_attach` — **no receipt at all for `attachFully` / `converterMonoidFullyBudgeted`**; the interface-local family it needs is supplied by the ruled `attachAt` primitive, whose row list and legs are the `DRIFT-REPAIR` section below (the refuted `relayExcept` design is retained there as row C22) | `D+I` (leg d: `attachEngineFully_comm`, `attachAt_comm`/`attachAt_actCommute`, `pairwiseOrderInvariant_attachAt`, `orderInvariant_attachAt`, inside Σ via `attachedWithin_attachAt_le_converterMonoidAt`) |
| 23 | §3.3 `𝓡 ⊆ Φ`; singleton `{R}` | 8 | `Specification`, `⟪R⟫`, `constructs_singleton_iff` | RS-B uses the singleton form throughout `MetricFullyDefined.lean` | `D+I` |
| 24 | §3.3 `α𝓡 = {αR \| R∈𝓡}`, `𝓡β`, `α𝓡β` | 8 | pointwise `•` on `Set Φ` (mathlib `Pointwise`) | consumed at both carriers | `D+I` |
| 25 | §3.4 `𝓡* := 𝓡Σ` | 8 | `Relaxation.star` (`Algebra/Star.lean`), `mem_star_iff`, `star_mono_submonoid` | **none** — every use site is abstract | `D+I` (rescore 2026-08-18, audit-verified: converterMonoidWithin + mem_star_ iff (#77, f63c4ed)) |
| 26 | §3.4 **eq. (1)** `𝓡 ⊆ 𝓡* = (𝓡*)*` | 8 | `Relaxation.star`'s `le_toFun` field; `star_idem` | none | `D+I` (rescore 2026-08-18, audit-verified: subset_star_/star_idem_converterMonoidWithin (#77)) |
| 27 | §3.4 blocking converter `⊣`; `R⊣` | 8 | `blk : SigmaR`, `blocked` (`Outbound.lean`); `blk` parameter in `Algebra/Star.lean` | RS-A `Converter.blkDDC`, `blkDDC_mem_attachedWithin`; RS-B `block`, `blockSet`, `blockLaw`, `block_mem_converterMonoidFullyBudgeted`, `block_mem_nonexpandingConverters` | `D+I` |
| 28 | §3.4 right-outbound `R*⊣ = R⊣` | 8 | `RightOutbound` — **two renderings**: `Outbound.lean` (`eL`/`eR`) and `Relaxation.RightOutbound` (homogeneous) | RS-A `Converter.rightOutbound_attach` (a *theorem* there: every resource is right-outbound at single-interface blocking); RS-B none | `D+I` (rescore 2026-08-18, audit-verified: rightOutbound_blockConverterAt + rightOutbound_subtype (#77, ff66d4d)) |
| 29 | §3.4 `𝓡⟦ := {S \| S right-outbound, S⊣ ∈ 𝓡⊣}` | 9 | `outboundCompatible` (`Outbound.lean`) and `Relaxation.outboundHull` (`Star.lean`) — duplicate renderings | RS-A `RandomSystemsReceipts.lean` §4; RS-B none | `D+I` (rescore 2026-08-18, audit-verified: mem_outboundHull_blockConverterAt_iff, both renderings (#77)) |
| 30 | §3.4 **eq. (2)** `𝓡 ⊆ 𝓡⟦ = (𝓡⟦)⟦` | 9 | equality: `outboundCompatible_idem`, `outboundHull_idem`.  Containment: `subset_outboundCompatible_iff`, `subset_outboundHull` — **with the tree's correction that it is NOT unconditional**, and the counterexample `outboundHull_eq_empty_of_top` | only the `RightOutbound` premise, at RS-A | `D+I` (rescore 2026-08-18, audit-verified: subset_outboundHull_blockConverterAt UNCONDITIONAL here (#77)) |
| 31 | §3.5 everything relevant is modeled as part of the resource | 9 | recorded in `THEORY.md` and module docstrings; no declaration | — | `PROSE` |
| 32 | §3.5 `Σ` as a parameter (models 1–4: IT / memory-bounded / connect-only / poly-time) | 9–10 | `Sigma` is a type parameter; `Submonoid Sigma` and `supportedOn` select a class | model 1 (IT) is what both carriers instantiate; models 2–4 unmodeled | `PARTIAL` (gap G9) |
| 33 | §4.1 **Definition 1** `𝓡 —π→ 𝓢 :⟺ π𝓡 ⊆ 𝓢` | 11 | `Constructs`, `constructs_iff` | RS-A and RS-B (see row 1) | `D+I` |
| 34 | §4.1 **Lemma 1** composability | 11 | `Constructs.trans`, `IsSeriallyComposable` instance | RS-A `RandomSystemsReceipts.lean` §2 | `D+I` |
| 35 | §4.1 **Definition 2** non-expanding, *both* clauses | 11 | `IsNonexpandingSMul`, `edist_smul_le`, `nonexpandingEnd` | RS-B `nonexpandingConverters_le_nonexpandingEnd`, `edist_apply_le_of_mem_nonexpandingConverters`, `edist_apply_le_of_mem_converterMonoidFullyBudgeted`, two `IsNonexpandingSMul` instances; RS-A `PDS.maxEDist_applyLaw_le` (deterministic application only) | `D+I` — β-clause verdict below |
| 36 | §4.1 **Lemma 2** non-expanding ⟹ `𝓡—π→𝓢 ⟹ 𝓡ᵋ—π→𝓢ᵋ` | 11 | `Relaxation.epsilonRelaxation_compatible` with `compatible_iff` (together exactly Lemma 2) | RS-B: fires by the registered `IsNonexpandingSMul` instance and is consumed by `constructs_epsilonRelaxation_trans_phi` / `_fully`; never separately stated at `Phi` | `D+I` |
| 37 | §4.1 **Lemma 3** `𝓡—π→𝓢 ⟹ 𝓡*—π→𝓢*` (paper gives no proof) | 11 | `Relaxation.constructs_star` — proved | **none**; needs `star` at Φ (row 25) and the commutation premise (row 22) | `D+I` (rescore 2026-08-18, audit-verified: constructs_star_converterMonoidWithin (#77)) |
| 38 | §4.1 **Lemma 4** `𝓡—π→𝓢 ⟹ 𝓡⟦—π→𝓢⟦` (paper gives no proof) | 11 | `Constructs.outboundCompatible` and `Relaxation.constructs_outboundHull` — proved | RS-A `RandomSystemsReceipts.lean` §4, premise discharged by `orderInvariant_attachedWithin`; RS-B none | `D+I` (at RS-A only — gap G4) |
| 39 | §4.2 **eq. (3)** `πR ≈ᵋ Sσ` | 12 | `Indifferentiable`; the `edist (π • R) (σ • S) ≤ ε` premise of `constructs_of_simulator` | none | `D+I` (rescore 2026-08-18, audit-verified: indifferentiable_iff_at (#77, 01f64e9)) |
| 40 | §4.2 **Lemma 5** `∃σ∈Σ: πR ≈ᵋ Sσ ⟹ R —π→ (S*)ᵋ` | 12 | `constructs_of_simulator`, `Indifferentiable.construct`, `Relaxation.star_construct_eps` | **none** — `RandomSystemsReceipts.lean`'s FRONTIER comment says so in-tree | `D+I` (rescore 2026-08-18, audit-verified: constructs_star_epsilonRelaxation_of_simulator_at (#77)) |
| 41 | §4.2 remark `πRβ ≈ᵋ Sσβ` (the β-clause's load-bearing use) | 12 | `edist_mul_smul_le_of_edist_le` (`Metric/Nonexpansion.lean`, beside Definition 2) — right attachment is multiplication in the one monoid, so `IsNonexpandingSMul` is the whole hypothesis | RS-B `edist_mul_smul_le_of_edist_le_fully` at `converterMonoidFullyBudgeted`, by the registered `IsNonexpandingSMul` instance | `D+I` (G12 closed) |
| 42 | §4.2 indifferentiability as a construction type: `T ⊆ (S*)ᵋ`; `T = πR ⟹ R—π→(S*)ᵋ` | 12 | `Indifferentiable`, `Indifferentiable.construct`, `Indifferentiable.trans` | none (`Applications/Sponge.lean` consumes the pattern but is itself abstract) | `D+I` (rescore 2026-08-18, audit-verified: indifferentiable_construct_at + constructs_star_epsilonRelaxation_trans_at (#77)) |
| 43 | §4.2 simulators are a proof device, not part of the definition | 12 | structural: `Constructs` carries no σ; recorded at `Specification/Basic.lean` and `Algebra/Star.lean` | holds at both carriers by construction | `D+I` |
| 44 | §4.3 a converter absorbed into the distinguisher ⟹ the metric is non-expanding | 12 | the justification of `IsNonexpandingSMul`; no separate abstract declaration | RS-B `RandomSystems/System/Absorb.lean` entire: `absorb`, `exists_absorb_relay`, `exists_absorb_connectFully`, `exists_absorb_blockSet`, `exists_absorb_par`, `exists_absorb_ofTyped`, `exists_absorb_relabel`, `PDS.advFullyDefined_fTransform_le` | `D+I` |
| 45 | §4.3 `πR = Sβ`, `β ∉ Σ` ⟹ `πR = [S,β̄]σ` and `R —π→ ([S,β̄])*` | 13 | — | — | `D+I` (rescore 2026-08-18, audit-verified: constructs_star_par_converterMonoidWithin (ParFace, R7''); abstract home constructs_star_par_of_smul_eq (Algebra/Star.lean)) |
| 48 | §5 **fn. 9** `d(R,S) = sup_{D∈𝓓} Δ^D(R,S)` | 13 | class-indexed suprema live only in `Metric/Distinguisher.lean` (`edistD`), which is fenced | RS-A `PDS.maxEDist`; RS-B `advFullyDefined` / `edist` | `FENCE-ONLY` abstractly (gap G10) |
| 61 | §6 unnumbered, inside Theorem 2's proof: `(𝓡ᵋ)* ⊆ (𝓡*)ᵋ` | 18 | `Relaxation.star_epsilonRelaxation_subset_epsilonRelaxation_star` (`Algebra/Star.lean`) — from `IsNonexpandingSMul` alone, as the matrix predicted; the reverse inclusion is not claimed | none — needs `star` at Φ (row 25) | `D+I` (rescore 2026-08-18, audit-verified: star_epsilonRelaxation_subset_epsilonRelaxation_star_converterMonoidWithin (#77)) |
| 62 | §7 left interface = one sub-interface per honest party; combined converter = list of converters | 19 | `attachedWithin e Z`, `patternAttach`, `supportedOn` | RS-A `Converter.attachFamily` over `P`; RS-A′ at `Phi` | `D+I` |
| 63 | §7 protocol = tuple of converters, one per potentially honest party | 19 | the tuple monoid `∀ i, Γ i`; `patternAttach P π` | RS-A `attachedWithin` products | `D+I` |
| 64 | §7 grouping: honest interfaces left, dishonest right; one statement per dishonest set | 19 | `orderInvariant_attachedWithin`, `actCommute_of_disjoint` | RS-A `RandomSystemsReceipts.lean` §3; RS-A′ `ConnectPhi.orderInvariant_attach` | `D+I` |
| 65 | §8 indifferentiability restated: special type `S*` with `S` right-outbound | 19 | same as row 42 | none | `D+I` (rescore 2026-08-18, audit-verified: constructs_star_epsilonRelaxation_trans_at (#77)) |

**Definition 2, the β-side — verdict.**  The tree has **no distinct β-side
statement**, and on the carriers it actually uses it does not need one.
`IsNonexpandingSMul` quantifies over *every* `c : Sigma`, and in both the
abstract interface-indexed model and the RS instantiations `αR` and `Rβ` are
actions of elements of the *same* monoid (`Pi.mulSingle` at a left- resp.
right-face interface; a tag-addressed `attachFully` at RS-B).  So the β-clause
is the same universally quantified statement, not a second axiom — row 35 is
genuinely `D+I`.  The residue is real but narrow: `Specification/Outbound.lean`
is the one place where left and right attachment are *distinct* monoids
(`eL`, `eR`), and that module imports no metric at all, so
`d(Rβ, Sβ) ≤ d(R, S)` is nowhere stated in the two-sided presentation and the
two presentations are not connected (gap G11).  Recorded at
`Metric/Nonexpansion.lean` by the M3 pass.

## APPLICATION rows — out of scope

Enumerated for completeness; no obligation follows from any of them.

| # | item | p. |
|---|---|---|
| 14–16 | §3.2 URF resource; the five example specifications 1–5; fixed- and arbitrary-input-length random oracles | 6–7 |
| 46–47 | §5 `PRᵏ` public randomness; `RO^{m→n}_{[q,q′]}` random oracle | 13 |
| 49–51 | §5 **Lemma 6** `PRᵏ ↛ PR^{k+1}⟦ᵋ`; **eq. (4)**; distinguisher `D₁` | 14 |
| 52–53 | §5 **Corollary 1**; **eqs. (5), (6)** | 15 |
| 54–55 | §5 **Theorem 1**; **eq. (7)**; distinguisher `D₂` | 16 |
| 56–60 | §6 **Theorem 2** and **eq. (8)**; **Lemma 7**; the simulator σ algorithm; **eqs. (9), (10)** | 17–18 |
| 66–69 | Appendix `H_min(X\|Y)`; **eq. (11)** chain rule; **Proposition 1**; **Corollary 2** | 20 |

## GAP LIST

Ordered by dependency: G1 is the root; G2 and G3 chain off it.

**G1 — §3.3's commutation `(αR)β = α(Rβ)` is not proved for the
metric-facing Σ.**  `converterMonoidFullyBudgeted`, built from `attachFully`,
has no `ActCommute` / `OrderInvariant` / `PairwiseOrderInvariant` receipt of
any kind.  The only Φ-level commutation receipts
(`ConnectPhi.pairwiseOrderInvariant_attach`, `ConnectPhi.orderInvariant_attach`)
are stated for the older `attach` / `connectPhi` action, which the carrier
ledger above classifies PARTIAL-ONLY because the B4 witness lives inside it —
so metric work may not consume them.  Row 22.  *Everything below in G2, G3 and
G4 consumes this.*

**G1 — SUPERSEDED BY THE DRIFT REPAIR (2026-08-17).**  The gap is not a missing
receipt over `converterMonoidFullyBudgeted`; it is that the migrated primitive
is the wrong one.  MauRen16 §3.3's `αⁱ` is interface-indexed, the tree's is
whole-face application, and the ruled repair replaces the primitive rather than
adding a receipt on top of it.  **See `# DRIFT-REPAIR: attachment primitive
(whole-face → attachAt)` below** for the audited closure, the classified row
list, the six repair legs and the BLOCKING RULE.  G1 closes when leg (d) —
rows C9, C12, C20, C21 there — closes; the refuted relay design recorded in the
next paragraph is retained only as the record of why (row C22, class RETIRE).

**[RETIRED — record-of-why; G1 CLOSED by leg (d), see the leg-(d) closures
paragraph.  The witnesses below refute the RELAY design only; the delivered
ownership-dispatch design is immune by construction.]**

**G1 — DESIGN FINDING, 2026-08-17 (pen-and-paper, two explicit witnesses; not
machine-checked, and deliberately not implemented).**  *Historical: this is the
refuted `relayExcept` design, superseded by the drift-repair section below.*
The receipt needs an
interface-local attachment family — `relayExcept i E`, serving outer queries
in `i` through `E` and relaying every other outer query verbatim, with
`attachFullyAt i E := attachFully (relayExcept i E)` — and the obvious such
engine **does not commute**, on either of its two faces.

A relayed round has already issued its request when the completion's answer
`o : Option Uni` comes back, so it cannot refuse (that is the B4 pathology; it
would cost `InnerTotal` and with it `exists_absorb_connectFully`).  It must
therefore render `⊥` as a designated `botToken : Uni` — and *rendering on one
side only* is what breaks the equation.  At `i = {a}`, `j = {b}`, `a ≠ b`:

* *inner face.*  `E` requests `a` and answers `c₁` on `some _`, `c₀` on
  `none`; `s` refuses `a`.  Attached outermost, `E` is driven against
  `connectFully (relayExcept j F) s`, whose relay round at `a ∉ j` answers
  `botToken` and never refuses — `E` sees `some botToken` and the composite
  answers `c₁`.  Attached innermost, `E` queries `s` directly, sees `none`,
  and the composite answers `c₀`.
* *outer face.*  `E` refuses the outer query `a`.  Attached outermost the
  composite refuses (observable `⊥`, query deleted by CR18 Def 3.3); attached
  innermost that refusal is read by a relay round of `relayExcept j F` and
  rendered `botToken` — a defined answer, query kept.

Neither is repairable by a hypothesis on `E`, `F` and `botToken`: the first
turns on whether `s` refuses, and row 22 is an equation of *endomorphisms*, so
it must hold at every `s`.

**The repair, and the ruling it needs.**  The composite's `⊥` and the relayed
inner `⊥` must be *identified*: (1) the engine feeds `E` the rendered answer
`some (ρ o)`, `ρ (some v) = v`, `ρ none = botToken` — forced, because
transparency needs `ρ (some (ρ o)) = ρ o`, which no injective rendering
satisfies, so the identification is unavoidable and this is the smallest one;
and (2) *either* the engine is total on outer queries, answering `botToken`
where `E` refuses (unconditional commutation; `attachFullyAt i E` then never
refuses and its image lies in the total subcarrier), *or* refusals are kept
and row 22 carries the hypothesis that `E` and `F` never refuse an outer query
(a converter-class restriction, faithful to the paper, whose converters always
respond).  Under (1)+(2)-total the receipts are cheap: `InnerTotal` is free
(the engine is total), the budget is `max K 1` (relay rounds cost one request,
`E`'s rounds keep `E`'s bound), and membership in
`converterMonoidFullyBudgeted` needs only `AnswersWithinUniformBudget E`.
Both readings change what an attachment *is* on this carrier, so the family is
not defined until the ruling is made.  Full statement of the finding at the
closing section of `RandomSystems/System/ConnectFullyDefined.lean`.

**G2 — `𝓡* = 𝓡Σ` is not instantiated on any RandomSystems carrier.**
`Relaxation.star` fires only at an abstract `Φ`; the in-tree consumers
(`Multiparty/Basic.lean`'s `∗Z`, `Specification/Filtered.lean`,
`Applications/Sponge.lean`) are all themselves abstract.  This blocks eq. (1)
(row 26) and Lemma 3 (row 37) at the carrier.  Depends on G1 for
`constructs_star`'s commutation premise.

**G3 — Lemma 5, eq. (3) and `Indifferentiable` are not instantiated on any
RandomSystems carrier.**  `RandomSystemsReceipts.lean`'s closing FRONTIER
comment names this exactly and correctly.  Rows 39, 40, 42, 65.  Depends on
G2 (needs `star` at Φ) and G1.

**G4 — §3.4's `𝓡⟦`, right-outboundness and Lemma 4 are instantiated only on
the metric-free carrier RS-A.**  Nothing states `RightOutbound`,
`outboundCompatible` or `Constructs.outboundCompatible` at `Phi`, which is
where the metric lives.  Rows 28, 29, 30, 38.

**G5 — no single RandomSystems carrier carries the whole MR16 core.**  RS-A
has §3.3, §3.4, §7 and Lemma 4 but no `PseudoEMetricSpace`; RS-B has the
metric, Definition 2 and Lemmas 1–2 but none of §3.4's relaxations and no
commutation receipt.  The two carriers do not even agree on the distance —
RS-A's is `PDS.maxEDist`, RS-B's is the symmetrization of
`PDS.advFullyDefined`.  Until one carrier carries all of §§2–4, "the MR16
basics are instantiated" is true only of a union that no theorem ranges over.

**G6 — `Par Phi` is not registered**, so MR16 §2.1's `[𝓡₁,…,𝓡ₙ]` and §2.2's
context-insensitivity never reach the metric carrier, and the parallel half of
JM20 Corollary 1 stays unavailable.  `RandomSystems.par` and its laws
(`par_comm`, `par_assoc`) exist and are unconditional; the blocker is the
addressing ruling — `par` is indexed by a splitting `c : Set Uni`, and electing
one splitting to be *the* parallel composition is an arbitrary choice of
addressing.  Recorded at `MetricFullyDefined.lean` under "Deferred".  Rows 4, 6.

**G7 — MR16 §4.3 p. 13's explicit-simulation-resource rephrasing is missing.**
`πR = Sβ` with `β ∉ Σ` becomes `πR = [S, β̄]σ` for the trivial connecting
converter σ, hence `R —π→ ([S, β̄])*`, "which makes the computational resource
required for the simulation explicit".  No declaration anywhere.  Row 45.

**G8 — CLOSED (abstractly), 2026-08-17.**  `(𝓡ᵋ)* ⊆ (𝓡*)ᵋ`, the generic ε/∗
interchange MauRen16 uses unnumbered inside Theorem 2's proof (p. 18), is
`Relaxation.star_epsilonRelaxation_subset_epsilonRelaxation_star`.  The
matrix's prediction held: `IsNonexpandingSMul` alone is the hypothesis — `σ`
moves two points by at most their distance — with no commutation and no
property of `H`.  The reverse inclusion is deliberately not claimed (a point
within `ε` of `σr` need not be `σ` of anything).  Row 61 is `DA`, not `D+I`:
its carrier home waits on G2, which is what gives `star` a Φ-level meaning.

**G9 — the admitted-constructor set `Γ` has no possibility-direction
rendering.**  `Unconstructible` takes `Γ : Set Sigma`, but `Constructs`
quantifies over all of `Sigma`, so §2.1's "`Γ`, possibly restricted in terms of
efficiency or implementation cost" is unmodeled on the positive side.  §3.5's
models 2–4 (memory-bounded, connect-only, efficiently implementable) are
likewise unmodeled; only model 1 (information-theoretic) is instantiated.
Rows 2, 32.

**G10 — fn. 9's `d = sup_{D∈𝓓} Δ^D` has no MR16-track abstract home.**  The
class-indexed distance is `DistinguisherClass.edistD`, which sits behind the
provenance fence on MauRen11 Definition 15/16 provenance; the MR16 track
carries only the structural `PseudoEMetricSpace`.  By the rule at the head of
this section a fenced-only home is a gap.  Note this is *not* a defect of the
fence: MauRen16 itself defers the distinguisher class to one informal sentence
in §3.1, so what is owed is an MR16-track supremum object, not the lifting of
the fence.  Rows 13, 48.

**G11 — Definition 2's β-clause is unstated in the two-sided presentation.**
`Specification/Outbound.lean` is the only module where left and right
attachment are distinct monoids (`eL`, `eR`), and it imports no metric, so
`d(Rβ, Sβ) ≤ d(R, S)` cannot be stated there.  The homogeneous reading
subsumes the clause (see the verdict above); what is missing is the bridge
saying so.  Row 35.

**G12 — CLOSED, 2026-08-17.**  MR16 §4.2's remark `πRβ ≈ᵋ Sσβ` — the one place
the paper actually spends non-expansion in §4.2 — is now
`edist_mul_smul_le_of_edist_le` (`Metric/Nonexpansion.lean`), stated beside
Definition 2 whose β-clause it consumes, and instantiated at RS-B as
`edist_mul_smul_le_of_edist_le_fully`.  Right attachment is multiplication in
the one monoid (matrix row 35's verdict), so appending `β` to `πR` is the
action of `β * π` and `IsNonexpandingSMul` is the whole hypothesis; the
statement is no longer only inline inside `Relaxation.star_construct_eps` and
`Indifferentiable.trans`.  Row 41.

# PRIMITIVE REGISTRY (binding; briefs must name primitives from here)

  PARALLEL — R7'' RATIFIED & IMPLEMENTED (2026-08-18; commits cad5da1/
  0cb5055/fad28cb/b0a6265; home RandomSystems/System/ParFace.lean; C13''-
  validated, spike proofs transplanted).  NOT ADDRESSED by this entry (so
  no later leg re-plans from it): Par ↥converterMonoidAt (MauRen11 §6.2
  α∣β), SMulParClass Sigma Phi (the framing law at Φ — statement shape
  exists at the wrong carrier as System.attachEngine_par), HasFixedDomain
  transfer through parF.  Original candidate record:
    Φ UNCHANGED (PDS Uni Uni).  NO special alphabet: W/List Λ is one typed
    alphabet among all; no word carrier, no privileged face, no `encode W`
    design element, no Encodable embeddings, no chosen equivalence, no
    type-level tags — ALL STRUCK (drafts R7/R7' superseded).
    Design: face L := ⋃ s ∈ L.support, System.support s;
    parF L M := par (face L) L M; instance Par Φ := ⟨parF⟩;
    canonicity par_eq_parF_of_separating; parF_comm/parF_assoc on disjoint
    faces; self-composition via copy k R := blockSet {p | p.1 ≠ k}
    (relabel Prod.snd id R) — n definedness-disjoint copies inside ONE
    typed alphabet (value-level fibers); tuple [R₁,…,Rₙ] = parF-fold.
    THE C8 LESSON (binding trap): addressing must live at the VALUE level
    of a single type — type-level tags are unreadable (type-constructor
    injectivity neither provable nor refutable; spike C8, REFUTED).
    IsNonexpandingPar Φ unconditional: NOT obtainable (spike G6.f) — the
    conditional form is the deliverable.
    ESCALATION FILTER (binding, from the H1 incident): a fork may be put
    to Marc ONLY after checking this registry and the rulings — a fork the
    record already answers is applied, not asked; agent reports must cite
    the registry entry their RISK/DECISION items were checked against.
    H1 RECORD: parF's absorption off the disjoint regime is parF_absorb
    (a documented theorem, unreachable from the copy-based user surface) —
    NOT a fork; both proposed guard options were superseded by the copies
    mechanism already recorded above.
    Spike verdict record (2026-08-18, /private/tmp/r7prime/VERDICT.md):
    C1 CONFIRMED (parallel Fin-only, zero delta) · C3-C6 CONFIRMED
    (attach-at-fiber, RequestsWithin structural, disjointness, grouping) ·
    C7 refuted-as-claimed (ingredients verified, assembly owed) · C8
    REFUTED (type-tags) · C11 CORRECTED BY MARC: CR18 takes NO stance on
    addressing/output tagging (fn.2/§3.2.3 under-specify it) — the spike's
    "untagged-output fidelity delta" is formalization freedom, NOT a
    mismatch; MR16 §2.1-2.2 + Jost Def 2.2.1 govern addressing (R8).

  ATTACHMENT (current): `attachEngineFully i E` — direct ownership dispatch
    (q ∉ i: resource verbatim, refusal preserved; q ∈ i: engine round vs R⊥;
    engine class InnerTotal + uniform budget + RequestsWithin i).
    Status: legs (a) 637938d/c31b9e9/87fdde3, (b) 8e4eed4/9aaeba2/c17c2df,
      (c) cf9bf55/5a1c49e — DONE.  Leg (c) put the primitive at the Φ level
      as `RandomSystems.attachAt`, re-based the metric-facing Σ as
      `RandomSystems.converterMonoidAt` (and A6's weaker monoid as
      `converterMonoidAtWeakBudget`), and re-derived the S4 receipts over it.
      All leg-(a)/(b)/(c) rows closed; every declaration axiom-clean.
      Homes: `RandomSystems/System/AttachEngineFully.lean`,
      `RandomSystems/System/MetricFullyDefined.lean`.
      Leg (d) 8a796e6(d1, landed inside a concurrent lane's add -A commit)/
      0475135/b405e9e/c8166ac — DONE: G1 CLOSED — the commutation
      (αR)β = α(Rβ) and MR16 §7 grouping hold over converterMonoidAt, at
      the price of Disjoint + two RequestsWithin and NO engine class
      (commutation is an equation of partial values; a diverging round
      diverges on both sides).
      Legs (e)+(f) DONE (coordinator, 2026-08-17): demotion bridges had
      landed in legs (a)/(c) (`attachEngineFully_univ`, `attachAt_univ`,
      the two monoid containments); RETIRE rows C21/C22 + the CFD closing
      note marked retired-as-record; matrix re-score: row 22 D+I, G1
      closed, D+I tally 28 -> 29, PARTIAL 9 -> 8.
      DRIFT-REPAIR COMPLETE — all 86 non-UNAFFECTED rows closed.
  SUPERSEDED — never the primitive again:
    `attachFully` / `converterMonoidFully` / `converterMonoidFullyBudgeted`
      (whole-face Φ level) -> superseded by `attachAt` /
      `converterMonoidAtWeakBudget` / `converterMonoidAt` (leg c); NOT
      deleted; containments: `converterMonoidFullyBudgeted_le_converterMonoidAt`,
      `converterMonoidFully_le_converterMonoidAtWeakBudget`, both riding
      `attachAt_univ : attachAt Set.univ E = attachFully E`.
    `connectFully` (whole-face, CR18 Def 3.9) -> becomes attachEngineFully univ
      via the leg-(e) bridge; until then RE-BASE rows only.
    `connect (liftAt i E)` (old carrier) -> PARTIAL-ONLY; proof TEMPLATES only
      (statement shapes, commutation invariant); the wrapper-engine MECHANISM
      is retired.
    `relayExcept`/`attachFullyAt`/`botToken` -> REFUTED design, never landed;
      tripwired in scripts/ledgerAudit.sh check 3.
  KEPT vs NOT-KEPT (the ruling): statements + proof architecture + engine-class
  predicates are reused; the relay mechanism is not.

**MATRIX CENSUS (2026-08-18, counted from the cells after the audited
rescore; supersedes every earlier tally line, several of which were stale —
including one applied by a commit whose message claimed more than its diff
did (23b0cd2), caught by the final audit):**
43 D+I · 0 DA · 3 PARTIAL · 0 MISSING · 1 FENCE-ONLY · 1 PROSE  (of 48).
**BASICS-DONE VERDICT: YES (2026-08-18, row 2 landed d6f07c3)** — with the
residue stated: rows 13/48 (gap G10 — fn. 9's class-indexed supremum;
MauRen16 itself defers the distinguisher class to one informal sentence;
fenced by design, not omission), row 32 (§3.5 models 2-4 — after d6f07c3 a
modeling CHOICE, not a missing mechanism: Γ is a parameter with carrier
entry points on both sides), row 31 (PROSE — a modeling principle by
nature).  Census counted from the cells: 44 D+I · 2 PARTIAL · 1 FENCE-ONLY · 1 PROSE of 48.

**GAP STATUS CONSOLIDATION (authoritative; older gap paragraphs are
historical record):** G1 CLOSED (leg d) · G2/G3/G4 CLOSED at the carrier
(#77) · G5 CLOSED for the generic core · G6 CLOSED (R7'' + G-6 leg:
instParPhi, instParConverterMonoidAt with the fn.23 ruling audit-verified
TWO-SIDED — attachAt_mul_parF compiles in the paper display's exact shape;
the two abstract classes SMulParClass/IsNonexpandingPar are uninstantiable
BY SHAPE, conditional theorems in the classes' own shapes are the
endpoints, constructs_parF_left/constructs_parF/
constructs_epsilonRelaxation_parF the usable class-free forms; honest note:
α∣α = α² at the converter Par, the twin of parF_self, recorded not hidden)
· G7 CLOSED (abstract + carrier) · G8 CLOSED (abstract + carrier) · G9 CLOSED (abstract + carrier, d6f07c3: both Γ-readings at RS-B; models 2-4 = row 32, a choice not a gap) · G12 CLOSED.  CORRECTION
to the earlier AUDIT RECORD: `Par ↥converterMonoidAt` IS now synthesizable
(410bf05); C5's conclusion stood only via SMulParClass, and C5 is now
closed by the class-free forms.

# DRIFT-REPAIR: attachment primitive (whole-face → attachEngineFully)

**The drift.**  MauRen16 §3.3's primitive is the *interface-indexed* attachment
`αⁱ : Φ → Φ`; the tree's migrated primitive is *whole-face* application —
`System.connectFully E R := DDC.apply (DDC.ofEngine E) R`, CR18 Def 3.9 through
`DDC.apply` — adopted at A6 by expedience, with every Φ-level object above it
(`attachFully`, `converterMonoidFully(Budgeted)`, the S4 receipts) inheriting
the whole face.  The relay design that was to recover `αⁱ` from it
(`relayExcept i E`, `attachFullyAt i E := attachFully (relayExcept i E)`) is
REFUTED on both faces (LEDGER G1; `ConnectFullyDefined.lean` closing section).

**The repair (ruled).**  A first-class `attachAt i E` by *ownership dispatch*:
a query outside `i` reaches the resource verbatim — its partiality, its
refusals and CR18 Def 3.3 deletion untouched, so nothing is ever *rendered* —
while a query in `i` runs the converter rounds with the engine's requests
confined to `i`.  Whole-face application is demoted to the special case
`i = univ`.  This section is the audited row list the repair executes against;
it does not build anything.

**M1 evidence note (from disk, not memory).**  MR16's αⁱ is already in the tree
one carrier down: `System.attachEngine i E R = connect (liftAt i E) R`
(`RandomSystems/System/Connect.lean:694`) is exactly ownership dispatch —
`liftAtRaw`'s foreign branch relays a non-`i` query down verbatim — and its
commutation `System.attachEngine_comm` (`Connect.lean:1573`, aux at 1327) is
PROVEN, lifted to `Converter.attachEngineAt_actCommute` /
`pairwiseOrderInvariant_attachEngineAt` (`Converter/Sigma.lean:151-179`).  It
is unusable only because it rides `connect`, which the B4 witness refutes.  So
leg (a) is a *migration* of `attachEngine` onto the completion, and leg (d) has
a proof template rather than a blank page.  Two genres meet in one definition:
the non-`i` face is the relay genre (one inner query per outer query, refusal
preserved, `exists_absorb_relay` applies), the `i` face is the engine genre
(`InnerTotal` + budget against `R⊥`).  That split is what makes both G1
witnesses evaporate — the non-`i` face never renders `⊥`, it *is* the
resource's `⊥`.

**Naming.**  `attachAt` is already taken twice, both in `Converter`
(`Converter.attachAt`, CR18 Def 3.13 memoryless, `Converter.lean:1920`;
`Converter.General.attachAt`, `Converter.lean:2149`), and `General.attachAtLaw`
is a carrier-ledger row, so the primitive took the registry name
`System.attachEngineFully` instead and the collision does not arise.

**Leg (a) closures (2026-08-17):** A12 `87fdde3` (`attachEngineFully_univ`);
A13 `637938d`+`87fdde3` (`ReachedAt`, univ instance via the bridge);
A14 `637938d` (`reachedAt_nil`); A15 `637938d` (`ReachedAt.unique`);
A16 `637938d` (`mem_attachEngineFullyDrive_concat`); A17 `c31b9e9`
(`attachEngineFully_concat_round` + `mem_dom_…_concat_{mem,not_mem}`);
A18 `c31b9e9` (`output_…_concat_{mem,not_mem}`); A19 `637938d`
(`attachEngineFully_reached_concat{,_not_mem,_mem}`); A27 `c31b9e9`
(`attachEngineFully_refusal_first` + `attachEngineFully_transparent`);
A28 `87fdde3` (`mem_dom_…_of_nil_{mem,not_mem}`); A29 `87fdde3`
(`mem_dom_…_of_nil_congr`).

**Leg (b) closures (2026-08-17):** A42 `8e4eed4` (`attachEngineFullyReplayStep`);
A43 `8e4eed4` (`attachEngineFullyNeed`); A44 `8e4eed4`
(`attachEngineFullyReplayStep_stop`); A45 `8e4eed4`
(`attachEngineFullyReplayStep_refuse` at the owned face +
`attachEngineFullyReplayStep_foreign`, the branch the dispatch splits off);
A46 `8e4eed4` (`attachEngineFullyReplayStep_round`); A47 `8e4eed4`
(`attachEngineFullyReplayStep_stall` + `attachEngineFullyReplayStep_foreign_stall`);
A48 `8e4eed4` (`attachEngineFullyNeed_round` + `attachEngineFullyNeed_foreign`);
A49 `8e4eed4` (`attachEngineFullyReplay`); A50 `8e4eed4`
(`attachEngineFullyReplay_zero`); A51 `8e4eed4` (`attachEngineFullyReplay_succ`);
A52 `8e4eed4` (`attachEngineFullyReplay_of_fixed`); A53 `8e4eed4`
(`absorbAttachEngineFully`); A54 `8e4eed4` (`answer_attachEngineFully_refuse` +
`answer_attachEngineFully_foreign`, the outside-`i` passthrough the row owed);
A55 `8e4eed4` (`answer_attachEngineFully_round`); A59 `8e4eed4`
(`attachEngineFullyReplay_invariant`); A60 `9aaeba2`
(`exists_absorb_attachEngineFully`).  All 16 leg-(b) rows closed; every
declaration axiom-clean.  A36–A41 and A56 were reused verbatim as the audit
certified — the inner induction `exists_roundReplay_absorb` applied at the
environment's own resource history and needed nothing.

**Leg (b) additions beyond the row list.**  Four bridging theorems the row list
does not name: the composite's resource history and an absorbing environment's
differ by exactly the foreign queries the resource refuses — the composite's
round is undefined there, so the query never enters its history, while the
environment must ask to learn the refusal.  CR18 Definition 3.3 deletes
precisely those, so the two agree up to `keptPrefix`, and that is the
invariant's new clause.  `mem_connStep_iff` (one connection step characterized)
and `exists_mem_resolve_of_keptPrefix_eq` ("a deleted query is invisible to a
round", by `PFun.fix_bisim`) say a round cannot tell the two histories apart;
`keptPrefix_append_congr` and `answer_congr_keptPrefix` say neither can the
completion.  This is what kept `exists_roundReplay_absorb` verbatim.  All four
are DDC-general and belong with the round equations in ConnectFullyDefined;
they live in AttachEngineFully.lean because leg (b) is their only consumer.

**Leg (b) extra deliverable.**  `attachEngineFully_mem_nonexpandingConverters`
(`c17c2df`): the metric consequence of A60 through
`PDS.advFullyDefined_fTransform_le`, stated at the raw pushforward so leg (c)
may name the Σ generator as it pleases; does NOT close A68 (a leg-(c) row).
`RequestsWithin` deliberately not a hypothesis — absorption is indifferent to
where requests point; the clause stays owed by leg (d)'s commutation.

**Leg (c) closures (2026-08-17):** A61 `cf9bf55` (`attachAt` + `attachAt_univ`);
A62–A67 `cf9bf55` (`converterMonoidAtWeakBudget` + its four memberships + unit
examples); A68 `cf9bf55` (`attachAt_mem_nonexpandingConverters`); A69–A73
`cf9bf55` (`converterMonoidAt` + its four memberships); A74 `cf9bf55`
(`converterMonoidAt_le_converterMonoidAtWeakBudget`); A75 `cf9bf55`
(`converterMonoidAt_le_nonexpandingConverters`); B8–B11 `5a1c49e` (derived
IsNonexpandingSMul instance, `edist_apply_le_of_mem_converterMonoidAt`,
`edist_mul_smul_le_of_edist_le_at`, `constructs_epsilonRelaxation_trans_at`);
B12 `5a1c49e` (MFD Scope paragraph); C19 (RS-B bullet, this commit).  All 21
leg-(c) rows closed.  Bridges beyond the rows: `attachAt_univ`,
`converterMonoidFullyBudgeted_le_converterMonoidAt`,
`converterMonoidFully_le_converterMonoidAtWeakBudget`.  Leg (f) re-points
C4/C14/C16/C30/C34 to `converterMonoidAt` and C3 to `attachAt`.

**Leg (d) closures (2026-08-17):** C9, C12, C20, C21 — `8a796e6`(d1)/`0475135`/
`b405e9e`/`c8166ac`.  Endpoints: `exists_mem_resolve_of_requestsWithin` +
`resolve_requests_within` + `mem_ofEngine_in_iff` (d1); frontier converses +
`answer_attachEngineFully_congr` + `exists_reachedAt_attachEngineFully_concat`
+ the round transfers (d2a); `attachEngineFully_comm_aux` +
`attachEngineFully_comm` (d2b); `attachAt_comm`, `attachAt_actCommute`,
`pairwiseOrderInvariant_attachAt`, `orderInvariant_attachAt`,
`attachedWithin_attachAt_le_converterMonoidAt` (d3).  All axiom-clean.  The
template `attachEngine_comm` transferred as architecture; new content = the
kept-prefix cross-identification of the two bottom histories and the
inner-face confinement lemma tagAt gave the old carrier for free.
**G1 — CLOSED (leg d).**  Commutation holds for the metric-facing Σ with NO
engine class (Disjoint + two RequestsWithin only); grouping discharged over
an abstract index ι with pairwise-disjoint w : ι → Set Uni and
protocol-valued converters (`ProtocolWithin`); the grouped converters are
INSIDE converterMonoidAt (`attachedWithin_attachAt_le_converterMonoidAt`).
Matrix rows 17/22 read D+I as of this closure; the fine-grained cell
re-pointing and tally re-read are leg (f)'s (row C18).  Consequential:
row 37 gap list drops G1; G2/G3 depend on G2's own star work only.

## Classified closure

File keys: **CFD** = `RandomSystems/System/ConnectFullyDefined.lean`,
**MFD** = `RandomSystems/System/MetricFullyDefined.lean`,
**ABS** = `RandomSystems/System/Absorb.lean`, **LED** = `LEDGER.md`,
**PHI** = `PHI-SPEC.md`, **THv2** = `THEORY-v2.md`.

Classes: **U** = UNAFFECTED, **RB** = RE-BASE, **DM** = DEMOTE (kept as
`i = univ` behind a bridging lemma), **RT** = RETIRE.  Legs are M3's, below.

### A — `ConnectFullyDefined.lean` (all 75 declarations; superset of the closure)

| # | name | file | class | leg | reason |
|---|---|---|---|---|---|
| A1 | `unlabel` | CFD | U | — | label stripping on `CIn`; no attachment |
| A2 | `unlabel_query` | CFD | U | — | `simp` equation for A1 |
| A3 | `unlabel_answer` | CFD | U | — | `simp` equation for A1 |
| A4 | `ofEngine` | CFD | U | — | engine → CR18 Def 3.8 converter; reused verbatim by `attachAt`'s `i`-rounds |
| A5 | `mem_dom_ofEngine` | CFD | U | — | domain of A4 |
| A6 | `output_ofEngine` | CFD | U | — | output of A4 |
| A7 | `mem_ofEngine_of_mem` | CFD | U | — | membership transport through A4 |
| A8 | `mem_ofEngine_out` | CFD | U | — | outer-answer case of A7 |
| A9 | `mem_ofEngine_in` | CFD | U | — | request case of A7 |
| A10 | `exists_move_ofEngine` | CFD | U | — | the answer/request dichotomy; per-round, attachment-agnostic |
| A11 | `mem_driveFrom_singleton` | CFD | U | — | one-query fold = one resolution; about `driveFrom`, not the face |
| A12 | `connectFully` | CFD | DM | a | *the* whole-face primitive; becomes `attachAt univ` with a bridging equation |
| A13 | `ReachedState` | CFD | DM | a | folds **every** outer query through the engine; `attachAt` needs an `i`-aware state |
| A14 | `reachedState_nil` | CFD | DM | a | base case of A13 |
| A15 | `ReachedState.unique` | CFD | DM | a | determinism of A13 |
| A16 | `mem_driveFrom_concat` | CFD | DM | a | frontier step of the whole-face fold |
| A17 | `mem_dom_connectFully_concat` | CFD | DM | a | frontier domain receipt, stated at `connectFully` |
| A18 | `output_connectFully_concat` | CFD | DM | a | frontier output receipt, stated at `connectFully` |
| A19 | `reachedState_concat` | CFD | DM | a | frontier state receipt, stated at the whole-face fold |
| A20 | `mem_resolve_of_answer` | CFD | U | — | CR18 Def 3.9 output rule at `resolve`; no attachment |
| A21 | `resolve_of_request` | CFD | U | — | CR18 Def 3.9 query rule at `resolve`; no attachment |
| A22 | `mem_dom_of_resolve_dom` | CFD | U | — | a resolved round certifies the engine's move; about `resolve` |
| A23 | `InnerTotal` | CFD | U† | — | predicate on the **engine alone**; survives verbatim as `attachAt`'s `i`-round class |
| A24 | `AnswersWithinBudget` | CFD | U† | — | predicate on the engine alone; unchanged |
| A25 | `AnswersWithinUniformBudget` | CFD | U† | — | predicate on the engine alone; unchanged |
| A26 | `resolve_dom_of_mem_dom` | CFD | U | — | "a started round ends", about `resolve`; mentions A23/A24 but is face-agnostic |
| A27 | `connectFully_refusal_first` | CFD | DM | a | stated at `dom (connectFully E R)`; `attachAt` needs it at `i`-queries plus a passthrough clause |
| A28 | `mem_dom_connectFully_of_nil` | CFD | DM | a | first-query corollary of A27 |
| A29 | `mem_dom_connectFully_of_nil_congr` | CFD | DM | a | the B4 criterion at the frontier, whole-face |
| A30 | `idEngineFully` | CFD | DM | e | the whole-face relay identity |
| A31 | `innerTotal_idEngineFully` | CFD | DM | e | A23 at A30 |
| A32 | `answersWithinBudget_idEngineFully` | CFD | DM | e | A24 at A30 |
| A33 | `mem_resolve_idEngineFully` | CFD | DM | e | one relay round of A30 |
| A34 | `exists_reachedState_idEngineFully` | CFD | DM | e | A13 at A30 |
| A35 | `connectFully_idEngineFully` | CFD | DM | e | `= R⊥`; under `attachAt` the unit is `attachAt ∅`, so this is the `i = univ` case |
| A36 | `move` | CFD | U | — | engine move as a total function; general infrastructure |
| A37 | `move_eq_some_iff` | CFD | U | — | characterization of A36 |
| A38 | `roundReplay` | CFD | U | — | replays **one engine round** from the converter history; that round is unchanged at `i` |
| A39 | `roundReplay_answer` | CFD | U | — | equation of A38 |
| A40 | `roundReplay_stuck` | CFD | U | — | equation of A38 |
| A41 | `roundReplay_request` | CFD | U | — | equation of A38 |
| A42 | `fullyReplayStep` | CFD | RB | b | routes **every** outer move into the engine; this is where the `i`-dispatch must go |
| A43 | `fullyNeed` | CFD | RB | b | same dispatch: outside `i` the needed inner query is the outer query itself |
| A44 | `fullyReplayStep_stop` | CFD | RB | b | equation of A42 |
| A45 | `fullyReplayStep_refuse` | CFD | RB | b | equation of A42; the refusal branch splits by `i` |
| A46 | `fullyReplayStep_round` | CFD | RB | b | equation of A42 |
| A47 | `fullyReplayStep_stall` | CFD | RB | b | equation of A42 |
| A48 | `fullyNeed_round` | CFD | RB | b | equation of A43 |
| A49 | `fullyReplay` | CFD | RB | b | iterate of A42 |
| A50 | `fullyReplay_zero` | CFD | RB | b | equation of A49 |
| A51 | `fullyReplay_succ` | CFD | RB | b | equation of A49 |
| A52 | `fullyReplay_of_fixed` | CFD | RB | b | stability of A49; content generic, statement names A42/A49 |
| A53 | `absorbFully` | CFD | RB | b | the absorbed environment, built from A43/A49 |
| A54 | `answer_connectFully_refuse` | CFD | RB | b | `answer (connectFully E R)`; needs the new outside-`i` passthrough branch |
| A55 | `answer_connectFully_round` | CFD | RB | b | `answer (connectFully E R)` at an accepted query |
| A56 | `exists_roundReplay_absorb` | CFD | U | — | the inner induction; parametric in the environment, names no attachment — **reusable verbatim** |
| A57 | `answeredQueries_concat_some` | CFD | U | — | list lemma on `answeredQueries` |
| A58 | `answeredQueries_concat_none` | CFD | U | — | list lemma on `answeredQueries` |
| A59 | `fullyReplay_invariant` | CFD | RB | b | the outer invariant; names `connectFully` + A13 + A53, and carries the dispatch |
| A60 | `exists_absorb_connectFully` | CFD | RB | b | the keystone absorption receipt, whole-face |
| A61 | `attachFully` | CFD | RB | c | the Σ generator; becomes `attachAt i`, with `attachFully = attachAt univ` as the demotion bridge |
| A62 | `converterMonoidFully` | CFD | RB | c | generator family built from A61 |
| A63 | `attachFully_mem_converterMonoidFully` | CFD | RB | c | membership over A62 |
| A64 | `block_mem_converterMonoidFully` | CFD | RB | c | membership over A62 (generator itself unchanged) |
| A65 | `parRight_mem_converterMonoidFully` | CFD | RB | c | membership over A62 |
| A66 | `parLeft_mem_converterMonoidFully` | CFD | RB | c | membership over A62 |
| A67 | `example : 1 ∈ converterMonoidFully` | CFD | RB | c | unit witness over A62 |
| A68 | `attachFully_mem_nonexpandingConverters` | CFD | RB | c | nonexpansion of the whole-face attachment; must be proved for `attachAt i` |
| A69 | `converterMonoidFullyBudgeted` | CFD | RB | c | **the metric-facing Σ**; its attachment family is the drift |
| A70 | `attachFully_mem_converterMonoidFullyBudgeted` | CFD | RB | c | membership over A69 |
| A71 | `block_mem_converterMonoidFullyBudgeted` | CFD | RB | c | membership over A69 |
| A72 | `parRight_mem_converterMonoidFullyBudgeted` | CFD | RB | c | membership over A69 |
| A73 | `parLeft_mem_converterMonoidFullyBudgeted` | CFD | RB | c | membership over A69 |
| A74 | `converterMonoidFullyBudgeted_le_converterMonoidFully` | CFD | RB | c | the budget delta, over A62/A69 |
| A75 | `converterMonoidFullyBudgeted_le_nonexpandingConverters` | CFD | RB | c | the closure step; its attachment generator is A68 |

† **U†** = UNAFFECTED-with-note; see the InnerTotal/budget verdict below.

### B — `MetricFullyDefined.lean` and `Absorb.lean`

| # | name | file | class | leg | reason |
|---|---|---|---|---|---|
| B1 | `instance : PseudoEMetricSpace Phi` | MFD | U | — | `Adv⊥` symmetrization; no converter appears |
| B2 | `edist_def` | MFD | U | — | definitional unfolding of B1 |
| B3 | `edist_eq_advFullyDefined_of_weight_eq` | MFD | U | — | equal-weight collapse of B1 |
| B4 | `nonexpandingConverters_le_nonexpandingEnd` | MFD | U | — | about `nonexpandingConverters`, defined by absorption, not by attachment |
| B5 | `edist_apply_le_of_mem_nonexpandingConverters` | MFD | U | — | Def 2 at the *specification* family |
| B6 | `instance IsNonexpandingSMul nonexpandingConverters Phi` | MFD | U | — | at the specification family |
| B7 | `constructs_epsilonRelaxation_trans_phi` | MFD | U | — | at the specification family |
| B8 | `instance IsNonexpandingSMul converterMonoidFullyBudgeted Phi` | MFD | RB | c | indexed by A69 |
| B9 | `edist_apply_le_of_mem_converterMonoidFullyBudgeted` | MFD | RB | c | MR16 Def 2 over A69 (matrix row 35's RS-B home) |
| B10 | `edist_mul_smul_le_of_edist_le_fully` | MFD | RB | c | **G12's RS endpoint**, over A69 |
| B11 | `constructs_epsilonRelaxation_trans_fully` | MFD | RB | c | JM20 Cor 1.1 over A69 |
| B12 | module docstring §Scope (l. 36–46) | MFD | RB | c | names `attachFully` / both `Fully` monoids as the scope of the receipts |
| B13 | `exists_absorb_relay` docstring, l. 310 | ABS | RB | f | "Engines … need their own machinery (`exists_absorb_connectFully`)" — pointer |

### C — non-code sites

| # | site | file | class | leg | reason |
|---|---|---|---|---|---|
| C1 | carrier row `connectFully (A6)` | LED | DM | e | the whole-face receipt row; restated as the `i = univ` case |
| C2 | carrier row `idEngineFully` | LED | DM | e | the whole-face identity row |
| C3 | carrier row `attachFully` | LED | RB | f | the Σ generator row |
| C4 | carrier row `converterMonoidFullyBudgeted` | LED | RB | f | the metric-facing Σ row |
| C5 | carrier row `converterMonoidFully` | LED | RB | f | the documented-delta row |
| C6 | carrier row `attach, block (Φ), … General.attachAtLaw` | LED | RB | f | says "the re-based Σ is `converterMonoidFully`"; also the `attachAt` name collision |
| C7 | METRIC §"B4-RESUME additions" ¶ | LED | RB | f | lists A36–A53 as one block; A36/A38 stay, A42–A53 re-base |
| C8 | PRIMITIVE §"A6 additions" ¶ | LED | DM | e | `ReachedState` demotes; `InnerTotal`/`AnswersWithin*` keep their rows verbatim |
| C9 | matrix row 17 (§3.3 `Σ`, `αⁱ`) | LED | RB | d | **the headline**: the row claims `αⁱ` `D+I` while its RS-B home is whole-face |
| C10 | matrix row 19 (§3.3 `id ∈ Σ`) | LED | DM | e | cites `idEngineFully`, `connectFully_idEngineFully` |
| C11 | matrix row 20 (§3.3 `Σ∘Σ = Σ`) | LED | RB | f | cites both `Fully` monoids |
| C12 | matrix row 22 (§3.3 commutation, G1) | LED | RB | d | the root gap; "no receipt at all for `attachFully` / `converterMonoidFullyBudgeted`" |
| C13 | matrix row 27 (§3.4 blocking `⊣`) | LED | RB | f | cites `block_mem_converterMonoidFullyBudgeted` |
| C14 | matrix row 35 (Def 2, both clauses) | LED | RB | f | cites `edist_apply_le_of_mem_converterMonoidFullyBudgeted` |
| C15 | matrix row 36 (Lemma 2) | LED | RB | f | cites `constructs_epsilonRelaxation_trans_phi` / `_fully` |
| C16 | matrix row 41 (§4.2 remark, G12) | LED | RB | f | cites `edist_mul_smul_le_of_edist_le_fully` at A69 |
| C17 | matrix row 44 (§4.3 absorption) | LED | RB | f | cites `exists_absorb_connectFully` |
| C18 | matrix tally (28 `D+I` of 48) | LED | RB | f | the count the BLOCKING RULE below suspends |
| C19 | "The two RandomSystems carriers", RS-B bullet | LED | RB | c | defines RS-B's `Σ` as A69 |
| C20 | "Definition 2, the β-side — verdict" ¶ | LED | RB | d | its premise is "a tag-addressed `attachFully` at RS-B" — exactly what `attachAt` supplies and whole-face does not |
| C21 | G1 gap ¶1 (the gap statement) | LED | RB | d | restated against `attachAt`; the receipt owed is unchanged |
| C22 | G1 "DESIGN FINDING" block (relay witnesses + `botToken` repair) | LED | RT | f | the refuted relay design; becomes the record-of-why, marked closed by supersession |
| C23 | G2 / G3 / G4 "depends on G1" lines | LED | U | — | pointer only; verified none of rows 25/26/28/29/30/37/38/39/40/42/65 names the drifted family |
| C24 | closing §"Interface-local attachment … (G1)", l. 1270–1332 | CFD | RT | f | the refutation note; **no `.lean` edit in this audit** — the repair retires it |
| C25 | B4 ladder row (l. 335–344) | PHI | RB | f | "the migrated generator is `System.connectFully`" |
| C26 | B5 ladder row (l. 357–364) | PHI | RB | f | the `converterMonoidFully(Budgeted)` closure record |
| C27 | B7 ladder row (l. 397–402) | PHI | RB | f | unscoping record over A69 |
| C28 | A6 audit + M1–M4 (l. 551–656) | PHI | DM | e | the whole-face design record; restated as the `i = univ` case |
| C29 | B4-RESUME M1–M3 (l. 657–725) | PHI | RB | f | the absorption record, whole-face |
| C30 | "THE METRIC-FACING Σ" (l. 780–792) | PHI | RB | f | defines Σ as A69 |
| C31 | GAP CLOSURES, G12 ¶ (l. 920) | PHI | RB | f | cites `edist_mul_smul_le_of_edist_le_fully` over A69 |
| C32 | GAP CLOSURES, G1 ¶ (l. 924–941) | PHI | RT | f | the `relayExcept`/`botToken` refutation prose; superseded |
| C33 | narrative l. 444 ("THAT IS EXACTLY WHAT HAPPENED") | PHI | U | — | B4-history prose; no name from the family |
| C34 | Σ line (l. 114–115) | THv2 | RB | f | "Σ: converterMonoidFullyBudgeted (InnerTotal + uniform Def 3.8 budget)" |

**Tally.**  122 rows — 87 code (75 CFD + 12 MFD/ABS incl. two docstring sites),
35 non-code.  **UNAFFECTED 36** (3 of them U†), **RE-BASE 61**, **DEMOTE 22**,
**RETIRE 3**.  86 rows are non-UNAFFECTED and each is assigned exactly one leg.

**Self-check.**  The grep that produced the closure —
`connectFully`, `attachFully`, `attachFullyAt`, `converterMonoidFullyBudgeted`,
`relayExcept`, `idEngineFully`, `exists_absorb_connectFully`, `InnerTotal`,
`AnswersWithinBudget`, `AnswersWithinUniformBudget`, `botToken`, word-matched
over every non-`.lake` `.lean` and `.md` file — was re-run against the finished
table.  It reaches exactly three `.lean` files (CFD, MFD, ABS) and four
documents (LED, PHI, THv2, and CFD's own note), all present above; block A
lists the whole of CFD, so no CFD declaration can be missing.  `relayExcept`,
`attachFullyAt` and `botToken` occur in **no** `.lean` code — only in prose
(C22, C24, C32), which is why they are RETIRE and not RE-BASE.

## The InnerTotal / budget verdict — SURVIVE, do not demote

`InnerTotal E`, `AnswersWithinBudget E β` and `AnswersWithinUniformBudget E`
are read off their statements as predicates on the **engine alone**: each
quantifies over engine histories `l : List (U ⊕ Option Y)` and the engine's
own `E.1`, and none mentions `connectFully`, a resource, a face or an interface
set.  What they say — "once the engine has requested, it is defined at that
history extended by any completion answer", and "a well-founded, uniformly
bounded count of consecutive requests" — is exactly the class condition
`attachAt`'s `i`-rounds need, because an `i`-round *is* the same engine round.
So they are UNAFFECTED-with-note, not DEMOTE.  Two notes, both leg (a):

1. a **new, separate** engine-side clause is owed, `RequestsWithin i E` (the
   engine's requests carry addresses in `i`); it is not a weakening or
   strengthening of the three, it is orthogonal to them, and nothing in the
   tree states it;
2. the budget's *arithmetic* role changes, not its statement: `m := n * K` in
   `exists_absorb_connectFully` becomes a mixed count — an `i`-round still
   costs at most `K` inner queries, a non-`i` query costs exactly one — so the
   re-based receipt carries `m := n * max K 1`.  `AnswersWithinUniformBudget`
   itself is untouched.

Their carrier-ledger PRIMITIVE rows therefore stay verbatim (C8).

## M3 — repair legs

Dependency-ordered; each non-UNAFFECTED row appears in exactly one leg.

**(a) `attachAt` definition + `i`-aware round receipts** — 11 rows: A12–A19,
A27–A29.  Define `System.attachAt (i) (E) (R)` by ownership dispatch, the
`i`-aware reached state, the frontier trio, refusal-first at `i`-queries, the
verbatim-passthrough clause outside `i` (**new**, no current analogue), and
`RequestsWithin i E` (**new**).  Close with the bridge
`attachAt univ E R = connectFully E R`, which is what makes leg (e) cheap.
Template: `System.attachEngine` / `liftAtRaw` on the completion instead of
`connect`.

**(b) absorption re-base** — 16 rows: A42–A55, A59, A60.  DONE (`8e4eed4`,
`9aaeba2`, `c17c2df`).  The `i`-dispatch entered at `attachEngineFullyReplayStep`
/ `attachEngineFullyNeed`; the outer invariant carries it, together with the
mixed-history clause the dispatch forces; the receipt re-emerged as
`exists_absorb_attachEngineFully` at the mixed count `m := n * max K 1`.
A36–A41 and A56 were reused verbatim, the inner induction
`exists_roundReplay_absorb` included.

**(c) Σ re-base + S4 receipts** — 21 rows: A61–A75, B8–B12, C19.  `attachAt i`
replaces `attachFully` as the Σ generator; the budgeted monoid, the membership
lemmas, `attachFully_mem_nonexpandingConverters`, the `IsNonexpandingSMul`
instance and the three MFD endpoints re-state over it.  Consumes (b).

**(d) G1 commutation via the par-crux genre** — 4 rows: C9, C12, C20, C21.
`attachAt i E ∘ attachAt j F = attachAt j F ∘ attachAt i E` for disjoint
`i`, `j`, then `PairwiseOrderInvariant` / `OrderInvariant` at
`attachedWithin`.  Template: `attachEngine_comm` (`Connect.lean:1573`) and
`pairwiseOrderInvariant_attachEngineAt`.  Consumes (a); does **not** consume
(b) or (c) — commutation is a carrier equation.

**(e) whole-face demotion bridge** — 11 rows: A30–A35, C1, C2, C8, C10, C28.
`idEngineFully` and its receipts become the `i = univ` instance; state whether
the migrated unit is now `attachAt ∅ = id` rather than `R ↦ R⊥` (the dispatch
makes it plausible — decide it, do not assume it).  Consumes (a).

**(f) matrix reconciliation + retirement** — 23 rows: B13, C3–C7, C11,
C13–C18, C22, C24–C27, C29–C32, C34.  Re-point every citation, retire the three
RETIRE sites as record-of-why, re-tally the matrix.  Consumes (c), (d), (e).

**BLOCKING RULE (binding).**  The MR16 matrix's "basics are done" claim is
blocked until every RE-BASE, DEMOTE and RETIRE row in this section is closed;
rows close only by commit references.  In particular matrix rows 17, 19, 20,
22, 27, 35, 36, 41 and 44 may not be read as `D+I` for the interface-indexed
`αⁱ` while their RS-B home is whole-face application.

# LANZENBERGER OBLIGATION MATRIX + quarry-reuse map

**SCOPE NOTE (CR18 sweep F-5, 2026-08-18): this matrix enumerates thesis
CHAPTER 2 ONLY.  Chapter 3 (Theory of Amplification, printed pp. 43-84 —
hardness amplification for games §3.3 and predicates §3.5) is UNMAPPED and
is a PRIMARY source for the ground CR18 §4.9 / half of §4.4 covers: the
stretch items S-04/S-12/S-13 must be recast from Lanz Ch. 3, not built
from CR18.  A Ch. 3 matrix extension is owed when amplification opens.**

**LANE RULES (binding for every Lanzenberger-lane brief; Marc, 2026-08-17).**

TERMINOLOGY (Marc, 2026-08-18): the read-only source tree at
../random-systems is called THE REFERENCE REPOSITORY (older text says
"quarry" — same object; Q: pointers abbreviate it).

REUSE RULE.  Existing RS work is reused WHENEVER POSSIBLE, in this order:
  (1) current-tree declarations as-is; (2) quarry proof ARCHITECTURE
  (invariants, induction shapes, case splits — transplanted, cited by
  file:line); (3) quarry statement shapes (restated on the current carrier,
  never copied).  Building fresh what the quarry already proves is a
  brief violation; the matrix's quarry column is the authority on what
  exists.  The quarry is READ-ONLY, always.

TRANSPLANT RULES (from the audit's nine pin-contradictions):
  - Quarry `Δ(S, T)` notation means `maxAdvantage`, NOT `classDistance` —
    verbatim copying silently changes theorems.  Restate everything.
  - `maxAdvantage` / `maxEDist` are FORBIDDEN statement targets (pin 2);
    quarry results stated against them are re-targeted to
    `advFullyDefined`/`classDistance` or not transplanted.
  - `adv_eq_maxAdvantage_swap`: the argument order SWAPS — the naive
    pairing is documented refutable.
  - Thm 2.31 forms carry the finiteness bundle (HasFixedDomain + QBounded +
    finite alphabets) — attainment is FALSE without it
    (AttainmentCounterexample.lean:766).
  - Three live quarry sorries are never forwarded:
    Legacy/FundamentalTheorem.lean:172, Legacy/Amplification.lean:119,
    CBCStructureGraph.lean:1415.  Legacy `advantage` is non-adaptive — it
    is NOT Def 2.26.
  - Thesis errata (kernel-checked in the quarry): Def 2.27/2.28 inner inf
    should be sup; Thm 2.29 min over pairs should be max.  State the
    CORRECTED forms; cite the erratum in the docstring.

SCOPE AMENDMENT (Marc, 2026-08-18b): THE TECHNIQUE PROGRAM IS OPENED —
game winnability/blinders (Lanz Ch.2 L4's technique half), conditional
equivalence (Maurer02/Mau13), MBO + MPR07's optimal failure condition,
the Patarin H-coefficient technique — integrated as MODELING (first-class
objects) + PROOF TECHNIQUE (bound theorems against Adv⊥/classDistance +
application kits).  L5's amplification APPLICATION theorems stay deferred.
Survey matrix first (from disk + visual sources), then legs.

SCOPE (original, 2026-08-18): PURE RANDOM-SYSTEMS MATERIAL ONLY until further
ruling — L4 (games, rows 2.20-2.25/2.35-2.37) and L5 (amplification, §2.5)
are DEFERRED; active queue: L2b (Thms 2.29/2.30, errata-corrected max
forms), row 2.19 (#72 Behaviour quotient), U1 (single-query tuple reading),
row 2.16 (Example 2.16 artifact).  No lane brief may open L4/L5 material.

NAMING CONVENTIONS (three layers, all binding):
  (1) PAPER NAMES FIRST: objects named by their names in the source papers
      under the SOURCE HIERARCHY (MR16, Jost, Liu, Lanz primary; CR18
      fallback-only — see the register at the top of this file):
      equivalent/classDistance from Lanz Defs 2.17/2.28, Adv/statDist per
      the papers; keptPrefix/fullyDefined keep their historical CR18 names.  A name not
      from a paper is a COINAGE: flagged in the docstring AND its ledger
      row.
  (2) MATHLIB GRAMMAR: defs camelCase; theorem names snake-joined tokens
      with def names verbatim (grep the def, find every theorem).
  (3) RS HOUSE PATTERNS: established vocabulary is continued, never
      re-invented (historyAt, keptPrefix, exists_absorb_*, *_concat
      frontier receipts, *_congr transports, the replay/need/absorb
      decomposition); suffix conventions follow the layer (_fully, _at).


**Source.**  D. Lanzenberger, *A Theory of Random Systems, Games, and Hardness
Amplification*, DISS ETH No. 29554.  Chapter 2 ("Theory of Random Systems and
Games"), printed pp. 5–41 (PDF pp. 15–51), read visually in full, plus
Appendix A.1 ("Extra Proofs for Chapter 2", printed pp. 87–89), which carries
two numbered lemmas that Chapter 2 consumes.

**Deliverable status.**  This is a scratch file produced by a READ-ONLY audit.
The coordinator applies it to `LEDGER.md`; nothing in either repository was
edited.

---

## The four pins (binding context for every row below)

1. **Fixed `(X, Y)`.**  Every obligation is stated at a fixed pair of alphabets.
   Nothing here asks for the universal carrier `Phi` or for cross-alphabet
   statements; those belong to the MR16 track.
2. **The distance is `PDS.advFullyDefined` / `PDS.trLawFullyDefined`**
   (`RandomSystems/System/Environment.lean` (line drifts; grep `advFullyDefined`), `:627`) — the *fully defined*
   presentation, a supremum over `DDE.Total` environments and lengths `n` of
   `statDist` of the two transcript laws.  It is **never**
   `PDS.Adv` (`Environment.lean:251`), the strict-compatibility form indexed by
   compatible stopping environments, and it is **never** `PDS.maxEDist`
   (`ProbabilisticSystem.lean:274`), the Jost/strict-distinguisher form.
   Lanzenberger's own Definition 2.26 is `Adv`; the tree's ruling R4 replaces it
   by `advFullyDefined`, CONNECTED on the shared-domain slice as of L1 (`PDS.advFullyDefined_eq_Adv_of_dom_eq`; `Adv_le_advFullyDefined` unconditional) and IDENTIFIED WITH Δ on the finite slice as of L3 (`PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded`; Def-2.26 reading `classDistance_eq_Adv_of_commonDomain_bounded`).
3. **Converter-free.**  Any item that needs a converter/protocol *attached* to a
   system routes to the MR16 track (`attachEngineFully`, LEDGER DRIFT-REPAIR),
   not here.  This bites §2.5 hardest: Definition 2.41's construction `C` and
   Definition 2.42's combiner are exactly attachment-shaped.
4. **Typed ↔ Φ transfer only through the `ofTyped` isometry receipts.**
   *Correction to the brief:* the isometry is
   `PDS.advFullyDefined_ofTyped` at **`RandomSystems/System/Absorb.lean:1062`**
   (with `System.exists_absorb_ofTyped` `:939` and
   `System.exists_absorb_ofTyped_typed` `:1009`), **not** in `ClassDistance.lean`
   — `ClassDistance.lean` contains no `ofTyped` declaration at all.

## The quarry rule

`/Users/marcilunga/Documents/tob/research/random-systems` is READ-ONLY, always.
Nothing there is imported, built, or edited.  A quarry verdict is a claim about
what *transplants*, and every REUSE verdict carries a **transplant delta**
saying what must change:

| delta | meaning |
|---|---|
| `carrier` | the statement/proof rides a different system type (old `DDS`/`RandomSystem`/`PFunDDS`/`Legacy.PDS`) and must be re-based on `RandomSystems.PDS X Y = Distribution (System.DDS X Y)` |
| `metric` | the statement is phrased with `maxEDist` / `maxAdvantage` / a CR18-`⊥` convention and must be re-phrased on `advFullyDefined` (pin 2) |
| `both` | both of the above |
| `none` | pure `Distribution`/combinatorial content, carrier- and metric-free |

| verdict | meaning |
|---|---|
| `REUSE-ARCH` | the proof structure transplants; the row names the file:line and the invariant/technique |
| `REUSE-STMT` | the statement shape transplants; the proof must be redone on the current carrier |
| `REF-ONLY` | informs the work but does not transplant |
| `NONE` | nothing in the quarry |

## The five series legs

* **L1** — equivalence + the non-adaptive reduction (Def 2.17 / Lemma 2.18).
* **L2** — finite slice + multi-system Δ (Thm 2.29 / Lemma 2.30) + the
  q-query `Fintype` subcarrier.
* **L3** — attainment → Thm 2.31 / 2.32: Lemma 2.33, Notation 2.34's successor
  systems, the δ-partition (Lemma 2.5), the coding map.
* **L4** — games: Defs 2.20–2.25, winnability Thm 2.37 and related.
* **L5** — applications §2.5: Thm 2.45, combiners, combinations of games.
* **L0** — already-closed substrate (no obligation, or closed in-tree).

---

# M1 — Chapter 2 enumeration (visual read, complete)

**57 items**: 49 numbered items `2.1`–`2.49`, 2 Appendix-A.1 lemmas
(`A.1`, `A.2`) that Chapter 2's proofs consume, and 6 substantive *unnumbered*
claims that carry real obligations (`U1`–`U6`).  Chapter 2 has no numbered item
outside the run `2.1`–`2.49`; §2.4.2, §2.4.3 and §2.5 introduce load-bearing
machinery inside proofs and inside prose paragraphs, which is where `U1`–`U6`
come from.

Item kinds: Def = Definition, Lem = Lemma, Thm = Theorem, Cor = Corollary,
Not = Notation, Ex = Example, Rem = Remark, Unn = substantive unnumbered claim.

---

# M2 — the current tree: verified anchors

Every declaration below was read on disk (not assumed).  `AC` = the
abstract-crypto repository root.

## Probability layer (Lanzenberger §2.2, verbatim)

| thesis object | declaration | file:line |
|---|---|---|
| Def 2.1 distribution (finite support, **arbitrary weight**) | `Probability.Distribution A := A →₀ ℝ`, `.weight`, `.isProbDist` | `Probability/Distribution.lean:56,77,138` |
| Def 2.2 marginal | `Distribution.marginal`, `marginalAt` | `Probability/Distribution.lean:658,667` |
| Def 2.4 statistical distance (one-sided `Σ max(0, X−Y)`) | `Probability.statDist` | `Probability/StatisticalDistance.lean:142` |
| Def 2.4's remark forms | `statDist_eq_weight_sub_sum_min`, `statDist_eq_half_sum_abs_of_weight_eq`, `statDist_symm_of_eq_weight` | `…/StatisticalDistance.lean:228,258,188` |
| Lem 2.5 partition additivity | `statDist_partition` | `…/StatisticalDistance.lean:896` |
| Def 2.6 f-transformation | `Distribution.fTransform` | `Probability/Distribution.lean:685` |
| Lem 2.7 data processing | `statDist_fTransform_le` | `…/StatisticalDistance.lean:921` |
| Lem 2.8(1) coupling bound | `Probability.statDist_le_offDiagonalMass` | `Probability/Coupling.lean:247` |
| Lem 2.8(2) optimal coupling exists | `exists_coupling_offDiagonalMass_eq`, `optimalJoint`, `isCoupling_optimalJoint`, `offDiagonalMass_optimalJoint` | `Probability/Coupling.lean:326,126,179,208` |

## System layer (§2.3)

| thesis object | declaration | file:line |
|---|---|---|
| Def 2.9 DDS | `System.DDS X Y` (a `PFun (List X) Y` with `Valid`: non-empty, prefix-closed domain) | `RandomSystems/System/DiscreteSystem.lean:66,60` |
| Def 2.9 finiteness clause | `QBounded`, `filterQueries` — predicates only, **no `Fintype` anywhere** | `…/DiscreteSystem.lean:37,403` |
| Def 2.11 DDE | `System.DDE Y X` | `RandomSystems/System/Environment.lean:72` |
| Def 2.12 transcript + compatibility | `System.trN`, `tr`, `Stops`, `Compatible` | `…/Environment.lean:114,155,150,170` |
| Def 2.13 parallel composition | `System.parallel`, `parallelDom`, `PDS.parLaw` | `…/DiscreteSystem.lean:585,580`; `…/Parallel.lean:76` |
| Def 2.14 PDS + common-domain clause | `RandomSystems.PDS X Y := Distribution (System.DDS X Y)`, `PDS.HasFixedDomain` | `…/ProbabilisticSystem.lean:73,85` |
| Def 2.15 PDE | `PDE Y X` | `…/Environment.lean:217` |
| Def 2.17 equivalence | `PDS.equivalent` (over `DDE.Total`, at every length) | `…/ClassDistance.lean:85` |
| Def 2.26 `Adv` | `PDS.Adv` — **present but off-pin**; `PDS.advFullyDefined` is the pin-2 object | `…/Environment.lean:251`, `:636` |
| Def 2.28 `Δ` | `PDS.classDistance` | `…/ClassDistance.lean:143` |

## The pin-2 metric and its receipts

`PDS.trLawFullyDefined e n S := fTransform (fun s => DDE.Total.transcript s e n) S`
(`Environment.lean:627`) and
`PDS.advFullyDefined S T := ⨆ e ⨆ n, ofReal (statDist (trLaw… S) (trLaw… T))`
(`:636`).  Receipts already proved:

* `advFullyDefined_self` `:645`, `advFullyDefined_triangle` `:682`,
  `advFullyDefined_comm_of_weight_eq` `:672` — pseudometric laws.
* `advFullyDefined_le_statDist` `:754` — the R4 bridge (Lem 2.7 at every index).
* `advFullyDefined_le_offDiagonalMass` `:782` — the coupling method at Φ.
* `advFullyDefined_sum_le` `:710` — mixtures.
* `advFullyDefined_congr` `ClassDistance.lean:118`,
  `classDistance_congr` `:185`, `classDistance_le_statDist_of_equivalent` `:154`,
  `le_classDistance` `:162`.
* `advFullyDefined_le_classDistance` `ClassDistance.lean:246` — **the easy half of
  Thm 2.31** (`Adv⊥ ≤ Δ`), unconditional.
* `classDistance_le_offDiagonalMass` `:262`,
  `advFullyDefined_le_offDiagonalMass_of_equivalent` `:282` — prove-static /
  consume-interactive.
* `PDS.advFullyDefined_ofTyped` **`Absorb.lean:1062`** — the pin-4 isometry
  (`=`, both directions), built from `System.exists_absorb_ofTyped` `:939` and
  `System.exists_absorb_ofTyped_typed` `:1009`.

## What the tree already says is missing (in-tree admission)

`ClassDistance.lean:290–320` is a signed "Queued: the reverse inequality" note
that itemizes the Theorem 2.31 gap exactly as this matrix does: (i) the finite
slice — *"no `Fintype` on any system carrier, and none is possible on
`System.DDS X Y` even at finite alphabets, since `List X` is infinite"*, with the
`q`-query subtype named as the missing object; (ii) the attainment machinery —
Lemma 2.33, Notation 2.34, Lemma 2.5's partition, the query induction with the
adaptive step `sup_e = max_x ∑_y sup_{e'}`; (iii) which `Adv` — the coding map
from Def 2.26's `PDS.Adv` to `advFullyDefined`.  I verified each of the three
claims independently; all three hold.

## Empty placeholders (confirmed by reading the files)

`RandomSystems/Game/{Game,MonotoneCondition,Winnability}.lean` and
`RandomSystems/Technique/{ConditionalEquivalence,DataProcessing,HCoefficient,
Switching}.lean` are 10-line "Target module for the random-systems migration.
Not yet populated." stubs.  **The whole of L4 has no home yet.**

---

# M4 — THE MATRIX

Pages are **printed** thesis pages.  `AC:` = abstract-crypto path, `Q:` = quarry
path (`RandomSystems/…` under
`/Users/marcilunga/Documents/tob/research/random-systems`).

## Quarry vocabulary trap (read before using any pointer below)

The quarry and the current tree use **the same notation for different objects**:

| symbol | quarry meaning | current-tree meaning |
|---|---|---|
| `Δ(S, T)` (with parens) | `maxAdvantage` — `sSup` over probability **distinguishers** `D` of the *signed* `verdictProb D T − verdictProb D S` (`Q: Distinguishing.lean:136,139`) | `PDS.classDistance` — Def 2.28's infimum over representatives (`AC: ClassDistance.lean:149`) |
| `Δ S T` (no parens) | the class distance, Def 2.28 (`Q: RandomSystem.lean:8358`) | — |
| `Adv S T` | `sup_e δ(tr(S,e), tr(T,e))`, Def 2.26 (`Q: RandomSystem.lean:901`) | `PDS.Adv` (`AC: Environment.lean:251`), **off-pin** |
| — | — | `Adv⊥(S, T)` = `advFullyDefined`, the pin-2 object |

Any transplant that copies a quarry statement verbatim will silently change
which distance is being claimed.  Every `metric` delta below is this.

---

## L0 — substrate (closed, or no obligation)

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.1 | 11 | Def | distribution over `A`: `A → ℝ≥0` with finite support; weight `\|X\|`; **weight is not required to be 1** | **DONE** `Probability.Distribution := A →₀ ℝ`, `.weight`, `.isProbDist` (`AC: Probability/Distribution.lean:56,77,138`) | REF-ONLY — `Q: Dist.lean:55` is the identical `Dist A := A →₀ ℝ`; the current tree is a copy already. delta `none` |
| 2.2 | 12 | Def | marginal `Xᵢ` of a distribution over a product | **DONE** `Distribution.marginal`, `marginalAt` (`AC: Distribution.lean:658,667`) | REF-ONLY — `Q: Dist.lean:617,626`. delta `none` |
| 2.4 | 12 | Def | `δ(X,Y) := Σ max(0, X(a)−Y(a)) = \|X\| − Σ min(X,Y)`; asymmetric off equal weight | **DONE** `statDist` + `statDist_eq_weight_sub_sum_min`, `statDist_symm_of_eq_weight`, `statDist_eq_half_sum_abs_of_weight_eq` (`AC: StatisticalDistance.lean:142,228,188,258`) | REF-ONLY — `Q: StatDist.lean:142,200,170,230` is the same file one generation back. delta `none` |
| 2.6 | 12 | Def | `f`-transformation `f(X) := X ∘ f⁻¹` | **DONE** `Distribution.fTransform` (`AC: Distribution.lean:685`) | REF-ONLY — `Q: Dist.lean:644`. delta `none` |
| 2.7 | 13 | Lem | data processing: `δ(X,Y) ≥ δ(f(X), f(Y))` for total `f` | **DONE** `statDist_fTransform_le` (`AC: StatisticalDistance.lean:921`) | REF-ONLY — `Q: StatDist.lean:815`, plus the equality-under-injectivity companion `:914`. delta `none` |
| 2.8 | 13 | Lem | Coupling Lemma (Aldous 3.6): (1) any joint gives `δ ≤ Pr(X≠Y)`; (2) a joint attaining equality exists | **DONE** (1) `statDist_le_offDiagonalMass` (`AC: Coupling.lean:247`); (2) `exists_coupling_offDiagonalMass_eq` `:326`, witness `optimalJoint` `:126` | REF-ONLY — `Q: Coupling.lean:149,378`, witness `optimalJoint` `:191`, header cites this as *"Lemma 4 of Lanzenberger–Maurer (TCC 2020)"*. Identical shape; the current tree already carries the improved `IsCoupling`/`offDiagonalMass` split. delta `none` |
| 2.9 | 13 | Def | `(X,Y)`-DDS: partial `s : X⁺ → Y` with prefix-closed domain; *finite* if `X` finite and `dom(s) ⊆ ∪_{i≤n} Xⁱ`; `dom₁(s)` | **DONE** (object) `System.DDS`, `Valid` (`AC: DiscreteSystem.lean:66,60`); **PARTIAL** (finiteness clause) — see L2 | REF-ONLY — `Q: PFunDDS.lean:64` `{S : List X →. Y // Valid S}` is the same object. delta `carrier` (the quarry rides `PFunDDS`, the tree rides `PFun (List X) Y` with `Valid`; equivalent but not literally interchangeable) |
| 2.10 | 14 | Ex | the four single-query `({0,1},{0,1})`-DDS `zero, one, id, flip` | **MISSING** — no worked instance; `functionEvaluator` (`AC: DiscreteSystem.lean:114`) covers the genus | REUSE-STMT — `Q: AttainmentCounterexample.lean:44–57` builds four concrete `Bool`-query atoms in exactly this style. delta `carrier` |
| 2.11 | 14 | Def | DDE `e : Y* → X`, partial, prefix-closed domain | **DONE** `System.DDE` (`AC: Environment.lean:72`) | REF-ONLY — `Q: PFunDDS.DDE`. delta `carrier` |
| 2.12 | 14 | Def | transcript `tr(s,e)`; compatibility ("`e` never queries outside `dom s`"); the environment may stop | **DONE** `trN`, `tr`, `Stops`, `Compatible` (`AC: Environment.lean:114,155,150,170`); the pin-2 line replaces compatibility+stopping by the total presentation `DDE.Total.transcript` `:356` | REF-ONLY — `Q` uses `transcriptDist S e n` throughout (`BoundedAttainment`, `TranscriptHybrid`), the same length-indexed shape. delta `carrier` |
| 2.14 | 15 | Def | PDS = distribution over DDS, all support elements sharing one domain; always finite | **DONE** `PDS X Y := Distribution (System.DDS X Y)`, common-domain clause as `HasFixedDomain` (`AC: ProbabilisticSystem.lean:73,85`) | REF-ONLY — `Q: PDS.lean:68` `PFunPDS X Y := Dist (PFunDDS.DDS X Y)`, normalized subtype `PFunPDS.Prob` `:76`. delta `carrier` |
| 2.15 | 15 | Def | PDE = distribution over DDE | **DONE** `PDE Y X` (`AC: Environment.lean:217`) | REF-ONLY. delta `carrier` |
| 2.23 | 17 | Rem | an environment does not observe the MC; this matters in the probabilistic case | **PROSE** — no obligation | NONE |
| 2.26 | 18 | Def | `Adv(S,T) := sup_e δ(tr(S,e), tr(T,e))`, same domain | **PARTIAL** — Def 2.26 verbatim is `PDS.Adv` (`AC: Environment.lean:251`), which pin 2 forbids; the pin-2 object `advFullyDefined` `:636` is Def 2.26 *over the CR18 total presentation*. **The coding map between them is not stated anywhere** (the tree's own `ClassDistance.lean:312` admits this) | REUSE-STMT — `Q: RandomSystem.lean:901` is Def 2.26 verbatim on the partial carrier; `Q: TranscriptAdvantage.lean:109` `maxAdvantage_eq_transcriptAdvantageOn_of_common_fTransform` is the **only** quarry statement of the shape "restricting the environment index set is lossless", which is the shape the missing coding map needs. delta `both` |

**L0 tally: 14 items — 11 DONE, 1 PARTIAL (2.26), 1 MISSING (2.10), 1 PROSE (2.23); quarry 2 REUSE-STMT, 11 REF-ONLY, 1 NONE.**

---

## L1 — equivalence and the non-adaptive reduction

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.16 | 15 | Ex | `V := {(zero,¼),(one,¼),(id,¼),(flip,¼)}`, `V′`, and the family `V_α`; **`[V] = {V_α \| α ∈ [0,½]}`** — the equivalence class of a PDS is a nontrivial line | **MISSING** — no worked class in the tree at all | **REUSE-ARCH** — `Q: Example216.lean` is this example, complete and `sorry`-free: `singleQuery` `:129`, `V` `:310`, `isProbDist_V` `:356`, `classBehavior` `:367`, `observableBehavior_V` `:387`, `equivalent_V` `:439` (`α,β ≤ ½ → Equivalent (V α) (V β)`), `delta_V0_Vhalf` `:490` (`δ(V 0, V ½) = 1`). The invariant that transplants: **the whole class is pinned by one closed-form behavior function** (`classBehavior`), so `equivalent_V` is a `rfl`-after-`observableBehavior_V` argument rather than an environment induction. delta `carrier` (`PFunPDS Bool Bool` → `PDS Bool Bool`; `δ` → `statDist`, which are *equal* on non-negative laws, `Q: RandomSystem.lean:93`) |
| 2.17 | 16 | Def | `S ≡ T` iff same domain **and** `tr(S,e) = tr(T,e)` for all compatible DDE `e`; `[S]` | **DONE** `PDS.equivalent` (`AC: ClassDistance.lean:85`), over `DDE.Total` at every length; the domain clause is documented as subsumed by the total presentation | **REUSE-STMT + a decisive bridge.** `Q: RandomSystem.lean:550` `Equivalent` is the same total-presentation definition. **The important find is `Q: ThesisModel.lean`**, which states Def 2.17 in the *thesis's own* shape — a partial environment `PartialDDE := {e : List Y →. X // prefix-closed}` `:88`, `Compatible` `:220`, `ThesisEquivalent` `:244` — and then proves **`equivalent_iff_thesisEquivalent` `:786`** under `HasFixedDomain S D`/`HasFixedDomain T D`. delta `carrier` |
| 2.18 | 16 | Lem | `S ≡ T` ⟺ transcripts agree for all compatible **non-adaptive** DDE | **MISSING** — `AC: ClassDistance.lean:82` explicitly records it as "a *characterization* … not needed by anything below" | **REUSE-ARCH** — proved twice in the quarry: `Q: RandomSystem.lean:796` `transcript_equivalent_of_nonadaptive_transcript_equivalent` (with `NonAdaptive e := ∀ y y', y.length = y'.length → e y = e y'` `:622` and the replay environment `playQueries` `:767`), restated in thesis shape as `Q: LanzenbergerChain.lean:188` `lemma_2_18_nonadaptive_environments_suffice`. The transplantable invariant is the Appendix-A.1 device `Q: LanzenbergerChain.lean:160` `fixed_transcript_event_eq_fixed_query_event`: *a fixed transcript event is a fixed-query event*, which is exactly the replay step of the thesis proof. There is also a *legacy* proof on the total carrier, `Q: Legacy/Equiv.lean:895` `equivAdaptive_iff_nonadaptive`, whose machinery (`firstInputIndex`, position tapes, fiber counting) is a **different, much heavier** route — do not transplant that one. delta `carrier` |
| 2.19 | 16 | Not | bold `S` = the equivalence class; `tr(S,e)` well defined on the class | **PARTIAL** — the tree works with representatives + `advFullyDefined_congr` (`AC: ClassDistance.lean:118`) and never forms the quotient | REUSE-STMT — `Q: RandomSystemQuotient.lean:99` builds the actual quotient `RandomSystem X Y` with `ofProb` `:150`, `of_prob_eq_of_prob_iff` `:154`, and a descended distance `maximalAdvantage` `:171`; `Q: RandomSystemMetric.lean:59` upgrades it to a genuine `MetricSpace` via `maximal_advantage_eq_zero_iff_equivalent` `:49`. **delta `metric`** — that `MetricSpace` instance is built on `maxAdvantage`, which pin 2 forbids; the quotient *construction* transplants, the metric instance does not |

**L1 tally: 4 items — 1 DONE, 1 PARTIAL, 2 MISSING; quarry 2 REUSE-ARCH, 2 REUSE-STMT, 0 NONE.**
**L1 is the cheapest leg in the whole matrix: every obligation has a finished quarry proof.**

---

## L2 — the finite slice and the multi-system distance

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.9 (fin) | 13 | Def | a DDS is *finite* when `X` is finite and `dom(s) ⊆ ∪_{i≤n} Xⁱ`; the thesis restricts to finite systems throughout | **MISSING** — the two ingredients exist as *predicates* (`QBounded` `AC: DiscreteSystem.lean:37`, `HasFixedDomain` `ProbabilisticSystem.lean:85`) but **`QBounded` has zero call sites** and there is **no `Fintype` on any system carrier anywhere in the tree** (verified by grep). `AC: ClassDistance.lean:301` states the obstruction: `List X` is infinite even at finite `X`, so the `Fintype` must come from a `q`-query *subtype* | **REUSE-STMT** — the quarry never builds a `Fintype` subcarrier either; it packages the three hypotheses instead: `Q: BoundedAttainment.lean:90` `PFunPDS.HaveCommonDomainAndBounded S T D q` = `[Fintype X]` + `HasFixedDomain … D` + `QBounded D q`, and every attainment theorem carries it. **This is the shape to copy**: the finite slice is a *hypothesis bundle*, not a subtype. delta `carrier` |
| U5 | 38 | Unn | "On the Number of Queries": `q` is a property of the **system** (how many queries it answers), not of the distinguisher; a bound on the components induces a bound `q′` on the construction | **MISSING** as a ruling; `filterQueries` (`AC: DiscreteSystem.lean:403`) is the mechanism | REUSE-ARCH — the quarry adopts exactly this ruling and mechanizes it: `Q: PFunDDS.lean:395` `filterQueries`, `Q: MaxWinProb.lean` docstring ("impose the bound by the filter `[q]` on the *game*, not here"), and the normalization predicates `Q: GameOf.lean:1163` `DeltaFiniteQueryNormalization` / `:1176` `DeltaFilteredFiniteQueryNormalization` with the discharge `:1204` from `TotalOnNonempty`. delta `carrier` |
| 2.27 | 18 | Def | `Δ(𝒮) := 1 − inf_{(S₁,…,Sₙ)} sup_ℰ Pr(S₁ = … = Sₙ)` for a finite set of random systems | **MISSING** | **REUSE-ARCH, with a source erratum.** `Q: MultiSystemCoupling.lean` builds the agreement side: `IsJointOf` `:215`, `agreementMass` `:243`, `supAgreement` `:248`, `overlapDist` `:374` (pointwise min), `agreementMass_le_weight_overlapDist` `:422`, existence `:477`, **attainment `supAgreement_eq_weight_overlapDist` `:550`**, and the `n=2` bridge `supAgreement_pair_eq_weight_sub_delta` `:615`. `Q: LanzenbergerChain.lean:350` `multiSystemDistance` packages Def 2.27 **with `inf` corrected to `sup`**, keeping the verbatim printed form as `printedMultiSystemDistance` `:366` and refuting it with `Q: Example216.lean:591` `definition_2_28_printed_displays_disagree` (`printedMultiSystemDistance (fun _ : Fin 2 => V 0) ≠ Δ (V 0) (V 0)`), while `:602` `corrected_display_agrees_at_V` confirms the corrected form. **Do not transplant the printed display.** delta `carrier` (the agreement machinery is on plain `Dist A` with no system content — delta `none` for `MultiSystemCoupling` itself) |
| 2.29 | 19 | Thm | `min_{i≠j} Δ(Sᵢ,Sⱼ) ≤ Δ(𝒮) ≤ (min(n,ℓ)−1)·min_{i≠j} Δ(Sᵢ,Sⱼ)`, `ℓ = \|∪ᵢ∪_{Sᵢ} supp(Sᵢ)\|` | **MISSING** | **REUSE-ARCH, with a second source erratum.** `Q: MultiSystemCoupling.lean:774` `theorem_2_29_distribution_upper_bound` proves the upper bound in **attained `∃ i ≠ j` form**, and `:958` `printed_min_form_counterexample` is a **kernel-checked refutation of the printed `min` over pairs** (3 laws on `Fin 3`); the correct reading is `max`. `Q: LanzenbergerChain.lean:567,577,608` carries the lower bound, the refuted min-form, and the corrected upper bound as three named declarations. delta `none` for the distribution-level content, `carrier` for the system-level wrapper |
| 2.30 | 19 | Lem | matrix lemma: `A ∈ ℝ₊^{n×m}`, every column has a zero, every row sums to `δ` ⟹ `min_{i,j} Σ_k min(A_ik, A_jk) ≤ (1 − 1/(min(m,n)−1))·δ` | **MISSING** | **REUSE-ARCH** — `Q: MultiSystemCoupling.lean:641` `lemma_2_30_zero_column_matrix_bound`, stated in `∃ i ≠ i'` form over `[Fintype row] [Fintype col]` with `2 ≤ card`. The one deviation worth copying: the thesis's "WLOG reorder the rows" is replaced by an explicit **zero-row selector** `z : column → row`, which is what makes the case split formalizable. delta `none` — this is pure real-matrix combinatorics, no carrier and no metric |

**L2 tally: 4 items (2.27, 2.29, 2.30, U5) — all 4 MISSING; quarry 3 REUSE-ARCH, 1 REUSE-STMT.**  The first row above (`2.9 (fin)`) is an *annex*: it re-opens the finiteness clause of item 2.9, counted once in L0, and it is L2's entry obligation.
**L2 carries the two source errata; both are kernel-checked in the quarry and must travel with the transplant.**

---

## L3 — attainment: Theorems 2.31 / 2.32

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.3 | 12 | Lem | `n` distributions of a common weight `p` admit a joint with those marginals (witness `p^{-(n-1)}∏ᵢXᵢ`) | **PARTIAL** — `Probability/FiberCoupling.lean:242` `exists_coupling_of_fTransform_eq` is the *2-ary conditional* gluing (equal pushforward along a shared projection); the `n`-ary equal-weight product is not there | REUSE-STMT — `Q: DistCoupling.lean:242` is the same 2-ary fiber statement (the current tree's file is a rename of it); the `n`-ary form appears only inside `Q: RandomSystem.lean`'s Lemma-2.33 apparatus (`jointProfileList` `:2835`, `crossJointOf` `:3586`). delta `none` |
| 2.5 | 12 | Lem | `δ(X,Y) = Σᵢ δ(Xᵢ,Yᵢ)` for a partition with `supp(Xᵢ), supp(Yᵢ) ⊆ 𝒜ᵢ` | **DONE** at the distribution level (`AC: StatisticalDistance.lean:896`); **MISSING** in the form L3 actually consumes — additivity across *first-answer branches* of a transcript law | **REUSE-ARCH** — `Q: TranscriptBranchDistance.lean:35` is exactly the consumed form: `δ(Σ_{y∈ys} (x,y)::Sf y, Σ_{y∈ys} (x,y)::Tf y) = Σ_{y∈ys} δ(Sf y, Tf y)`, with the branch index an explicit `Finset (Option Y)` and disjointness *derived* from distinct first answers rather than assumed. Its one hypothesis (`Tf` branchwise `NonNeg`) is defended in-file as Lemma 2.5's own, not an artifact. delta `carrier` |
| 2.28 | 18 | Def | `Δ(S,T) := inf_{S∈S,T∈T} δ(S,T)` | **DONE** `PDS.classDistance` (`AC: ClassDistance.lean:143`) with both eliminators (`le_classDistance` `:162`, `classDistance_le_statDist_of_equivalent` `:154`) | REF-ONLY — `Q: RandomSystem.lean:8358` `Δ` is the same `sInf`, but restricted to `NonNeg` representatives. **Worth importing that restriction as a design question**, not as code. delta `carrier` |
| U1 | 20 | Unn | the single-query case: a single-query DDS is a tuple in `Y^{\|X\|}`, and `Adv(S,T) = max_i δ(Sᵢ,Tᵢ)` | **MISSING** | REUSE-ARCH — `Q: BoundedAttainment.lean:382` `optimal_advantage_eq_static_distance_of_finite_common_domain_and_bounded_zero` is the depth-0 base case (`Adv S T = δ S T`) and `:348` gives its closed form `max(\|S\|−\|T\|, 0)`; `Q: Example216.lean` supplies the single-query DDS-as-tuple representation on the partial carrier. delta `both` |
| 2.33 | 21 | Lem | families `Xᵢ, Yᵢ` of common weights `p_X, p_Y` admit joints `X, Y` with those marginals and `δ(X,Y) = max_i δ(Xᵢ,Yᵢ)` | **MISSING** — `AC: ClassDistance.lean:307` names it as one of the three missing objects and correctly notes `exists_coupling_offDiagonalMass_eq` is "the two-law case, **not** this" | **REUSE-ARCH** — `Q: RandomSystem.lean:4113` `exists_finite_class_joint_witness_of_common_side_weights` (structure `FiniteClassJointWitness` at `:4075`) is Lemma 2.33 at finite first-query classes, built from `jointProfileList` `:2835`, `jointProfile` `:3048`, `classChoiceDist` `:3120`, `choiceOf` `:3275`, `trimOf` `:3349`, `crossJointOf` `:3586`. This is ~1300 lines of apparatus and is the single largest transplantable asset for L3. delta `carrier` |
| 2.34 | 21 | Not | successor system `s^{↑x}`, successor environment `e^{↑y}`, and the PDS transform `S^{↑x↓y}` — **weight `\|S^{↑x↓y}\|` = Pr[S answers `y` to `x`], so it is *not* a probability distribution**; this is why Def 2.1 must allow arbitrary weight | **MISSING** | **REUSE-ARCH** — `Q` has it twice. Live carrier: `successorTransform` with `Q: RandomSystem.lean:2169` `weight_successorTransform` (`= S.mass fun s => output (fullyDefined s) [x] _ = y`) — exactly the thesis's weight identity — plus `Q: BoundedAttainment.lean:254` (successor pairs keep a common domain with bound `q−1`), `:539` (transcript law splits over the first-answer image), `:584` (reassembly: equal weight + rejection agreement off `D` + successorwise equivalence ⟹ `Equivalent`), `:1129` (per-answer δ identity). Legacy carrier: `Q: Legacy/Successor.lean:42` `firstQueryMass`, `:51` `successor_weight`, `:128` `successor_preserves_equiv` — same content, crushed by a two-level `Fintype` instance burden the file itself flags as its "defining friction". **Transplant the live one.** delta `carrier` |
| U2 | 22 | Unn | eq. (2.1) and its induction: for all `q`-query PDS with the same domain, `∃ S′∈[S], T′∈[T]` with `δ(S′,T′) = sup_e δ(tr(S,e),tr(T,e))`; induction on `q` with the adaptive step `sup_e = max_x Σ_y sup_{e′}` and an initial-query prepend | **MISSING** — this *is* the missing induction | **REUSE-ARCH** — `Q: BoundedAttainment.lean:751` `exists_bounded_attainment_witness_of_finite_common_domain_and_bounded` **is this induction, finished**, returning `Nonempty (BoundedAttainmentWitness S T q)` (structure `:705` carrying the two representatives, their equivalences, their preserved weights, an attaining environment, and the δ = transcript-δ identity). delta `carrier` |
| 2.31 | 20 | Thm | `Δ(S,T) = Adv(S,T)`, **with attainment** | **PARTIAL — one half only.** `AC: ClassDistance.lean:246` `advFullyDefined_le_classDistance` is `Adv⊥ ≤ Δ`, unconditional. The reverse is absent by design; `:290–320` itemizes what is missing | **REUSE-ARCH — the theorem is proved in the quarry.** `Q: BoundedAttainment.lean:1106` `class_distance_eq_optimal_advantage_of_finite_common_domain_and_bounded : Δ S T = Adv S T`, with the attainment form at `:1074`, restated in thesis shape as `Q: LanzenbergerChain.lean:208` `theorem_2_31_distance_eq_advantage_attained` (conjunction of the equality and the attaining pair). **Critical caveat: this is `Adv` (Def 2.26 on the quarry's partial carrier), not `Adv⊥`, and it carries `[Fintype X] + HaveCommonDomainAndBounded`.** delta `both` |
| 2.32 | 20 | Thm | Coupling Theorem for Random Systems: `∃ S∈S, T∈T` with a joint s.t. `Adv(S,T) = Pr(S ≠ T)` | **PARTIAL** — the inequality direction is `AC: ClassDistance.lean:282` `advFullyDefined_le_offDiagonalMass_of_equivalent`, and Lemma 2.8's attainment half is `AC: Coupling.lean:326`; the *composition* (attained representatives ∘ optimal coupling) is missing because 2.31 is | **REUSE-ARCH** — `Q: RandomSystemCoupling.lean:112` `exists_equivalent_representatives_with_probability_coupling_disagreement_eq_optimal_advantage_of_finite_common_domain_and_bounded`, restated at `Q: LanzenbergerChain.lean:260`. The proof is literally three lines once 2.31 is available — attained pair, then `optimal_probability_coupling_exists` `:48`. delta `both` |
| — | — | — | **the unrestricted strengthening is FALSE** (a project finding, not a thesis claim) | **not recorded in the tree** | **REUSE-ARCH (a refutation you must import).** `Q: AttainmentCounterexample.lean:766` `four_pattern_unrestricted_class_distance_ne_optimal_advantage`: at `PFunPDS Bool PUnit`, `Adv = ½` (`:643`) while **every** equivalent representative pair has `δ = 1` (`:718`), so `Δ = 1` (`:734`); the pair has no common support domain (`:252`). The mechanism is CR18 Def 3.3: a rejected query is *visibly* `⊥` and is deleted only from the DDS-side history, giving the environment a free domain probe. **The current tree's `advFullyDefined` runs on exactly that presentation (`DDE.Total.transcript` over `s⊥`), so this counterexample is expected to apply verbatim — Theorem 2.31 must be stated with `HasFixedDomain` + `QBounded` + finite `X`, never unrestricted.** delta `carrier` |
| 2.26↔`Adv⊥` | 18 | Unn | the coding map: Def 2.26's compatible/stopping environments vs. the total presentation | **MISSING** — named as gap (iii) at `AC: ClassDistance.lean:312` | **REUSE-ARCH — this is the highest-leverage find in the whole survey.** `Q: ThesisModel.lean` builds the thesis's partial-environment model inside the CR18 carrier and closes both bridges: `PartialDDE.toDDE` `:296` (totalization), `transcript_toDDE_eq_someMap_thesisTranscript` `:339` (the coded environment reproduces the thesis transcript), `prunedPartialDDE` `:490` + `compatible_prunedPartialDDE` `:635` (the rejection-pruning replay, which is the hard direction), and the two endpoints **`equivalent_iff_thesisEquivalent` `:786`** and **`adv_eq_thesisAdv` `:847`** — both under `HasFixedDomain` on each side. delta `carrier` |

**L3 tally: 9 items (2.3, 2.5, 2.28, 2.31, 2.32, 2.33, 2.34, U1, U2) — 1 DONE (2.28), 4 PARTIAL (2.3, 2.5, 2.31, 2.32), 4 MISSING (2.33, 2.34, U1, U2); quarry 7 REUSE-ARCH, 1 REUSE-STMT, 1 REF-ONLY.**  The last two rows above are *annexes*, not thesis items: the attainment counterexample (a project finding that constrains how 2.31 may be stated) and the `Adv`↔`Adv⊥` coding map (gap (iii) of the tree's own queued note).
**Every L3 obligation has a finished quarry proof; not one of them is on the current carrier or the pin-2 metric.**

---

## L4 — games and winnability

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.20 | 17 | Def | monotone condition `A : X* → {0,1}` (monotone: `A(t)=1 → A(t\|t′)=1`); a DDG is the pair `s^A` | **MISSING** — `RandomSystems/Game/MonotoneCondition.lean` is a 10-line "Not yet populated" stub | **REUSE-ARCH** — carriers all exist: `Q: PDS.lean:3045` `IsMBO`, `:3060` `DDS.IsGame`, `:3066` `DDG`, `:3101` `MonotoneMBO`; transcript-level `Q: GameOf.lean:280` `MonotoneCond` and the constructor `Q: GameOf.lean:230` `gameOfDDS` with `Q: GameOf.lean:268` `ignoreMBO_gameOfDDS` (`Ŝ⁻ = s`). `Q: LanzenbergerChain.lean:63` records the reconciliation between the thesis's per-realization predicate `A_s : X* → {0,1}` and CR18's MBO-as-extra-output-bit. **Modeling delta to decide up front:** the quarry realizes a game as `PDS X (Y × Bool)` (bit adjoined to the answer), not as a pair `(s, A)`. delta `carrier` |
| 2.21 | 17 | Def | transcript of a DDG: `tr(s^A, e) = (t, A(t′))` — the environment sees the answers and the **final** MC value, not the per-round bits | **MISSING** | **REUSE-ARCH** — `Q: GameWinnability.lean:144` `wonFlag`, `:177` `gameTranscriptView` (`t ↦ (t.map (·,·.map Prod.fst), wonFlag t)`), `:181` `gameTranscriptDist`. The docstring states the modeling point explicitly: per-round MC bits are **not** observable, which is Remark 2.23 made structural. delta `carrier` |
| 2.22 | 17 | Def | PDG = distribution over DDG; two PDG are equivalent when domains agree and DDG-transcript laws agree in all environments | **MISSING** | **REUSE-ARCH** — `Q: GameWinnability.lean:194` `GameEquivalent` (`∀ winner n, gameTranscriptDist G winner n = gameTranscriptDist H winner n`). A *second, coarser* relation also exists — `Q: GameEquivalence.lean:64` `GameEquiv` (`≡ᵍ`, CR18 Def 4.16, equality of pre-winning behavior) — **which is not Def 2.22**; picking the wrong one silently weakens every downstream statement. delta `carrier` |
| 2.24 | 17 | Rem | a random game `S^A` is an equivalence class of PDG, characterized by `p^{S^A}_{Y_i A_i \| X^i Y^{i-1} A_{i-1}}`; an MC can be *adjoined* to a random system | **MISSING** | REUSE-ARCH — adjunction is `Q: GameOf.lean:988` `gameOf S cond` with `:1018` `ignoreMBO_gameOf` (`Ŝ⁻ = S`, proved) and `:1031` `monotoneMBO_gameOf`; the class-level half is `Q: GameWinnability.lean:205` `gameEquivalent_of_equivalent`. delta `carrier` |
| 2.25 | 18 | Def | `ν(S^A) := sup_e Pr(tr(S^A,e) ∈ 𝒯_w)`, `𝒯_w` = transcripts ending in `(·,1)`; deterministic environments suffice | **MISSING** | **REUSE-ARCH** — `Q: GameWinnability.lean:105` `WinningTranscript` (with `:111` monotonicity), `:124` `winningMass`, `:248` `supWinProb` (`ν`). The bridge to CR18's `Γ` is proved: `Q: GameWinnability.lean:885` `maxWinProb_eq_supWinProb`, so `Q: MaxWinProb.lean:170` `GamePerf.maxWinProb` (Def 4.17, fully generic in `Winner`/`Game`) and `Q: WinProb.lean:63` are usable as the same object. `Q: MaxWinProb.lean:156` `winProb_eq_expect_single` is the "deterministic winners suffice" step, hypothesis-free. delta `carrier` |
| U3 | 23–24 | Unn | the games `G`, `G′` on two ε-biased coins: equivalent as games, yet `G′` is **unwinnable with probability ½−ε** over its own randomness while `G` is winnable with probability 1 — the motivating gap between `ν` and per-representative winnability | **MISSING** | **NONE** — no quarry file builds this pair. It is the game-side analogue of Example 2.16, and `Q: Example216.lean` is the template for how to build such a worked pair on this carrier, but the content is absent |
| 2.35 | 24 | Def | a DDG `s^A` is **winnable** if `∃ x̂ ∈ dom(s)` with `A(x̂) = 1` | **MISSING** | **REUSE-ARCH** — `Q: GameWinnability.lean:281` `PFunDDS.Winnable` (`∃ l, ∃ hl : l ∈ dom g, (output g l hl).2 = true`). delta `carrier` |
| 2.36 | 24 | Def | `ω(S^A) := inf_{S^A ∈ S^A} Pr^{S^A}(S^A is winnable)` | **MISSING** | **REUSE-ARCH** — `Q: GameWinnability.lean:294` `infWinnability`, taken over `{H \| H.NonNeg ∧ GameEquivalent H G}`. delta `carrier` |
| 2.37 | 24 | Thm | **Winnability Theorem**: `ν(S^A) = ω(S^A)`, with an attaining representative | **MISSING** | **REUSE-ARCH — proved in the quarry.** `Q: GameWinnability.lean:778` `winnability_theorem_of_fixed_domain_and_bounded`: under `[Fintype X]`, `HasFixedDomain G D`, `QBounded D q`, `G.NonNeg`, concludes `supWinProb G = infWinnability G ∧ ∃ G', G'.NonNeg ∧ Equivalent G' G ∧ G'.mass Winnable = supWinProb G`. The trivial direction is `:338` `supWinProb_le_infWinnability`. Two **documented deviations from the thesis** that transplant with it: MC monotonicity is *never assumed* (the winning event's own monotonicity `:111` replaces it), and no probability-normalization hypothesis is used (`NonNeg` only — Def 2.1's arbitrary-weight generality). Restated in thesis shape at `Q: LanzenbergerChain.lean:300`. delta `carrier` |
| U4 | 26 | Unn | the **alternative proof of 2.37 via Theorem 2.31**: build `T : (X, Y×{0,1})`-system emitting the monotone win bit and `V` the same system always emitting `0`; then `Adv(T,V) = ν(S^A)`, and Theorem 2.31's attainment makes `T` unwinnable with probability `1 − ν` | **MISSING** | **REUSE-ARCH** — the `V` half is exactly `Q: GameWinnability.lean:356` `PFunDDS.zeroMBO` / `:374` `zeroMBODist`, and the `Adv(T,V) ≤ ν` half is `:747` `adv_zeroMBODist_le_supWinProb`; `:737` `winningMass_eq_winningMass_blindize` supplies the "bit-adaptivity is useless" step the reduction needs. **This is the route that makes L4 a corollary of L3 rather than an independent induction** — worth choosing deliberately. delta `both` |

**L4 tally: 10 items — 0 DONE, 0 PARTIAL, 10 MISSING; quarry 9 REUSE-ARCH, 0 REUSE-STMT, 1 NONE.**
**L4 has no home in the current tree at all** (three empty `Game/` stubs), and the most complete quarry coverage of any leg: `GameWinnability.lean` is a direct, `sorry`-free formalization of thesis §2.3.3 + §2.4.3.

---

## L5 — applications (§2.5)

| item | p. | kind | content | current tree | quarry verdict |
|---|---|---|---|---|---|
| 2.13 | 14 | Def | parallel composition `[s₁,…,sₙ]` as an `(X×[n], Y)`-DDS, by projecting the input list to each component | **DONE** `System.parallel`, `parallelDom` (`AC: DiscreteSystem.lean:585,580`), `restrict` `:479`; law level `PDS.parLaw` (`AC: Parallel.lean:76`) | REF-ONLY — `Q: PFunDDS.lean:577,572` is the same construction, annotated "Lanzenberger Def 2.13 = CR18 Def 3.4". delta `carrier` |
| 2.38 | 28–29 | Ex | 20 permutations → 4, `64ε⁵` by MPR07 Thm 1 | **MISSING** (illustration) | REF-ONLY — `Q: Legacy/Applications/CascadePRP.lean:90` `URPfunCascade_eq_URPfun` proves the *perfect* case (composing two uniform permutations is uniform), which is the `(1,2)`-combiner core the example instantiates. No ε-version. delta `both` |
| 2.39 | 29 | Ex | 15 permutations → 4, `320ε⁶` | **MISSING** (illustration) | **NONE** |
| 2.40 | 30 | Ex | 10 random functions + a `4×10` MDS matrix → 4 functions, `7680ε⁷` | **MISSING** (illustration) | **NONE** — no MDS-matrix construction anywhere in the quarry (grep-checked) |
| 2.41 | 30 | Def | an `n`-ary **construction** `C` is a probability distribution over functions `𝒮₁×…×𝒮ₙ → 𝒮_{n+1}` that respects `≡` in every slot | **MISSING** | REUSE-STMT — `Q: Legacy/Construction.lean:39` `structure Construction` (LM20 Def 13) has exactly the `respects_equiv` field, and `Q: Legacy/HConstruction.lean:35` generalizes to heterogeneous index types with a substitution operator `:160`. **But pin 3 bites here**: a construction wires calls to component systems, i.e. it is attachment. Under the converter-free pin this row **routes to the MR16 track** (`attachEngineFully`) rather than being built inside this matrix. delta `both` |
| 2.42 | 31 | Def | for a **monotone** `𝒜 ⊆ {0,1}ⁿ`, `C` is an `𝒜`-combiner for `(F₁,I₁),…,(Fₙ,Iₙ)` iff `C(⟨F/I⟩_{bⁿ}) ≡ C(I₁,…,Iₙ)` for every `bⁿ ∈ 𝒜` | **MISSING** | REUSE-STMT **with a shape mismatch to fix.** `Q: Legacy/Combiner.lean:44` `IsCombiner` is LM20 Def 14 — "*ideal when **all** components are ideal*" — which is the `𝒜 = {1ⁿ}` special case, **not** the thesis's monotone-set-indexed definition. The `⟨F/I⟩_{bⁿ}` mixed-tuple notation has no quarry counterpart at all. delta `both` (+ statement generalization) |
| 2.43 | 31 | Def | `(k,n)`-combiner: an `𝒜`-combiner with `{bⁿ \| Σbᵢ ≥ k} ⊆ 𝒜` | **MISSING** | REUSE-STMT — `Q: Legacy/Combiner.lean:61` `IsThresholdCombiner` is this, phrased over a `Finset (Fin n) J` with `k ≤ J.card`; `:75` `threshold_combiner_is_combiner`. Closest thesis match in the whole of L5. delta `both` |
| 2.44 | 32 | Lem | the blinding lemma: `Adv(C(F),C(I)) ≤ B(0ⁿ)⁻¹ · Σ_{e∈{0,1}ⁿ} δ(blind(B,e), blind(B′,e))·Pr(E = e)`, for probability laws `B, B′` on `𝒜 ∪ {0ⁿ}` with `B(0ⁿ)>0`, `B′(0ⁿ)=0` | **MISSING** | **NONE** — no `blind` operation on multisets/tuples, and no quarry statement of this shape |
| 2.45 | 34 | Thm | `(k,n)`-combiner amplification: `Adv ≤ Σ_{i=n−k+1}^{n} ζ_{i−(n−k),i}·Pr(Σ_{j} E_j = n−k+1)` with `ζ_{l,m} = ½(1 + Σ_{j=l}^{m} C(m,j)C(j−1,l−1))` | **MISSING** | **REF-ONLY, and a trap.** `Q: Legacy/Amplification.lean:57` `amplification_theorem` is LM20 **Theorem 3**, a *different* statement (`Adv ≤ C(n,k−1)·εᵏ`, no `ζ`, no Bernoulli sum), it takes the black-box reduction as an **explicit hypothesis**, and **its `k ≥ 2` branch is `sorry` at `:119`**. `Q: Legacy/Amplification.lean:127` `amplification_theorem_k1` (`≤ n·ε`) and `:165` `threshold_combiner_bound_1_2` (`≤ 2ε`) are independently proved but are plain hybrid bounds — **not amplification** (no exponent in ε). **Nothing here may be forwarded as evidence for Theorem 2.45.** |
| 2.46 | 36 | Cor | (i) `2^{n−k}Σ_j C(j−1,n−k)Pr(ΣEᵢ=j)`; (ii) `½C(n,k−1)(2ε)^{n−k+1}`; (iii) `(2e·n/(n−k+1)·ε)^{n−k+1}` | **MISSING** | **NONE** for the bounds. The one reusable *fragment* is the binomial identity `Σ_{j≥m} C(j,m)C(n,j)εʲ(1−ε)^{n−j} = C(n,m)εᵐ` proved in the source by `E[C(X,m)]`; the current tree has `Distribution.expect` (`AC: Probability/Expectation.lean:65`) and `Distribution.prod`/`iidPow` (`Distribution.lean:1356,1422`), and the quarry has `Q: Counting.lean` for the surrounding inequalities, but the identity itself is nowhere |
| U6 | 38 | Unn | a simple `(k,n)`-combiner for random functions: `C(x) := A·xᵀ` for an MDS matrix `A ∈ 𝔽^{k×n}`; hence `Adv((F′₁,…,F′ₖ), Rᵏ) ≤ ½C(n,k−1)(2ε)^{n−k+1}` | **MISSING** | REF-ONLY — the nearest quarry object is `Q: KWiseIndepPoly.lean:197` `kIndepRV_polyEval` (`k`-wise independence from polynomial evaluation over an arbitrary finite field, CR18 §6.1.2), which shares the "linear-algebraic combiner over a finite field" genre and the `k ≤ \|F\|` side condition — but a Vandermonde/Cauchy matrix is a *different* object from an MDS `k×n` matrix and no MDS predicate exists. delta `none` (pure algebra) |
| 2.47 | 39 | Lem | quasigroup sharing construction: partition `n` systems into `m+1` sets, combine with `⊙`; `Adv(C(Q),Uⁿ) ≤ m(m+1)/4·(2ε)^{2n/(m+1)}` | **MISSING** | **NONE** — no quasigroup structure in the quarry |
| 2.48 | 41 | Def | for a monotone `ψ : {0,1}ⁿ → {0,1}`, the MC `ψ_{A₁..ₙ}(x̂) := ψ(A₁(x̂\|₁),…,Aₙ(x̂\|ₙ))` and the ψ-parallel composition `[s₁,…,sₙ]^{ψ_{A₁..ₙ}}` | **MISSING** | REUSE-STMT — the two halves exist separately and have never been combined: parallel composition `Q: PFunDDS.lean:577` with its projection `restrict` `:471`, and the MBO carriers `Q: PDS.lean:3045,3101`. The composite MC is not defined anywhere. delta `carrier` |
| 2.49 | 41 | Cor | `ω([S₁,…,Sₙ]^{ψ}) = Pr(ψ(B₁,…,Bₙ)=1)` with `Bᵢ` independent Bernoulli of parameter `ω(Sᵢ^{Aᵢ})` — the exact winnability of an arbitrary monotone combination of parallel games | **MISSING** | **NONE** for the statement, **REUSE-ARCH for its two inputs**: `ω` is `Q: GameWinnability.lean:294` and Theorem 2.37 is `:778`; the proof is `≤` by picking each sub-game's minimal representative and `≥` by playing independently, then Theorem 2.37. Independent-Bernoulli machinery: the current tree has `Distribution.prod`/`iidPow` but no Bernoulli vector; `Q` has none either. delta `carrier` |
| A.1 | 88 | Lem | (cf. MPR07 Lemma 3) `Adv(⟨S/T⟩_B, T) = B(0)·Adv(S,T)` for a probability law `B` on `{0,1}` — the exact scaling of the advantage under a two-point mixture | **MISSING** — the tree has only the inequality direction, `advFullyDefined_sum_le` (`AC: Environment.lean:710`) | REF-ONLY — `Q: Distinguishing.lean:187` `advantage_eq_expect_single` and `Q: MaxWinProb.lean:156` `winProb_eq_expect_single` are the linearity facts A.1 is built from, both hypothesis-free; A.1's *equality* (which needs the `sSup` to commute with the scaling) is not stated. delta `both` |
| A.2 | 88–89 | Lem | `ζ_{l,m} = 2ζ_{l,m−1} + ζ_{l−1,m−1} − 1`, and `2^{m−l}C(m−1,l−1) ∈ [ζ_{l,m}, 2ζ_{l,m}−1]` | **MISSING** | **NONE** — pure binomial recursion, nothing analogous in the quarry. delta `none` (would be written from scratch, carrier- and metric-free) |

**L5 tally: 16 items — 1 DONE (2.13), 0 PARTIAL, 15 MISSING; quarry 1 REUSE-ARCH(partial, for 2.49's inputs), 4 REUSE-STMT, 4 REF-ONLY, 7 NONE.**
**L5 is the only leg where the quarry is nearly empty**, and it is also the leg where **pin 3 disqualifies the core**: Definitions 2.41–2.43 and Theorem 2.45 are statements about a construction `C` wiring component systems, which is attachment and therefore MR16-track work.

---

# Aggregate tally

| leg | items | DONE | PARTIAL | MISSING | PROSE | REUSE-ARCH | REUSE-STMT | REF-ONLY | NONE |
|---|---|---|---|---|---|---|---|---|---|
| L0 | 14 | 11 | 1 | 1 | 1 | 0 | 2 | 11 | 1 |
| L1 | 4 | 1 | 2 | 1 | 0 | 2 | 2 | 0 | 0 |
| L2 | 4 | 0 | 0 | 4 | 0 | 3 | 1 | 0 | 0 |
| L3 | 9 | 1 | 4 | 4 | 0 | 7 | 1 | 1 | 0 |
| L4 | 10 | 0 | 0 | 10 | 0 | 9 | 0 | 0 | 1 |
| L5 | 16 | 1 | 0 | 15 | 0 | 1 | 4 | 4 | 7 |
| **total** | **57** | **14** | **6** | **36** | **1** | **22** | **10** | **16** | **9** |

Read the two halves together: **42 of 57 obligations are open** (MISSING or PARTIAL), and **31 of those 42 have a REUSE-ARCH or REUSE-STMT verdict** — the quarry already contains a finished proof or a usable statement shape for three quarters of the open work.  The residue with no quarry support is concentrated almost entirely in L5.

---

# Pin conflicts — what the quarry contains that must NOT be transplanted as-is

Nine hazards, each verified in the quarry source.

1. **`Δ(S, T)` means `maxAdvantage`, not `classDistance`.**  In the quarry, `Δ(·,·)` **with parentheses** is `sSup` over probability *distinguishers* of the signed `verdictProb D T − verdictProb D S` (`Q: Distinguishing.lean:136,139`), while the class distance is `Δ S T` **without** parentheses (`Q: RandomSystem.lean:8358`).  The current tree binds `Δ(S, T)` to `classDistance` (`AC: ClassDistance.lean:149`).  A verbatim copy silently changes the theorem.

2. **`maxAdvantage` is forbidden by pin 2, and it is load-bearing across the quarry.**  `Q: CompatibleMetric.lean:1358` (eq. (4), non-expansion), `:1396` (eq. (3)), `:1421` (symmetry), `Q: RandomSystemMetric.lean:59` (the `MetricSpace` instance), `Q: AbsorbDPI.lean:991,2240` (converter DPI), `Q: SwitchingLemma.lean:1864`, `Q: CBCMAC.lean:1077,1103`, `Q: GameOf.lean:1431,1472` are all stated on it.  Each is a *statement-shape* asset only; the metric must be re-based on `advFullyDefined`.

3. **`maxEDist` is forbidden by pin 2, and the quarry itself records that it is strictly weaker.**  `Q: StrictContext.lean:158` defines it; `Q: StrictContextAdvantage.lean:403` proves `maxEDist ≤ ofReal Δ(·,·)` **unconditionally**, with equality only on total laws (`Q: StrictContextTotal.lean:474`) or on the shared-domain subcarrier (`Q: StrictContextSharedDomain.lean:934`).  `Q: StrictParallel.lean`'s header states the consequence outright: *"the strict metric is only bounded by `Δ` (`AttainmentCounterexample` refutes the converse), so Maurer's eq. (3) for `Δ` transfers nothing to `maxEDist`."*  Do not import any `StrictContext*` or `StrictParallel` statement into this matrix's work.

4. **The `Adv` ↔ `Δ(·,·)` orientation is forced and counter-intuitive.**  `Q: RandomSystem.lean:1830` `adv_eq_maxAdvantage_swap` proves `Adv S T = Δ(T, S)` — arguments **swapped** — and its docstring records that the naive pairing `Adv S T = Δ(S, T)` is *refutable* (at `S = 0`, `Adv 0 T = 0` while `Δ(0, T)` is `T`'s weight).  Any transplant that guesses the orientation gets a false statement.

5. **Legacy `advantage` is NON-ADAPTIVE and is not Definition 2.26.**  `Q: Legacy/Advantage.lean:62` is a `Finset.sup` over *fixed input tuples*; the adaptive one is the separate `advantageAdaptive` `:84`, and `advantage_le_advantageAdaptive` `:229` is only `≤`.  Every `Legacy/` theorem naming `advantage` — including `Legacy/FundamentalTheorem.lean:216` `delta_eq_advantage` ("Theorem 1") — is therefore about the weaker quantity.

6. **Three live `sorry`s.  None may be forwarded as evidence.**  `Q: Legacy/FundamentalTheorem.lean:172` (the successor branch of Theorem 1 — so `delta_le_advantage` `:189` and `delta_eq_advantage` `:216` are *not* proved); `Q: Legacy/Amplification.lean:119` (the `k ≥ 2` branch of Theorem 3 — so `amplification_theorem` `:57` is *not* proved); `Q: CBCStructureGraph.lean:1415` (`mass_cbcGraphBad_le`, whose own docstring flags that the stated constant is unreachable by the intended union bound).  The live-carrier attainment results (`BoundedAttainment`, `RandomSystemCoupling`, `GameWinnability`, `MultiSystemCoupling`, `Example216`, `ThesisModel`, `LanzenbergerChain`) are `sorry`-free at source level; note that **none of the four surveys ran `#print axioms`**, so "axiom-clean" is not established, only "no source-level `sorry`/`axiom`".

7. **Pin 3 disqualifies the converter-attached quarry assets.**  `Q: AbsorbDPI.lean` (the whole DPI development), `Q: CompatibleMetric.lean:1358` eq. (4), `Q: CBCMAC.lean`, and — decisively — thesis Definitions 2.41–2.43 and Theorem 2.45 are statements about attaching a construction to component systems.  They belong to the MR16 attachment track (`attachEngineFully`), not here.

8. **Two source errata must travel with the L2 transplant.**  (a) Definition 2.27/2.28's inner `inf` over representatives is wrong; the quarry keeps the verbatim display as `Q: LanzenbergerChain.lean:366` `printedMultiSystemDistance` and *refutes* it with `Q: Example216.lean:591` `definition_2_28_printed_displays_disagree`, using the corrected `sup` form `:350` everywhere else.  (b) Theorem 2.29's printed `min_{i≠j}` in the upper bound should be `max`; refuted by `Q: MultiSystemCoupling.lean:958` `printed_min_form_counterexample`.  Transplanting the printed forms imports two false statements.

9. **Attainment is FALSE without the finiteness bundle, on exactly the presentation the current tree uses.**  `Q: AttainmentCounterexample.lean:766` refutes `Δ = Adv` unrestricted, and the mechanism is CR18 Def 3.3 — a rejected query is a *visible* `⊥` deleted only from the DDS-side history, giving the environment a free domain probe.  `PDS.advFullyDefined` is built on precisely that presentation (`DDE.Total.transcript` over `s⊥`).  **Theorem 2.31 must therefore be stated with `HasFixedDomain` + `QBounded` + finite `X`; an unrestricted statement should be expected to be false, not merely unproved.**

**One further definitional decision the quarry forces into the open.**  The quarry's `Δ` (`Q: RandomSystem.lean:8358`) quantifies over **non-negative** representatives only; the current tree's `classDistance` (`AC: ClassDistance.lean:143`) is unrestricted.  On the signed carrier these are different infima.  Pick one before any L3 statement is written.

---

# RECOMMENDED ORDER

**L1 → L2a → L3 → L4 → (L2b in parallel) → L5-residue.**

**1. L1 (equivalence + non-adaptive reduction) — first, and cheap.**
Four items, every one with a finished quarry proof, and the leg where the current tree is already closest (Def 2.17 is `DONE`).  Two of its assets are prerequisites for everything after it: `Q: ThesisModel.lean`'s `equivalent_iff_thesisEquivalent` `:786` / `adv_eq_thesisAdv` `:847` are the **`Adv` ↔ `Adv⊥` coding map**, which the tree's own queued note names as blocking gap (iii) of Theorem 2.31; and `Q: LanzenbergerChain.lean:160`'s "fixed transcript event = fixed query event" device is the replay step Lemma 2.18 needs.  Doing L1 first converts the pin-2 metric from an *unrelated* object into Definition 2.26 proper, which is what makes every later statement citable against the thesis.

**2. L2a (the finite slice: 2.9's finiteness clause + U5's query ruling) — the gate.**
Not a leg so much as an entry condition.  The current tree has `QBounded` with **zero call sites** and no `Fintype` on any system carrier.  The quarry's answer is decisive and cheap to copy: **do not build a subtype — bundle the hypotheses**, exactly as `Q: BoundedAttainment.lean:90` `HaveCommonDomainAndBounded` does (`[Fintype X]` + `HasFixedDomain … D` + `QBounded D q`).  Nothing in L3 or L4 can be *stated correctly* until this exists, because of pin conflict 9.

**3. L3 (attainment) — the largest payoff, and it must come third.**
Nine items, seven REUSE-ARCH, and the whole leg is finished in the quarry: Lemma 2.33's ~1300-line apparatus (`Q: RandomSystem.lean:4113`), Notation 2.34's successor calculus with the weight identity (`Q: RandomSystem.lean:2169` + `Q: BoundedAttainment.lean:254,539,584,1129`), the branch-additivity form of Lemma 2.5 (`Q: TranscriptBranchDistance.lean:35`), the query induction (`Q: BoundedAttainment.lean:751`), Theorem 2.31 (`:1106`) and Theorem 2.32 (`Q: RandomSystemCoupling.lean:112`).  It depends on L1 (the coding map) and L2a (the hypothesis bundle) and on nothing else.  Budget it as the long leg: every piece needs re-basing onto `PDS X Y = Distribution (System.DDS X Y)` and onto `advFullyDefined`.

**4. L4 (games and winnability) — short *if* it comes after L3.**
Ten items, nine REUSE-ARCH, no home in the current tree (three empty stubs).  The choice that determines its cost is which proof of Theorem 2.37 to take: the quarry's self-contained induction (`Q: GameWinnability.lean:778`) repeats L3's successor machinery, whereas the thesis's **alternative proof (U4)** derives 2.37 from Theorem 2.31 through the always-lose twin `V` — and the quarry already has both halves of that reduction (`Q: GameWinnability.lean:356,374,747,737`).  Sequenced after L3, L4 is a reduction; sequenced before it, L4 is a second induction.  Sequence it after.

**5. L2b (multi-system Δ: 2.27, 2.29, 2.30) — parallelizable, low priority.**
Genuinely independent: `Q: MultiSystemCoupling.lean` is on plain `Dist A` with no system content and no metric, so its transplant delta is `none` for the combinatorial core.  Nothing in L3, L4 or L5 consumes it.  Hand it to a separate worker at any time — but ship the two errata (pin conflict 8) with it, since the printed statements are false.

**6. L5 (applications) — last, and mostly out of scope.**
Sixteen items, seven with no quarry support at all, and **pin 3 removes its core**: Definitions 2.41–2.43 and Theorem 2.45 are attachment statements that belong to the MR16 track.  What genuinely remains inside this matrix is a short tail — Definition 2.48's composite MC, Corollary 2.49 (a two-line consequence of Theorem 2.37 once L4 exists), and Lemma A.2's binomial recursion (carrier-free, writable from scratch).  Everything else in L5 should be recorded as deferred rather than scheduled.

**Dependency summary.**

```
L1 ──┬─────────────► L3 ──► L4 ──► (2.49 tail of L5)
     │              ▲
L2a ─┴──────────────┘

L2b  (independent; no consumer)

L5 core (2.41–2.43, 2.45)  ──► MR16 attachment track, not this matrix
```

# TECHNIQUE-PROGRAM SURVEY MATRIX

Charter: LEDGER.md SCOPE AMENDMENT (Marc, 2026-08-18b) — the technique program is
opened.  Four techniques integrated as MODELING (first-class objects) + PROOF
TECHNIQUE (bound theorems against `Adv⊥`/`classDistance` + application kits).
This document is the from-disk inventory that prices the integration.

* Target tree (**AC**): `/Users/marcilunga/Documents/tob/research/abstract-crypto`
* Quarry (**Q**, READ-ONLY): `/Users/marcilunga/Documents/tob/research/random-systems`
* Papers (visual reads only): `Q:papers/`

Status: SURVEY.  Nothing here is a landed statement; every "verdict" is a claim
about what transplants, in the LEDGER "quarry rule" sense.

---

## Verdict tally (38 rows)

| technique | PRESENT | TRANSPLANT | MODEL-NEW | BLOCKED-ON | other | rows |
|---|---|---|---|---|---|---|
| **T1** conditional equivalence + MBO | 0 | 6 (+1 partial) | 2 | 1 | 1 REF-ONLY | 11 |
| **T2** MPR07 Lemma 5 (completeness) | 0 | 1 | 2 | 0 | 1 PARTIAL, 1 out-of-scope | 5 |
| **T3** game winnability | 0 | 5 (+1 hybrid) | 4 | 0 | — | 9 |
| **T4** H-coefficient | **3** | 7 | 1 | 2 | — | 13 |
| **total** | **3** | **19** | **9** | **4** | 3 | **38** |

**Headline reading.** The program is dominated by **TRANSPLANT** (19/38): the
mathematics exists and is sorry-free in the quarry, and the cost is re-basing
statements onto `Adv⊥`/`Δ` and the fully-defined carrier — not new proofs.  Only
**T2 is genuinely MODEL-NEW** (the quarry has ingredients but never states MPR07
Lemma 5), and only **T4 has anything already PRESENT** — its entire distribution-level
kernel is landed in `AC:Probability/StatisticalDistance.lean`.

## 0. Binding context read before this survey (LEDGER + PHI-SPEC)

| ruling | content | consequence for the technique program |
|---|---|---|
| R1 | `Φ := PDS Uni Uni`; the official carrier is the **fully defined slice**; partial systems enter via `s⊥`; deletion is the embedding's shape, not an interaction rule (`AC:PHI-SPEC.md:14-18`) | every quarry technique statement conditioned on a *partial* domain must be re-read (§CONFLICTS) |
| R2 | refusal is observable (`⊥ = none`) and **non-fatal**, for every system incl. converters (`AC:PHI-SPEC.md:19-21`) | the MBO bit must survive `⊥`-completion; the CE conditioning event lives on completed transcripts |
| R3 | addressing is exogenous: an interface is a `Set Uni`; ownership never inferred from domains | games/blinders are not interface objects — technique work is converter-free (pin 3) |
| R4 | statement-facing metric is `Adv⊥ = PDS.advFullyDefined` (`AC:RandomSystems/System/Environment.lean:751`), notation `Adv⊥(S,T)`; `maxAdvantage`/`maxEDist` are FORBIDDEN statement targets (pin 2) | **every** technique's main bound must land on `Adv⊥` or `Δ`, never on the quarry's `Δ(S,T) = maxAdvantage` |
| R4′ | both presentations first-class: `equivalent` (Def 2.17, `ClassDistance.lean:1322`), `classDistance` (Def 2.28, `ClassDistance.lean:1546`), `Adv⊥ ≤ Δ`, coupling bounds land on `Adv⊥`; domain-indexed strict layer `HasDomain`/`CompatibleD`/`AdvD` | techniques may target either, and the crossing API already exists |
| R9 | `classDistance` infimizes over **honest (NonNeg)** representatives; signed representatives are proof tools only | the quarry's `infWinnability` already writes the `NonNeg` conjunct — see T3 |
| SOURCE HIERARCHY | MauRen16 > Jost > LiuMau20 > Lanzenberger; **CR18 DEMOTED** to fallback-only, and only for a concept no primary covers (`AC:LEDGER.md:7-15`) | **the single largest re-basing cost of this program**: the quarry's CE/MBO/game development is presented as *CR18 Defs 4.15–4.19 / Thm 4.17*.  Lanzenberger Ch.2 §2.3.3/§2.4.3 and Maurer02 §4 are the primary-source presentations that must carry the AC statements; CR18 numbering may survive only as historical provenance in docstrings |
| naming (3 layers) | paper names first; mathlib grammar; RS house patterns; a non-paper name is a flagged COINAGE | `massYAfalse`, `blindMaxWinProb`, `zeroMBO`, `prewinBehavior` are quarry coinages and must be re-named or flagged |
| escalation filter | a fork goes to Marc only after checking the PRIMITIVE REGISTRY and the rulings (`AC:LEDGER.md:672-676`) | every CONFLICT below is *flagged*, not resolved, per this brief |

**Correction to the charter's shorthand.** The brief (and this document's first
draft) says "the new rulings **R1–R9**".  `AC:PHI-SPEC.md` in fact names
**R1, R2, R3, R4, R4′, R7″, R8, R9** — there is no R5 and no R6.  "R1–R9" is a
range, not an enumeration; a re-based skill must list the eight actual rulings.

**LEDGER line-number drift (from-disk finding).**  LEDGER pin 2 cites
`PDS.advFullyDefined` at `Environment.lean:636` and `trLawFullyDefined` at `:627`;
on disk today they are at **`:751`** and **`:742`**, and `PDS.Adv` is at **`:324`**
(pin 2 says `:251`).  The definitions are unchanged; only the offsets moved.  The
matrix below cites from-disk lines.

---

## SOURCE-IDENTITY CORRECTION (affects the charter's T1/T3 source list)

Verified visually, and it changes two rows of the brief:

1. **`Q:papers/LanMau20.pdf` is Lanzenberger & Maurer, "Coupling of Random Systems"
   (TCC 2020), 34 pp., printed folio = PDF page.**  Its **§4 is "Coupling Theorem
   for Discrete Systems"** — Defs 10–12, Theorem 1 (Δ = Adv + attainment),
   Theorem 2 (Coupling Theorem), Lemma 6, Notation 2.  It contains **no games, no
   monotone conditions, no winnability, no ν/ω, and no MPR07 representative
   remark**.  The charter's "LanMau20 §4 = the condensed games/winnability form"
   and "LanMau20 pdf pp. 8, 20" premises do not hold for this file.  The overlap
   with the thesis is verbatim: LanMau20 Def 10/Lemma 5/Not. 1/Def 11/Def 12/Thm 1/
   Thm 2/Lem 6/Not. 2 = thesis Def 2.17/Lem 2.18/Not. 2.19/Def 2.26/Def 2.28/
   **Thm 2.31**/**Thm 2.32**/Lem 2.33/Not. 2.34, with **no** changed hypothesis and
   **no** renamed object.  The thesis is a strict superset (it adds Def 2.27/
   Thm 2.29/Lem 2.30 and the entire games layer).
   *Consequence:* **the games/winnability development exists ONLY in the thesis**
   among the two files on disk.  T3's primary source is thesis §2.3.3 + §2.4.3, full stop.
   (The token `blind` occurs 23× in LanMau20 but is a *helper function* in its §5
   amplification proof — `blind(x,m)` deletes coordinates where `mᵢ = 0`.  It is
   unrelated to any blinder object.  Do not let the name collide with the quarry's
   `blindMaxWinProb`.)

2. **There is no "blinder" object anywhere in thesis Ch. 2.**  §2.3.3's numbered
   items are exactly Defs 2.20, 2.21, 2.22, Remarks 2.23, 2.24, Def 2.25; §2.4.3's
   are exactly Defs 2.35, 2.36, Thm 2.37.  "Def/Lemma 2.38" does not exist (2.38 is
   an unrelated Example in §2.5.1).  The nearest object is the **unnamed always-losing
   system `V`** inside the *alternative* proof of Thm 2.37 (printed p. 26) — which is
   exactly what the quarry named `zeroMBO` / `zeroMBODist`
   (`Q:RandomSystems/GameWinnability.lean:356,374`).  **`zeroMBO` is therefore a
   COINAGE under the naming ruling and must be flagged as one.**

3. **A game is NOT defined as a system over `Y × {0,1}`.**  Thesis Def 2.20:
   *"A monotone condition (MC) for an (X,Y)-DDS `s` is a monotone predicate
   `A : X* → {0,1}`.  A deterministic discrete (X,Y)-game is a pair `(s, A)`,
   denoted `s^A`."*  The MC reads **only the input sequence**.  The `Y × {0,1}`
   presentation appears once, inside the alternative proof of Thm 2.37, as a derived
   construction.  Maurer13b Def 9 (printed p. 3152) is where `Y × {0,1}` *is* the
   definition.  **This is the T3 design fork** (§T3 row "carrier shape").

---

# SOURCE LEDGER (visually verified; every row read from rendered pages)

Pagination anchors, verified: **CR18_LN.pdf** PDF page *N* holds printed *2N−13* /
*2N−12* (printed *P* → PDF ⌊(P+13)/2⌋).  **MaPiRe07.pdf** PDF *Q* = printed *129+Q*.
**Maurer13b.pdf** PDF *Q* = printed *3149+Q*.  **Maurer02.pdf** is the **ETH
preprint**, self-numbered 1–23 — *not* the LNCS 2332 pp. 110–132 pagination
(LNCS ≈ preprint + 109).  **Maurer09c.pdf** is 2 pages, printed 44–45.
**thesis (1).pdf** printed *P* = PDF *P+10*.

## The four presentations of the same technique, side by side

| concept | Maurer02 (preprint) | MPR07 | Maurer13b | CR18 §4.10-4.11 | thesis Ch. 2 |
|---|---|---|---|---|---|
| the condition | MES `𝒜 = A₀,A₁,…`, **`Aᵢ = 1` means SATISFIED (good)**; p. 7 §3.2 | MBO, **`Aᵢ = 1` means WON (bad)**; Def 9, p. 138 | MBO / **game**; Def 9, p. 3152 | MBO / **DDG**; **Def 3.22, p. 71** (not in §4.10-4.11) | MC `A : X* → {0,1}`, **input-only**; Def 2.20, p. 16 |
| the object | `F^𝒜` (system + MES) | `(𝒳,𝒴×{0,1})`-system | `(𝒳,𝒴×{0,1})`-system | `(X, Y×{0,1})`-DDS | **pair** `s^A = (s, A)` |
| stripped | — | `S⁻` (Def 9(i)) | `S⁻` (Def 12, p. 3153) | `S⁻` (**Def 4.18, p. 107**) | — |
| masked | — | `S⊣` (Def 9(ii)) | — | — | — |
| "same until won" | `F^𝒜 ≡ G^ℬ` (Def 5, p. 7) — *stronger* | **restricted equivalence** `S⊣ ≡ T⊣` (Def 10, p. 138) | `≡ᵍ` (Def 11, p. 3153) | **pre-winning behaviour** (Def 4.15) + `≡ᵍ` (**Def 4.16, p. 105**) | game equivalence (Def 2.22) |
| **CE** | `F\|𝒜 ≡ G` (**Def 6, p. 8**), one-step `p_{Yᵢ\|Xⁱ Y^{i−1} Aᵢ}` | — | `S\|𝒜 ≡ T` (**Def 13, p. 3153**), joint `p_{Yⁱ\|Xⁱ, Aᵢ=0}` | `S ⊫ T` (**Def 4.19, p. 108**), joint `p_{Yⁱ\|Xⁱ, Aᵢ=0}`, eq. (4.38) product form | — |
| winning prob | `ν` adaptive, `μ` non-adaptive (Def 11, p. 11) | `ν_k^D`, `ν_k^𝒟`, `ν_k^NA` (Def 11, p. 139) | `Γ_q^W`, `Γ^𝒲` (Def 10, p. 3152) | `Ḡ(W)` eq. (4.37); **`Γ(G) := sup_W Ḡ(W)`** (Def 4.17, p. 106) | `ν` (Def 2.25), `ω` (Def 2.36) |
| **how blindness is rendered** | a *separate* quantity `μ` = max over `x^k` | superscript `NA` on the class | the **operator `⟦DT⟧`** (p. 3152): D runs against `T`, its queries echoed, replies ignored | a **BLOCKING CONVERTER `b`** (**Def 4.20, p. 109**): `Γ(bŜ)`; plus `T̃` (Def 4.21) | Rem 2.23: the environment *never sees* the bit — blind **by definition** |
| **main theorem** | **Thm 1, p. 12**: `F^𝒜≡G^ℬ` or `F\|𝒜≡G` ⟹ `Δ_k(F,G) ≤ ν(F, Ā_k)` — **ADAPTIVE RHS** | Lem 4, p. 139 (easy dir.); **Lem 5, p. 140 (converse)** | **Thm 3, p. 3154**: `Ŝ\|𝒜≡T` ⟹ `Δ_q^D(S,T) ≤ Γ_q^{⟦DT⟧}(Ŝ)`, in particular `Δ_q(S,T) ≤ Γ_q^{NA}(Ŝ)` — **NON-ADAPTIVE RHS** | **Thm 4.17, p. 110**: `Ŝ ⊫ T` ⟹ `⟨S\|T⟩ ≤ b̄Ŝ ∘ ρ^{T̃}`, in particular **`Δ(S,T) ≤ Γ(bŜ)`** — **NON-ADAPTIVE RHS** | Thm 2.37 `ν = ω`, p. 26 |

### Verbatim anchors worth pinning

* **CR18 Def 4.19** `[printed p. 108 / PDF 60]`: `S ⊫ T` iff `p^S_{Yⁱ | Xⁱ, Aᵢ=0} = p^T_{Yⁱ | Xⁱ}` for `i ≥ 1`; product form **eq. (4.38)** `p^S_{Yⁱ, Aᵢ=0 | Xⁱ} = p^S_{Aᵢ=0|Xⁱ} · p^T_{Yⁱ|Xⁱ}`.  The notes then say `T` *is* `S⁻`, and read CE as **factorization**: `S` splits into a `Y`-component and an *independent* MBO component while the MBO is 0.
* **CR18 footnote 29** `[p. 108]`: "Two conditional probability distributions are considered to be equal if they are equal for all arguments for which they are both defined."  This is exactly what the quarry's cross-multiplied `CondEquiv` honours (`Q:CondEquiv.lean:25`).
* **CR18 Lem 4.16** `[p. 107]`: `S ≡ᵍ T ⟹ ⟨S⁻|T⁻⟩ ≤ S̄` — pointwise in `D`, adaptive, **one-sided** (`⟨S|T⟩(D)` is the *signed* `Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`, and `Δ := sup_D`, not a sup of an absolute value).
* **CR18 Thm 4.17 proof** `[p. 110]`: enhance `T` by `p^T̂_{Yⁱ Aᵢ | Xⁱ} = p^T_{Yⁱ|Xⁱ} · p^Ŝ_{Aᵢ|Xⁱ}`, i.e. **`T̂`'s MBO depends only on the inputs**; then `Ŝ ≡ᵍ T̂` (4.39), `T̂ = T̃ b Ŝ` (4.40), and absorb `T̃` into the winner.  *That input-only enhancement is precisely what converts an adaptive distinguisher into a blind winner.*
* **CR18 §4.10 standing simplification** `[p. 105]`: environments stop after finitely many queries, `q` an upper bound, and **short runs are padded with dummy queries** so transcripts are fixed-length `(X^q, Y^q)`.  **There is no `⊥`, no refusal, and no partial-domain apparatus in §4.10-4.11 at all.**
* **MPR07 Lemma 5** `[printed p. 140 / PDF 11]`: *for any two `(𝒳,𝒴)`-systems `S` and `T` there exist `(𝒳, 𝒴×{0,1})`-systems `Ŝ`, `T̂` with MBOs such that* (i) `Ŝ⁻ ≡ S`, (ii) `T̂⁻ ≡ T`, (iii) `Ŝ⊣ ≡ T̂⊣`, (iv) **`δ_k^D(S,T) = ν_k^D(Ŝ) = ν_k^D(T̂)` for all `D`**.  Footnote 16: this also gives `Δ_k(S,T) = ν_k(Ŝ)` and `Δ_k^NA(S,T) = ν_k^NA(Ŝ)`.
  Quantifier order **`∀ S,T ∃ Ŝ,T̂ ∀ D`** — one condition works uniformly for every distinguisher.
  Construction `[p. 141, eq. (4)]`: `m_{xⁱ,yⁱ} := min(p^S_{Yⁱ|Xⁱ}, p^T_{Yⁱ|Xⁱ})`, `p^Ŝ_{Yⁱ Aᵢ|Xⁱ}(yⁱ,0,xⁱ) := m`, `(yⁱ,1,xⁱ) := p^S − m` — **maximal coupling**, and it runs on **eq. (3)** `δ(P,Q) = 1 − Σₓ min(P(x),Q(x))` `[p. 140]`.
  Tightness claim `[p. 133]`: "This paper settles a main open problem from [MP04], as **Lemma 5 is tight**."
  Coupling reading `[p. 142]`: "For any distinguisher `D`, two random systems `S` and `T` are equal with probability `1 − δ`."

### Three findings that change how T1/T2 must be stated

**F1 — the comparison quantity in MPR07 Lemma 5 is `δ` (transcript distance), not `Δ` (advantage).**
`[MPR07 p. 140]`: "in general `Δ_k^D(S,T) ≤ δ_k^D(S,T)`, but for a computationally unbounded `D` that chooses the output bit optimally, `Δ_k^D = δ_k^D`.  In particular `Δ_k = δ_k` and `Δ_k^NA = δ_k^NA`."  The per-`D` equality is with `δ`; the equality with `Δ` needs the maximisation.  **AC is on the right side of this**: `Adv⊥` is *defined* as a sup of `statDist` of transcript laws (`AC:Environment.lean:751`) — i.e. it is a `δ`-shaped object already, and the `Δ`/`δ` gap MPR07 flags does not arise.  A transplant that stated Lemma 5 against a verdict-probability advantage would import a hypothesis AC does not need.

**F2 — "optimal failure condition" is not MPR07's phrase, and there is no `S^A` notation in MPR07.**
The paper's own framing is "**Lemma 5 is tight**" and the *converse* of Lemma 4.  `S^A` is Maurer02's `F^𝒜`.  The charter's T2 title should be read as naming the *concept*, not quoting the source.  Corrected naming for the AC row: **MPR07 Lemma 5 (tight MBO existence / converse of the bad-event bound)**.

**F3 — the completeness lemma lives on equivalent representatives of BOTH systems, and the representative is genuinely non-unique.**
`[MPR07 p. 133, §1.3]` verbatim: "For two systems `S` and `T` one can always define **new systems** `Ŝ` and `T̂`, which are **equivalent** to `S` and `T`, respectively, but have an additional monotone binary output (MBO), such that (i) … the distinguishing advantage … is equal to the probability that `D` sets the MBO to 1 in `Ŝ` (or `T̂`), and (ii) `Ŝ` and `T̂` are equivalent as long as the respective MBOs are 0."
And `[p. 141]`: "(4) only determines the interrelation between the system's output `Yᵢ` and the value `Aᵢ` of the MBO **at the same step**, but it does **not specify the dependency on previous values `A^{i−1}`**.  In fact, there are various degrees of freedom in the definition of `Ŝ`…"  (the free `r_{xⁱ,yⁱ}` parameters, constrained by eq. (5)).
Maurer09c `[printed p. 45]` restates this informally, verbatim the same sentence with `F,G` for `S,T` — **it is a restatement, not independent evidence**, and it drops MPR07's `δ`-vs-`Δ` qualification.
**This confirms the prior repository note's caveat, and sharpens it**: the freedom is not merely "some equivalent representative" but (a) the joint law of `(Yⁱ, Aⁱ)` — *new data not present in `S` at all* — and (b) the `r`-parameters.  Since a random system *is* its behaviour (MPR07 Def 2/3), `Ŝ⁻ ≡ S` is as strong as equality **at the level of random systems**; the representative freedom is entirely in the adjoined data.  In AC this lands exactly on the `Behaviour` quotient (`AC:Behaviour.lean:151`) — the statement is naturally `∀ B C : Behaviour X Y, ∃ …`, and the non-uniqueness is *expected*, not a defect.

### Cross-source traps (must be in any transplant brief)

1. **POLARITY FLIP.**  Maurer02's `Aᵢ = 1` = condition **satisfied** (good), failure is `Āᵢ`.  MPR07 / Maurer13b / CR18: `Aᵢ = 1` = game **won** (bad).  Maurer02's `Aᵢ` ≙ Maurer13b's `{Aᵢ = 0}`.  Transcribing between papers requires flipping the bit.  *The quarry follows the CR18 polarity* (`false = 0 = not won`, `Q:CondEquiv.lean:16`) — so a Maurer02-sourced statement must be flipped before comparison.
2. **CE is not one relation.**  Maurer02 Def 6 is the **one-step** form `p_{Yᵢ|Xⁱ Y^{i−1} Aᵢ}`; Maurer13b Def 13 and CR18 Def 4.19 are the **joint** form `p_{Yⁱ|Xⁱ, Aᵢ=0}`.  They coincide only after the eq.(1) chain-rule conversion *and* the polarity flip.  The quarry implements the **joint** (CR18/Maurer13b) form.
3. **ADAPTIVE vs NON-ADAPTIVE RHS is a real strengthening, not a restatement.**  Maurer02 Thm 1's RHS is the *adaptive* `ν`; the non-adaptive `μ` is reached only through **Thm 2 (p. 13)** under the extra hypothesis `p^F_{Aᵢ|Xⁱ Y^{i−1} A_{i−1}} = p^F_{Aᵢ|Xⁱ A_{i−1}}`.  Maurer13b Thm 3 and CR18 Thm 4.17 get the non-adaptive RHS **unconditionally**, via the blinding operator.  Stating the AC endpoint with a blind RHS while citing Maurer02 Thm 1 would be a false citation.
4. **Definition- and equation-number collisions across papers.**  "Definition 9" is *distinguisher* (Maurer02 p. 10), *MBO + `S⁻`/`S⊣`* (MPR07 p. 138), *game* (Maurer13b p. 3152).  "Definition 6" is *CE* (Maurer02 p. 8), *distinguisher* (Maurer13b p. 3151), *advantage `Δ`* (MPR07 p. 137).  "eq. (1)" is the chain rule (MPR07 p. 135), the transcript law (Maurer13b p. 3152), and Thm 2's adaptivity criterion (Maurer02 p. 13).  **Never cite by bare number across papers** — every AC docstring must carry paper + page.
5. **Maurer13b does NOT contain the completeness result** — it cites MPR07 only for the easy direction (its Lemma 2).  **Maurer09c defines no `S⁻`, no CE, no `ν`/`Γ`** — it is a 2-page keynote note and can only be cited for the informal restatement.
6. **CR18's `Γ(bŜ)` is a *converter* application** (Def 4.20: `b` blocks the replies), where Maurer13b uses the operator `⟦DT⟧` and the quarry uses a **predicate on winners** (`IsBlind`, `Q:BlindConverter.lean:51`).  Three different renderings of one idea — see the ARCHITECTURE note below.

# T1 — CONDITIONAL EQUIVALENCE (CE) + MBO

**What it is.**  Adjoin to a system `S` a *monotone binary output* (MBO) — a bit
that, once set, stays set — and call the enriched object a **game** `Ŝ`.  `Ŝ` is
**conditionally equivalent** to a second system `T` when the output law of `Ŝ`
*conditioned on the MBO still being 0* equals the output law of `T`.  The payoff
theorem then says: if such an MBO exists, the distinguishing advantage between
`S = Ŝ⁻` (the MBO stripped off) and `T` is bounded by the probability of making
the MBO fire — a *game-winning* probability, which is a one-system quantity and
therefore usually a counting problem rather than a distinguishing problem.  The
technique converts "these two systems look alike" into "this bad event is rare".

**Where the main bound lands (AC).**  `Adv⊥(S, T) ≤ Γ(Ŝ)`, i.e. an upper bound on
`PDS.advFullyDefined` (`AC:RandomSystems/System/Environment.lean:751`), with `Δ`
following through the existing `Adv⊥ ≤ Δ` / finite-slice identification.

## Quarry home (from disk)

The quarry's CE development is **CR18-shaped** (Defs 4.15–4.19, Thm 4.17) and is
one of its most complete chains — definition, filtration algebra, seed-indexed
constructors, and two paper-facing endpoints, with real applications hanging off it.

| object | quarry `file:line` | what it is |
|---|---|---|
| `PFunDDS.stripMBO` / `PFunPDS.stripMBO`, notation `S⁻` | `Q:RandomSystems/SystemMBO.lean:29`, `:45`, `:48` | CR18 Def 4.18: post-compose the output with `Prod.fst`; at the law level `Dist.fTransform` of the deterministic strip.  **Domain-preserving definitionally** (`stripMBO_dom`, `:32`) — validity needs no proof |
| `massYAfalse` (game numerator) | `Q:RandomSystems/CondEquiv.lean:61` | `p^Ŝ_{Yⁱ,Aᵢ=0|Xⁱ}` as one `Dist.mass` over a prefix-match predicate that additionally requires every prefix MBO bit `false` |
| `massAfalse` (game normalizer) | `Q:CondEquiv.lean:73` | `p^Ŝ_{Aᵢ=0|Xⁱ}` |
| `massY`, `massDom` (plain side) | `Q:CondEquiv.lean:81`, `:88` | `p^T_{Yⁱ|Xⁱ}` and the `T`-side normalizer |
| `TotalOnNonempty` | `Q:CondEquiv.lean:96` | the standing "systems are defined on the histories under discussion" hypothesis, rendered in the partial model as: every support realization accepts every **nonempty** history |
| **`CondEquiv`**, notation `Ŝ \|≡ T` | `Q:CondEquiv.lean:118`, `:124` | CR18 Def 4.19 / eq. (4.38), stated **cross-multiplied and division-free**, guarded by both normalizers being nonzero |
| filtration algebra | `Q:CondEquiv.lean:152-247` | `condEquiv_filterDom` (`:203`), `condEquiv_filterQueries` (`:237`) and the four mass-level `filterDom`/`filterQueries` commutations — CE survives both restrictions |
| seed-indexed constructors | `Q:CondEquiv.lean:256-347` | `mass*_fTransform_historyEvaluator` (`:256`, `:270`, `:288`), `monotoneMBO_fTransform_historyEvaluator` (`:328`), `totalOnNonempty_fTransform_historyEvaluator` (`:340`) — the kit that discharges the standing hypotheses for seed-indexed systems |
| `MonotoneMBO`, `DDS.IsGame`, `IsMBO`, `DDG` | `Q:RandomSystems/PDS.lean:3101`, `:3060`, `:3045`, `:3066` | the game carrier: `MonotoneMBO Ŝ := ∀ s ∈ Ŝ.support, s.IsGame`, i.e. monotonicity is a **support-wise, per-realization** property |
| `gameOfDDS` / `gameOf`, `MonotoneCond` | `Q:RandomSystems/GameOf.lean:230`, `:988`, `:280` | build a game from a base system + a transcript condition `cond : List (X × Y) → Bool` |
| `GameEquiv` (`≡ᵍ`), `prewinBehavior` | `Q:RandomSystems/GameEquivalence.lean:64`, `:45`, `:51` | CR18 Def 4.15: two games agree on the not-yet-won behaviour |
| `winsDDS`, `winProb`, `maxWinProb` (`Γ`) | `Q:RandomSystems/WinProb.lean:32`, `:38`, `:63`; generic `Q:RandomSystems/MaxWinProb.lean:38`, `:170` | the adaptive winning probability |
| `IsBlind`, `blindMaxWinProb` (`Γᵇ`) | `Q:RandomSystems/BlindConverter.lean:51`, `:67`; `Γᵇ ≤ Γ` at `:108` | the **non-adaptive (blind)** winning probability — the strictly stronger right-hand side |
| `gameEnhance` / `combineSys` | `Q:RandomSystems/Theorem417.lean:33` (`combineSys`) | CR18 eq. (4.39): enhance `T` with `Ŝ`'s MBO as an independent product, so `T̂⁻ = T` and `massYAfalse T̂ = massYAfalse Ŝ` |

### The endpoints (this is what a transplant is buying)

| endpoint | `file:line` | statement shape | RHS |
|---|---|---|---|
| abstract adaptive helper | `Q:Theorem417.lean:764` `advantage_le_maxWinProb_of_condEquiv` | `⟨S\|T⟩(D) ≤ Γ(Ŝ)` for a free game `Ŝ`, hyps: `isProbDist` ×2, `Ŝ \|≡ T`, `MonotoneMBO Ŝ`, `TotalOnNonempty` ×2, `QueriesExactly (i+1)` on `D.support`, `D.isProbDist` | adaptive `Γ` |
| bounded-totality variant | `Q:Theorem417.lean:724` `advantage_le_maxWinProb_of_condEquiv_of_totalUpTo` | same, with `TotalUpTo _ (i+1)` instead of global totality — the filtered systems' honest hypothesis | adaptive `Γ` |
| **paper-facing headline** | `Q:GameOf.lean:1472` `maxAdvantage_le_blindMaxWinProb_of_condEquiv_gameOf` | takes **base** `S T : PFunPDS X Y` and the MBO `cond`, *constructs* `Ŝ := gameOf S cond` in the statement, and concludes `(gameOf S cond \|≡ T) → Δ(S,T) ≤ Γᵇ(gameOf S cond)` | **blind `Γᵇ`** |
| abstract-game filtered form | `Q:GameOf.lean:1431` `maxAdvantage_filterQueries_le_blindMaxWinProb_of_condEquiv` | `Ŝ \|≡ T → Δ(⌈q⌉S, ⌈q⌉T) ≤ Γᵇ(⌈q⌉Ŝ)`, for MBOs that are **not** transcript conditions (seed-indexed) | blind `Γᵇ` |
| eq. (4.39) content | `Q:GameOf.lean:1497` `massYAfalseEq_gameEnhance_of_condEquiv` | `Ŝ ≡ᵍ T̂` as the mass equality the Lemma-4.16 chain consumes | — |
| blind-winner reduction | `Q:BlindConverter.lean:208`, `:247`; `Q:BlindAbsorption.lean:642`, `:699`, `:729`, `:743` | per-winner and per-`D` forms; `BlindAbsorption` is the absorption route to `Γᵇ` | blind |
| domain-filtered form | `Q:FilterDomNormalization.lean:1220` | the `filterDom` sibling of `GameOf.lean:1431` | blind |

### Applications already riding the quarry CE chain (evidence the architecture works)

`Q:RandomSystems/CBCMAC.lean:932` `cbc_condEquiv`; `Q:CBCStructureGraph.lean:317`
`cbcGraphGame_condEquiv`; `Q:SumOfPermutations.lean:196` `sop_condEquiv` and
`Q:SumOfPermutationsTight.lean:579` `sopTight_condEquiv`;
`Q:SwitchingLemma.lean:1745` `filterURF_collisionCond_condEquiv_filterURP`,
`:2204` `seededHashThenURF_condEquiv`, and the reusable reduction
`:563` `condEquiv_of_transcript_mass_reductions`;
`Q:HistoryConditionC.lean:211`/`:676` the stateful history-condition kit.

### Carrier delta (per the LEDGER delta vocabulary)

* **carrier**: everything rides `PFunPDS X Y = Dist (PFunDDS.DDS X Y)`, a *typed*
  `(X,Y)` partial carrier.  AC's is `PDS X Y = Distribution (System.DDS X Y)`
  with the fully-defined slice as the official object — same *shape*, different
  type, and the ⊥-convention differs (see CONFLICTS C1).
* **metric**: the endpoints are stated against `advantage` (per-`D`) and
  `Δ(S,T) = maxAdvantage` (the quarry's `Δ`, **not** AC's `classDistance`).  Under
  pin 2 both are FORBIDDEN statement targets.  Every endpoint above is
  delta = **both**.

### T1 matrix rows

| # | object / theorem | source | quarry home + carrier delta | AC asset | verdict | size |
|---|---|---|---|---|---|---|
| T1.1 | MBO / monotone condition as a first-class object | Maurer02 §4; Maurer13b Def 9; thesis Def 2.20 (input-only MC) | `Q:PDS.lean:3045` `IsMBO`, `:3060` `IsGame`, `:3066` `DDG`, `:3101` `MonotoneMBO`; delta `carrier` | `AC:RandomSystems/Game/MonotoneCondition.lean` is a **10-line placeholder** | **MODEL-NEW** — needs the carrier decision first (T3 "carrier shape" fork) | S |
| T1.2 | `S⁻` (strip the MBO) | CR18 Def 4.18 (CR18-fallback: check whether a primary states it) | `Q:SystemMBO.lean:29,45` (50 lines total); delta `carrier` | none | **TRANSPLANT** — trivial once T1.1 lands; the `stripMBO_dom` definitional-domain trick transplants verbatim | S |
| T1.3 | conditional equivalence `Ŝ \|≡ T` | Maurer02 Def 6; Maurer13b Def 13; CR18 Def 4.19 eq. (4.38) | `Q:CondEquiv.lean:118`; delta `carrier` | none | **MODEL-NEW** (definition) — but the *cross-multiplied division-free form* is the design and it transplants as-is | S |
| T1.4 | CE is preserved by query/domain filtering | not in the papers (formalization-forced) | `Q:CondEquiv.lean:203`, `:237` (+4 mass lemmas); delta `carrier` | AC has `filterQueries` at `AC:RandomSystems/System/DiscreteSystem.lean:403` | **TRANSPLANT** (REUSE-ARCH: the proofs are mass-level rewrites) | S |
| T1.5 | seed-indexed MBO constructor kit | none (formalization-forced) | `Q:CondEquiv.lean:256-347`; delta `carrier` | AC has `historyEvaluator` at `DiscreteSystem.lean:157` | **TRANSPLANT** | M |
| T1.6 | `gameEnhance` / eq. (4.39): `Ŝ \|≡ T ⟹ Ŝ ≡ᵍ T̂` with `T̂⁻ = T` | CR18 eq. (4.39) | `Q:Theorem417.lean:33` + `Q:GameOf.lean:1497`; delta `carrier` | none | **TRANSPLANT** (REUSE-ARCH — the independent-product construction is the whole proof) | M |
| T1.7 | **CE ⟹ indistinguishability, adaptive** `Adv ≤ Γ(Ŝ)` | Maurer02 Thm 1; CR18 Thm 4.17 | `Q:Theorem417.lean:764` (and `:724`); delta `both` | none; target distance `Adv⊥` exists (`Environment.lean:751`) | **TRANSPLANT** — restate on `Adv⊥`; the hypothesis bundle re-derives (see C2/C3) | L |
| T1.8 | **CE ⟹ indistinguishability, blind** `Δ ≤ Γ(bŜ)` (the headline) | **Maurer13b Thm 3, printed p. 3154** (via `⟦DT⟧`); **CR18 Thm 4.17, printed p. 110** (via the blocking converter `b`, Def 4.20 p. 109) — both VERIFIED, both NON-ADAPTIVE RHS unconditionally | `Q:GameOf.lean:1472`, `:1431`; delta `both` | none | **TRANSPLANT** — the strictly stronger endpoint; needs T3.2.  **See the `b`-as-converter note below: AC can state this paper-faithfully where the quarry could not** | PARTIAL (T1: gameTranscript/gameTrLaw/supWinProb landed; Γ/Γᵇ deliberately NOT built — T3.9, hierarchy prefers ν stated once) |
| T1.7b | Maurer02's adaptive route + its non-adaptive side condition | **Maurer02 Thm 1, preprint p. 12** (adaptive `ν`); **Thm 2, p. 13** (`ν = μ` under `p^F_{Aᵢ\|Xⁱ Y^{i−1} A_{i−1}} = p^F_{Aᵢ\|Xⁱ A_{i−1}}`) | not formalized in the quarry | none | **REF-ONLY** — record as the historical route; the CR18/Maurer13b blinding argument supersedes it and needs no side condition | — |
| T1.9 | conditional-probability toolkit the CE proofs stand on | MPR07 eq. (1) chain rule | `Q:RandomSystems/DistCond.lean` (592 lines): `condProb` `:88`, multiplication rule `:134`, Bayes `:145`/`:155`, total probability `:168-192`, chain rules `:213`/`:244`/`:287`; delta `none` (pure `Dist`) | `AC:Probability/Distribution.lean:476` `cond` (Part-valued), `condPMF`, a chain rule at `:1138` | **PARTIAL / TRANSPLANT** — AC has the `Part`-valued `cond` but **not** the total `condProb` nor the hypothesis-free multiplication/chain rules; delta `none` makes this the cheapest, highest-leverage row | CLOSED (T0 cee67d7: Conditional.lean — condProb :106, mult :169/:178, Bayes :190/:200, cross-mult :216, total prob :266-290, chain rules :312/:343/:386; independence half out-of-row, not transplanted) |
| T1.10 | CE application kits (CBC-MAC, SoP, switching, history-condition) | — | `Q:CBCMAC.lean:932`, `Q:SumOfPermutations.lean:196`, `Q:SwitchingLemma.lean:563`, `Q:HistoryConditionC.lean:211` | none | **BLOCKED-ON** T1.7/T1.8 + the converter layer | L (out of first scope) |

# T2 — MPR07's OPTIMAL FAILURE CONDITION (completeness of the bad-event method)

**What it is, for us.**  Not a bound — a **meta-theorem about T1**.  T1 is only
useful if a *good* MBO exists; T2 says a *tight* one always does.  It is the
answer to "we tried an MBO and got a lossy bound — is that the technique's
ceiling or our choice's?"  It converts every CE bound from a lucky construction
into a *search over a space known to contain the optimum*, and it is what licenses
saying "the H-technique/CE gap here is real" instead of "we did not find the right
event".

**Where the main bound lands (AC).**  It bounds nothing; it is an existence +
optimality statement about a monotone condition, whose optimum equals a distance
already in the tree (`Adv⊥` or `Δ`).  Its natural AC home is a *completeness*
theorem sitting beside T1's endpoint.

## Quarry home: essentially EMPTY — this is the one MODEL-NEW technique

Exhaustive grep of the quarry for `MPR07`/`MaPiRe07`/`optimal failure`/`Pietrzak`
returns only **ingredients and citations**, never the lemma:

| quarry hit | `file:line` | what it actually is |
|---|---|---|
| MPR07 eq. (1), the defining identity of a random system | `Q:RandomSystems/DistCond.lean:275` `condProb_biForall_lt_eq_prod_condProb` (+ header `:24`, `:64`) | the chain rule `p_{Yⁿ\|Xⁿ} = ∏ p_{Y_j\|X^j Y^{j-1}}` — an ingredient |
| MPR07 eq. (3), min-form of statistical distance | `Q:RandomSystems/StatDist.lean:211` (weight-one specialization); also `Q:SoP/SoP2.lean:853` | an ingredient |
| MPR07 Lemma 4's `½ + ½p` best-success computation | `Q:StatDist.lean:399`, `:470`; and `:405` states in-tree that the rest "is separate work" | an ingredient, with an explicit in-tree admission of the gap |
| MPR07 Theorem 3 (amplification) | `Q:Legacy/Amplification.lean` — `amplification_theorem`, **`sorry` at `:119`** (the `k ≥ 2` case, with a written proof outline) | a LEGACY, **never-forward** item under the LEDGER lane rules; also L5, deferred by scope |
| "events generalize MPR07's MBOs" | `Q:RandomSystemsCC/EventHistory.lean:25` | see the source-hierarchy note below — this is the most important T2 hit |

**No declaration in the quarry states the completeness/optimality lemma.**
Verdict for the whole technique: **MODEL-NEW**, with delta `none` ingredients
available.

## The source-hierarchy opening (a T1+T2 finding, from disk)

`Q:RandomSystemsCC/EventHistory.lean:10-40` records, from a visual read of the
Jost thesis, that **Jost p. 33 states outright that events *generalize* MPR07's
MBOs**, and that Jost §3.2.2 says "an event is essentially just a named monotone
condition".  The file then proves the fit is exact: composite events are the
monotone predicates on histories = upper sets of the extension order, whose
**dual** satisfies GegMau26 Def 9, so `EventAlgebra (LowerSet P)` applies with no
new axioms (`compositeEventAlgebra`).

Why this matters for the charter: the SOURCE HIERARCHY demotes CR18 to
fallback-only, "consult it ONLY for a concept none of the primaries addresses"
(`AC:LEDGER.md:8-10`).  The quarry's own reading says **Jost — a PRIMARY — does
address the MBO concept**, as events.  So the T1/T2 modeling layer should be
grounded on Jost's events (+ Maurer02/Maurer13b/thesis for the CE and game
statements), with CR18 Def 4.18/4.19 retained only as historical docstring
provenance.  **AC already has the abstract half**:
`AC:AbstractCryptography/EventAlgebra.lean` (775 lines, incl. `forestOrder`
`:435`).  What is missing is the *instantiation onto interaction histories* —
the content of `Q:RandomSystemsCC/EventHistory.lean` (174 lines).
**Flagged, not decided** (escalation filter): this is a modeling ruling —
"is the AC MBO an `EventAlgebra` element or a `Bool`-valued monotone predicate?" —
and it is exactly the kind of question the registry says to check before forking.

## T2 matrix rows

| # | object / theorem | source | quarry home + delta | AC asset | verdict | size |
|---|---|---|---|---|---|---|
| T2.1 | MBO / monotone condition as an *event* (the primary-source presentation) | Jost thesis p. 33 + §3.2.2 (per `Q:EventHistory.lean:10-40`; **visual re-verification owed** — this row is the one unverified source claim in the matrix) | `Q:RandomSystemsCC/EventHistory.lean` (174 lines), delta `none` (order theory) | `AC:AbstractCryptography/EventAlgebra.lean` (775 lines) — abstract half **PRESENT**; the history instantiation ABSENT | **TRANSPLANT** (order-theoretic, carrier-free) — and it is the SOURCE-HIERARCHY-correct home for T1.1 | M |
| T2.2 | **MPR07 Lemma 5** — tight MBO existence (the converse of the bad-event bound): `∀ S,T ∃ Ŝ,T̂` with `Ŝ⁻≡S`, `T̂⁻≡T`, `Ŝ⊣≡T̂⊣`, and `δ_k^D(S,T) = ν_k^D(Ŝ) = ν_k^D(T̂)` **for all `D`** | **MPR07 Lem 5, printed p. 140 (PDF 11)** — VISUALLY VERIFIED; construction eq. (4) p. 141 = **maximal coupling** on eq. (3) p. 140 | **NONE** | none; but AC has `Probability/Coupling.lean:143` `optimalJoint` + `:196` `isCoupling_optimalJoint` + `:225` `offDiagonalMass_optimalJoint` — **the maximal-coupling kernel MPR07's proof runs on is already landed** | **MODEL-NEW**, but the proof engine is PRESENT | M–L (down from L) |
| T2.3 | the representative caveat: the condition sits on **new systems equivalent to both**, and is **non-unique** (free `A^{i−1}`-dependence / `r`-parameters) | MPR07 p. 133 §1.3 + p. 141 (VERIFIED); Maurer09c p. 45 restates it verbatim, informally | none | `equivalent` (`ClassDistance.lean:1322`), **`Behaviour` quotient** (`Behaviour.lean:151`), R9 honest-representative infimum | **MODEL-NEW** — state it *at the quotient*, where non-uniqueness is expected rather than a defect | S (once T2.2 lands) |
| T2.4 | MPR07 eq. (1) chain rule and eq. (3) min-form | MPR07 | `Q:DistCond.lean:275`, `Q:StatDist.lean:211`; delta `none` | AC: chain rule at `Probability/Distribution.lean:1138`; `statDist` in `Probability/StatisticalDistance.lean` | **PARTIAL** — see T1.9 | CLOSED (T0: chain rule Conditional.lean:386; eq.(3) min-form was already PRESENT — statDist_eq_one_sub_sum_min, StatisticalDistance.lean:251) |
| T2.5 | MPR07 Thm 3 / amplification | MPR07 Thm 3, LanMau20 §5 | `Q:Legacy/Amplification.lean` with a live `sorry` at `:119` | none | **OUT OF SCOPE** — L5 deferred by the scope ruling; and a never-forward sorry | — |

# T3 — GAME WINNABILITY (and the "blinder" question)

**What it is.**  Two numbers are attached to a game `S^A`.  `ν(S^A)` is the
*supremum winning probability*: over all environments/strategies, the chance of
driving the monotone condition to 1.  `ω(S^A)` is the *infimum winnability*: over
all representatives of the game's equivalence class, the probability mass of
realizations that are winnable **at all** — a static, strategy-free property of
the realization.  The **Winnability Theorem** says `ν = ω`, and that the infimum
is *attained*.  Operationally: a game with maximal winning probability `δ` is,
on some equivalent representative, simply **unwinnable on `1 − δ` of its own
randomness** — no strategy involved.  That is what makes a winning probability
countable: it demotes an adversarial sup to a mass computation.

**Where the main bound lands (AC).**  Not a distance bound at all — it is an
*identity* between two functionals of a game, plus attainment.  It feeds T1: it
is what makes the `Γ`/`Γᵇ` on the right-hand side of the CE theorem tractable.

## SOURCE FINDINGS (visual, verified — these change the brief)

Recorded at the top of this document; restated here because they determine the
whole T3 design:

* **The games layer exists only in the thesis** (`Q:papers/thesis (1).pdf`), NOT in
  LanMau20 — which is "Coupling of Random Systems" (TCC 2020) and whose §4 is the
  *Coupling Theorem for Discrete Systems* (Thms 1/2 = thesis Thms 2.31/2.32).
* **§2.3.3 numbered items are exactly** Def 2.20, Def 2.21, Def 2.22, Rem 2.23,
  Rem 2.24, Def 2.25.  **§2.4.3 is exactly** Def 2.35, Def 2.36, Thm 2.37.
  There is **no Def/Lem 2.38** (2.38 is an unrelated Example in §2.5.1).
* **There is no "blinder" object in the thesis.**  The charter's "blinders" maps
  onto two real things: (i) **Rem 2.23** — the environment never observes the MC
  during the interaction, i.e. strategies are *bit-blind by definition*; and
  (ii) the unnamed **always-losing system `V`** in the alternative proof of
  Thm 2.37 (printed p. 26).  The quarry named (ii) `zeroMBO`/`zeroMBODist`
  (`Q:GameWinnability.lean:356`, `:374`) — a **COINAGE**, to be flagged as such.
  The quarry named (i)'s formal counterpart `blindize`/`IsBlind`
  (`Q:GameWinnability.lean:658`, `Q:BlindConverter.lean:51`) — also coinages.
* **Def 2.20's MC is input-only**: `A : X* → {0,1}` monotone, and a deterministic
  game is the **pair** `s^A = (s, A)`.  The `Y × {0,1}` output-alphabet
  presentation is **Maurer13b Def 9** and appears in the thesis only inside the
  alternative proof of Thm 2.37.  **This is the T3 design fork.**

## Quarry home (from disk) — the strongest single asset in this program

`Q:RandomSystems/GameWinnability.lean` (916 lines) is a **thesis-primary** file
(header: "Lanzenberger thesis §2.3.3 and §2.4.3"), not a CR18 file, and it
already carries the model bridge, the CR18 reconciliation, and two documented
*generalizations* beyond the thesis.

| object | quarry `file:line` | notes |
|---|---|---|
| `WinningTranscript` (`𝒯_w`, Def 2.25) | `:105`; monotonicity `:111` | "some answered query carries MC bit `1`" — the ∃-form, chosen as the faithful reading in the ⊥-totalized model |
| `winningMass` | `:124`; `= mass transcriptDist` `:130`; **class-invariance** `:138` `winningMass_congr_equivalent` | |
| `wonFlag`, `gameTranscriptView`, `gameTranscriptDist` | `:156`, `:177`, `:184` | the Def 2.21 observable: bit-stripped transcript + one `wonFlag` bit |
| `GameEquivalent` (Def 2.22) | `:194`; refl `:198`; **`gameEquivalent_of_equivalent`** `:205` | game equivalence is *weaker* than Def 2.17 equivalence — load-bearing in the final step |
| **`supWinProb`** (`ν`, Def 2.25) | `:248`; nonempty `:252`; `bddAbove` (needs `NonNeg`) `:261`; defining property `:270` | `sSup` over **deterministic bit-blind** environments (`winnerView`) and prefix lengths |
| **`PFunDDS.Winnable`** (Def 2.35) | `:281` | `∃ l ∈ dom g, (output g l).2 = true` — a *static* property of the realization |
| **`infWinnability`** (`ω`, Def 2.36) | `:294`; `bddBelow` `:300` | `sInf` over `{H \| H.NonNeg ∧ GameEquivalent H G}` — **the `NonNeg` conjunct is written explicitly** and the docstring says why: on the signed carrier, dropping it drives the infimum to `−∞` |
| `ν ≤ ω` (easy direction) | `:338` `supWinProb_le_infWinnability`, via `:310` `winnable_of_winningTranscript` | |
| the never-won twin `V` | `:356` `zeroMBO`, `:374` `zeroMBODist`, `:406`, `:380` | thesis p. 26's "always outputs `bᵢ = 0`" |
| no equivalent rep of `V` is winnable | `:535` `mass_winnable_eq_zero_of_equivalent_zeroMBODist` | the crux: a winnable atom would show up under its own fixed-query environment (`playQueries`) |
| `δ(tr) ≤ winningMass` | `:632` `δ_transcriptDist_zeroMBODist_le_winningMass`, via `:616`, `:563` | |
| **bit-adaptivity is useless** | `:737` `winningMass_eq_winningMass_blindize`, via `:658` `blindize`, `:690` | why the bound lands on the *bit-blind* supremum |
| `Adv(G, V) ≤ ν(G)` | `:747` `adv_zeroMBODist_le_supWinProb` | |
| **THE WINNABILITY THEOREM (Thm 2.37)** | **`:778` `winnability_theorem_of_fixed_domain_and_bounded`** | see below |
| CR18 reconciliation `Γ = ν` | `:829`+ (`winProb_eq_sum_mass` `:829`, `winProb_single_eq_mass` `:839`), endpoint `maxWinProb_eq_supWinProb` | proves the CR18-shaped `Γ` layer *states* thesis Def 2.25 |

### The winnability theorem, exactly as the quarry states it

```
theorem winnability_theorem_of_fixed_domain_and_bounded
    [Fintype X] {G : PFunPDS X (Y × Bool)} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg)
    (hdomain : PFunPDS.HasFixedDomain G D) (hbounded : QBounded D q) :
    supWinProb G = infWinnability G ∧
      ∃ G' : PFunPDS X (Y × Bool), G'.NonNeg ∧ Equivalent G' G ∧
        G'.mass PFunDDS.Winnable = supWinProb G
```
(`Q:RandomSystems/GameWinnability.lean:778`)

Read carefully, this is **stronger than the thesis's letter in three ways**, all
documented in the file's own header (`:44-56`):
1. the attained representative is `Equivalent` (Def 2.17), *strictly stronger*
   than the Def 2.22 game equivalence `ω` quantifies over;
2. **monotonicity of the MC is never assumed** — "the winning event 'some
   answered bit is 1' is itself monotone along the interaction";
3. **no probability-distribution hypothesis** — everything at Def 2.1's
   arbitrary-weight generality, with `NonNeg` where and only where it is needed.

**Integration shape (the charter's KEY DESIGN QUESTION), answered from disk.**
The quarry's answer is: a game is **`PFunPDS X (Y × Bool)`** — a PDS at output
alphabet `Y × Bool` — with monotonicity a *separate, support-wise predicate*
(`MonotoneMBO`, `Q:PDS.lean:3101`), **not** a bundled structure; `DDG` exists as a
subtype (`Q:PDS.lean:3066`) but the theorems do not use it.  The quarry documents
the bridge from the thesis's pair `(s, A)` to this carrier explicitly at
`Q:GameWinnability.lean:16-40`: a thesis pair is `gameOfDDS` at an *input-only*
condition, the thesis environment is `Winner X Y = DDE X Y` acting through
`winnerView`, and the thesis observable is `gameTranscriptDist`.
**So the fork is already surveyed and answered in the quarry — the transplant
inherits a decision, it does not have to make one.**  What AC must decide is only
whether to keep the CR18/Maurer13b `Y × Bool` carrier (quarry's choice, and the
one all the CE machinery needs) or the thesis's Def-2.20 pair — and the quarry's
own bridge argues for `Y × Bool` with the pair recovered as a special case.

### Carrier + metric delta

* delta **carrier** throughout (`PFunPDS` → `PDS`), and the proof route depends on
  the quarry's `Adv`/`δ`/`Equivalent`/`HasFixedDomain`/`QBounded` bundle.
* delta **metric** only in step 6 (`adv_zeroMBODist_le_supWinProb` uses the
  quarry's `Adv`).  `ν` and `ω` themselves are **metric-free** (`ℝ`-valued sups of
  masses) — delta `none` for the definitions.
* **The AC substrate for the proof route already exists.**  The quarry proves
  Thm 2.37 by *reducing to Thm 2.31* rather than repeating the thesis induction
  (`Q:GameWinnability.lean:58-77`), and AC has Thm 2.31/2.32 landed at both the
  presentation level (`AC:RandomSystems/System/Attainment.lean`) and the
  quotient (`AC:RandomSystems/System/BehaviourAttainment.lean:149`, `:165`, `:189`,
  `:214`, `:233`, `:258`).  This is the single best-supported transplant in the
  program.

### T3 matrix rows

| # | object / theorem | source (visually verified) | quarry home + delta | AC asset | verdict | size |
|---|---|---|---|---|---|---|
| T3.1 | game object + MC/MBO | thesis Def 2.20 (printed p.16) = pair `(s, A)`, `A : X* → {0,1}` monotone, **input-only**; Maurer13b Def 9 = `Y × {0,1}` | `Q:PDS.lean:3045/3060/3066/3101` + bridge `Q:GameWinnability.lean:16-40`; delta `carrier` | `AC:RandomSystems/Game/Game.lean` + `Game/MonotoneCondition.lean` — **10-line placeholders** | **MODEL-NEW**, decision pre-surveyed by the quarry | CLOSED (T1 c6f460e/7949cf6: Game.lean; the empty Game/ placeholders superseded — games live under System/ where the gate covers them) |
| T3.2 | game transcript + observable; `Γ`, `Γᵇ`, `ν` | thesis Def 2.21, Rem 2.23 (bit-blind), Def 2.25 | `Q:GameWinnability.lean:156/177/184/248`; `Q:WinProb.lean:32/38/63`; `Q:BlindConverter.lean:51/67/108`; delta `carrier` | none | **MODEL-NEW + TRANSPLANT** | PARTIAL (T1: gameTranscript/gameTrLaw/supWinProb landed; Γ/Γᵇ deliberately NOT built — T3.9, hierarchy prefers ν stated once) |
| T3.3 | game equivalence (Def 2.22) and class-invariance of `ν` | thesis Def 2.22 | `Q:GameWinnability.lean:194/198/205/234`; delta `carrier` | AC has Def-2.17 `equivalent` (`ClassDistance.lean:1322`) and the `Behaviour` quotient (`Behaviour.lean:151`) — the **coarser** game quotient is missing | **MODEL-NEW** (a second, coarser quotient beside `Behaviour`) | CLOSED (T2 9a5dccc/a9d9546: gameEquivalent + GameBehaviour; ν and ω descend) |
| T3.4 | `Winnable` (Def 2.35), `ω` (Def 2.36) | thesis Def 2.35, 2.36 (printed pp. 23-27) | `Q:GameWinnability.lean:281`, `:294`; delta `none` for the defs | none | **MODEL-NEW** — and R9-aligned already (the `NonNeg` conjunct is exactly R9's honest-representative discipline) | CLOSED (T2 9a5dccc: Winnable, infWinnability; R9-aligned) |
| T3.5 | `ν ≤ ω` | thesis Thm 2.37, easy half | `Q:GameWinnability.lean:310`, `:338`; delta `carrier` | none | **TRANSPLANT** (REUSE-ARCH) | CLOSED (T2: supWinProb_le_infWinnability; carries the necessary empty-history clause) |
| T3.6 | the never-won twin `V` and its no-winnable-representative lemma | thesis p. 26 (unnamed `V`) | `Q:GameWinnability.lean:356/374/535`; delta `carrier` | none | **TRANSPLANT**; **rename** — `zeroMBO` is a coinage | CLOSED by construction (⊥ in the condition lattice; supWinProb_adjoin_bot = 0; zeroMBO retired) |
| T3.7 | bit-adaptivity is useless (`blindize`) | thesis Rem 2.23 (the *reason*), formalized as a theorem | `Q:GameWinnability.lean:658/690/737`; delta `carrier` | none | **TRANSPLANT** — this is the honest formal content of "blinder" | SUBSUMED (pair carrier: no bit-adaptive environment exists by type; contentful residue proved for the derived view — winningMass_eq_mass_lastBit_toBitLaw; BlindConverter/BlindAbsorption not needed) |
| T3.8 | **Winnability Theorem `ν = ω` + attainment** | thesis Thm 2.37 + its alternative proof, printed p. 26 | `Q:GameWinnability.lean:778`; delta `both` (step 6 only) | **substrate PRESENT**: Thm 2.31/2.32 at `AC:Attainment.lean` + `AC:BehaviourAttainment.lean:149-258`; the finiteness bundle is `PDS.HaveCommonDomainAndBounded` (`AC:Attainment.lean:481`), `PDS.HasDomain` (`AC:Environment.lean:284`), `QBounded` (`AC:DiscreteSystem.lean:37`) — **trap**: AC's `PDS.HasFixedDomain` (`AC:ProbabilisticSystem.lean:85`) is the one-system *existential* class, documented as NOT usable for two-system statements (`AC:Environment.lean:280`, `AC:Attainment.lean:456`), whereas the quarry's `PFunPDS.HasFixedDomain G D` is a two-argument relation — the transplant must re-target it to `HasDomain` | **TRANSPLANT** (REUSE-ARCH, the p.26 alternative proof) — highest-confidence row in the program | CLOSED (T2 e221d9e/65a87f2: winnability_theorem via the p.26 alternative proof; HasFixedDomain trap avoided — one PDG.HasDomain clause; all three reference strengthenings kept) |
| T3.9 | `Γ = ν` (CR18 layer states the thesis definition) | reconciliation, not a paper claim | `Q:GameWinnability.lean:829+`, endpoint `maxWinProb_eq_supWinProb`; delta `carrier` | none | **TRANSPLANT** — only needed if both presentations are kept; under the SOURCE HIERARCHY, prefer stating `ν` once and deriving | S |

### DESIGN NOTE — the three renderings of "blind", and why AC gets the paper's one

CR18 Def 4.20 `[p. 109]` defines `bS` as **`S` with a blocking converter applied**:
"`b` is the simple converter that is transparent for the queries `Xᵢ` but blocks
the replies `Yᵢ`", and the headline is `Δ(S,T) ≤ Γ(bŜ)`.  Maurer13b instead uses
the operator `⟦DT⟧`.  The quarry, having no converter layer available at that
point, rendered blindness as a **predicate on winners** — `IsBlind`
(`Q:BlindConverter.lean:51`), `blindMaxWinProb` (`:67`) — a coinage, plus a whole
file (`Q:BlindAbsorption.lean`) to push bounds through it.

**AC already has the blocking converter, with receipts.**  `blockSet` is a PROVEN
RECEIPT row (`fullyDefined_blockSet`); `block` at the Resource level is PROVEN
(`fullyDefined_block` + `exists_absorb_block`, read at the tag cylinder through
`block_eq_blockSet`); and `attachAt`/`converterMonoidAt` is the ratified
attachment primitive (PRIMITIVE REGISTRY).  So the AC statement can be
`Adv⊥(S,T) ≤ Γ(b • Ŝ)` with `b` an actual member of the metric-facing `Σ` —
**CR18 Def 4.20 verbatim**, no `IsBlind` coinage, and `Q:BlindConverter.lean` +
`Q:BlindAbsorption.lean` (≈1400 lines of quarry machinery) become unnecessary
rather than transplanted.

Two caveats, **flagged not decided** (escalation filter):
* pin 3 says converter-attaching items route to the MR16 track.  This one is a
  *technique* statement that mentions a converter, so the pin needs a reading.
* `b` blocks **replies**, i.e. it is an output-side block; AC's `blockSet` blocks
  **queries** by a `Set` of them.  Whether `b` is `blockSet` at some index, a new
  `relabel`-style output map, or a third primitive is an open modeling question —
  and the PRIMITIVE REGISTRY is the place it must be checked before any fork.

**Certification note.** The charter says "the L4 matrix already certified it
sorry-free".  From disk: `Q:GameWinnability.lean` contains no `sorry`; the three
live quarry sorries named by the LEDGER lane rules
(`Legacy/FundamentalTheorem.lean:172`, `Legacy/Amplification.lean:119`,
`CBCStructureGraph.lean:1415`) are all outside this file.

# T4 — THE H-COEFFICIENT TECHNIQUE

**What it is.**  Fix the *transcript* — the full record of an interaction.  If, for
every "good" transcript, the real world's probability of producing it is at least
`(1−ε)` times the ideal world's, then the statistical distance between the two
worlds is at most `ε + Pr[bad]`.  The point is that the hypothesis is a *pointwise
ratio of transcript probabilities*, which is a **counting problem** with the
adversary factored out; adaptivity survives because the environment's contribution
to a transcript's probability is a common factor that cancels in the ratio.  It is
the workhorse for concrete-security bounds (switching lemma, sum-of-permutations,
HCTR2, hash-then-PRF).

**Where the main bound lands (AC).**  `statDist` of two transcript laws, hence
`Adv⊥` after taking the supremum over `DDE.Total` and `n` — i.e. **exactly the
shape of `AC:Environment.lean:751`**.  T4 is the technique whose target distance AC
already has in the right form.

## Provenance — what the quarry ACTUALLY cites (not what one might assume)

Recorded verbatim, because the brief requires the tree's own citation and forbids
inventing one:

* `Q:HTechnique/Density.lean:15` — "`source theorem: Patarin/Jha-Nandi H-coefficient ratio bound;`"
* `Q:HTechnique/Density.lean:18` — "`source theorem: one-sided H-technique density ratio bound;`"
* `Q:HTechnique/Counting.lean:21` — "`source theorem: Jha-Nandi Proposition 8.1 counting core for the sum-of-permutations application.`"
* `Q:HTechnique/Derivation.lean:53-55` — "**Layer D′ (generalized H-lemma)** — the **Chen–Steinberger** partition form `δ ≤ Σᵢ εᵢ·Pr[cell = i]`"; also `:649`, `:1069` ("Patarin/Chen–Steinberger route").
* `Q:HTechnique/Derivation.lean:20-23` — the derivation follows "the chain of `DESIGN.md` §9 (thesis references: **Lanzenberger**, Defs 2.9–2.19, Lemma 2.18/App. A.1, Def 2.26, Thm 2.31)"; `:43-45` cites "thesis App. A.1; **CR18 Lemma 3.2**".
* `Q:HTechnique/HashThenPRF.lean:18` — "**Jha-Nandi §5.1, Lemma 5.1**"; `Q:HTechnique/TweakablePRP.lean:11` — "ePrint 2021/1441 §3.5, [HR03] App. C Lemma 6"; `Q:HTechnique/HCTR2Paper.lean:13` — "ePrint 2021/1441 p. 17".

**Names the quarry does NOT cite anywhere in `HTechnique/`**: Hoang, Tessaro,
Mennink, Bellare, Rogaway.  No bibliography entry, year, or full citation string
exists for Patarin or Chen–Steinberger — **they appear as bare author names in
prose.**  Under the AC naming/source rules, the transplant must upgrade these to
proper citations (paper + year + page), and must decide where Patarin/Jha-Nandi/
Chen–Steinberger sit relative to the SOURCE HIERARCHY, which does not mention them
at all (they are outside the MauRen16/Jost/LiuMau20/Lanzenberger list).  **Flagged.**

**Hygiene**: `grep -rnE "\bsorry\b|\badmit\b|^axiom "` over all 42 files of
`Q:RandomSystems/HTechnique/` returns **zero matches** — the quarry's H-technique
tree is sorry-free, admit-free, and axiom-free.

## Architecture of the quarry's technique (the layer names are the quarry's own)

| layer | content | quarry `file:line` | bounds | carrier |
|---|---|---|---|---|
| **C** | the distribution-level H-lemmas: ratio, expectation, eq-on-good, one-sided, mass-function, `fTransform` variants | **owner** `Q:RandomSystems/StatDist.lean:587,631,682,707,720,738,751,775,836,858`; forwarded by `Q:HTechnique/Density.lean:53-153` and `Q:HTechnique/TranscriptLawCore.lean:33,53` | `statDist` + `probBad` | plain `Dist A` |
| **B** | the σ·η **factorization / adaptive bridge**: a fixed-query pointwise ratio transfers to every environment (CR18 Lem 3.2 / thesis App. A.1) | `Q:HTechnique/Derivation.lean:212-220`, `:602`, `:634`; law-level owner `Q:RandomSystems/AdaptiveLawBridge.lean:597-609`, `:694-710`; representative compat `Q:HTechnique/AdaptiveBridge.lean:42-56`, `:98-116` | pointwise, then `statDist` | `ProbPDS`/`ProbPDE` |
| **D** | the **adaptive endpoints**: `Adv[q](S,T) ≤ δb + ε` from a fixed-query ratio + a *uniform* bad-mass bound | `Q:Derivation.lean:398-406`, `:439-445`, `:488-499`, `:540-546` | `adaptiveTranscriptAdvantage` | `ProbPDS` |
| **D′** | the **Chen–Steinberger partition** refinement | `Q:Derivation.lean:664-671`, `:691-697`, `:732-740` | `statDist`/`Adv` | `Dist` / `ProbPDS` |
| **E/E′/E″** | **extended transcripts**: reveal extra data `Z` (a key, a hash value) and run the ratio there; `σ⁺`, `aug` at the system and at the representative level | `Q:Derivation.lean:780-784`, `:797-811`, `:1076-1085`, `:1270-1285` | `Adv` | `ProbPDS` + `Dist (Transcript × Z)` |
| **F** | the fundamental-theorem side: `Adv ≤ lawStatDist`, `Adv ≤ Δ[q]` (thesis Thm 2.31 `≤`), and the **coupling reading** `Adv ≤ Pr_J[s ≠ s′]` (Thm 2.32) | `Q:Derivation.lean:1633-1637`, `:1648`, `:1667`, `:1683`, `:1789-1794` | `Adv` | `ProbPDS` + joint `Dist` |
| filtered/WLOG | filtered advantage, `EnvRespects`, the pointless-query self-answer WLOG, environment/chooser duality | `Q:Derivation.lean:1802-2373`, `:2719-3594`, `:3730` | filtered `Adv`, `maxAdvantage` | `ProbPDS` |
| counting | SoP fiber ratio; falling factorials, permutation-consistency mass, gate sums | `Q:HTechnique/Counting.lean:42`; `Q:RandomSystems/Counting.lean`; `Q:Derivation.lean:4071-4600`, `:4886-5030` | none (arithmetic) | `ℕ`/`NNReal` |
| defs | `fixedQueryAdv` (non-adaptive), `Adv` (adaptive, thesis Def 2.26), `advPRF/advNPRF/advPRP/advNPRP`, `filteredDelta_le_Adv` | `Q:HTechnique/SecurityDefs.lean:51,85,93,115,132,148,173,196,221` | — | `ProbPDS` |
| apps | HCTR2 (`HCTR2Paper.lean:2237`), TweakablePRP (`:940`), SoP (`SoPBoundary.lean:47-168`), HashThenPRF, switching (`Derivation.lean:5244`, `:5456`), StrongPRP models, ProjectedBirthday, RepeatNormalization, GF2Field | — | `Adv`/`advPRF`/`advPRP` | `ProbPDS` |

`Q:Derivation.lean:84-86` states the technique's single adaptive residue in the
quarry's own words: *"The residual adaptivity is isolated in exactly one
hypothesis: the bad-transcript mass `Pr_{tr(T,E)}[Bad]` is bounded uniformly over
environments; everything else is checked non-adaptively."*  **That sentence is the
integration contract** — it is what an AC endpoint must reproduce.

## What the target tree already has — Layer C, complete and name-for-name

`AC:Probability/StatisticalDistance.lean` carries an **independently proved** (not
aliased) port of the quarry's entire Layer C, same names, same hypotheses:

| declaration | `AC:Probability/StatisticalDistance.lean` |
|---|---|
| `probBad` (def) | `:651` |
| `probBad_const_pair`, `probBad_eq_evalPred`, `probBad_iUnion_le` | `:659`, `:668`, `:675` — **richer than the quarry's `Density` layer** |
| `statDist_le_of_one_sub_mul_le` (the shared engine) | `:629`; helper `sub_le_mul_of_one_sub_mul_le` `:618`; `statDist_le_sum_of_forall_tsub_le` `:609` |
| **`hTechnique_ratio`** | `:692` |
| **`hTechnique_expectation`** | `:736` |
| **`hTechnique_eq_on_good`** | `:787` |
| **`oneSided_hTechnique`** | `:812` |
| `oneSided_hTechnique_fTransform` | `:825` |
| `oneSided_hTechnique_proper` | `:843` |
| `hTechnique_ratio_massFunction` | `:856` |
| `oneSided_hTechnique_massFunction` | `:880` |
| `hTechnique_eq_on_good_fTransform` | `:972` |
| `hTechnique_ratio_fTransform` | `:994` |
| `statDist_partition` (the Lemma-2 *identity*) | `:903` |
| `statDist_fTransform_le` (DPI, Lemma 3) | `:928` |
| `statDist_eq_mass_on_zero_support` | `:1016` |
| `statDist_project_const_pair` | `:1100` |

Supporting ingredients confirmed present: `Distribution.mass` (`Distribution.lean:195`),
`mass_mono` (`:313`, whose comment `:309` records it was *"Promoted here from
`CR18.HTechniqueDerivation`"*), `mul_fTransform_le_fTransform_of_forall_mul_le`
(`:1208` — the exact ingredient `oneSided_hTechnique_fTransform` consumes),
`fTransform_fst_const_pair` (`:2010`), `mass_prod_and` (`:1769`), first-class
`expect` with `expect_indicator` (`Expectation.lean:65`, `:191`), Markov (`:232`),
and the coupling half `statDist_le_offDiagonalMass` (`Coupling.lean:264`) +
attainment `exists_coupling_offDiagonalMass_eq` (`:343`).

### CORRECTION to one negative finding (verified from disk)

A sub-report claimed the target tree has *no transcript layer at all*.  **That is
wrong**, and the matrix does not carry it: `AC:RandomSystems/System/Environment.lean`
contains 121 occurrences of "transcript" and defines `abbrev Transcript` (`:126`),
`trStep` (`:132`), `trN` (`:142`), `tr` (`:183`), `transcript` for total
environments (`:471`), and `trLawFullyDefined` (`:742`).  What is true is narrower
and is the actual finding: **`AC:RandomSystems/System/Transcript.lean` and
`Advantage.lean` and `Distinguisher.lean` are 10-line placeholders** — the reserved
*names* are empty because the content lives in `Environment.lean` instead.  The
real gap is not "no transcripts" but **"no fixed-query / q-indexed transcript
prefix type and no per-environment law indexed by a query vector"**.

## T4 matrix rows

| # | object / theorem | source (as the quarry cites it) | quarry home + delta | AC asset | verdict | size |
|---|---|---|---|---|---|---|
| T4.1 | Layer C: `hTechnique_ratio` + the eq-on-good / expectation / one-sided / massFunction / fTransform family | "Patarin/Jha-Nandi H-coefficient ratio bound" (`Q:Density.lean:15`) | `Q:StatDist.lean:587-872`; delta `none` | **`AC:StatisticalDistance.lean:692,736,787,812,825,843,856,880,972,994`** | **PRESENT** (complete, and richer on `probBad`) | — |
| T4.2 | `probBad` API + DPI + partition identity | thesis Lem 2.7 (data processing) per `Q:Derivation.lean:58` | `Q:Derivation.lean` | `AC:…:651-687`, `:903`, `:928` | **PRESENT** | — |
| T4.3 | coupling ⟹ `statDist`, with attainment | thesis Thm 2.32 | `Q:Derivation.lean:1683` | `AC:Coupling.lean:264`, `:343`, `:143`, `:196`, `:225` | **PRESENT** | — |
| T4.4 | **fixed-query transcript carrier**: a `q`-indexed transcript prefix type, `fixedQueryTranscriptDist`, `deterministicTranscriptDist`, weight normalization | CR18 Lem 3.2 / thesis App. A.1 | `Q:TranscriptLawPublic.lean:27,34,47,53,66,121,130,149,159`; `Q:FixedQueryLaw.lean:57`; `Q:TranscriptLawCore.lean:88,107`; delta `carrier` | AC has the *variable-length* transcript layer (`Environment.lean:126,471,742`) but **no `q`-indexed prefix type and no query-vector-indexed law**.  `System/Transcript.lean` is the reserved empty home | **MODEL-NEW** (the missing half the brief asked about) | **L** |
| T4.5 | **Layer B — the σ·η factorization / adaptive bridge** | CR18 Lem 3.2; thesis App. A.1 | `Q:Derivation.lean:212-220`, `:602`, `:634`; `Q:AdaptiveLawBridge.lean:597-609`, `:694-710`; delta `carrier` | **ABSENT** — no factorization of a transcript law into system × environment factors anywhere in AC | **TRANSPLANT** (REUSE-ARCH — the (★) identity `Q:Derivation.lean:634` is the whole proof) | **L** |
| T4.6 | Layer D adaptive endpoints `Adv ≤ δb + ε` | Patarin/Chen–Steinberger route (`Q:Derivation.lean:1069`) | `Q:Derivation.lean:398,439,488,540`; delta `both` | none; **target distance `Adv⊥` is already `statDist`-of-transcript-laws shaped** (`AC:Environment.lean:751`) | **TRANSPLANT** — restate on `Adv⊥`; needs T4.4+T4.5 | M |
| T4.7 | Layer D′ partition (Chen–Steinberger) | `Q:Derivation.lean:53-55`, `:649` | `Q:Derivation.lean:664-671`, `:691-697`, `:732-740`; delta `none` for the `Dist` form | **PARTIAL** — AC has the partition *identity* `statDist_partition` (`:903`) and disjoint-cell mass sums (`Distribution.lean:405`, `:441`), but **not** the partition *bound* | **TRANSPLANT** (small, delta `none`) | CLOSED (T0 dbe169e: hTechnique_partition :820 + ratio_via_partition :861) |
| T4.8 | Layer E extension lemma `π₁⋆P' = P ⟹ δ(P,Q) ≤ δ(P',Q')` | — | `Q:Derivation.lean:780-784`; delta `none` | **PARTIAL** — AC has `statDist_project_const_pair` (`:1100`) and `fTransform_fst_const_pair` (`Distribution.lean:2010`), not the general lemma | **TRANSPLANT** (small, delta `none`) | CLOSED (T0 dbe169e: statDist_le_of_extension :1104; general form :1092) |
| T4.9 | Layers E′/E″ — reveal/`aug` extended transcripts | — | `Q:Derivation.lean:1076-1085`, `:1270-1285`; delta `carrier` | ABSENT | **BLOCKED-ON** T4.4 | M |
| T4.10 | counting kernel (falling factorials, permutation-consistency mass, SoP fiber ratio, gate sums) | "Jha-Nandi Proposition 8.1" (`Q:Counting.lean:21`) | `Q:Counting.lean:42`; `Q:RandomSystems/Counting.lean`; `Q:Derivation.lean:4071-4600`, `:4886-5030`; delta `none` | **ABSENT** — AC has only generic uniform-mass atoms (`Distribution.lean:1571`, `:1588`, `:1732`) | **TRANSPLANT** (delta `none` — pure combinatorics, the cheapest large win) | CLOSED (T0 ce0eb22: Probability/Counting.lean, 34 declarations; residue available cheaply: two-sided birthday, sorted-pair sums, function fibers, block-major encoding, re-randomisation fibers) |
| T4.11 | security-definition wrappers (`fixedQueryAdv`, `Adv`, `advPRF/PRP`, `filteredDelta_le_Adv`) | thesis Def 2.17/2.19/2.26 (`Q:SecurityDefs.lean:17-23`) | `Q:SecurityDefs.lean:51-234`; delta `both` | `System/Advantage.lean` is the reserved empty home; `Adv⊥`/`Adv`/`AdvD`/`Δ` all exist in `Environment.lean`/`ClassDistance.lean` | **TRANSPLANT** — but re-target: AC does **not** need a second advantage object, only the `q`-filtered *reading* of `Adv⊥` | M |
| T4.12 | filtered advantage + pointless-query self-answer WLOG + environment/chooser duality | `Q:Derivation.lean:1804-1809` (the paper's §3.4 restriction, and the quarry's note that it is **NOT** WLOG when the two worlds are not both permutations) | `Q:Derivation.lean:1802-2373`, `:2719-3594`, `:3730`; delta `both` | ABSENT | **TRANSPLANT** — and the "not WLOG" caveat must travel with it | L |
| T4.13 | application kits (HCTR2, SoP, hash-then-PRF, switching, tweakable/strong PRP, projected birthday) | ePrint 2021/1441; Jha-Nandi §5.1; [HR03] | `Q:HTechnique/*` | AC has `Probability/UniversalHash.lean` (299 lines), the ε-AXU family hash-then-PRF consumes | **BLOCKED-ON** T4.4–T4.6 | L (out of first scope) |

**T4's headline for pricing: the technique is exactly half-present.**  The
*mathematical kernel* (Layer C) is landed and needs nothing.  What is missing is
the *system-facing half* — a `q`-indexed transcript prefix, the σ·η factorization,
and the adaptive endpoint — and that half is `carrier`-delta work, not new
mathematics.  Two of the remaining refinements (T4.7, T4.8) and the whole counting
kernel (T4.10) are delta `none` and can be transplanted immediately, before any
carrier decision.

# THE RESERVED HOMES (from disk) — and their build status

The target tree already carries the technique program's module names, all as
10-line placeholders reading "Target module for the random-systems migration.
Not yet populated.":

| reserved module | lines | status |
|---|---|---|
| `AC:RandomSystems/Game/Game.lean` | 10 | placeholder |
| `AC:RandomSystems/Game/MonotoneCondition.lean` | 10 | placeholder |
| `AC:RandomSystems/Game/Winnability.lean` | 10 | placeholder |
| `AC:RandomSystems/Technique/ConditionalEquivalence.lean` | 10 | placeholder |
| `AC:RandomSystems/Technique/HCoefficient.lean` | 10 | placeholder |
| `AC:RandomSystems/Technique/Switching.lean` | 10 | placeholder |
| `AC:RandomSystems/Technique/DataProcessing.lean` | 10 | placeholder |
| `AC:RandomSystems/System/Coupling.lean` | 10 | placeholder |
| `AC:RandomSystems/Interface/{Interface,Alphabet}.lean` | 10 each | placeholder |

**None of them is imported anywhere** (`grep -rn "RandomSystems.Game|RandomSystems.Technique|RandomSystems.Interface|RandomSystems.System.Coupling"` over `AC/**.lean` returns nothing), and `AC:RandomSystems.lean` (29 imports) does not reach them.  They are reserved names, not wired build targets — so the first leg in each lane pays a small wiring cost, and the ledger gate must be re-run because `System/Coupling.lean` sits under `RandomSystems/System/`, which the LEDGER rule says must be fully classified.

# INTEGRATION ARCHITECTURE

## The tree's existing layers, and where each technique attaches

```
  L0  Probability/            Distribution, statDist, Coupling, MultiCoupling,
                              FiberCoupling, Expectation, UniversalHash
        |                     statDist  : Probability/StatisticalDistance.lean:142
        |                     cond      : Probability/Distribution.lean:476  (Part-valued)
        |
  L1  System/DiscreteSystem   DDS X Y (partial), keptPrefix :206, fullyDefined :214,
        |                     filterQueries :403, historyEvaluator :157, QBounded :37
        |
  L2  System/Environment      DDE.Total :399, transcript :471,
        |                     trLawFullyDefined :742,  **Adv⊥ = advFullyDefined :751**
        |                     Adv :324 (off-pin), AdvD :360, HasDomain :284
        |
  L3  System/ClassDistance    equivalent (Def 2.17) :1322,
        |                     **classDistance (Def 2.28) Δ :1546**,
        |                     Adv⊥ ≤ Δ  :1671   (unconditional)
        |
  L4  System/Attainment       Thm 2.31 / 2.32 at presentations;
        |                     HaveCommonDomainAndBounded :481
        |
  L5  System/Behaviour        Behaviour quotient :151, EMetricSpace :273,
        |  BehaviourAttainment Thm 2.31 :149, attainment :165, coupling Thm 2.32 :233/:258
        |
  L6  System/DistinguisherClass :42  →  AbstractCryptography (Jost Def 2.2.8)
        |
  (orthogonal)  AbstractCryptography/EventAlgebra.lean  (775 lines, GegMau26)
```

**Every technique's main bound lands on `Adv⊥` (`Environment.lean:751`)**, and
crosses to `Δ` through the *already-proven* `advFullyDefined_le_classDistance`
(`ClassDistance.lean:1671`) and, on the finite shared-domain slice, the identity
`classDistance_eq_advFullyDefined_of_commonDomain_bounded`
(`BehaviourAttainment.lean:149`).  No technique needs a new distance.

## Dependency order of the four techniques

```
        [T2.1  events/MBO object]         ← Jost primary; AC EventAlgebra present
                  |
                  v
        [T1.1-T1.3  game carrier + S⁻ + CE definition]
             /            \
            v              v
  [T3.1-T3.4  ν, ω,   ]   [T1.4-T1.6  filtration algebra,
  [ game equivalence  ]   [  seed kit, gameEnhance     ]
            |                          |
            v                          v
  [T3.5-T3.8  WINNABILITY ]  ---->  [T1.7/T1.8  CE ⟹ Adv⊥ ≤ Γ / Γᵇ]
  [  ν = ω + attainment   ]              |
   (consumes AC Thm 2.31)                v
                                 [T2.2  completeness of the method]

  [T4  H-coefficient]  — INDEPENDENT of T1/T2/T3; consumes only L0+L2
        (transcript laws + statDist), not the game layer
```

Three load-bearing observations:

1. **T3 is a prerequisite of T1's *useful* form, not a sibling.**  T1's endpoint is
   only valuable because its right-hand side `Γ`/`Γᵇ` is computable, and what makes
   it computable is T3.8 (`ν = ω`: the sup over strategies collapses to a mass) and
   T3.7 (bit-adaptivity is useless: the sup is over *blind* strategies).  Ordering
   T1 before T3 buys an endpoint whose RHS nobody can evaluate.
2. **T3.8's proof consumes AC's Thm 2.31, which is already landed.**  The quarry's
   route (`Q:GameWinnability.lean:58-77`) reduces winnability to attainment rather
   than repeating the thesis induction — and `AC:Attainment.lean` +
   `AC:BehaviourAttainment.lean` supply exactly that, at both the presentation and
   the quotient level, including the coupling form.  This is the cheapest large
   theorem in the program.
3. **T4 is architecturally disjoint.**  It bounds `statDist` of transcript laws
   directly and never mentions a game, an MBO, or a winning probability.  It can be
   run in parallel with T1-T3 by a second lane with no merge conflict beyond
   `Probability/StatisticalDistance.lean`.

## Naming obligations under the three-layer convention

Quarry names that are **COINAGES** and must be renamed-or-flagged in AC:
`massYAfalse`, `massAfalse`, `massY`, `massDom`, `TotalOnNonempty`, `gameEnhance`,
`combineSys`, `zeroMBO`/`zeroMBODist`, `blindize`, `blindMaxWinProb`,
`prewinBehavior`, `wonFlag`, `gameTranscriptView`, `Winnable` (thesis says
"winnable", so this one is a paper name), `supWinProb`/`infWinnability` (the paper
symbols are `ν`/`ω` — the spelled-out names are house-pattern coinages of the
symbols, the mildest category).

# CONFLICTS — what each technique's transplant must RE-READ because of the carrier change

Per the brief: **flagged, not solved.**  Each row names the quarry decision, the AC
ruling it meets, and the specific statement that has to be re-derived rather than
copied.  Nothing here is a defect in the quarry — these are consequences of a
deliberate carrier change.

## C1 — RS-PARTIAL-001 (partiality intentional) vs R1 (fully defined is the carrier)

The quarry's governing decision, retrieved from its own decision store:

> **RS-PARTIAL-001** — "CR18 partial systems and observable bottom are intentional.
> Model CR18 systems as prefix-closed partial functions and preserve the
> observable-bottom conventions.  **Partiality is a modeling choice, not a defect
> to erase through an unrelated total carrier.**"  (authority: quarry `DESIGN.md`
> §8; anchors `RandomSystems/PFunDDS.lean`, `RandomSystems/PDS.lean`)

AC's R1 says the *official interaction carrier* is the **fully defined slice**,
partial systems entering via `s⊥`, "deletion is the embedding's shape, not an
interaction rule" (`AC:PHI-SPEC.md:14-18`).

**These are not contradictory at the level of objects** — AC keeps the partial
`System.DDS` and completes it — but they are contradictory at the level of
*where a statement lives*.  Every quarry technique theorem is stated on the
partial object with partiality-aware hypotheses; every AC technique theorem must
be stated after completion.  The four re-reads this forces:

| # | what must be re-read | why |
|---|---|---|
| C1.1 | **`TotalOnNonempty`** (`Q:CondEquiv.lean:96`) — "every support realization accepts every nonempty history" | This is the quarry's rendering of the papers' standing "systems are defined on the histories under discussion".  Under R1 **every** system is total after `⊥`-completion, so the hypothesis is either vacuous (drop it) or it is secretly saying something else (that no query is *refused*, which after completion is an observable statement about the answer being `some`).  Deciding which is a **statement-shape decision**, and it propagates to every endpoint: `Q:Theorem417.lean:764`, `Q:GameOf.lean:1431`, `:1472`, `Q:HistoryConditionC.lean:450`. |
| C1.2 | **the CE conditioning event** | `CondEquiv` (`Q:CondEquiv.lean:118`) is guarded by `massAfalse Ŝ xⁱ ≠ 0 → massDom T xⁱ ≠ 0 →`.  `massDom` (`:88`) is *the mass of realizations that accept `xⁱ`* — a **partiality** normalizer.  After completion `massDom` is the total weight (`Q:CondEquiv.lean:131` already proves this under `TotalOnNonempty`), so the guard collapses on one side but **not** the other: `massAfalse ≠ 0` survives as CR18 footnote 29's "where both are defined".  The AC definition therefore has *one* guard, not two — a genuinely different `Prop`. |
| C1.3 | **the MBO bit under completion** | A game is `PDS X (Y × Bool)`; completion gives answers in `Option (Y × Bool)`, so a **refused round carries no bit at all**.  The quarry anticipated exactly this: `WinningTranscript` is the `∃`-form ("some *answered* query carries MC bit 1") and its docstring says so is "the faithful reading in the `⊥`-totalized model (where a rejected query is answered `none` and deleted)" (`Q:GameWinnability.lean:105`, header `:36-40`).  **The `∃`-form transplants; the "transcript ends with `(·,1)`" form does not.**  What must be re-derived is `MonotoneMBO` (`Q:PDS.lean:3101`), a *support-wise per-realization* property whose interaction with completion is not stated anywhere. |
| C1.4 | **the environment class** | Quarry `ν` (`Q:GameWinnability.lean:248`) sups over `Winner X Y = DDE X Y` — the *partial* environment.  AC's `Adv⊥` sups over `System.DDE.Total` (`AC:Environment.lean:399`, `:751`).  The winnability theorem's `ν` must move to `DDE.Total` or the two sides of `ν = ω` are indexed by different sets.  Note AC already has the pruning apparatus for exactly this migration (`AC:ClassDistance.lean:603-897`: `pruneStep`/`Blocked`/`pruneRun`/`prunedEnv`). |

## C2 — the sources themselves have no ⊥ convention (a *source*-side conflict)

Verified: **CR18 §4.10–4.11 contains no `⊥`, no refusal, and no partial-domain
apparatus.**  Its standing simplification `[printed p. 105]` pads short runs with
**dummy queries** to fixed-length `(X^q, Y^q)` transcripts.  MPR07 and Maurer13b
likewise work with `p_{Yⁱ|Xⁱ}` on all histories.

*This is good news for AC and bad news for verbatim transplanting.*  AC's
`advFullyDefined` — a supremum over `DDE.Total` environments **and over lengths
`n`** of `statDist` of transcript laws (`AC:Environment.lean:751`) — is a very
close formal match to "fixed-length `q`-transcripts, sup over `q`".  The quarry's
`QueriesExactly (i+1)` hypotheses on `D.support` (`Q:Theorem417.lean:724`, `:764`)
and its whole `DeltaFiniteQueryNormalization` apparatus
(`Q:GameOf.lean:1163`, `:1176`, `:1204`) exist to *recover* that fixed-length
reading inside a partial, variable-length model.  **Under R1 much of that
normalization layer may simply not be needed** — which is a cost saving, but it
means those hypotheses cannot be copied across; they must be re-derived or dropped
with an argument.  Flagged as the single largest "the transplant is smaller than
it looks" item, and also the largest risk of silently weakening a theorem.

## C3 — the `Δ` vocabulary trap, twice over

The LEDGER already records that quarry `Δ(S,T)` = `maxAdvantage` while AC `Δ` =
`classDistance` (`AC:LEDGER.md` M4 vocabulary table).  The source ledger above adds
a **second** layer of the same trap:

* **MPR07 `δ` vs `Δ`** `[p. 140]`: `Δ_k^D ≤ δ_k^D` in general, with equality only
  for an unbounded optimally-deciding `D`.  Lemma 5's per-`D` equality is with `δ`.
* **AC's `Adv⊥` is `δ`-shaped** (a sup of `statDist` of *transcript* laws), not
  verdict-probability-shaped.  So the T2 transplant lands on the *favourable* side
  of MPR07's caveat — but only if the statement is written against `Adv⊥` and not
  against a verdict advantage.
* **Sign/argument order.**  CR18 defines `⟨S|T⟩(D) = Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`
  — **`T` first, signed, no absolute value**, and `Δ := sup_D` of that signed
  quantity.  This is precisely the LEDGER lane rule "`adv_eq_maxAdvantage_swap`:
  the argument order SWAPS — the naive pairing is documented refutable".  Every
  T1 endpoint is one-sided in this sense and must be transcribed with the swap.

## C4 — a NON-conflict worth recording (so no leg re-litigates it)

**R9 and the quarry's `ω` already agree.**  R9 requires `classDistance` to
infimize over *honest* (`NonNeg`) representatives.  `Q:GameWinnability.lean:294`
defines `infWinnability` as an `sInf` over `{H | H.NonNeg ∧ GameEquivalent H G}`,
and its docstring gives R9's exact reason: "on the signed carrier the conjunct
`H.NonNeg` has to be written down … dropping it would let a signed `H` with the
same observable drive the infimum to `−∞`."  The quarry independently arrived at
AC's ruling.  **`ω` transplants with its honesty clause intact; no re-reading
needed.**

## C5 — CE's polarity and shape (source-side, carrier-independent)

Traps 1–3 of the source ledger (polarity flip; one-step vs joint CE; adaptive vs
non-adaptive RHS) are **not** carrier issues but they will bite exactly as hard.
The quarry follows the CR18 polarity and the joint CE form; a leg that reaches for
Maurer02 (a primary is not available for CE — see C6) must flip and convert.

## C6 — the SOURCE HIERARCHY problem for T1 (structural, needs a ruling)

The hierarchy is MauRen16 > Jost > LiuMau20 > Lanzenberger, with **CR18
fallback-only, "ONLY for a concept none of the primaries addresses"**
(`AC:LEDGER.md:8-10`).  From disk and from the visual reads:

* **Conditional equivalence is not in any of the four primaries.**  It is in
  Maurer02 (Def 6), Maurer13b (Def 13), and CR18 (Def 4.19).  The Lanzenberger
  thesis Ch. 2 — the one primary with a games layer — has **no CE definition at
  all** (§2.3.3/§2.4.3 enumerated exhaustively above).
* **MBOs *are* addressed by a primary**: Jost states events generalize MPR07's
  MBOs (per `Q:RandomSystemsCC/EventHistory.lean:10-40`; visual re-verification
  owed).
* **Games/winnability are addressed by a primary**: Lanzenberger Defs 2.20–2.25,
  2.35–2.36, Thm 2.37.

So the honest reading is: **T3 is primary-sourced (Lanzenberger); T1's MBO object
is primary-sourced (Jost, as events); T1's CE relation and its main theorem are
CR18-fallback material** (with Maurer02/Maurer13b as the *original* sources, which
sit outside the hierarchy list entirely).  That is a hierarchy question the
register does not currently answer — **flagged for Marc**, with the registry-check
done: neither the PRIMITIVE REGISTRY nor PHI-SPEC nor the CR18-FALLBACK register
mentions CE, games, or MBOs.  Suggested shape of the ruling (not applied): add CE
+ Thm 4.17 to the CR18-FALLBACK register with Maurer13b named as the preferred
citation, since Maurer13b is the paper whose statement AC would actually be
formalizing (non-adaptive RHS, joint form).

# SKILLS REVIEW — can the quarry's skills be re-based onto AC?

**Framing fact established first**: `AC` has **no `.claude/` directory at all** — no
skills exist on the target side today, and no `.mcp.json` and no `tools/rs-memory`.
So this is a *port*, not a merge.  The quarry's four files total 1,531 lines.

## Per-file verdict table

| file | lines | (a) what it prescribes | (b) quarry-carrier-bound | (c) transfers as-is | verdict |
|---|---|---|---|---|---|
| **`Q:.claude/skills/random-systems-proofs/SKILL.md`** (+6 `references/`) | 466 | rs-memory preflight; the premise that every statement is an advantage bound proved by a **closed set of seven technique families**; a **7-stage checklist** (SKETCH → DAG → REUSE SEARCH → AUDIT → SKELETON → FILL LEAVES → RECEIPTS) with an artifact and a gate each; the stage-4 source audit (quote the sentence, sum the number); Lean-free stage 1; the **routing ladder**; the `[LIB]`/`[ROUTINE]`/`[CREATIVE]` obligation ledger; five proof-shape rules; 18 rationalizations to reject | **20 items**, incl.: `Δ(S,T)`/`maxAdvantage`/`maxEDist` as statement targets (`:3`, `:115`, `:216-221`, `:250-253`, `:311`, `:426-428`) — all forbidden by pin 2; **the entire `[ROUTINE]` tactic table** `cr18_*`/`htechnique_*` (`:190-199`) — *zero* of which resolve in AC; **"`cr18_total` fails ⇒ the system carries partiality it should not"** (`:207`, `:414-415`) — **exactly backwards under R2**, where refusal is observable and non-fatal; "family I, is the distance ZERO, CHECK FIRST" (`:134`) — but in AC `Δ(S,S) = ⊤` off the honest carrier (R9); `CHEATSHEET.md` "**Always first**" and `LanzenbergerChain.lean` (`:288-289`, `:370-374`) — **neither file exists in AC**; the `Adv S T = Δ(T,S)` orientation (`:324-326`) pins the documented swap to the wrong pair; `rs_prepare_task` preflight (`:10-16`) | the whole stage-4 source-audit discipline (`:38-67`); Lean-free stage 1 + the anchoring argument (`:69-98`); the freedom-per-stage table; the three-class obligation ledger *as a concept*; skeleton-compiles-first (`:211-234`); **all five proof-shape rules** (`:236-280`); DPI-as-pushforward; most rationalizations | **RE-BASE AS METHOD ONLY** — the workflow is gold, the entire endpoint catalogue, metric vocabulary, tactic layer and reuse index are quarry-bound |
| **`Q:.claude/skills/cc-constructions/SKILL.md`** (+1 reference) | 227 | audit-before-building as rule #1; the **L0–L6 tower** and "almost every failure mode is working at the wrong floor"; the **two-intervention rule** (probability enters exactly twice); the **identity ladder** (rungs 1–3, zero-slack rule); the reduction pattern; the leaf handoff to `random-systems-proofs` | **worst of the four.** Carrier rows `DependentDDS`/`PFunDDS`/`Machine`/`TypedResource` (`:46-48`) — none exist in AC; the whole **"Maurer-pass surface"** paragraph (`:52-63`) incl. `α •[i] R` and a **glyph collision**: `≈[ε]` exists in AC too, as MauRen16 Def 2; **"Prefer total machines: `step = none` is blocking divergence"** (`:96-99`) — a **direct contradiction of R2**; `Services`/`Services.free` kernel codes (`:103-109`) — the shape AC's C8 spike **REFUTED**; every discovery pointer (`Jost.lean`, `CHEATSHEET.md`, `DESIGN.md §10.11`, `STATUS.md`) | audit-before-building (`:17-26`); wrong-floor diagnosis; the **two-intervention rule** and "never cross a specification boundary" (`:65-75`); the identity ladder + zero-slack rule (`:111-131`); the reduction pattern; the leaf-handoff protocol incl. "**never a conclusion-shaped hint**" (`:144-149`) | **REWRITE** — keep four principles, replace the tower, the surface, and the totality ruling |
| **`Q:skills/PROOF-WORKFLOWS.md`** | 643 | self-described "design prep for a skill", read off the quarry at commit `4376f54` with a `file:line` per claim; the six-stage workflow; **per-technique obligation ledgers** (H's three axes/five analyses, CE's two doors, coupling, winnability, counting); 13 anti-rabbit-hole rules; the measured cost of a wrong technique choice | pinned to the quarry tree by construction (`:14`); the family-II table is *entirely* `maxAdvantage_*` (`:451-456`); **§3.9 literally instructs "State headline results in `Δ`"** (`:478-481`) — i.e. instructs a pin-2 violation; a 15-endpoint H catalogue and CE/coupling/winnability door lists that **do not exist in AC**; legacy-carrier entry points incl. two of the three never-forward sorries; `ccprover` framed as reference-only — **in AC it is a downstream consumer to build**; the coupling exactness claim (`:421-423`) stated **without** AC's finiteness bundle, licensing a false exactness claim | §0's tractability argument; the six-stage workflow with artifact+gate; the sketch's five required contents incl. "**technique choice, with the negative**"; the DAG node contract; "**a `NEW` verdict with no search record is not a verdict**" (`:267`); receipts + axiom envelope; §3's *questions* minus every name; **rule 12: papers are read visually, text extraction fails silently** (`:502-503`); "**never pass a conclusion-shaped constraint or another agent's unverified claim to a subagent**" (`:578-581`) | **HARVEST** — mine the workflow and the per-technique *questions*; discard the catalogue |
| **`Q:.claude/skills/writing-lean-proofs/SKILL.md`** (+5 references) | 195 | "design top-down, prove bottom-up; statements are the stable interface, proofs are disposable"; design definitions **and their API** first; sorry-skeleton at project and proof scale; one focused goal at a time; verify mechanically; the extraction ladder; a rule table with the enforcing linter per row | **almost none** — 4 frictions, all EDIT-sized: "prefer total functions with **junk values** over `Option`" (`:45-47`) — in AC `none` **is** the semantics (R1/R2); "defer to CONTRIBUTING" (`:34-36`) — AC has none; the `! grep sorry` recipe (`:107-110`) vs AC's four scans; "name lemmas from their statements" (`:167`) — insufficient under AC's paper-names-first + COINAGE rule | essentially the whole file | **RE-BASE WITH ~4 EDITS** — the cheapest port |

**`research-memory`** exists as a fifth quarry skill (41 lines) and routes to the
`rs-memory` MCP + the page-addressable PDF corpus.  AC has neither the MCP config
nor the corpus (the papers live in the quarry).  Its *rule* — "extracted text is
navigation only until the original page is visually checked" — must survive the
port even though its mechanism cannot.

## The one asset worth porting intact: technique-selection guidance

**It exists**, and it is the strongest thing in these files.  The routing ladder at
`Q:.claude/skills/random-systems-proofs/SKILL.md:131-146` (duplicated verbatim at
`Q:skills/PROOF-WORKFLOWS.md:313-328`) answers exactly the charter's question:

```
0. Is the distance ZERO?        → family I. CHECK FIRST.
1. Can Δ be split or stripped?  → family II reshape (hybrid / DPI / restriction).
2. What is the "bad thing"?     → family III — THE choice point:
     a bad TRANSCRIPT           → H-technique
     a CONDITION the adversary triggers, adaptive/stateful
                                → conditional equivalence
     DISAGREEMENT under shared randomness
                                → coupling
     the adversary WINNING a given game
                                → winnability
3. Discharge the probability    → family VI counting
4. Arithmetic                   → cr18_arith / cr18_algebra / cr18_close
```

plus the discipline that makes it real: *"State the technique **and the alternative
you rejected, with a reason**.  A sketch that cannot say why the other door is wrong
has not chosen a door."* (`:156-157`).  Secondary preference rules exist too:
CE-vs-winnability — *"Overlaps CE heavily — **prefer CE** unless the game is given
rather than derived"* (`PROOF-WORKFLOWS.md:437-438`); within-H — *"take the most
special variant that applies"* (`:359`); coupling exactness — optimal vs online, and
*"say **which** of the two is the source"* of slack (`:424-431`).  And the cost of
choosing wrong is measured: CE (packaged) proved a theorem in ~11 lines; the
H-technique proved the same theorem with **~90 lines of glue and zero new
mathematics** (`:541-547`).

**Eight things that guidance is missing for AC**, and they are the highest-value
additions a re-based skill would make:

1. **No selection axis on the statement target.**  AC makes `Adv⊥` vs `classDistance`
   a first-order choice, and it constrains technique: R4′ says *"coupling bounds land
   on `Adv⊥`"*, and R9 restricts `classDistance` to honest representatives.
2. **No admissibility preconditions per technique.**  `PROOF-WORKFLOWS.md:421-423`
   asserts the optimal coupling's disagreement *equals* `Δ` with **no hypotheses**;
   AC records attainment as **FALSE** without the finiteness bundle
   (`AC:LEDGER.md:1140-1142`, counterexample at `AttainmentCounterexample.lean:766`).
3. **No refusal/⊥ axis.**  Nothing asks whether the argument survives observable
   refusal (R2) or needs the strict `HasDomain`/`CompatibleD`/`AdvD` layer.
4. **No converter axis.**  Pin 3 routes converter-attaching work to the MR16 track;
   the ladder has no such node, so a CE-vs-coupling call could be made in the wrong lane.
5. **No source-anchored technique identity.**  The SCOPE AMENDMENT names each
   technique's source; the ladder cites none, so a choice cannot be checked against
   the SOURCE HIERARCHY.
6. **No completeness/ceiling statement** — which is precisely **T2** of this matrix.
   MPR07 Lemma 5 is the missing "is this the technique's ceiling or my choice's?" half.
7. **The module-route heuristic is unusable on AC** — it reads the route off
   `CHEATSHEET.md` §9, and every AC technique module is an empty placeholder.
8. **AC has the list but not the criteria.**  `AC:AGENTS.md:102-103` enumerates
   routes ("direct metric, simulator, conditional equivalence, coupling,
   H-coefficient, hybrid, or reduction") with **zero** selection guidance, and
   `:209-210` forbids automating the choice.  So: **AC has the list, the quarry has
   the criteria, and neither has criteria calibrated to `Adv⊥`/`classDistance`.**

## Delta list for the re-based AC skill (52 items, condensed by theme)

Tags: **KEEP** / **EDIT** / **DROP** / **NEW**.  Every item cites its source.

**Identity & preflight** — 1 EDIT the frontmatter description off `Δ(S,T) ≤ ε` onto
`Adv⊥`/`classDistance` (`SKILL.md:3`).  2 NEW a *regime preflight*: read `PHI-SPEC.md`
in full + `LEDGER.md` (source hierarchy, the four pins, lane rules) and **run
`scripts/ledgerAudit.sh` before planning** (`AC:LEDGER.md:36-37`).  3 DROP the
`rs_prepare_task`/`tools/rs-memory` preflight (no MCP in AC).  4 KEEP the rule it
carried: extracted text is navigation until the page is visually verified.

**Metric & carrier** — 5 EDIT every `Δ(S,T)`/`maxAdvantage`/`maxEDist`/`Adv[q]` to
`Adv⊥`/`classDistance`, **with the explicit warning that quarry `Δ` means
`maxAdvantage`**.  6 NEW an opening "which metric is your statement in?" with the
R4′ crossing API and its two connection lemmas.  7 EDIT the "≤ vs =" receipt to carry
its finiteness hypotheses.  8 EDIT the orientation rule to AC's recorded
`adv_eq_maxAdvantage_swap` fact.  9 EDIT family I: `Δ(S,S) = ⊤` off the honest
carrier; zero distinguisher distance is not generic equality.  10 NEW the carrier
paragraph (`Φ`, the fully-defined slice, `s⊥`, `ofTyped` as the only typed↔Φ transfer).

**Partiality** — 11 DROP "`cr18_total` fails ⇒ the system is defined wrong".
12 DROP "prefer total machines; `step = none` is blocking divergence".  13 NEW the R2
paragraph in their place (refusal observable and non-fatal for every system,
converters included; both proposed violations refuted).

**Tactics, gates, dev loop** — 14 DROP the whole `[ROUTINE]` tactic table.  15 KEEP
the three-class ledger as a *concept*, noting AC's `[ROUTINE]` class is the
`ac_*`/`cc_*`/`rs_*` command surface plus `inferInstance`.  16 NEW the **four
ledgerAudit gates** and what each catches: (1) every top-level `def`/`abbrev`/
`structure`/`instance` under `System/`+`Converter/` must appear as a whole word in
`LEDGER.md` — *presence, not correct classification*; (2) the MR11 provenance fence
at **import granularity** (fails if the fenced list is empty); (3) a tripwire on the
three REFUTED names `relayExcept`/`attachFullyAt`/`botToken`; (4)
`lake env lean RandomSystems.lean` must elaborate, because the build globs exclude it
and a cross-lane duplicate declaration can hide behind a green build.  17 NEW AC's
verification recipes + the `#print axioms` envelope.  18 EDIT the dev loop: keep
"read the goal state, not the build log"; note `lake build RandomSystems` in AC globs
**all** submodules, unlike the quarry.  19 DROP "do not write `private`" — no AC gate
enforces it.

**Reuse, transplant, provenance** — 20 DROP `CHEATSHEET.md`-first and
`LanzenbergerChain.lean` as the anti-false-gap check.  21 NEW the LEDGER reuse order
(tree declarations → quarry **architecture** cited `file:line` → quarry statement
**shapes** restated, never copied) and "building fresh what the quarry already proves
is a brief violation".  22 NEW the delta vocabulary (`carrier`/`metric`/`both`/`none`)
and verdicts (`REUSE-ARCH`/`REUSE-STMT`/`REF-ONLY`/`NONE`), **replacing** the quarry's
REUSE/ADAPT/NEW scale.  23 NEW the seven transplant rules as a checklist.  24 NEW the
quarry rule (READ-ONLY, always; never imported or built).  25 NEW the SOURCE HIERARCHY
+ CR18 demotion + the five-item fallback register + the duty to say so explicitly.
26 EDIT "CR18 numbering is not evidence of conformance" into "CR18-derived **names**
stay; their docstring citations are historical provenance, not authority".  27 NEW the
**derived-from-disk** rule with its defect record (planning from memory missed
`connect`) — never plan a leg from a remembered inventory.  28 NEW the MR11 fence.

**Naming & statements** — 29 NEW the three-layer naming convention with COINAGE
flagging in **both** docstring and ledger row.  30 EDIT the naming rule with AC's bans
(no paper numbers, task numbers, author initials, or proof-method words in public
names).  31 EDIT "prefer junk values over `Option`" — on AC's carrier `none` is
meaningful refusal.  32 NEW the **ledger-registration duty** for any new declaration
under `System/`/`Converter/` — a skill about *defining things* that omits this
produces a red gate on first use.  33 EDIT house-style deferral to
`AGENTS.md`/`LIBRARY_GUIDE.md`/`LEDGER.md`.  34 EDIT the `sorry` grep to AC's four scans.

**CC-modeling skill** — 35 EDIT the tower onto AC's layers.  36 DROP the whole
Maurer-pass surface paragraph.  37 NEW R7″ in its place (`attachAt`,
`converterMonoidAt`, `parF`, the fn.23 ruling, `α∣α = α²` recorded,
`IsNonexpandingPar` unconditional NOT obtainable).  38 NEW a **glyph warning**: `≈[ε]`
in AC is MauRen16 Def 2, not the quarry's surface closeness.  39 DROP `Services`/kernel
codes; NEW R3 + the C8 lesson (value-level addressing; type-level tags REFUTED).
40 KEEP the identity ladder, the two-intervention rule, "never cross a specification
boundary", the reduction pattern, the leaf handoff — restated on AC names.  41 NEW the
PRIMITIVE REGISTRY + SUPERSEDED list as the "what may I author against" gate.  42 NEW
AC's `ac_*` surface, the CNL sentence contract, and the mandated H-coefficient section
order `Model / Representatives / TranscriptExtension / BadEvent / GoodRatio / BadMass /
MainLemma / ConstructionOrReduction`.

**Process, escalation, honesty** — 43 NEW the ESCALATION FILTER (check registry +
rulings before raising a fork; reports must cite the registry entry checked against).
44 NEW the doc-authority rule — **flagged**: it has *no written home in AC today*
(grep of `LEDGER.md`/`PHI-SPEC.md`/`AGENTS.md`/`README.md` returns nothing); a
re-based skill would be its first, and its nearest neighbour `AC:AGENTS.md:320-331`
independently forbids agents from creating completion ledgers or audit notes.  45 KEEP
"never pass a conclusion-shaped constraint or another agent's unverified claim to a
subagent — doing so launders a guess into evidence"; no `sorry` allowances in a
dispatch.  46 NEW AC's own verification-honesty precedent: *"none of the four surveys
ran `#print axioms`, so 'axiom-clean' is not established, only 'no source-level
`sorry`/`axiom`'"*.  47 NEW the scope gate: technique program open per the amendment,
**survey matrix first, then legs**; L5 amplification applications stay deferred.
48 NEW a "the endpoints do not exist yet" branch in routing — AC's `Technique/`,
`Game/`, `System/{Advantage,Coupling,Distinguisher,Transcript}` are placeholders, so
stage 3 usually terminates in a **transplant verdict with a delta**, not an endpoint
citation.  49 NEW pin-3 lane routing.  50 KEEP the stage-4 source audit, Lean-free
stage 1, skeleton-first, leaves-first, the five proof-shape rules, the adaptation
table, "after the second failed fix, restate", "compiling is the floor".  51 EDIT the
"structure whose fields are the creative obligations" design note to bind it to AC's
automation policy — **never a tactic that selects the proof route**.  52 EDIT the
`ccprover` framing: in AC it is a downstream consumer to build, not reference-only.

## Recommendation

Port as **two** AC skills plus one shared reference, not four:

* **`ac-lean-proofs`** — the `writing-lean-proofs` re-base (items 30–34), cheapest,
  do it first; it is the one an agent needs on day one.
* **`ac-random-systems-proofs`** — the method half of `random-systems-proofs` +
  `PROOF-WORKFLOWS`'s workflow and per-technique *questions*, with the routing ladder
  rebuilt around the eight missing axes above.  **This skill cannot be finished before
  the technique legs land** — items 48 and the whole routing ladder depend on
  endpoints that do not yet exist.  Write it incrementally, one technique at a time,
  as each leg closes.
* **`ac-cc-constructions`** — the four surviving principles on AC's tower.

The single highest-value new content is **technique-selection criteria calibrated to
`Adv⊥`/`classDistance`, carrying each technique's admissibility preconditions** —
which neither repository has today, and which this matrix's T1–T4 rows are the raw
material for.


# RECOMMENDED LEG ORDER, PRICED

Sizing convention: **S** ≈ one focused session; **M** ≈ a few sessions or one
substantial file; **L** ≈ a multi-session leg with its own gates.  Every leg ends
with `lake run ledgerAudit` (four gates) plus the focused build of the modules it
touched; every new declaration under `RandomSystems/System/` must be classified in
`LEDGER.md` **in the same leg**.

### Phase 0 — free wins, no carrier decision required (delta `none`)

| leg | content | rows | size | why first |
|---|---|---|---|---|
| **P0.1** | **`condProb` toolkit**: the total conditional probability beside AC's `Part`-valued `cond`, the hypothesis-free multiplication rule, Bayes, total probability, and the two chain rules (incl. MPR07 eq. (1)) | T1.9, T2.4 | **M** | CLOSED (T0: chain rule Conditional.lean:386; eq.(3) min-form was already PRESENT — statDist_eq_one_sub_sum_min, StatisticalDistance.lean:251) |
| **P0.2** | **H-technique refinements**: the Chen–Steinberger partition *bound* and the general extension lemma | T4.7, T4.8 | **S** | CLOSED (T0 dbe169e: statDist_le_of_extension :1104; general form :1092) |
| **P0.3** | **counting kernel**: falling factorials, permutation-consistency mass, gate sums, the SoP fiber ratio | T4.10 | **M** | CLOSED (T0 ce0eb22: Probability/Counting.lean, 34 declarations; residue available cheaply: two-sided birthday, sorted-pair sums, function fibers, block-major encoding, re-randomisation fibers) |

Phase 0 is ≈ **S+M+M** and touches only `Probability/`, so it cannot conflict with
any carrier ruling and can start immediately.

### Phase 1 — the two rulings that gate everything else

These are **not** implementation legs.  They are the escalations this survey
raises, and both must be closed before T1/T3 code is written.

| # | question | evidence assembled here |
|---|---|---|
| **R-A** | **Game carrier**: `PDS X (Y × Bool)` with a separate `MonotoneMBO` predicate (quarry's choice, and what all the CE machinery needs), or the thesis Def 2.20 pair `(s, A)` with an *input-only* MC? | The quarry surveyed this and chose `Y × Bool`, documenting the bridge at `Q:GameWinnability.lean:16-40`.  Maurer13b Def 9 and CR18 Def 3.22 both *define* the game that way.  The thesis pair is recoverable as `gameOfDDS` at an input-only condition. |
| **R-B** | **Source hierarchy for CE**: no primary defines conditional equivalence (§C6).  Does CE enter the CR18-FALLBACK register, with Maurer13b named as the preferred citation? | §C6 + the source ledger.  Registry checked: neither the PRIMITIVE REGISTRY nor PHI-SPEC nor the CR18-FALLBACK register mentions CE, games, or MBOs. |
| *(secondary)* | **R-C**: is the MBO an `EventAlgebra` element (Jost, a primary) or a `Bool`-valued monotone predicate? | §T2, `AC:AbstractCryptography/EventAlgebra.lean` (775 lines) vs `Q:RandomSystemsCC/EventHistory.lean` (174 lines).  Note this one can be deferred without blocking: the `Bool` reading is a model of the event reading. |
| *(secondary)* | **R-D**: is CR18 Def 4.20's blocking converter `b` expressible with AC's landed `blockSet`/`block`/`attachAt`, and does pin 3 permit it in a technique statement? | The `b`-as-converter design note in §T1. |

### Phase 2 — the ordered legs

| # | leg | rows | size | depends on | payoff |
|---|---|---|---|---|---|
| **L-1** | **Game objects**: game carrier, `S⁻`, `MonotoneMBO`, game transcript/observable, game equivalence (the coarser quotient beside `Behaviour`), `ν`, `Winnable`, `ω` | T1.1, T1.2, T3.1–T3.4 | **M–L** | R-A | CLOSED (T2 9a5dccc: Winnable, infWinnability; R9-aligned) |
| **L-2** | **The Winnability Theorem** `ν = ω` + attainment, via the thesis p. 26 alternative proof reducing to Thm 2.31 | T3.5–T3.8 | **L** | L-1 | CLOSED (T2 e221d9e/65a87f2: winnability_theorem via the p.26 alternative proof; HasFixedDomain trap avoided — one PDG.HasDomain clause; all three reference strengthenings kept) |
| **L-3** | **CE definition + filtration algebra + seed kit + `gameEnhance`** | T1.3–T1.6 | **M–L** | L-1, R-B, P0.1 | populates `Technique/ConditionalEquivalence.lean` |
| **L-4** | **CE ⟹ indistinguishability**: `Adv⊥(S,T) ≤ Γ(Ŝ)` then the blind headline `Adv⊥(S,T) ≤ Γ(bŜ)` | T1.7, T1.8 | **L** | L-2, L-3, R-D | the payoff theorem; with R-D resolved it is stated **CR18 Def 4.20 verbatim** and ≈1400 lines of quarry blind-winner machinery are *not needed* |
| **L-5** | **H-technique system half**: `q`-indexed transcript prefix + query-vector-indexed law, then the σ·η factorization, then the adaptive endpoint on `Adv⊥` | T4.4–T4.6, T4.11 | **L** | P0.2, P0.3 (helpful, not blocking) | **runs in parallel with L-1…L-4 — no shared files beyond `Probability/`** |
| **L-6** | **MPR07 Lemma 5** (tight MBO existence), stated at the `Behaviour` quotient, with the maximal-coupling construction | T2.2, T2.3 | **M–L** | L-3, L-4 | completeness of the whole T1 method; the proof engine (`optimalJoint`, `isCoupling_optimalJoint`, `offDiagonalMass_optimalJoint`) is already landed in `AC:Coupling.lean:143,196,225` |
| **L-7** | filtered advantage + the pointless-query WLOG (carrying the quarry's "NOT WLOG when the worlds are not both permutations" caveat) | T4.12 | **L** | L-5 | needed before any concrete application |
| **L-8** | the events/MBO reconciliation (`EventAlgebra` instantiated on interaction histories) | T2.1 | **M** | R-C | source-hierarchy hygiene; optional if R-C defers |
| **L-9** | application kits (switching, SoP, hash-then-PRF, CBC-MAC, HCTR2) | T1.10, T4.13 | **L**× | L-4, L-5, L-7 | out of first scope |

### The two-lane picture

```
  lane A (games/CE):   P0.1 → [R-A,R-B] → L-1 → L-2 → L-3 → L-4 → L-6
  lane B (H-technique): P0.2, P0.3 ──────────────────→ L-5 → L-7
                                                          ↘ L-9 (both lanes)
```

They share only `Probability/` and can be run concurrently by two lanes without a
merge conflict, provided lane B does not touch `RandomSystems/System/` beyond the
new transcript-prefix module (which the ledger gate will force it to classify).

### Where the skills port fits

**`ac-lean-proofs` before Phase 0** (S) — it is 4 edits and every subsequent leg
benefits.  **`ac-cc-constructions`** whenever CC work resumes (M).
**`ac-random-systems-proofs` last, and incrementally**: its routing ladder is a map
of endpoints, and AC's technique endpoints do not exist yet — write one branch of the
ladder as each leg closes (L-2 → the winnability branch, L-4 → the CE branch, L-5 →
the H-technique branch).  Writing it up front would document a tree that isn't there.

### If only one leg can be funded

**L-2 (the Winnability Theorem).**  It is primary-sourced (Lanzenberger Thm 2.37,
a source in the hierarchy), its quarry proof is sorry-free and thesis-shaped, its
proof route consumes an AC theorem that is already landed, its `ω` already writes
R9's honesty clause, and it is the result that makes every `Γ` on the right-hand
side of a CE bound computable.  It is the highest ratio of theorem-weight to
carrier risk in the program.

# TECHNIQUE-PROGRAM PLAN (binding; PHI-SPEC R10 carries the design)

LEGS (each: comprehensive brief, code + proposed doc deltas, all four
gates, adversarial audit before deltas apply):
  T0 CLOSED (cee67d7/dbe169e/ce0eb22; 63 declarations, all axiom-clean; coinages condProb/condDist flagged in-code; Patarin/Chen-Steinberger/Jha-Nandi attributions remain UNVERIFIED as the quarry's own, flagged in-code, papers not on disk — citation upgrade owed). Was: conditional-probability toolkit, the two
     H-technique refinements, the counting kernel — carrier-delta-free
     rows of the matrix above.
  T1 games: Def 2.20-2.25 objects (pair primitive), the bit-output view +
     round trip, the `adjoin` constructor with its TWO OBLIGATIONS
     (monotone per atom; forgetting law against the class), blindness =
     blocking converter (Rem 2.23 via blockSet — the ~1400-line IsBlind
     machinery is NOT transplanted).
  T2 CLOSED (9a5dccc/e221d9e/65a87f2/a9d9546): route = the thesis p.26
     alternative proof (Thm 2.31 + one run-agreement induction); the plan's
     word 'architecture' for GameWinnability.lean:778 refers to that
     reduction, per its own header :58-77.
  T3 conditional equivalence: definition + the CE bound against Adv⊥.
     GATE RESOLVED 2026-08-18 (PHI-SPEC CE-sources line): no admission
     needed — charter sources + trap list govern.  Contract = R11(a)+(b):
     one new relation over the landed observables; the quarry's proven
     CondEquiv/Theorem417 lemma DAG transported along the CE dictionary
     (RECAST POLICY, CE rows).  DISPATCHABLE.
  T4 MPR07 Lemma 5 as constructor completeness (on the Behaviour
     quotient; MaPiRe07.pdf p. 140, visual).
  T5 H layer-3: the η·σ factorization + the environment-uniform
     corollary; then the counting layer for applications.
  T6 (Marc 2026-08-18: integrate even without consumers): the reference
     repository's remaining probability material — the information-theory
     layer (Divergence.lean, DistExpect.lean: divergences, entropy,
     expectation extras) and the counting residue listed at the T4.10
     closure — through the established toPMF bridge on the honest
     subcarrier; statements restated on Distribution.
  SKILL (SEQUENCED LAST — after T1-T5 land, so it cites real endpoint
     names; Marc 2026-08-18: premature before the techniques exist): the
     abstract-crypto proving skill — METHOD from random-systems-proofs
     (seven stages + routing), contents re-targeted, plus per-technique
     ADMISSIBILITY CONDITIONS.  Drafted by an agent, applied by the
     coordinator, only once the technique layer is in the tree.

R10 REFINEMENT (Marc 2026-08-18, second ruling supersedes the first): the
monotone-condition CARRIER is the upper-set form (UpperSet of the prefix
order) — chosen for long-term algebra: the complete lattice (joins of bad
events), comap along the tree's prefix-monotone maps (historyAt/keptPrefix
— condition transport across par/attachment/blocking), the firing
frontier.  FAITHFULNESS CERTIFIED: the definition carries an adjacent
proven equivalence to the thesis's literal form
{A : List X → Bool // Monotone A} (Def 2.20 quoted in the docstring), and
the Bool-predicate view is the derived presentation with a round trip.  The GAME is the linking: the pair carrier, with
"conditions on S" = the fiber of the forgetful projection over S's
behaviour (membership = the forgetting law), and adjoin = the fiber's
constructor.  Obligation 1 lives in the MC subtype, obligation 2 in the
fiber membership — no ad-hoc structure fields.

CR18 RECAST POLICY (Marc, 2026-08-18; GENERALIZED 2026-08-18 = PHI-SPEC
R11): ALL CR18/Maurer-school material — multigames, game reductions,
conditional equivalence, everything after — is the CONCEPT recast ON TOP
of the landed infrastructure, never a parallel lane and never a parallel
modeling.  We already have PDS, games (`PDG` pairs), conditions
(`MonotoneCondition`), transcript observables (`gameTrLaw`,
`trLawFullyDefined`), conditioning (T0 `Probability/Conditional.lean`):
a source concept enters as definitions/theorems OVER these, and a concept
that seems to need a new object stack is a fork to Marc, not a build.
The dictionary: multigame = system + FAMILY of conditions (the
lattice gives or/and/frontier games); same-system reduction = the
upper-set order; cross-system reduction = converter + comap + absorption;
S⁻ (Def 4.18) = forget; game equivalence (§4.10.1) = equivalent on the
bit view; k-bit presentation = derived view at a product of bits.  CE rows
(T3, thought through 2026-08-18): conditional law `p_{Yⁱ|Xⁱ, A=0}` = the
not-won slice of `gameTrLaw (playQueries l)` with conditioning from T0's
`condDist`/cross-multiplied lemma (never re-rolled); CE `Ŝ ⊨ T` = ONE new
Prop, division-free (slice `= (1 − winningMass) • trLawFullyDefined`),
quantified over query lists = Maurer13b Def 13's fixed-`Xⁱ`; `ν` =
`supWinProb`, stated once — NO `Γ`/`Γᵇ`, no blinded-system objects, no
`S⁻`/`S⊣` operators (the T2 `⊥`-twin at `toBitLaw` is the only twin);
endpoint `CondEquiv G T → Adv⊥(forget G, T) ≤ ofReal (supWinProb G)` with
the coupling core generalizing T2's `statDist_fTransform_le_mass_of_eq_off`
route via T0's chain rules; everything on the `Adv⊥` ⊥-total carrier (F-2
— CR18 §4.10's no-refusal simplification is rejected).  R11(b) minimal
migration: the quarry's PROVEN `CondEquiv.lean`/`Theorem417.lean` lemma
DAG is the route — transport it along this dictionary, re-elaborating
each node on our observables; change only what the recast forces; do NOT
invent a fresh proof route, and do NOT transcribe text across carriers.
All of it enters under the R8 fallback register, flagged.

DRIFT TRIPWIRES for every T-brief: the R10 vocabulary rules (LEDGER +
PHI-SPEC); games are PAIRS (bit view derived); conditions are per-atom
input predicates (internal randomness via the joint distribution);
environments never observe the condition; no "blinder" objects; the
forgetting law is stated against equivalence classes; H-layer-3 is the
only H build item (layers 1-2 exist — do not re-prove); R11 concept
recast — no parallel object stacks, CE/any-new-concept consumes the
landed observables + T0 conditioning, a seemingly-needed new object is a
fork to Marc not a build; R11(b) minimal migration — where a proven
development exists (source theory or reference repo), adapt its lemma
DAG along the recast dictionary with the minimal forced delta, never
reinvent the route, never transcribe across carriers.

# CR18 full-sweep register — stretch goals for abstract-crypto

**Source**: `/Users/marcilunga/Documents/tob/research/random-systems/papers/CR18_LN.pdf`
(Cachin–Renner–(Maurer) lecture notes; 85 PDF pages, 2-up: PDF page *N* holds
printed *2N−13* / *2N−12*; printed *P* → PDF ⌊(P+13)/2⌋).

**Read discipline**: visual only, ≤6 PDF pages per chunk, chapter by chapter.
**Both repos READ-ONLY.**

**Classification**
- `COVERED` — exists in abstract-crypto, or sits on an existing plan line (named).
- `RECAST-PLANNED` — inside the LEDGER CR18 RECAST POLICY dictionary or a T-leg (T0–T6).
- `STRETCH` — not planned anywhere. Each carries: chapter/printed page · one-line
  content · nearest primary source (MauRen16 / Jost / LiuMau20 / Lanzenberger) with
  the recast route, or `CR18-ONLY` · size guess S/M/L.

---

## Reading log

(filled per chunk)

---

## Register

(filled per chunk)

### Chunk A — PDF 1–6 (front matter, full TOC, preface)

Identified: **Ueli Maurer, "Cryptography Foundations", ETH Zürich, Spring 2018.**
(Single author — the repo shorthand "CR18" is retained here for continuity.)

Full chapter map (printed pages → PDF page = ⌊(P+13)/2⌋):

| ch | title | printed | PDF |
|---|---|---|---|
| 1 | Introduction | 1–11 | 7–12 |
| 2 | Some Cryptographic Schemes, Protocols, and Security Definitions | 12–54 | 12–33 |
| 3 | Discrete Systems | 55–71 | 34–42 |
| 4 | Computational Problems and Reductions | 72–111 | 42–62 |
| 5 | Constructive Cryptography | 112–122 | 62–67 |
| 6 | Randomness Expansion | 123–131 | 68–72 |
| 7 | Constructing Shared Secret Keys | 132–142 | 72–77 |
| A | Appendix (probability / information theory / number theory) | A1–A13 | 78–85 |

Section skeleton worth flagging up front (detail verified chunk by chunk below):
- **3.1–3.7** reactive systems, DDS, parallel composition, interfaces/resources,
  environments+transcripts, converters (filters, cascading, output-combining,
  interface connection), probabilistic systems, behavior (channels-in-IT view,
  equivalence, cumulative description, transcript-distribution computation),
  **3.7 discrete computational problems (discrete games, discrete distinguishers)**.
- **4.1–4.11** decision/search problems, beyond-worst-case, two worked
  number-theoretic examples, **4.4 abstract computational problems, solvers,
  performance, the reduction concept, composition of reductions, generalized
  reductions, worst-case problems**, 4.5 games/multi-games/distinction/bit-guessing,
  4.6 discrete computational problems, **4.7 basic reduction types**,
  **4.8 reduction statements for games (repetition amplification, cloning, random
  self-reduction)**, **4.9 hardness amplification for games**, 4.10 relating games
  and distinction problems, 4.11 proving indistinguishability (CE, switching lemma).
- **5.1–5.5** construction paradigm, resource specifications/constructions/
  relaxations, **5.3.4–5.3.9 ε-relaxation, reduction-based relaxations,
  ∗-relaxations, a new look at the simulation paradigm, game-relaxation,
  substitution relaxation**, 5.4 authentication amplification,
  **5.5 parameterized resources and constructions**.
- **6.1–6.2** randomness expansion; k-wise independence; URF domain extension
  (VIL-URF, CBC-MAC as randomness expander, collision-game compression function,
  CRHF, δ-AUH).
- **7.1–7.3** key agreement; IT key agreement (impossibility, possibility, privacy
  amplification); ROM key agreement; impossibility of implementing a random oracle.

### Chunk B — PDF 7–24 (Ch. 1 complete; Ch. 2 printed 12–36)

**Ch. 1 (printed 1–11)** — pure prose: mission of crypto, paradoxes, terminology
(scheme/protocol; correctness/security/practicality), attack-based vs ideal-world
definitions, adversary as a hypothetical entity, IT vs computational security,
modularity/composability, role of assumptions, §1.5 informal hardness implications
and the reduction idea (formalized in Ch. 4), §1.6 research categories.
**No formal content. Nothing registrable.**  (§1.3.3 "function vs algorithm" is the
paper's stated reason for *not* carrying an efficiency predicate — relevant to the
complexity question below, as the paper's own position.)

**Ch. 2, printed 12–36** — classical schemes as motivation:
Def 2.1 symmetric cryptosystem; §2.2.2 IND-CPA game (Def 2.2); OTP (Prop 2.1 perfect
secrecy); §2.2.5 the two "security problems" of OTP; §2.2.6 additive stream cipher;
Def 2.3 PRG (informal); Def 2.4 block cipher; PRF via a distinction problem;
§2.3 **three problem types**: Def 2.5 game winning probability `Γ^W(G) := Pr^{WG}(A=1)`,
Def 2.6 **signed** distinguishing advantage `Δ^D(S,T) := Pr^{DT}(Z=1) − Pr^{DS}(Z=1)`,
Def 2.7 `Δ^𝒟` = sup over a distinguisher class, `Δ` = sup over all,
Def 2.8 statistical distance, Lemma 2.1 (best distinguisher = statistical distance),
Lemma 2.2 (hybrid/telescoping), Def 2.9 **bit-guessing advantage**
`Λ^D((S,B)) := 2(Pr(Z=B) − ½)`, Lemma 2.3 `Λ^D((S_U,U)) = Δ^D(S_0,S_1)`,
Lemma 2.4 `Δ^D((S,B),(S,U)) = ½Λ^{D'}((S,B))`;
§2.4 CC first example (real/ideal, converters, simulator, eq. (2.2)
`otp-dec^B otp-enc^A [KEY,AUT] ≡ sim^E SEC`, computational variant `≈`, composability);
§2.5 MACs (Def 2.10, Def 2.11 forgery game, CBC-MAC, Encrypt-then-MAC);
§2.6 Diffie–Hellman.

Classification for this chunk:
- Def 2.5 / 2.6 / 2.7 / 2.8, Lemmas 2.1, 2.2 — **COVERED** (metric layer:
  `PDS.advFullyDefined`, `edist`, statDist family; Def 2.7's class-indexed sup is the
  fenced `Metric/Distinguisher.lean` `edistD` — LEDGER gap G10, already a known gap).
- Def 2.2 IND-CPA / Def 2.11 MAC game / Def 2.3 PRG / Def 2.4 block cipher /
  §2.5.3 CBC-MAC — **out of scope** (LEDGER "APPLICATION rows" discipline).
- §2.4 (real/ideal, converter, simulator, composability) — **COVERED** (MR16 rows 1,
  33, 39–43).
- **Def 2.9 + Lemmas 2.3/2.4: bit-guessing problems as a first-class problem type,
  and the two-way dictionary to distinction problems.** → see STRETCH S-01.

### Chunk C — PDF 25–36 (Ch. 2 printed 37–54; Ch. 3 printed 55–60)

**Ch. 2 tail (printed 37–54)** — DH key agreement, §2.6.4 extractors (informal),
Def 2.12/2.13/2.14 DL / CDH / DDH (explicitly typed: "the first two are *games*, the
last is a *distinction problem*"), PKE (Def 2.15), Def 2.16/2.17 IND-CCA/IND-CPA games,
TOWP (Def 2.18, Def 2.19 inversion game), RSA (Thm 2.5, Def 2.20), digital signatures
(Def 2.21, Def 2.22 forgery game), hash functions (Def 2.23), Def 2.24 collision-finding
game, Def 2.25 collision resistance of a *family*, §2.8.5 hash-then-sign, §2.9 the
protocol wrap-up. **All APPLICATION / out of scope** by the LEDGER discipline. The one
transferable remark: §2.8.4's insistence that a fixed instance cannot be hard — only a
problem with a large instance set — which is the paper's motivation for the §4.4
performance/solver apparatus (see S-04).

**Ch. 3 opening (printed 55–60)** — verified against the tree:
- §3.1.1 reactive `(𝒳,𝒴)`-system; Ex 3.1 function system; **Def 3.1 `𝒴`-source**
  (unary/trigger input alphabet; memoryless or with memory; Ex 3.2 beacon `B_n`,
  Ex 3.3 `U_n` one-shot); Ex 3.4 the three descriptions of a URF (on-the-fly vs
  once-and-for-all function table) — §3.1.2 **descriptions vs mathematical types**
  (prose, but it is the paper's stated reason for the behavior layer of §3.6).
- **Def 3.2** DDS = partial `s : 𝒳*\{ε} → 𝒴` with prefix-closed domain; "finite"
  = `dom(s) ⊆ 𝒳^n` — **COVERED** (`System/DiscreteSystem.lean`; R1).
- **Def 3.3** `s⊥` completion with deletion of the undefined queries — **COVERED**
  (CR18-FALLBACK register line 1; `fullyDefined`/`keptPrefix`).
- **Def 3.4** parallel composition `[s₁,…,sₙ]`, with `[s₁,…,sₙ]⊥ = [s₁⊥,…,sₙ⊥]` —
  **COVERED** (`System.parallel`, `parallel_fullyDefined`).
- §3.2.3 interfaces as a partition of `𝒳`; **Def 3.5** deterministic resource with
  interface set `𝓘` as an `(𝓘×𝒳, 𝒴)`-DDS — **COVERED** (R3 exogenous addressing;
  RS-A `Φ := PDS (P × X) Y`).
- **Def 3.6** DDE `e : (𝒴∪{⊥})* → 𝒳∪{⊣}` with an explicit **stop symbol `⊣`**;
  **Def 3.7** transcript `tr(s,e)` — **COVERED** (`DDE.Total`, `Environment.lean`).

### Chunk D — PDF 37–42 (Ch. 3 printed 61–71; Ch. 4 opens printed 72)

Ch. 3 core, item by item:
- **Def 3.8** DDC with the finite bound on consecutive `(in,x)` outputs — **COVERED**
  (`Converter.AnswersWithinBudget`; CR18-FALLBACK register line 2).
- **Def 3.9** converter application `αs` (paper itself declines to prove `αs` is a
  `(𝒰,𝒱)`-DDS: *"we do not give a completely formal definition"*) — **COVERED**
  (`DDC.apply`/`connectFully`; MR16 §3.3 is the authority).
- **§3.4.3 filters** `φ` with `dom(φs) ⊆ dom(s)`, `(φs)(x^k) = s(x^k)`; **Def 3.10**
  the query filter `[q]` — **COVERED-PENDING** (LEDGER RECEIPT row
  `filterDom, filterQueries | PENDING (CR18 Def 3.10 filters; O8/Budget) | A8`).
- **Def 3.11 cascade `s ▷ t`** of an `(𝒳,𝒴)`-DDS with a `(𝒴,𝒵)`-DDS, plus the
  converter form `casc[s,t] = s ▷ t` on parallel access → **STRETCH S-02**.
- **Def 3.12 output combination `s ⋆ t`** for an operation `⋆` on `𝒴`, plus its
  converter form `comb^⋆[s,t]` → **STRETCH S-03**.
- **Def 3.13** `α^i s` (converter at interface `i`) — **COVERED** (`attachAt i E`, R7″).
- **Lemma 3.1** `α^i β^j s = β^j α^i s` for `i ≠ j` — **COVERED** (MR16 row 22:
  `attachAt_comm`, `pairwiseOrderInvariant_attachAt`).
- **Def 3.14** PDS = random variable over DDS — **COVERED**.
- **Def 3.15** `(𝒳,𝒴)`-random function / `𝒳`-random permutation as a random variable
  over *functions*; Ex 3.5 URF `R_{m,n}` / URP `P_m` → see STRETCH S-05 (the
  function-valued-random-variable presentation and URF/URP as named objects).
- **Def 3.16** PDE, `tr(S,E)` as a random variable — **COVERED**.
- **Def 3.17 probabilistic discrete converter (PDC)** = random variable over DDC,
  composition `(α,s) ↦ αs` lifted → **STRETCH S-06**.
- **§3.6.1 channels**: `p^C_{Y|X}`, behavior of a channel, `C₁ ≡ C₂`, channel cascade
  `p^{C▷D}_{Z|X} = Σ_y p^C_{Y|X} p^D_{Z|Y}` — the equivalence-class reading of a
  conditional distribution is **COVERED** in spirit (`Behaviour.lean` quotient); the
  channel layer itself is part of S-02/S-07.
- **Def 3.18 behavior** `b(S) = (p^S_{Y_i|X^i Y^{i-1}})_{i≥1}`; **Def 3.19** `S ≡ T`
  iff `b(S) = b(T)` — **COVERED** (`equivalent`, `Behaviour.lean`).
- **Ex 3.7 VIL-URF `V_n`**: a *behavior with no underlying PDS* (uncountable sample
  space) — the paper explicitly allows behaviors that no PDS realizes → **FLAG F-1**
  (see Contradictions).
- **§3.6.4 Def 3.20 cumulative description** `p^S_{Y^i|X^i}`, eq. (3.2) the product
  form, the inverse (division) formula, and *"the behavior of a system answering at
  most `q` queries is completely specified by `p^S_{Y^q|X^q}`"* —
  **RECAST-PLANNED** (T4.4 fixed-query transcript carrier, T5).
- **§3.6.5 Def 3.21** behavior of an environment; **Lemma 3.2**
  `p^{ES}_{X^k Y^k} = ∏_i (p^E_{X_i|X^{i-1}Y^{i-1}} · p^S_{Y_i|X^i Y^{i-1}})
   = p^E_{X^k|Y^{k-1}} · p^S_{Y^k|X^k}` — **RECAST-PLANNED** (this is exactly the
  η·σ factorization; PHI-SPEC R10 H-layer-3 / LEDGER T4.5 / T5).
- **eq. (3.3) + its negation**: `p^{ES}_{Y_i|X^i Y^{i-1}} = p^S_{Y_i|X^i Y^{i-1}}`
  holds, but `p^{ES}_{Y^i|X^i} ≠ p^S_{Y^i|X^i}` in general → **TRAP T-1** worth pinning
  in the T5 brief (the environment's presence changes the *cumulative* law even though
  it does not change the one-step law).
- **§3.7.1 Def 3.22** MBO / DDG; **Def 3.23** winner = DDE; `tr(g,w)` carries `a_i`;
  the notes flag **multi-games** (several MBOs; hiding the bits then matters) —
  **RECAST-PLANNED** (CR18 RECAST POLICY: multigame = system + FAMILY of conditions).
- **§3.7.2 Def 3.24 discrete distinguisher (DDD)** = an environment with **two stop
  symbols `⊣₀`, `⊣₁`**, output = index of the stop symbol, `0` if it never stops →
  **STRETCH S-08** (the output-by-stop-symbol convention; AC's environments carry one
  stop and read the verdict elsewhere).

### Chunk E — PDF 43–54 (Ch. 4 printed 73–96)

**§4.1–4.3 (printed 73–84)** — problem taxonomy and two worked number-theoretic
reductions:
- **Def 4.1 search problem** = 4-tuple `(𝒳, 𝒲, Q, P_X)` — instance set, witness set,
  predicate, **instance distribution** → part of STRETCH S-04.
- §4.1.3 worst-case vs average-case, "almost-everywhere hardness"; §4.1.4 the three
  crypto problem types (game / distinction / bit-guessing).
- §4.2 Thm 4.1 + Lemma 4.2 (RSA LSB), §4.3 the DL-LSB reduction chain (Thm 4.3,
  Cor 4.4, ideas 1–5: instance shifting, worst→average, initial segment, **performance
  amplification by majority vote**, instance-distribution change; Ex 4.4 "changing the
  instance distribution by `d` in statistical distance changes performance by ≤ `2d`",
  Ex 4.5). **Application/pedagogy**, but they are the paper's motivation for §4.4.

**§4.4 Abstract Computational Problems and Reductions (printed 84–89)** — the paper's
own abstract theory of problems and reductions. **None of this is in abstract-crypto
and none of it is in the RECAST dictionary or the T-legs.** → STRETCH S-04 (with
sub-items):
- **Def 4.2 problem** `p = (Σ_p solvers, (Ω_p,≤) performance poset, p̄ : Σ_p → Ω_p)`;
  `a`-solver. Performance sets are `[0,1]` for games, `[−1,1]` for distinction problems.
- §4.4.4 upper bounds `p̄ ≤ ε` as the shape of an information-theoretic statement.
- **§4.4.5 Def 4.3 the reduction**: reduction function `ρ : Σ_p → Σ_q`, performance
  translation `τ : Ω_p → Ω_q` (≤-respecting), **eq. (4.1) `τ p̄ ≤ q̄ ρ`**; `ρ` is a
  `τ`-reduction of `q` to `p`.
- §4.4.6 the two quality axes (complexity blow-up of `ρ`, performance loss of `τ`);
  the dual form via `λ` with `id ≤ λτ` (eq. 4.2) giving **eq. (4.3) `p̄ ≤ λ q̄ ρ`**.
- **§4.4.7 complexity-theoretic interpretation** — the *only* complexity layer in the
  notes: `Σ_c := {s | γ(s) ≤ c}`, derived problem `p̄'(c) = sup{p̄(s) : s ∈ Σ_c}`,
  derived reduction `ρ'(c) = sup{γ(ρ(s)) : s ∈ Σ_c}`; the paper deliberately stops
  short of a computational model. → STRETCH S-09.
- **§4.4.8 Lemma 4.5 / Lemma 4.6 — composition of reductions** (both forms).
- **§4.4.9 generalized reductions** — a reduction from a *list* of problems:
  eq. (4.4) `τ(p̄₁(s₁),…,p̄ₙ(sₙ)) ≤ q̄ ρ(s₁,…,sₙ)`, eq. (4.5) `p̄ ≤ λ q̄ ρ` with
  `λ` typically `sum`.
- **§4.4.10 Def 4.4 worst-case problem** `𝒫̄(s) := inf_{p∈𝒫} p̄(s)`.

**§4.5 Basic types as instantiations (printed 90–92)**:
- **Def 4.5 game** = `(𝒢, 𝒲, ω : 𝒲×𝒢 → {0,1})`, `Ḡ(W) := Pr^{WG}(ω(W,G)=1)`,
  `Ω = [0,1]` — **RECAST-PLANNED** (T1/T2 game layer), but note the paper's abstract
  form takes `𝒢`, `𝒲` as *arbitrary sets*, not discrete systems (§4.6 does the
  discrete instantiation separately).
- **Multi-games** `ω₁,…,ω_k`; **Def 4.6 `g^∨` / `g^∧`**; Ex 4.10 hash-then-sign as a
  3-condition multi-game with `ω₃ → (ω₁ ∨ ω₂)` ⟹ `Ḡ₃ ≤ Ḡ₁ + Ḡ₂` —
  **RECAST-PLANNED** (dictionary: multigame = system + FAMILY of conditions; the
  lattice gives or/and/frontier games).
- **Def 4.7 distinction problem** `⟨S₀|S₁⟩` with performance `Δ^D` (signed), Def 2.7
  class advantage, `Δ^𝒟 = sup_{D∈𝒟} |Δ^D|` when `𝒟` is closed under complementing the
  output bit; **Lemma 4.7: closure under output-complementation ⟹ `Δ^{𝒟'}` is a
  pseudo-metric**; eq. (4.6) the hybrid lemma restated as
  `⟨S₀|S_k⟩ ≤ sum(⟨S₀|S₁⟩,…,⟨S_{k−1}|S_k⟩)` — the metric is **COVERED**
  (`PseudoEMetricSpace Phi`), but *Lemma 4.7 as a criterion on a distinguisher class*
  is not (→ S-10).
- **Def 4.8 bit-guessing problem** `[S;B]` with performance `Λ^D`; eq. (4.7)
  `[S_U;U] = ⟨S₀|S₁⟩`; eq. (4.8) `(S,B) = 2·⟨(S,B)|(S,U)⟩ρ` → STRETCH S-01.

**§4.7 Basic reduction types (printed 93–94)** → STRETCH S-11:
- **Def 4.9** `X^q` = `q` **independent** copies, `⟨X⟩` = countably many independent
  copies; **Def 4.10** `X^{[q]}` = `q` **clones** (`X₁ = … = X_q`). Applied to systems,
  environments and converters: `S^q`, `S^{[q]}`, `C^q S^q = (CS)^q`, `E^q`.
- §4.7.2 **reduction by a converter**: `ω(wc, g) = ω(w, cg)` (eq. 4.9),
  `ρ^C : W ↦ WC`, **eq. (4.10) `CG = Ḡ ρ^C`** (converter application on a game *is* a
  reduction function) — partially in the RECAST dictionary (cross-system reduction),
  but the *equation between a composed game and a composed performance function* is not.
- §4.7.3 **reduction by multiple instantiation** `σ^q : W ↦ W^q`.

**§4.8 Reduction statements for games (printed 94–97)** → STRETCH S-12:
- **Def 4.11** `ψ_q(x) := 1−(1−x)^q`, `χ_q := ψ_q^{-1}`, eq. (4.11)
  `χ_q(x) ≤ −ln(1−x)/q`; **Lemma 4.8 `ψ_q Ḡ ≤ Ḡ^{q∨} σ^q`** — performance
  amplification for games by repetition.
- **Def 4.12 `q`-clonability by a converter `K`**: `KG ≡ G^{[q]∨}`; eq. (4.14)
  `Ḡ^{[q]∨} = Ḡ ρ^K`.
- **Def 4.13 random self-reducibility by a converter `R`**: `∀g ∈ 𝒢, Rg ≡ G`
  (a fixed instance is converted into a *random* one).
- §4.8.4 combining clonability and random self-reduction (worst-case ← average-case).

### Chunk F — PDF 55–60 (Ch. 4 printed 97–108)

- **§4.8.3–4.8.4** Lemma 4.9 (`Ḡ = 𝒢̄ ρ^R` for random self-reducible `G`, turning a
  worst-case performance into an average-case one), **Theorem 4.10**
  (`ψ_q Ḡ = Ḡ ρ^K σ^q ρ^R` — random self-reducibility + clonability ⟹ strong
  amplification), Ex 4.12 (DL is random self-reducible), Ex 4.7 (CDH) → STRETCH S-12.
- **§4.9 Hardness Amplification for Games (printed 98–104)** → **STRETCH S-13**:
  §4.9.1 `[G₁,…,G_k]^∧`; §4.9.2 the goal
  `hard(G,β) ∧ hard(H,γ) ⟹ hard([G,H]^∧, βγ)` stated *constructively*;
  **§4.9.3 Lemma 4.11** (a general lemma on `μ : 𝒮×𝒯 → [0,1]`:
  `E_ST[μ] ≤ Pr^S(μ₁(S)≥ε)·Pr^T(μ₂(T)≥ε′) + ε + ε′`) and its `k`-ary
  **Lemma 4.13**; **§4.9.4 Def 4.14** the emulating converters `H̲`, `G̲` and
  **Theorem 4.12** (`G`,`H` clonable ⟹ generalized reduction
  `[G,H]^∧ ≤ λ(Ḡ,H̄)[ρ₁,ρ₂]`, `λ(x,y) = (1+δ)xy + δ′`, with the explicit
  `q ≈ 2ln(2/δ)/δ′` calibration); **§4.9.5 Theorem 4.14**
  `Ḡ^{k∧} ≤ λ Ḡ ρ`, `λ(x) = (1+δ)x^k + δ′`, implying
  `hard(G,β) ⟹ hard(G^{k∧}, β^k)`.  (Provenance: the notes cite Maurer–Pietrzak–Renner,
  *Indistinguishability amplification*, CRYPTO 2007.)
- **§4.10 (printed 104–108)** — the standing `q`-query/dummy-padding simplification
  (already pinned in the LEDGER SOURCE LEDGER); **Def 4.15 pre-winning behavior**,
  **Def 4.16 `G ≡ᵍ H`**, **Lemma 4.15** (`G ≡ᵍ H ⟹ Ḡ = H̄`), **Def 4.17
  `Γ(G) := sup_W Ḡ(W)`**, **Def 4.18 `S⁻`**, **Lemma 4.16 `⟨S⁻|T⁻⟩ ≤ S̄`** —
  all **RECAST-PLANNED** (T1/T2; LEDGER T1.2, T3.x, and the RECAST dictionary line
  "`S⁻` (Def 4.18) = forget; game equivalence (§4.10.1) = equivalent on the bit view").
- **§4.10.2 eq. for `p^{DS}_{X^q Y^q Z}` = `p^D_{X^q|Y^{q−1}} · p^S_{Y^q|X^q} ·
  p^D_{Z|X^q Y^q}`** — the **three-factor** decomposition (η · σ · *verdict*), a
  refinement of Lemma 3.2 that T5's brief should carry: the distinguisher's output bit
  is a third factor, not part of `η`.  → **TRAP T-2** (T5 scope note, not a stretch item).
- **§4.11.1 Def 4.19 conditional equivalence `S ⊫ T`** + eq. (4.38) — **RECAST-PLANNED**
  (T3, gated on the pending Maurer02/Maurer13b source admission).

### Chunk G — PDF 61–66 (Ch. 4 printed 109–111; Ch. 5 printed 112–120)

Ch. 4 close:
- **Def 4.20 `bS`** (blocking converter: transparent for queries `X_i`, blocks replies
  `Y_i`) and `Γ(bS)` = the non-adaptive winning probability; **Def 4.21 `T̃`**
  (copies queries to a second system, ignores its replies); **Theorem 4.17**
  `⟨S|T⟩ ≤ b̄Ŝ ∘ ρ^T̃`, in particular `Δ(S,T) ≤ Γ(bŜ)`, with the (4.39)/(4.40)
  enhancement proof — **RECAST-PLANNED** (T1/T3; already pinned verbatim in the
  LEDGER SOURCE LEDGER).
- **§4.11.3 the switching lemma**: Def 4.22 `p_coll(t,q)`, Lemma 4.18
  `p_coll(t,q) ≤ ½q²/t`, **Lemma 4.19 `Δ([q]R_{n,n}, [q]P_n) ≤ ½q²2^{−n}`**, proved via
  Ex 4.15's distinctness MBO. Application-genre; the *technique* is planned (T1/T3),
  the URP/URF instance is an application. Note the statement is phrased with the
  **`[q]` filter**, i.e. it consumes Def 3.10 (LEDGER A8 PENDING row).

**Ch. 5, printed 112–120**:
- §5.1.1 modular construction / step-wise refinement (prose).
- **Def 5.1 construction** = a *relation* `⊆ Ω × Γ × Ω`; **Def 5.2 composable**
  construction (eq. 5.1) — **COVERED** (`Constructs`, `IsSeriallyComposable`, and the
  paper's point that composability is a property to be *proved*, which is exactly the
  AC class-based treatment).  eq. (5.2) `∘_i` (plugging a constructor into the `i`-th
  argument) and **eq. (5.3) `⋀_i (R_i →^{a_i} S_i) ⟹ [R₁,…,R_k] →^{[a₁,…,a_k]}
  [S₁,…,S_k]`** — the paper explicitly *declines to discuss* these; AC has the
  one-slot form (row 6, `constructs_parF_left`) but not the simultaneous `k`-ary form
  → minor, folded into S-14.
- **Def 5.3 resource specification**, "at least as specific as", abstraction —
  **COVERED** (row 7).
- **Def 5.4 `𝓡 →^γ 𝓢 :⟺ γ(𝓡) ⊆ 𝓢`**, **Lemma 5.1** composability — **COVERED**
  (rows 33, 34).
- **Def 5.5 relaxation** `ρ : 𝒫(Φ) → 𝒫(Φ)` with `𝓡 ⊆ ρ(𝓡)`, pointwise-induced form,
  ε-relaxation — **COVERED** (`Relaxation` with its `le_toFun` field; rows 8, 9).
- **Def 5.6 compatibility of a relaxation with a construction set** + non-expanding
  `γ` + "all `γ` non-expanding ⟹ ε-relaxation is compatible" — **COVERED**
  (rows 35, 36; `IsNonexpandingSMul`, `epsilonRelaxation_compatible`).
- **Def 5.7 compatibility of a relaxation with parallel composition**
  `[R₁,…,ρ(R_i),…,R_n] ⊆ ρ([R₁,…,R_n])`, and eq. (5.4) "pulling relaxations to the
  outside" → **STRETCH S-14**.
- **§5.3.1 three interface types: party / adversary / FREE** (the free interface models
  the *environment's* access, e.g. the forwarding trigger of an authenticated channel)
  → **STRETCH S-15**.
- **Def 5.8 protocol** `π = (π₁,…,π_n)`, construction function
  `𝓡 ↦ π₁^{P₁}⋯π_n^{P_n}𝓡` — **COVERED** (rows 62, 63; `patternAttach`).
- **§5.3.3 resources vs converters** — three choices for the converter class
  (all systems / **trivial, connect-only** / efficiently implementable); the notes
  adopt the *trivial-converter* stance and reify a converter as a parallel resource:
  **`αR = π[R, α̃]`** → **STRETCH S-16** (nearest planned neighbour: MR16 row 32
  "Σ as a parameter, models 1–4", status `PARTIAL`, gap G9).
- §5.3.4 ε-relaxation `𝓡^ε` — **COVERED**.
- **§5.3.5 reduction-based relaxations**: `f = λ(p̄₁,…,p̄ₙ)[ρ₁,…,ρₙ]` a performance
  function, **eq. (5.5) `𝓡^f := {R′ | ∃R ∈ 𝓡 : ⟨R|R′⟩ ≤ f}`** — computational
  closeness as a relaxation indexed by a *reduction*, plus the remark that
  compatibility for this type is "a bit subtle" and is **not discussed** →
  **STRETCH S-18** (recast route: `Metric/ReductionRelaxation.lean` = Jost Def 2.2.9 /
  JM20 Def 3 exists but is **behind the MR11 PROVENANCE FENCE**, so it is planned-but-
  blocked, not available).
- **§5.3.6 Def 5.9 ∗-relaxation** `𝓡^{*E} := {α^E R | α ∈ Σ, R ∈ 𝓡}` — **COVERED**
  (rows 25, 26; `Relaxation.star`).
- **§5.3.7 a new look at the simulation paradigm**: `U ≡ σ^E V ⟹ ∀α ∃β : α^E U =
  β^E V` (`β = ασ`), and `U ≡ σ^E V ⟹ U* ⊆ [V, σ̃_E]*` — **COVERED** (MR16 rows 39–43
  and especially **row 45** `constructs_star_par_of_smul_eq`, which is this
  reification).
- **§5.3.8 Def 5.10 game-relaxation `T̂^⊥`**: the set of PDS that behave as `T` while
  the MBO is 0 and **arbitrarily** once it is 1 → **STRETCH S-17** (a
  relaxation *built from a game* — this is the game layer meeting the specification
  layer, and it is NOT in the CR18 RECAST dictionary).

### Chunk H — PDF 67–72 (Ch. 5 printed 121–122; Ch. 6 printed 123–131; Ch. 7 opens 132)

Ch. 5 close:
- **Lemma 5.2** (`S ≡ᵍ T̂ ⟹ S ⊆ T̂^⊥`) and **Lemma 5.3** (`Ŝ ⊫ T ⟹ S ⊆ T̂^⊥`) —
  the bridges from game equivalence / conditional equivalence into the game-relaxation;
  both stated **without proof**; plus the claim that game-relaxation is compatible per
  Defs 5.6 and 5.7 → part of **STRETCH S-17**.
- **§5.3.9 substitution relaxation** — named and then *explicitly not discussed*
  ("Substitution relaxations will not be discussed in this course"). A name with no
  content in this source → **NOT registrable from CR18** (noted so no future brief
  chases it here).
- **§5.4 Theorem 5.4 (authentication amplification)**:
  `hsh[AUT_k, INS_n, H_A, H_B] chk ⊆ [AUT_n, γ_coll H_E]^{*⊥}` — a construction
  statement whose ideal specification is a **∗- and game-relaxed** resource carrying a
  **collision game at the adversary interface**, deliberately avoiding both asymptotics
  and a collision-resistance assumption. Application-genre, but it is the *worked
  example* of S-17 and is the paper's answer to "how to state hash-based security
  without asymptotic families".
- **§5.5 Def 5.11 parameterized resources and constructions**: a family
  `{φ_r R}_{r∈𝒵}` of finite resources cut out of a (generally infinite) `R` by a family
  of **filter converters**; Ex 5.2 `[r]R_{n,n}`; **eq. (5.6)**
  `φ_r R →^{ψ_r α} ψ_r S^{f_r} ⟺ ψ_r α φ_r R ⊆ ψ_r S^{f_r}` with `α` independent of
  `r` and `ψ_r α φ_r = ψ_r α` → **STRETCH S-19**.

**Ch. 6 Randomness Expansion (printed 123–131)** — a constructions chapter; every
statement is of the parameterized/filtered shape (5.6):
- §6.1.1 randomness expansion as a construction; IT vs computational split.
- §6.1.2 `k`-wise independence from a degree-`(k−1)` polynomial over `GF(2^m)`:
  `U_{km} →^{[k]α} [k]R_{m,m}`.
- **§6.2.2 Def 6.1 VIL-URF `V_n`** — defined as a **behavior**, with the explicit
  remark that *"because the input alphabet is infinite, `V_n` can not be described as a
  probabilistic discrete system"* → reinforces **FLAG F-1**.
- **§6.2.3 Theorem 6.1 (CBC-MAC as a randomness expander)**: with the restriction
  converter `θ_r`, eq. (6.1) `θ_r CBC = θ_r CBC[r]`, and
  `[r]R_{n,n} →^{θ_r CBC} (θ_r V_n)^{ε_r}`, `ε_r = ½r²2^{−n}`; proof = MBO + Thm 4.17
  + Lemma 4.18.
- **§6.2.4 Theorem 6.2 (construction from a collision game)**:
  `[S, [r]R_{m,n}] →^{[r]casc} ([r]V_n)^{f_r}` with
  `f_r = b[r]S̃ ∘ [r]Ṽ_n ≤ Γ(b[r]Ŝ)` — a construction whose **relaxation is indexed by
  a game-winning performance function**; consumes `casc` (Def 3.11) as a converter.
- §6.2.5 the CRHF discussion — "a reduction statement for which there exists **no**
  corresponding hardness statement", since a single fixed hash function has a trivial
  collision finder. A methodological pin worth keeping (it is the same point as
  §2.8.4 and the motivation for §5.4).
- **§6.2.6 Def 6.2 `δ`-almost universal hash function** with a **length-dependent**
  `δ : ℕ → ℝ⁺` (`Pr(H_K(y) = H_K(y′)) ≤ δ(max(|y|,|y′|))`, explicitly more general than
  the usual definition); **Lemma 6.3** the polynomial `δ`-AUH with `δ(ℓ) = 2^{−m}ℓ/m`.
- **§6.2.7 Corollary 6.4** URF domain extension from a `δ`-AUH:
  `[U_k, [r]R_{m,n}] →^{τ_{r,ℓ}α} (τ_{r,ℓ}V_n)^{ε_{r,ℓ}}`, `ε_{r,ℓ} = ½r²δ(ℓ)`.
→ **STRETCH S-20** (the whole chapter as a construction *genre*: filtered/parameterized
randomness-expansion statements, with S-17/S-18/S-19 as its machinery).

### Chunk I — PDF 73–78 (Ch. 7 printed 133–144)

- **Def 7.1 key agreement** typed as a construction with a **performance-function
  relaxation**: `[•→•, •←•] →^π (σ^E •≡≡•)^f`; **Theorem 7.1** DH achieves it with
  `f = DDH ρ` (a §5.3.5 reduction-based relaxation instantiated by a distinction
  problem) — a clean worked instance of S-18.
- **§7.2.1 Theorem 7.2 (impossibility of IT key agreement)**: no `π`, `σ` with
  `ε ≤ ¼`, even with arbitrarily many rounds; eq. (7.1) the generalized statement with
  an initial correlation `[P_XYZ]`. Modeling device worth noting: **`Φ_E`, the
  specification of an *arbitrary* resource at `E`**, used to say "we do not care what
  the constructed resource gives Eve, including an arbitrarily powerful computer" →
  folded into **STRETCH S-15** (interface typing) / S-16.
  AC does have the impossibility *shape* (`Unconstructible`, MR16 rows 3 and 11).
- **Theorem 7.3** `I(K_A;ZC) + H(K_A|K_B) ≥ H(K_A) − I(X;Y|Z)`, proved by showing
  `I(X';Y'|Z')` cannot increase under any of the four protocol operations (local
  randomness, local computation, sending a message, deletion of information);
  **Corollary 7.4** `H(K) ≤ min(I(X;Y), I(X;Y|Z))`; Fact 7.1 (basic entropy facts) →
  **STRETCH S-21**.
- §7.2.2 possibility: the **satellite model** (Thm 7.5), the **bounded-storage model**,
  quantum key distribution — named resource genres, application-level.
- **§7.2.3 privacy amplification**: `d(X)`, `p_max(X)`, `p_coll(X)`, **min-entropy
  `H_∞`**, **Rényi entropy `R(X)`**; Lemma 7.6 `1/|𝒳| ≤ p_coll ≤ p_max`;
  **Lemma 7.7 `d(X) ≤ ½√(|𝒳|·p_coll(X) − 1)`**; **Def 7.2 2-universal class of hash
  functions**; Lemma 7.8 (the `GF(2^n)`-multiply-and-truncate class is universal);
  **Theorem 7.9 (leftover hash / privacy amplification)
  `d((G,G(W))) ≤ ½√(2^r p_coll(W))`** → **STRETCH S-22**.
- **§7.3 Def 7.3 random oracle model**: `PO_k`, a uniform random function
  `{0,1}* → {0,1}^k` **as a resource accessible to all parties**; §7.3.2 TOWP-based KA
  in the ROM; **§7.3.3 Theorem 7.10** (Canetti–Goldreich–Halevi: schemes secure in the
  ROM but insecure under *every* concrete instantiation), with a proof sketch →
  **STRETCH S-23**.

### Chunk J — PDF 79–85 (Appendix A)

- **A.1 probability basics** (Defs A.1–A.6: probability space, independence, conditional
  probability, random variable, conditional distribution as a *partial* function,
  statistical independence), **A.1.3 expectation and variance** — Mathlib / the tree's
  `Probability/Distribution.lean` + `Expectation.lean` territory. **COVERED**.
- **A.2 information theory basics**: Def A.7 entropy `H(X)`, Thm A.1 `0 ≤ H ≤ log|𝒳|`,
  Thm A.2, **Def A.8 conditional entropy + mutual information**, the chain rule,
  **Def A.9 conditional mutual information `I(X;Y|Z)`**, Thm A.3 `I(X;Y|Z) ≥ 0`,
  and the entropy-diagram remark that `R(X;Y;Z)` can be negative → the toolkit
  Theorem 7.3 consumes; see **STRETCH S-21**.
- **A.3 number theory and algebra** (Euclid, modular inverses, CRT, groups, Lagrange,
  Euler/Fermat, fast exponentiation) — Mathlib territory, **out of scope**.

---

## Verification pass against the abstract-crypto tree (read-only)

97 library files (`AbstractCryptography`, `ConstructiveCryptography`, `RandomSystems`,
`Probability`, `Applications`). Findings that changed a classification:

| probe | result |
|---|---|
| `Probability/Distribution.lean:1487,1528` | **CR18 Def 4.9 `iidPow` and Def 4.10 `clonePow` are already in the tree**, cited by number (with Example 4.11) — at the *distribution* level only |
| `Probability/UniversalHash.lean:92,99,115` | **CR18 Def 6.2 `δ`-AUH is already in the tree** (`IsAlmostUniversalFor`/`IsAlmostUniversal`, length-dependent `δ`, cited by number), and Def 7.2's 2-universal as `Is2Universal` |
| `Probability/StatisticalDistance.lean:405–500` | **CR18 Exercise 4.4 is formalized** (`abs_expect_sub_expect_le_mul_statDist`), including footnote 12's game-vs-bit-guessing constant; `avgSuccessProb` + the Bayes-error identity `bayesRisk = ½ − ½δ(X,Y)` is the *distribution-level* bit-guessing↔distinction dictionary |
| `RandomSystems/Converter/Cascade.lean` | is **converter serial composition** (Def 3.9, `apply_comp`, `(αβ)ⁱR`), **not** Def 3.11's system cascade `s ▷ t` |
| `RandomSystems/System/Game.lean` (1017 lines) | the T1 game layer is landing: `MonotoneCondition` upper-set lattice, `comap`, `DDG`, the `Y × Bool` view with a proven round trip, `winningMass` (Def 2.25) |
| `RandomSystems/{Game,Technique}/*.lean` | all six are 10-line reserved-home stubs |
| grep: URF, URP, random function/permutation, source, beacon | **no hits anywhere** |
| grep: probabilistic converter / distribution over converters | **no hits** |
| grep: solver, performance, worst-case, problem, self-reduction, multi-game, clone (at system level) | **no hits** |
| grep: min-entropy, Rényi, privacy amplification | only a *pointer* in `StatisticalDistance.lean:529` to `RandomSystems/Entropy.lean` in the **reference** repo |
| `AbstractCryptography/Metric/ReductionRelaxation.lean` | exists, and is **FENCED** (`FENCED: AbstractCryptography.Metric.ReductionRelaxation`, MR11-DEFERRED) |
| `AbstractCryptography/Algebra/Indexed.lean` | its "free interface" means the *exposed index type* (MMPRT18 Def 3.1) — a different concept from CR18 §5.3.1's free interface |
| `AbstractCryptography/Algebra/Star.lean` | classified "CITATION-ONLY | **CR18 Def 5.9** and MauRen16 §3.4/§4.2" — the ∗-relaxation is covered |

**Accuracy note for the CR18-FALLBACK register (LEDGER lines 17–28).** It lists five
load-bearing CR18 items (⊥-completion, converter budget, converter application, filters,
memoryless attachment). At least **four more CR18 definitions are already load-bearing
in the tree and cited by number**: Def 4.9, Def 4.10, Def 6.2, Exercise 4.4 — plus
Def 5.9 in `Algebra/Star.lean`. The register understates the CR18 dependency.

**Primary-source finding (affects the recast routes below).** The LEDGER's
LANZENBERGER OBLIGATION MATRIX enumerates **Chapter 2 only** ("M1 — Chapter 2
enumeration (visual read, complete)"; L5 = §2.5). The thesis's table of contents
(visual read, `papers/thesis (1).pdf`, PDF p. 9–10) shows **Chapter 3, "Theory of
Amplification", printed pp. 43–84**: §3.2 Preliminaries, §3.3 *Hardness Amplification
for Games* (3.3.1 the setting, 3.3.2 monotonic `ψ`, 3.3.3 monotonic and concave `ψ`,
3.3.4 "the square is not (always) optimal", 3.3.5 general predicates), §3.4 Applying the
Amplification Theorem, §3.5 *Hardness Amplification for Predicates* (Levin's reduction,
Chernoff–Hoeffding, a tighter bound for Levin's reduction, an alternative reduction),
plus §2.5.2 *Combinations of Games*. **A primary source covers the ground of CR18 §4.9
and part of §4.4, and no matrix in the LEDGER enumerates it.**

---

# THE STRETCH REGISTER

23 items (S-08 was assigned at the Chunk-D reading log but dropped from this
table; row restored 2026-08-18).  Per-item build assessment: see THE STRETCH
REGISTER ASSESSMENT below. `route` = the primary source that touches the same ground under the R8
hierarchy (MauRen16 > Jost > LiuMau20 > Lanzenberger); `CR18-ONLY` = none does.
Size is a build guess, not a priority.

| # | ch / printed p. | content (one line) | route | size |
|---|---|---|---|---|
| **S-01** | 2 p.26; 4 p.92 | **bit-guessing problems** as a first-class type: Def 2.9 `Λ^D((S,B)) := 2(Pr(Z=B)−½)`, Def 4.8 `[S;B]`, and the two-way dictionary to distinction problems (Lemma 2.3 / eq. 4.7 `[S_U;U] = ⟨S₀|S₁⟩`; Lemma 2.4 / eq. 4.8) | **CR18-ONLY**. The *distribution-level* twin already exists (`Probability/StatisticalDistance.lean` `avgSuccessProb`, Bayes-error identity); missing is the system-level pair and the dictionary | S |
| **S-02** | 3 p.63 | **system cascade `s ▷ t`** (Def 3.11) of an `(𝒳,𝒴)`-DDS with a `(𝒴,𝒵)`-DDS, and its converter form `casc[s,t] = s ▷ t` on parallel access | **CR18-ONLY — but IN TREE** (register was mis-scoped; corrected 2026-08-18): `System.cascade` = Def 3.11 (`Converter/Converter.lean`, notation `⊲ₚ`) with `cascadeAccess`/`cascadeConverter`/`cascadeViaConverter` (`cascadeViaConverter_eq_cascade`), all already listed under §PARTIAL-ONLY above. `Converter/Cascade.lean` is a *different* object (converter serial composition). Residue = the honest realization theorem (reference repo `CascadeRealization.lean`) + the Φ lift. Load-bearing in the source (Thm 6.2, Cor 6.4) | **XS** (COVERED-PARTIAL) |
| **S-03** | 3 p.63 | **output combination `s ⋆ t`** (Def 3.12) for an operation `⋆` on `𝒴`, and its converter form `comb^⋆[s,t]` | **CR18-ONLY — but IN TREE** (same correction): `System.combine` = Def 3.12 (`Converter/Converter.lean`, `⋆ₚ[op]`) with `combineConverter`/`combineViaConverter`, already §PARTIAL-ONLY. Residue = realization theorem + Φ lift; do with S-02 as one commit | **XS** (COVERED-PARTIAL) |
| **S-04** | 4 pp.73, 85–89 | **abstract problems, solvers, performance, and the reduction calculus**: Def 4.1 search problem (with an *instance distribution*), Def 4.2 problem `(Σ_p, (Ω_p,≤), p̄)`, Def 4.3 + eq. (4.1) `τ p̄ ≤ q̄ρ`, the dual eq. (4.3) `p̄ ≤ λ q̄ρ`, Lemmas 4.5/4.6 composition, §4.4.9 generalized (list-indexed) reductions eqs. (4.4)/(4.5), Def 4.4 worst-case problem `𝒫̄(s) := inf_p p̄(s)` | **Lanzenberger Ch. 3** (§3.2/§3.3.1/§3.5) is the un-enumerated primary; recast route = enumerate Lanz Ch. 3 first, then state CR18's frame as its abstraction | L |
| **S-05** | 3 pp.55–57, 64 | **named random-object layer**: Def 3.1 `𝒴`-source (memoryless / with memory), Ex 3.2 beacon `B_n`, Ex 3.3 `U_n`, **Def 3.15 `(𝒳,𝒴)`-random function / `𝒳`-random permutation as function-valued random variables**, Ex 3.5 `R_{m,n}` / `P_m` | MauRen16 §3.2 has the URF, but only as **APPLICATION rows 14–16 (declared out of scope)**; no primary makes the function-valued-RV presentation a definition | S–M |
| **S-06** | 3 p.64 | **probabilistic discrete converter (PDC)**, Def 3.17: a random variable over DDCs, with the lifted composition `(α,s) ↦ αs`; "equivalence of converters is defined" (used at CR18 eq. 6.1) | **CR18-ONLY**. AC's `Σ`/`converterMonoidAt` is a monoid of *deterministic* converters; there is no distribution over converters anywhere | M |
| **S-07** | 3 pp.65–66 | **the channel layer**: a channel as a single-input PDS, `p^C_{Y\|X}`, channel equivalence `C₁ ≡ C₂` and the reading of a conditional distribution as *the equivalence class* of PDS, and the channel cascade `p^{C▷D}_{Z\|X} = Σ_y p^C p^D` | **CR18-ONLY**. `Behaviour.lean` has the general quotient but not the single-round channel nor its composition law | S |
| **S-08** | 3 §3.7.2 | **discrete distinguisher (DDD)** Def 3.24: an environment with two stop symbols `⊣₀`/`⊣₁`, output = index of the stop symbol, `0` if it never stops | **CR18-ONLY**. AC environments carry one stop and the verdict is a *third* factor of the transcript law (F-7), so the two-stop convention is an **encoding, not a semantics**: one `Equiv` "two stop symbols ≃ one stop × Bool verdict" | XS |
| **S-09** | 4 pp.87–88 | **the complexity layer** (§4.4.7): `Σ_c := {s \| γ(s) ≤ c}`, the derived problem `p̄'(c) = sup{p̄(s) : s ∈ Σ_c}` and derived reduction `ρ'(c) = sup{γ(ρ(s))}`, with the paper's *explicit refusal* to fix a computational model. **This is the only complexity/asymptotic apparatus in the whole of CR18** (§1.3.3 argues against carrying efficiency in definitions) | **CR18-ONLY**. MR16 row 32's "models 2–4" (`PARTIAL`, gap G9) is the *converter-class* version, a different axis | M |
| **S-10** | 4 p.91 | **Lemma 4.7**: a distinguisher class closed under complementing the output bit makes `Δ^𝒟` a **pseudo-metric**, and collapses `sup Δ^D` to `sup \|Δ^D\|` — the criterion, on a class, rather than an instance | **CR18-ONLY within the hierarchy**; the class object (`edistD`) is MauRen11 Def 15/16 and is **FENCED** | S |
| **S-11** | 4 p.93 | **`q`-fold instantiation vs cloning lifted to systems**: `S^q`, `S^{[q]}`, `E^q`, `C^q`, the interchange `C^q S^q = (CS)^q`, and `⟨X⟩` (countably many independent copies) | **CR18-ONLY**. Defs 4.9/4.10 already exist at the *distribution* level (`Distribution.lean:1487,1528`); the system/converter/environment lift and the interchange law do not | M |
| **S-12** | 4 pp.93–97 | **reductions on games**: `ρ^C : W ↦ WC` with `ω(wc,g) = ω(w,cg)` and **eq. (4.10) `CG = Ḡ ρ^C`**; `σ^q : W ↦ W^q`; Def 4.11 `ψ_q(x)=1−(1−x)^q`, `χ_q`, eq. (4.11); Lemma 4.8 repetition amplification; **Def 4.12 `q`-clonability by a converter** (`KG ≡ G^{[q]∨}`); **Def 4.13 random self-reducibility** (`∀g, Rg ≡ G`); Lemma 4.9; Theorem 4.10 (`ψ_q Ḡ = Ḡ ρ^K σ^q ρ^R`) | **Lanzenberger Ch. 3** for the amplification half; clonability and random self-reducibility are **CR18-ONLY** | L |
| **S-13** | 4 pp.98–104 | **hardness amplification for games** (§4.9 entire): `[G₁,…,G_k]^∧`; Lemma 4.11 and its `k`-ary Lemma 4.13 (a general `[0,1]`-valued two-argument lemma); Def 4.14 the emulating converters `H̲`,`G̲`; **Theorem 4.12** (`[G,H]^∧ ≤ λ(Ḡ,H̄)[ρ₁,ρ₂]`, `λ(x,y)=(1+δ)xy+δ′`, with the `q ≈ 2ln(2/δ)/δ′` calibration); **Theorem 4.14** (`Ḡ^{k∧} ≤ λ Ḡ ρ`, `λ(x)=(1+δ)x^k+δ′`) ⟹ `hard(G,β) ⟹ hard(G^{k∧}, β^k)` | **Lanzenberger Ch. 3 §3.3 is a direct primary home** (and its abstract claims a *simpler, more general and stronger* theorem of this type). Recast: enumerate Lanz §3.3, state CR18 §4.9 as its special case; do **not** build from CR18 | L |
| **S-14** | 5 pp.114, 116 | **relaxation ∥ parallel composition**: Def 5.7 `[R₁,…,ρ(R_i),…,Rₙ] ⊆ ρ([R₁,…,Rₙ])` and eq. (5.4) "pulling relaxations to the outside"; plus the simultaneous `k`-ary construction composition eq. (5.3) that the notes decline to discuss | **JosMau20** (`Specification/Parallel.lean` is JM20 Theorem 1.2) — recast there, not from CR18 | S |
| **S-15** | 5 p.117; 7 p.133 | **interface typing**: party / adversary / **free** interfaces (the free interface models the *environment's* access, e.g. an authenticated channel's forwarding trigger `F`); and §7.2.1's `Φ_E` device — the specification of an *arbitrary* resource at `E` ("we do not care what Eve gets") | MR16 §3.1/§7 has honest-vs-dishonest grouping (rows 12, 64) but no third role; the **free interface is CR18-ONLY**, and the name collides with `Algebra/Indexed.lean`'s unrelated use — see FLAG F-4 | S–M |
| **S-16** | 5 p.117 | **the converter/resource boundary**: the three choices for what a converter may compute (all systems / **trivial, connect-only** / efficiently implementable), the notes' adoption of the trivial-converter stance, and the reification **`αR = π[R, α̃]`** (a converter re-read as a parallel resource plugged by a connect-only converter) | MR16 §3.5 row 32 (`PARTIAL`, gap G9) is the planned home for "Σ as a parameter, models 1–4"; this is that gap's content, named. §5.3.7's `U* ⊆ [V,σ̃_E]*` half is already **COVERED** by MR16 row 45 | M |
| **S-17** | 5 pp.120–122 | **game-relaxation** Def 5.10: `T̂^⊥` = the PDS that behave as `T` while the MBO is 0 and **arbitrarily** once it is 1; Lemma 5.2 (`S ≡ᵍ T̂ ⟹ S ⊆ T̂^⊥`), Lemma 5.3 (`Ŝ ⊫ T ⟹ S ⊆ T̂^⊥`), its compatibility per Defs 5.6/5.7, and Theorem 5.4 (authentication amplification: `hsh[AUT_k,INS_n,H_A,H_B] chk ⊆ [AUT_n, γ_coll H_E]^{*⊥}`) as the worked example — a hash-based security statement with **no asymptotics and no collision-resistance assumption** | **LiuMau20 §2.4/§2.5** game specifications over test families (`ConstructiveCryptography/Multiparty/Basic.lean`) is the recast route. **NOT in the CR18 RECAST dictionary** — the dictionary covers multigames, game reductions, `S⁻`, game equivalence, the `k`-bit view, and stops there | M |
| **S-18** | 5 p.119; 6 p.128; 7 p.132 | **reduction-based relaxations**: `f = λ(p̄₁,…,p̄ₙ)[ρ₁,…,ρₙ]` and **eq. (5.5) `𝓡^f := {R′ \| ∃R ∈ 𝓡 : ⟨R\|R′⟩ ≤ f}`** — computational closeness as a relaxation indexed by a reduction; instantiated at Thm 7.1 (`f = DDH ρ`) and Thm 6.2 (`f = Γ(b[r]Ŝ)`). The notes flag compatibility for this type as "a bit subtle" and skip it | **Jost Def 2.2.9 / JM20 Def 3** — `Metric/ReductionRelaxation.lean` exists **but is behind the MR11 PROVENANCE FENCE**. Planned-but-blocked, not absent | M |
| **S-19** | 5 p.122 | **parameterized resources and constructions** Def 5.11: a family `{φ_r R}_{r∈𝒵}` of *finite* resources cut from a (generally infinite) `R` by a family of filter converters, and **eq. (5.6)** `φ_r R →^{ψ_r α} ψ_r S^{f_r}` with `α` **independent of `r`** and the coherence `ψ_r α φ_r = ψ_r α` | **CR18-ONLY**. Depends on the filter row (LEDGER `filterDom/filterQueries`, PENDING, A8) | M |
| **S-20** | 6 pp.123–131 | **the randomness-expansion construction genre**: `k`-wise independence from a `GF(2^m)` polynomial (`U_{km} →^{[k]α} [k]R_{m,m}`); Def 6.1 **VIL-URF `V_n`**; Theorem 6.1 CBC-MAC as a randomness expander (`[r]R_{n,n} →^{θ_r CBC} (θ_r V_n)^{½r²2^{−n}}`); Theorem 6.2 construction from a **collision game** (`[S,[r]R_{m,n}] →^{[r]casc} ([r]V_n)^{f_r}`, `f_r ≤ Γ(b[r]Ŝ)`); Cor 6.4 `δ`-AUH domain extension | **CR18-ONLY**. Partly pre-empted: **Def 6.2 `δ`-AUH is already in the tree** (`Probability/UniversalHash.lean`, cited by number). Missing = the objects (URF/VIL-URF, see S-05) and the four construction theorems | L |
| **S-21** | 7 pp.134–136; App. A.2 | **the IT key-agreement bound**: Theorem 7.3 `I(K_A;ZC) + H(K_A\|K_B) ≥ H(K_A) − I(X;Y\|Z)`, proved by showing `I(X';Y'\|Z')` is non-increasing under each of the four protocol operations (local randomness, local computation, sending a message, deleting information); Cor 7.4 `H(K) ≤ min(I(X;Y), I(X;Y\|Z))`; and the App. A.2 toolkit (`H`, `H(Y\|X)`, `I(X;Y)`, `I(X;Y\|Z)`, chain rule, Thms A.1–A.3) | MauRen16's appendix has `H_min(X\|Y)` + chain rule (**APPLICATION rows 66–69, out of scope**). The **toolkit** is on the plan as **T6** ("the information-theory layer … Divergence.lean, DistExpect.lean"); the **four-operation monotonicity argument and the KA bound are not** | M |
| **S-22** | 7 pp.138–141 | **privacy amplification**: `d(X)`, `p_max(X)`, `p_coll(X)`, **min-entropy `H_∞`**, **Rényi entropy `R(X)`**, Lemma 7.6 `1/\|𝒳\| ≤ p_coll ≤ p_max`, Lemma 7.7 `d(X) ≤ ½√(\|𝒳\|p_coll(X) − 1)`, Lemma 7.8 (the `GF(2^n)`-multiply-and-truncate universal class), **Theorem 7.9 `d((G,G(W))) ≤ ½√(2^r p_coll(W))`** | **CR18-ONLY**. Def 7.2 (2-universal) is already covered (`Is2Universal`); min-entropy exists only in the **reference** repo (`RandomSystems/Entropy.lean`), pointed at from `StatisticalDistance.lean:529` | M |
| **S-23** | 7 pp.141–143 | **the random oracle as a resource**: Def 7.3 `PO_k`, a uniform random function `{0,1}* → {0,1}^k` **accessible to all parties**; the ROM key-agreement construction; and **Theorem 7.10** (Canetti–Goldreich–Halevi: schemes secure in the ROM, insecure under *every* concrete instantiation) | **CR18-ONLY**. `Applications/Sponge.lean` / `Algebra/Star.lean` use random oracles only in the indifferentiability sense; there is no `PO_k` resource and no uninstantiability statement. Note Thm 7.10 is a **proof sketch** in the source | M |

## CR18-ONLY sublist (no primary in the R8 hierarchy touches the same ground)

**S-01** bit-guessing problems · **S-02** system cascade `s ▷ t` · **S-03** output
combination `s ⋆ t` · **S-06** probabilistic converters (PDC) · **S-07** the channel
layer · **S-09** the complexity layer §4.4.7 · **S-10** Lemma 4.7's pseudo-metric
criterion · **S-11** `q`-fold/cloning at the system level · **S-19** parameterized
resources and constructions · **S-20** the randomness-expansion genre · **S-22**
privacy amplification · **S-23** the random oracle as a resource.

Partly CR18-only: **S-12** (clonability and random self-reducibility have no primary;
the amplification half routes to Lanz Ch. 3) · **S-15** (the *free* interface role) ·
**S-21** (the four-operation monotonicity argument and the KA bound).

## Items with a primary recast route (do NOT build these from CR18)

| item | recast route |
|---|---|
| S-04, S-12 (amplification half), **S-13** | **Lanzenberger thesis Chapter 3, "Theory of Amplification"** (printed 43–84) — §3.3 Hardness Amplification for Games, §3.4, §3.5 Hardness Amplification for Predicates. Currently **un-enumerated** in the LEDGER (see FLAG F-5) |
| S-14 | JosMau20 Theorem 1.2 (`Specification/Parallel.lean`) |
| S-17 | LiuMau20 §2.4/§2.5 game specifications (`Multiparty/Basic.lean`) |
| S-18 | Jost Def 2.2.9 / JM20 Def 3 — the file exists and is **FENCED** |
| S-16 | MauRen16 §3.5 row 32 / gap G9 |
| S-05 | MauRen16 §3.2 (application rows 14–16, currently declared out of scope) |


---

# THE STRETCH REGISTER ASSESSMENT (2026-08-18)

Read-only assessment pass (agent) over both repositories; **every "in tree"
claim below was re-verified by the coordinator against the named declaration
before it entered this section** (docstring provenance included: `System.cascade`
carries "CR18 Definition 3.11", `combine` "CR18 Definition 3.12",
`ParCompatible` quotes Def 5.7, `relax_trans` quotes eq. (5.4)).  Path
convention: `Specification/`, `Metric/`, `Algebra/` resolve under
`AbstractCryptography/`; `Multiparty/` under `ConstructiveCryptography/`;
`System/`, `Converter/` under `RandomSystems/`.

Revised sizes: **XS 4 · S 7 · S–M 5 · M 3 · L 4** (23 rows) — the register's
build guesses were 7 S/S–M · 11 M · 4 L.  `⚠Bn` = breakage row below.

## Per-item: really missing / route on existing infra

| # | really missing | route (non-breaking) | size | ⚠ |
|---|---|---|---|---|
| S-01 | the system-level pair `(S,B)` + dictionary; `avgSuccessProb` + `sSup_avgSuccessProb_eq_half_add_half_statDist` landed (`Probability/StatisticalDistance.lean`); the carrier shape is `PDG`'s with `Bool` for the condition | reserved `System/Advantage.lean`: `BitPDS := Distribution (DDS X Y × Bool)`; `guessAdv` over `trLawFullyDefined`; eq. (4.7) = sup-exchange over the Bayes identity (`=` on the `[Fintype]` slice per F-2, `≤` unconditional); eq. (4.8) from `advFullyDefined_sum_le`. Do NOT model the bit as an output — collides with `toBitSystem`'s monotone-bit convention | S (easier after T5) | B4 |
| S-02 | realization theorem + Φ lift only (see corrected row) | transplant reference `CascadeRealization.lean` (DDS-level, carrier delta none); `cascadeLaw S T := fTransform (fun p => System.cascade p.1 p.2) (Distribution.prod S T)` + one support lemma in the `faceT` idiom | **XS** | B9 B10 |
| S-03 | realization theorem + Φ lift only | identical shape: `combineLaw op`; one commit with S-02 | **XS** | B9 B10 |
| S-04 | genuinely new — nothing in the tree is a "problem"/"performance"; nearest: `gameSpec`, `Constructible` | **F-5 gate first** (visual enumeration of Lanz Ch. 3 §3.2/§3.3.1/§3.5 — a research task, not code); then carrier-free order theory in `AbstractCryptography/Problem.lean`: `Problem` triple, `Reduction` with eq. (4.1) `perf_p ≤ perf_q ∘ τ`, Lemmas 4.5/4.6 = `le_trans`, Def 4.4 = `iInf`; reuse the `Relaxation`/`Constructs` ordering idiom | L (M code + enumeration). **The register's critical path: S-09b, S-12b hang off it** | — |
| S-05 | only the NAMED objects — `functionEvaluator` (`DiscreteSystem.lean`) already IS Def 3.15's function-valued-RV presentation; `singleQueryEquiv` the single-query reading; URP mass law = `uniform_perm_consistent_mass_eq` (`Probability/Counting.lean`) | `urf`/`urp`/`beacon`/`unif` as `fTransform` pushes of uniform distributions; per F-1 unbounded objects enter as **families of bounded slices** indexed via `filterQueries` | S | B8 B9 |
| S-06 | named PDC + composition + converter equivalence + a probabilistic Σ; `connectPhi` (`ConnectPhi.lean`) already IS Def 3.17's lifted `(α,s) ↦ αs`; the mixture step is `mem_nonexpandingConverters_of_sum` (`Absorb.lean`) — the Absorb scope note ("deterministic input missing") predates legs (c)/(d) and is superseded | `attachLawAt i EL := fun R => fTransform (fun p => attachEngineFully i p.1 p.2) (prod EL R)`; a **NEW** submonoid `converterMonoidAtProb` + its own nonexpansion instance (containment proved, generator set of `converterMonoidAt` untouched — now pinned, check 5); converter equivalence = equality of induced `Function.End Phi` | S–M | **B2** |
| S-07 | the name `Channel`, the kernel `X → Distribution Y` + round trip, the cascade law; single-round object + class reading landed (`SingleQuery.lean`, `Behaviour.lean`) | `Channel X Y := {C : PDS X Y // HasDomain C (singleQueryDomain X)}`; kernel via the answer pushforward; kernel = complete invariant of `Behaviour`; cascade law consumes S-02's `cascadeLaw` + `Conditional.mass_eq_sum_condProb_mul_mass` | S, **after S-02** | B9 |
| S-08 | an encoding, not a semantics (F-7: verdict = third factor) | one `Equiv` "two stop symbols ≃ one stop × Bool verdict" | XS | — |
| S-09 | **split**: converter half = `Constructible.mono_constructors` (`ConstructorClass.lean`), i.e. "shrink the solver set, the problem gets harder", already stated for constructions; performance half (`p̄'`, `ρ'`) is content-empty without S-04 | cheap half now: `costBounded (γ : Sigma → ℕ∞) c := {s \| γ s ≤ c}` + the monotone chain, γ a parameter (matching the source's explicit refusal to fix a computational model); rest folds into S-04 | S (half) + folded | — |
| S-10 | only the *criterion* — the conclusion is landed twice (`instance PseudoEMetricSpace Phi` by ⊔-symmetrization; `advFullyDefined_comm_of_weight_eq` = symmetry at equal weight with NO class hypothesis); F-3 records this | fence-clean form if ever funded: `OutputFlipClosed` on **environment sets** + one sup-collapse theorem via `statDist_symm_of_eq_weight`; never over the fenced class objects | S — **PROPOSED CUT 1** | B4 |
| S-11 | `S^{[q]}` (one sample, q addresses), `C^q`, the interchange; `S^q` in substance = `tuple`/`copy` at disjoint fibers (landed R7″ surface) | `clonePhi q R` via `System.copy` folds; `converterPow q := ∏ attachAt (fiber k) E` inside `converterMonoidAt`; interchange by iterating `attachAt_mul_parF` + `smul_parF`, disjointness by `face_copy_disjoint`, commutation by `parF_copy_comm`. NO unconditional interchange (`parF_absorb` documents off-disjoint; `parF_self` needs weight 1) | S–M | — |
| S-12 | **split**. ρ^C is `MonotoneCondition.comap` — RECAST-PLANNED, not stretch. S-12a (Def 4.12 q-clonability `KG ≡ G^{[q]∨}`, Def 4.13 RSR `∀g, Rg ≡ G`, Lemma 4.9, Thm 4.10 skeleton): two `gameEquivalent` statements + a `supWinProb_congr_gameEquivalent` chain. S-12b (ψ_q, χ_q, Lemma 4.8): F-5-blocked | S-12a in `RandomSystems/Game/` (gate-free) after S-11; S-12b only after the Lanz Ch. 3 enumeration | S-12a M · S-12b L | — |
| S-13 | genuinely new AND entirely F-5-blocked (recast bound to Lanz Ch. 3 §3.3, un-enumerated); adjacent assets landed: `expect_mul_sq_le_sq_mul_sq`, `ConcaveOn.le_map_expect`/`ConvexOn.map_expect_le`, `one_sub_sum_le_prod_one_sub`; the `∧`-combination = the landed `MonotoneCondition` lattice meet on a product system — no new lattice | (1) F-5 enumeration; (2) the two-argument `[0,1]` lemma on `Distribution.expect` (carrier-free); (3) Thm 4.12/4.14 over `supWinProb` | L — **PROPOSED CUT 3** (sequencing, not value) | — |
| S-14 | almost nothing: `Relaxation.ParCompatible` IS Def 5.7, `Constructs.relax_trans` IS eq. (5.4), `relax_par`/`relax_par_right` + `Constructs.epsilonRelaxation_par(_resource)` = eq. (5.3) binary. Whole residue = `epsilonRelaxation_parCompatible` takes `[IsNonexpandingPar Φ]`, **not obtainable at the RS Phi** (spike G6.f) | one Φ-level theorem in `ParFace.lean`'s metric section: `parF`-slot containment of ε-relaxations under a separating splitting + sub-probability, via `edist_parF_right_le`/`edist_parF_left_le`; leave the class **uninstantiated** (now gated, check 5) | **XS** | **B6** |
| S-15 | the third interface ROLE + a name for `Φ_E`; two-role split landed everywhere (`attachedWithin`, `filteredAt`, `zSub`/`zStar`, `converterMonoidWithin`); §7.2.1's `Φ_E` already IS `star (converterMonoidWithin E)` (eliminator `mem_star_converterMonoidWithin_iff`) | three pairwise-disjoint sets `(iP, iA, iF)`; admissible Σ = `converterMonoidWithin (iF)ᶜ`; role algebra free from `converterMonoidWithin_mono` + `commute_converterMonoidWithin`. Name the role `openInterface`/`environmentInterface` — **never `freeInterface`** (F-4) | S | B7 |
| S-16 | the reification `αR = π[R, α̃]` only (converter-class choices already parametric via `Constructible (Γ)`; row 32 = recorded modeling CHOICE) | `α̃ := copy k (ofDDS E)` into a disjoint fiber; `π := attachAt (i ∪ fiber k) W` an ordinary `InnerTotal` + `AnswersWithinUniformBudget` engine; one theorem via `attachAt_parF` + `attachAt_mul_parF` + `face_copy_disjoint`; precedent: `exists_attachAt_eq_block` | M — **highest breakage risk** | **B1** |
| S-17 | the set `T̂^⊥`, Lemma 5.3, Def 5.6/5.7 compatibility; **Lemma 5.2's engine is proved** (`advFullyDefined_toBitLaw_le_supWinProb`, `Winnability.lean`) | `gameRelaxation (T̂ : PDG X Y) : Specification Phi` off the fired set (`winningMass`/`gameTrLaw`); containment `gameRelaxation T̂ ⊆ epsilonRelaxation (ofReal (supWinProb T̂)) {forget T̂}` — **⊆ only, NOT `=`** (the ε-ball is strictly larger; do not define `T̂^⊥` as a ball); Lemma 5.3 = `supWinProb_le_infWinnability` ∘ containment; compatibility descends from `epsilonRelaxation_compatible` + the S-14 Φ-form to the subset. Thm 5.4 (authentication amplification) scoped out as an application rider | S–M — **nearly free NOW** (T2 closed) | B5 |
| S-18 | mathematically nothing — `Metric/ReductionRelaxation.lean` (fenced) already has the object, composition, three compatibility legs, `relax`-trans/par, and both scalar comparisons (`reductionRelaxation_const_eq_epsilonRelaxation`, `…_singleton_ne_…`) | administrative resolution FIRST: (a) scalar reading = `epsilonRelaxation`, already landed and consumed; (b) fence-clean twin = re-index the budget by environment sets, re-prove the four lemmas. Unfence only at the MR11 reconciliation task | S (a) / M (b) | B3 |
| S-19 | the family statement eq. (5.6) + coherence; **both filter realization theorems are proven** (`apply_restrictionFn`, `apply_queryLimitFn`, `Converter/Cascade.lean`) — the A8 `PENDING` filter row understates the tree | `ParameterizedConstruction (φ ψ : Z → Sigma) (π : Sigma)` with a single quantified `π`; coherence `ψ r * π * φ r = ψ r * π` collapses the family, via `constructs_congr_protocol` + `approximately_constructs_congr_protocol`. Prereq: Φ-level `fTransform (filterQueries q)` (one line; check-1 row; prove membership in `converterMonoidAt` — the `block Q` generator is the precedent) | S–M | B9 |
| S-20 | the four construction theorems + the objects; landed: δ-AUH (`IsAlmostUniversalFor`) + collision lemmas, `birthday_bound`/`switching_ratio_le` | each theorem = `Constructs … (epsilonRelaxation ε …)` with the probabilistic leaf handed to the H/counting layer; k-wise-independence half = carrier-free `Probability/` algebra (reference `KWiseIndepPoly.lean` is a statement shape, NOT an import) | L — blocked on S-05 + S-17 + T5 | **B11** |
| S-21 | the entire IT layer (no entropy/MI/divergence anywhere) = **T6's declared content**; then the four-operation monotonicity argument + Thm 7.3/Cor 7.4 | after T6: one inductive statement over a four-constructor protocol-step type with `I(X';Y'\|Z')` monotone in each; concavity via `ConcaveOn.le_map_expect`, conditioning via `Conditional`'s chain rules | M after T6 / L without — strictly after T6 | — |
| S-22 | `p_max`/`p_coll`/`H_∞`/Rényi + Lemmas 7.6/7.7 + Thm 7.9; landed: `Is2Universal`, `IsAlmostXorUniversal`, `mass_exists_ne_le_choose_two_mul`, `statDist_eq_one_sub_sum_min` | `pColl X := ∑ a, (X a)^2` + `pMax`; Lemma 7.6 by Cauchy–Schwarz; Lemma 7.7 by `expect_mul_sq_le_sq_mul_sq`; Thm 7.9 = 7.7 + the 2-universal collision bound. **T6-independent** if `H_∞ := −log pMax` (statement-only use) | S–M — first of the IT trio | — |
| S-23 | `PO_k` as printed is outside Φ (F-1: uncountable sample space); no `PO_k`, no uninstantiability statement anywhere | bounded family `poK k n := urf (Fin n → Bool) (Fin k → Bool)` (after S-05); "accessible to all parties" = a shared query set under R3 (ownership exogenous — no `copy` needed); ROM KA = ordinary `Constructs` + probabilistic leaf; docstring must cite F-1 (family, not the paper's single infinite object). **Thm 7.10: PROPOSED CUT 2** — proof sketch in the source, and `Unconstructible`'s ∀-over-all-instantiations cannot be honestly discharged | S with the cut | B8 B9 |

## Dependency-ordered shortlist

* **Tier 0 — S-size today, no T dependency:** S-02+S-03 (one commit) · S-14 (XS)
  · S-05 · S-15 · S-09 converter half · S-06 · S-19.
* **Tier 1 — nearly free after their input:** **S-17 (input = T2, CLOSED — buildable
  now)** · S-07 (after S-02) · S-01 (after T5) · S-12a (after S-11) · S-22
  (T6-independent route) · S-21 (after T6).
* **Tier 2 — stay M/L:** S-11 · S-16 (B1) · S-18b · S-23 · S-04 (F-5) ·
  S-13 (F-5) · S-20 · S-12b (F-5).
* **PROPOSED CUTS (pending Marc, recorded not decided):** (1) S-10 entire —
  conclusion landed twice, the criterion is about a fenced object, no in-tree
  consumer; (2) S-23's Thm 7.10 — see row; (3) S-13 until the F-5 enumeration —
  a sequencing cut; funding it from CR18 first would reproduce the R8 defect.

## Breakage risks (assessment rows B1–B11)

| # | items | risk | gate | mitigation |
|---|---|---|---|---|
| B1 | S-16 | the reification's natural implementation is a **relay** (REFUTED design family) | check 3 (`relayExcept`/`attachFullyAt`/`botToken`) | `π` = ordinary `InnerTotal` + `AnswersWithinUniformBudget` engine at `attachAt`; never `attachFully`/`connectFully` |
| B2 | S-06 | widening `converterMonoidAt` — the metric-facing Σ carrying `IsNonexpandingSMul` + all leg-(c)/(d) receipts | **check 5 pin (added 2026-08-18; previously ungated)** | new submonoid `converterMonoidAtProb` + own instance; prove containment |
| B3 | S-18 | `Metric/ReductionRelaxation.lean` is FENCED | check 2 | scalar reading, or the environment-indexed twin; never import |
| B4 | S-10, S-01 | natural home = fenced class objects (`Metric/Distinguisher`, `System/DistinguisherClass`) | check 2 | state over environment sets + `PDS.Distinguisher`/`outputOne` (MR16-CORE) |
| B5 | S-17 | `Multiparty/GameMetric` (FENCED) vs `Multiparty/Basic` (MR16-CORE) — one split file, easy to confuse | check 2 | import `Multiparty/Basic` only |
| B6 | S-14 | registering `instance : IsNonexpandingPar Phi` — recorded NOT OBTAINABLE (G6.f); would silently unlock `epsilonRelaxation_parCompatible` unsoundly | **check 5 tripwire (added 2026-08-18; previously ungated)** | hypothesised Φ-form over `edist_parF_parF_le`; class stays uninstantiated |
| B7 | S-15 | F-4 vocabulary collision ("free interface") | none (brief-level) | `openInterface`/`environmentInterface` |
| B8 | S-05, S-20, S-23 | unbounded ideal objects are outside Φ (F-1/R1); a definition no PDS inhabits | none (F-1 is prose) | families of bounded slices; a first-class unbounded object = carrier-extension **ruling (fork to Marc, only if ever needed)** |
| B9 | S-02/03/05/07/11/19/23 | new names under `System/`/`Converter/` | check 1 | LEDGER rows in the same commit, or the gate-free homes |
| B10 | S-02, S-03 | `cascade`/`combine` are §PARTIAL-ONLY: **no metric claims before A6-style migration** | none automatic | the Φ lift is fine as an object; any `Adv⊥` bound over it needs the migration first |
| B11 | S-20 | CBC-MAC/SoP/switching kits exist only in the read-only reference repo (different carrier) | none | re-derive at Φ, or scope out |

Non-risks verified: reserved 10-line homes exist for S-01/S-12a/S-13/S-17; zero
`sorry` across all five build trees; `Probability/` items (S-13/S-21/S-22) are
carrier-free and gate-free.

## Register defects corrected in this pass

1. **S-02/S-03 were mis-scoped** — route cells corrected in place; §PARTIAL-ONLY
   had listed `cascade`/`combine` all along (the register contradicted the
   ledger's own classification).  Header note amended likewise.
2. **S-08 row restored** (was named at the Chunk-D reading log, dropped from the
   table; count corrected 22 → 23).
3. **Re-priced from the tree:** S-05, S-06, S-14, S-17, S-19 (per rows above).
4. **S-09/S-12 recorded as splits** (register rows kept as the reading record;
   the split is the build plan).
5. **Two previously ungated risks gated:** `ledgerAudit.sh` check 5 —
   `IsNonexpandingPar`-at-`Phi` instance tripwire + `converterMonoidAt`
   definition pin (hash; a legitimate re-ruling updates pin + registry together).

---

# FLAGS — where the paper contradicts, or outruns, what we built

**F-1 (carrier scope). Behaviors with no underlying PDS.**  Ex 3.7 (printed p. 68) and
Def 6.1 (p. 125) say it twice and explicitly: the **VIL-URF `V_n`** over `𝒳 = {0,1}*`
"does not correspond to a PDS as defined here since the sample space would be
uncountable … we can consider the behavior without an underlying probabilistic system."
PHI-SPEC R1 makes the AC carrier `Φ := PDS Uni Uni` — a distribution over DDS — and
`Behaviour` is defined as a **quotient of PDS**.  So every variable-input-length object
(VIL-URF, the arbitrary-input-length random oracle of MR16 §3.2, CR18's `PO_k`) is
outside the AC carrier by construction, and the behavior-first escape the source uses is
not available in the tree.  **Not a broken theorem — a scope limit the source states in
the negative and no AC document records.**  Flagging, not solving.

**F-2 (fallback hygiene).**  §4.10's standing simplification (p. 105) has **no `⊥`, no
refusal, no partial domain**: environments stop after `q` queries and short runs are
padded with dummies.  Already pinned in the LEDGER SOURCE LEDGER; restated because six
of the register's items (S-01, S-10, S-11, S-12, S-13, and the T1/T3 recasts) live in
that section and every one of them must be re-derived on the `Adv⊥` carrier.  PHI-SPEC
R2's observable, non-fatal refusal has **no counterpart in this source at all**.

**F-3 (metric convention).**  Def 2.6 defines `Δ^D` **signed**; `Δ^𝒟 = sup |Δ^D|` is a
*theorem* (Lemma 4.7) conditional on the class being closed under complementing the
output bit.  AC reaches the same place by ⊔-symmetrizing `advFullyDefined`.  No
contradiction — but the criterion, not the conclusion, is what S-10 asks for.

**F-4 (vocabulary collision).** "**Free interface**" means two different things:
CR18 §5.3.1 = a third interface *role* (the environment's access, e.g. a channel's
forwarding trigger); `AbstractCryptography/Algebra/Indexed.lean:11,59,73` = the
*exposed interface index type* of a resource (MMPRT18 Def 3.1).  Any S-15 brief must
rename one of them.

**F-5 (coverage gap in a primary matrix — highest value).**  The LEDGER's LANZENBERGER
OBLIGATION MATRIX enumerates **Chapter 2 only** and presents itself as complete ("M1 —
Chapter 2 enumeration (visual read, complete)"; the aggregate tally is 57 items over
L0–L5 = §2.1–§2.5).  The thesis has a **Chapter 3, "Theory of Amplification" (printed
43–84)**, whose §3.3 is *Hardness Amplification for Games* and §3.5 *Hardness
Amplification for Predicates*.  That is a **primary** source for the ground CR18 §4.9
and part of §4.4 cover, and it is unmapped.  Consequence for this register: S-13 (and
half of S-04/S-12) must **not** be built from CR18 — the correct next step is an
enumeration pass over Lanz Ch. 3.

**F-6 (dead pointers in the source).**  Two of CR18's own relaxation types come with no
content: §5.3.9 *substitution relaxation* is named and then "will not be discussed", and
§5.3.5 says compatibility of reduction-based relaxations "is a bit subtle" and skips it.
Recorded so no future brief chases either here.

**F-7 (T5 scope traps, not stretch items).**
- eq. (3.3) + its negation (p. 70): the **one-step** law survives embedding in an
  environment (`p^{ES}_{Y_i|X^i Y^{i−1}} = p^S_{Y_i|X^i Y^{i−1}}`) but the **cumulative**
  law does **not** (`p^{ES}_{Y^i|X^i} ≠ p^S_{Y^i|X^i}`).
- §4.10.2 (p. 106): against a *distinguisher* the transcript law is a **three**-factor
  product `p^D_{X^q|Y^{q−1}} · p^S_{Y^q|X^q} · p^D_{Z|X^q Y^q}` — the verdict bit is a
  third factor, not part of `η`.  Lemma 3.2's two-factor form is the *winner* case.

---

# COUNTS

| class | count | notes |
|---|---|---|
| **COVERED** | 34 | Ch. 3 carrier (Defs 3.2–3.9, 3.13, 3.14, 3.16, 3.18–3.21, Lemma 3.1), Ch. 5 specification calculus (Defs 5.1–5.6, 5.8, 5.9, Lemma 5.1, §5.3.4, §5.3.7), the metric (Defs 2.6–2.8, Lemmas 2.1, 2.2), and four CR18 items already in-tree and cited by number (Defs 4.9, 4.10, 6.2, Ex 4.4) + Def 7.2 |
| **COVERED-PENDING** | 2 | §3.4.3 filters + Def 3.10 `[q]` (LEDGER A8 `PENDING`); MR16 row 32 / gap G9 (the S-16 residue) |
| **RECAST-PLANNED** | 14 | Def 3.20 cumulative law + Lemma 3.2 (T4.4/T5); Def 3.22 MBO/DDG, Def 3.23 winner, Def 4.5 game, multi-games + Def 4.6 `g^∨`/`g^∧`, Defs 4.15–4.18, Lemmas 4.15/4.16, Def 4.19 CE + eq. (4.38), Defs 4.20/4.21 + Thm 4.17 (T1/T2/T3 + the CR18 RECAST dictionary) |
| **STRETCH** | **22** | the register above |
| out of scope (application rows) | ~45 | Ch. 2 entire, §4.2/§4.3, §4.11.3, §5.4, §7.2.2 — by the LEDGER's own APPLICATION discipline |
| no content in the source | 2 | §5.3.9 substitution relaxation; §5.3.5 compatibility |
| flags | 7 | F-1 … F-7 |

Of the 22 STRETCH items: **12 CR18-ONLY**, **6 with a primary recast route**,
**3 partly CR18-only**, **1 (S-18) planned-but-fenced**.
Sizes: **4 L** (S-04, S-12, S-13, S-20), **11 M**, **7 S/S–M**.

# PROVENANCE FENCE (MR11-DEFERRED)

**Rule (binding, 2026-08-17).**  The working discipline is **MR16-only** until
an explicit MR11 reconciliation task.  Every module listed under `FENCED:`
below holds MauRen11-specific constructs; **no MR16-track file may import a
fenced module.**  Fenced → fenced is permitted, as is fenced → MR16-track.
`scripts/ledgerAudit.sh` derives the fence from the `FENCED:` lines in this
file and FAILS listing any MR16-track file that imports one, so the list here
is the gate's only source of truth — add a module to it in the same commit
that fences it.

Nothing is deleted, deprecated, weakened, or `sorry`-ed by the fence.  Every
declaration keeps its statement and its proof, and every fenced module stays
compiled: the AbstractCryptography ones under the `AbstractCryptographyMR11`
Lake target, the rest under the globbed `ConstructiveCryptography`,
`RandomSystems` and `Applications` targets.  What the fence changes is only
*who may import them*.

The occasion (`PHI-SPEC.md`, MR16-ONLY DISCIPLINE CHECK): MauRen16 formalizes
**no** distinguisher class — one informal sentence (§3.1) defers it — while the
in-tree `DistinguisherClass` is MauRen11 Definition 15/16 provenance.  MR16's
own interface is §4.1's metric on `Φ` plus Definition 2 (non-expanding, two
sided) and Lemmas 1–4, and that is what the MR16 track keeps.

## Classification (M1 audit, every file READ)

| file | verdict | reason |
|---|---|---|
| `AbstractCryptography/Metric/Distinguisher.lean` | MR11-OBJECT | defines `DistinguisherClass` (MauRen11 Def 15/16) and `edistD` (§6.1); the file *is* that object |
| `AbstractCryptography/Metric/Behaviour.lean` | MR11-OBJECT | the carrier taken up to the zero set of `edistD` — MauRen11 Def 14 read through the class |
| `AbstractCryptography/Metric/ReductionRelaxation.lean` | MR11-OBJECT (new, split from `Metric/Epsilon.lean`) | Jost Def 2.2.9 / JM20 Def 3 at a budget indexed by `D.tests`, and the scalar↔indexed bridge |
| `AbstractCryptography/Metric/Simulation.lean` | MR11-OBJECT | Jost Def 2.2.12 stated as `π•ℛ ⊆ D.reductionRelaxation ε (σ•𝒮)`; every declaration consumes `D` |
| `AbstractCryptography/Specification/ChoiceSetting.lean` | MR11-OBJECT | MauRen11 §§4–5, 7 literal: choice settings, CFRs, Defs 1/4/8/9/10/11/18, Theorem 2.  No MauRen16 counterpart |
| `AbstractCryptography/Specification/TwoParty.lean` | MR11-OBJECT (new, split from `Specification/Filtered.lean`) | MauRen11 App. C: Definition 20, eq. (5), Theorem 4 |
| `AbstractCryptography/Refinement/StepwiseRefinement.lean` | MR11-OBJECT | MauRen11 App. A: Definition 19 and Theorem 3.  No MauRen16 counterpart |
| `ConstructiveCryptography/Generalizations/ContextRestricted.lean` | MR11-OBJECT | states every §4.2 construction over `DistinguisherClass` + `reductionRelaxation` |
| `ConstructiveCryptography/Multiparty/GameMetric.lean` | MR11-OBJECT (new, split from `Multiparty/Basic.lean`) | `gameSpec_of_edistD_le`, indexed by `D` |
| `RandomSystems/System/DistinguisherClass.lean` | MR11-OBJECT (new, split from `System/ProbabilisticSystem.lean`) | `PDS.Resource.distinguishers` builds a `DistinguisherClass` |
| `Applications/Frost/ConstructionEps.lean` | MR11-OBJECT (new, split from `Frost/Construction.lean`) | `frost_end_to_end_eps` takes a `DistinguisherClass` parameter |
| `AbstractCryptography/Metric/Epsilon.lean` | MR16-CORE after the split | the scalar `ε`-ball, CR18 §5.2.1 / JM20 Thm 2–3 / Cor 1, over `PseudoEMetricSpace` + MauRen16 Def 2 non-expansion — exactly what `RandomSystems/System/MetricFullyDefined.lean` consumes |
| `AbstractCryptography/Specification/Filtered.lean` | MR16-CORE after the split | `filteredAt` is choice-free and LiuMau20 §§2.4–2.5-grounded (explicitly *not* MauRen11 Def 18); its metric leg uses MauRen16 Def 2 |
| `ConstructiveCryptography/Multiparty/Basic.lean` | MR16-CORE after the split | LiuMau20 §2.4/§2.5 `∗Z`-calculus, game specifications over plain `Set (Φ → ℝ≥0∞)` test families, adversary structures |
| `RandomSystems/System/ProbabilisticSystem.lean` | MR16-CORE after the split | Lanzenberger Def 2.14 carrier, protocols, `Distinguisher`, `outputOne`, `maxEDist` (MauRen16 fn. 9).  Its `AbstractCryptography.Metric.Simulation` import — the only MauRen11 dependency in the whole `RandomSystems` tree — is gone |
| `Applications/Frost/Construction.lean` | MR16-CORE after the split | the exact two-rung ladder and the threshold instance |
| `AbstractCryptography/Metric/Nonexpansion.lean` | CITATION-ONLY | MauRen16 Definition 2 is the primary citation; MauRen11 Def 2/3 quoted as the interface-indexed twin |
| `AbstractCryptography/Algebra/Attachment.lean` | CITATION-ONLY | the equality-level `Monoid`/`MulAction` rendering; MauRen16 §3.3 and CR18 ground it identically |
| `AbstractCryptography/Algebra/Indexed.lean` | CITATION-ONLY | MMPRT18 Def 3.1 is the object; MauRen11 fn. 20 is cited for what it does *not* supply |
| `AbstractCryptography/Algebra/Star.lean` | CITATION-ONLY | CR18 Def 5.9 and MauRen16 §3.4/§4.2; `Indifferentiable` is dual-grounded — MauRen11 Def 23 states it, MauRen16 Lemma 5 makes it a construction statement |
| `AbstractCryptography/Specification/Basic.lean` | CITATION-ONLY | JM20 §2.2 / MauRen16 §3.3 |
| `AbstractCryptography/Specification/Parallel.lean` | CITATION-ONLY | JM20 Theorem 1.2 |
| `AbstractCryptography/Refinement/Basic.lean` | CITATION-ONLY | MauRen11 Defs 5–7, but the same composition laws are MauRen16 Lemma 1 and CR18 Lemma 5.1; it is the base every other module imports |
| `AbstractCryptography/Tactics/ControlledNaturalLanguage.lean` | CITATION-ONLY | prose provenance for sentence wording; no MauRen11 object |
| `AbstractCryptography/Tactics/ProofAutomation.lean` | CITATION-ONLY, one deferred rule | `ac_transfer_property` and its `ac_rules` row name `one_tsub_le_test_of_close`, a fenced lemma, inside syntax quotations.  Both references are built with `Lean.mkIdent` so the name resolves at the **use site**: the rule fires in a file importing `AbstractCryptography.MR11` and reports its ordinary failure message in one that does not.  The module itself imports nothing fenced |
| `RandomSystems/Converter/Converter.lean` | CITATION-ONLY | one remark naming Def 15/16 as the layer a weakened finiteness clause would not survive |
| `RandomSystems/Converter/Cascade.lean` | CITATION-ONLY | one remark: `apply_comp` is what Def 16's emulation closure needs |
| `RandomSystems/System/Absorb.lean` | CITATION-ONLY | MauRen11 Def 2 eq. (4) = MauRen16 Def 2 |

Test and demo modules are fenced because they *consume* the quarantined
surface, not because they define it: `AbstractCryptography{SelectedSurface,
IndexedRelaxation,ProofAutomation,ContextRestricted}Tests` and
`ConstructiveCryptographyDemo{,Support}`.

## The fence (machine-readable; the gate reads exactly these lines)

FENCED: AbstractCryptography.MR11
FENCED: AbstractCryptography.Metric.Distinguisher
FENCED: AbstractCryptography.Metric.Behaviour
FENCED: AbstractCryptography.Metric.ReductionRelaxation
FENCED: AbstractCryptography.Metric.Simulation
FENCED: AbstractCryptography.Specification.ChoiceSetting
FENCED: AbstractCryptography.Specification.TwoParty
FENCED: AbstractCryptography.Refinement.StepwiseRefinement
FENCED: ConstructiveCryptography.Generalizations.ContextRestricted
FENCED: ConstructiveCryptography.Multiparty.GameMetric
FENCED: RandomSystems.System.DistinguisherClass
FENCED: Applications.Frost.ConstructionEps
FENCED: AbstractCryptographySelectedSurfaceTests
FENCED: AbstractCryptographyIndexedRelaxationTests
FENCED: AbstractCryptographyProofAutomationTests
FENCED: AbstractCryptographyContextRestrictedTests
FENCED: ConstructiveCryptographyDemoSupport
FENCED: ConstructiveCryptographyDemo


AUDIT RECORD (adversarial statement-content audit, 2026-08-18,
/private/tmp/claimaudit/AUDIT.md): 10 of 12 claims HOLD with compiled
evidence (canonicity non-vacuous; parF_self's weight-1 hypothesis proven
NECESSARY; quotient-2.31 genuinely class-level, rfl fails; EMetricSpace
separation real; Example 2.16 and Figure 2.1 match the printed pages).
OVERSTATED, corrected above: D2 (edist_parF_left_le frame hypotheses),
D3 (absorption reachable at empty faces), D5 (min-form counterexample
refutes the proof display, not the theorem).  D4: row 2.16 prints [V] =
{V_α}; the tree proves ⊆ only.  BROKEN + FIXED: D1 — duplicate
`answeredQueries_concat_{some,none}` in both lanes made the subtrees
mutually unimportable, hidden because `lake build`'s globs exclude the
root; consolidated to Environment.lean (the definition's home), root
elaborates, and ledgerAudit check 4 (rootAudit) now makes the blindness
impossible.  C5 note: `contextInsensitive_par_left` is a conditional with
NO inhabiting instance today (Par ↥converterMonoidAt unsynthesizable) —
usable only after the G-6 class leg.
# PHI-SPEC — the rulings register

The working spec of the MR16/CC formalization.  (Ruling labels R1-R9 are
historical names, not an enumeration — R5/R6 were never assigned.)  Validation state lives in
`LEDGER.md` (four-gate `scripts/ledgerAudit.sh`); the full design
archaeology (contracts, pipelines, refutations, closeouts) lives in the git
history on branch `archive/pre-squash-2026-08-18`.

## Sources (R8)
Primary, in order: **MauRen16, Jost thesis, LiuMau20, Lanzenberger thesis**.
CR18 is fallback-only (register in LEDGER.md top); MauRen11 is behind the
provenance fence pending an explicit reconciliation.

## Carrier (R1–R3)
*(Scope note, corrected 2026-08-18 — Marc: variable-input-length SYSTEMS
are ordinary PDS at their own message alphabets (CBC = finite-support
mixture over its keys, in Φ; its theorems exist in the reference
repository and are not re-proven).  The limit concerns only infinite-domain
IDEAL objects — the uniform random function over {0,1}*, CR18 Ex 3.7 —
which need uncountable randomness: no finite-support PDS realizes or is
behaviorally equal to one.  They enter as families of bounded slices
(bounded query count/length restrictions ARE honest PDS), which is how
every quantitative theorem uses them; a carrier-extension ruling is owed
only if an UNBOUNDED ideal object must ever be first-class.)*
- **R1** Φ := `PDS Uni Uni`, `Uni := Σ X : Type u, X`; the official
  interaction carrier is the FULLY DEFINED slice (CR18 Def 3.3's completion
  promoted to object); partial systems enter via `s⊥`; deletion is the
  embedding's shape, not an interaction rule.
- **R2** Refusal is observable (⊥ = `none`) and non-fatal — for every
  system, converters included (the uniform reading; its two violations were
  refuted: the B4 rewind and the G1 relay).
- **R3** Addressing is exogenous: an interface is a set of queries
  (`Set Uni`); ownership is never inferred from domains.

## Metric (R4/R4′)
- **R4** The statement-facing metric is `Adv⊥` (`PDS.advFullyDefined`) —
  Lanzenberger Def 2.26 over the CR18 total presentation; `PseudoEMetricSpace
  Phi` by ⊔-symmetrization.
- **R4′** (Marc-ruled, option A) Both presentations first-class with a
  crossing API: `equivalent` (Def 2.17), `classDistance` (Def 2.28),
  congruence transports, `Adv⊥ ≤ Δ`, coupling bounds land on `Adv⊥`.
  Domain-indexed strict layer: `HasDomain`/`CompatibleD`/`AdvD` (descends
  unconditionally).

## Parallel and converters (R7″)
- Primitive attachment: `attachAt i E` (interface-indexed ownership
  dispatch; `attachEngineFully` at the carrier); whole-face = `attachAt
  Set.univ`; the metric-facing Σ is `converterMonoidAt`.
- Parallel: `parF L M := par (face L) L M` — face dispatch, two-splitting
  canonicity, comm/assoc on separated faces; user surface through
  definedness-disjoint `copy`/`tuple`; `parF_absorb` documents the
  off-regime.  Converter `∣ := *` with the fn. 23 ruling (an fn. 20
  addressing artifact; `α∣1 = α` proven, `α∣α = α²` recorded).
- The C8 lesson (binding trap): addressing lives at the VALUE level of a
  single type; type-level tags are unreadable.

## Class distance (R9)
`classDistance` infimizes over HONEST (NonNeg) representatives — the
thesis's Def 2.28 meaning; signed representatives are proof tools only.
`Δ(S,S) = ⊤` off the honest carrier (empty infimum, thesis-correct).
Def 2.28's pair identity is an equality; Thms 2.31/2.32 hold on the finite
shared-domain slice and at the Behaviour quotient (an `EMetricSpace`).

## Status
Information theory (T6, 2026-08-18, audited): LANDED on Distribution —
Shannon entropy, conditional entropy, mutual and conditional mutual
information with all chain rules AND equality conditions; min-entropy /
collision entropy with the MauRen16 chain rule; KL divergence with Gibbs
and Pinsker.  Base conventions deliberate and documented: entropy layer =
BITS (log₂, CR18's convention), klDiv = NATS (pins Pinsker's ½); no
statement mixes them.  mathlib has no distribution-level entropy and no
Pinsker — these are native; the mathlib alignments that exist are
`entropy_eq_sum_negMulLog_div_log_two` and `Distribution.klDiv_toPMF`
(kernel-checked on the isProbDist slice via Probability/
DistributionMeasure.lean).  S-21/S-22 unblocked on the probability side.
MR16 basics-done: **YES** — census 44/48 D+I counted from the matrix
cells; residue by design (G10 fenced rows 13/48, §3.5 models row 32
optional, prose row 31).  Lanzenberger pure-RS scope complete (L4 games +
L5 amplification deferred by scope ruling).  Deferred queues and open
micro-questions: see LEDGER.md.

## Technique program (R10, 2026-08-18)
- **Game** := the thesis's pair — a system with a monotone condition
  `A : X⁺ → Bool` per deterministic atom (Def 2.20); probabilistic game =
  joint distribution over pairs (Def 2.22).  The bit-output presentation
  (Maurer13b Def 9 / CR18) is a DERIVED VIEW with a proven round trip; the
  two are equivalent at both levels (per-atom, inputs determine the whole
  interaction, so input predicates lose no generality; internal randomness
  enters through the joint distribution — CBC: the condition is A_k,
  key-indexed).  No fork exists.
- **Integration pattern** (binding): modeling = CONSTRUCTORS WITH NAMED
  OBLIGATIONS; technique = theorems over the valid class.  The game
  constructor is `adjoin` (Rem 2.24's word) with two obligations:
  (1) per-atom monotonicity; (2) the forgetting law — dropping the bit
  returns the original BEHAVIOUR (stated against the equivalence class;
  representative choice is how one discharges it, not a modeling wrinkle).
  MPR07 Lemma 5 = COMPLETENESS of the GAME LAYER (T4 audit correction,
  2026-08-18).  At a FIXED presentation `adjoin` cannot carry the witness —
  its not-won mass is a sum of whole atom masses (`winningMass_adjoin`),
  while eq. (4) needs the fraction `min(p^S,p^T)/p^S` — and Definition
  2.22's law over pairs supplies the split natively
  (`PDS.exists_gamesFor_notWonLaw_eq_trLawFullyDefined`).  At the class
  the constructor question is open and not load-bearing: the witness may
  equally be an `adjoin` of a re-decomposed presentation.  Attains the
  distance on equivalent systems; non-unique; δ-shaped.  SCOPE (T4
  discovery, kernel receipt, 2026-08-18): per-distinguisher tightness
  (Lemma 5(iv)) holds on the FULLY-DEFINED slice only — on the ⊥-total
  carrier it is REFUTED (conditions read answeredQueries, refusal-deleted;
  total environments observe refusals; the nowhere-defined system is a
  counterexample against every game on every equivalent presentation).
  The supremum-level form (fn. 16) is unaffected.
- **H-coefficient, three layers**: (1) partition bound (in tree:
  statDist_sum_of_disjoint_support family); (2) good/bad corollary (in
  tree: the hTechnique kernel); (3) transcript instantiation — the ONLY
  build item: the factorization Pr[τ] = η(e,τ)·σ(S,τ) and its corollary
  (ratio on σ over good + ideal bad mass ⇒ environment-uniform Adv⊥
  bound; adaptivity free because η cancels).
- **Vocabulary** (binding): "monotone condition (MC)", "game", "adjoin",
  "σ/η factorization", "good/bad", "deficiency".  FORBIDDEN: "blinder" as
  an object (none exists in any source); the bit-output form as primitive;
  any environment that observes the condition (Rem 2.23).
- **R11 — concept recast, never parallel modeling (Marc, 2026-08-18,
  binding on every migration leg):** "CR18 migration" means taking THE
  CONCEPT and reimplementing it ON TOP of the landed infrastructure — we
  already have PDS, games, conditions, transcript laws, conditioning.  A
  source concept enters ONLY as definitions/theorems over the existing
  objects (`Phi`/`PDS`, `PDG`, `MonotoneCondition`, `gameTrLaw`,
  `supWinProb`, `Adv⊥`, the T0 conditional layer).  FORBIDDEN: a second
  notion of system/game/equivalence/conditioning; new object stacks or
  operators copied from a source's own presentation (`S⁻`/`S⊣` as
  operators, Γ/Γᵇ, blinded-system objects); indiscriminate transcription.  NARROW CLARIFICATION
  (2026-08-19, earned by the blind-winning layer): CR18 Def 4.20's `b` is NOT
  a blinded-system object — it is an ordinary attachment engine (forward the
  query, answer a constant, refusals included), so building it breaks nothing.
  This settles `b` ONLY; whether a PDG assembled from landed pieces (product
  law + `comap`-transported condition, e.g. `enhance`) is admissible is
  recorded as a coordinator ruling at LEDGER's F-8 entry, pending Marc.
  If a concept genuinely seems to need a NEW object, that is a fork to
  Marc, not a build.
  **Clause (b) — minimal migration, no wheel-reinvention (Marc, same
  ruling):** the dual guard.  When the concept is already available AND
  PROVEN — in the source theory or in the reference repository's
  kernel-checked development — ADAPT that artifact: keep its statement
  shapes, lemma decomposition, and proof architecture, and change only
  what clause (a)'s recast dictionary forces (carrier/observable
  substitution).  Deriving a fresh route where a proven one adapts is the
  proof-side twin of parallel modeling: two developments of one theory.
  (No blind transcription either — carriers differ, so every node is
  re-elaborated on our objects; "adapt" means the DAG transports, not the
  text.)  Worked instance, LANDED at T3 (b82f449, adversarially audited):
  CE = TWO new Props over landed objects (`CondEquiv` and
  `EquivalentAsGames` — the audit corrected the predicted "one relation")
  on the not-won restriction of `gameTrLaw` vs `trLawFullyDefined`, in
  Maurer13b Def 13's OWN printed division-free product form (p. 3153);
  the reference repository's proven DAG transported with three nodes
  collapsing on this carrier (monotone bridge, totality, gameEnhance);
  see LEDGER CR18 RECAST POLICY CE rows + the audited T1.8 record.
- CE sources (RESOLVED 2026-08-18, Marc: "already accounted for in the
  CR18 migration"): NO separate admission — the T3 charter (LEDGER
  SOURCE-IDENTITY CORRECTION) already assigns the presentations: thesis
  Ch. 2 §2.3.3/§2.4.3 in-hierarchy where it covers the ground; Maurer02
  §4 / MPR07 / Maurer13b as the verified original papers (cite paper +
  printed page, never bare numbers — the charter's trap list is binding);
  CR18 §4.10–4.11 numbering as historical provenance in docstrings only.
  Consistent with the standing T4 MPR07 leg, which never had an
  admission gate.  The former PENDING line was an escalation-filter
  miss: it re-asked what the charter had settled.

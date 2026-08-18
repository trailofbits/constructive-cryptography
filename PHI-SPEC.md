# PHI-SPEC — the rulings register

The working spec of the MR16/CC formalization.  Validation state lives in
`LEDGER.md` (four-gate `scripts/ledgerAudit.sh`); the full design
archaeology (contracts, pipelines, refutations, closeouts) lives in the git
history on branch `archive/pre-squash-2026-08-18`.

## Sources (R8)
Primary, in order: **MauRen16, Jost thesis, LiuMau20, Lanzenberger thesis**.
CR18 is fallback-only (register in LEDGER.md top); MauRen11 is behind the
provenance fence pending an explicit reconciliation.

## Carrier (R1–R3)
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
MR16 basics-done: **YES** — census 44/48 D+I counted from the matrix
cells; residue by design (G10 fenced rows 13/48, §3.5 models row 32
optional, prose row 31).  Lanzenberger pure-RS scope complete (L4 games +
L5 amplification deferred by scope ruling).  Deferred queues and open
micro-questions: see LEDGER.md.

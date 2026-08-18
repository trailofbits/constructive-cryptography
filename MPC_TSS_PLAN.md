# MPC and FROST: active remaining work

This file contains only unresolved work. General AC usage belongs in
`LIBRARY_GUIDE.md`; contributor rules belong in `AGENTS.md`.

## Target

Connect the existing abstract multiparty/FROST statements to a concrete,
source-faithful random-system carrier and a checked OMDL/AOMDL security
reduction.

The intended layer path is

```text
AbstractCryptography
    ↓
ConstructiveCryptography
    ↓
ConstructiveCryptography.MultipartyComputation
    ↓
RandomSystemsCC fixed/typed signatures
    ↓
Applications.Frost
```

Primary sources are MauRen11 Theorem 2 (MR11-DEFERRED — see LEDGER PROVENANCE
FENCE: cite it, but state the plan's constructions over the MR16-track
surface; the fenced modules are for the reconciliation task), LiuMau20, RFC
9591, and the selected
FROST/threshold-signature security papers cited in `Applications/Frost.lean`.
Use the PDFs, not this plan, to settle theorem hypotheses.

## Scope: assume a broadcast channel (match the FROST papers)

A **broadcast channel `BC` (and authenticated channels) are assumed base
resources**; constructing them is **out of scope**.  This is the exact
assumption level of the source papers — RFC 9591, Komlo–Goldberg, and
BCKMTZ22 are static-corruption `t`-out-of-`n` statements that assume `BC`
and never build it.  Consequently:

* the construction ladder is only the DKG and signing rungs,
  `[NET, BC, RO, COIN] —[π_dkg]→ KEYS∗Z —[π_sign]→ TSS∗Z`;
* LiuMau20's `Q³` / honest-majority regime is **not** required — it is the
  hypothesis a broadcast *construction* would need, and that step is out of
  scope.  The headline is `frost_threshold_unforgeability` (no `Q³`,
  dishonest majority tolerated); `frost_threshold` (with `Q³`) is retained
  only as the abstract hook for a future, out-of-scope broadcast
  de-idealization and is not a FROST deliverable;
* the authentication and broadcast rungs (A, B) named in earlier drafts are
  dropped from the remaining work; `BC` and per-pair channels stay inside
  the assumed `Frost.Model` `.assumed` bundle.

## Existing interfaces to reuse

- `AbstractCryptography.Multiparty`: `ConstructsForAll`, `zSub`, `zStar`,
  `AdversaryStructure`, `Q3`, `threshold`, `gameSpec`, gate hierarchies, and
  the generic MPC composition step.
- `ConstructiveCryptography`: fixed-dishonest-set availability/security and
  exact, serial, parallel, and context composition.
- `Applications.Frost`: the RFC 9591 functional algebra and abstract
  construction statements.
- `RandomSystemsCC`: fixed-signature and typed-signature serial integration
  surfaces.

These are inputs to the remaining work, not evidence that the concrete
security theorem is finished.

## The frozen ConstructiveCryptography.MultipartyComputation contract (decided)

These four decisions are final; the Lean receipts live in
`AbstractCryptography/Multiparty.lean` unless noted.

### Simulator quantifier order: per-`(Z, R)` existential

The public predicate is LiuMau20's — the simulator is chosen after the
dishonest set and the assumed resource.  The MauRen11 Theorem 2
shared-tuple order is a *strictly stronger* premise: shared ⟹ per-pattern
is `leaf_of_shared_simulator`; the converse is refuted by the inline
negative example after it.  A statement needing the shared order must
take the tuple `σ` explicitly.

### Joint dishonest action: `zSub tupleGamma`, correlation via the ideal

For finite dishonest sets the generated class is exactly the
`Z`-supported tuples (`zSub_tupleGamma_eq_supportedOn`), so the tuple
algebra is as expressive as it can be.  What the tuple monoid cannot
express is one machine with state shared across the interfaces of `Z`;
in the carrier such correlation must flow through the resource.  Design
consequence for the leaves: the ideal resources (KEYS, TSS) must expose
per-party dishonest capabilities rich enough that per-interface simulator
converters suffice.  A merged-interface converter carrier is deliberately
not introduced; revisit only if a specific leaf proof fails for this
reason.

### Parallel shape: not needed — monolithic assumed resource

The FROST assembly (`frost_instantiated`) never uses `Par`.  The assumed
`[NET, BC, RO, COIN]` specification is modeled as one typed resource whose
interface type is structured (party × subchannel through the
`SignatureUniverse` codes).  The binary-fold versus flat-tuple choice is
deferred until a theorem actually composes parallel resources.

### Game meaning: win-probability tests over flattened laws

A `gameSpec` test is the win-probability functional of a forgery
distinguisher (`DDD`) against the resource's flattened global laws.  The
bridge is the RS repo's Theorem 4.17
(`advantage_le_maxWinProb_of_condEquiv`) with `RelateGameDistinguishing`
and `TypedFramingAdvantage`.  The ideal TSS is the **gated real signer**:
it runs the genuine signing algebra and its guarantee is the gate (it
signs only quorum-approved messages); validity stays public algebra.  Its
game bound `ε_game` is therefore the standard game-based FROST
unforgeability statement (BCKMTZ22/CGRS23 shape) — the single
computational leaf — discharged by the carrier reduction to OMDL/AOMDL
through `IsCostedReduction`, with the signing-simulator leg statistical.
(A repository-style ideal with `ε_game = 0` was considered and rejected:
it forces the signing simulator to be computational — a rushing adversary
fixes its commitments after the ideal has fixed `R`.)  The intermediate
KEYS ideal starts **uniform-key**; the Pedersen/GJKR bias is to appear as
a machine-checked impossibility for that ideal (no simulator closer than
≈ 1/2), and only then is the bias-absorbing KEYS introduced as the
repair the impossibility forces.  The exact event, budget, solver map,
and cost map are fixed when the carrier games land (work package 3).

Threshold headline: FROST unforgeability tolerates a dishonest majority —
`frost_threshold_unforgeability` (no `Q³`); `frost_threshold` keeps `Q³`
for composing with a future broadcast de-idealization.

## Status: assembled, modular, three named leaves remain

The abstract layers, the flip to a carrier-free `abstract-crypto`, the
concrete signature model, the modular security assembly, the AOMDL
reduction contract, and the DKG-bias impossibility are done and
axiom-clean (`propext`/`Classical.choice`/`Quot.sound` only).  The
concrete side lives in `random-systems` under `RandomSystemsCC.Frost`:

- `Frost.Model` — the concrete signature universe (one interface per
  party; `.assumed` bundle, uniform-key `.keys`, gated-signer `.tss`).
- `Frost.EndToEnd` — the `Setup` structure (fixed carrier data bundled
  once), the three leaf predicates `DkgLeaf`/`SignLeaf`/`GameLeaf`, the
  two reusable stage constructions `dkgStage`/`signStage`, and
  `Setup.secure` + availability.
- `Frost.Reduction` — `gameBound_of_reduction`, the `AomdlHard` /
  `AomdlReduction` contracts, `gameLeaf_of_aomdl`, and
  `Setup.secure_of_aomdl` (only cryptographic inputs: two statistical
  simulators + AOMDL hardness + reduction soundness).
- `Frost.DkgImpossibility` — `uniform_key_dkg_impossible`
  (Gennaro–Jarecki–Krawczyk–Rabin, machine-checked).

### The three leaves: deterministic cores proven, couplings residual

Each leaf now splits into a machine-checked deterministic core and one
named probabilistic residual (the pattern established by the AOMDL
reduction and mirrored for the DKG simulator).

1. **AOMDL reduction (item 3).**  *Done:* the extraction algebra
   (`schnorr_extract`, `frost_share_extract`, carrier-free); AOMDL as a
   genuine CR18 `Problem` over distributions (`aomdlProblem`, solver =
   `Dist (Option (ZMod q))`, performance = winning probability via
   `Dist.mass`); the reduction as a distribution map (`reduce`) with
   `reduction_winProb` proving it *tight* (reduced-solver winning
   probability = forger's fork-production probability, since extraction
   never fails).  The two reduction notions are linked by a checked
   declaration: `gameBound_of_aomdl` (`ReductionLink`) instantiates
   `gameBound_of_reduction`'s abstract advantage slot with the concrete
   AOMDL `Problem` performance, producing the `gameSpec` game leaf from
   the actual `Problem` reduction.  *Residual:* the forking lemma
   (`ForkingLemma` contract) — the rewinding success bound over
   `PFunPDS` — and the flattening `forkerOf` (forgery test ↦ forker over
   `FrostGroup`), which needs the concrete `.tss` resource.  `AomdlHard`
   stays the sole bounded-advantage hardness assumption.

2. **Bias-absorbing key ideal + DKG simulator (item 1).**  *Done:* the
   uniform-key impossibility (`uniform_key_dkg_impossible`) forcing the
   repair; the bias-absorption algebra (`key_bias_decomposition`,
   `key_bias_absorb`, carrier-free) and the simulator key-programming core
   over `FrostGroup` (`dkgHonestContribution`, `key_matches`,
   `key_programming_injective`); and the **key ideal's cryptographic core
   as a genuine carrier resource** (`Frost.KeyResource`: `keyResource` a
   `Phi`, a uniform Shamir sharing with per-party shares / group key /
   public-key shares, VSS consistency `keyAnswer_vss`, group-key/constant
   relation `keyAnswer_groupKey`, and quorum reconstruction
   `key_reconstruct` via the proven `shamir_reconstruct_smul`).  *Residual:*
   the adversarial bias arm + signing-channel bundling to make this the
   full `Setup.keys`; the RO-programming coupling
   (`DkgIndistinguishable` contract) giving `εDkg = 0`; the `Setup.DkgLeaf`
   discharge.  `Z = ∅` availability via `verify_aggregate_dkg`.

3. **The signing leaf (item 2, not yet started).**  Define `.tss` as the
   gated real signer as a `DependentPDS` law; prove `SignLeaf` with
   small/zero `εSign` (the ideal's transcripts are real-shaped;
   deterministic core `verify_aggregate`).

A pure-RS prerequisite for the concrete `.keys`/`.tss` laws: the
multi-interface arbitrary-stateful attach-behavior lemmas (the
`Unit`-interface coherence `attachAt_unit_eq_toUnitResource_apply` exists;
the `Fin n` version is new and everything downstream reasons through it).

## Completion criteria

The work is complete only when:

- the three leaves above are proved without `sorry` (AOMDL hardness the
  sole remaining bounded-advantage assumption);
- the final theorem consumes them through `Setup.secure_of_aomdl`;
- the pure RS root remains independent;
- generic proofs do not enumerate `Fin n` or raise heartbeat limits.

Delete this file when those conditions hold. Move lasting usage lessons to
`LIBRARY_GUIDE.md` or `AGENTS.md` rather than appending a completion log.

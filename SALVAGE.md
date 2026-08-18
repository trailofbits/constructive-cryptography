# SALVAGE

Notes on content deleted from the build, kept because it is worth re-deriving
later on the unbundled foundation. Not a changelog: only the pieces with
mathematical content that has no counterpart in the surviving tree.

## The bundled `CCAlgebra` cluster (deleted 2026-08-13)

Recover from commit `664dc51` (`git show 664dc51:<path>`):

| path | lines |
| --- | --- |
| `AbstractCryptography/Algebra/Bundled.lean` | 327 |
| `AbstractCryptography/Algebra/Composition.lean` | 1083 |
| `AbstractCryptography/Algebra/Bridge.lean` | 177 |
| `AbstractCryptography/Algebra/SpecBridge.lean` | 138 |
| `ConstructiveCryptography/Multiparty/TwoParty.lean` | 602 |

`structure CCAlgebra (I : Type*)` bundled the carrier, the converter space, the
distance and the MauRen11 Definition 14 axioms as fields. It was removed
because:

* the five files formed a closed loop — nothing outside them imported any of
  them except the two aggregator roots `AbstractCryptography.lean` and
  `ConstructiveCryptography.lean`;
* its `dist : Resource → Resource → NNReal` cannot express `⊤`, which the rest
  of the tree uses for "no bound" / the vacuous distinguisher class. The live
  algebra (`AbstractCryptography/Algebra/Attachment.lean` plus the `Metric` layer) uses
  Mathlib `PseudoEMetricSpace`/`edist` in `ℝ≥0∞`;
* `AbstractCryptography/Algebra/SpecBridge.lean` imported
  `ConstructiveCryptography.Multiparty.TwoParty`, so the abstract layer depended on
  the CC layer, inverting the tower.

Two pieces are worth porting. They were not ported now because each is a real
re-derivation on a different foundation, not a mechanical rewrite: the bundled
statements are phrased in terms of `A.dist`, `A.Attached i`, and the
per-interface `apply`, whereas the unbundled surface has a tuple `MulAction` of
`∀ i, Γ i` on `Φ` with `edist` in `ℝ≥0∞`, and the two-party interface set has no
bundled `CCAlgebra ABE` to hang the statements on.

### 1. Simulators absorbed into `*`-relaxations

`AbstractCryptography/Algebra/SpecBridge.lean` re-expressed bundled metric witnesses
as JM20 specification statements `ℛ —[π]→ 𝒮` over `Set A.Resource`, with the
errors as `Relaxation.epsilonRelaxation` and **the simulator absorbed into a
`Relaxation.star` at the adversary interface**, so they compose by
`Constructs.epsilonRelaxation_trans` (JM20 Cor. 1) instead of bespoke
`serial_composition` lemmas. The working monoid was
`nonexpandingEnd A.Resource`.

Declarations: `CCAlgebra.attachedNE`, `CCAlgebra.neMonoidAt`,
`CCAlgebra.LocalConstruction.toConstructs` (`d(π^i R, S) ≤ ε` becomes
`{R} —[π]→ (S)^ε`), `CCAlgebra.TargetConstruction.toConstructs` (the MR16
Lemma 5 shape: `{R} —[1]→ ((S)^{*_i})^ε`),
`ABE.SecureConstruction.toConstructs`, and `CCAlgebra.localConstruction_chain`
(constructions chain across *different* interfaces with additive error).

The unbundled side already has the pieces this was built from:
`AbstractCryptography.constructs_of_simulator`, `Relaxation.star`,
`Relaxation.epsilonRelaxation`, `Constructs.epsilonRelaxation_trans`, and `nonexpandingEnd`, all in
`AbstractCryptography/Algebra/Star.lean` and `AbstractCryptography/Specification/`. What is
missing is the statement that a *simulator-carrying* construction over the
selected `MulAction` surface is a `star`-relaxed construction, stated directly
rather than through a bundled algebra.

### 2. MauRen11 Appendix C — the two-party statement

`ConstructiveCryptography/Multiparty/TwoParty.lean` fixed the interface set
`ABE = {A, B, E}` and stated:

* `FourConditionConstruction` — Appendix C.1 eq. (5), the four-condition
  two-party construction (both honest / Alice honest / Bob honest / both
  dishonest), each with its own error, plus `maxError`;
* `SecureConstruction` — Maurer 2011 §5.1 Def. 3: the availability
  (`d(π_A π_B ⊥^E R, ⊥^E S) ≤ ε_avail`) and security
  (`d(π_A π_B R, σ^E S) ≤ ε_sec`) package, with `SecureConstruction.compose`
  giving the §5.2 Theorem 1 serial composition with additive errors, and the
  support lemmas `availability_from_nonexpansive` and `security_triangle`;
* `Protocol` / `Protocol.comp` / `Protocol.applyTo` — the Alice-Bob converter
  pair and its bookkeeping.

Not lost, despite the file's headline: the Appendix C.3 impossibility results.
The file's own honesty notes (dated 2026-07-03) record that its `PlainChannel`
imposes no condition and that `impossibility_self` /`impossibility_self_equiv`
are near-definitional, and point at the faithful Definition 20 and Theorem 4 —
`AbstractCryptography.TwoParty.IsPlainChannel` and
`AbstractCryptography.TwoParty.not_abstraction_plainChannel`, both live in
`AbstractCryptography/Specification/TwoParty.lean` (split out of
`Specification/Filtered.lean` on 2026-08-17; MR11-DEFERRED — see LEDGER
PROVENANCE FENCE), along with the quantitative
variant `not_abstraction_plainChannel_quantitative`. Likewise the Appendix D
`Indifferentiable` structure and its two lemmas are superseded by
`AbstractCryptography.Indifferentiable` in `AbstractCryptography/Algebra/Star.lean`
(Definition 23 plus MauRen16 Lemma 5, with `Indifferentiable.construct` and
`Indifferentiable.trans`).

So the port to write is the four-condition statement and the
availability/security package over the unbundled surface — the Appendix C
impossibility half is already there.  That port is Appendix C content and
therefore lands behind the fence (MR11-DEFERRED — see LEDGER PROVENANCE
FENCE): write it into `AbstractCryptography/Specification/TwoParty.lean` and
add nothing MR16-track that imports it.

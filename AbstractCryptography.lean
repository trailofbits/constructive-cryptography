/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography.Refinement.Basic
import AbstractCryptography.Refinement.StepwiseRefinement
import AbstractCryptography.Algebra.Attachment
import AbstractCryptography.Algebra.Indexed
import AbstractCryptography.Algebra.Star
import AbstractCryptography.Specification.Basic
import AbstractCryptography.Specification.Parallel
import AbstractCryptography.Specification.Relaxation
import AbstractCryptography.Metric.Epsilon
import AbstractCryptography.Metric.Distinguisher
import AbstractCryptography.Specification.Filtered
import AbstractCryptography.Specification.ChoiceSetting
import AbstractCryptography.Tactics.ProofAutomation
import AbstractCryptography.Tactics.ControlledNaturalLanguage

/-!
# Abstract Cryptography

MauRen11 §1.5 places this library at **Level 1**: "the most general
notion of a *system* and of the *composition* of systems.  The
composition laws are described by simple algebraic rules."

§1.5's inheritance principle is the whole formalization program in one
sentence: definitions and theorems are inherited by lower levels
*provided the lower levels satisfy the postulated axioms*.  Nothing here
mentions a carrier.  The random-systems carrier (the paper's Level 2 —
"the most general notion of a *discrete* system … an extension of
Maurer's random system framework for single-interface systems to
multiple-interface systems and to the composition of systems") lives in
the separate `random-systems` repository; that repository keeps the pure
`RandomSystems` root separate from its non-default `RandomSystemsCC`
integration target, whose modules may consume the narrowest public theory
surface each instantiation needs (`AbstractCryptography`, `ConstructiveCryptography`,
or `ConstructiveCryptography.MultipartyComputation`).

Four semantic AC layers — `Refinement`, `Algebra`, `Specification`, `Metric` —
divide the paper-facing responsibilities as follows; two further root imports
provide deterministic proof frontends over that semantic surface, and they now
sit outside the mathematics tree, under `AbstractCryptography.Tactics`:

* `AbstractCryptography.Refinement.Basic` — §3: Definition 5 (component and
  constructor sets), Definition 6 (reductions `R —α→ S`), Definition 7
  (serially composable, context-insensitive, generally composable).
* `AbstractCryptography.Refinement.StepwiseRefinement` — App. A's Definition 19 and
  Theorem 3 via the law-free derived-chain forward
  theorem `soundForDerivedChainStepwiseRefinement_of_isGenerallyComposable`
  and, under the two serial unit laws, the exact repaired child-parallel
  characterization
  `isGenerallyComposable_and_red_par_par_iff_soundForChildParallelStepwiseRefinement`.
* `AbstractCryptography.Algebra.Attachment` — §6's selected equality-level
  `Monoid`/`MulAction` rendering of converter composition and attachment,
  together with independent parallel and pseudo-emetric non-expansion mixins.
* `AbstractCryptography.Algebra.Indexed` — the same treatment for the index-varying
  layer Definition 14 leaves implicit (fn. 20; MMPRT18 Definition 3.1): the
  algebraic mixin `IndexedPar` over a type family `Res : Type u → Type v`, and
  the separate metric mixin `IsNonexpandingIndexedPar` over one Mathlib
  `PseudoEMetricSpace` per fibre.  It has no instances yet.
* `AbstractCryptography.Specification.Basic` and `AbstractCryptography.Specification.Parallel`
  — JM20 Definition 1 / CR18 Definition 5.4,
  `Constructs π R S :⇔ π • R ⊆ S`, and its composability laws.
* `AbstractCryptography.Specification.Relaxation`, `AbstractCryptography.Metric.Epsilon`, and
  `AbstractCryptography.Algebra.Star` — CR18/JM20 relaxations, pseudo-emetric balls,
  star relaxation, simulator construction, and indifferentiability.
* `AbstractCryptography.Metric.Distinguisher` — selected distinguisher classes and the
  induced pseudo-emetric/non-expanding action.
* `AbstractCryptography.Specification.Filtered` — choice-free endpoint-pattern/star
  specifications and local-simulator construction analogues motivated by §7.
  This module also contains App. C's two-party case.
* `AbstractCryptography.Specification.ChoiceSetting` — MauRen11's literal
  choice-setting layer
  (§§4–5, 7): Definitions 8–11 and 18 in the §7.1 converter specialization,
  and Theorem 2 (`filteredAbstraction_of_local_simulators`) — local ongoing
  simulation proves the choice-domain/CFR abstraction `R_φ ⊑^π S_ψ` — on the
  same selected `Monoid`/`MulAction` contract as the rest of the surface.
* `AbstractCryptography.Tactics.ProofAutomation` — a finite proof-language layer over
  the semantic modules: scoped paper notation, curated normalization, named leaf
  rules,
  and explicit construction assemblers. It adds no construction semantics and
  imports no CC, MPC, RS, EventAlgebra, application, widget, or compatibility
  module.
* `AbstractCryptography.Tactics.ControlledNaturalLanguage` — a separately scoped,
  paper-readable syntax layer over those same deterministic assemblers.
  Downstream CC and RS modules may extend its neutral language scope without
  adding concrete vocabulary to AC.

The systematic public setup is:

```lean
import AbstractCryptography
open AbstractCryptography
open scoped AbstractCryptography
```

This makes both the scoped notation and the `ac_*` proof commands available.
A narrow file may instead import `AbstractCryptography.Tactics.ProofAutomation` with
the same two `open` commands.

Controlled-language sentences are opt-in even through the public root:

```lean
open scoped CryptoControlledNaturalLanguage
```

The `ConstructiveCryptography` module is the next layer and the public root of
its own tree. `ConstructiveCryptography.Multiparty.Basic` is owned by the
separate `ConstructiveCryptographyMultipartyComputation` target. The obsolete
raw modulo-`Equiv` compatibility rendering has been deleted; the RS integration
must instantiate this selected equality-level surface through its own
fixed-signature quotients.

The bundled `CCAlgebra` rendering (`Algebra.Bundled`, `Algebra.Composition`,
`Algebra.Bridge`, `Algebra.SpecBridge`, and `ConstructiveCryptography.Multiparty.TwoParty`)
was deleted on 2026-08-13; see `SALVAGE.md` for what it contained and where to
recover it. Its distance was `NNReal`-valued and so could not express `⊤`, and
`Algebra.SpecBridge` imported the CC layer from inside the abstract layer.

`AbstractCryptography.EventAlgebra` is **not a rung of this ladder.**  It is
GegMau26, an orthogonal axis: §1.4 says event algebras are "a priori
incomparable to the abstract theory of systems of [MauRen11]; the two
theories are compatible on a more concrete level (satisfying both sets
of axioms)."  A concrete interaction instantiates both.

The standards — FIPS 180-4, SEC 1 / SEC 2, and RFC 9591 — are in
`Applications`. SHA-256 and secp256k1 are standalone deterministic cores;
`Applications.Frost` imports
`ConstructiveCryptography.MultipartyComputation`, while `Applications.Sponge`
imports `AbstractCryptography.Algebra.Star`. Dependencies point from applications
into the theory layers, never back.

## Editorial note — §3 has one public rendering

This is not paper content. `AbstractCryptography.Refinement.Basic` renders Definition 6
through the `HasReduction` typeclass, `Reduces`, and the `—[π]→` notation;
Definition 7 is represented by `IsSeriallyComposable`,
`IsContextInsensitive`, and `IsGenerallyComposable`. The earlier disconnected
rendering and its consumer chain have been removed. Active action-based
consumers and the `CCDiagram` binding use this selected surface.
-/

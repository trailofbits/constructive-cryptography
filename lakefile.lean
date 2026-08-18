import Lake
open Lake DSL

package AbstractCryptography where
  buildDir := (get_config? verificationBuildDir).getD ".lake/build"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0"

/-- Presentation layer: the `CCDiagram` proof-widget engine
(`Rendering.CCWidget`) and its semantic-role bindings for the abstract
surface (`Rendering.Widget`).  The engine is theory-free — it imports only
ProofWidgets and matches goal heads by name — so both this package's
surfaces and the random-systems H-technique surface can import it without
pulling any theory or staged `sorry`.  It ends with a global
`show_panel_widgets`: importing it makes every downstream file
diagram-enabled with zero per-proof ceremony.  No mathematics lives here. -/
@[default_target]
lean_lib Rendering where
  globs := #[.submodules `Rendering]

/-- MauRen11's **Level 1**: "the most general notion of a *system* and of the
*composition* of systems" (§1.5).  Carrier-agnostic throughout; the Level-2
random-systems carrier lives in the sibling `random-systems` repository.

The public root owns the carrier-agnostic semantic layers `Refinement`,
`Algebra`, `Specification`, and `Metric`, plus the
theory-free-of-later-layers `Tactics.ProofAutomation` re-export. Automation
lives under `AbstractCryptography.Tactics`, never in the mathematics tree; the
`SemanticRegistry` attribute module stays at the root because it is metadata
tagged onto mathematical declarations. The bundled `CCAlgebra` rendering was
deleted 2026-08-13 — see `SALVAGE.md`. Later
targets own the CC specialization, the
`ConstructiveCryptography.MultipartyComputation` extension, and the orthogonal
EventAlgebra axis.

MauRen11 Definition 6 now has one public rendering: `HasReduction`, with
`IsSeriallyComposable`, `IsContextInsensitive`, and `IsGenerallyComposable`.
No raw bundled declaration is imported by this public target. -/
@[default_target]
lean_lib AbstractCryptography where
  globs := #[.one `AbstractCryptography]

/-- The quarantined MauRen11 surface (provenance fence, 2026-08-17).  The
working discipline is MR16-only until an explicit MR11 reconciliation, so the
public `AbstractCryptography` root imports none of these modules; this target
keeps them compiled and their mathematics green.  See `LEDGER.md` PROVENANCE
FENCE and the gate in `scripts/ledgerAudit.sh`. -/
@[default_target]
lean_lib AbstractCryptographyMR11 where
  globs := #[.one `AbstractCryptography.MR11]

/-- Public `ConstructiveCryptography.MultipartyComputation` layer: its root and
multiparty implementation module. The Lake target name omits the module-name
separator. -/
lean_lib ConstructiveCryptographyMultipartyComputation where
  globs := #[
    .one `ConstructiveCryptography.MultipartyComputation,
    .one `ConstructiveCryptography.Multiparty.Basic
  ]

/-- GegMau26's orthogonal EventAlgebra axis. It remains a default target,
preserving the coverage formerly supplied by the broad AC target. -/
@[default_target]
lean_lib EventAlgebra where
  globs := #[.one `AbstractCryptography.EventAlgebra]

/-- The standards, implemented: FIPS 180-4 (SHA-256), SEC 1 / SEC 2
(secp256k1), and RFC 9591 (FROST), together with FROST's Shamir/Lagrange
algebra and functional core.

Applications *of* the stack: the deterministic cores stand alone, but the
FROST layer additionally imports
`ConstructiveCryptography.MultipartyComputation` to state FROST as a two-stage
construction (`Frost.lean`'s `frost_end_to_end`).
`AbstractCryptography` does not import this library — the dependency is one-way,
applications on top of the abstraction. -/
@[default_target]
lean_lib Applications where
  globs := #[.andSubmodules `Applications]

/-- Abstract, choice-free public-surface smoke test. Non-default and kept out
of the library root; its sole example imports only `AbstractCryptography` and uses no
concrete or finite interface carrier. -/
lean_lib AbstractCryptographySelectedSurfaceTests where
  globs := #[.one `AbstractCryptographySelectedSurfaceTests]

/-- Non-default checked examples for the scoped AC paper notation and proof
automation.  It remains outside the public root and concrete carriers. -/
lean_lib AbstractCryptographyProofAutomationTests where
  globs := #[.one `AbstractCryptographyProofAutomationTests]

/-- Non-default usability gate for Jost's §4.2 context-restricted
constructions: the collapse to the ordinary notion at `𝒞_id`, the closure of a
context set, and both composition rules firing on the smallest non-trivial
context sets.  Carrier-agnostic, so it stays out of the public root. -/
lean_lib AbstractCryptographyContextRestrictedTests where
  globs := #[.one `AbstractCryptographyContextRestrictedTests]

/-- Non-default non-vacuity witness for the distinguisher-indexed
`ε`-relaxation (Jost Def. 2.2.9): the smallest distinguisher class whose
indexed budget is matched by no scalar radius.  It is the only module in the
package that fixes a concrete carrier, so it stays out of the public root. -/
lean_lib AbstractCryptographyIndexedRelaxationTests where
  globs := #[.one `AbstractCryptographyIndexedRelaxationTests]

/-- Non-default positive, negative, and trace tests for the scoped controlled
natural-language frontend over the deterministic AC proof commands. -/
lean_lib AbstractCryptographyControlledNaturalLanguageTests where
  globs := #[.one `AbstractCryptographyControlledNaturalLanguageTests]

/-- Non-default audience demo: MauRen11's MAC-plus-encryption secure-channel
composition followed by the plain-channel impossibility calculation.  Build
with `lake build ConstructiveCryptographyDemo`. -/
lean_lib ConstructiveCryptographyDemo where
  globs := #[
    .one `ConstructiveCryptographyDemoSupport,
    .one `ConstructiveCryptographyDemo
  ]

/-- Non-default ordinary-value versus indexed-local-class experiment for a
typed two-step AC construction workflow. -/
lean_lib AbstractCryptographyConstructionWorkflowTests where
  globs := #[.one `AbstractCryptographyConstructionWorkflowTests]

/-- CC-shaped downstream smoke for the selected public AC root. Non-default;
the sole example imports `AbstractCryptography`, not the bundled CC implementation. -/
lean_lib ConstructiveCryptographySelectedSurfaceTests where
  globs := #[.one `ConstructiveCryptographySelectedSurfaceTests]

/-- SHA-256 known-answer tests. Non-default to keep executable KAT churn out
of the library build; the current vectors use axiom-free `decide +kernel`
(see `AGENTS.md`, "Performance and computability"). Build with
`lake build Sha256Tests`. -/
lean_lib Sha256Tests where
  globs := #[.one `Sha256Tests]

/-- RFC 9591 Appendix E.5 known-answer tests for FROST(secp256k1,
SHA-256).  Non-default like `Sha256Tests`; the point-arithmetic KATs
use `native_decide`.  Build with `lake build FrostRfc9591Tests`. -/
lean_lib FrostRfc9591Tests where
  globs := #[.one `FrostRfc9591Tests]

/-- The public Constructive Cryptography layer: the `ConstructiveCryptography`
root — a stable entry point that is also the root of the module tree beneath it
— together with Jost's context-restricted generalization and the multiparty
layer.  The bundled `CCAlgebra` rendering and its bridges were deleted
2026-08-13 (see `SALVAGE.md`); what is left is reached independently by the
`AbstractCryptography` and `ConstructiveCryptographyMultipartyComputation` targets,
and this target keeps the tree covered under its own root. -/
@[default_target]
lean_lib ConstructiveCryptography where
  globs := #[.andSubmodules `ConstructiveCryptography]

/-- Finitely supported distributions, expectation, statistical distance,
couplings and universal hashing.  Independent of any system model. -/
@[default_target]
lean_lib Probability where
  globs := #[.andSubmodules `Probability]

/-- Maurer's random systems: discrete systems, converters, the distinguishing
metric and the proof techniques.  Depends on `Probability`, not on the
abstract layer. -/
@[default_target]
lean_lib RandomSystems where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystems]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[.submodules `RandomSystems]

/-- The tower at one carrier: every abstract-layer join stated as an
`example` on the one concrete `Φ`.  If a refactor disconnects a layer,
this target stops compiling. -/
@[default_target]
lean_lib RandomSystemsReceipts where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystemsReceipts]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[]

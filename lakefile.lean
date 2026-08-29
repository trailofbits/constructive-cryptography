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
surface (`Rendering.Widget`).  The engine is theory-free: it imports only
ProofWidgets and matches goal heads by name, so semantic libraries may use it
without importing one another.  It ends with a global
`show_panel_widgets`: importing it makes every downstream file
diagram-enabled with zero per-proof ceremony.  No mathematics lives here. -/
@[default_target]
lean_lib Rendering where
  globs := #[.submodules `Rendering]

/-- The carrier-independent MR16-track theory.  Its public root exports the
single typed `ResourceAlgebra` presentation, specifications, exact and
approximate constructions, ordered parallel composition, relaxations, and
deterministic proof-language frontends.  It imports no concrete Random Systems
carrier; that instantiation belongs to `RandomSystemsCC`. -/
@[default_target]
lean_lib AbstractCryptography where
  globs := #[.one `AbstractCryptography]

/-- Public `ConstructiveCryptography.MultipartyComputation` layer: its root and
multiparty implementation module. The Lake target name omits the module-name
separator. -/
lean_lib ConstructiveCryptographyMultipartyComputation where
  globs := #[
    .one `ConstructiveCryptography.MultipartyComputation,
    .one `ConstructiveCryptography.Multiparty.Basic
  ]

/-- GegMau26's orthogonal EventAlgebra axis, exposed as a separate default
target. -/
@[default_target]
lean_lib EventAlgebra where
  globs := #[.one `AbstractCryptography.EventAlgebra]

/-- The standards, implemented: FIPS 180-4 (SHA-256), SEC 1 / SEC 2
(secp256k1), and RFC 9591 (FROST), together with FROST's Shamir/Lagrange
algebra and functional core.

Applications *of* the stack: the deterministic cores stand alone, but the
FROST layer additionally imports
`ConstructiveCryptography.MultipartyComputation` to state FROST as a two-stage
construction (`Applications.Frost.Construction`).
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

/-- Non-default firing evidence for the construction layer's `Trans`
instances: every paper composition that `calc` can carry, written as a single
calculation.  Carrier-agnostic, so it stays out of the public root. -/
lean_lib AbstractCryptographyCalcChainTests where
  globs := #[.one `AbstractCryptographyCalcChainTests]

/-- Non-default positive, negative, and trace tests for the scoped controlled
natural-language frontend over the deterministic AC proof commands. -/
lean_lib AbstractCryptographyControlledNaturalLanguageTests where
  globs := #[.one `AbstractCryptographyControlledNaturalLanguageTests]

/-- Non-default regression tests for ordinary-value and indexed-local-class
forms of a typed two-stage AC construction. -/
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

/-- The Constructive Cryptography module tree over the single
`ResourceAlgebra` presentation. -/
@[default_target]
lean_lib ConstructiveCryptography where
  globs := #[.andSubmodules `ConstructiveCryptography]

/-- Finitely supported distributions, expectation, statistical distance,
couplings and universal hashing.  Independent of any system model. -/
@[default_target]
lean_lib Probability where
  globs := #[.andSubmodules `Probability]

/-- The fixed-interface Random Systems library. Its public root contains DDS,
DDE, PDS, observation, distance, ordered parallel composition, and the partial
H-coefficient bounds. It depends on `Probability`, not on AC or CC. -/
@[default_target]
lean_lib RandomSystems where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystems]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[.one `RandomSystems]

/-- Optional functional DDC extension of the fixed-interface Random Systems
library. -/
lean_lib RandomSystemsConverter where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      `RandomSystems.Converter,
      `RandomSystems.Converter.Checks
    ]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      .one `RandomSystems.Converter,
      .one `RandomSystems.Converter.Checks
    ]

/-- Abstract-Cryptography adapter for the selected query-indexed random-system
carrier. -/
lean_lib RandomSystemsCC where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      `RandomSystemsCC,
      `RandomSystemsCC.Checks
    ]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      .one `RandomSystemsCC,
      .one `RandomSystemsCC.Checks,
      .one `RandomSystemsCC.ResourceAlgebra
    ]

/-- Cross-layer tests that instantiate Maurer-style abstract declarations on
one concrete Random Systems carrier. -/
@[default_target]
lean_lib RandomSystemsCCInstantiationTests where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystemsCC.InstantiationTests]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[.one `RandomSystemsCC.InstantiationTests]

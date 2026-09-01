import Lake
open Lake DSL

package ConstructiveCryptography where
  buildDir := (get_config? verificationBuildDir).getD ".lake/build"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

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

/-- Public `ConstructiveCryptography.MultipartyComputation` layer: its root and
multiparty implementation module. The Lake target name omits the module-name
separator. -/
lean_lib ConstructiveCryptographyMultipartyComputation where
  globs := #[
    .one `ConstructiveCryptography.MultipartyComputation,
    .one `ConstructiveCryptography.Multiparty.Basic
  ]

/-- Tests for the Constructive Cryptography resource algebra, construction
calculus, proof language, and multiparty surfaces. -/
lean_lib ConstructiveCryptographyTests where
  globs := #[
    .one `Tests.ConstructiveCryptography.ResourceAlgebra,
    .one `Tests.ConstructiveCryptography.ConstructionWorkflow,
    .one `Tests.ConstructiveCryptography.Tactics.ProofAutomation,
    .one `Tests.ConstructiveCryptography.Presentation.ControlledNaturalLanguage,
    .one `Tests.ConstructiveCryptography.Composition,
    .one `Tests.ConstructiveCryptography.SelectedSurface,
    .one `Tests.ConstructiveCryptography.MultipartyComputation
  ]

/-- The MR16/Jost/Liu Constructive Cryptography theory before selecting a
concrete system model.
Its public root exports the single typed `ResourceAlgebra`, specifications,
construction judgments, ordered parallel composition, relaxations, and the
deterministic proof language. It imports no concrete Random Systems carrier;
that instantiation belongs at the deferred adapter boundary. -/
@[default_target]
lean_lib ConstructiveCryptography where
  globs := #[.andSubmodules `ConstructiveCryptography]

/-- Finitely supported distributions, expectation, statistical distance,
couplings and universal hashing. Independent of any system model. -/
@[default_target]
lean_lib Probability where
  globs := #[.andSubmodules `Probability]

/-- The fixed-interface Random Systems library. Its public root contains DDS,
DDE, PDS, observation, distance, ordered parallel composition, exact
transcript factorization, and the partial H-coefficient bounds. It depends on
`Probability`, not on Constructive Cryptography. -/
@[default_target]
lean_lib RandomSystems where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystems]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[.one `RandomSystems]

/-- Optional query-indexed deterministic-converter extension of the
fixed-interface Random Systems library. -/
lean_lib RandomSystemsConverter where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[`RandomSystems.Converter]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[.one `RandomSystems.Converter]

/-- Tests for standalone Random Systems and its optional converter extension. -/
lean_lib RandomSystemsTests where
  roots :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      `Tests.RandomSystems.SelectedSurface,
      `Tests.RandomSystems.Converter.SelectedSurface
    ]
  globs :=
    if get_config? disableRandomSystems = some "true" then #[]
    else #[
      .one `Tests.RandomSystems.SelectedSurface,
      .one `Tests.RandomSystems.Converter.SelectedSurface
    ]

import Lake
open Lake DSL

package ConstructiveCryptography where
  srcDir := "src"
  buildDir := (get_config? focusedBuildDir).getD ".lake/build"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0"

/-- Finitely supported distributions, statistical distance, couplings,
expectation and counting. Independent of any system model. -/
@[default_target]
lean_lib Probability where
  globs := #[.andSubmodules `Probability]

/-- Random systems, deterministic and probabilistic converters, attachment,
parallel composition, distance and games; typed systems and typed converters on interfaces. -/
@[default_target]
lean_lib RandomSystems where
  globs := #[.andSubmodules `RandomSystems]

/-- Constructive Cryptography on the random-systems model, its categorical
packaging, and the substitution and DSL extensions. -/
@[default_target]
lean_lib ConstructiveCryptography where
  globs := #[.andSubmodules `ConstructiveCryptography]

/-- Common ideal systems, schemes and security definitions. -/
@[default_target]
lean_lib Commons where
  globs := #[.andSubmodules `Commons]

/-- Applications and examples. -/
@[default_target]
lean_lib Examples where
  globs := #[.andSubmodules `Examples]

/-- Axiom audits, counterexamples and frontend diagnostics. -/
@[default_target]
lean_lib Tests where
  globs := #[.andSubmodules `Tests]

input_file diagramStyles where
  path := "src" / "Rendering" / "cc-diagram.css"
  text := true

input_file diagramInspector where
  path := "src" / "Rendering" / "inspector.js"
  text := true

/-- Optional deterministic diagrams and static export for the Lean infoview. -/
lean_lib Rendering where
  globs := #[.andSubmodules `Rendering]
  needs := #[diagramStyles, diagramInspector]

input_file cadmoStyles where
  path := "src" / "Informalization" / "Render" / "cadmo-reader.css"
  text := true

input_file cadmoScript where
  path := "src" / "Informalization" / "Render" / "cadmo-reader.js"
  text := true

/-- Optional human-first informalization engine (Infoview, ETH CADMO HTML, Verso JSON). -/
lean_lib Informalization where
  globs := #[.andSubmodules `Informalization]
  needs := #[cadmoStyles, cadmoScript]

/-- Paper-centric formalizations written with the `Paper` register and `PaperProof` DSL. -/
lean_lib Paper where
  globs := #[.submodules `Paper]

/-- Standalone CLI exporting checked ETH CADMO HTML & Verso JSON for any declaration. -/
lean_exe informalize where
  root := `Informalization.CLI
  supportInterpreter := true

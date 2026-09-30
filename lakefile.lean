import Lake
open Lake DSL

package ConstructiveCryptography where
  srcDir := "src"
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.1"

/-- Finitely supported distributions, statistical distance, couplings,
expectation and counting. Independent of any system model. -/
@[default_target]
lean_lib Probability where
  globs := #[.andSubmodules `Probability]

/-- Random systems, deterministic and probabilistic converters, attachment,
parallel composition, distance and games. -/
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

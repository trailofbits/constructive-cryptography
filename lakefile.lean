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

/-- The abstract layer: the specification calculus and the resource algebra,
with the metric that connects them. -/
@[default_target]
lean_lib AbstractCryptography where
  globs := #[.one `AbstractCryptography]

/-- The constructive layer: protocols, multi-party constructions, and the
generalizations of the construction notion. -/
@[default_target]
lean_lib ConstructiveCryptography where
  globs := #[.andSubmodules `ConstructiveCryptography]

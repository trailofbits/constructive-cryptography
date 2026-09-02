import Lake
open System Lake DSL

-- The talk is a deliberately nested presentation project. It consumes the
-- informalizer's public document and renderer without importing either the
-- informalization backend or the downstream CBC proof into its Lean build.
require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git"@"f98ff4ba2e9951dc917c0c6cd6c7caa1dc577ab6"

package «informalization-slides» where
  version := v!"0.1.0"

lean_lib DraftTalk

@[default_target] lean_exe «swiss-crypto-day» where root := `MainDraftTalk

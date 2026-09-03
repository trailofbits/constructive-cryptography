import Lake

open Lake DSL

package CryptoLanguage where
  leanOptions := #[⟨`autoImplicit, false⟩]

/-- The library this project lives in: the parent directory of the checkout,
so the informalizer always builds against the commit it is committed with. -/
require ConstructiveCryptography from ".."

/-- The CBC consumer, from GitHub. Its public theorem is an integration
fixture for the shared Random Systems ontology plus the thin CBC vocabulary
extension. -/
require «cbc-mac-cc» from git
  "https://github.com/trailofbits/cbc-mac-cc" @ "main"

lean_lib LanguageDesign where
  globs := #[.andSubmodules `LanguageDesign]

/-- Closed-world checks for the normative language contract. This target is
independent of the optional Random Systems application adapters. -/
lean_lib LanguageDesignContractTests where
  srcDir := "tests"
  globs := #[.one `ContractTests]

lean_lib Verbose where
  globs := #[.andSubmodules `Verbose]

@[default_target]
lean_lib Informalization where
  globs := #[.andSubmodules `Informalization]

/-- The Apache-2.0 LeanTeX pretty-printer used as the exact-expression
fallback.  It intentionally remains a separate library. -/
lean_lib LeanTeX where
  globs := #[.andSubmodules `LeanTeX]
  leanOptions := #[⟨`autoImplicit, true⟩]

lean_exe informalize where
  root := `Informalization.CLI
  supportInterpreter := true

/-- Compile-time semantic registry and IR tests imported by the executable
test driver. -/
lean_lib InformalizationSemanticTests where
  srcDir := "tests"
  globs := #[
    .one `Tests.Semantics,
    .one `Tests.Symbols,
    .one `Tests.Canonical,
    .one `Tests.CBCSemantic,
    .one `Tests.EvidenceCompression,
    .one `Tests.ProofPlan,
    .one `Tests.Discourse,
    .one `Tests.LanguageDesign
  ]

/-- Integration checks against the real downstream CBC project. These are
kept separate from the closed synthetic fixtures, which intentionally define
mock declarations in production namespaces. -/
lean_lib CBCInformalizationIntegrationTests where
  srcDir := "tests"
  globs := #[
    .one `Tests.CBCFrontend,
    .one `Tests.CBCExternal,
    .one `Tests.CBCProofExpansion,
    .one `Tests.SemanticHtml
  ]

/-- Positive, negative, parser, trace, and complete-proof tests for the
author-facing controlled language. -/
lean_lib VerboseTests where
  srcDir := "tests"
  globs := #[
    .one `VerboseTests,
    .one `VerboseTests.Structural,
    .one `VerboseTests.Statements,
    .one `VerboseTests.AbstractCryptography,
    .one `VerboseTests.RandomSystems,
    .one `VerboseTests.Events,
    .one `VerboseTests.Switching,
    .one `VerboseTests.Rendering,
    .one `VerboseTests.Grammar,
    .one `VerboseTests.Notation,
    .one `VerboseTests.HCoefficient,
    .one `VerboseTests.ProofSpine,
    .one `VerboseTests.Routine,
    .one `VerboseTests.Corpus,
    .one `VerboseTests.SpecConformance
  ]

/-- Opt-in live common-domain carrier gate. It is separate from the fixed-
interface language suite so an in-progress upstream carrier rewrite cannot be
mistaken for a grammar regression. -/
lean_lib CommonDomainVerboseTests where
  srcDir := "tests"
  globs := #[.one `VerboseTests.CommonDomain]

/-- Opt-in live CBC gates. These deliberately remain outside the fixed
language suite because they track the evolving application boundary. -/
lean_lib CBCVerboseTests where
  srcDir := "tests"
  globs := #[
    .one `VerboseTests.CBCReachability,
    .one `VerboseTests.CBCSignatureManifest
  ]

lean_exe informalizationTests where
  srcDir := "tests"
  root := `Tests.Main
  supportInterpreter := true

/-- Opt-in source-aware extraction of the live CBC theorem. -/
lean_exe cbcExternalTests where
  srcDir := "tests"
  root := `Tests.CBCExternalMain
  supportInterpreter := true

/-- Full semantic and interactive-reader acceptance check against the live
CBC consumer. -/
lean_exe cbcIntegrationTests where
  srcDir := "tests"
  root := `Tests.CBCIntegrationMain
  supportInterpreter := true

/-- The library is the enclosing checkout; the CBC consumer is the git
dependency Lake materializes under the workspace's packages directory. -/
private def validateUpstream : IO UInt32 := do
  let upstream := ".."
  let cbcConsumer := ".lake/packages/cbc-mac-cc"
  let localToolchain ← IO.FS.readFile "lean-toolchain"
  let upstreamToolchain ← IO.FS.readFile s!"{upstream}/lean-toolchain"
  let cbcToolchain ← IO.FS.readFile s!"{cbcConsumer}/lean-toolchain"
  let localToolchain := localToolchain.trimAscii.toString
  let upstreamToolchain := upstreamToolchain.trimAscii.toString
  let cbcToolchain := cbcToolchain.trimAscii.toString
  if localToolchain != upstreamToolchain then
    IO.eprintln s!"Lean toolchain mismatch: this project uses {localToolchain}, but the enclosing constructive-cryptography checkout uses {upstreamToolchain}"
    return 1
  if localToolchain != cbcToolchain then
    IO.eprintln s!"Lean toolchain mismatch: this project uses {localToolchain}, but the cbc-mac-cc dependency uses {cbcToolchain}"
    return 1
  let rootResult ← IO.Process.output {
    cmd := "git"
    args := #["-C", upstream, "rev-parse", "--show-toplevel"]
  }
  if rootResult.exitCode != 0 then
    IO.eprintln rootResult.stderr
    return rootResult.exitCode
  let commitResult ← IO.Process.output {
    cmd := "git"
    args := #["-C", upstream, "rev-parse", "HEAD"]
  }
  if commitResult.exitCode != 0 then
    IO.eprintln commitResult.stderr
    return commitResult.exitCode
  let statusResult ← IO.Process.output {
    cmd := "git"
    args := #["-C", upstream, "status", "--porcelain"]
  }
  if statusResult.exitCode != 0 then
    IO.eprintln statusResult.stderr
    return statusResult.exitCode
  let state := if statusResult.stdout.trimAscii.isEmpty then "clean" else "dirty"
  IO.println s!"constructive-cryptography checkout: {rootResult.stdout.trimAscii}"
  IO.println s!"constructive-cryptography commit: {commitResult.stdout.trimAscii} ({state})"
  IO.println s!"cbc-mac-cc dependency: {cbcConsumer}"
  IO.println s!"shared Lean toolchain: {localToolchain}"
  return 0

script provenance do
  validateUpstream

script test do
  let provenanceResult ← validateUpstream
  if provenanceResult != 0 then return provenanceResult
  let contractResult ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "LanguageDesignContractTests"]
  } >>= (·.wait)
  if contractResult != 0 then return contractResult
  let verboseResult ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "VerboseTests"]
  } >>= (·.wait)
  if verboseResult != 0 then return verboseResult
  for negativeFixture in #[
      "tests/VerboseNegative/ScopeClosed.lean",
      "tests/VerboseNegative/Misspelled.lean",
      "tests/VerboseNegative/RewritingNotPublic.lean",
      "tests/VerboseNegative/ArbitraryFactNotPublic.lean",
      "tests/VerboseNegative/OldFactEnvelope.lean",
      "tests/VerboseNegative/OldNaturalBudget.lean",
      "tests/VerboseNegative/BackendActionForgery.lean"] do
    let negativeResult ← IO.Process.output {
      cmd := "lake"
      args := #["env", "lean", negativeFixture]
    }
    if negativeResult.exitCode == 0 then
      IO.eprintln s!"negative grammar fixture unexpectedly compiled: {negativeFixture}"
      return 1
  let result ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "informalizationTests"]
  } >>= (·.wait)
  if result != 0 then return result
  let cbcResult ← IO.Process.spawn {
    cmd := "lake"
    args := #["exe", "cbcIntegrationTests"]
  } >>= (·.wait)
  if cbcResult != 0 then return cbcResult
  let forbidden ← IO.Process.output {
    cmd := "rg"
    args := #[
      "--line-number",
      "h_ideal|h_real|userName.*Bad|kind := `List",
      "Informalization",
      "LeanTeX",
      "--glob",
      "*.lean"
    ]
  }
  if forbidden.exitCode == 0 then
    IO.eprintln "forbidden output-driven informalization trigger found:"
    IO.eprintln forbidden.stdout
    return 1
  else if forbidden.exitCode != 1 then
    IO.eprintln forbidden.stderr
    return forbidden.exitCode
  let verboseForbidden ← IO.Process.output {
    cmd := "rg"
    args := #[
      "--line-number",
      "\\b(aesop|grind|simp_all)\\b|maxHeartbeats|maxRecDepth|collisionGamePDS|restrictedCollisionGamePDS",
      "Verbose",
      "--glob",
      "*.lean"
    ]
  }
  if verboseForbidden.exitCode == 0 then
    IO.eprintln "forbidden search, resource override, or private CBC trigger found:"
    IO.eprintln verboseForbidden.stdout
    return 1
  else if verboseForbidden.exitCode != 1 then
    IO.eprintln verboseForbidden.stderr
    return verboseForbidden.exitCode
  return 0

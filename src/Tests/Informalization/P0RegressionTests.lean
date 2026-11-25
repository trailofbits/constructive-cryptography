/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization
import Informalization.Verbose
import Informalization.Render.Json
import Informalization.Render.Html
import Informalization.CLI
import Examples.AuthenticatedEncryption.Security

/-!
# P0 End-to-End Regression Suite (`--tier authored`)

Three targeted regression tests verifying every P0.0–P0.5 fix (`adversarial_review_and_hardened_spec.md`):
1. `subtype_overapplied_no_h_le_h`: `Hygiene.lean` exact-arity unwrapping of over-applied
   `Subtype.val` (`g1.1 h ≤ g0.1 h` renders `g_1(h) ≤ g_0(h)`, never `h ≤ h`).
2. `josMau20_prop6_mixed_roles`: 5-level `ContextProfile` lattice under `ChannelContext` combining
   `@[paper_role "shared key resource"]` (`EncKey`), `AuthCh`/`SecCh` (channels), `π_ENC`
   (protocol), `σ` (simulator), and `E : SymmetricEncryption` (`PaperDescribe` L2) in one statement.
3. `spine_induction_obtain_cases`: `By induction on`, `We obtain`, `By cases on`, `Finset.sum`,
   `Finset.prod`, `Finset.filter`, `Exists`, and `ZMod` cleanly render and pass `--tier authored`.
-/

namespace Tests.Informalization.P0RegressionTests

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.CryptographicAlgebra.Specification
open SystemAlgebra Probability Commons
open Informalization.Core.Presentation Informalization.Core.ContextProfile
open scoped NNReal SystemAlgebra VerboseCC

paper_describe_for Finset "finite set" (plural := "finite sets") (carrier := false) (qualifier := "of {0}")

/-! ## Regression 1: Over-Applied `Subtype.val` (`g1.1 h ≤ g0.1 h`) -/

section SubtypeRegression
paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Over-applied `Subtype.val` on a `TypedSystem` transcript probability inequality must never
unwrap to `h ≤ h`. -/
theorem subtype_overapplied_no_h_le_h
    {A : Interface} (g₀ g₁ : TypedSystem A)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (hle : g₁.1 h ≤ g₀.1 h) :
    g₁.1 h ≤ g₀.1 h := by
  We conclude "By hypothesis, $[g₁.1 h ≤ g₀.1 h]" by
    exact hle

informal_title subtype_overapplied_no_h_le_h "Over-Applied Subtype Unwrapping Regression"
informal_kind subtype_overapplied_no_h_le_h "Theorem"
informal_section subtype_overapplied_no_h_le_h "Channel Composition and Structural Examples"
informal_section_prelude subtype_overapplied_no_h_le_h "definition" "Setup" "Subtypes and Constructive Channel Roles"
  "Distinguishing bounds operate over subtype-restricted domains while constructive channel compositions track shared key resources, authenticated and confidential channels, and protocol converters simultaneously."

end SubtypeRegression

/-! ## Regression 2: Channel-Context Mixed-Role Composition -/

section JosMau20Prop6Regression
paper_context ChannelContext
set_option linter.paperPresentation true

/-- Shared key resource type carrier tagged at Level 1 with `@[paper_role "shared key resource"]`. -/
@[paper_role "shared key resource",
  paper_describe "shared key resource" (plural := "shared key resources") (carrier := false)
  (qualifier := "with interface {K}")]
abbrev SharedKeyResource (K : Interface) : Type := TypedSystem K

/-- Mixed-role channel-composition example combining a shared key resource, authenticated and
hybrid channels, encryption and application converters, a simulator, and a symmetric-key encryption
scheme in a single statement. -/
theorem josMau20_prop6_mixed_roles
    {K A B P Q H : Interface} {K_E M C : Type} [Fintype K_E] [Fintype M] [Fintype C]
    (E : SymmetricEncryption K_E M C)
    (EncKey : SharedKeyResource K)
    (AuthCh : TypedSystem A)
    (SecCh : TypedSystem B)
    (IdealApp : TypedSystem (H ⊗ Q))
    (π_ENC : B ⟶ A ⊗ K)
    (π_app : H ⊗ P ⟶ B)
    (σ : P ⟶ Q)
    (simulators : Set (P ⟶ Q))
    {ε₁ ε₂ : ENNReal}
    (_hEncKey : E = E)
    (hEnc : ({π_ENC • (AuthCh ∥ EncKey)} : Specification (TypedSystem B))
      —[𝟙 B; ε₁]→ {SecCh})
    (_hSim : ({SecCh} : Specification (TypedSystem B))
      —[π_app]→ Commons.Indifferentiability.specification IdealApp simulators ε₂)
    (hSimAdmitted : σ ∈ simulators)
    (hSimBound : Δ (π_app • SecCh) ((H ◁ σ) • IdealApp) ≤ ε₂) :
    ({π_ENC • (AuthCh ∥ EncKey)} : Specification (TypedSystem B))
      —[𝟙 B; ε₁]→ {SecCh} ∧
    (σ ∈ simulators ∧ Δ (π_app • SecCh) ((H ◁ σ) • IdealApp) ≤ ε₂) := by
  Proof overview "We verify both the channel-construction step from ${AuthCh} and ${EncKey} to ${SecCh} using ${π_ENC} and the admitted simulator bound for ${σ} in the presence of ${E}."
  We conclude "Both the ${π_ENC} construction of ${SecCh} from ${AuthCh} and ${EncKey} and the ${σ} simulation bound against ${IdealApp} hold by assumption." by
    exact ⟨hEnc, ⟨hSimAdmitted, hSimBound⟩⟩

informal_title josMau20_prop6_mixed_roles "Mixed-Role Channel Composition with Simulator Bounds"
informal_kind josMau20_prop6_mixed_roles "Theorem"

end JosMau20Prop6Regression

/-! ## Regression 3: Spine `induction` / `obtain` / `cases` + `Finset` / `Exists` / `ZMod` -/

section SpineAndMathlibRegression
paper_context GameBasedContext
set_option linter.paperPresentation true

/-- Exercises `By induction on`, `We obtain`, `By cases on`, `Finset.sum`, `Finset.prod`,
`Finset.filter`, `Exists`, and `ZMod` in a single Spine-authored theorem. -/
theorem spine_induction_obtain_cases
    (n : ℕ) (S : Finset ℕ) (hEx : ∃ m : ℕ, m > 0) (z : ZMod 7) :
    (∑ i ∈ Finset.range n, (i + 1)) ≥ n ∧
    (∏ i ∈ Finset.range 1, (i + 1)) = 1 ∧
    (S.filter (fun x => x > 0)).card ≤ S.card ∧
    (∃ k : Fin (n + 1), k.val = 0) ∧
    z = z := by
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · By induction on n explaining "Proceeding by induction on ${n}"
    · simp
    · rw [Finset.sum_range_succ]
      omega
  · simp
  · exact Finset.card_filter_le S _
  · We obtain ⟨m, hm⟩ from hEx explaining "Unpacking the positive witness from $[∃ m : ℕ, m > 0]"
    By cases on hZero : (m = 0) explaining "Splitting into cases on whether ${m} = 0"
    · omega
    · exact ⟨⟨0, Nat.succ_pos n⟩, rfl⟩

informal_title spine_induction_obtain_cases "Spine Induction, Witness Extraction, and Mathlib Printers"
informal_kind spine_induction_obtain_cases "Theorem"

end SpineAndMathlibRegression

/-! ## Axiom Audits & Programmatic P0 Regression Assertions -/

#print axioms subtype_overapplied_no_h_le_h
#print axioms josMau20_prop6_mixed_roles
#print axioms spine_induction_obtain_cases

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let targetDecls : Array Name := #[
    ``subtype_overapplied_no_h_le_h,
    ``josMau20_prop6_mixed_roles,
    ``spine_induction_obtain_cases
  ]
  let doc ← liftTermElabM <| Informalization.Render.Json.buildDocument
    "Constructive Channel Composition and Structural Proof Examples"
    (some "Selected examples of constructive channel roles, subtype bounds, and structural induction")
    targetDecls
  let texts := Informalization.CLI.collectDocumentTexts doc
  let leaks := Informalization.Core.Hygiene.auditZeroLeakage texts
  unless leaks.isEmpty do
    throwError "P0RegressionTests leaked {leaks.size} forbidden string(s): {leaks}"

  -- Assert Test 1: g1(h) <= g0(h), never h <= h
  let e1 := doc.entries[0]!
  let e1Texts := e1.statement.flatMap (·.map (·.collectText)) ++ e1.proof.flatMap (·.collectAllText)
  let e1Joined := String.intercalate " " e1Texts.toList
  unless (e1Joined.splitOn "g_{1}").length > 1 && (e1Joined.splitOn "g_{0}").length > 1 do
    throwError "Regression 1 failed: missing g_1 / g_0 in rendered prose: {e1Joined}"
  if (e1Joined.splitOn "h \\le h").length > 1 then
    throwError "Regression 1 failed: corrupted h ≤ h appeared in rendered prose: {e1Joined}"

  -- Assert Test 2: 5-level lattice preserves shared key resource, channels, simulator, and scheme
  let e2 := doc.entries[1]!
  let e2Stmt := String.intercalate " " ((e2.statement.flatMap (·.map (·.collectText))).toList)
  for expected in ["shared key resource", "symmetric-key encryption scheme", "real channel", "hybrid channel"] do
    unless (e2Stmt.splitOn expected).length > 1 do
      throwError "Regression 2 failed: expected '{expected}' in statement: {e2Stmt}"

  let outDir : System.FilePath :=
    "/Users/marcilunga/.gemini/antigravity/brain/63ffab73-7f96-4075-be50-4d10a715e8ee/scratch/cc-validation"
  IO.FS.createDirAll outDir
  IO.FS.writeFile (outDir / "p0_regressions.json")
    (Informalization.Render.Json.renderDocumentJson doc)
  IO.FS.writeFile (outDir / "p0_regressions.html")
    (Informalization.Render.Html.renderDocumentHtml doc)
  IO.println s!"P0RegressionTests: exported {doc.entries.size} entries, all P0 assertions PASSED"

end Tests.Informalization.P0RegressionTests

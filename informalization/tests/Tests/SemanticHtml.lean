import CBCMAC
import Informalization.MassotMiller.InfoTree
import Informalization.MassotMiller.Describe
import Informalization.MassotMiller.RandomSystems
import Informalization.MassotMillerWeb
import Informalization.Semantics.CBC
import Informalization.Semantics.Explanation
import Informalization.Semantics.GoalState
import Informalization.Semantics.Report
import Tests.CBCExternal

/-!
# Genuine semantic-HTML integration check

This acceptance test re-elaborates the live `cbc-mac-cc` theorem in its owning
workspace, follows the reusable Random Systems semantics plus the thin CBC
extension, and constructs the standalone interactive reader document.
-/

namespace Tests.SemanticHtml

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.InfoTree
open Informalization.Semantics

private def assertIO (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def joinedVisibleText (declaration : LemmaInfo) (expanded : Bool) : String :=
  let proof := declaration.explanations.toList.map fun explanation =>
    (explanation.setAllExpanded expanded).visibleText
  declaration.visibleStatement ++ "\n" ++ String.intercalate "\n" proof

private def joinedProofText (declaration : LemmaInfo) (expanded : Bool) : String :=
  String.intercalate "\n" <| declaration.explanations.toList.map fun explanation =>
    (explanation.setAllExpanded expanded).visibleText

private partial def interactiveDepth : Explanation → Nat
  | .empty | .paragraphBreak | .str _ | .human _ | .goalState _ => 0
  | .join values | .list values | .enumList values =>
      values.foldl (fun depth value => Nat.max depth (interactiveDepth value)) 0
  | .withReplacement value replace preValue preReplace postValue postReplace _ =>
      1 + #[value, replace, preValue, preReplace, postValue, postReplace].foldl
        (fun depth value => Nat.max depth (interactiveDepth value)) 0
  | .withTrailer value trailer _ =>
      1 + Nat.max (interactiveDepth value) (interactiveDepth trailer)
  | .withToolTip value _ | .withLeanHovers value _ | .indent value =>
      interactiveDepth value
  | .withLeanEvidence value _ _ _ => interactiveDepth value
  | .withConcreteProof value proof _ =>
      1 + Nat.max (interactiveDepth value) (interactiveDepth proof)
  | .computation _ steps =>
      steps.foldl (fun depth step => Nat.max depth (interactiveDepth step.expl)) 0

private def hasForbiddenSurface (text : String) : Bool :=
  #["Fintype", "DecidableEq", "Nonempty", "Type*", "RandomSystems.",
    "CBCMAC.",
    "Lean.Expr", "Expr.app", "Expr.const", "_uniq", "_hyg",
    "Subtype.val", "OfNat.ofNat", "by exact", "by simpa", "simp ["].any
      fun fragment => text.contains fragment

/-- Run the genuine external-workspace semantic-to-HTML acceptance check. -/
unsafe def check : IO Unit := do
  initSearchPath (← findSysroot)
  let root ← Tests.CBCExternal.projectRoot
  let source := root / "CBCMAC" / "Main.lean"
  let setup ← Tests.CBCExternal.lakeSetupFor root
    ("CBCMAC/Main.lean" : System.FilePath)
  let some module ← elaborateFile source `SemanticHtmlCBCFixture (some setup) #[]
    | throw (IO.userError "could not elaborate the genuine CBC source")

  let declaration := `CBCMAC.cbc_randomness_expander
  let concreteLanguage := {
    Informalization.MassotMiller.RandomSystems.languageConfig with
    checkedPropositionRenderer? := some
      (Informalization.Semantics.Realize.checkedPropositionLatex?
        Informalization.Semantics.CBC.profile)
  }
  let some metadata ← Informalization.MassotMiller.Describe.lemmaInfo module declaration {
      formalTrailers := false
      language := concreteLanguage
    }
    | throw (IO.userError "could not retain the concrete CBC proof tree")
  let catalog := Informalization.Semantics.CBC.catalog
  let visibleCatalog := catalog.filter fun entry =>
    (module.environment.find? entry.declaration).isSome
  let issues := Registry.validateCatalog module.environment visibleCatalog
  assertIO issues.isEmpty
    s!"CBC semantic catalog does not match the target environment: {repr issues}"

  let some context := module.contextFor declaration
    | throw (IO.userError "missing elaboration context for the CBC theorem")
  let (report, realized, publicDeclaration) ← context.runMetaM {} do
    let information ← getConstInfo declaration
    forallTelescope information.type fun _ conclusion => do
      let report ← Report.ofConclusion module.environment catalog declaration conclusion
        Informalization.Semantics.CBC.profile
      let some realized := report.discourse?
        | throwError "the CBC declaration did not produce semantic discourse"
      let goals ← GoalState.build information.type realized
        Informalization.MassotMiller.RandomSystems.goalLanguageConfig
      let publicDeclaration := Explanation.replaceProof metadata realized {} goals
      return (report, realized, publicDeclaration)

  assertIO (publicDeclaration.statement.contains "\\Delta(" &&
      publicDeclaration.statement.contains "\\theta[B, q]" &&
      publicDeclaration.statement.contains "\\mathsf{CBC}[B]" &&
      publicDeclaration.statement.contains "[q]\\,R" &&
      publicDeclaration.statement.contains "R" &&
      publicDeclaration.statement.contains "V" &&
      publicDeclaration.statement.contains "\\lvert X \\rvert")
    s!"the CBC statement lost its composed systems or distance bound:\n\
      {publicDeclaration.statement}"
  assertIO (publicDeclaration.title == some "CBC-MAC Randomness Expansion")
    s!"the CBC theorem lost its reader-facing title: {repr publicDeclaration.title}"
  assertIO (publicDeclaration.statement.contains "finite abelian group of blocks" &&
      publicDeclaration.statement.contains "finite set of messages with at least two elements" &&
      publicDeclaration.statement.contains "prefix-free" &&
      publicDeclaration.statement.contains "block former" &&
      publicDeclaration.statement.contains "R = \\operatorname{URF}(X,X)" &&
      publicDeclaration.statement.contains "V = \\operatorname{URF}(M,X)" &&
      publicDeclaration.statement.contains "processes the blocks of \\(B(m)\\) in sequence" &&
      publicDeclaration.statement.contains "stops answering once")
    s!"the CBC theorem does not introduce its inputs before the conclusion:\n\
      {publicDeclaration.statement}"
  let statementJson := publicDeclaration.statementExplanation?.map
    (·.toJson.compress) |>.getD ""
  assertIO (statementJson.contains "Explanation.withLeanHovers" &&
      statementJson.contains "\"name\":\"X\"" &&
      statementJson.contains "\"name\":\"M\"" &&
      statementJson.contains "\"name\":\"blockForm\"" &&
      statementJson.contains "\"name\":\"q\"" &&
      statementJson.contains "uniform random function system" &&
      statementJson.contains "ideal variable-input-length random function" &&
      statementJson.contains "CBCMAC.R" &&
      statementJson.contains "CBCMAC.V" &&
      statementJson.contains "CBCMAC.cbc" &&
      statementJson.contains "CBCMAC.theta")
    s!"the CBC theorem introductions lost their checked hover descriptions:\n\
      {statementJson}"
  assertIO (publicDeclaration.declarationHover?.any fun hover =>
      hover.name == "CBCMAC.cbc_randomness_expander" &&
        hover.type.contains "dist")
    s!"the theorem heading lost its Lean declaration hover: \
      {repr publicDeclaration.declarationHover?}"
  let publicJson := publicDeclaration.toJson.compress
  assertIO (publicJson.contains "Explanation.withConcreteProof" &&
      publicJson.contains "Explanation.withReplacement" &&
      publicJson.contains "\"goalState\"" &&
      !publicJson.contains "\\text{Eq.mpr" &&
      !publicJson.contains "Explanation.withLeanEvidence")
    "the CBC reader lost its concrete proof tree or leaked a flat Lean-evidence panel"
  let renderedProof := joinedProofText publicDeclaration true
  assertIO (renderedProof.contains
        "\\theta[B, q]\\cdot \\widehat{\\mathsf{CBC}}[B; R] \\mathrel{\\mid\\!\\equiv} \\theta[B, q]\\cdot V" &&
      !publicJson.contains "\\informalizationRaw{")
    "the concrete CBC proof did not use proportional, profile-aware LaTeX"

  let collapsed := joinedVisibleText publicDeclaration false
  let collapsedProof := joinedProofText publicDeclaration false
  let expandedProof := joinedProofText publicDeclaration true
  assertIO (collapsedProof.contains
        "The total-block restriction permits the converter to make at most \\(q\\) calls" &&
      collapsedProof.contains "\\theta[B, q]\\circ \\mathsf{CBC}[B]" &&
      collapsedProof.contains "Consider the collision game" &&
      collapsedProof.contains "whose MBO records a nontrivial collision" &&
      collapsedProof.contains "Outside the collision event" &&
      collapsedProof.contains "final round-function inputs distinct" &&
      collapsedProof.contains "uniform and consistent" &&
      collapsedProof.contains "In a blind strategy" &&
      collapsedProof.contains "message list is fixed" &&
      collapsedProof.contains "next fresh round-function value is uniform" &&
      collapsedProof.contains "the original distance is at most" &&
      collapsedProof.contains "Substituting this estimate" &&
      collapsedProof.contains
        "\\Gamma(b(\\theta[B, q]\\cdot \\widehat{\\mathsf{CBC}}[B; R]))" &&
      !collapsedProof.contains "common-domain" &&
      !collapsedProof.contains "normalized PDS" &&
      !collapsedProof.contains "\\operatorname{Adv}" &&
      !collapsedProof.contains "Taking the supremum" &&
      !collapsedProof.contains "R_{1}" &&
      !collapsedProof.contains "G_{1}" &&
      !collapsedProof.contains "V_{1}" &&
      !collapsedProof.contains "The formal derivation is retained" &&
      !collapsedProof.contains "registered restriction")
    s!"the collapsed CBC explanation lost its semantic proof spine:\n{collapsedProof}"
  assertIO (expandedProof.contains
        "The collision game and the target system are conditionally equivalent" &&
      expandedProof.contains
        "Applying the same restriction to both sides preserves" &&
      expandedProof.contains
        "On the collision-free slice, the output law factors as follows" &&
      expandedProof.contains "chosen in advance" &&
      expandedProof.contains "collision mass satisfies" &&
      expandedProof.contains "Explicitly" &&
      !expandedProof.contains "checked formula" &&
      !expandedProof.contains "checked conclusion" &&
      !expandedProof.contains "restricted conditional-equivalence claim")
    s!"the expanded CBC explanation lost a substantive subargument:\n{expandedProof}"
  assertIO (!hasForbiddenSurface collapsed)
    s!"kernel syntax, carrier plumbing, or tactic narration leaked into CBC prose:\n{collapsed}"
  assertIO (publicDeclaration.explanations.any fun explanation =>
      interactiveDepth explanation >= 8)
    "the CBC proof does not retain the deep concrete proof tree"

  let semanticJson := realized.toJsonString
  assertIO (semanticJson.contains "conditional-equivalence-to-blind-winning" &&
      semanticJson.contains "conditional-uniform-outputs" &&
      semanticJson.contains
        "CBCMAC.CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq" &&
      semanticJson.contains "distinct-terminal-inputs" &&
      semanticJson.contains "CBCMAC.CBCCombinatorics.cbcLastInput_injOn" &&
      semanticJson.contains "collision-mass-bound" &&
      semanticJson.contains "supportOrigin" &&
      semanticJson.contains "children")
    "the CBC discourse JSON lost proof roles or support ancestry"
  let reportJson := report.toJson.pretty
  assertIO (reportJson.contains "CBCMAC.cbc_randomness_expander")
    "the enclosing CBC report JSON lost its declaration identity"

  let page : WebPage := {
    title := "CBC-MAC randomness expansion"
    declarations := #[publicDeclaration]
  }
  let html := page.toHtml
  assertIO (html.contains "CBCMAC.cbc_randomness_expander" &&
      html.contains "CBC-MAC Randomness Expansion" &&
      html.contains "statementExplanation" &&
      html.contains "with-tooltip" &&
      html.contains "Explanation.withLeanHovers" &&
      html.contains "Explanation.withConcreteProof" &&
      html.contains "declarationHover" &&
      html.contains "lean-reference" &&
      html.contains "concrete-proof-button" &&
      html.contains "button.textContent = '⋯';" &&
      html.contains "proof-state-pane" &&
      html.contains "goalPane.hidden = true" &&
      html.contains ".with-tooltip:hover" &&
      html.contains "collision" &&
      !html.contains "Formal evidence" &&
      !html.contains "_uniq" &&
      !html.contains "Lean.Expr")
    "the standalone CBC page dropped semantic content or exposed backend evidence"

end Tests.SemanticHtml

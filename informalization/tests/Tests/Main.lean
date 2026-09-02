import Informalization
import Informalization.MassotMiller.RandomSystems
import Informalization.Semantics.RandomSystems
import Informalization.Semantics.Validation
import Tests.Semantics
import Tests.Symbols
import Tests.Canonical
import Tests.CBCSemantic
import Tests.EvidenceCompression
import Tests.ProofPlan
import Tests.Discourse
import Tests.LanguageDesign
import Informalization.MassotMiller.Topology

open Lean Meta
open Informalization.MassotMiller
open Informalization.MassotMiller.InfoTree
open Informalization.MassotMiller.Describe

private def fixture : String := include_str "../Fixtures/StructuredProof.lean"

private def assertIO (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)

private def semanticStatementCoverage (module : ElaboratedModule) (name : Name)
    (catalog : Informalization.Semantics.Registry.Catalog) : IO (Bool × Nat) := do
  let some context := module.contextFor name
    | throw (IO.userError s!"missing semantic test context for {name}")
  context.runMetaM {} do
    let information ← getConstInfo name
    forallTelescope information.type fun _ conclusion => do
      let accepted ← Informalization.Semantics.Validation.isSecurityStatementRootWith
        module.environment catalog conclusion
      let graph? ← Informalization.Semantics.Registry.recoverGraphWith?
        module.environment catalog conclusion
      return (accepted, graph?.map (·.nodes.size) |>.getD 0)

private def configuredHandler : English.PropositionHandler := {
  kind := `Fixtures.Related
  run := fun _ _ _ => pure (some "the configured relation holds")
}

private partial def firstComputationSize? : Explanation → Option Nat
  | .computation _ steps => some steps.size
  | .join values | .list values | .enumList values =>
      values.findSome? firstComputationSize?
  | .withReplacement value replace preValue preReplace postValue postReplace _ =>
      firstComputationSize? value <|> firstComputationSize? replace <|>
        firstComputationSize? preValue <|> firstComputationSize? preReplace <|>
        firstComputationSize? postValue <|> firstComputationSize? postReplace
  | .withTrailer value trailer _ =>
      firstComputationSize? value <|> firstComputationSize? trailer
  | .withToolTip value _ | .indent value => firstComputationSize? value
  | _ => none

unsafe def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let some module ← elaborateSourceModule fixture "StructuredProof.lean" `StructuredProof
    | throw (IO.userError "could not elaborate neutral fixture")
  let semanticCatalog := Informalization.Semantics.RandomSystems.catalog
  assertIO semanticCatalog.hasUniqueDeclarations
    "Random Systems semantic catalog contains duplicate declarations"
  let fixtureCatalog := semanticCatalog.filter fun entry =>
    entry.declaration == `LE.le ||
      entry.declaration == `RandomSystems.PDS.advFullyDefined
  assertIO ((Informalization.Semantics.Registry.validateCatalog
      module.environment fixtureCatalog).isEmpty)
    "semantic catalog does not match the separately elaborated fixture signatures"
  assertIO ((Informalization.Semantics.Registry.lookupWith? module.environment
      semanticCatalog `RandomSystems.PDS.advFullyDefined).map (·.role) ==
        some (.quantity .distinguishingAdvantage))
    "explicit semantic catalog did not cross the external-workspace boundary"
  let securityCoverage ← semanticStatementCoverage module
    `Fixtures.configuredAdvantage semanticCatalog
  assertIO (securityCoverage.1 && securityCoverage.2 ≥ 2)
    "advantage-bound root was not recovered as a compositional security graph"
  let arithmeticCoverage ← semanticStatementCoverage module
    `Fixtures.arithmeticBound semanticCatalog
  assertIO (!arithmeticCoverage.1)
    "an arithmetic inequality passed the semantic security-statement gate"
  let document ← Describe.document module #[`Fixtures.structured]
  assertIO (document.size == 1) "generic declaration was not informalized"
  let json := documentToJsonString document
  assertIO (json.contains "Fixtures.structured") "declaration name is absent from JSON"
  assertIO (!json.contains "RandomSystems" && !json.contains "CBC")
    "domain-specific vocabulary leaked into the generic output"
  assertIO (json.contains "We have" && json.contains "Q")
    "a source have-step was not narrated from its introduced fact"
  assertIO (json.contains "The result follows from" && json.contains "hqr")
    "a source exact-step lost its cited reference"
  let config : Describe.Config := {
    language := { propositionHandlers := #[configuredHandler] }
  }
  let configured ← Describe.document module #[`Fixtures.configuredLanguage] config
  assertIO (configured.size == 1) "configured declaration was not informalized"
  assertIO (configured[0]!.statement.contains "the configured relation holds")
    "application proposition handler was not used"
  let calculation ← Describe.document module #[`Fixtures.calculated]
  assertIO (calculation.size == 1) "calculation declaration was not informalized"
  assertIO (firstComputationSize? calculation[0]!.explanations[0]! == some 2)
    "kernel-backed calc reconstruction did not retain both steps"
  let legacyRandomSystemsConfig : Describe.Config := {
    language := Informalization.MassotMiller.RandomSystems.languageConfig
  }
  let ordinaryList ← Describe.document module #[`Fixtures.ordinaryList]
    legacyRandomSystemsConfig
  assertIO (!ordinaryList[0]!.statement.contains "transcript")
    "an arbitrary List was misclassified as a transcript"
  let arbitraryBadName ← Describe.document module #[`Fixtures.arbitraryBadName]
    legacyRandomSystemsConfig
  assertIO (!arbitraryBadName[0]!.statement.contains "is good")
    "a predicate was misclassified from the local name Bad"
  let genericTopology ← Describe.document module #[`Fixtures.topologyVocabulary]
  assertIO (!genericTopology[0]!.statement.contains "topological space" &&
      !genericTopology[0]!.statement.contains "is open")
    "topology vocabulary leaked into the domain-neutral profile"
  let topologyConfig : Describe.Config := {
    language := Informalization.MassotMiller.Topology.languageConfig
  }
  let configuredTopology ← Describe.document module #[`Fixtures.topologyVocabulary]
    topologyConfig
  assertIO (configuredTopology[0]!.statement.contains "topological space" &&
      configuredTopology[0]!.statement.contains "is open")
    "the optional topology profile did not restore Rudin vocabulary"
  let page : WebPage := { title := "Neutral fixture", declarations := document }
  assertIO (page.toHtml.contains "informalization-data")
    "HTML renderer did not embed the public explanation document"
  assertIO (page.toHtml.contains "(function ()" &&
      !page.toHtml.contains "src=\"massot-miller.js")
    "HTML renderer is not standalone"
  let goal : GoalInfo := {
    target := "\\(P\\)"
    paragraphForm := "It remains to prove \\(P\\)."
    items := #[
      { name := some "X", singularType := "is a type",
        pluralType := some "are types" },
      { name := some "x✝", singularType := "is an internal term",
        pluralType := some "are internal terms" }
    ]
  }
  let goalDocument : Document := #[{
    name := "Fixtures.goalMarker"
    statement := "Suppose \\(P\\)."
    explanations := #[.join #[.goalState goal, .str "The result follows."]]
  }]
  let goalJson := documentToJsonString goalDocument
  let goalPage : WebPage := { title := "Goal marker fixture", declarations := goalDocument }
  assertIO (goalJson.contains "Explanation.goalState" &&
      goalPage.toHtml.contains "proof-state-pane" &&
      goalPage.toHtml.contains "aria-pressed" &&
      goalPage.toHtml.contains "contextNameForDisplay" &&
      goalPage.toHtml.contains "renderedGoals.indexOf(currentGoal) < 0" &&
      goalPage.toHtml.contains "paragraphForm !== currentGoal.target")
    "standalone renderer lost the Miller-style goal marker/inspector contract"
  assertIO (page.toHtml.contains "if (!hasGoals)" &&
      page.toHtml.contains "main-div-no-goals")
    "a document without goal-state nodes no longer suppresses the empty inspector"
  let richStatement : Explanation := .join #[
    .str "Let ",
    .withToolTip (.str "\\(R\\)") "The real random system.",
    .str " be the real system.",
    .paragraphBreak,
    .withLeanHovers
      (.str "Then \\[\\Delta(R,V) \\leq \\varepsilon.\\]")
      #[{
        latex := "R"
        name := "Fixtures.R"
        type := "RandomSystem"
        explicit? := some "Fixtures.R"
        documentation? := some "The real system."
      }]
  ]
  let exactEvidence : Explanation := .withLeanEvidence
    (.str "This claim is checked.")
    #[{
      label := "proof step 0"
      declaration? := some "Fixtures.checkedClaim"
      type := "True"
      expected? := some "True"
      term := "True.intro"
      source? := some {
        moduleName := "Fixtures"
        line := 12
        column := 0
        endLine := 12
        endColumn := 20
      }
    }]
    none false
  assertIO (exactEvidence.visibleText == "This claim is checked." &&
      (exactEvidence.setAllExpanded true).visibleText == "This claim is checked." &&
      (exactEvidence.setAllExpanded true).toJson.compress.contains "\"expanded\":false")
    "semantic expansion opened or leaked the independent Lean-evidence tier"
  let concreteTree : Explanation := .withReplacement
    (.str "A concrete step.")
    (.join #[
      .str "A concrete step.",
      .paragraphBreak,
      .indent (.withReplacement
        (.str "Its checked substep.")
        (.str "Its complete checked subderivation.")
        .empty .empty .empty .empty false)
    ])
    .empty .empty .empty .empty false
  let proofViews : Explanation :=
    .withConcreteProof exactEvidence concreteTree false
  let expandedProofView := proofViews.setAllExpanded true
  let expandedProofViews := expandedProofView.toJson.compress
  let concreteTierStayedClosed := match expandedProofView with
    | .withConcreteProof _ _ expanded => !expanded
    | _ => false
  assertIO (proofViews.visibleText == "This claim is checked." &&
      concreteTierStayedClosed &&
      expandedProofViews.contains "Explanation.withConcreteProof" &&
      expandedProofViews.contains "Its complete checked subderivation" &&
      expandedProofViews.contains "\"expanded\":false" &&
      !expandedProofViews.contains "\"expanded\":true")
    "semantic expansion changed the independent complete-proof tier"
  let openConcreteProof : Explanation :=
    .withConcreteProof exactEvidence concreteTree true
  let fullyExpandedConcreteProof := openConcreteProof.setAllExpanded true
  let selectedConcreteTierExpanded := match fullyExpandedConcreteProof with
    | .withConcreteProof _ (.withReplacement _ _ _ _ _ _ expanded) selected =>
        selected && expanded
    | _ => false
  assertIO selectedConcreteTierExpanded
    "global expansion did not recurse through the selected complete-proof tier"
  let globalProofView := proofViews.setGlobalExpansion true
  let globalConcreteTreeExpanded := match globalProofView with
    | .withConcreteProof _ (.withReplacement _ _ _ _ _ _ expanded) selected =>
        selected && expanded
    | _ => false
  let globalProofViewCollapsed := globalProofView.setGlobalExpansion false
  let globalCollapseRestoredProse := match globalProofViewCollapsed with
    | .withConcreteProof value _ selected =>
        !selected && value.visibleText == "This claim is checked."
    | _ => false
  assertIO (globalConcreteTreeExpanded && globalCollapseRestoredProse)
    "the global reader transition did not open the complete tree or restore prose"
  let richDocument : Document := #[{
    name := "Fixtures.readerFacingTheorem"
    title := some "Reader-Facing Security Bound"
    statement := richStatement.visibleText
    statementExplanation? := some richStatement
    declarationHover? := some {
      name := "Fixtures.readerFacingTheorem"
      type := "Prop"
    }
    explanations := #[proofViews]
  }]
  let richPage : WebPage := {
    title := "Rich theorem fixture"
    declarations := richDocument
  }
  let richHtml := richPage.toHtml
  assertIO (richHtml.contains "Reader-Facing Security Bound" &&
      richHtml.contains "statementExplanation" &&
      richHtml.contains "Explanation.withToolTip" &&
      richHtml.contains "Explanation.withLeanHovers" &&
      richHtml.contains "Explanation.withLeanEvidence" &&
      richHtml.contains "Explanation.withConcreteProof" &&
      richHtml.contains "declarationHover" &&
      richHtml.contains "annotateMathReferences" &&
      richHtml.contains "lean-evidence-button" &&
      richHtml.contains "button.textContent = '⊢';" &&
      richHtml.contains "Show the exact formalization" &&
      richHtml.contains "Exact Lean formalization" &&
      richHtml.contains "Formal statement" &&
      richHtml.contains "concrete-proof-button" &&
      richHtml.contains "button.textContent = '⋯';" &&
      richHtml.contains "function mountInformalization(mountNode, declarations, options)" &&
      richHtml.contains "publicApi.mount = mountInformalization;" &&
      richHtml.contains "elt('div', 'proof-controls')" &&
      richHtml.contains "if (controls) documentNode.appendChild(controls);" &&
      richHtml.contains "tooltipRoot.appendChild(tip);" &&
      richHtml.contains "button.textContent = node.expanded ? '⊖' : '⊕';" &&
      richHtml.contains "setAllExpanded(state, node.expanded ? node.proof : node.value);" &&
      richHtml.contains "function setGlobalExpansion(state, node)" &&
      richHtml.contains "setGlobalExpansion(state, decl);" &&
      richHtml.contains "node.expanded = state;\n        if (state)" &&
      !richHtml.contains "node.expanded = state;\n        setAllExpanded(state, node.value);\n        setAllExpanded(state, node.proof);" &&
      richHtml.contains ".explanation-refinement-button {\n  float: none;" &&
      richHtml.contains ".lean-hover-content {" &&
      richHtml.contains "position: fixed;" &&
      richHtml.contains "max-height: none;" &&
      richHtml.contains "overflow: visible;" &&
      richHtml.contains "attachFloatingTooltip" &&
      richHtml.contains "tooltip-visible" &&
      richHtml.contains "rawSourceFragments" &&
      richHtml.contains "inert-source-fragment" &&
      !richHtml.contains "max-height: min(24rem, 70vh);" &&
      !richHtml.contains "background: #f7f8f9;" &&
      !richHtml.contains "border: 1px solid #d5d9dd;" &&
      richHtml.contains ".math-display > .katex-display > .katex { font-size: 1.04em; }" &&
      richHtml.contains ".proof-controls input {" &&
      richHtml.contains "font-size: 0.76em;" &&
      !richHtml.contains "font-size: 0.76rem;" &&
      richHtml.contains "The real random system." &&
      richHtml.contains "theorem-statement-content")
    "the HTML renderer lost theorem titles, structured openings, unboxed Lean evidence, Lean hovers, or math scale"
  IO.println "informalization backend tests passed"
  return 0

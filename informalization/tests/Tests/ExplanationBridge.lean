import Informalization.Semantics.Explanation

namespace Tests.ExplanationBridge

open Lean
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Discourse
open Informalization.Semantics.Realize
open Informalization.Semantics.Explanation
open Informalization.MassotMiller

private def source : Realize.Document := {
  security := none
  planKind := .conditionalEquivalenceBlind
  sentences := #[
    {
      moveId := 0
      kind := .stateSecurityGoal
      semanticDepth := 0
      text := "The distinguishing advantage is at most the stated bound."
      primaryEvidence? := some (.statementNode { index := 0 })
      evidence := #[.statementNode { index := 0 }]
    },
    {
      moveId := 1
      kind := .conditionalEquivalenceReduction
      semanticDepth := 0
      text := "Conditional equivalence reduces the claim to blind winning."
      primaryEvidence? := some (.proofStep 0)
      evidence := #[.proofStep 0]
      details := #[{
        kind := .registeredRule .conditionalEquivalenceUnderRestriction
        semanticDepth := 1
        text := "The query restriction preserves conditional equivalence."
        primaryEvidence := .proofStep 1
        evidence := #[.proofStep 99, .proofStep 1]
        children := #[{
          kind := .registeredRule .nonadaptiveQueriesFixed
          semanticDepth := 2
          text := "A non-adaptive execution fixes the query set."
          primaryEvidence := .proofStep 2
          evidence := #[.proofStep 2]
          children := #[{
            kind := .registeredRule .birthdayBound
            semanticDepth := 3
            text := "The birthday estimate bounds its collision probability."
            primaryEvidence := .proofStep 3
            evidence := #[.proofStep 3]
          }]
        }]
      }]
    },
    {
      moveId := 2
      kind := .formalFallback
      semanticDepth := 0
      text := "The remaining proof region is retained in formal form."
      primaryEvidence? := some (.formalFallback 0)
      evidence := #[.formalFallback 0]
    }
  ]
  evidenceIndex := #[
    {
      reference := .statementNode { index := 0 }
      formal := mkConst `Statement.Conclusion
    },
    {
      reference := .proofStep 0
      formal := mkConst (Name.mkSimple
        "RandomSystems.System.transcriptInputs_uniq.88956_uniq.88956")
      expected? := some
        (mkConst (Name.mkSimple
          "RandomSystems.System.DDE.Total.transcript_uniq.88956_uniq.88956"))
    },
    {
      reference := .proofStep 1
      formal := mkConst `Detail.Payload
      expected? := some (mkConst `Detail.Conclusion)
    },
    {
      reference := .formalFallback 0
      formal := mkConst `Fallback.Payload
      expected? := some (mkConst `Fallback.Conclusion)
    },
    {
      reference := .proofStep 2
      formal := mkConst `Nested.Payload
      expected? := some (mkConst `Nested.Conclusion)
    },
    {
      reference := .proofStep 3
      formal := mkConst `Birthday.Payload
      expected? := some (mkConst `Birthday.Conclusion)
    }
  ]
}

private def result := toLemmaInfo `Tests.semanticProof source

#guard result.name == "Tests.semanticProof"
#guard result.statement ==
  "The distinguishing advantage is at most the stated bound."
#guard result.explanations.size == 1

private def collapsed := result.explanations[0]!.visibleText
private def expanded :=
  (result.explanations[0]!.setAllExpanded true).visibleText
private def json := result.toJson.compress

-- The collapsed proof is semantic prose, not a proof term or formal dump.
#guard collapsed.contains
  "Conditional equivalence reduces the claim to blind winning."
#guard collapsed.contains
  "The remaining proof region is retained in formal form."
#guard !collapsed.contains "The query restriction preserves"
#guard !collapsed.contains "Checked.Conclusion"
#guard !collapsed.contains "Proof.Payload"

-- Expansion reveals only the semantic subargument.  Evidence identifiers stay
-- in tooltips, and neither checked propositions nor proof payloads become
-- expand-all content.
#guard expanded.contains "The query restriction preserves conditional equivalence."
#guard expanded.contains "A non-adaptive execution fixes the query set."
#guard expanded.contains "The birthday estimate bounds its collision probability."
#guard !expanded.contains "proof step 0"
#guard !expanded.contains "proof step 1"
#guard !expanded.contains "formal fallback 0"
#guard !expanded.contains "Formal evidence"
#guard !expanded.contains "Checked.Conclusion"
#guard !expanded.contains "Detail.Conclusion"
#guard !expanded.contains "Fallback.Conclusion"
#guard !expanded.contains "Proof.Payload"
#guard !expanded.contains "Detail.Payload"
#guard !expanded.contains "Fallback.Payload"
#guard !expanded.contains "_uniq"
#guard !expanded.contains "RandomSystems.System"

-- The reader-facing default retains semantic disclosure but no implementation
-- provenance or serialized Lean `Expr` surface.
#guard result.explanations[0]!.interactiveCount == 3
#guard json.contains "Explanation.withReplacement"
#guard !json.contains "Explanation.withTrailer"
#guard !json.contains "Explanation.enumList"
#guard !json.contains "Explanation.withToolTip"
#guard !json.contains "Checked against: proof step 0"
#guard !json.contains "Expr.const"
#guard !json.contains "Proof.Payload"
#guard !json.contains "Formal evidence"
#guard !json.contains "_uniq"
#guard !json.contains "RandomSystems.System"

-- Even the deprecated trailer switch cannot re-open the raw-expression leak.
private def compatibilityConfig : Config := { formalTrailers := true }
private def compatibilityJson :=
  (toLemmaInfo `Tests.semanticProof source compatibilityConfig).toJson.compress
#guard !compatibilityJson.contains "Explanation.withTrailer"
#guard !compatibilityJson.contains "Formal evidence"
#guard !compatibilityJson.contains "_uniq"

-- Initial disclosure depth is semantic and recursive: opening one layer does
-- not flatten every descendant into the same panel.
private def throughOne := (toLemmaInfo `Tests.semanticProof source {
  initialExpansion := .through 1
}).explanations[0]!.visibleText
private def throughTwo := (toLemmaInfo `Tests.semanticProof source {
  initialExpansion := .through 2
}).explanations[0]!.visibleText
private def throughThree := (toLemmaInfo `Tests.semanticProof source {
  initialExpansion := .through 3
}).explanations[0]!.visibleText
#guard throughOne.contains "The query restriction preserves conditional equivalence."
#guard !throughOne.contains "A non-adaptive execution fixes the query set."
#guard throughTwo.contains "A non-adaptive execution fixes the query set."
#guard !throughTwo.contains "The birthday estimate bounds its collision probability."
#guard throughThree.contains "The birthday estimate bounds its collision probability."

-- A merged provenance list may begin with a wrapper step.  The checkpoint is
-- selected only by the node's explicit primary evidence.
private def primaryGoals : GoalState.Index := {
  entries := #[
    {
      reference := .proofStep 99
      goal := { target := "WRONG WRAPPER CHECKPOINT" }
    },
    {
      reference := .proofStep 1
      goal := { target := "PRIMARY RESTRICTION CHECKPOINT" }
    }
  ]
}
private def primaryGoalJson := (toLemmaInfo `Tests.semanticProof source
  { initialExpansion := .through 1 } primaryGoals).toJson.compress
#guard primaryGoalJson.contains "PRIMARY RESTRICTION CHECKPOINT"
#guard !primaryGoalJson.contains "WRONG WRAPPER CHECKPOINT"

-- A caller may opt into a quiet visual verification cue.  It resolves to the
-- same stable tooltip and cannot expose the evidence expression.
private def cueResult := toLemmaInfo `Tests.semanticProof source {
  evidenceTooltips := true
  checkedSourceCue := true
}
private def cueJson := cueResult.toJson.compress
#guard cueResult.explanations[0]!.visibleText.contains "✓"
#guard cueJson.contains "Checked against: proof step 0"
#guard !cueJson.contains "_uniq"

#guard (toLemmaInfoWithStatement `Tests.semanticProof
  "A caller-supplied statement." source).statement ==
    "A caller-supplied statement."

private def legacyMetadata : LemmaInfo := {
  name := "Tests.legacyMetadata"
  header := "Lemma"
  statement := "The retained statement."
  explanations := #[.human "Rejected legacy proof prose."]
}

private def replaced := replaceProof legacyMetadata source

#guard replaced.name == legacyMetadata.name
#guard replaced.header == legacyMetadata.header
#guard replaced.statement == legacyMetadata.statement
#guard !replaced.explanations[0]!.visibleText.contains "Rejected legacy proof prose"
#guard replaced.explanations[0]!.visibleText.contains "Conditional equivalence"

private def presentedSource : Realize.Document := {
  source with
  theoremPresentation? := some {
    declaration := `Tests.semanticProof
    title := "A Reader-Facing Result"
    introductions := #[{
      fragments := #[
        .text "Let ",
        .reference {
          target := .theoremBinder `X
          latex := "X"
          description := "The finite input space."
        },
        .text " be the input space."
      ]
    }]
  }
}

private def presented := toLemmaInfo `Tests.semanticProof presentedSource
private def presentedJson := presented.toJson.compress

#guard presented.title == some "A Reader-Facing Result"
#guard presented.statement ==
  "Let \\(X\\) be the input space.\n\nThe distinguishing advantage is at most the stated bound."
#guard presented.visibleStatement == presented.statement
#guard presentedJson.contains "statementExplanation"
#guard presentedJson.contains "Explanation.withToolTip"
#guard presentedJson.contains "The finite input space."

private def titledMetadata : LemmaInfo := {
  name := "Tests.titledMetadata"
  title := some "Caller Title"
  statement := "A compatibility statement."
}

#guard (replaceProof titledMetadata presentedSource).title == some "Caller Title"

#guard (toDocument #[(`Tests.semanticProof, source)]).size == 1

end Tests.ExplanationBridge

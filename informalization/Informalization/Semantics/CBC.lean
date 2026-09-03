/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.CanonicalRandomSystems
import Informalization.Semantics.RandomSystems

/-!
# CBC semantic profile

This is the executable informalization contract for the standalone
`cbc-mac-cc` project. It maps that project's public declarations to the shared
Random Systems ontology; it contains no proof-specific prose and imports no
CBC source module.

The reusable Random Systems profile remains application-neutral. Selecting
this overlay adds the public CBC converter, total-block restriction, round
query restriction, collision game, real and ideal systems, and the named
mathematical steps used by `CBCMAC.cbc_randomness_expander`.
-/

namespace Informalization.Semantics.CBC

open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Registry

def primaryArgument (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot }

def supportingArgument (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot, salience := .supporting }

def implementationArgument (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot, salience := .implementation }

private def presentationText (value : String) : PresentationFragment :=
  .text value

private def binderReference (binder : Lean.Name) (latex description : String)
    (hoverLatex : String := "") :
    PresentationFragment :=
  .reference { target := .theoremBinder binder, latex, hoverLatex, description }

private def declarationReference (declaration : Lean.Name) (latex description : String)
    (hoverLatex : String := "") :
    PresentationFragment :=
  .reference { target := .declaration declaration, latex, hoverLatex, description }

private def notationLiteral (value : String) : DeclarationNotationPiece :=
  .literal value

private def notationOperand (slot : Lean.Name) : DeclarationNotationPiece :=
  .operand slot

private def cbcRandomnessExpansionPresentation : TheoremPresentation := {
  declaration := `CBCMAC.cbc_randomness_expander
  title := "CBC-MAC Randomness Expansion"
  introductions := #[
    { fragments := #[
        presentationText "Let ",
        binderReference `X "X"
          "The finite abelian group of blocks, written additively.",
        presentationText " be a finite abelian group of blocks, written additively; ",
        binderReference `M "M"
          "The finite set of messages, containing at least two elements.",
        presentationText " a finite set of messages with at least two elements; and ",
        binderReference `blockForm "B : M \\to X^*"
          "The block former, mapping each message to a finite sequence of blocks." "B",
        presentationText " a block former. Let ",
        binderReference `q "q \\in \\mathbb{N}"
          "The total block budget available to the construction." "q",
        presentationText " bound the total number of blocks processed."
      ] },
    { fragments := #[
        presentationText "Assume that ",
        binderReference `blockForm "B"
          "The block former, mapping each message to a finite sequence of blocks.",
        presentationText " is prefix-free: for two distinct messages, neither block sequence is a prefix of the other."
      ] },
    { fragments := #[
        presentationText "Write ",
        declarationReference `CBCMAC.R "R = \\operatorname{URF}(X,X)"
          "The uniform random function system from blocks to blocks." "R",
        presentationText " for the uniform random function on blocks, and ",
        declarationReference `CBCMAC.V "V = \\operatorname{URF}(M,X)"
          "The ideal random-function system from messages to blocks." "V",
        presentationText " for the ideal random function from messages to blocks."
      ] },
    { fragments := #[
        presentationText "The converter ",
        declarationReference `CBCMAC.cbc "\\mathsf{CBC}[B]"
          "The CBC converter instantiated with the block former B." "\\mathsf{CBC}",
        presentationText " processes the blocks of \\(B(m)\\) in sequence, using its attached system as the round function. The restriction ",
        declarationReference `CBCMAC.theta "\\theta[B,q]"
          "The converter that restricts the total number of encoded blocks to q." "\\theta",
        presentationText " stops answering once the processed messages contain more than \\(q\\) blocks in total."
      ] }
  ]
}

/-- Canonical decoding vocabulary for the public `cbc-mac-cc` theorem. -/
def profile : DecoderProfile :=
  let base := Canonical.RandomSystemsProfile.profile
  { base with
    namedSystems := base.namedSystems ++ #[
      `CBCMAC.R,
      `CBCMAC.V,
      `CBCMAC.cbcPDS,
      `CBCMAC.realPDS,
      `CBCMAC.restrictedRandomFunction,
      `CBCMAC.idealPDS,
      `CBCMAC.restrictedCBCPDS,
      `CBCMAC.restrictedIdealFunctionPDS
    ]
    converterAtoms := base.converterAtoms ++ #[
      `CBCMAC.cbc,
      `CBCMAC.queryLimit
    ]
    converterRestrictions := base.converterRestrictions ++ #[
      `CBCMAC.theta
    ]
    queryRestrictionConverters := base.queryRestrictionConverters ++ #[
      `CBCMAC.queryLimit
    ]
    namedGames := base.namedGames ++ #[
      `CBCMAC.cbcCollisionGame,
      `CBCMAC.restrictedCBCCollisionGame
    ]
    primaryHypotheses := base.primaryHypotheses ++ #[
      `CBCMAC.PrefixFree
    ]
    declarationNotations := base.declarationNotations ++ #[
      {
        declaration := `CBCMAC.R
        latex := "R"
      },
      {
        declaration := `CBCMAC.V
        latex := "V"
      },
      {
        declaration := `CBCMAC.cbc
        latex := "\\mathsf{CBC}"
        style := .bracketed
        operandSlots := #[`blockForm]
      },
      {
        declaration := `CBCMAC.theta
        latex := "\\theta"
        style := .bracketed
        operandSlots := #[`blockForm, `queryBudget]
      },
      {
        declaration := `CBCMAC.cbcPDS
        latex := "\\mathsf{CBC}"
        style := .template
        operandSlots := #[`blockForm, `roundFunction]
        template := #[
          notationLiteral "\\mathsf{CBC}[",
          notationOperand `blockForm,
          notationLiteral "]\\cdot ",
          notationOperand `roundFunction
        ]
      },
      {
        declaration := `CBCMAC.restrictedRandomFunction
        latex := "[q]R"
        style := .template
        operandSlots := #[`queryBudget, `roundFunction]
        template := #[
          notationLiteral "[",
          notationOperand `queryBudget,
          notationLiteral "]\\,",
          notationOperand `roundFunction
        ]
      },
      {
        declaration := `CBCMAC.realPDS
        latex := "\\theta\\cdot\\mathsf{CBC}\\cdot[q]R"
        style := .template
        operandSlots := #[`blockForm, `queryBudget, `roundFunction]
        template := #[
          notationLiteral "\\theta[",
          notationOperand `blockForm,
          notationLiteral ", ",
          notationOperand `queryBudget,
          notationLiteral "]\\cdot\\mathsf{CBC}[",
          notationOperand `blockForm,
          notationLiteral "]\\cdot[",
          notationOperand `queryBudget,
          notationLiteral "]\\,",
          notationOperand `roundFunction
        ]
      },
      {
        declaration := `CBCMAC.idealPDS
        latex := "\\theta\\cdot V"
        style := .template
        operandSlots := #[`blockForm, `queryBudget, `idealFunction]
        template := #[
          notationLiteral "\\theta[",
          notationOperand `blockForm,
          notationLiteral ", ",
          notationOperand `queryBudget,
          notationLiteral "]\\cdot ",
          notationOperand `idealFunction
        ]
      },
      {
        declaration := `CBCMAC.restrictedCBCPDS
        latex := "\\theta\\cdot\\mathsf{CBC}\\cdot R"
        style := .template
        operandSlots := #[`blockForm, `queryBudget, `roundFunction]
        template := #[
          notationLiteral "\\theta[",
          notationOperand `blockForm,
          notationLiteral ", ",
          notationOperand `queryBudget,
          notationLiteral "]\\cdot\\mathsf{CBC}[",
          notationOperand `blockForm,
          notationLiteral "]\\cdot ",
          notationOperand `roundFunction
        ]
      },
      {
        declaration := `CBCMAC.restrictedIdealFunctionPDS
        latex := "\\theta\\cdot V"
        style := .template
        operandSlots := #[`blockForm, `queryBudget, `idealFunction]
        template := #[
          notationLiteral "\\theta[",
          notationOperand `blockForm,
          notationLiteral ", ",
          notationOperand `queryBudget,
          notationLiteral "]\\cdot ",
          notationOperand `idealFunction
        ]
      },
      {
        declaration := `CBCMAC.cbcCollisionGame
        latex := "\\widehat{\\mathsf{CBC}}"
        style := .template
        operandSlots := #[`blockForm, `roundFunction]
        template := #[
          notationLiteral "\\widehat{\\mathsf{CBC}}[",
          notationOperand `blockForm,
          notationLiteral "; ",
          notationOperand `roundFunction,
          notationLiteral "]"
        ]
      },
      {
        declaration := `CBCMAC.restrictedCBCCollisionGame
        latex := "\\theta\\cdot\\widehat{\\mathsf{CBC}}"
        style := .template
        operandSlots := #[`blockForm, `queryBudget, `roundFunction]
        template := #[
          notationLiteral "\\theta[",
          notationOperand `blockForm,
          notationLiteral ", ",
          notationOperand `queryBudget,
          notationLiteral "]\\cdot\\widehat{\\mathsf{CBC}}[",
          notationOperand `blockForm,
          notationLiteral "; ",
          notationOperand `roundFunction,
          notationLiteral "]"
        ]
      }
    ]
    theoremPresentations := base.theoremPresentations ++ #[
      cbcRandomnessExpansionPresentation
    ]
    rules := base.rules ++ #[
      {
        declaration := `CBCMAC.cbc_randomness_expander
        rule := .deriveDistanceBound
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `q, slot := `blockBudget }
        ]
        proofSlots := #[.sideCondition]
      },
      {
        declaration := `CBCMAC.theta_cbc_eq_theta_cbc_queryLimit
        rule := .custom `restrictionApplicationEquation
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `q, slot := `blockBudget }
        ]
        formula? := some .converterEquality
      },
      {
        declaration := `CBCMAC.cbcCollisionGame_conditionallyEquivalent
        rule := .establishConditionalEquivalence
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm }
        ]
        proofSlots := #[.sideCondition]
      },
      {
        declaration := `CBCMAC.cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad
        rule := .establishConditionalEquivalence
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `condition, slot := `collisionCondition }
        ]
        proofSlots := #[.sideCondition, .sideCondition]
      },
      {
        declaration := `CBCMAC.theta_cbcCollisionGame_conditionallyEquivalent
        rule := .preserveConditionalEquivalence
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `q, slot := `blockBudget }
        ]
        proofSlots := #[.conditionalEquivalence]
      },
      {
        declaration := `CBCMAC.supWinProb_blind_filterDom_cbc_le
        rule := .establishBlindWinningBound
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `q, slot := `blockBudget },
          { selector := .binder `condition, slot := `collisionCondition }
        ]
        proofSlots := #[.sideCondition]
      },
      {
        declaration := `CBCMAC.CBCCombinatorics.mass_cbcBad_le
        rule := .custom `collisionMassBound
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `limit, slot := `blockLimit },
          { selector := .binder `messages, slot := `messages }
        ]
        formula? := some .collisionMassBound
        proofSlots := #[.sideCondition]
      },
      {
        declaration :=
          `CBCMAC.CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq
        rule := .custom `conditionalUniformOutputs
        operands := #[
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `messages, slot := `messages },
          { selector := .binder `answers, slot := `answers }
        ]
        formula? := some .conditionalProductIdentity
        proofSlots := #[.sideCondition]
      },
      {
        declaration :=
          `CBCMAC.CBCCombinatorics.not_cbcBad_inputs_ne
        rule := .custom `distinctSiteInputs
        operands := #[
          { selector := .binder `f, slot := `function },
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `message, slot := `message },
          { selector := .binder `other, slot := `otherMessage },
          { selector := .binder `position, slot := `position },
          { selector := .binder `otherPosition, slot := `otherPosition }
        ]
        formula? := some .distinctSiteInputs
        proofSlots := #[.sideCondition, .sideCondition, .sideCondition,
          .sideCondition, .sideCondition, .sideCondition]
      },
      {
        declaration := `CBCMAC.CBCCombinatorics.cbcLastInput_injOn
        rule := .custom `terminalInputInjective
        operands := #[
          { selector := .binder `f, slot := `function },
          { selector := .binder `blockForm, slot := `blockForm },
          { selector := .binder `messages, slot := `messages }
        ]
        formula? := some .terminalInputInjective
        proofSlots := #[.sideCondition, .sideCondition, .sideCondition]
      }
    ]
  }

/-- CBC-specific entries composed with the reusable Random Systems catalog. -/
def overlay : Catalog := #[
  {
    declaration := `CBCMAC.R
    role := .system .uniformRandomFunction
  },
  {
    declaration := `CBCMAC.V
    role := .system .idealFunctionality
  },
  {
    declaration := `CBCMAC.cbc
    role := .converter .atom
    arguments := #[primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm)]
  },
  {
    declaration := `CBCMAC.theta
    role := .converter .blockRestriction
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockLimit (.binder `limit) (.custom `blockLimit)
    ]
  },
  {
    declaration := `CBCMAC.queryLimit
    role := .converter .queryRestriction
    arguments := #[primaryArgument `queryBudget (.binder `limit) .queryBudget]
  },
  {
    declaration := `CBCMAC.cbcCollisionCondition
    role := .entity .collisionCondition
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `roundFunction (.binder `function) (.custom `roundFunction)
    ]
  },
  {
    declaration := `CBCMAC.cbcCollisionGame
    role := .game .atom
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction)
    ]
  },
  {
    declaration := `CBCMAC.restrictedCBCCollisionGame
    role := .game .queryRestriction
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction)
    ]
  },
  {
    declaration := `CBCMAC.restrictedCBCPDS
    role := .system .queryRestriction
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction)
    ]
  },
  {
    declaration := `CBCMAC.restrictedIdealFunctionPDS
    role := .system .idealFunctionality
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `idealFunction (.binder `idealFunction) (.custom `idealFunction)
    ]
  },
  {
    declaration := `CBCMAC.PrefixFree
    role := .proposition (.custom `prefixFree)
    arguments := #[primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm)]
  },
  {
    declaration := `CBCMAC.cbc_randomness_expander
    role := .proofRule .distanceBound
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      supportingArgument `prefixFree (.binder `prefixFree) (.premise 0),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.cbcCollisionGame_conditionallyEquivalent
    role := .proofRule .collisionConditionalEquivalence
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      supportingArgument `prefixFree (.binder `prefixFree) (.premise 0),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.cbc_conditionallyEquivalent_urf_of_condition_eq_cbcBad
    role := .proofRule .collisionConditionalEquivalence
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      supportingArgument `prefixFree (.binder `prefixFree) (.premise 0),
      primaryArgument `collisionCondition (.binder `condition) .condition,
      supportingArgument `conditionCharacterization
        (.binder `condition_eq_cbcBad) (.premise 1),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.theta_cbcCollisionGame_conditionallyEquivalent
    role := .proofRule .conditionalEquivalenceUnderRestriction
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      supportingArgument `conditionalEquivalence
        (.binder `conditionalEquivalence) (.premise 0),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.supWinProb_blind_filterDom_cbc_le
    role := .proofRule .blindWinningBound
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `collisionCondition (.binder `condition) .condition,
      supportingArgument `conditionCharacterization
        (.binder `condition_eq_cbcBad) (.premise 0),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.CBCCombinatorics.mass_cbcBad_le
    role := .proofRule .collisionMassBound
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockLimit (.binder `limit) (.custom `blockLimit),
      primaryArgument `messages (.binder `messages) .transcript,
      supportingArgument `admitted (.binder `admitted) (.premise 0),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration :=
      `CBCMAC.CBCCombinatorics.mass_cbc_outputs_and_not_cbcBad_on_list_eq
    role := .proofRule .conditionalUniformOutputs
    expandProof := true
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      supportingArgument `prefixFree (.binder `prefixFree) (.premise 0),
      primaryArgument `messages (.binder `messages) .transcript,
      primaryArgument `answers (.binder `answers) (.custom `answers),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.CBCCombinatorics.not_cbcBad_inputs_ne
    role := .proofRule .distinctTerminalInputs
    arguments := #[
      primaryArgument `function (.binder `f) (.custom `function),
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `messages (.binder `messages) .transcript,
      primaryArgument `message (.binder `message) (.custom `message),
      primaryArgument `otherMessage (.binder `other) (.custom `otherMessage),
      primaryArgument `position (.binder `position) (.custom `position),
      primaryArgument `otherPosition (.binder `otherPosition) (.custom `otherPosition),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.CBCCombinatorics.cbcLastInput_injOn
    role := .proofRule .distinctTerminalInputs
    arguments := #[
      primaryArgument `function (.binder `f) (.custom `function),
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `messages (.binder `messages) .transcript,
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.cbcPDS_advantage_le_restrictedCBCPDS_advantage
    role := .proofRule .commonDomainDataProcessing
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction),
      primaryArgument `idealFunction (.binder `idealFunction) (.custom `idealFunction),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.theta_cbc_eq_theta_cbc_queryLimit
    role := .proofRule .restrictionApplicationEquation
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockLimit (.binder `q) (.custom `blockLimit),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.realPDS_eq
    role := .proofRule .restrictionApplicationEquation
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockLimit (.binder `limit) (.custom `blockLimit),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction),
      primaryArgument `result .result .conclusion
    ]
  },
  {
    declaration := `CBCMAC.underlying_restrictedCBCCollisionGame
    role := .proofRule .ignoreGameMBO
    arguments := #[
      primaryArgument `blockForm (.binder `blockForm) (.custom `blockForm),
      primaryArgument `blockBudget (.binder `q) (.custom `blockBudget),
      primaryArgument `roundFunction (.binder `roundFunction) (.custom `roundFunction),
      primaryArgument `result .result .conclusion
    ]
  }
]

def catalog : Catalog :=
  Informalization.Semantics.RandomSystems.catalog ++ overlay

run_cmd
  unless overlay.hasUniqueDeclarations do
    throwError "CBC semantic overlay contains duplicate declarations"
  unless overlay.all Entry.hasUniqueSlots do
    throwError "CBC semantic overlay contains duplicate semantic slots"
  unless profile.hasUniqueRuleOperandSlots do
    throwError "CBC canonical profile contains duplicate rule operand slots"
  unless profile.hasUniqueTheoremPresentations do
    throwError "CBC canonical profile contains duplicate theorem presentations"
  unless profile.hasWellFormedDeclarationNotations do
    throwError "CBC canonical profile contains invalid declaration notation"
  unless profile.theoremPresentations.all (·.isWellFormed) do
    throwError "CBC canonical profile contains an invalid theorem presentation"
  if Informalization.Semantics.RandomSystems.catalog.any fun entry =>
      overlay.any fun cbcEntry => cbcEntry.declaration == entry.declaration then
    throwError "CBC semantic overlay duplicates a reusable Random Systems declaration"

end Informalization.Semantics.CBC

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Canonical

/-!
# Random Systems canonical decoder profile

This module is the only place where the canonical claim decoder knows the
fully qualified declaration vocabulary of the in-tree Random Systems library.
The entries assign mathematical roles and proof-obligation slots; they do not
contain rendered prose or proof-specific display names.
-/

namespace Informalization.Semantics.Canonical.RandomSystemsProfile

open Lean Meta
open Informalization.Semantics.Canonical

/-- Reusable canonical semantics for Random Systems declarations. -/
def profile : DecoderProfile := {
  systemCarrierTypes := #[
    `RandomSystems.PDS,
    `RandomSystems.Ambient.PDS,
    `RandomSystems.Ambient.RandomSystem,
    `RandomSystems.CommonDomain.ProbabilityRandomSystem,
    `RandomSystems.PDS.Behaviour,
    `RandomSystems.RandomFunction
  ]
  uniformRandomFunctions := #[
    `RandomSystems.PDS.urf
  ]
  uniformRandomPermutations := #[
    `RandomSystems.PDS.urp
  ]
  presentationQuotients := #[
    `RandomSystems.Ambient.RandomSystem.ofPDS,
    `RandomSystems.RandomFunction.toPDS,
    `RandomSystems.RandomFunction.toAmbientPDS,
    `RandomSystems.RandomFunction.toRandomSystem,
    `RandomSystems.Ambient.PDS.toRandomSystem
  ]
  converterApplications := #[
    `HSMul.hSMul,
    `RandomSystems.Ambient.RandomSystem.apply,
    `RandomSystems.Ambient.PDS.apply,
    `RandomSystems.Ambient.RandomSystem.applyDDC,
    `RandomSystems.CommonDomain.ProbabilityRandomSystem.apply
  ]
  converterCoercions := #[
    `RandomSystems.Ambient.DDC.asHom,
    `RandomSystems.DomainFilter.toDDC
  ]
  converterSerialCompositions := #[
    `CategoryTheory.CategoryStruct.comp,
    `RandomSystems.Ambient.DDC.serial
  ]
  converterAtoms := #[
    `RandomSystems.Ambient.DDC.queryLimit
  ]
  queryRestrictionConverters := #[
    `RandomSystems.Ambient.DDC.queryLimit
  ]
  declarationNotations := #[{
    declaration := `RandomSystems.Ambient.DDC.queryLimit
    latex := ""
    style := .bracketed
    operandSlots := #[`queryBudget]
  }]
  constructions := #[
    `AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
  ]
  specificationSingletons := #[
    `Singleton.singleton
  ]
  transforms := #[
    `Probability.Distribution.fTransform
  ]
  queryTransformers := #[
    `RandomSystems.System.filterQueries
  ]
  systemQueryRestrictions := #[
    `RandomSystems.filterQueries,
    `RandomSystems.Switching.limit
  ]
  gameQueryRestrictions := #[
    `RandomSystems.Switching.limitGame,
    `RandomSystems.PDG.filterDom
  ]
  gameConverterApplications := #[
    `HSMul.hSMul
  ]
  blindGameTransforms := #[
    `RandomSystems.PDG.blind
  ]
  mboEnhancements := #[
    `RandomSystems.PDS.adjoin
  ]
  gameForgetting := #[
    `RandomSystems.PDG.forget,
    `RandomSystems.PDG.underlying
  ]
  conditionalEquivalence := #[
    `RandomSystems.PDG.CondEquiv,
    `RandomSystems.ConditionalEquivalence.ConditionallyEquivalent
  ]
  statisticalDistance := #[
    `EDist.edist,
    `Dist.dist
  ]
  fullyDefinedAdvantage := #[
    `RandomSystems.PDS.advFullyDefined
  ]
  distinguishingAdvantage := #[
    `RandomSystems.Ambient.PDS.advantage,
    `RandomSystems.PDS.advantage,
    `RandomSystems.Ambient.RandomSystem.advantage
  ]
  winningProbability := #[
    `RandomSystems.PDG.supWinProb
  ]
  blindWinningProbability := #[
    `RandomSystems.PDG.blindSupWinProb
  ]
  scalarCoercions := #[
    `ENNReal.ofReal
  ]
  nonnegativityPredicates := #[
    `Probability.Distribution.NonNeg
  ]
  weightFunctions := #[
    `Probability.Distribution.weight
  ]
  rules := #[
    {
      declaration :=
        `RandomSystems.CommonDomain.ProbabilityRandomSystem.edist_apply_le
      rule := .custom `commonDomainDataProcessing
      operands := #[
        { selector := .binder `converter, slot := `converter },
        { selector := .binder `left, slot := `leftSystem },
        { selector := .binder `right, slot := `rightSystem }
      ]
    },
    {
      declaration :=
        `RandomSystems.Ambient.RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent
      rule := .conditionalEquivalenceToBlindWinning
      operands := #[
        { selector := .binder `left, slot := `ambientLeftSystem },
        { selector := .binder `right, slot := `ambientRightSystem },
        { selector := .binder `game, slot := `game },
        { selector := .binder `target, slot := `targetSystem },
        { selector := .binder `domain, slot := `domain }
      ]
      proofSlots := #[.custom `gameDomain, .custom `targetDomain,
        .conditionalEquivalence, .custom `refinement]
    },
    {
      declaration := `RandomSystems.PDG.condEquiv_filterQueries
      rule := .preserveConditionalEquivalence
      operands := #[
        { selector := .binder `q, slot := `queryBudget },
        { selector := .binder `G, slot := `game },
        { selector := .binder `T, slot := `target }
      ]
      proofSlots := #[
        .sourceTotal,
        .targetTotal,
        .conditionalEquivalence
      ]
    },
    {
      declaration := `RandomSystems.PDG.condEquiv_filterDom
      rule := .preserveConditionalEquivalence
      operands := #[
        { selector := .binder `P, slot := `condition },
        { selector := .binder `G, slot := `game },
        { selector := .binder `T, slot := `target }
      ]
      proofSlots := #[
        .sideCondition,
        .sourceTotal,
        .targetTotal,
        .conditionalEquivalence
      ]
    },
    {
      declaration :=
        `RandomSystems.PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
      rule := .conditionalEquivalenceToBlindWinning
      operands := #[
        { selector := .binder `game, slot := `game },
        { selector := .binder `target, slot := `targetSystem },
        { selector := .binder `domain, slot := `domain },
        { selector := .binder `epsilon, slot := `errorBound }
      ]
      proofSlots := #[.custom `gameNormalized, .custom `targetNormalized,
        .custom `gameDomain, .custom `targetDomain,
        .conditionalEquivalence, .custom `blindWinningBound]
    },
    {
      declaration := `RandomSystems.PDG.supWinProb_blind_filterDom_fTransform_le
      rule := .establishBlindWinningBound
      operands := #[
        { selector := .binder `source, slot := `sourceDistribution },
        { selector := .binder `toGame, slot := `gameFamily },
        { selector := .binder `allowed, slot := `allowedHistories },
        { selector := .binder `bad, slot := `badEvent },
        { selector := .binder `bound, slot := `errorBound }
      ]
      proofSlots := #[.sideCondition, .sideCondition, .sideCondition,
        .sideCondition, .sourceNonnegative, .sideCondition, .custom `badMassBound]
    },
    {
      declaration :=
        `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
      rule := .conditionalEquivalenceToBlindWinning
      operands := #[
        { selector := .binder `G, slot := `game },
        { selector := .binder `T, slot := `target }
      ]
      proofSlots := #[
        .sourceNonnegative,
        .targetNonnegative,
        .equalWeight,
        .conditionalEquivalence
      ]
    },
    {
      declaration := `RandomSystems.PDG.conditional_equivalence_theorem_blind
      rule := .conditionalEquivalenceToBlindWinning
      operands := #[
        { selector := .binder `G, slot := `game },
        { selector := .binder `T, slot := `target }
      ]
      proofSlots := #[
        .sourceNonnegative,
        .targetNonnegative,
        .equalWeight,
        .sideCondition,
        .sideCondition,
        .sideCondition,
        .conditionalEquivalence
      ]
    },
    {
      declaration := `RandomSystems.PDG.conditional_equivalence_theorem
      rule := .conditionalEquivalenceToWinning
      operands := #[
        { selector := .binder `G, slot := `game },
        { selector := .binder `T, slot := `target }
      ]
      proofSlots := #[
        .sourceNonnegative,
        .targetNonnegative,
        .equalWeight,
        .conditionalEquivalence
      ]
    },
    {
      declaration := `RandomSystems.PDS.conditional_equivalence_theorem_adjoin
      rule := .conditionalEquivalenceToWinning
      operands := #[
        { selector := .binder `S, slot := `source },
        { selector := .binder `T, slot := `target },
        { selector := .binder `A, slot := `condition }
      ]
      proofSlots := #[
        .sourceNonnegative,
        .targetNonnegative,
        .equalWeight,
        .conditionalEquivalence
      ]
    },
    {
      declaration := `RandomSystems.Switching.uniform_function_collision_on_finset_le
      rule := .custom `collisionProbabilityBound
      operands := #[
        { selector := .binder `X, slot := `alphabet },
        { selector := .binder `S, slot := `queriedSet }
      ]
    },
    {
      declaration := `Probability.Counting.uniform_mass_walk_repeat_le
      rule := .custom `collisionCounting
      operands := #[
        { selector := .binder `par, slot := `parentMap },
        { selector := .binder `g, slot := `walkStep },
        { selector := .binder `x₀, slot := `initialState },
        { selector := .binder `rank, slot := `rank },
        { selector := .binder `inp, slot := `siteInput }
      ]
      formula? := some .walkCollisionBound
    },
    {
      declaration := `ENNReal.ofReal_le_ofReal
      rule := .custom `scalarClosure
      operands := #[
        { selector := .binder `p, slot := `lower },
        { selector := .binder `q, slot := `upper }
      ]
      formula? := some .scalarMonotonicity
      proofSlots := #[.sideCondition]
    },
    {
      declaration := `Probability.Counting.birthday_bound
      rule := .custom `birthdayBound
      operands := #[
        { selector := .binder `N, slot := `sampleSpaceCardinality },
        { selector := .binder `q, slot := `sampleSize }
      ]
      proofSlots := #[.queryBudget, .sideCondition]
    },
    {
      declaration := `RandomSystems.PDG.blindSupWinProb_le_of_forall
      rule := .custom `blindWinningToNonadaptive
      operands := #[
        { selector := .binder `G, slot := `game },
        { selector := .binder `c, slot := `pointwiseBound }
      ]
      proofSlots := #[.sideCondition]
    },
    {
      declaration := `RandomSystems.Switching.blindSupWinProb_limit_urf_collision_le
      rule := .establishBlindWinningBound
      operands := #[
        { selector := .binder `X, slot := `alphabet },
        { selector := .binder `q, slot := `queryBudget }
      ]
    },
    {
      declaration := `RandomSystems.Switching.limit_urf_collision_condEquiv_limit_urp
      rule := .preserveConditionalEquivalence
      operands := #[
        { selector := .binder `X, slot := `alphabet },
        { selector := .binder `q, slot := `queryBudget }
      ]
    },
    {
      declaration := `RandomSystems.Switching.urf_collision_condEquiv_urp
      rule := .establishConditionalEquivalence
      operands := #[
        { selector := .binder `X, slot := `alphabet }
      ]
    }
  ]
}

run_cmd
  unless profile.hasUniqueRuleOperandSlots do
    throwError "Random Systems canonical profile contains duplicate rule operand slots"
  unless profile.hasWellFormedDeclarationNotations do
    throwError "Random Systems canonical profile contains invalid declaration notation"

def decodeSystem (expression : Expr) : MetaM SystemTerm :=
  Canonical.decodeSystem profile expression

def decodeGame (expression : Expr) : MetaM GameTerm :=
  Canonical.decodeGame profile expression

def decodeBound (expression : Expr) : MetaM BoundTerm :=
  Canonical.decodeBound profile expression

def decodeClaim? (expression : Expr) : MetaM (Option Claim) :=
  Canonical.decodeClaim? profile expression

def decodeDerivation? (expression : Expr) : MetaM (Option DerivationApplication) :=
  Canonical.decodeDerivation? profile expression

end Informalization.Semantics.Canonical.RandomSystemsProfile

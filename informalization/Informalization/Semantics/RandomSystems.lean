/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Registry

/-!
# Random Systems semantic registrations

This optional adapter assigns typed cryptographic roles to fully qualified
declarations owned by the `abstract-crypto` Random Systems library.  The
package remains standalone: declaration names are stable registry keys and
are validated when their applications are recovered in the source project's
elaborated environment.

The entries contain no English templates or local-variable-name tests.
Application declarations such as CBC are adapters onto the same generic
system, converter, distance, collision, and construction roles; they do not
extend the generic ontology or grammar.
-/

namespace Informalization.Semantics.RandomSystems

open Informalization.Semantics
open Informalization.Semantics.Registry

private def primary (selector : ArgumentSelector) (role : ArgumentRole) :
    ArgumentBinding := { selector, role }

private def supporting (selector : ArgumentSelector) (role : ArgumentRole) :
    ArgumentBinding := { selector, role, salience := .supporting }

private def implementation (selector : ArgumentSelector) (role : ArgumentRole) :
    ArgumentBinding := { selector, role, salience := .implementation }

private def namedPrimary (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot }

private def namedSupporting (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot, salience := .supporting }

private def namedImplementation (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot, salience := .implementation }

/-! The catalog is the profile boundary used when the source project is
elaborated in a separate environment.  The same values are also persisted
below for source modules that import this adapter directly. -/

def catalog : Catalog := #[
  {
    declaration :=
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
    role := .proposition .construction
    arguments := #[
      namedPrimary `sourceSpecification (.binder `source)
        (.custom `sourceSpecification),
      namedPrimary `converter (.binder `converter) .converter,
      namedPrimary `targetSpecification (.binder `target)
        (.custom `targetSpecification),
      namedPrimary `errorBound (.binder `error) .bound
    ]
  },
  {
    declaration := `RandomSystems.Ambient.RandomSystem.ofPDS
    role := .system .presentationQuotient
    arguments := #[
      namedPrimary `presentation (.binder `system) .sourceSystem
    ]
  },
  {
    declaration := `RandomSystems.Ambient.RandomSystem.apply
    role := .system .converterApplication
    arguments := #[
      namedPrimary `converter (.explicit 0) .converter,
      namedPrimary `system (.explicit 1) .sourceSystem
    ]
  },
  {
    declaration := `RandomSystems.Ambient.PDS.apply
    role := .system .converterApplication
    arguments := #[
      namedPrimary `converter (.binder `converter) .converter,
      namedPrimary `system (.binder `system) .sourceSystem
    ]
  },
  {
    declaration := `RandomSystems.CommonDomain.ProbabilityRandomSystem.apply
    role := .system .converterApplication
    arguments := #[
      namedPrimary `converter (.binder `converter) .converter,
      namedPrimary `system (.binder `system) .sourceSystem
    ]
  },
  {
    declaration := `RandomSystems.Ambient.DDC.serial
    role := .converter .serialComposition
    arguments := #[
      namedPrimary `outerConverter (.binder `outer) (.custom `outerConverter),
      namedPrimary `innerConverter (.binder `inner) (.custom `innerConverter)
    ]
  },
  {
    declaration := `EDist.edist
    role := .quantity .statisticalDistance
    arguments := #[
      namedPrimary `leftSystem (.explicit 0) .sourceSystem,
      namedPrimary `rightSystem (.explicit 1) .targetSystem
    ]
    argumentTypeConstraints := #[
      { role := .sourceSystem, allowedTypeHeads := #[
          `RandomSystems.Ambient.RandomSystem,
          `RandomSystems.CommonDomain.ProbabilityRandomSystem,
          `RandomSystems.PDS.Behaviour] },
      { role := .targetSystem, allowedTypeHeads := #[
          `RandomSystems.Ambient.RandomSystem,
          `RandomSystems.CommonDomain.ProbabilityRandomSystem,
          `RandomSystems.PDS.Behaviour] }
    ]
  },
  {
    declaration := `Dist.dist
    role := .quantity .statisticalDistance
    arguments := #[
      namedPrimary `leftSystem (.explicit 0) .sourceSystem,
      namedPrimary `rightSystem (.explicit 1) .targetSystem
    ]
    argumentTypeConstraints := #[
      { role := .sourceSystem,
        allowedTypeHeads := #[`RandomSystems.Ambient.RandomSystem] },
      { role := .targetSystem,
        allowedTypeHeads := #[`RandomSystems.Ambient.RandomSystem] }
    ]
  },
  {
    declaration := `RandomSystems.PDS.advantage
    role := .quantity .distinguishingAdvantage
    arguments := #[
      namedPrimary `leftSystem (.binder `S) .sourceSystem,
      namedPrimary `rightSystem (.binder `T) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.Ambient.PDS.advantage
    role := .quantity .distinguishingAdvantage
    arguments := #[
      namedPrimary `leftSystem (.binder `left) .sourceSystem,
      namedPrimary `rightSystem (.binder `right) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.PDS
    role := .entity .randomSystem
  },
  {
    declaration := `RandomSystems.PDG
    role := .entity .game
  },
  {
    declaration := `RandomSystems.ConditionalEquivalence.ConditionallyEquivalent
    role := .proposition .conditionalEquivalence
    arguments := #[
      namedPrimary `game (.binder `game) .game,
      namedPrimary `targetSystem (.binder `target) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.System.DDS
    role := .entity .randomSystem
  },
  {
    declaration := `RandomSystems.System.DDE.Total
    role := .entity .environment
  },
  {
    declaration := `RandomSystems.PDS.urf
    role := .system .uniformRandomFunction
    arguments := #[
      primary (.explicit 0) .inputSpace,
      primary (.explicit 1) .outputSpace
    ]
  },
  {
    declaration := `RandomSystems.PDS.urp
    role := .system .uniformRandomPermutation
    arguments := #[primary (.explicit 0) .alphabet]
  },
  {
    declaration := `RandomSystems.System.filterQueries
    role := .converter .queryRestriction
    arguments := #[primary (.binder `q) .queryBudget]
  },
  {
    declaration := `RandomSystems.filterQueries
    role := .converter .queryRestriction
    arguments := #[primary (.binder `q) .queryBudget]
  },
  {
    declaration := `RandomSystems.Ambient.DDC.queryLimit
    role := .converter .queryRestriction
    arguments := #[primary (.binder `q) .queryBudget]
  },
  {
    declaration := `Probability.Distribution.fTransform
    role := .system .transform
    arguments := #[
      primary (.binder `f) (.custom `transformation),
      primary (.binder `X) .probabilityLaw
    ]
  },
  {
    declaration := `RandomSystems.PDS.adjoin
    role := .game .enhanceWithMBO
    arguments := #[
      primary (.binder `S) .sourceSystem,
      primary (.binder `A) .condition
    ]
  },
  {
    declaration := `RandomSystems.PDG.forget
    role := .system .forgetGame
    arguments := #[primary (.binder `G) .game]
  },
  {
    declaration := `RandomSystems.Switching.limit
    role := .system .queryRestriction
    arguments := #[
      primary (.binder `q) .queryBudget,
      primary (.binder `S) .sourceSystem
    ]
  },
  {
    declaration := `RandomSystems.Switching.limitGame
    role := .system .queryRestriction
    arguments := #[
      primary (.binder `q) .queryBudget,
      primary (.binder `G) .game
    ]
  },
  {
    declaration := `RandomSystems.Switching.collisionCondition
    role := .entity .collisionCondition
  },
  {
    declaration := `RandomSystems.PDS.advFullyDefined
    role := .quantity .distinguishingAdvantage
    arguments := #[
      primary (.binder `S) .sourceSystem,
      primary (.binder `T) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.PDG.supWinProb
    role := .quantity .winningProbability
    arguments := #[primary (.binder `game) .game]
  },
  {
    declaration := `RandomSystems.PDG.blindSupWinProb
    role := .quantity .blindWinningProbability
    arguments := #[primary (.binder `G) .game]
  },
  {
    declaration := `Probability.probBad
    role := .quantity .badEventProbability
    arguments := #[
      primary (.binder `D) .probabilityLaw,
      primary (.binder `B) .badEvent
    ]
  },
  {
    declaration := `LE.le
    role := .proposition .upperBound
    arguments := #[
      primary (.explicit 0) .subject,
      primary (.explicit 1) .bound
    ]
  },
  {
    declaration := `RandomSystems.PDG.CondEquiv
    role := .proposition .conditionalEquivalence
    arguments := #[
      primary (.binder `G) .game,
      primary (.binder `T) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.PDG.EquivalentAsGames
    role := .proposition .gameEquivalence
    arguments := #[
      primary (.binder `left) .sourceSystem,
      primary (.binder `right) .targetSystem
    ]
  },
  {
    declaration := `RandomSystems.PDS.advFullyDefined_triangle
    role := .proofRule .triangleHybrid
    arguments := #[
      primary (.binder `S) .sourceSystem,
      primary (.binder `T) (.custom `intermediateSystem),
      primary (.binder `U) .targetSystem,
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDS.h_coefficient_theorem
    role := .proofRule .hTechnique
    arguments := #[
      primary (.binder `S) .realSystem,
      primary (.binder `T) .idealSystem,
      primary (.binder `Bad) .badEvent,
      primary (.binder `eps) .errorTerm,
      primary (.binder `δb) .bound,
      implementation (.binder `hS) (.premise 0),
      implementation (.binder `hT) (.premise 1),
      implementation (.binder `hw) (.premise 2),
      implementation (.binder `hT1) (.premise 3),
      supporting (.binder `h_ratio) (.premise 4),
      supporting (.binder `h_bad) (.premise 5),
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDS.h_coefficient_theorem_eq_on_good
    role := .proofRule .hTechnique
    arguments := #[
      primary (.binder `S) .realSystem,
      primary (.binder `T) .idealSystem,
      primary (.binder `Bad) .badEvent,
      primary (.binder `δb) .bound,
      implementation (.binder `hS) (.premise 0),
      implementation (.binder `hT) (.premise 1),
      implementation (.binder `hw) (.premise 2),
      implementation (.binder `hT1) (.premise 3),
      supporting (.binder `h_eq) (.premise 4),
      supporting (.binder `h_bad) (.premise 5),
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.fundamental_lemma_of_game_playing
    role := .proofRule .gamePlayingFundamentalLemma
    arguments := #[
      primary (.binder `G) .sourceSystem,
      primary (.binder `H) .targetSystem,
      implementation (.binder `hG) (.premise 0),
      implementation (.binder `hH) (.premise 1),
      implementation (.binder `hw) (.premise 2),
      supporting (.binder `h) (.premise 3),
      primary .result .conclusion
    ]
  },
  {
    declaration :=
      `RandomSystems.CommonDomain.ProbabilityRandomSystem.edist_apply_le
    role := .proofRule .commonDomainDataProcessing
    arguments := #[
      namedPrimary `converter (.binder `converter) .converter,
      namedPrimary `leftSystem (.binder `left) .sourceSystem,
      namedPrimary `rightSystem (.binder `right) .targetSystem,
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration :=
      `RandomSystems.Ambient.RandomSystem.advantage_le_supWinProb_blind_of_conditionallyEquivalent
    role := .proofRule .conditionalEquivalenceToBlindWinning
    arguments := #[
      namedPrimary `ambientLeftSystem (.binder `left) (.custom `ambientLeftSystem),
      namedPrimary `ambientRightSystem (.binder `right) (.custom `ambientRightSystem),
      namedPrimary `game (.binder `game) .game,
      namedPrimary `targetSystem (.binder `target) .targetSystem,
      namedPrimary `domain (.binder `domain) (.custom `domain),
      namedImplementation `gameDomain (.binder `gameDomain) (.premise 0),
      namedImplementation `targetDomain (.binder `targetDomain) (.premise 1),
      namedSupporting `conditionalEquivalence
        (.binder `equivalent) (.premise 2),
      namedSupporting `refinement (.binder `refinement) (.premise 3),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Ambient.RandomSystem.edist_eq_advantage
    role := .proofRule .rewriting
    arguments := #[
      namedPrimary `leftSystem (.binder `left) .sourceSystem,
      namedPrimary `rightSystem (.binder `right) .targetSystem,
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Ambient.RandomSystem.advantage_ofPDS
    role := .proofRule .rewriting
    arguments := #[
      namedPrimary `leftSystem (.binder `left) .sourceSystem,
      namedPrimary `rightSystem (.binder `right) .targetSystem,
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Ambient.RandomSystem.apply_ofPDS_eq
    role := .proofRule .rewriting
    arguments := #[
      namedPrimary `converter (.binder `converter) .converter,
      namedPrimary `system (.binder `system) .sourceSystem,
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Ambient.PDS.apply_serial_eq
    role := .proofRule .rewriting
    arguments := #[
      namedPrimary `outerConverter (.binder `outer) (.custom `outerConverter),
      namedPrimary `innerConverter (.binder `inner) (.custom `innerConverter),
      namedPrimary `system (.binder `system) .sourceSystem,
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.condEquiv_filterQueries
    role := .proofRule .conditionalEquivalenceUnderRestriction
    arguments := #[
      namedPrimary `queryBudget (.binder `q) .queryBudget,
      namedPrimary `game (.binder `G) .game,
      namedPrimary `target (.binder `T) .targetSystem,
      namedImplementation `sourceTotal (.binder `hG) (.premise 0),
      namedImplementation `targetTotal (.binder `hT) (.premise 1),
      namedSupporting `conditionalEquivalence (.binder `h) (.premise 2),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.condEquiv_filterDom
    role := .proofRule .conditionalEquivalenceUnderRestriction
    arguments := #[
      namedPrimary `predicate (.binder `P) .condition,
      namedPrimary `game (.binder `G) .game,
      namedPrimary `target (.binder `T) .targetSystem,
      namedImplementation `prefixClosed (.binder `hP) (.premise 0),
      namedImplementation `sourceTotal (.binder `hG) (.premise 1),
      namedImplementation `targetTotal (.binder `hT) (.premise 2),
      namedSupporting `conditionalEquivalence (.binder `h) (.premise 3),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.conditional_equivalence_theorem
    role := .proofRule .conditionalEquivalence
    arguments := #[
      namedPrimary `game (.binder `G) .game,
      namedPrimary `target (.binder `T) .targetSystem,
      namedImplementation `sourceNonnegative (.binder `hG) (.premise 0),
      namedImplementation `targetNonnegative (.binder `hT) (.premise 1),
      namedImplementation `equalWeight (.binder `hw) (.premise 2),
      namedSupporting `conditionalEquivalence (.binder `hCE) (.premise 3),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDS.conditional_equivalence_theorem_adjoin
    role := .proofRule .conditionalEquivalence
    arguments := #[
      namedPrimary `source (.binder `S) .sourceSystem,
      namedPrimary `target (.binder `T) .targetSystem,
      namedPrimary `condition (.binder `A) .condition,
      namedImplementation `sourceNonnegative (.binder `hS) (.premise 0),
      namedImplementation `targetNonnegative (.binder `hT) (.premise 1),
      namedImplementation `equalWeight (.binder `hw) (.premise 2),
      namedSupporting `conditionalEquivalence (.binder `hCE) (.premise 3),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.conditional_equivalence_theorem_blind
    role := .proofRule .conditionalEquivalenceToBlindWinning
    arguments := #[
      namedPrimary `game (.binder `G) .game,
      namedPrimary `target (.binder `T) .targetSystem,
      namedImplementation `sourceNonnegative (.binder `hG) (.premise 0),
      namedImplementation `targetNonnegative (.binder `hT) (.premise 1),
      namedImplementation `equalWeight (.binder `hw) (.premise 2),
      namedImplementation `targetNormalized (.binder `hT1) (.premise 3),
      namedImplementation `sourceDomain (.binder `hdomG) (.premise 4),
      namedImplementation `targetDomain (.binder `hdomT) (.premise 5),
      namedSupporting `conditionalEquivalence (.binder `hCE) (.premise 6),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv
    role := .proofRule .conditionalEquivalenceToBlindWinning
    arguments := #[
      namedPrimary `game (.binder `G) .game,
      namedPrimary `target (.binder `T) .targetSystem,
      namedImplementation `sourceNonnegative (.binder `hG) (.premise 0),
      namedImplementation `targetNonnegative (.binder `hT) (.premise 1),
      namedImplementation `equalWeight (.binder `hw) (.premise 2),
      namedSupporting `conditionalEquivalence (.binder `hCE) (.premise 3),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration :=
      `RandomSystems.PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
    role := .proofRule .conditionalEquivalenceToBlindWinning
    arguments := #[
      namedPrimary `game (.binder `game) .game,
      namedPrimary `targetSystem (.binder `target) .targetSystem,
      namedPrimary `domain (.binder `domain) (.custom `domain),
      namedImplementation `gameNormalized
        (.binder `gameProbability) (.premise 0),
      namedImplementation `targetNormalized
        (.binder `targetProbability) (.premise 1),
      namedImplementation `gameDomain (.binder `gameDomain) (.premise 2),
      namedImplementation `targetDomain (.binder `targetDomain) (.premise 3),
      namedSupporting `conditionalEquivalence
        (.binder `equivalent) (.premise 4),
      namedPrimary `errorBound (.binder `epsilon) .bound,
      namedSupporting `blindWinningBound
        (.binder `supWinProb_blind_le) (.premise 5),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.supWinProb_blind_filterDom_fTransform_le
    role := .proofRule .blindWinningToNonadaptive
    arguments := #[
      namedPrimary `sourceDistribution (.binder `source) .probabilityLaw,
      namedPrimary `gameFamily (.binder `toGame) (.custom `gameFamily),
      namedPrimary `allowedHistories (.binder `allowed) .condition,
      namedPrimary `badCondition (.binder `bad) .badEvent,
      namedPrimary `errorBound (.binder `bound) .bound,
      namedSupporting `fixedScheduleBound (.binder `badMass_le) (.premise 6),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `Probability.statDist_triangle
    role := .proofRule .triangleHybrid
    arguments := #[primary .result .conclusion]
  },
  {
    declaration := `Probability.Counting.birthday_bound
    role := .proofRule .birthdayBound
    arguments := #[
      primary (.binder `N) (.custom `sampleSpaceCardinality),
      primary (.binder `q) .queryBudget,
      implementation (.binder `h_le) (.premise 0),
      implementation (.binder `h_pos) (.premise 1),
      primary .result .conclusion
    ]
  },
  {
    declaration := `Probability.Counting.uniform_perm_consistent_mass_eq
    role := .proofRule .counting
    arguments := #[
      primary (.binder `q) .queryBudget,
      primary (.binder `xs) (.custom `inputAssignment),
      primary (.binder `ys) (.custom `outputAssignment),
      supporting (.binder `hx) (.premise 0),
      supporting (.binder `hy) (.premise 1),
      implementation (.binder `h_le) (.premise 2),
      primary .result .conclusion
    ]
  },
  {
    declaration := `Probability.Counting.uniform_mass_walk_repeat_le
    role := .proofRule .counting
    arguments := #[
      namedPrimary `parent (.binder `par) (.custom `parentMap),
      namedPrimary `step (.binder `g) (.custom `walkStep),
      namedPrimary `initial (.binder `x₀) (.custom `initialState),
      namedPrimary `rank (.binder `rank) (.custom `rank),
      namedPrimary `input (.binder `inp) (.custom `siteInput),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `ENNReal.ofReal_le_ofReal
    role := .proofRule .scalarClosure
    expansionOnly := true
    arguments := #[
      namedPrimary `lower (.binder `p) .errorTerm,
      namedPrimary `upper (.binder `q) .bound,
      namedSupporting `estimate (.binder `h) (.premise 0),
      namedPrimary `result .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.uniform_function_collision_on_finset_le
    role := .proofRule .collisionProbabilityBound
    arguments := #[
      primary (.binder `S) (.custom `queriedSet),
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.urf_collision_condEquiv_urp
    role := .proofRule .collisionConditionalEquivalence
    arguments := #[
      primary (.binder `X) .alphabet,
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.limit_urf_collision_condEquiv_limit_urp
    role := .proofRule .conditionalEquivalenceUnderRestriction
    arguments := #[
      primary (.binder `X) .alphabet,
      primary (.binder `q) .queryBudget,
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.blindSupWinProb_limit_urf_collision_le
    role := .proofRule .blindWinningBound
    arguments := #[
      primary (.binder `X) .alphabet,
      primary (.binder `q) .queryBudget,
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.PDG.blindSupWinProb_le_of_forall
    role := .proofRule .blindWinningToNonadaptive
    arguments := #[
      primary (.binder `G) .game,
      primary (.binder `c) .bound,
      supporting (.binder `h) (.premise 0),
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.System.transcriptInputs_congr_of_nonAdaptive
    role := .proofRule .nonadaptiveQueriesFixed
    arguments := #[
      supporting (.binder `he) (.premise 0),
      primary (.binder `s) .sourceSystem,
      primary (.binder `s') .targetSystem,
      primary (.binder `n) (.custom `executionLength),
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.forget_limitGame_adjoin
    role := .proofRule .ignoreGameMBO
    arguments := #[
      primary (.binder `q) .queryBudget,
      primary (.binder `S) .sourceSystem,
      primary (.binder `A) .condition,
      primary .result .conclusion
    ]
  },
  {
    declaration := `RandomSystems.Switching.urf_urp_switching
    role := .proofRule (.custom `securityTheorem)
    arguments := #[
      primary (.binder `X) .alphabet,
      primary (.binder `q) .queryBudget,
      primary .result .conclusion
    ]
  }
]

run_cmd
  unless catalog.hasUniqueDeclarations do
    throwError "Random Systems semantic catalog contains duplicate declarations"
  unless catalog.all Entry.hasUniqueSlots do
    throwError "Random Systems semantic catalog contains duplicate semantic slots"
  if catalog.any fun entry => entry.declaration.toString.startsWith "Applications." then
    throwError "the reusable Random Systems catalog contains an application declaration"
  for entry in catalog do
    register entry

end Informalization.Semantics.RandomSystems

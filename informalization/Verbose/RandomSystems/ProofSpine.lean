import Verbose.RandomSystems
import RandomSystems.Technique.ConditionalEquivalence
import RandomSystems.Technique.BlindWinning

/-!
# Reusable Random Systems proof-spine sentences

These forms name generic mathematical transitions used by CBC and other
applications.  They contain no application-specific declaration names.
-/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.RandomSystems.ProofSpine

def transformConditionalLaw :=
  { assertionDescriptor `rs.conditionalEquivalence `transform
      rsTransformConditionalLaw
      Relations.conditionalEquivalence #[
        explicitOperand (role `systemTransform) Ontology.systemTransform,
        explicitOperand (role `gameTransform) Ontology.gameTransform,
        explicitOperand (role `absorption) Ontology.proof,
        explicitOperand (role `conditionalLaw) Ontology.proof]
      "preserve conditional equivalence under one explicit deterministic transformation"
      `CryptoLanguage.Verbose.RandomSystems.ProofSpine.Backend.transformConditionalLaw with
    fixedProofCombinators := #[`RandomSystems.PDG.condEquiv_fTransform] }

def collisionMassBound :=
  assertionDescriptor `rs.collision `massBound
    rsMassBound Relations.upperBound #[
      explicitOperand (role `queries) Ontology.queryList,
      explicitOperand (role `law) Ontology.probabilityLaw,
      explicitOperand (role `collisionEvent) Ontology.collisionEvent,
      explicitOperand (role `bound) Ontology.bound,
      explicitOperand (role `proof) Ontology.proof]
    "bound the exact mass of an explicit query-indexed collision event under a named law"
    `CryptoLanguage.Verbose.RandomSystems.ProofSpine.Backend.collisionMassBound

namespace Backend

def transformConditionalLaw (systemTransform gameTransform absorption
    conditionalLaw : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact RandomSystems.PDG.condEquiv_fTransform $systemTransform
      $gameTransform $absorption $conditionalLaw))

def collisionMassBound (queries law collisionEvent bound proof : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact (show Probability.Distribution.mass $law
      (fun outcome => $collisionEvent outcome $queries) ≤ $bound from $proof)))

end Backend
end CryptoLanguage.Verbose.RandomSystems.ProofSpine

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.RandomSystems.ProofSpine

elab "crypto_verbose_rs_transform_conditional " systemTransform:verboseReference
    ", " gameTransform:verboseReference &"using" absorption:verboseReference
    ", " conditionalLaw:verboseReference : tactic => do
  let systemTransformRef ← decodeReference systemTransform
  let gameTransformRef ← decodeReference gameTransform
  let absorptionRef ← decodeReference absorption
  let conditionalLawRef ← decodeReference conditionalLaw
  runSentenceWith (← getRef) transformConditionalLaw .closeMain #[
      ⟨role `systemTransform, systemTransformRef⟩,
      ⟨role `gameTransform, gameTransformRef⟩,
      ⟨role `absorption, absorptionRef⟩,
      ⟨role `conditionalLaw, conditionalLawRef⟩] #[] <|
    backendAction Backend.transformConditionalLaw
      (systemTransformRef.term, gameTransformRef.term, absorptionRef.term,
        conditionalLawRef.term)

elab "crypto_verbose_rs_collision_mass " queries:verboseReference ", "
    law:verboseReference ", " collisionEvent:verboseReference ", "
    bound:verboseReference &"using"
    proof:verboseReference : tactic => do
  let queriesRef ← decodeReference queries
  let lawRef ← decodeReference law
  let collisionEventRef ← decodeReference collisionEvent
  let boundRef ← decodeReference bound
  let proofRef ← decodeReference proof
  runSentenceWith (← getRef) collisionMassBound .closeMain #[
      ⟨role `queries, queriesRef⟩, ⟨role `law, lawRef⟩,
      ⟨role `collisionEvent, collisionEventRef⟩,
      ⟨role `bound, boundRef⟩, ⟨role `proof, proofRef⟩] #[] <|
    backendAction Backend.collisionMassBound
      (queriesRef.term, lawRef.term, collisionEventRef.term, boundRef.term,
        proofRef.term)

namespace CryptoVerbose

scoped macro &"Transforming" &"the" &"system" &"by"
    systemTransform:verboseReference &"and" &"the" &"game" &"by"
    gameTransform:verboseReference &"preserves" &"conditional" &"equivalence"
    &"using" absorption:verboseReference &"and"
    conditionalLaw:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_transform_conditional $systemTransform,
    $gameTransform using $absorption, $conditionalLaw)

scoped macro &"For" queries:verboseReference "," &"under" law:verboseReference
    "," &"the" &"collision" &"event" collisionEvent:verboseReference &"has"
    &"mass" &"at" &"most" bound:verboseReference &"by" proof:verboseReference : tactic =>
  `(tactic| crypto_verbose_rs_collision_mass $queries, $law, $collisionEvent,
    $bound using $proof)

end CryptoVerbose

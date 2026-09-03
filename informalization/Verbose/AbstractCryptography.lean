import Verbose.Core
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Abstract/Constructive Cryptography sentences

Each elaborator calls exactly one existing deterministic `ac_*` backend.  The
canonical context wording is new; the older `With context ...` spelling remains
owned by the upstream compatibility module and is not emitted here.
-/

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.AbstractCryptography

@[crypto_verbose_sentence] def constructionFrom :=
  { assertionDescriptor `ac.construction `fromProof
      acConstructionFrom
      Relations.construction #[explicitOperand (role `proof) Ontology.proof]
      "close the construction from an explicit checked fact"
      `CryptoLanguage.Verbose.AbstractCryptography.Backend.construct with
    fixedProofCombinators := #[``id,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff] }

@[crypto_verbose_sentence] def equalityFrom :=
  { assertionDescriptor `ac.equality `fromProof
      acEqualityFrom
      Relations.equality #[explicitOperand (role `proof) Ontology.proof]
      "close a converter-attachment equality from an explicit converter equality"
      `CryptoLanguage.Verbose.AbstractCryptography.Backend.equality with
    fixedProofCombinators := #[
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq] }

@[crypto_verbose_sentence] def replaceProtocol := assertionDescriptor `ac.construction `replaceProtocol
  acReplaceProtocol
  Relations.construction #[explicitOperand (role `construction) Ontology.construction,
    explicitOperand (role `equation) Ontology.equation]
  "replace only the converter in a supplied construction"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.replace

@[crypto_verbose_sentence] def compose := assertionDescriptor `ac.construction `compose
  acCompose
  Relations.construction #[explicitOperand (role `firstLeg) Ontology.construction,
    explicitOperand (role `secondLeg) Ontology.construction]
  "compose two constructions in written execution order"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.compose

@[crypto_verbose_sentence] def simulator := descriptor `ac.construction `simulator
  acSimulator .reduction (.replaceMain #[obligation `membership, obligation `distance] #[])
  Relations.construction #[explicitOperand (role `simulator) Ontology.simulator]
  "fix the simulator and expose its membership and distance obligations"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.simulator

@[crypto_verbose_sentence] def contextRight := assertionDescriptor `ac.construction `contextRight
  acContextRight
  Relations.construction #[explicitOperand (role `context) Ontology.context,
    explicitOperand (role `construction) Ontology.construction]
  "extend a construction by a fixed right parallel context"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.contextRight

@[crypto_verbose_sentence] def contextLeft := assertionDescriptor `ac.construction `contextLeft
  acContextLeft
  Relations.construction #[explicitOperand (role `context) Ontology.context,
    explicitOperand (role `construction) Ontology.construction]
  "extend a construction by a fixed left parallel context"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.contextLeft

@[crypto_verbose_sentence] def triangleClose :=
  { assertionDescriptor `ac.distance `triangleClose
      acTriangleClose
      Relations.distanceBound #[
        explicitOperand (role `intermediate) Ontology.intermediate,
        explicitOperand (role `firstBound) Ontology.proof,
        explicitOperand (role `secondBound) Ontology.proof]
      "close an additive distance bound from two proved legs"
      `CryptoLanguage.Verbose.AbstractCryptography.Backend.triangleClose with
    fixedProofCombinators := #[``LE.le.trans, `add_le_add] }

@[crypto_verbose_sentence] def triangleReduce := descriptor `ac.distance `triangleReduce
  acTriangleReduce .reduction
    (.replaceMain #[obligation `firstLeg, obligation `secondLeg] #[])
  Relations.distanceBound #[explicitOperand (role `intermediate) Ontology.intermediate]
  "choose the intermediate and expose the two distance legs"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.triangleReduce

@[crypto_verbose_sentence] def relax := assertionDescriptor `ac.construction `relax
  acRelax Relations.construction #[
    explicitOperand (role `firstLeg) Ontology.construction,
    explicitOperand (role `secondLeg) Ontology.construction,
    explicitOperand (role `compatibility) Ontology.compatibility]
  "compose two construction legs through an explicit compatible relaxation"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.relax

@[crypto_verbose_sentence] def filtered :=
  { assertionDescriptor `ac.construction `filtered
      acFiltered Relations.construction #[
        explicitOperand (role `commutation) Ontology.proof,
        explicitOperand (role `simulatorAdmission) Ontology.proof,
        explicitOperand (role `proof) Ontology.proof]
      "close a filtered construction from explicit commutation, simulator-admission, and equality-or-distance facts"
      `CryptoLanguage.Verbose.AbstractCryptography.Backend.filtered with
    fixedProofCombinators := #[
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_of_eq,
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_epsilonRelaxation_of_distance_le] }

@[crypto_verbose_sentence] def parallel := assertionDescriptor `ac.construction `parallel
  acParallel Relations.construction #[
    explicitOperand (role `leftLeg) Ontology.construction,
    explicitOperand (role `rightLeg) Ontology.construction]
  "combine two exact component constructions in public parallel order"
  `CryptoLanguage.Verbose.AbstractCryptography.Backend.parallel

@[crypto_verbose_sentence] def composeSimulators :=
  { assertionDescriptor `ac.construction `composeSimulators
      acComposeSimulators Relations.construction #[
        explicitOperand (role `firstLeg) Ontology.construction,
        explicitOperand (role `secondLeg) Ontology.construction,
        explicitOperand (role `commutation) Ontology.proof]
      "compose two simulator-target constructions with explicit commutation evidence"
      `CryptoLanguage.Verbose.AbstractCryptography.Backend.composeSimulators with
    fixedProofCombinators := #[
      `AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators] }

namespace Backend

def construct (fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_construct using $fact))

def equality (fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_transport using $fact))

def replace (construction equation : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_transport $construction using $equation))

def compose (first second : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_compose $first, $second))

def simulator (value : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_simulator $value))
  tagCurrentGoals #[`membership, `distance]

def contextRight (context construction : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_context_left $context using $construction))

def contextLeft (context construction : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_context_right $context using $construction))

def triangleClose (intermediate first second : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    exact
      (AbstractCryptography.Categorical.ResourceAlgebra.distance_triangle
        _ $intermediate _).trans (add_le_add $first $second)))

def triangleReduce (intermediate : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_triangle via $intermediate))
  tagCurrentGoals #[`firstLeg, `secondLeg]

def relax (first second compatibility : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_relax using $first, $second with $compatibility))

def filtered (commutation simulatorAdmission fact : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    ac_filtered using $commutation, $simulatorAdmission, $fact))

def parallel (left right : Term) : TacticM Unit := do
  evalTactic (← `(tactic| ac_parallel $left, $right))

def composeSimulators (first second commutation : Term) : TacticM Unit := do
  evalTactic (← `(tactic|
    ac_compose_simulators $first, $second using $commutation))

end Backend
end CryptoLanguage.Verbose.AbstractCryptography

open CryptoLanguage.Verbose
open CryptoLanguage.Verbose.AbstractCryptography

elab (name := internalConstructionFrom) "crypto_verbose_ac_construction_from "
    fact:verboseReference : tactic => do
  let factRef ← decodeReference fact
  runSentenceWith (← getRef) constructionFrom .closeMain
      #[⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.construct (factRef.term)

elab (name := internalEqualityFrom) "crypto_verbose_ac_equality_from "
    fact:verboseReference : tactic => do
  let factRef ← decodeReference fact
  runSentenceWith (← getRef) equalityFrom .closeMain
      #[⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.equality (factRef.term)

elab (name := internalReplace) "crypto_verbose_ac_replace "
    construction:verboseReference &"using" equation:verboseReference : tactic => do
  let constructionRef ← decodeReference construction
  let equationRef ← decodeReference equation
  runSentenceWith (← getRef) replaceProtocol .closeMain
      #[⟨role `construction, constructionRef⟩, ⟨role `equation, equationRef⟩] #[] <|
    backendAction Backend.replace (constructionRef.term, equationRef.term)

elab (name := internalCompose) "crypto_verbose_ac_compose "
    first:verboseReference ", " second:verboseReference : tactic => do
  let firstRef ← decodeReference first
  let secondRef ← decodeReference second
  runSentenceWith (← getRef) compose .closeMain
      #[⟨role `firstLeg, firstRef⟩, ⟨role `secondLeg, secondRef⟩] #[] <|
    backendAction Backend.compose (firstRef.term, secondRef.term)

elab (name := internalSimulator) "crypto_verbose_ac_simulator "
    value:verboseReference : tactic => do
  let valueRef ← decodeReference value
  runSentenceWith (← getRef) simulator (.replaceMain 2)
      #[⟨role `simulator, valueRef⟩] #[] <|
    backendAction Backend.simulator (valueRef.term)

elab (name := internalContextRight) "crypto_verbose_ac_context_right "
    context:verboseReference &"using" construction:verboseReference : tactic => do
  let contextRef ← decodeReference context
  let constructionRef ← decodeReference construction
  runSentenceWith (← getRef) contextRight .closeMain
      #[⟨role `context, contextRef⟩, ⟨role `construction, constructionRef⟩] #[] <|
    backendAction Backend.contextRight (contextRef.term, constructionRef.term)

elab (name := internalContextLeft) "crypto_verbose_ac_context_left "
    context:verboseReference &"using" construction:verboseReference : tactic => do
  let contextRef ← decodeReference context
  let constructionRef ← decodeReference construction
  runSentenceWith (← getRef) contextLeft .closeMain
      #[⟨role `context, contextRef⟩, ⟨role `construction, constructionRef⟩] #[] <|
    backendAction Backend.contextLeft (contextRef.term, constructionRef.term)

elab (name := internalTriangleClose) "crypto_verbose_ac_triangle_close "
    intermediate:verboseReference &"via" first:verboseReference ", "
    second:verboseReference : tactic => do
  let intermediateRef ← decodeReference intermediate
  let firstRef ← decodeReference first
  let secondRef ← decodeReference second
  runSentenceWith (← getRef) triangleClose .closeMain
      #[⟨role `intermediate, intermediateRef⟩, ⟨role `firstBound, firstRef⟩,
        ⟨role `secondBound, secondRef⟩] #[] <|
    backendAction Backend.triangleClose
      (intermediateRef.term, firstRef.term, secondRef.term)

elab (name := internalTriangleReduce) "crypto_verbose_ac_triangle_reduce "
    intermediate:verboseReference : tactic => do
  let intermediateRef ← decodeReference intermediate
  runSentenceWith (← getRef) triangleReduce (.replaceMain 2)
      #[⟨role `intermediate, intermediateRef⟩] #[] <|
    backendAction Backend.triangleReduce (intermediateRef.term)

elab "crypto_verbose_ac_relax " first:verboseReference ", "
    second:verboseReference &"using" compatibility:verboseReference : tactic => do
  let firstRef ← decodeReference first
  let secondRef ← decodeReference second
  let compatibilityRef ← decodeReference compatibility
  runSentenceWith (← getRef) relax .closeMain #[
      ⟨role `firstLeg, firstRef⟩, ⟨role `secondLeg, secondRef⟩,
      ⟨role `compatibility, compatibilityRef⟩] #[] <|
    backendAction Backend.relax
      (firstRef.term, secondRef.term, compatibilityRef.term)

elab "crypto_verbose_ac_filtered " fact:verboseReference &"using"
    commutation:verboseReference &"and" simulatorAdmission:verboseReference : tactic => do
  let factRef ← decodeReference fact
  let commutationRef ← decodeReference commutation
  let simulatorAdmissionRef ← decodeReference simulatorAdmission
  runSentenceWith (← getRef) filtered .closeMain #[
      ⟨role `commutation, commutationRef⟩,
      ⟨role `simulatorAdmission, simulatorAdmissionRef⟩,
      ⟨role `proof, factRef⟩] #[] <|
    backendAction Backend.filtered
      (commutationRef.term, simulatorAdmissionRef.term, factRef.term)

elab "crypto_verbose_ac_parallel " left:verboseReference ", "
    right:verboseReference : tactic => do
  let leftRef ← decodeReference left
  let rightRef ← decodeReference right
  runSentenceWith (← getRef) parallel .closeMain #[
      ⟨role `leftLeg, leftRef⟩, ⟨role `rightLeg, rightRef⟩] #[] <|
    backendAction Backend.parallel (leftRef.term, rightRef.term)

elab "crypto_verbose_ac_compose_simulators " first:verboseReference ", "
    second:verboseReference &"using" commutation:verboseReference : tactic => do
  let firstRef ← decodeReference first
  let secondRef ← decodeReference second
  let commutationRef ← decodeReference commutation
  runSentenceWith (← getRef) composeSimulators .closeMain #[
      ⟨role `firstLeg, firstRef⟩, ⟨role `secondLeg, secondRef⟩,
      ⟨role `commutation, commutationRef⟩] #[] <|
    backendAction Backend.composeSimulators
      (firstRef.term, secondRef.term, commutationRef.term)

namespace CryptoVerbose

scoped macro &"The" &"construction" &"follows" &"from"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_construction_from $fact)

scoped macro &"The" &"equality" &"follows" &"from"
    fact:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_equality_from $fact)

scoped macro &"Replacing" &"the" &"converter" &"in"
    construction:verboseReference &"using" equation:verboseReference
    "," &"we" &"obtain" &"the" &"required"
    &"construction" : tactic =>
  `(tactic| crypto_verbose_ac_replace $construction using $equation)

scoped macro &"The" &"construction" &"follows" &"by" &"composing"
    first:verboseReference &"and" second:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_compose $first, $second)

scoped macro &"We" &"use" value:verboseReference &"to" &"prove"
    &"the" &"construction" : tactic =>
  `(tactic| crypto_verbose_ac_simulator $value)

scoped macro &"With" context:verboseReference &"as" &"the" &"right"
    &"parallel" &"context" "," &"the" &"construction" &"follows" &"from"
    construction:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_context_right $context using $construction)

scoped macro &"With" context:verboseReference &"as" &"the" &"left"
    &"parallel" &"context" "," &"the" &"construction" &"follows" &"from"
    construction:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_context_left $context using $construction)

scoped macro &"The" &"distance" &"bound" &"follows" &"through"
    intermediate:verboseReference &"using" first:verboseReference &"and"
    second:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_triangle_close $intermediate via $first, $second)

scoped macro &"To" &"prove" &"the" &"distance" &"bound" "," &"apply" &"the"
    &"triangle" &"inequality" &"through" intermediate:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_triangle_reduce $intermediate)

scoped macro &"The" &"construction" &"follows" &"by" &"relaxing"
    first:verboseReference &"through" second:verboseReference &"using"
    compatibility:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_relax $first, $second using $compatibility)

scoped macro &"The" &"filtered" &"construction" &"follows" &"from"
    fact:verboseReference &"using" commutation:verboseReference &"and"
    simulatorAdmission:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_filtered $fact using $commutation and
    $simulatorAdmission)

scoped macro &"The" &"construction" &"follows" &"in" &"parallel" &"from"
    left:verboseReference &"and" right:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_parallel $left, $right)

scoped macro &"The" &"construction" &"follows" &"by" &"composing" &"the"
    &"simulators" &"in" first:verboseReference &"and" second:verboseReference
    &"using" commutation:verboseReference : tactic =>
  `(tactic| crypto_verbose_ac_compose_simulators $first, $second using $commutation)

end CryptoVerbose

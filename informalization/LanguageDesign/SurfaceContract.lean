import LanguageDesign.Ontology
import LanguageDesign.Rules

/-!
# Executable canonical surface contract

This typed catalog, rather than a Markdown passage, is the authority for the
accepted surface forms. Every entry fixes its parser context, semantic
identity, bindings, operands, abstract form, and one concrete parser witness.
The prose specification contains only a generated projection of this value.

Lean's parser declarations cannot themselves be assembled from runtime
strings. The conformance suite therefore parses every `parserWitness`
directly from this catalog and separately checks each sentence entry against
its registered semantic descriptor and checked lowering trace.
-/

namespace CryptoLanguage.LanguageDesign.SurfaceContract

open Lean
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Ontology
open CryptoLanguage.LanguageDesign.Rules

inductive ParserContext
  | theoremGiven
  | tactic
deriving Repr, BEq, Inhabited

inductive SemanticOwner
  | theoremBinder (ruleId : RuleId)
  | sentence (ruleId : RuleId)
  | assertionEnvelope
deriving Repr, BEq, Inhabited

structure Hole where
  id : Name
  placeholder : String
deriving Repr, BEq, Inhabited

inductive Piece
  | literal (text : String)
  | hole (value : Hole)
deriving Repr, BEq, Inhabited

structure Template where
  pieces : Array Piece
deriving Repr, BEq, Inhabited

structure Form where
  id : Name
  parserContext : ParserContext
  owner : SemanticOwner
  bindings : Array BindingSchema
  operands : Array OperandSchema
  template : Template
  witnessValues : Array (Name × String)
deriving Repr, BEq, Inhabited

/-- One canonical English realization owned by the shared contract.  A rule
may have more than one form only when the variants have different typed
schemas (for example, `Fix x` and `Fix x with hx : P x`). -/
structure CanonicalForm where
  id : Name
  ruleId : RuleId
  template : Template
deriving Repr, BEq, Inhabited

private def Template.render (template : Template)
    (valueFor : Hole → String) : String :=
  template.pieces.foldl (init := "") fun result piece =>
    result ++ match piece with
      | .literal text => text
      | .hole value => valueFor value

def Template.abstractForm (template : Template) : String :=
  template.render (·.placeholder)

def Template.instantiate (template : Template)
    (values : Array (Name × String)) : String :=
  template.render fun hole =>
    match values.find? (fun value => value.1 == hole.id) with
    | some value => value.2
    | none => hole.placeholder

def Template.instantiateChecked (template : Template)
    (values : Array (Name × String)) : Except String String :=
  template.pieces.toList.foldlM (init := "") fun result piece =>
    match piece with
    | .literal text => pure (result ++ text)
    | .hole hole =>
        match values.find? (fun value => value.1 == hole.id) with
        | some value => pure (result ++ value.2)
        | none => throw s!"canonical surface is missing the `{hole.id}` role"

def Template.holeIds (template : Template) : Array Name :=
  template.pieces.filterMap fun piece => match piece with
    | .literal _ => none
    | .hole value => some value.id

def Form.abstractForm (form : Form) : String :=
  form.template.abstractForm

def Form.parserWitness (form : Form) : String :=
  form.template.instantiate form.witnessValues

def Form.witnessComplete (form : Form) : Bool :=
  let holes := form.template.holeIds
  holes.all fun id => form.witnessValues.any (fun value => value.1 == id)

private def value (id : Name) (text : String) : Name × String := (id, text)
private def hole (id : Name) (placeholder : String) : Piece :=
  .hole ⟨id, placeholder⟩

private def roleHole (id : Name) : Piece := hole id id.toString
private def literal (text : String) : Piece := .literal text
def canonical (id : Name) (ruleId : RuleId)
    (pieces : Array Piece) : CanonicalForm :=
  { id, ruleId, template := ⟨pieces⟩ }

/-! ## Informalization discourse frames

These frames are the executable wording contract for the semantic reader.
Mathematical holes remain typed fragments in the renderer; this catalog owns
only their grammatical order. -/

def informalizationRestrictionRedundancy : CanonicalForm :=
  canonical `informalization.restrictionRedundancy
    proofRestrictionApplicationEquation #[
      literal "The total-block restriction permits the converter to make at most ",
      roleHole `budget,
      literal " calls to its underlying system. Hence the query restriction is redundant:",
      roleHole `equation]

def informalizationIgnoreCollisionMbo : CanonicalForm :=
  canonical `informalization.ignoreCollisionMbo proofIgnoreGameMBO #[
    literal "Consider the collision game ", roleHole `game,
    literal ", whose MBO records a nontrivial collision among the inputs to the round function. Its underlying system is ",
    roleHole `system, literal "."]

def informalizationConditionalEquivalenceReduction : CanonicalForm :=
  canonical `informalization.conditionalEquivalenceReduction
    rsConditionalBlindBound #[
      literal "Because ", roleHole `conditionalEquivalence,
      literal ", the conditional-equivalence theorem gives",
      roleHole `consequence]

/-- This stronger realization is selected only when the recursive checked
support contains a source-licensed collision conditional equivalence and the
restriction-preservation step. The application attestation records the two
mathematical reasons summarized by this sentence. -/
def informalizationCollisionEquivalenceReduction : CanonicalForm :=
  canonical `informalization.collisionEquivalenceReduction
    rsConditionalBlindBound #[
      literal "Consider the collision game ", roleHole `game,
      literal ", whose MBO records a nontrivial collision among the inputs to the round function. Outside the collision event, prefix-freeness makes the final round-function inputs distinct for distinct messages. Their replies are therefore uniform and consistent, exactly as in the ideal system. This remains true under the total-block restriction. Consequently, the original distance is at most the probability of winning the collision game blindly:",
      roleHole `consequence]

/-- The fixed-list explanation is licensed only when a blind-to-non-adaptive
step and the collision-mass estimate occur in the recursive checked support. -/
def informalizationBlindCollisionEstimate : CanonicalForm :=
  canonical `informalization.blindCollisionEstimate rsBlindWinningBound #[
    literal "In a blind strategy, the message list is fixed before any replies are seen. Until the first collision, the next fresh round-function value is uniform over the block space. The collision estimate therefore applies to every admissible list, giving",
    roleHole `bound]

def informalizationCollisionConditionalEquivalence : CanonicalForm :=
  canonical `informalization.collisionConditionalEquivalence
    proofCollisionConditionalEquivalence #[
      literal "The collision game and the target system are conditionally equivalent:",
      roleHole `conditionalEquivalence]

def informalizationPreserveConditionalEquivalence : CanonicalForm :=
  canonical `informalization.preserveConditionalEquivalence
    proofConditionalEquivalenceUnderRestriction #[
      literal "Applying the same restriction to both sides preserves this conditional equivalence:",
      roleHole `conditionalEquivalence]

def informalizationCommonDomainBridge : CanonicalForm :=
  canonical `informalization.commonDomainBridge
    proofCommonDomainDataProcessing #[
      literal "The resulting comparison reduces, by common-domain data processing, to the corresponding normalized PDS advantage."]

def informalizationExactFormula : CanonicalForm :=
  canonical `informalization.exactFormula proofRewriting #[
    literal "Explicitly,", roleHole `formula]

def informalizationBoundConclusion : CanonicalForm :=
  canonical `informalization.boundConclusion proofDistanceBound #[
    literal "Substituting this estimate in the preceding reduction proves the claim:",
    roleHole `conclusion]

def naturalNumberTemplate : Template := ⟨#[
  .literal "Let ", hole `name "NAME", .literal " ∈ ℕ"]⟩

def systemTemplate : Template := ⟨#[
  .literal "Let ", hole `name "NAME", .literal " be the system ",
  hole `value "SYSTEM"]⟩

def mboTemplate : Template := ⟨#[
  .literal "Let ", hole `name "NAME", .literal " be the MBO given by ",
  hole `assignment "ASSIGNMENT",
  .literal ", which is set on a query history exactly when two distinct queries in that history receive the same answer, as shown by ",
  hole `characterization "PROOF"]⟩

def factTemplate : Template := ⟨#[
  .literal "Fact ", hole `name "NAME", .literal ": ",
  hole `body "ASSERTION by PROOF"]⟩

def naturalNumberBinder (name : String) : String :=
  naturalNumberTemplate.instantiate #[value `name name]

def systemBinder (name system : String) : String :=
  systemTemplate.instantiate #[value `name name, value `value system]

def mboDefinition (name assignment characterization : String) : String :=
  mboTemplate.instantiate #[value `name name, value `assignment assignment,
    value `characterization characterization]

def namedFact (name assertion : String) : String :=
  factTemplate.instantiate #[value `name name, value `body assertion]

def naturalNumberForm : Form := {
  id := `naturalNumberBinder
  parserContext := .theoremGiven
  owner := .theoremBinder structuralTheorem
  bindings := #[typedBinding (role `number) naturalNumber]
  operands := #[]
  template := naturalNumberTemplate
  witnessValues := #[value `name "q"]
}

def systemForm : Form := {
  id := `systemBinder
  parserContext := .tactic
  owner := .sentence rsBindSystem
  bindings := #[typedBinding (role `system) pdsLaw]
  operands := #[explicitOperand (role `value) pdsLaw]
  template := systemTemplate
  witnessValues := #[value `name "restrictedURF", value `value "[q] URF(X)"]
}

def mboForm : Form := {
  id := `characterizedMBO
  parserContext := .tactic
  owner := .sentence rsDefineCharacterizedMBO
  bindings := #[typedBinding (role `condition) monotoneCondition]
  operands := #[
    explicitOperand (role `assignment) monotoneCondition,
    explicitOperand (role `characterization) proof]
  template := mboTemplate
  witnessValues := #[value `name "collisionMBO",
    value `assignment "collisionCondition",
    value `characterization "collisionCharacterization"]
}

def factForm : Form := {
  id := `namedFact
  parserContext := .tactic
  owner := .assertionEnvelope
  bindings := #[typedBinding (role `claim) proposition]
  operands := #[
    explicitOperand (role `assertion) proposition,
    explicitOperand (role `proof) proof]
  template := factTemplate
  witnessValues := #[value `name "conditionalLaw",
    value `body
      "The game game is conditionally equivalent to system by conditionalProof"]
}

def forms : Array Form := #[naturalNumberForm, systemForm, mboForm, factForm]

/-! ## Complete canonical-rendering catalog

These templates are the only canonical English word order owned by the
project. Parser declarations and renderers consume this catalog or are checked
against it; they do not create a second prose specification. -/

def canonicalForms : Array CanonicalForm := #[
  informalizationRestrictionRedundancy,
  informalizationIgnoreCollisionMbo,
  informalizationConditionalEquivalenceReduction,
  informalizationCollisionEquivalenceReduction,
  informalizationBlindCollisionEstimate,
  informalizationCollisionConditionalEquivalence,
  informalizationPreserveConditionalEquivalence,
  informalizationCommonDomainBridge,
  informalizationExactFormula,
  informalizationBoundConclusion,
  canonical `structural.goalReminder structuralGoalReminder #[
    literal "It remains to prove ", roleHole `proposition],
  canonical `structural.rewriting proofRewriting #[
    literal "Replacing ", roleHole `old, literal " by ", roleHole `new,
    literal " using ", roleHole `equation, literal " yields ", roleHole `result],
  canonical `structural.fix structuralFix #[
    literal "Fix ", roleHole `object],
  canonical `structural.fixWith structuralFix #[
    literal "Fix ", roleHole `object, literal " with ", roleHole `condition,
    literal " : ", roleHole (Name.str `condition "type")],
  canonical `structural.assume structuralAssume #[
    literal "Assume ", roleHole `assumption, literal " : ",
    roleHole (Name.str `assumption "type")],
  canonical `structural.choose structuralChoose #[
    literal "From ", roleHole `existence, literal ", choose ", roleHole `witness,
    literal " such that ", roleHole `witnessProperty, literal " : ",
    roleHole (Name.str `witnessProperty "type")],
  canonical `structural.conjunction structuralConjunction #[
    literal "From ", roleHole `conjunction, literal ", obtain ", roleHole `leftFact,
    literal " : ", roleHole `left, literal " and ", roleHole `rightFact,
    literal " : ", roleHole `right],

  canonical `ac.constructionFrom acConstructionFrom #[
    literal "The construction follows from ", roleHole `proof],
  canonical `ac.equalityFrom acEqualityFrom #[
    literal "The equality follows from ", roleHole `proof],
  canonical `ac.replaceProtocol acReplaceProtocol #[
    literal "Replacing the converter in ", roleHole `construction,
    literal " using ", roleHole `equation,
    literal ", we obtain the required construction"],
  canonical `ac.compose acCompose #[
    literal "The construction follows by composing ", roleHole `firstLeg,
    literal " and ", roleHole `secondLeg],
  canonical `ac.simulator acSimulator #[
    literal "We use ", roleHole `simulator,
    literal " to prove the construction"],
  canonical `ac.contextRight acContextRight #[
    literal "With ", roleHole `context,
    literal " as the right parallel context, the construction follows from ",
    roleHole `construction],
  canonical `ac.contextLeft acContextLeft #[
    literal "With ", roleHole `context,
    literal " as the left parallel context, the construction follows from ",
    roleHole `construction],
  canonical `ac.triangleClose acTriangleClose #[
    literal "The distance bound follows through ", roleHole `intermediate,
    literal " using ", roleHole `firstBound, literal " and ", roleHole `secondBound],
  canonical `ac.triangleReduce acTriangleReduce #[
    literal "To prove the distance bound, apply the triangle inequality through ",
    roleHole `intermediate],
  canonical `ac.relax acRelax #[
    literal "The construction follows by relaxing ", roleHole `firstLeg,
    literal " through ", roleHole `secondLeg, literal " using ",
    roleHole `compatibility],
  canonical `ac.filtered acFiltered #[
    literal "The filtered construction follows from ", roleHole `proof,
    literal " using ", roleHole `commutation, literal " and ",
    roleHole `simulatorAdmission],
  canonical `ac.parallel acParallel #[
    literal "The construction follows in parallel from ", roleHole `leftLeg,
    literal " and ", roleHole `rightLeg],
  canonical `ac.composeSimulators acComposeSimulators #[
    literal "The construction follows by composing the simulators in ",
    roleHole `firstLeg, literal " and ", roleHole `secondLeg,
    literal " using ", roleHole `commutation],

  canonical `rs.pdsEquivalent rsPdsEquivalent #[
    literal "The PDS laws ", roleHole `left, literal " and ", roleHole `right,
    literal " are observationally equivalent by ", roleHole `proof],
  canonical `rs.gameEquivalent rsGameEquivalent #[
    literal "The games ", roleHole `left, literal " and ", roleHole `right,
    literal " are equivalent by ", roleHole `proof],
  canonical `rs.forgetGame rsForgetGame #[
    literal "Ignoring the MBO of ", roleHole `game, literal " yields ",
    roleHole `system, literal " by ", roleHole `proof],
  canonical `rs.bindSystem rsBindSystem #[
    literal "Let ", roleHole `system, literal " be the system ", roleHole `value],
  canonical `rs.defineCharacterizedMBO rsDefineCharacterizedMBO #[
    literal "Let ", roleHole `condition, literal " be the MBO given by ",
    roleHole `assignment,
    literal ", which is set on a query history exactly when two distinct queries in that history receive the same answer, as shown by ",
    roleHole `characterization],
  canonical `rs.enhanceWithMBO rsEnhanceWithMBO #[
    literal "The game obtained by enhancing ", roleHole `system,
    literal " with the MBO defined by ", roleHole `condition,
    literal " is ", roleHole `game, literal " by ", roleHole `proof],
  canonical `rs.conditionalLaw rsConditionalLaw #[
    literal "The game ", roleHole `game,
    literal " is conditionally equivalent to ", roleHole `system,
    literal " by ", roleHole `proof],
  canonical `rs.transformConditionalLaw rsTransformConditionalLaw #[
    literal "Transforming the system by ", roleHole `systemTransform,
    literal " and the game by ", roleHole `gameTransform,
    literal " preserves conditional equivalence using ", roleHole `absorption,
    literal " and ", roleHole `conditionalLaw],
  canonical `rs.filterConditionalLaw rsFilterConditionalLaw #[
    literal "Filtering both sides by ", roleHole `predicate,
    literal " preserves conditional equivalence using ", roleHole `prefixClosed,
    literal ", ", roleHole `gameNeverRefuses, literal ", ",
    roleHole `systemNeverRefuses, literal ", and ", roleHole `conditionalLaw],
  canonical `rs.filterQueriesConditionalLaw rsFilterQueriesConditionalLaw #[
    literal "Restricting both sides to ", roleHole `queryBudget,
    literal " queries preserves conditional equivalence using ",
    roleHole `gameNeverRefuses, literal ", ", roleHole `systemNeverRefuses,
    literal ", and ", roleHole `conditionalLaw],
  canonical `rs.conditionalBlindBound rsConditionalBlindBound #[
    literal "Using ", roleHole `conditionalLaw, literal ", ",
    roleHole `gameNonnegative, literal ", ", roleHole `idealNonnegative,
    literal ", and ", roleHole `equalWeight,
    literal ", it suffices to prove the blind winning probability of ",
    roleHole `game, literal " is at most ", roleHole `bound],
  canonical `rs.conditionalBlindComparison rsConditionalBlindComparison #[
    literal "The conditional equivalence in ", roleHole `conditionalLaw,
    literal " gives Adv⊥(forget(", roleHole `game, literal "), ",
    roleHole `system, literal ") ≤ νᴺᴬ[", roleHole `winningGame, literal "]"],
  canonical `rs.blindUniversal rsBlindUniversal #[
    literal "To bound the blind winning probability of ", roleHole `game,
    literal ", fix ", roleHole `environment, literal " with ",
    roleHole `nonadaptive, literal " : ", roleHole (Name.str `nonadaptive "type"),
    literal ", and horizon ", roleHole `rounds],
  canonical `rs.blindWinningBound rsBlindWinningBound #[
    literal "The supremum of the winning probabilities achievable by non-adaptive strategies against ",
    roleHole `game, literal " is at most ", roleHole `bound,
    literal " by ", roleHole `proof],
  canonical `rs.commonDomainDataProcessing rsCommonDomainDataProcessing #[
    literal "Applying ", roleHole `converter,
    literal " cannot increase the distance between ", roleHole `left,
    literal " and ", roleHole `right],
  canonical `rs.massBound rsMassBound #[
    literal "For ", roleHole `queries, literal ", under ", roleHole `law,
    literal ", the collision event ", roleHole `collisionEvent,
    literal " has mass at most ", roleHole `bound, literal " by ",
    roleHole `proof],
  canonical `rs.hCoefficient rsHCoefficient #[
    literal "Apply the H-coefficient theorem to ", roleHole `real,
    literal " and ", roleHole `ideal, literal " with bad predicate ",
    roleHole `badPredicate, literal ", ratio loss ", roleHole `ratioLoss,
    literal ", and bad-mass loss ", roleHole `badMassLoss,
    literal " using ", roleHole `realNonnegative, literal ", ",
    roleHole `idealNonnegative, literal ", ", roleHole `equalWeight,
    literal ", and ", roleHole `idealWeightAtMostOne]
]

def canonicalFormsForRule (ruleId : RuleId) : Array CanonicalForm :=
  canonicalForms.filter (·.ruleId == ruleId)

def canonicalFormById? (id : Name) : Option CanonicalForm :=
  canonicalForms.find? (·.id == id)

def documentationBlock : String :=
  let body := String.intercalate "\n"
    (forms.toList.map fun form => form.abstractForm)
  "<!-- GENERATED_VERBOSE_SURFACE_BEGIN -->\n\
This block is generated from `LanguageDesign.SurfaceContract.forms`; edit the Lean contract, not this projection.\n\
```text\n" ++ body ++ "\n```\n\
<!-- GENERATED_VERBOSE_SURFACE_END -->"

/-- Stable review seal for prose requirements not yet represented by a typed
surface form. Any edit to `VERBOSE_SPEC.md` invalidates this value and forces
an explicit implementation review before the test suite can pass again. -/
def specificationReviewDigest (text : String) : UInt64 :=
  text.foldl (init := 14695981039346656037) fun hash character =>
    (hash ^^^ UInt64.ofNat character.toNat) * 1099511628211

/-- Digest of the complete reviewed `VERBOSE_SPEC.md`. This is deliberately
separate from `documentationBlock`: typed forms enforce executable agreement,
while this seal prevents architectural prose edits from passing unnoticed. -/
def reviewedSpecificationDigest : UInt64 := 15269655195118679248

end CryptoLanguage.LanguageDesign.SurfaceContract

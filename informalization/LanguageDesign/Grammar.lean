import LanguageDesign.Basic

/-!
# Language-neutral discourse frames

Frames distinguish the mathematical register in which a rule is stated. The
English frontend chooses words for them; the shared design layer does not.
-/

namespace CryptoLanguage.LanguageDesign

inductive DiscourseRegister
  | structural
  | construction
  | system
  | game
  | law
  | probability
  | counting
deriving Repr, BEq, Inhabited

inductive PredicateFrame
  | followsFrom
  | preserves
  | reducesTo
  | boundedBy
  | equivalentTo
  | introduces
deriving Repr, BEq, Inhabited

structure DiscourseFrame where
  register : DiscourseRegister
  predicate : PredicateFrame
deriving Repr, BEq, Inhabited

/-! ## Indexed abstract grammar

These axes are the executable counterpart of `LANGUAGE_DESIGN` Section 6.
They classify meaning and occurrence independently of English realization. -/

inductive EntityKind
  | carrier
  | interface
  | history
  | system
  | converter
  | game
  | strategy
  | law
  | event
  | quantity
  | specification
  | construction
  | proofObject
  | formalArtifact
deriving Repr, BEq, Hashable, Inhabited

inductive Phase
  | declaration
  | theoremStatement
  | proof
  | exposition
  | diagnostic
deriving Repr, BEq, Hashable, Inhabited

inductive DiscourseAct
  | introduce
  | define
  | describe
  | assume
  | assert
  | derive
  | preserve
  | reduce
  | instantiate
  | split
  | calculate
  | estimate
  | conclude
  | refer
deriving Repr, BEq, Hashable, Inhabited

inductive DefinitionMode
  | abstract
  | denotational
  | operational
  | derived
  | predicate
  | representational
  | notation
  | roleAssignment
deriving Repr, BEq, Hashable, Inhabited

inductive BinderMode
  | given
  | assumed
  | fixedArbitrary
  | chosenWitness
  | implicitCapability
deriving Repr, BEq, Hashable, Inhabited

inductive ClaimMode
  | theoremRoot
  | localResult
  | sideCondition
  | displayedEquation
deriving Repr, BEq, Hashable, Inhabited

inductive ProofPosition
  | opening
  | derivation
  | preservation
  | reduction
  | instantiation
  | caseAnalysis
  | induction
  | calculation
  | estimate
  | closure
deriving Repr, BEq, Hashable, Inhabited

inductive InformationStatus
  | new
  | given
  | active
  | contrastive
  | reintroduced
deriving Repr, BEq, Hashable, Inhabited

inductive DisclosureMode
  | collapsed
  | expanded
  | diagnostic
deriving Repr, BEq, Hashable, Inhabited

structure OccurrenceContext where
  phase : Phase
  act : DiscourseAct
  definitionMode? : Option DefinitionMode := none
  binderMode? : Option BinderMode := none
  claimMode? : Option ClaimMode := none
  proofPosition? : Option ProofPosition := none
  informationStatus : InformationStatus := .active
  visibility : DisclosureMode := .collapsed
deriving Repr, BEq, Hashable, Inhabited

inductive Register
  | formal
  | construction
  | system
  | game
  | law
  | scalar
  | algebra
deriving Repr, BEq, Hashable, Inhabited

inductive DiscourseRelation
  | definition
  | elaboration
  | cause
  | result
  | preservation
  | reduction
  | instantiation
  | bound
  | combination
  | conclusion
deriving Repr, BEq, Hashable, Inhabited

inductive ReferenceForm
  | symbol
  | fullNounPhrase
  | shortNounPhrase
  | safeAnaphor
deriving Repr, BEq, Hashable, Inhabited

inductive Voice
  | active
  | passive
  | copular
deriving Repr, BEq, Hashable, Inhabited

inductive GrammaticalFunction
  | subject
  | directObject
  | indirectObject
  | complement
  | adjunct
deriving Repr, BEq, Hashable, Inhabited

inductive Polarity
  | positive
  | negative
deriving Repr, BEq, Hashable, Inhabited

inductive InferenceStage
  | grounding
  | semanticComposition
  | evidenceNormalization
  | clausePlanning
  | discoursePlanning
  | compression
  | fallback
deriving Repr, BEq, Hashable, Inhabited

end CryptoLanguage.LanguageDesign

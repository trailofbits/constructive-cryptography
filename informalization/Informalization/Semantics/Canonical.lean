/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.IR
import LanguageDesign.Presentation

/-!
# Canonical cryptographic claims

This module is the operand-bearing boundary between elaborated Lean and
language realization.  It records *what* a statement says and *which* proof
rule was applied, but contains no prose templates and no Random Systems
declaration names.

Declaration names enter through `DecoderProfile`.  A theory adapter supplies
one such profile, while the canonical terms, claims, obligations, and rule
applications remain usable by other system models.
-/

namespace Informalization.Semantics.Canonical

open Lean Meta
open Informalization.Semantics

/-- A named transformation together with its exact elaborated operands. -/
structure TransformationTerm where
  source : Expr
  declaration? : Option Name := none
  operands : Array Expr := #[]
  deriving Inhabited, BEq, Repr

/-- A condition attached to a game.  Named conditions retain their declaration
and operands; an opaque condition still retains its exact checked expression. -/
inductive ConditionTerm where
  | opaque (source : Expr)
  | named (source : Expr) (declaration : Name) (operands : Array Expr := #[])
  deriving Inhabited, BEq, Repr

def ConditionTerm.source : ConditionTerm → Expr
  | .opaque source | .named source _ _ => source

/- Canonical converter expressions keep composition and restrictions distinct.
Named leaves retain their checked declaration and operands; an unknown
converter remains exact and opaque. -/
inductive ConverterTerm where
  | opaque (source : Expr)
  | named (source : Expr) (declaration : Name) (operands : Array Expr := #[])
  | restriction (source : Expr) (declaration : Name) (operands : Array Expr := #[])
  | serialComposition (source : Expr) (outer inner : ConverterTerm)
  deriving Inhabited, BEq, Repr

def ConverterTerm.source : ConverterTerm → Expr
  | .opaque source
  | .named source _ _
  | .restriction source _ _
  | .serialComposition source _ _ => source

/- Canonical system and game expressions are mutually recursive because
ignoring a game's MBO produces a system and enhancing a system with an MBO
produces a game. Every constructor stores the exact expression it represents. -/
mutual
  inductive SystemTerm where
    | opaque (source : Expr)
    | named (source : Expr) (declaration : Name) (operands : Array Expr := #[])
    | uniformRandomFunction (source inputSpace outputSpace : Expr)
    | uniformRandomPermutation (source alphabet : Expr)
    | presentationQuotient (source : Expr) (presentation : SystemTerm)
    | converterApplication (source : Expr) (converter : ConverterTerm)
        (underlying : SystemTerm)
    | transform (source : Expr) (transformation : TransformationTerm)
        (underlying : SystemTerm)
    | queryRestriction (source budget : Expr) (underlying : SystemTerm)
    | forgetGame (source : Expr) (game : GameTerm)
    deriving Inhabited, BEq, Repr

  inductive GameTerm where
    | opaque (source : Expr)
    | named (source : Expr) (declaration : Name) (operands : Array Expr := #[])
    | enhanceWithMBO (source : Expr) (system : SystemTerm)
        (condition : ConditionTerm)
    | converterApplication (source : Expr) (converter : ConverterTerm)
        (underlying : GameTerm)
    | transform (source : Expr) (transformation : TransformationTerm)
        (underlying : GameTerm)
    | queryRestriction (source budget : Expr) (underlying : GameTerm)
    deriving Inhabited, BEq, Repr
end

def SystemTerm.source : SystemTerm → Expr
  | .opaque source
  | .named source _ _
  | .uniformRandomFunction source _ _
  | .uniformRandomPermutation source _
  | .presentationQuotient source _
  | .converterApplication source _ _
  | .transform source _ _
  | .queryRestriction source _ _
  | .forgetGame source _ => source

def GameTerm.source : GameTerm → Expr
  | .opaque source
  | .named source _ _
  | .enhanceWithMBO source _ _
  | .converterApplication source _ _
  | .transform source _ _
  | .queryRestriction source _ _ => source

def SystemTerm.isStructured : SystemTerm → Bool
  | .opaque _ => false
  | _ => true

def GameTerm.isStructured : GameTerm → Bool
  | .opaque _ => false
  | _ => true

/-- A set of systems used as a source or target specification.  The first
construction slice recognizes singleton specifications without assigning
semantics to arbitrary set constructors. -/
inductive SpecificationTerm where
  | opaque (source : Expr)
  | singleton (source : Expr) (system : SystemTerm)
  deriving Inhabited, BEq, Repr

def SpecificationTerm.source : SpecificationTerm → Expr
  | .opaque source | .singleton source _ => source

/-- The operands exposed when a query-restricted MBO-enhanced game is recognized. -/
structure RestrictedEnhancedGame where
  source : Expr
  budget : Expr
  baseSystem : SystemTerm
  condition : ConditionTerm
  deriving Inhabited, BEq, Repr

/-- Recognize `restrict budget (enhanceWithMBO system condition)` without
inspecting display names or unfolding the condition. -/
def GameTerm.restrictedEnhancement? : GameTerm → Option RestrictedEnhancedGame
  | .queryRestriction source budget (.enhanceWithMBO _ system condition) =>
      some { source, budget, baseSystem := system, condition }
  | _ => none

/-- Distinguishing quantities which have different observer classes and must
not share notation. -/
inductive AdvantageKind where
  | fullyDefined
  | ambient
  deriving Inhabited, BEq, Repr

/-- Scalar expressions that participate in security bounds.  An unrecognized
formula remains exact rather than being assigned a guessed meaning. -/
inductive BoundTerm where
  | expression (source : Expr)
  | named (source : Expr) (declaration : Name) (operands : Array Expr := #[])
  /-- The standard quadratic collision term `q² / (2 |X|)`. Retaining its
  checked operands keeps presentation independent of notation imports in the
  source theorem's elaboration environment. -/
  | quadraticCollision (source queryBudget alphabet : Expr)
  | statisticalDistance (source : Expr) (left right : SystemTerm)
  | distinguishingAdvantage (source : Expr) (kind : AdvantageKind)
      (real ideal : SystemTerm)
  | winningProbability (source : Expr) (game : GameTerm)
  | blindWinningProbability (source : Expr) (game : GameTerm)
  | coercion (source : Expr) (inner : BoundTerm)
  deriving Inhabited, BEq, Repr

def BoundTerm.source : BoundTerm → Expr
  | .expression source
  | .named source _ _
  | .quadraticCollision source _ _
  | .statisticalDistance source _ _
  | .distinguishingAdvantage source _ _ _
  | .winningProbability source _
  | .blindWinningProbability source _
  | .coercion source _ => source

def BoundTerm.blindWinningGame? : BoundTerm → Option GameTerm
  | .blindWinningProbability _ game => some game
  | .coercion _ inner => inner.blindWinningGame?
  | _ => none

/-- Canonical propositions used by cryptographic proof planning. -/
inductive Claim where
  | systemEquality (source : Expr) (left right : SystemTerm)
  | conditionalEquivalence (source : Expr) (game : GameTerm) (target : SystemTerm)
  | distanceBound (source : Expr) (left right : SystemTerm) (upper : BoundTerm)
  | advantageBound (source : Expr) (kind : AdvantageKind)
      (real ideal : SystemTerm) (upper : BoundTerm)
  | blindWinningBound (source : Expr) (game : GameTerm) (upper : BoundTerm)
  | upperBound (source : Expr) (lower upper : BoundTerm)
  | construction (source : Expr) (sourceSpecification : SpecificationTerm)
      (converter : ConverterTerm) (targetSpecification : SpecificationTerm)
      (error : BoundTerm)
  deriving Inhabited, BEq, Repr

def Claim.source : Claim → Expr
  | .systemEquality source _ _
  | .conditionalEquivalence source _ _
  | .distanceBound source _ _ _
  | .advantageBound source _ _ _ _
  | .blindWinningBound source _ _
  | .upperBound source _ _
  | .construction source _ _ _ _ => source

/-- Every checked proposition has a canonical representation.  Cryptographic
claims use the structured language above; a proposition outside that language
remains an exact opaque leaf rather than preventing its proof rule from taking
part in the recursive proof tree. -/
inductive CanonicalProposition where
  | claim (value : Claim)
  | opaque (source : Expr)
  deriving Inhabited, BEq, Repr

def CanonicalProposition.source : CanonicalProposition → Expr
  | .claim value => value.source
  | .opaque source => source

def CanonicalProposition.claim? : CanonicalProposition → Option Claim
  | .claim value => some value
  | .opaque _ => none

/-- Stable semantic slots for proof obligations.  These are mathematical
roles, not the binder names or prose labels used by an individual theorem. -/
inductive ObligationSlot where
  | sourceTotal
  | targetTotal
  | sourceNonnegative
  | targetNonnegative
  | nonnegative
  | equalWeight
  | conditionalEquivalence
  | monotonicity
  | queryBudget
  | sideCondition
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Stable identity of a proof-valued declaration argument.  Telescope
position is the primary identity; proof ordinal records its position among all
proof arguments, including implicit typeclass evidence.  Neither component
depends on the binder's spelling or on a flattened presentation order. -/
structure ObligationKey where
  telescopePosition : Nat := 0
  proofOrdinal : Nat := 0
  deriving Inhabited, BEq, Repr

/-- A proof-valued theorem argument, kept separately from the conclusion.
`claim?` is populated when the proposition is itself a canonical claim. -/
structure ProofObligation where
  key : ObligationKey := {}
  slot : ObligationSlot
  salience : Salience := .supporting
  proposition : Expr
  evidence : Expr
  claim? : Option Claim := none
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A checked, non-proof operand of a rule application.  The slot is a stable
mathematical role supplied by the theory profile; `value` and `type?` retain
the elaborated Lean data without asking a renderer to recover it from the
rule's substituted conclusion. -/
structure CanonicalOperand where
  slot : Name
  value : Expr
  type? : Option Expr := none
  deriving Inhabited, BEq, Repr

/-- Checked mathematical formulae whose meaning is fixed by a registered
public rule and its typed operands.  These constructors are semantic notation
objects, not theorem-name or syntax-pattern templates.  `source` is always
the exact elaborated proposition proved by the rule application. -/
inductive FormulaTerm where
  | converterEquality (source : Expr) (left right : ConverterTerm)
  | restrictionAttachment (source blockForm limit system : Expr)
  | conditionalProductIdentity (source blockForm messages answers : Expr)
  | distinctSiteInputs (source function blockForm message other
      position otherPosition : Expr)
  | terminalInputInjective (source function blockForm messages : Expr)
  | walkCollisionBound (source parent step initial rank input : Expr)
  | collisionMassBound (source blockForm limit messages : Expr)
  | scalarMonotonicity (source lower upper : Expr)
  deriving Inhabited, BEq, Repr

def FormulaTerm.source : FormulaTerm → Expr
  | .converterEquality source ..
  | .restrictionAttachment source ..
  | .conditionalProductIdentity source ..
  | .distinctSiteInputs source ..
  | .terminalInputInjective source ..
  | .walkCollisionBound source ..
  | .collisionMassBound source ..
  | .scalarMonotonicity source .. => source

/-- The proposition shape expected from one formula-bearing public rule.
Profiles select a schema only after validating the exact declaration surface;
the decoder separately checks the proposition relation and required operands. -/
inductive FormulaSchema where
  | converterEquality
  | restrictionAttachment
  | conditionalProductIdentity
  | distinctSiteInputs
  | terminalInputInjective
  | walkCollisionBound
  | collisionMassBound
  | scalarMonotonicity
  deriving Inhabited, BEq, Repr

/-- Paper-level derivation rules.  They describe a mathematical transition,
not the Lean tactic or theorem spelling that implemented it. -/
inductive DerivationRule where
  | establishSystemEquality
  | establishConstruction
  | establishConditionalEquivalence
  | preserveConditionalEquivalence
  | conditionalEquivalenceToWinning
  | conditionalEquivalenceToBlindWinning
  | establishBlindWinningBound
  | deriveDistanceBound
  | deriveAdvantageBound
  | combineBounds
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- A canonical rule application with an operand-bearing conclusion and
separate proof obligations. -/
structure DerivationApplication where
  rule : DerivationRule
  conclusion : CanonicalProposition
  formula? : Option FormulaTerm := none
  operands : Array CanonicalOperand := #[]
  obligations : Array ProofObligation := #[]
  source : Expr
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- Look up a retained mathematical operand by its stable rule slot. -/
def DerivationApplication.operandForSlot?
    (application : DerivationApplication) (slot : Name) : Option CanonicalOperand :=
  application.operands.find? (·.slot == slot)

/-- Stable ways for a theory profile to select one declaration-telescope
argument.  Binder selection is appropriate when the source API treats binder
names as stable.  Positional selection is guarded by the expected binder name,
so a telescope reorder or signature drift cannot silently change semantics. -/
inductive RuleOperandSelector where
  | binder (name : Name)
  | position (index : Nat) (expectedBinder : Name)
  deriving Inhabited, BEq, Repr

/-- Map one non-proof declaration argument to a stable mathematical slot. -/
structure RuleOperandProfile where
  selector : RuleOperandSelector
  slot : Name
  deriving Inhabited, BEq, Repr

/-- Semantic role assigned to a declaration by a theory profile. -/
structure RuleDeclarationProfile where
  declaration : Name
  rule : DerivationRule
  /-- Non-proof mathematical operands retained independently of the
  conclusion and of proof obligations. -/
  operands : Array RuleOperandProfile := #[]
  /-- Optional checked formula schema for a public rule whose proposition is
  more specific than the generic cryptographic `Claim` language. -/
  formula? : Option FormulaSchema := none
  /-- Slots in non-instance proof-argument order, hence independent of binder
  spelling.  Exact child identity is carried separately by `ObligationKey`. -/
  proofSlots : Array ObligationSlot := #[]
  deriving Inhabited, BEq, Repr

/-- Operand slots are keys within one rule schema. -/
def RuleDeclarationProfile.hasUniqueOperandSlots
    (rule : RuleDeclarationProfile) : Bool :=
  rule.operands.all fun operand =>
    (rule.operands.filter (·.slot == operand.slot)).size == 1

/-- Surface shape for a declaration whose mathematical notation is supplied
by a theory adapter. The renderer never derives this choice from a Lean name. -/
inductive DeclarationNotationStyle where
  | atom
  | bracketed
  /-- A composite notation assembled from literal pieces and named checked
  operands. -/
  | template
  deriving Inhabited, BEq, Repr

/-- One typed piece of a declaration-owned notation template. -/
inductive DeclarationNotationPiece where
  | literal (value : String)
  | operand (slot : Name)
  deriving Inhabited, BEq, Repr

/-- Profile-owned mathematical notation. `operandSlots` assign semantic roles
to the explicit operands used by the notation, allowing the renderer to reuse
the same scoped symbols as the surrounding proof. -/
structure DeclarationNotation where
  declaration : Name
  latex : String
  style : DeclarationNotationStyle := .atom
  operandSlots : Array Name := #[]
  template : Array DeclarationNotationPiece := #[]
  deriving Inhabited, BEq, Repr

/-- Composite notation is accepted only when every referenced slot is supplied
by the declaration profile. -/
def DeclarationNotation.isWellFormed (entry : DeclarationNotation) : Bool :=
  match entry.style with
  | .atom => !entry.latex.trimAscii.isEmpty && entry.template.isEmpty
  | .bracketed => entry.template.isEmpty
  | .template =>
      !entry.template.isEmpty && entry.template.all fun piece =>
        match piece with
        | .literal value => !value.isEmpty
        | .operand slot => entry.operandSlots.contains slot

abbrev PresentationReferenceTarget :=
  CryptoLanguage.LanguageDesign.Presentation.ReferenceTarget
abbrev PresentationReference :=
  CryptoLanguage.LanguageDesign.Presentation.Reference
abbrev PresentationFragment :=
  CryptoLanguage.LanguageDesign.Presentation.Fragment
abbrev PresentationParagraph :=
  CryptoLanguage.LanguageDesign.Presentation.Paragraph
abbrev TheoremPresentation :=
  CryptoLanguage.LanguageDesign.Presentation.TheoremPresentation

/-- Declaration vocabulary needed to decode one system theory.  Arrays permit
semantic aliases without coupling the canonical AST to any particular API. -/
structure DecoderProfile where
  /-- Carrier constructors on which a polymorphic distance symbol has Random
  Systems meaning.  This prevents an arbitrary `edist x y` from being
  classified as a cryptographic distance merely because the head constant is
  shared. -/
  systemCarrierTypes : Array Name := #[]
  namedSystems : Array Name := #[]
  uniformRandomFunctions : Array Name := #[]
  uniformRandomPermutations : Array Name := #[]
  presentationQuotients : Array Name := #[]
  converterApplications : Array Name := #[]
  converterAtoms : Array Name := #[]
  converterRestrictions : Array Name := #[]
  /-- Converter declarations whose application to a system is canonically a
  query restriction rather than an opaque converter application. -/
  queryRestrictionConverters : Array Name := #[]
  /-- Semantically transparent carrier embeddings around converters. -/
  converterCoercions : Array Name := #[]
  converterSerialCompositions : Array Name := #[]
  specificationSingletons : Array Name := #[`Set.singleton]
  constructions : Array Name := #[]
  namedBounds : Array Name := #[]
  transforms : Array Name := #[]
  queryTransformers : Array Name := #[]
  systemQueryRestrictions : Array Name := #[]
  gameQueryRestrictions : Array Name := #[]
  /-- Overloaded applications whose converter operand can be validated as a
  registered game restriction before assigning game semantics. -/
  gameConverterApplications : Array Name := #[]
  mboEnhancements : Array Name := #[]
  namedGames : Array Name := #[]
  /-- Unary game transforms that turn a game into its blind version. -/
  blindGameTransforms : Array Name := #[]
  gameForgetting : Array Name := #[]
  conditionalEquivalence : Array Name := #[]
  statisticalDistance : Array Name := #[]
  /-- Fully-defined partial-system advantage, conventionally `Adv⊥`. -/
  fullyDefinedAdvantage : Array Name := #[]
  /-- Ambient normalized-system advantage. -/
  distinguishingAdvantage : Array Name := #[]
  winningProbability : Array Name := #[]
  blindWinningProbability : Array Name := #[]
  scalarCoercions : Array Name := #[]
  nonnegativityPredicates : Array Name := #[]
  weightFunctions : Array Name := #[]
  /-- Proposition declarations which are primary mathematical hypotheses for
  this domain.  Checked evidence compression keeps these hypotheses visible;
  it never treats them as implementation normalization. -/
  primaryHypotheses : Array Name := #[]
  rules : Array RuleDeclarationProfile := #[]
  declarationNotations : Array DeclarationNotation := #[]
  theoremPresentations : Array TheoremPresentation := #[]
  deriving Inhabited, BEq, Repr

/-- Validate the declaration-level operand maps in a decoder profile. -/
def DecoderProfile.hasUniqueRuleOperandSlots (profile : DecoderProfile) : Bool :=
  profile.rules.all RuleDeclarationProfile.hasUniqueOperandSlots

/-- A declaration has at most one reader-facing theorem presentation. -/
def DecoderProfile.hasUniqueTheoremPresentations
    (profile : DecoderProfile) : Bool :=
  profile.theoremPresentations.all fun presentation =>
    (profile.theoremPresentations.filter
      (·.declaration == presentation.declaration)).size == 1

/-- Declaration notation is a checked profile surface: declarations are
unique and every template is complete. -/
def DecoderProfile.hasWellFormedDeclarationNotations
    (profile : DecoderProfile) : Bool :=
  profile.declarationNotations.all DeclarationNotation.isWellFormed &&
    profile.declarationNotations.all fun entry =>
      (profile.declarationNotations.filter
        (·.declaration == entry.declaration)).size == 1

private structure AppliedArgument where
  position : Nat
  binderName : Name
  domain : Expr
  value : Expr
  binderInfo : BinderInfo

private partial def collectAppliedArguments (type : Expr) (arguments : Array Expr)
    (index : Nat) (result : Array AppliedArgument) : MetaM (Array AppliedArgument) := do
  if index == arguments.size then return result
  let type ← whnf type
  match type with
  | .forallE binderName domain body binderInfo =>
      let value := arguments[index]!
      collectAppliedArguments (body.instantiate1 value) arguments (index + 1)
        (result.push { position := index, binderName, domain, value, binderInfo })
  | _ => return result

private def appliedArguments (expression : Expr) : MetaM (Array AppliedArgument) := do
  let expression ← instantiateMVars expression
  let function := expression.consumeMData.getAppFn.consumeMData
  collectAppliedArguments (← inferType function) expression.getAppArgs 0 #[]

private def explicitArguments (expression : Expr) : MetaM (Array Expr) := do
  return (← appliedArguments expression).filterMap fun argument =>
    if argument.binderInfo.isExplicit then some argument.value else none

private def headDeclaration? (expression : Expr) : Option Name :=
  match expression.consumeMData.getAppFn.consumeMData with
  | .const declaration _ => some declaration
  | _ => none

private def hasHead (declarations : Array Name) (expression : Expr) : Bool :=
  (headDeclaration? expression).any declarations.contains

private def naturalLiteral? (expression : Expr) : Option Nat :=
  match expression.consumeMData with
  | .lit (.natVal value) => some value
  | expression =>
      if headDeclaration? expression == some ``OfNat.ofNat then
        expression.getAppArgs.findSome? fun
          | .lit (.natVal value) => some value
          | _ => none
      else none

private def unaryExplicitOperand? (expression : Expr) : MetaM (Option Expr) := do
  return (← explicitArguments expression)[0]?

/-- Recognize the exact scalar shape used by the standard birthday-style
collision estimate. This is intentionally structural and fail-closed: it does
not classify an arbitrary division or polynomial as a collision bound. -/
private def quadraticCollisionOperands?
    (expression : Expr) : MetaM (Option (Expr × Expr)) := do
  unless headDeclaration? expression == some ``HDiv.hDiv do return none
  let division ← explicitArguments expression
  let some numerator := division[0]? | return none
  let some denominator := division[1]? | return none

  unless headDeclaration? numerator == some ``HPow.hPow do return none
  let power ← explicitArguments numerator
  let some castBudget := power[0]? | return none
  let some exponent := power[1]? | return none
  unless naturalLiteral? exponent == some 2 do return none
  unless headDeclaration? castBudget == some ``Nat.cast do return none
  let some queryBudget ← unaryExplicitOperand? castBudget | return none

  unless headDeclaration? denominator == some ``HMul.hMul do return none
  let product ← explicitArguments denominator
  let some coefficient := product[0]? | return none
  let some castCardinality := product[1]? | return none
  unless naturalLiteral? coefficient == some 2 do return none
  unless headDeclaration? castCardinality == some ``Nat.cast do return none
  let some cardinality ← unaryExplicitOperand? castCardinality | return none
  unless headDeclaration? cardinality == some "Fintype.card".toName do return none
  let some alphabet ← unaryExplicitOperand? cardinality | return none
  return some (queryBudget, alphabet)

/-- Replace local `let` variables by their checked values before semantic
decoding.  Paper-level proof objects are commonly introduced by `let G := …`;
leaving such variables opaque would make a canonical rule remember only the
local spelling `G`, rather than the MBO enhancement or restriction it denotes.

This is deliberately zeta-only: ordinary hypotheses and parameters remain
free variables, and no declaration body is unfolded. -/
partial def expandLocalLets (raw : Expr) (fuel : Nat := 64) : MetaM Expr := do
  if fuel == 0 then return raw
  let next := fuel - 1
  match raw.consumeMData with
  | .fvar id =>
      match ← id.getDecl with
      | .ldecl (value := value) .. => expandLocalLets value next
      | _ => return raw
  | .app function argument =>
      return .app (← expandLocalLets function next) (← expandLocalLets argument next)
  | .lam name domain body info =>
      return .lam name (← expandLocalLets domain next)
        (← expandLocalLets body next) info
  | .forallE name domain body info =>
      return .forallE name (← expandLocalLets domain next)
        (← expandLocalLets body next) info
  | .letE name type value body nondep =>
      return .letE name (← expandLocalLets type next)
        (← expandLocalLets value next) (← expandLocalLets body next) nondep
  | .proj typeName index value =>
      return .proj typeName index (← expandLocalLets value next)
  | expression => return expression

private def transformation (expression : Expr) : MetaM TransformationTerm := do
  return {
    source := expression
    declaration? := headDeclaration? expression
    operands := ← explicitArguments expression
  }

private partial def findApplicationsWithHead (declarations : Array Name)
    (expression : Expr) (result : Array Expr := #[]) : Array Expr :=
  let expression := expression.consumeMData
  let result := if hasHead declarations expression then result.push expression else result
  match expression with
  | .app function argument =>
      findApplicationsWithHead declarations argument
        (findApplicationsWithHead declarations function result)
  | .lam _ domain body _ | .forallE _ domain body _ =>
      findApplicationsWithHead declarations body
        (findApplicationsWithHead declarations domain result)
  | .letE _ type value body _ =>
      findApplicationsWithHead declarations body
        (findApplicationsWithHead declarations value
          (findApplicationsWithHead declarations type result))
  | .proj _ _ value => findApplicationsWithHead declarations value result
  | .mdata _ body => findApplicationsWithHead declarations body result
  | _ => result

/-- Recover the unique query budget mentioned by a query-filter transformer.
The uniqueness check prevents an arbitrary lambda containing several filters
from being mislabeled as one canonical restriction. -/
private def queryBudgetFromTransformer? (profile : DecoderProfile)
    (expression : Expr) : MetaM (Option Expr) := do
  let applications := findApplicationsWithHead profile.queryTransformers expression
  let mut budgets : Array Expr := #[]
  for application in applications do
    if let some budget := (← explicitArguments application)[0]? then
      unless budgets.contains budget do budgets := budgets.push budget
  return if budgets.size == 1 then budgets[0]? else none

private def projectedValue? (expression : Expr) : Option Expr :=
  match expression.consumeMData with
  | .proj _ _ value => some value
  | expression =>
      match headDeclaration? expression with
      | some ``Subtype.val | some ``Prod.fst => expression.getAppArgs.back?
      | _ => none

private def GameTerm.withSource (term : GameTerm) (source : Expr) : GameTerm :=
  match term with
  | .opaque _ => .opaque source
  | .named _ declaration operands => .named source declaration operands
  | .enhanceWithMBO _ system condition => .enhanceWithMBO source system condition
  | .converterApplication _ converter underlying =>
      .converterApplication source converter underlying
  | .transform _ transformation underlying =>
      .transform source transformation underlying
  | .queryRestriction _ budget underlying =>
      .queryRestriction source budget underlying

private def SystemTerm.withSource (term : SystemTerm) (source : Expr) : SystemTerm :=
  match term with
  | .opaque _ => .opaque source
  | .named _ declaration operands => .named source declaration operands
  | .uniformRandomFunction _ input output =>
      .uniformRandomFunction source input output
  | .uniformRandomPermutation _ alphabet =>
      .uniformRandomPermutation source alphabet
  | .presentationQuotient _ presentation =>
      .presentationQuotient source presentation
  | .converterApplication _ converter underlying =>
      .converterApplication source converter underlying
  | .transform _ transformation underlying =>
      .transform source transformation underlying
  | .queryRestriction _ budget underlying =>
      .queryRestriction source budget underlying
  | .forgetGame _ game => .forgetGame source game

private def decodeCondition (expression : Expr) : MetaM ConditionTerm := do
  match headDeclaration? expression with
  | some declaration =>
      return .named expression declaration (← explicitArguments expression)
  | none => return .opaque expression

/-- Decode a converter without unfolding its implementation.  Serial order is
retained as the checked outer and inner operands supplied by the declaration. -/
partial def decodeConverter (profile : DecoderProfile) (raw : Expr) : MetaM ConverterTerm := do
  let expression ← expandLocalLets (← instantiateMVars raw)
  if hasHead profile.converterCoercions expression then
    if let some underlying := (← explicitArguments expression).back? then
      return ← decodeConverter profile underlying
  if hasHead profile.converterSerialCompositions expression then
    let arguments ← explicitArguments expression
    if arguments.size >= 2 then
      let outer := arguments[arguments.size - 2]!
      let inner := arguments[arguments.size - 1]!
      return .serialComposition expression
        (← decodeConverter profile outer) (← decodeConverter profile inner)
  if hasHead profile.converterRestrictions expression then
    if let some declaration := headDeclaration? expression then
      return .restriction expression declaration (← explicitArguments expression)
  if hasHead profile.converterAtoms expression then
    if let some declaration := headDeclaration? expression then
      return .named expression declaration (← explicitArguments expression)
  return .opaque expression

mutual
  /-- Decode a system expression according to a theory profile.  Unknown
  systems are explicit opaque leaves; no semantic guess is made from a local
  variable name. -/
  partial def decodeSystem (profile : DecoderProfile) (raw : Expr) : MetaM SystemTerm := do
    let expression ← expandLocalLets (← instantiateMVars raw)
    if let some projected := projectedValue? expression then
      if hasHead profile.namedSystems projected ||
          hasHead profile.converterApplications projected ||
          hasHead profile.systemQueryRestrictions projected ||
          hasHead profile.transforms projected ||
          hasHead profile.gameForgetting projected then
        return (← decodeSystem profile projected).withSource expression
    if hasHead profile.presentationQuotients expression then
      if let some presentation := (← explicitArguments expression).back? then
        return .presentationQuotient expression (← decodeSystem profile presentation)
    if hasHead profile.converterApplications expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let converter := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        let decodedConverter ← decodeConverter profile converter
        let restrictionOperands? := match decodedConverter with
          | .named _ declaration operands | .restriction _ declaration operands =>
              if profile.queryRestrictionConverters.contains declaration then
                some operands
              else
                none
          | _ => none
        if let some restrictionOperands := restrictionOperands? then
          if let some budget := restrictionOperands.back? then
            return .queryRestriction expression budget
              (← decodeSystem profile underlying)
        return .converterApplication expression decodedConverter
          (← decodeSystem profile underlying)
    if hasHead profile.namedSystems expression then
      if let some declaration := headDeclaration? expression then
        return .named expression declaration (← explicitArguments expression)
    if hasHead profile.uniformRandomFunctions expression then
      let arguments ← explicitArguments expression
      if let some inputSpace := arguments[0]? then
        if let some outputSpace := arguments[1]? then
          return .uniformRandomFunction expression inputSpace outputSpace
    if hasHead profile.uniformRandomPermutations expression then
      if let some alphabet := (← explicitArguments expression)[0]? then
        return .uniformRandomPermutation expression alphabet
    if hasHead profile.systemQueryRestrictions expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let budget := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        return .queryRestriction expression budget (← decodeSystem profile underlying)
    if hasHead profile.gameForgetting expression then
      if let some game := (← explicitArguments expression).back? then
        return .forgetGame expression (← decodeGame profile game)
    if hasHead profile.transforms expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let map := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        if let some budget ← queryBudgetFromTransformer? profile map then
          return .queryRestriction expression budget (← decodeSystem profile underlying)
        return .transform expression (← transformation map)
          (← decodeSystem profile underlying)
    return .opaque expression

  /-- Decode a game expression, interpreting an adjoin projection as the game
  obtained by enhancing a system with an MBO, and a transformed query filter
  as a query restriction. -/
  partial def decodeGame (profile : DecoderProfile) (raw : Expr) : MetaM GameTerm := do
    let expression ← expandLocalLets (← instantiateMVars raw)
    if let some projected := projectedValue? expression then
      if hasHead profile.namedGames projected ||
          hasHead profile.gameConverterApplications projected ||
          hasHead profile.gameQueryRestrictions projected ||
          hasHead profile.transforms projected then
        return (← decodeGame profile projected).withSource expression
    if hasHead profile.namedGames expression then
      if let some declaration := headDeclaration? expression then
        return .named expression declaration (← explicitArguments expression)
    if hasHead profile.blindGameTransforms expression then
      if let some underlying := (← explicitArguments expression).back? then
        return .transform expression (← transformation expression)
          (← decodeGame profile underlying)
    if hasHead profile.gameConverterApplications expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let converter := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        match ← decodeConverter profile converter with
        | decoded@(.restriction _ declaration operands) =>
            if profile.queryRestrictionConverters.contains declaration then
              if let some budget := operands.back? then
                return .queryRestriction expression budget
                  (← decodeGame profile underlying)
            return .converterApplication expression decoded
              (← decodeGame profile underlying)
        | .opaque _ => pure ()
        | decoded =>
            return .converterApplication expression decoded
              (← decodeGame profile underlying)
    if hasHead profile.gameQueryRestrictions expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let budget := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        return .queryRestriction expression budget (← decodeGame profile underlying)
    if let some projected := projectedValue? expression then
      if hasHead profile.mboEnhancements projected then
        let arguments ← explicitArguments projected
        if arguments.size >= 2 then
          let system := arguments[arguments.size - 2]!
          let condition := arguments[arguments.size - 1]!
          return .enhanceWithMBO expression (← decodeSystem profile system)
            (← decodeCondition condition)
    if hasHead profile.transforms expression then
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let map := arguments[arguments.size - 2]!
        let underlying := arguments[arguments.size - 1]!
        if let some budget ← queryBudgetFromTransformer? profile map then
          return .queryRestriction expression budget (← decodeGame profile underlying)
        return .transform expression (← transformation map)
          (← decodeGame profile underlying)
    return .opaque expression
end

/-- A blind-winning quantity already records blindness in its constructor, so
the nested game term denotes the underlying game rather than repeating the
blind transform on the reader surface. -/
private def blindUnderlyingGame? (profile : DecoderProfile)
    (expression : Expr) : MetaM (Option Expr) := do
  if !hasHead profile.blindGameTransforms expression then return none
  return (← explicitArguments expression).back?

/-- Decode a specification operand.  Singleton recognition is scoped to the
construction decoder, so a generic set expression is never globally relabeled
as a cryptographic specification. -/
def decodeSpecification (profile : DecoderProfile) (raw : Expr) : MetaM SpecificationTerm := do
  let expression ← expandLocalLets (← instantiateMVars raw)
  if hasHead profile.specificationSingletons expression then
    if let some member := (← explicitArguments expression).back? then
      return .singleton expression (← decodeSystem profile member)
  return .opaque expression

/-- Decode a scalar expression used in an inequality. -/
partial def decodeBound (profile : DecoderProfile) (raw : Expr) : MetaM BoundTerm := do
  let original ← instantiateMVars raw
  let expression ← expandLocalLets original
  if hasHead profile.namedBounds expression then
    if let some declaration := headDeclaration? expression then
      return .named original declaration (← explicitArguments expression)
  if hasHead profile.statisticalDistance expression then
    let arguments ← explicitArguments expression
    if arguments.size >= 2 then
      let left := arguments[arguments.size - 2]!
      let right := arguments[arguments.size - 1]!
      let leftSystem ← decodeSystem profile left
      let rightSystem ← decodeSystem profile right
      let hasRegisteredCarrier (value : Expr) : MetaM Bool := do
        let type ← instantiateMVars (← inferType value)
        return hasHead profile.systemCarrierTypes type
      if (leftSystem.isStructured || (← hasRegisteredCarrier left)) &&
          (rightSystem.isStructured || (← hasRegisteredCarrier right)) then
        return .statisticalDistance original leftSystem rightSystem
  let advantageKind? :=
    if hasHead profile.fullyDefinedAdvantage expression then
      some AdvantageKind.fullyDefined
    else if hasHead profile.distinguishingAdvantage expression then
      some AdvantageKind.ambient
    else none
  if let some advantageKind := advantageKind? then
    let arguments ← explicitArguments expression
    if arguments.size >= 2 then
      let real := arguments[arguments.size - 2]!
      let ideal := arguments[arguments.size - 1]!
      return .distinguishingAdvantage original advantageKind
        (← decodeSystem profile real) (← decodeSystem profile ideal)
  if hasHead profile.blindWinningProbability expression then
    if let some game := (← explicitArguments expression).back? then
      let underlying := (← blindUnderlyingGame? profile game).getD game
      return .blindWinningProbability original (← decodeGame profile underlying)
  if hasHead profile.winningProbability expression then
    if let some game := (← explicitArguments expression).back? then
      let decoded ← decodeGame profile game
      if hasHead profile.blindGameTransforms game then
        let underlying := (← blindUnderlyingGame? profile game).getD game
        return .blindWinningProbability original (← decodeGame profile underlying)
      return .winningProbability original decoded
  if hasHead profile.scalarCoercions expression then
    if let some inner := (← explicitArguments expression).back? then
      return .coercion original (← decodeBound profile inner)
  if let some (queryBudget, alphabet) ← quadraticCollisionOperands? expression then
    return .quadraticCollision original queryBudget alphabet
  return .expression original

/-- Decode the canonical proposition at the root of an elaborated expression. -/
def decodeClaim? (profile : DecoderProfile) (raw : Expr) : MetaM (Option Claim) := do
  let expression ← expandLocalLets (← instantiateMVars raw)
  if hasHead profile.constructions expression then
    let arguments ← explicitArguments expression
    if arguments.size >= 4 then
      let converter := arguments[arguments.size - 4]!
      let source := arguments[arguments.size - 3]!
      let target := arguments[arguments.size - 2]!
      let error := arguments[arguments.size - 1]!
      return some (.construction expression
        (← decodeSpecification profile source)
        (← decodeConverter profile converter)
        (← decodeSpecification profile target)
        (← decodeBound profile error))
  if hasHead profile.conditionalEquivalence expression then
    let arguments ← explicitArguments expression
    if arguments.size >= 2 then
      let game := arguments[arguments.size - 2]!
      let target := arguments[arguments.size - 1]!
      return some (.conditionalEquivalence expression
        (← decodeGame profile game) (← decodeSystem profile target))
  match headDeclaration? expression with
  | some ``Eq =>
      let arguments ← explicitArguments expression
      if arguments.size >= 2 then
        let left ← decodeSystem profile arguments[arguments.size - 2]!
        let right ← decodeSystem profile arguments[arguments.size - 1]!
        if left.isStructured || right.isStructured then
          return some (.systemEquality expression left right)
      return none
  | some ``LE.le =>
      let arguments ← explicitArguments expression
      if arguments.size < 2 then return none
      let lower ← decodeBound profile arguments[arguments.size - 2]!
      let upper ← decodeBound profile arguments[arguments.size - 1]!
      match lower with
      | .statisticalDistance _ left right =>
          return some (.distanceBound expression left right upper)
      | .distinguishingAdvantage _ kind real ideal =>
          return some (.advantageBound expression kind real ideal upper)
      | .blindWinningProbability _ game =>
          return some (.blindWinningBound expression game upper)
      | .coercion _ (.blindWinningProbability _ game) =>
          return some (.blindWinningBound expression game upper)
      | _ => return some (.upperBound expression lower upper)
  | _ => return none

/-- Decode every checked proposition, retaining an exact opaque leaf when the
cryptographic claim vocabulary does not yet cover its shape. -/
def decodeProposition (profile : DecoderProfile) (raw : Expr) :
    MetaM CanonicalProposition := do
  let expression ← instantiateMVars raw
  match ← decodeClaim? profile expression with
  | some claim => return .claim claim
  | none => return .opaque expression

private def ruleProfile? (profile : DecoderProfile) (declaration? : Option Name) :
    Option RuleDeclarationProfile := do
  let declaration ← declaration?
  profile.rules.find? (·.declaration == declaration)

private def operandArgument? (arguments : Array AppliedArgument) :
    RuleOperandSelector → Option AppliedArgument
  | .binder name =>
      let candidates := arguments.filter (·.binderName == name)
      if candidates.size == 1 then candidates[0]? else none
  | .position index expectedBinder => do
      let argument ← arguments[index]?
      if argument.binderName == expectedBinder then some argument else none

/-- Resolve the non-proof operands declared by a rule profile.  A missing or
ambiguous selector is an adapter error rather than a cue to guess from the
substituted conclusion. -/
private def canonicalOperands (rule : RuleDeclarationProfile)
    (arguments : Array AppliedArgument) : MetaM (Array CanonicalOperand) := do
  unless rule.hasUniqueOperandSlots do
    throwError "canonical rule {rule.declaration} has duplicate operand slots"
  let mut result := #[]
  for configured in rule.operands do
    let some argument := operandArgument? arguments configured.selector
      | throwError "canonical operand {configured.slot} cannot be resolved in {rule.declaration}"
    if ← isProp argument.domain then
      throwError "canonical operand {configured.slot} in {rule.declaration} selects a proof argument"
    result := result.push {
      slot := configured.slot
      value := argument.value
      type? := some argument.domain
    }
  return result

private def isWeightExpression (profile : DecoderProfile) (expression : Expr) : Bool :=
  hasHead profile.weightFunctions expression

private def inferredSlot (profile : DecoderProfile) (claim? : Option Claim)
    (proposition : Expr) : ObligationSlot :=
  match claim? with
  | some (.conditionalEquivalence ..) => .conditionalEquivalence
  | _ =>
      if hasHead profile.nonnegativityPredicates proposition then .nonnegative
      else if headDeclaration? proposition == some ``Eq then
        let arguments := proposition.getAppArgs
        if arguments.any (isWeightExpression profile) then .equalWeight
        else .sideCondition
      else .sideCondition

private def inferredRule (conclusion : Claim)
    (obligations : Array ProofObligation) : DerivationRule :=
  let hasConditionalEquivalence := obligations.any
    (fun obligation => obligation.slot == .conditionalEquivalence)
  match conclusion with
  | .systemEquality .. => .establishSystemEquality
  | .construction .. => .establishConstruction
  | .conditionalEquivalence .. =>
      if hasConditionalEquivalence then .preserveConditionalEquivalence
      else .establishConditionalEquivalence
  | .advantageBound _ _ _ _ upper =>
      if upper.blindWinningGame?.isSome && hasConditionalEquivalence then
        .conditionalEquivalenceToBlindWinning
      else if obligations.countP (fun obligation => obligation.claim?.isSome) >= 2 then
        .combineBounds
      else .deriveAdvantageBound
  | .distanceBound .. => .deriveDistanceBound
  | .blindWinningBound .. => .establishBlindWinningBound
  | .upperBound .. => .combineBounds

private def operandValue? (operands : Array CanonicalOperand)
    (slot : Name) : Option Expr :=
  (operands.find? (·.slot == slot)).map (·.value)

private def propositionHasHead (proposition : Expr) (heads : Array Name) : Bool :=
  (headDeclaration? proposition).any heads.contains

/-- Instantiate a registered formula schema from exact checked operands.
Relation-head guards make a stale or incorrectly registered theorem fail
closed instead of acquiring a plausible-looking formula. -/
private def decodeFormula? (profile : DecoderProfile) (schema : FormulaSchema)
    (proposition : Expr) (operands : Array CanonicalOperand) :
    MetaM (Option FormulaTerm) :=
  match schema with
  | .converterEquality => do
      if !propositionHasHead proposition #[``Eq] then return none
      let arguments := proposition.getAppArgs
      if arguments.size < 2 then return none
      let left := arguments[arguments.size - 2]!
      let right := arguments[arguments.size - 1]!
      return some (.converterEquality proposition
        (← decodeConverter profile left) (← decodeConverter profile right))
  | .restrictionAttachment => pure <| do
      guard (propositionHasHead proposition #[``Eq])
      let blockForm ← operandValue? operands `blockForm
      let limit ← operandValue? operands `blockLimit
      let system ← operandValue? operands `system
      return .restrictionAttachment proposition blockForm limit system
  | .conditionalProductIdentity => pure <| do
      guard (propositionHasHead proposition #[``Eq])
      let blockForm ← operandValue? operands `blockForm
      let messages ← operandValue? operands `messages
      let answers ← operandValue? operands `answers
      return .conditionalProductIdentity proposition blockForm messages answers
  | .distinctSiteInputs => pure <| do
      guard (propositionHasHead proposition #[``Ne, ``Not])
      let function ← operandValue? operands `function
      let blockForm ← operandValue? operands `blockForm
      let message ← operandValue? operands `message
      let other ← operandValue? operands `otherMessage
      let position ← operandValue? operands `position
      let otherPosition ← operandValue? operands `otherPosition
      return .distinctSiteInputs proposition function blockForm message other
        position otherPosition
  | .terminalInputInjective => pure <| do
      guard (propositionHasHead proposition #[`Set.InjOn])
      let function ← operandValue? operands `function
      let blockForm ← operandValue? operands `blockForm
      let messages ← operandValue? operands `messages
      return .terminalInputInjective proposition function blockForm messages
  | .walkCollisionBound => pure <| do
      guard (propositionHasHead proposition #[``LE.le])
      let parent ← operandValue? operands `parentMap
      let step ← operandValue? operands `walkStep
      let initial ← operandValue? operands `initialState
      let rank ← operandValue? operands `rank
      let input ← operandValue? operands `siteInput
      return .walkCollisionBound proposition parent step initial rank input
  | .collisionMassBound => pure <| do
      guard (propositionHasHead proposition #[``LE.le])
      let blockForm ← operandValue? operands `blockForm
      let limit ← operandValue? operands `blockLimit
      let messages ← operandValue? operands `messages
      return .collisionMassBound proposition blockForm limit messages
  | .scalarMonotonicity => pure <| do
      guard (propositionHasHead proposition #[``LE.le])
      let lower ← operandValue? operands `lower
      let upper ← operandValue? operands `upper
      return .scalarMonotonicity proposition lower upper

/-- Decode a proof term as a canonical mathematical rule application.  Its
proof-valued arguments become separately slotted obligations; ordinary
parameters remain represented by the conclusion's operand tree. -/
def decodeDerivation? (profile : DecoderProfile) (raw : Expr) :
    MetaM (Option DerivationApplication) := do
  let expression ← instantiateMVars raw
  let proposition ← instantiateMVars (← inferType expression)
  let claim? ← decodeClaim? profile proposition
  let conclusion := claim?.map CanonicalProposition.claim |>.getD
    (.opaque proposition)
  let declaration? := headDeclaration? expression
  let configured := ruleProfile? profile declaration?
  let arguments ← appliedArguments expression
  let operands ← match configured with
    | some rule => canonicalOperands rule arguments
    | none => pure #[]
  let formula? ← match configured.bind (·.formula?) with
    | some schema => decodeFormula? profile schema proposition operands
    | none => pure none
  if claim?.isNone && formula?.isNone then return none
  let mut obligations := #[]
  let mut proofOrdinal := 0
  let mut semanticProofIndex := 0
  for argument in arguments do
    if ← isProp argument.domain then
      let key : ObligationKey := {
        telescopePosition := argument.position
        proofOrdinal
      }
      proofOrdinal := proofOrdinal + 1
      if argument.binderInfo == .instImplicit then continue
      let claim? ← decodeClaim? profile argument.domain
      let inferred := inferredSlot profile claim? argument.domain
      let slot := (configured.bind fun rule =>
        rule.proofSlots[semanticProofIndex]?).getD inferred
      obligations := obligations.push {
        key
        slot
        salience := if argument.binderInfo.isExplicit then .supporting else .implicit
        proposition := argument.domain
        evidence := argument.value
        claim?
        provenance := {
          expression := argument.value
          declaration? := headDeclaration? argument.value
          evidenceKind := .proofTerm
        }
      }
      semanticProofIndex := semanticProofIndex + 1
  let rule ← match configured, claim? with
    | some configured, _ => pure configured.rule
    | none, some conclusion => pure (inferredRule conclusion obligations)
    | none, none => return none
  return some {
    rule
    conclusion
    formula?
    operands
    obligations
    source := expression
    provenance := {
      expression
      declaration?
      evidenceKind := .proofTerm
    }
  }

end Informalization.Semantics.Canonical

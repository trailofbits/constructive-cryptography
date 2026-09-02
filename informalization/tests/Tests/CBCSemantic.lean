import Informalization.Semantics.CanonicalRandomSystems
import Informalization.Semantics.Plan
import Informalization.Semantics.RandomSystems
import Informalization.Semantics.Validation

/-!
# Construction-decoder tests

These declarations reproduce only the reusable type shapes of the external
Random Systems construction boundary.  They contain no CBC proof paragraph or
theorem-shape heuristic; the assertions exercise fully qualified declaration
roles and the generic canonical operand language.
-/

namespace RandomSystems.Ambient

namespace DDC

def serial (outer inner : Nat) : Nat := outer + inner

end DDC

namespace PDS

def apply (converter system : Nat) : Nat := converter + system
def advantage (left right : Nat) : Nat := left + right

theorem apply_serial (outer inner system : Nat) :
    apply (DDC.serial outer inner) system = apply outer (apply inner system) := by
  simp [apply, DDC.serial, Nat.add_assoc]

end PDS

namespace RandomSystem

def ofPDS (system : Nat) : Nat := system
def apply (converter system : Nat) : Nat := converter + system

theorem apply_ofPDS (converter system : Nat) :
    apply converter (ofPDS system) = ofPDS (PDS.apply converter system) := rfl

theorem edist_eq_advantage (left right : Nat) : left + right = left + right := rfl
theorem advantage_ofPDS (left right : Nat) : left + right = PDS.advantage left right := rfl

end RandomSystem

end RandomSystems.Ambient

namespace RandomSystemsCC.FunctionalCategorical

structure Specification where
  members : List Nat

instance : Singleton Nat Specification := ⟨fun member => ⟨[member]⟩⟩

end RandomSystemsCC.FunctionalCategorical

namespace AbstractCryptography.Categorical.ResourceAlgebra.Specification

def ConstructsWithin (converter : Nat)
    (source target : RandomSystemsCC.FunctionalCategorical.Specification)
    (error : Nat) : Prop :=
  source.members ≠ [] ∧ target.members ≠ [] ∧ converter ≤ error + converter

end AbstractCryptography.Categorical.ResourceAlgebra.Specification

namespace Applications.CBCCombinatorics

def cbcEpsilon (X : Type) (r : Nat) : Nat :=
  let _ := X
  r + 1

end Applications.CBCCombinatorics

namespace Applications.CBCMAC

def cbc (blockForm : Nat) : Nat := blockForm
def theta (blockForm limit : Nat) : Nat := blockForm + limit
def restrictedRandomFunction (limit : Nat) : Nat := limit
def realPDS (blockForm limit : Nat) : Nat := blockForm + limit
def idealPDS (blockForm limit : Nat) : Nat := blockForm + limit + 1

theorem cbc_constructs_within (blockForm limit : Nat) (prefixFree : True) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      (RandomSystems.Ambient.DDC.serial (theta blockForm limit) (cbc blockForm))
      {RandomSystems.Ambient.RandomSystem.ofPDS
        (restrictedRandomFunction limit)}
      {RandomSystems.Ambient.RandomSystem.ofPDS (idealPDS blockForm limit)}
      (Applications.CBCCombinatorics.cbcEpsilon Nat limit) := by
  have _ := prefixFree
  simp [AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin,
    RandomSystems.Ambient.DDC.serial, theta, cbc,
    Applications.CBCCombinatorics.cbcEpsilon]

theorem constructionDirect (blockForm limit : Nat) (prefixFree : True) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      (RandomSystems.Ambient.DDC.serial (theta blockForm limit) (cbc blockForm))
      {RandomSystems.Ambient.RandomSystem.ofPDS
        (restrictedRandomFunction limit)}
      {RandomSystems.Ambient.RandomSystem.ofPDS (idealPDS blockForm limit)}
      (Applications.CBCCombinatorics.cbcEpsilon Nat limit) :=
  cbc_constructs_within blockForm limit prefixFree

theorem constructionRefactored (encoding bound : Nat) (condition : True) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      (RandomSystems.Ambient.DDC.serial (theta encoding bound) (cbc encoding))
      {RandomSystems.Ambient.RandomSystem.ofPDS
        (restrictedRandomFunction bound)}
      {RandomSystems.Ambient.RandomSystem.ofPDS (idealPDS encoding bound)}
      (Applications.CBCCombinatorics.cbcEpsilon Nat bound) := by
  apply cbc_constructs_within
  exact condition

def unrelatedRelation (_source : RandomSystemsCC.FunctionalCategorical.Specification)
    (_converter : Nat)
    (_target : RandomSystemsCC.FunctionalCategorical.Specification)
    (_error : Nat) : Prop := True

theorem unrelatedConstructionShape (blockForm limit : Nat) :
    unrelatedRelation
      {RandomSystems.Ambient.RandomSystem.ofPDS
        (restrictedRandomFunction limit)}
      (RandomSystems.Ambient.DDC.serial (theta blockForm limit) (cbc blockForm))
      {RandomSystems.Ambient.RandomSystem.ofPDS (idealPDS blockForm limit)}
      (Applications.CBCCombinatorics.cbcEpsilon Nat limit) := True.intro

end Applications.CBCMAC

namespace Tests.CBCSemantic

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Registry
open Informalization.Semantics.Validation

private def namedPrimary (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot }

private def namedSupporting (slot : Lean.Name) (selector : ArgumentSelector)
    (role : ArgumentRole) : ArgumentBinding :=
  { selector, role, slot? := some slot, salience := .supporting }

/-- Test-local vocabulary for the synthetic construction fixture above. The
production Random Systems profile intentionally contains no application
declarations. -/
private def mockProfile : DecoderProfile :=
  let base := Canonical.RandomSystemsProfile.profile
  { base with
    namedSystems := base.namedSystems ++ #[
      `Applications.CBCMAC.restrictedRandomFunction,
      `Applications.CBCMAC.realPDS,
      `Applications.CBCMAC.idealPDS
    ]
    converterAtoms := base.converterAtoms ++ #[`Applications.CBCMAC.cbc]
    converterRestrictions := base.converterRestrictions ++ #[`Applications.CBCMAC.theta]
    namedBounds := base.namedBounds ++ #[`Applications.CBCCombinatorics.cbcEpsilon]
    rules := base.rules ++ #[{
      declaration := `Applications.CBCMAC.cbc_constructs_within
      rule := .establishConstruction
      operands := #[
        { selector := .binder `blockForm, slot := `blockForm },
        { selector := .binder `limit, slot := `blockLimit }
      ]
      proofSlots := #[.sideCondition]
    }]
  }

/-- Test-local semantic registrations for the synthetic construction
fixture. They exercise overlay composition without polluting the reusable
production catalog. -/
private def mockCatalog : Catalog :=
  Informalization.Semantics.RandomSystems.catalog ++ #[
    {
      declaration := `Applications.CBCMAC.cbc
      role := .converter .atom
      arguments := #[
        namedPrimary `blockForm (.binder `blockForm) (.custom `blockForm)
      ]
    },
    {
      declaration := `Applications.CBCMAC.theta
      role := .converter .blockRestriction
      arguments := #[
        namedPrimary `blockForm (.binder `blockForm) (.custom `blockForm),
        namedPrimary `blockLimit (.binder `limit) (.custom `blockLimit)
      ]
    },
    {
      declaration := `Applications.CBCMAC.restrictedRandomFunction
      role := .system .queryRestriction
      arguments := #[
        namedPrimary `queryBudget (.binder `limit) .queryBudget
      ]
    },
    {
      declaration := `Applications.CBCMAC.realPDS
      role := .system .atom
      arguments := #[
        namedPrimary `blockForm (.binder `blockForm) (.custom `blockForm),
        namedPrimary `blockLimit (.binder `limit) (.custom `blockLimit)
      ]
    },
    {
      declaration := `Applications.CBCMAC.idealPDS
      role := .system .idealFunctionality
      arguments := #[
        namedPrimary `blockForm (.binder `blockForm) (.custom `blockForm),
        namedPrimary `blockLimit (.binder `limit) (.custom `blockLimit)
      ]
    },
    {
      declaration := `Applications.CBCCombinatorics.cbcEpsilon
      role := .quantity (.custom `collisionBound)
      arguments := #[
        namedPrimary `alphabet (.binder `X) .alphabet,
        namedPrimary `blockLimit (.binder `r) (.custom `blockLimit)
      ]
    },
    {
      declaration := `Applications.CBCMAC.cbc_constructs_within
      role := .proofRule .construction
      arguments := #[
        namedPrimary `blockForm (.binder `blockForm) (.custom `blockForm),
        namedPrimary `blockLimit (.binder `limit) (.custom `blockLimit),
        namedSupporting `prefixFree (.binder `prefixFree) (.premise 0),
        namedPrimary `result .result .conclusion
      ]
    }
  ]

private def requireClaim (expression : Expr) : MetaM Claim := do
  let some claim ← Canonical.decodeClaim?
      mockProfile expression
    | throwError "construction claim was not decoded"
  return claim

private def requirePlan (environment : Environment) (declaration : Name) : MetaM
    Informalization.Semantics.Plan.ProofPlan := do
  let some plan ← Informalization.Semantics.Plan.fromDeclarationWithProfile?
      environment mockCatalog mockProfile declaration
    | throwError "construction proof plan was not recovered"
  return plan

run_cmd liftTermElabM do
  let environment ← getEnv
  let blockForm := mkNatLit 4
  let limit := mkNatLit 9
  let proof ← mkAppM ``Applications.CBCMAC.cbc_constructs_within
    #[blockForm, limit, mkConst ``True.intro]
  let conclusion ← inferType proof

  let claim ← requireClaim conclusion
  match claim with
  | .construction _ source converter target error =>
      match source with
      | .singleton _ (.presentationQuotient _
          (.named _ declaration operands)) =>
          unless declaration == ``Applications.CBCMAC.restrictedRandomFunction &&
              operands == #[limit] do
            throwError "source singleton lost the restricted random-function operand"
      | _ => throwError "source specification was not decoded as a singleton quotient"
      match converter with
      | .serialComposition _
          (.restriction _ outerDeclaration outerOperands)
          (.named _ innerDeclaration innerOperands) =>
          unless outerDeclaration == ``Applications.CBCMAC.theta &&
              outerOperands == #[blockForm, limit] &&
              innerDeclaration == ``Applications.CBCMAC.cbc &&
              innerOperands == #[blockForm] do
            throwError "serial converter operands or application order were not retained"
      | _ => throwError "construction converter was not decoded as serial composition"
      match target with
      | .singleton _ (.presentationQuotient _
          (.named _ declaration operands)) =>
          unless declaration == ``Applications.CBCMAC.idealPDS &&
              operands == #[blockForm, limit] do
            throwError "target singleton lost the ideal-system operands"
      | _ => throwError "target specification was not decoded as a singleton quotient"
      match error with
      | .named _ declaration operands =>
          unless declaration == ``Applications.CBCCombinatorics.cbcEpsilon &&
              operands.size == 2 && operands[1]! == limit do
            throwError "construction error lost its canonical bound operands"
      | _ => throwError "construction error was not decoded as a named bound"
  | _ => throwError "the admitted root was not a canonical construction"

  let accepted ← isSecurityStatementRootWith environment
    mockCatalog conclusion
  unless accepted do
    throwError "registered construction relation failed the security-root gate"

  let some graph ← recoverGraphWith? environment
      mockCatalog conclusion
    | throwError "construction graph was not recovered"
  unless graph.rootNode?.map (·.role) == some (.proposition .construction) &&
      graph.nodes.any (·.role == .converter .serialComposition) &&
      graph.nodes.any (·.role == .converter .blockRestriction) &&
      graph.nodes.any (·.role == .converter .atom) do
    throwError "construction graph lost its relation or converter roles"

  let application := mkApp2 (mkConst ``RandomSystems.Ambient.RandomSystem.apply)
    (mkApp2 (mkConst ``RandomSystems.Ambient.DDC.serial)
      (mkApp2 (mkConst ``Applications.CBCMAC.theta) blockForm limit)
      (mkApp (mkConst ``Applications.CBCMAC.cbc) blockForm))
    (mkApp (mkConst ``RandomSystems.Ambient.RandomSystem.ofPDS)
      (mkApp (mkConst ``Applications.CBCMAC.restrictedRandomFunction) limit))
  match ← Canonical.decodeSystem mockProfile application with
  | .converterApplication _ (.serialComposition _ _ _)
      (.presentationQuotient _ (.named _ declaration operands)) =>
      unless declaration == ``Applications.CBCMAC.restrictedRandomFunction &&
          operands == #[limit] do
        throwError "random-system application lost its source presentation"
  | _ => throwError "random-system application was not decoded canonically"

  let unrelatedProof ← mkAppM ``Applications.CBCMAC.unrelatedConstructionShape
    #[blockForm, limit]
  let unrelatedConclusion ← inferType unrelatedProof
  if (← isSecurityStatementRootWith environment
      mockCatalog unrelatedConclusion) then
    throwError "an unregistered construction-shaped relation passed the root gate"
  if (← Canonical.decodeClaim? mockProfile unrelatedConclusion).isSome then
    throwError "an unregistered construction-shaped relation received a canonical claim"

  let arithmetic ← mkAppM ``LE.le #[blockForm, limit]
  if (← isSecurityStatementRootWith environment
      mockCatalog arithmetic) then
    throwError "an arithmetic inequality passed the construction root gate"

  let partialApplication := mkConst
    ``AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
  unless (← inferType partialApplication).isForall do
    throwError "partial construction fixture did not remain a function"
  if (← Canonical.decodeClaim? mockProfile partialApplication).isSome then
    throwError "a partially applied construction relation was admitted"

  let visibleCatalog := mockCatalog.filter fun entry =>
    (environment.find? entry.declaration).isSome
  let issues := validateCatalog environment visibleCatalog
  unless issues.isEmpty do
    throwError "construction catalog does not match the checked mock signatures: {repr issues}"

  let direct ← requirePlan environment ``Applications.CBCMAC.constructionDirect
  let refactored ← requirePlan environment ``Applications.CBCMAC.constructionRefactored
  unless direct.semanticFingerprint == refactored.semanticFingerprint do
    throwError "binder renaming or proof refactoring changed the construction fingerprint"

end Tests.CBCSemantic

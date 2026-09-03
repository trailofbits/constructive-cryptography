import Lean

/-!
# Shared language-design identifiers

This module is deliberately free of parser syntax, English strings, proof-state
mutation, and informalization code.  `/verbose` and `/informalization` share
these identifiers without depending on one another.
-/

namespace CryptoLanguage.LanguageDesign

open Lean

structure RuleId where
  layer : Name
  family : Name
  rule : Name
deriving Repr, BEq, Hashable, Inhabited

structure ConceptId where
  name : Name
deriving Repr, BEq, Hashable, Inhabited

structure RelationId where
  name : Name
deriving Repr, BEq, Hashable, Inhabited

structure ArgumentRole where
  name : Name
deriving Repr, BEq, Hashable, Inhabited

structure ObligationRole where
  name : Name
deriving Repr, BEq, Hashable, Inhabited

inductive SpeechAct
  | assertion
  | reduction
  | announcement
  | introduction
deriving Repr, BEq, Inhabited

inductive ProvisionPolicy
  | requireExplicit
  | inferCanonical
  | selectionOnly
deriving Repr, BEq, Inhabited

inductive SortConstraint
  | proposition
  | data
  | anySort
deriving Repr, BEq, Inhabited

/-- A reusable dependent type-pattern identity.  Concrete frontends interpret
the builder against the exact elaborated operand roles; the shared layer keeps
the pattern language-neutral. -/
structure TypePattern where
  builder : Name
  operandRoles : Array ArgumentRole := #[]
  expectedSort : SortConstraint := .anySort
deriving Repr, BEq, Inhabited

structure OperandSchema where
  role : ArgumentRole
  concept : ConceptId
  provision : ProvisionPolicy
  typePattern : TypePattern := { builder := .anonymous }
deriving Repr, BEq, Inhabited

structure BindingSchema where
  role : ArgumentRole
  concept : ConceptId
  typePattern : TypePattern := { builder := .anonymous }
deriving Repr, BEq, Inhabited

inductive EffectSchema
  | closeMain
  | replaceMain (obligations : Array ObligationRole)
      (bindings : Array BindingSchema := #[])
  | addLocalFact (binding : BindingSchema)
  | introduce (bindings : Array BindingSchema)
  | guardUnchanged
deriving Repr, BEq, Inhabited

/-- A sentence either has one fixed proof-state effect or denotes a reusable
mathematical assertion.  An assertion intrinsically proves one proposition;
its outer destination is selected independently by the surface envelope. -/
inductive SentenceEffectSchema
  | fixed (effect : EffectSchema)
  | assertion
deriving Repr, BEq, Inhabited

structure RuleSchema where
  id : RuleId
  act : SpeechAct
  result : RelationId
  inputs : Array OperandSchema
  outputs : Array BindingSchema
  effect : EffectSchema
deriving Repr, BEq, Inhabited

structure PresentationAnnotation where
  key : Name
  value : String
deriving Repr, BEq, Inhabited

def rule (layer family operation : Name) : RuleId :=
  ⟨layer, family, operation⟩

def concept (name : Name) : ConceptId := ⟨name⟩
def relation (name : Name) : RelationId := ⟨name⟩
def role (name : Name) : ArgumentRole := ⟨name⟩
def obligation (name : Name) : ObligationRole := ⟨name⟩

def explicitOperand (role : ArgumentRole) (concept : ConceptId) : OperandSchema :=
  { role, concept, provision := .requireExplicit,
    typePattern := { builder := concept.name } }

def canonicalOperand (role : ArgumentRole) (concept : ConceptId) : OperandSchema :=
  { role, concept, provision := .inferCanonical,
    typePattern := { builder := concept.name } }

def selectedOperand (role : ArgumentRole) (concept : ConceptId) : OperandSchema :=
  { role, concept, provision := .selectionOnly,
    typePattern := { builder := concept.name } }

def typedBinding (role : ArgumentRole) (concept : ConceptId) : BindingSchema :=
  { role, concept, typePattern := { builder := concept.name } }

end CryptoLanguage.LanguageDesign

import Verbose.Core

/-!
# Canonical English rendering

Rendering starts from stable mathematical rule and operand roles.  It never
pretty-prints an arbitrary elaborated expression to manufacture a missing
author choice.
-/

namespace CryptoLanguage.Verbose.English

open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules

structure RenderToken where
  role : ArgumentRole
  text : String

structure CanonicalRenderPlan where
  tokens : Array RenderToken

private def typeRole (bindingRole : ArgumentRole) : ArgumentRole :=
  role (bindingRole.name.str "type")

private def token (plan : CanonicalRenderPlan) (wanted : ArgumentRole) : Except String String :=
  match plan.tokens.find? (·.role == wanted) with
  | some value => pure value.text
  | none => throw s!"canonical rendering requires an author-supplied `{wanted.name}` reference or name"

private def operandForRole? (invocation : RuleInvocation)
    (wanted : ArgumentRole) : Option ElaboratedOperand :=
  invocation.operands.find? (·.role == wanted)

private def input (invocation : RuleInvocation) (plan : CanonicalRenderPlan)
    (wanted : ArgumentRole) : Except String String := do
  let some operand := operandForRole? invocation wanted
    | throw s!"the rule invocation has no `{wanted.name}` operand"
  let text ← token plan wanted
  return match operand.note? with
    | some note => s!"{text} noted {reprStr note}"
    | none => text

private def renderRule (invocation : RuleInvocation)
    (plan : CanonicalRenderPlan) : Except String String := do
  let formId :=
    if invocation.ruleId == structuralFix then
      if plan.tokens.any (·.role == role `condition) then
        `structural.fixWith
      else `structural.fix
    else
      let candidates := SurfaceContract.canonicalFormsForRule invocation.ruleId
      if candidates.size == 1 then candidates[0]!.id else .anonymous
  let some form := SurfaceContract.canonicalFormById? formId
    | throw s!"no unique canonical English form is registered for {invocation.ruleId.layer}.{invocation.ruleId.family}.{invocation.ruleId.rule}"
  let values ← form.template.holeIds.mapM fun id => do
    let wanted := role id
    let text ← match operandForRole? invocation wanted with
      | some _ => input invocation plan wanted
      | none => token plan wanted
    pure (id, text)
  form.template.instantiateChecked values

/-- An opaque rendering capability bound to one exact application occurrence.

Callers cannot turn an unrelated source citation into authority for another
rule.  The profile, theorem, backend, and rule are all checked when this token
is created. -/
private structure EffectiveApplicationLicense where
  key : ApplicationOccurrenceKey
  attestation : Corpus.Attestation

/-- Resolve the language license for one exact application occurrence. -/
def effectiveApplicationLicense? (profile : String) (declaration backend : Lean.Name)
    (ruleId : RuleId) : Option EffectiveApplicationLicense := do
  let attestation ← Corpus.applicationAttestationFor?
    profile declaration backend ruleId
  guard attestation.isPubliclyLicensed
  return {
    key := { profile, declaration, backendDeclaration := backend, ruleId }
    attestation
  }

/-- Render one checked invocation from explicit printable references. Missing
references fail closed; elaborated expressions are never used as fallback
source text. Generic rendering deliberately ignores application-only licenses. -/
def renderCanonical (invocation : RuleInvocation)
    (plan : CanonicalRenderPlan) : Except String String := do
  let some attestation := Corpus.attestationFor? invocation.ruleId
    | throw s!"no source attestation is registered for {invocation.ruleId.layer}.{invocation.ruleId.family}.{invocation.ruleId.rule}"
  unless attestation.isPubliclyLicensed do
    throw s!"the sentence for {invocation.ruleId.layer}.{invocation.ruleId.family}.{invocation.ruleId.rule} is pending source attestation"
  renderRule invocation plan

/-- Render one checked assertion occurrence. The `Fact` envelope contributes
only the local discourse anchor; the mathematical sentence still comes from
the assertion's registered rule. -/
def renderAssertionOccurrence (occurrence : AssertionOccurrenceSummary)
    (plan : CanonicalRenderPlan) : Except String String := do
  let body ← renderCanonical occurrence.invocation plan
  match occurrence.destination with
  | .closeMain => return body
  | .localFact name =>
      return SurfaceContract.namedFact name.toString body

/-- Render an assertion occurrence with its exact application-scoped license.
This is the path used for source-attested S1 facts such as the switching
conditional law. -/
def renderAssertionOccurrenceWithApplicationLicense
    (occurrence : AssertionOccurrenceSummary) (plan : CanonicalRenderPlan)
    (license : EffectiveApplicationLicense) : Except String String := do
  unless occurrence.applicationKey? == some license.key do
    throw "the application license does not authorize this exact theorem/backend occurrence"
  unless occurrence.invocation.ruleId == license.key.ruleId do
    throw s!"the application occurrence does not carry the licensed rule"
  let body ← renderRule occurrence.invocation plan
  match occurrence.destination with
  | .closeMain => return body
  | .localFact name =>
      return SurfaceContract.namedFact name.toString body

private def dummyOperand (schema : OperandSchema) : ElaboratedOperand :=
  ⟨schema.role, .sort .zero, .sort (.succ .zero), none⟩

/-- A parser-facing template is generated by the same renderer used for
checked invocations.  Operand and binding placeholders are role-labelled;
there is no separately maintained English copy in the catalog. -/
def renderTemplate (descriptor : SentenceDescriptor) : Except String String := do
  unless descriptor.sourceAttestation.isPubliclyLicensed do
    throw s!"the sentence for {descriptor.ruleId.layer}.{descriptor.ruleId.family}.{descriptor.ruleId.rule} is pending source attestation"
  let invocation : RuleInvocation :=
    ⟨descriptor.ruleId, descriptor.schema.inputs.map dummyOperand⟩
  let inputTokens := descriptor.schema.inputs.map fun schema =>
    ⟨schema.role, schema.role.name.toString⟩
  let bindingTokens := descriptor.schema.outputs.flatMap fun schema => #[
    ⟨schema.role, schema.role.name.toString⟩,
    ⟨typeRole schema.role, s!"{schema.role.name}Type"⟩]
  renderRule invocation ⟨inputTokens ++ bindingTokens⟩

end CryptoLanguage.Verbose.English

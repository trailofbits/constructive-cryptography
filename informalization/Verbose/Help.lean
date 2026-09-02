import Verbose.English.Structural
import Verbose.English.Render
import RandomSystems.Technique.BlindWinning

/-! Registry-backed, parser-checked contextual assistance. -/

register_option cryptoVerbose.helpEnabled : Bool := {
  defValue := true
  descr := "enable contextual help for the Crypto Verbose frontend"
}

register_option cryptoVerbose.suggestionsEnabled : Bool := {
  defValue := true
  descr := "enable non-inserting Crypto Verbose sentence suggestions"
}

namespace CryptoLanguage.Verbose.Help

open Lean Elab Command Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Ontology
open CryptoLanguage.Verbose

private partial def containsConstName (expression : Expr) (wanted : Name) : Bool :=
  match expression with
  | .const name _ => name == wanted
  | .app function argument =>
      containsConstName function wanted || containsConstName argument wanted
  | .lam _ domain body _ | .forallE _ domain body _ =>
      containsConstName domain wanted || containsConstName body wanted
  | .letE _ type value body _ =>
      containsConstName type wanted || containsConstName value wanted ||
        containsConstName body wanted
  | .mdata _ body | .proj _ _ body => containsConstName body wanted
  | _ => false

inductive GoalClass
  | equality
  | construction
  | conditionalEquivalence
  | advantageBound
  | distanceBound
  | winningBound
  | proposition
deriving BEq

private def classify (type : Expr) : GoalClass :=
  if type.getAppFn.constName? == some ``Eq then .equality
  else if containsConstName type `AbstractCryptography.Constructs then .construction
  else if containsConstName type `RandomSystems.PDG.CondEquiv then .conditionalEquivalence
  else if containsConstName type `RandomSystems.PDG.blindSupWinProb ||
      containsConstName type `RandomSystems.PDG.winningMass then .winningBound
  else if containsConstName type `EDist.edist || containsConstName type `edist then .distanceBound
  else if containsConstName type `RandomSystems.PDS.advFullyDefined ||
      containsConstName type `RandomSystems.MultiInterface.PDS.advantage then .advantageBound
  else .proposition

private def relevant (goalClass : GoalClass) (entry : SentenceDescriptor) : Bool :=
  if entry.ruleId.layer == `structural then true else
  match goalClass with
  | .equality => entry.schema.result == Relations.equality
  | .construction => entry.schema.result == Relations.construction
  | .conditionalEquivalence => entry.schema.result == Relations.conditionalEquivalence
  | .advantageBound => entry.schema.result == Relations.advantageBound
  | .distanceBound => entry.schema.result == Relations.distanceBound
  | .winningBound => entry.schema.result == Relations.winningBound
  | .proposition => false

private def rendered? (entry : SentenceDescriptor) : Option String :=
  (English.renderTemplate entry).toOption

private def line (entry : SentenceDescriptor) : Option String := do
  let source ← rendered? entry
  let attestation := entry.sourceAttestation
  return s!"{entry.ruleId.layer}.{entry.ruleId.family}.{entry.ruleId.rule}\n  {source}\n  {entry.summary}\n  source: {attestation.source.label}, {attestation.work}, {attestation.locator} ({attestation.strength.label}; {attestation.construction})"

private def catalogIsValid (environment : Environment)
    (catalog : Array SentenceDescriptor) : Bool :=
  !catalog.isEmpty && catalog.all fun entry =>
    entry.ruleId == entry.schema.id && entry.act == entry.schema.act &&
      (match entry.effect with
      | .fixed effect => effect == entry.schema.effect
      | .assertion => entry.act == .assertion &&
          entry.schema.effect == .closeMain && entry.schema.outputs.isEmpty) &&
      !entry.backendDeclaration.isAnonymous &&
      environment.contains entry.backendDeclaration &&
      entry.sourceAttestation.isPubliclyLicensed &&
      (catalog.filter (·.formId == entry.formId)).size == 1 &&
      catalog.any fun candidate =>
        candidate.ruleId == entry.ruleId && (rendered? candidate).isSome

private def templatesParse (environment : Environment)
    (catalog : Array SentenceDescriptor) : Bool :=
  catalog.all fun entry =>
    match rendered? entry with
    | none => true
    | some source => (Parser.runParserCategory environment `tactic source).isOk

elab "#crypto_verbose_sentences" : command => do
  let catalog ← unsafe registeredSentenceDescriptors
  logInfo <| MessageData.ofFormat <| Format.joinSep
    (catalog.filterMap line).toList (Format.line ++ Format.line)

elab "#crypto_verbose_validate" : command => do
  let catalog ← unsafe registeredSentenceDescriptors
  let environment ← getEnv
  unless catalogIsValid environment catalog do
    throwError "the Crypto Verbose sentence registry is inconsistent or lacks a canonical renderer"
  for entry in catalog do
    if let some source := rendered? entry then
      unless (Parser.runParserCategory environment `tactic source).isOk do
        throwError "canonical rendering does not parse as tactic syntax: {source}"
  logInfo m!"validated {catalog.size} registered sentence forms"

elab "#print_crypto_verbose_config" : command => do
  let helpEnabled ← getBoolOption `cryptoVerbose.helpEnabled true
  let suggestionsEnabled ← getBoolOption `cryptoVerbose.suggestionsEnabled true
  logInfo m!"language: English\nprofile: AC + Random Systems research\nhelp: {helpEnabled}\nsuggestions: {suggestionsEnabled}\nproof search: deterministic registries only"

syntax (name := cryptoHelp) "crypto_help" : tactic
syntax (name := cryptoHelpAt) "crypto_help " ident : tactic
syntax (name := cryptoSuggest) "crypto_suggest" : tactic

private def requireEnabled (optionName : Name) (feature : String) : TacticM Unit := do
  unless ← getBoolOption optionName true do
    throwError s!"Crypto Verbose {feature} is disabled by `{optionName}`"

private def matchingLocalProofs (goal : MVarId) : MetaM (Array LocalDecl) :=
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let mut found := #[]
    for declaration in (← getLCtx).decls do
      if let some declaration := declaration then
        if ← withoutModifyingState <| isDefEqGuarded declaration.type target then
          found := found.push declaration
    return found

private def closingRule? (goalClass : GoalClass) : Option RuleId :=
  match goalClass with
  | .construction => some CryptoLanguage.LanguageDesign.Rules.acConstructionFrom
  | .equality => some CryptoLanguage.LanguageDesign.Rules.acEqualityFrom
  | _ => none

private def closingSource (goalClass : GoalClass) (declaration : LocalDecl) :
    Except String String :=
  match closingRule? goalClass with
  | none => .ok s!"exact {declaration.userName}"
  | some closingRule =>
      let proofRole := role `proof
      let invocation : RuleInvocation :=
        ⟨closingRule, #[⟨proofRole, declaration.toExpr, declaration.type, none⟩]⟩
      English.renderCanonical invocation
        ⟨#[⟨proofRole, declaration.userName.toString⟩]⟩

private def dryElaborates (source : String) : TacticM Bool := do
  let environment ← getEnv
  let .ok parsed := Parser.runParserCategory environment `tactic source
    | return false
  let saved ← saveState
  try
    evalTactic parsed
    saved.restore (restoreInfo := true)
    return true
  catch _ =>
    saved.restore (restoreInfo := true)
    return false

private def exactSuggestions (goal : MVarId) : TacticM (Array String) := do
  let goalClass := classify (← goal.getType)
  let proofs ← matchingLocalProofs goal
  let mut suggestions := #[]
  for proof in proofs do
    if let .ok source := closingSource goalClass proof then
      if ← dryElaborates source then
        suggestions := suggestions.push source
  return suggestions

private def contextualLines (goal : MVarId) : TacticM (Array String) := do
  let catalog ← unsafe registeredSentenceDescriptors
  let goalClass := classify (← goal.getType)
  return (catalog.filter (relevant goalClass ·)).filterMap line

elab_rules : tactic
  | `(tactic| crypto_help) => do
      requireEnabled `cryptoVerbose.helpEnabled "help"
      let lines ← contextualLines (← getMainGoal)
      logInfo <| MessageData.ofFormat <| Format.joinSep
        lines.toList (Format.line ++ Format.line)
  | `(tactic| crypto_help $hypothesis:ident) => do
      requireEnabled `cryptoVerbose.helpEnabled "help"
      let goal ← getMainGoal
      withMainContext do
        let declaration ← getLocalDeclFromUserName hypothesis.getId
        let exactMatch ← withoutModifyingState <|
          isDefEqGuarded declaration.type (← goal.getType)
        if exactMatch then
          let source := closingSource (classify (← goal.getType)) declaration
          match source with
          | .ok source =>
              logInfo m!"{hypothesis.getId} exactly proves the current goal.\n\nChecked proof step: {source}"
          | .error error => throwError error
        else
          let catalog ← unsafe registeredSentenceDescriptors
          let entries := catalog.filter (relevant (classify declaration.type) ·)
          logInfo <| MessageData.ofFormat <| Format.joinSep
            (entries.filterMap line).toList (Format.line ++ Format.line)
  | `(tactic| crypto_suggest) => do
      requireEnabled `cryptoVerbose.suggestionsEnabled "suggestions"
      let suggestions ← exactSuggestions (← getMainGoal)
      if suggestions.isEmpty then
        logInfo "No dry-elaborated sentence is available. Use `crypto_help` to inspect forms whose non-canonical mathematical operands must be supplied explicitly."
      else
        logInfo ("Dry-elaborated suggestions (nothing was inserted):\n\n" ++
          String.intercalate "\n\n" suggestions.toList)

end CryptoLanguage.Verbose.Help

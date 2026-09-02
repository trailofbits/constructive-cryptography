import Verbose.Backend

/-!
# Small structural sentence kernel

These forms expose goal reminders, introductions, and explicit elimination.
They do not replace `exact`, calculations, cases, induction, or local
definitions. Named mathematical claims use `Fact NAME:` around a domain
assertion.
-/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.Structural

@[crypto_verbose_sentence] def goalReminder : SentenceDescriptor :=
  descriptor `structural.goal `reminder structuralGoalReminder
    .announcement .guardUnchanged
    Relations.proposition #[explicitOperand (role `proposition) Ontology.proposition]
    "check and foreground the current obligation"
    `CryptoLanguage.Verbose.Backend.guardGoal

@[crypto_verbose_sentence] def fixOne : SentenceDescriptor :=
  descriptor `structural.binder `fix structuralFix
    .introduction (.introduce #[typedBinding (role `object) Ontology.object])
    Relations.proofState #[]
    "introduce one explicitly quantified mathematical object"
    `CryptoLanguage.Verbose.Backend.introOne

@[crypto_verbose_sentence] def fixWith : SentenceDescriptor :=
  descriptor `structural.binder `fixWith structuralFix
    .introduction (.introduce #[
      typedBinding (role `object) Ontology.object,
      typedBinding (role `condition) Ontology.proposition])
    Relations.proofState #[]
    "introduce a quantified object and its stated condition"
    `CryptoLanguage.Verbose.Backend.introTwoWithType

@[crypto_verbose_sentence] def assume : SentenceDescriptor :=
  descriptor `structural.binder `assume structuralAssume
    .introduction (.introduce #[typedBinding (role `assumption) Ontology.proposition])
    Relations.proofState #[]
    "introduce the antecedent of an implication"
    `CryptoLanguage.Verbose.Backend.introOneWithType

@[crypto_verbose_sentence] def choose : SentenceDescriptor :=
  descriptor `structural.elimination `choose structuralChoose
    .introduction (.introduce #[
      typedBinding (role `witness) Ontology.object,
      typedBinding (role `witnessProperty) Ontology.proposition])
    Relations.proofState #[explicitOperand (role `existence) Ontology.proof]
    "eliminate an explicit existential and name its witness"
    `CryptoLanguage.Verbose.Backend.chooseFrom

@[crypto_verbose_sentence] def conjunction : SentenceDescriptor :=
  descriptor `structural.elimination `conjunction structuralConjunction
    .introduction (.introduce #[
      typedBinding (role `leftFact) Ontology.proposition,
      typedBinding (role `rightFact) Ontology.proposition])
    Relations.proofState #[explicitOperand (role `conjunction) Ontology.proof,
      explicitOperand (role `left) Ontology.proposition,
      explicitOperand (role `right) Ontology.proposition]
    "eliminate an explicit conjunction into two named facts"
    `CryptoLanguage.Verbose.Backend.obtainConjunction

end CryptoLanguage.Verbose.Structural

open CryptoLanguage.Verbose

elab (name := internalRemind) "crypto_verbose_remind " statement:term : tactic => do
  runSentenceWith (← getRef) Structural.goalReminder .guardUnchanged
      #[operand (role `proposition) statement] #[] <|
    backendAction Backend.guardGoal (statement)

elab (name := internalFix) "crypto_verbose_fix " name:ident : tactic => do
  runSentenceWithBindings (← getRef) Structural.fixOne (.addLocals #[name.getId])
      #[] #[⟨role `object, name.getId, none⟩] #[] <|
    backendAction Backend.introOne (name)

elab (name := internalFixWith) "crypto_verbose_fix_with " name:ident ", "
    condition:ident ":" property:term : tactic => do
  runSentenceWithBindings (← getRef) Structural.fixWith
      (.addLocals #[name.getId, condition.getId]) #[] #[
        ⟨role `object, name.getId, none⟩,
        ⟨role `condition, condition.getId, some property⟩] #[] <|
      backendAction Backend.introTwoWithType (name, condition, property)

elab (name := internalAssume) "crypto_verbose_assume " name:ident ":"
    proposition:term : tactic => do
  runSentenceWithBindings (← getRef) Structural.assume (.addLocals #[name.getId])
      #[] #[⟨role `assumption, name.getId, some proposition⟩] #[] <|
    backendAction Backend.introOneWithType (name, proposition)

elab (name := internalChoose) "crypto_verbose_choose "
    existence:verboseReference &"as"
    witness:ident ", " factName:ident ":" property:term : tactic => do
  let existenceRef ← decodeReference existence
  runSentenceWithBindings (← getRef) Structural.choose
      (.addLocals #[witness.getId, factName.getId])
      #[⟨role `existence, existenceRef⟩] #[
        ⟨role `witness, witness.getId, none⟩,
        ⟨role `witnessProperty, factName.getId, some property⟩] #[] <|
    backendAction Backend.chooseFrom
      (existenceRef.term, witness, factName, property)

elab (name := internalConjunction) "crypto_verbose_conjunction "
    conjunction:verboseReference
    &"as" leftName:ident ":" left:term ", " rightName:ident ":"
    right:term : tactic => do
  let conjunctionRef ← decodeReference conjunction
  runSentenceWithBindings (← getRef) Structural.conjunction
      (.addLocals #[leftName.getId, rightName.getId])
      #[⟨role `conjunction, conjunctionRef⟩, operand (role `left) left,
        operand (role `right) right] #[
        ⟨role `leftFact, leftName.getId, some left⟩,
        ⟨role `rightFact, rightName.getId, some right⟩] #[] <|
    backendAction Backend.obtainConjunction
      (conjunctionRef.term, leftName, left, rightName, right)

namespace CryptoVerbose

scoped macro &"It" &"remains" &"to" &"prove" statement:term : tactic =>
  `(tactic| crypto_verbose_remind $statement)

scoped macro &"Fix" name:ident : tactic =>
  `(tactic| crypto_verbose_fix $name)

scoped macro &"Fix" name:ident &"with" condition:ident ":" property:term : tactic =>
  `(tactic| crypto_verbose_fix_with $name, $condition : $property)

scoped macro &"Assume" name:ident ":" proposition:term : tactic =>
  `(tactic| crypto_verbose_assume $name : $proposition)

scoped macro &"From" existence:verboseReference "," &"choose" witness:ident
    &"such" &"that"
    factName:ident ":" property:term : tactic =>
  `(tactic| crypto_verbose_choose $existence as $witness, $factName : $property)

scoped macro &"From" conjunction:verboseReference "," &"obtain" leftName:ident ":"
    left:term:max &"and" rightName:ident ":" right:term : tactic =>
  `(tactic| crypto_verbose_conjunction $conjunction as $leftName : $left,
    $rightName : $right)

end CryptoVerbose

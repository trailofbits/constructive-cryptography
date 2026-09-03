import Verbose.Backend

/-!
# Application-scoped rewriting sentence

This sentence is not part of the public `Verbose` umbrella while its source
attestation remains application-specific.  Import this module explicitly from
the application profile that licenses the surface form.
-/

open Lean Elab Tactic Meta
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.LanguageDesign.Ontology

namespace CryptoLanguage.Verbose.Structural

def replaceInClaim : SentenceDescriptor :=
  assertionDescriptor `structural.rewriting `replace proofRewriting
    Relations.equality #[
      explicitOperand (role `old) Ontology.object,
      explicitOperand (role `new) Ontology.object,
      explicitOperand (role `equation) Ontology.equality,
      explicitOperand (role `result) Ontology.object]
    "replace one displayed mathematical expression by an explicitly equal one"
    `CryptoLanguage.Verbose.Backend.replaceInClaim

end CryptoLanguage.Verbose.Structural

open CryptoLanguage.Verbose

elab "crypto_verbose_replace " old:term:max &"by" new:term:max &"using"
    equation:verboseReference &"yields" result:term : tactic => do
  let equationRef ← decodeReference equation
  runSentenceWith (← getRef) Structural.replaceInClaim .closeMain #[
      operand (role `old) old, operand (role `new) new,
      ⟨role `equation, equationRef⟩, operand (role `result) result] #[] <|
    backendAction Backend.replaceInClaim (old, new, equationRef.term, result)

namespace CryptoVerbose

scoped macro &"Replacing" old:term:max &"by" new:term:max &"using"
    equation:verboseReference &"yields" result:term : tactic =>
  `(tactic| crypto_verbose_replace $old by $new using $equation yields $result)

end CryptoVerbose

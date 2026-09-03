import Verbose
import Verbose.English.Statements

/-! Quarantined declaration-prototype tests. `import Verbose` does not expose
this command; these checks are retained only as migration evidence until the
full declaration contract is implemented. -/

open Lean Elab Command
open CryptoLanguage.LanguageDesign
open CryptoLanguage.LanguageDesign.Corpus
open CryptoLanguage.LanguageDesign.Rules
open CryptoLanguage.Verbose.English.Statements
open scoped CryptoVerbose

namespace CryptoLanguage.Verbose.Tests.Statements

Theorem identity "Identity"
  Given:
    (P : Prop)
  Assume:
    (proof : P)
  Conclusion:
    P
  Proof:
    exact proof
  QED

Theorem finiteAlphabetIdentity "Finite alphabet identity"
  Given:
    a finite nonempty alphabet X
    Let q ∈ ℕ
  Conclusion:
    q ≤ q
  Proof:
    exact le_rfl
  QED

#check finiteAlphabetIdentity

run_cmd do
  let declaration := `CryptoLanguage.Verbose.Tests.Statements.identity
  let some presentation := theoremPresentation? (← getEnv) declaration
    | throwError "missing theorem presentation metadata for {declaration}"
  unless presentation.title == "Identity" do
    throwError "unexpected theorem title {presentation.title}"
  unless presentation.ruleId == structuralTheorem do
    throwError "unexpected theorem presentation rule"
  unless presentation.binders.size == 2 && presentation.givens.size == 1 &&
      presentation.assumptionCount == 1 do
    throwError "the theorem presentation lost its exact telescope structure"
  let some declarationInfo := (← getEnv).find? declaration
    | throwError "missing elaborated theorem declaration"
  unless presentation.exactType == declarationInfo.type do
    throwError "the theorem presentation did not retain the exact declaration type"
  let some attestation := attestationFor? presentation.ruleId
    | throwError "the theorem declaration rule has no source attestation"
  unless attestation.isValid do
    throwError "the theorem declaration attestation is invalid"

run_cmd do
  let declaration :=
    `CryptoLanguage.Verbose.Tests.Statements.finiteAlphabetIdentity
  let some presentation := theoremPresentation? (← getEnv) declaration
    | throwError "missing natural theorem presentation metadata"
  unless presentation.binders.size == 5 && presentation.givens == #[
      .finiteNonemptyAlphabet `X,
      .naturalNumber `q SurfaceContract.naturalNumberForm.id] &&
      presentation.assumptionCount == 0 do
    throwError "natural theorem inputs did not expand to the exact five-binder telescope"

/- The command is still fail-closed: readable syntax does not weaken Lean's
checking of the conclusion against the proof. -/
/-- error: Type mismatch -/
#guard_msgs (substring := true) in
Theorem rejectsWrongProof "Rejected theorem"
  Given:
    (P Q : Prop)
  Assume:
    (proof : P)
  Conclusion:
    Q
  Proof:
    exact proof
  QED

end CryptoLanguage.Verbose.Tests.Statements

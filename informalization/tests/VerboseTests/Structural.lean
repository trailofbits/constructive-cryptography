import Verbose
import Verbose.English.Rewriting
import Verbose.RandomSystems

open Lean Elab Tactic
open CryptoLanguage.LanguageDesign
open CryptoLanguage.Verbose
open scoped CryptoVerbose

namespace CryptoLanguage.Verbose.Tests.Structural

private def testReplaceDescriptor : SentenceDescriptor := {
  CryptoLanguage.Verbose.Structural.replaceInClaim with
  sourceAttestation := {
    source := .projectControlled
    work := "Verbose rewriting regression harness"
    locator := "private checked-result mutation test"
    construction := `test.rewriting.checkedResult
    strength := .exactFormalRelation
  }
}

elab "test_replace " old:term:max " by " new:term:max " using " equation:term
    " yields " result:term : tactic => do
  runSentenceWith (← getRef) testReplaceDescriptor .closeMain #[
      operand (role `old) old, operand (role `new) new,
      operand (role `equation) equation, operand (role `result) result] #[] <|
    backendAction CryptoLanguage.Verbose.Backend.replaceInClaim
      (old, new, equation, result)

example (P : Prop) (proof : P) : P := by
  have namedProof : P := proof
  exact namedProof

/- A `Fact` anchor is a stable discourse name, not a shadowing binder. -/
example {X Y : Type*} (game : RandomSystems.PDG X Y)
    (system : RandomSystems.PDS X Y)
    (conditionalLaw : RandomSystems.PDG.CondEquiv game system) : True := by
  fail_if_success
    Fact conditionalLaw: The game game is conditionally equivalent to system by
      conditionalLaw
  trivial

example (P Q : Prop) (proofP : P) (proofQ : Q) : P := by
  have paired : P ∧ Q := ⟨proofP, proofQ⟩
  From paired, obtain leftProof : P and rightProof : Q
  exact leftProof

/- The displayed result must be the expression actually produced by the
replacement, not merely one side of the original equality. -/
example (a b : Nat) (equation : b = a) : a = b := by
  fail_if_success
    test_replace b by a using equation yields b
  test_replace b by a using equation yields a

/- A bare overloaded literal is not recorded under one default type and then
used by the backend under another. -/
example : (0 : ENNReal) = 0 := by
  fail_if_success
    test_replace 0 by (0 : ENNReal) using (Eq.refl (0 : ENNReal)) yields
      (0 : ENNReal)
  rfl

/- A logical equivalence has two projections but is not a conjunction. -/
example (P Q : Prop) (equivalence : P ↔ Q) : True := by
  fail_if_success
    From equivalence, obtain forward : (P → Q) and backward : (Q → P)
  trivial

example (P : Nat → Prop) (existence : ∃ n, P n) : True := by
  From existence, choose witness such that witnessProperty : P witness
  trivial

set_option linter.unusedTactic false in
example : ∀ n : Nat, n = n := by
  Fix n
  It remains to prove n = n
  rfl

example (P : Nat → Prop) : ∀ n, P n → P n := by
  Fix n with hypothesis : P n
  exact hypothesis

example (P Q : Prop) : P → Q → P := by
  Assume proofP : P
  Assume proofQ : Q
  exact proofP

/- The prose vocabulary remains ordinary identifier vocabulary while the
scope is open. -/
def construction := 1
def system := 2
def simulator := 3
def proof := 4
def condition := 5
def bound := 6
def as := 7

example : construction + system + simulator + proof + condition + bound + as = 28 := by
  decide

/- Reserved Lean words remain available through Lean's ordinary escaped-name
mechanism; the controlled grammar does not invent a second escape convention. -/
def «have» := 8

example : «have» = 8 := rfl

/- error: This sentence cannot establish -/
#guard_msgs (substring := true) in
example : True := by
  It remains to prove False

/- error: This sentence cannot establish -/
#guard_msgs (substring := true) in
example (P Q : Prop) (proof : P) : Q := by
  exact proof

end CryptoLanguage.Verbose.Tests.Structural

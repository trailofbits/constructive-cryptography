/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomation

/-!
# Typed AC construction-workflow experiment

This non-default module compares an ordinary certificate value with a locally
indexed certificate typeclass for one deliberately narrow workflow: two
scalar-metric construction steps.  Every non-canonical choice used by that
workflow is a field of `ConstructionProblem`; neither presentation may infer
the protocols, intermediate specification, or errors.

This is an experiment, not a second construction semantics.  Both result
theorems close directly with `ac_compose`, hence ultimately with
`AbstractCryptography.Constructs.epsilonRelaxation_trans`.
-/

open AbstractCryptography
open scoped AbstractCryptography

namespace AbstractCryptography.ConstructionWorkflow.Tests

universe u v

/-- All choices for the tested two-step scalar construction workflow. -/
structure ConstructionProblem (M : Type u) (Phi : Type v) where
  real : Set Phi
  intermediate : Set Phi
  ideal : Set Phi
  firstProtocol : M
  secondProtocol : M
  firstError : ENNReal
  secondError : ENNReal

section Certificates

variable {M : Type u} {Phi : Type v}
variable [Monoid M] [MulAction M Phi] [PseudoEMetricSpace Phi]
variable [IsNonexpandingSMul M Phi]

/-- Ordinary-value presentation of the two named construction obligations. -/
structure ConstructionCertificateValue (problem : ConstructionProblem M Phi) : Prop where
  first : problem.real —[problem.firstProtocol; problem.firstError]→
    problem.intermediate
  second : problem.intermediate —[problem.secondProtocol; problem.secondError]→
    problem.ideal

/-- The ordinary certificate is only packaging around the public AC theorem. -/
theorem ConstructionCertificateValue.constructs
    {problem : ConstructionProblem M Phi}
    (certificate : ConstructionCertificateValue problem) :
    problem.real —[problem.secondProtocol * problem.firstProtocol;
      problem.firstError + problem.secondError]→ problem.ideal := by
  ac_compose certificate.first, certificate.second

/-- Indexed-class presentation with exactly the same proof fields.  Intended
only as a local instance attached to an explicit `problem`. -/
class ConstructionCertificate (problem : ConstructionProblem M Phi) : Prop where
  first : problem.real —[problem.firstProtocol; problem.firstError]→
    problem.intermediate
  second : problem.intermediate —[problem.secondProtocol; problem.secondError]→
    problem.ideal

/-- The indexed class also delegates directly to the public AC theorem.  The
problem argument is explicit because its intermediate field is intentionally
not reconstructible from the conclusion. -/
theorem ConstructionCertificate.constructs
    (problem : ConstructionProblem M Phi)
    [certificate : ConstructionCertificate problem] :
    problem.real —[problem.secondProtocol * problem.firstProtocol;
      problem.firstError + problem.secondError]→ problem.ideal := by
  ac_compose certificate.first, certificate.second

end Certificates

section Coexistence

variable {M : Type u} {Phi : Type v}
variable [Monoid M] [MulAction M Phi] [PseudoEMetricSpace Phi]
variable [IsNonexpandingSMul M Phi]

variable (real middleA middleB ideal : Set Phi)
variable (firstProtocolA secondProtocolA firstProtocolB secondProtocolB : M)
variable (firstErrorA secondErrorA firstErrorB secondErrorB : ENNReal)

private def problemA : ConstructionProblem M Phi where
  real := real
  intermediate := middleA
  ideal := ideal
  firstProtocol := firstProtocolA
  secondProtocol := secondProtocolA
  firstError := firstErrorA
  secondError := secondErrorA

private def problemB : ConstructionProblem M Phi where
  real := real
  intermediate := middleB
  ideal := ideal
  firstProtocol := firstProtocolB
  secondProtocol := secondProtocolB
  firstError := firstErrorB
  secondError := secondErrorB

variable
  (firstA : real —[firstProtocolA; firstErrorA]→ middleA)
  (secondA : middleA —[secondProtocolA; secondErrorA]→ ideal)
  (firstB : real —[firstProtocolB; firstErrorB]→ middleB)
  (secondB : middleB —[secondProtocolB; secondErrorB]→ ideal)

private def valueCertificateA : ConstructionCertificateValue
    (problemA real middleA ideal firstProtocolA secondProtocolA
      firstErrorA secondErrorA) where
  first := firstA
  second := secondA

private def valueCertificateB : ConstructionCertificateValue
    (problemB real middleB ideal firstProtocolB secondProtocolB
      firstErrorB secondErrorB) where
  first := firstB
  second := secondB

example :
    real —[secondProtocolA * firstProtocolA;
      firstErrorA + secondErrorA]→ ideal :=
  (valueCertificateA real middleA ideal firstProtocolA secondProtocolA
    firstErrorA secondErrorA firstA secondA).constructs

example :
    real —[secondProtocolB * firstProtocolB;
      firstErrorB + secondErrorB]→ ideal :=
  (valueCertificateB real middleB ideal firstProtocolB secondProtocolB
    firstErrorB secondErrorB firstB secondB).constructs

example :
    (real —[secondProtocolA * firstProtocolA;
      firstErrorA + secondErrorA]→ ideal) ∧
    (real —[secondProtocolB * firstProtocolB;
      firstErrorB + secondErrorB]→ ideal) := by
  letI : ConstructionCertificate
      (problemA real middleA ideal firstProtocolA secondProtocolA
        firstErrorA secondErrorA) := {
    first := firstA
    second := secondA
  }
  letI : ConstructionCertificate
      (problemB real middleB ideal firstProtocolB secondProtocolB
        firstErrorB secondErrorB) := {
    first := firstB
    second := secondB
  }
  constructor
  · exact ConstructionCertificate.constructs
      (problemA real middleA ideal firstProtocolA secondProtocolA
        firstErrorA secondErrorA)
  · exact ConstructionCertificate.constructs
      (problemB real middleB ideal firstProtocolB secondProtocolB
        firstErrorB secondErrorB)

/-- error: Fields missing: `second` -/
#guard_msgs (substring := true) in
private def incompleteValueCertificate : ConstructionCertificateValue
    (problemA real middleA ideal firstProtocolA secondProtocolA
      firstErrorA secondErrorA) where
  first := firstA

end Coexistence

section MissingInstance

variable {M : Type u} {Phi : Type v}
variable [Monoid M] [MulAction M Phi] [PseudoEMetricSpace Phi]
variable [IsNonexpandingSMul M Phi]

/-- error: failed to synthesize instance of type class
  ConstructionCertificate problem -/
#guard_msgs (substring := true) in
example (problem : ConstructionProblem M Phi) :
    problem.real —[problem.secondProtocol * problem.firstProtocol;
      problem.firstError + problem.secondError]→ problem.ideal :=
  ConstructionCertificate.constructs problem

end MissingInstance

end AbstractCryptography.ConstructionWorkflow.Tests

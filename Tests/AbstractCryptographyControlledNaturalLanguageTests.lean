/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ControlledNaturalLanguage

/-!
# Abstract Cryptography controlled-language tests

These examples check that the first controlled-language slice is only a
readable frontend for the existing deterministic AC proof commands.  The
tests are carrier-polymorphic and use neither finite interface enumeration nor
heartbeat overrides.
-/

open AbstractCryptography
open scoped AbstractCryptography CryptoControlledNaturalLanguage

namespace AbstractCryptography.ControlledNaturalLanguage.Tests

universe u v w

variable {I : Type u} {Gamma : I -> Type v} {Phi : Type w}
variable [forall i, Monoid (Gamma i)] [MulAction (forall i, Gamma i) Phi]
variable [PseudoEMetricSpace Phi]

example (protocol : forall i, Gamma i) (real ideal : Phi)
    (actionEquation : protocol • real = ideal) :
    ⟪real⟫ —[protocol]→ ⟪ideal⟫ := by
  The construction follows from actionEquation

example (protocol : forall i, Gamma i) (real ideal : Phi)
    (error : ENNReal) (distanceBound : edist (protocol • real) ideal <= error) :
    ⟪real⟫ —[protocol; error]→ ⟪ideal⟫ := by
  The construction follows from distanceBound

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i} (resource : Phi)
    (protocolEquation : protocol = protocol') :
    protocol • resource = protocol' • resource := by
  The equality follows from protocolEquation

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i}
    {real ideal : Set Phi} (protocolEquation : protocol = protocol')
    (construction : real —[protocol]→ ideal) :
    real —[protocol']→ ideal := by
  Replacing the protocol in construction using protocolEquation,
    we obtain the required construction

example [IsNonexpandingSMul (forall i, Gamma i) Phi]
    {firstProtocol secondProtocol : forall i, Gamma i}
    {real middle ideal : Set Phi} {firstError secondError : ENNReal}
    (firstLeg : real —[firstProtocol; firstError]→ middle)
    (secondLeg : middle —[secondProtocol; secondError]→ ideal) :
    real —[secondProtocol * firstProtocol; firstError + secondError]→ ideal := by
  The construction follows by composing firstLeg and secondLeg

example (protocol : forall i, Gamma i) (real ideal : Phi)
    (error : ENNReal) (distanceBound : edist (protocol • real) ideal ≤ error) :
    ⟪real⟫ —[protocol; error]→ ⟪ideal⟫ := by
  We have construction : ⟪real⟫ —[protocol; error]→ ⟪ideal⟫ by
    The construction follows from distanceBound
  The construction follows from construction

example (protocol : forall i, Gamma i) (real ideal : Phi)
    (error : ENNReal)
    (existingConstruction : ⟪real⟫ —[protocol; error]→ ⟪ideal⟫) :
    ⟪real⟫ —[protocol; error]→ ⟪ideal⟫ := by
  We have construction : ⟪real⟫ —[protocol; error]→ ⟪ideal⟫
    from existingConstruction
  The construction follows from construction

example (protocol simulator : forall i, Gamma i)
    (simulators : Submonoid (forall i, Gamma i)) (real ideal : Phi)
    (error : ENNReal) (simulatorMembership : simulator ∈ simulators)
    (distanceBound : edist (protocol • real) (simulator • ideal) ≤ error) :
    ⟪real⟫ —[protocol; error]→ (⟪ideal⟫ ^⋆[simulators]) := by
  We use simulator to prove the construction
  · exact simulatorMembership
  · exact distanceBound

example [Par (forall i, Gamma i)] [Par Phi]
    [SMulParClass (forall i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : forall i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal}
    (construction : real —[protocol; error]→ ideal) :
    real ∥ context —[protocol ∥ 1; error]→ ideal ∥ context := by
  With context as the right parallel context,
    the construction follows from construction

example [IsNonexpandingSMul (forall i, Gamma i) Phi]
    {firstProtocol secondProtocol : forall i, Gamma i}
    {real middle ideal : Set Phi} {firstError secondError : ENNReal}
    (firstLeg : real —[firstProtocol; firstError]→ middle)
    (secondLeg : middle —[secondProtocol; secondError]→ ideal) :
    real —[secondProtocol * firstProtocol; firstError + secondError]→ ideal := by
  The construction follows by composing
    firstLeg ("The first protocol constructs the intermediate resource.") and
    secondLeg ("The second protocol constructs the ideal resource.")

example [Par (forall i, Gamma i)] [Par Phi]
    [SMulParClass (forall i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : forall i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal}
    (construction : real —[protocol; error]→ ideal) :
    context ∥ real —[1 ∥ protocol; error]→ context ∥ ideal := by
  With context as the left parallel context,
    the construction follows from construction

example [Par (forall i, Gamma i)] [Par Phi]
    [SMulParClass (forall i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : forall i, Gamma i} {real ideal context : Phi}
    {error : ENNReal}
    (construction : ⟪real⟫ —[protocol; error]→ ⟪ideal⟫) :
    ⟪real ∥ context⟫ —[protocol ∥ 1; error]→ ⟪ideal ∥ context⟫ := by
  With context as the right parallel context,
    the construction follows from construction

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.follows_from -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
omit [PseudoEMetricSpace Phi] in
example (protocol : forall i, Gamma i) (real ideal : Phi)
    (actionEquation : protocol • real = ideal) :
    ⟪real⟫ —[protocol]→ ⟪ideal⟫ := by
  The construction follows from actionEquation

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.equality.follows_from -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i} (resource : Phi)
    (protocolEquation : protocol = protocol') :
    protocol • resource = protocol' • resource := by
  The equality follows from protocolEquation

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.replace_protocol -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i}
    {real ideal : Set Phi} (protocolEquation : protocol = protocol')
    (construction : real —[protocol]→ ideal) :
    real —[protocol']→ ideal := by
  Replacing the protocol in construction using protocolEquation,
    we obtain the required construction

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.by_composition -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example [IsNonexpandingSMul (forall i, Gamma i) Phi]
    {firstProtocol secondProtocol : forall i, Gamma i}
    {real middle ideal : Set Phi} {firstError secondError : ENNReal}
    (firstLeg : real —[firstProtocol; firstError]→ middle)
    (secondLeg : middle —[secondProtocol; secondError]→ ideal) :
    real —[secondProtocol * firstProtocol; firstError + secondError]→ ideal := by
  The construction follows by composing firstLeg and secondLeg

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.from_simulator -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example (protocol simulator : forall i, Gamma i)
    (simulators : Submonoid (forall i, Gamma i)) (real ideal : Phi)
    (error : ENNReal) (simulatorMembership : simulator ∈ simulators)
    (distanceBound : edist (protocol • real) (simulator • ideal) ≤ error) :
    ⟪real⟫ —[protocol; error]→ (⟪ideal⟫ ^⋆[simulators]) := by
  We use simulator to prove the construction
  · exact simulatorMembership
  · exact distanceBound

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.argument.named_fact -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example (proposition : Prop) (proof : proposition) : proposition := by
  We have intermediateFact : proposition by
    exact proof
  exact intermediateFact

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.right_parallel_context -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example [Par (forall i, Gamma i)] [Par Phi]
    [SMulParClass (forall i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : forall i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal}
    (construction : real —[protocol; error]→ ideal) :
    real ∥ context —[protocol ∥ 1; error]→ ideal ∥ context := by
  With context as the right parallel context,
    the construction follows from construction

/-- trace: [CryptoControlledNaturalLanguage.sentence] ac.construction.left_parallel_context -/
#guard_msgs in
set_option trace.CryptoControlledNaturalLanguage.sentence true in
example [Par (forall i, Gamma i)] [Par Phi]
    [SMulParClass (forall i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : forall i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal}
    (construction : real —[protocol; error]→ ideal) :
    context ∥ real —[1 ∥ protocol; error]→ context ∥ ideal := by
  With context as the left parallel context,
    the construction follows from construction

/-- error: ac_construct could not use the supplied equality, inclusion, distance bound, or pointwise proof -/
#guard_msgs (substring := true) in
example (irrelevantFact : True) : True := by
  The construction follows from irrelevantFact

/-- error: ac_transport expected a protocol-action equality or exact/scalar construction equivalence matching the supplied protocol equality -/
#guard_msgs (substring := true) in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i}
    (protocolEquation : protocol = protocol') : True := by
  The equality follows from protocolEquation

/-- error: ac_transport could not replace the protocol in the supplied construction using the supplied equality -/
#guard_msgs (substring := true) in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : forall i, Gamma i}
    (protocolEquation : protocol = protocol') (irrelevantFact : True) : True := by
  Replacing the protocol in irrelevantFact using protocolEquation,
    we obtain the required construction

/-- error: ac_compose expected two composable exact or scalar-metric construction proofs -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  The construction follows by composing firstFact and secondFact

/-- error: ac_simulator expected a singleton construction into an epsilon-ball around an explicit star relaxation -/
#guard_msgs (substring := true) in
example (simulator : forall i, Gamma i) : True := by
  We use simulator to prove the construction

/-- error: ac_context_left expected an exact or scalar-metric construction and a fixed right context -/
#guard_msgs (substring := true) in
example (context construction : Set Phi) : True := by
  With context as the right parallel context,
    the construction follows from construction

/-- error: expected `construction` or `equality` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (protocol : forall i, Gamma i) (real ideal : Phi)
    (actionEquation : protocol • real = ideal) :
    ⟪real⟫ —[protocol]→ ⟪ideal⟫ := by
  The result follows from actionEquation

/-- error: expected `follows` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (protocol : forall i, Gamma i) (real ideal : Phi)
    (actionEquation : protocol • real = ideal) :
    ⟪real⟫ —[protocol]→ ⟪ideal⟫ := by
  The construction follow from actionEquation

/-- error: expected `composing` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  The construction follows by combining firstFact and secondFact

/-- error: expected `left` or `right` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (context construction : Set Phi) : True := by
  With context as the middle parallel context,
    the construction follows from construction

/-- error: expected `use` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example (simulator : forall i, Gamma i) : True := by
  We choose simulator to prove the construction

/-- error: deliberate intermediate-fact failure -/
#guard_msgs (substring := true) in
example : True := by
  We have intermediateFact : True by
    fail "deliberate intermediate-fact failure"
  exact intermediateFact

/-- error: expected `have` in this controlled-language sentence -/
#guard_msgs (substring := true) in
example : True := by
  We possess intermediateFact : True by
    trivial
  exact intermediateFact

end AbstractCryptography.ControlledNaturalLanguage.Tests

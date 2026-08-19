/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomation
import AbstractCryptography.MR11

/-!
# Abstract Cryptography proof-language tests

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

This non-default module checks the paper-facing AC notation against its stable
declaration-level expansion.  All examples are polymorphic in the resource and
interface carriers; no finite interface enumeration or heartbeat override is
used.

The checked paper-style matrix is:

| Proof shape | Source receipt | Selected modeling delta | Expected open goals |
| --- | --- | --- | --- |
| exact singleton | JM20 Def. 1, p. 8; CR18 Def. 5.4, pp. 115--116 | singleton specialization of set construction | equality, or none with `using` |
| scalar singleton/general set | JM20 Defs. 1 and 3, pp. 8 and 10 | one `ENNReal` pseudo-emetric ball | one distance / the pointwise witness |
| supplied protocol equality | equality congruence | no recursive rewriting of expansive converter equations | none after the explicit equation/construction proof |
| simulator to star | MauRen16 §4.2 Lemma 5, pp. 11--13 | explicit simulator witness; no synthesized simulator | membership and distance |
| exact/metric filtered pattern | MauRen11 §7.4 Theorem 2, pp. 15--16 | choice-free endpoint-pattern analogue | explicit support plus equality/distance |
| exact/relaxed serial | MauRen11 Defs. 5--7, p. 8; JM20 Thm. 1.1 and Cor. 1 | right factor acts first; scalar additive error | none after named legs |
| parallel and ordered context | MauRen11 Def. 7, p. 8; JM20 Thm. 1.2, p. 8 | explicit `protocol ∥ 1` / `1 ∥ protocol` | none after named legs |
| triangle and non-expansion | MauRen11 Defs. 13--16, pp. 12--14 | pseudo-emetric and ordered contexts remain mixins | two legs / none |
| property transfer | MauRen11 Defs. 15--16, pp. 13--14; LiuMau20 specification idiom | `propSpec` endpoint is an explicit project lemma | none after the five explicit hypotheses |
| zero-distance separation | MauRen11 Eq. (2), p. 9 | only with explicit `Set.SeparatesPoints` | none |
| two distinguisher metrics | MauRen11 §6.1, pp. 13--14 | both metrics stay local; no global instance | none |
| intentional failures | proof-language contract | no recovery/search fallback | one rule-specific diagnostic |

A 2026-07-21 `lean --profile` run measured 124 ms total elaboration for this
whole module after its 1.47 s import; no individual example crossed the 10 ms
profiling threshold. First-process metaprogram interpretation is reported
separately by Lean and does not indicate proof search or heartbeat pressure.
-/

open AbstractCryptography
open Pointwise
open scoped AbstractCryptography

namespace AbstractCryptography.ProofAutomation.Tests

universe u v w

variable {I : Type u} {Gamma : I → Type v} {Phi : Type w}
variable [∀ i, Monoid (Gamma i)] [MulAction (∀ i, Gamma i) Phi]
variable [PseudoEMetricSpace Phi]

example (R S : Phi) (error : ENNReal) : (R ≈[error] S) ↔ edist R S ≤ error :=
  Iff.rfl

example (R S T : Phi) [Par Phi] (error : ENNReal) :
    (R ∥ T ≈[error] S ∥ T) ↔ edist (R ∥ T) (S ∥ T) ≤ error :=
  Iff.rfl

example (real ideal : Set Phi) :
    (real —[∃ (∀ i, Gamma i)]→ ideal) ↔ Reduces (∀ i, Gamma i) real ideal :=
  Iff.rfl

example (relaxation : Relaxation Phi) (specification : Set Phi) :
    specification ^ᵣ[relaxation] = relaxation specification :=
  rfl

example (specification : Set Phi) (error : ENNReal) :
    specification ^ε[error] = Relaxation.epsilonRelaxation error specification :=
  rfl

example (simulators : Submonoid (∀ i, Gamma i)) (specification : Set Phi) :
    specification ^⋆[simulators] = Relaxation.star simulators specification :=
  rfl

example (protocol : ∀ i, Gamma i) (P : Set I) :
    protocol ⇂ P = patternAttach P protocol :=
  rfl

example (protocol : ∀ i, Gamma i) (P : Set I) (R : Phi) :
    protocol ⇂ Pᶜ • R = patternAttach Pᶜ protocol • R :=
  rfl

example (R : Phi) : ⟪R⟫ = ({R} : Set Phi) :=
  rfl

section PaperFilterFacade

variable (queryLimit : Nat → (∀ i, Gamma i))

/- A deliberately narrow application scope may reproduce a paper's `[r]`
filter literally.  A local macro rule is required: ordinary notation would be
ambiguous with Lean's singleton-list syntax. -/
local macro_rules
  | `([$r]) => `(queryLimit $r)

omit [PseudoEMetricSpace Phi] in
example (theta cbc : ∀ i, Gamma i) (r : Nat)
    (filterExchange : theta * cbc = theta * cbc * queryLimit r) :
    theta * cbc = theta * cbc * [r] :=
  filterExchange

omit [PseudoEMetricSpace Phi] in
example (theta cbc : ∀ i, Gamma i) (r : Nat) (R : Phi)
    (filterExchange : theta * cbc = theta * cbc * queryLimit r) :
    (theta * cbc) • R = (theta * cbc * [r]) • R := by
  ac_transport using filterExchange

end PaperFilterFacade

example (protocol : ∀ i, Gamma i) (real ideal : Set Phi) (error : ENNReal) :
    (real —[protocol; error]→ ideal) ↔
      real —[protocol]→ Relaxation.epsilonRelaxation error ideal :=
  Iff.rfl

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    (same : protocol = protocol') :
    (real —[protocol]→ ideal) ↔ real —[protocol']→ ideal :=
  constructs_congr_protocol same

example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    {error : ENNReal} (same : protocol = protocol') :
    (real —[protocol; error]→ ideal) ↔
      real —[protocol'; error]→ ideal :=
  approximately_constructs_congr_protocol same

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} (R : Phi)
    (same : protocol = protocol') :
    protocol • R = protocol' • R := by
  ac_transport using same

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    (same : protocol = protocol') :
    (real —[protocol]→ ideal) ↔ real —[protocol']→ ideal := by
  ac_transport using same

example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    {error : ENNReal} (same : protocol = protocol') :
    (real —[protocol; error]→ ideal) ↔
      real —[protocol'; error]→ ideal := by
  ac_transport using same

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    (same : protocol = protocol') (construction : real —[protocol]→ ideal) :
    real —[protocol']→ ideal := by
  ac_transport construction using same

omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    (same : protocol = protocol') (construction : real —[protocol']→ ideal) :
    real —[protocol]→ ideal := by
  ac_transport construction using same

example {protocol protocol' : ∀ i, Gamma i} {real ideal : Set Phi}
    {error : ENNReal} (same : protocol = protocol')
    (construction : real —[protocol; error]→ ideal) :
    real —[protocol'; error]→ ideal := by
  ac_transport construction using same

example (protocol : ∀ i, Gamma i) (real ideal : Set Phi) (error : ENNReal)
    (h : ∀ R ∈ real, ∃ S ∈ ideal, edist (protocol • R) S ≤ error) :
    real —[protocol; error]→ ideal := by
  ac_construct using h

example (protocol : ∀ i, Gamma i) (R S : Phi)
    (h : protocol • R = S) :
    ⟪R⟫ —[protocol]→ ⟪S⟫ := by
  ac_construct using h

example (protocol : ∀ i, Gamma i) (R S : Phi) (error : ENNReal)
    (h : edist (protocol • R) S ≤ error) :
    ⟪R⟫ —[protocol; error]→ ⟪S⟫ := by
  ac_construct using h

example (protocol : ∀ i, Gamma i) (real ideal : Set Phi)
    (h : protocol • real ⊆ ideal) : real —[protocol]→ ideal := by
  ac_construct using h

example (protocol simulator : ∀ i, Gamma i)
    (simulators : Submonoid (∀ i, Gamma i)) (R S : Phi) (error : ENNReal)
    (hsimulator : simulator ∈ simulators)
    (hdistance : edist (protocol • R) (simulator • S) ≤ error) :
    ⟪R⟫ —[protocol; error]→ (⟪S⟫ ^⋆[simulators]) := by
  ac_simulator simulator
  · exact hsimulator
  · exact hdistance

example {P : Set I} {H : ∀ i, Submonoid (Gamma i)}
    {protocol realFilter idealFilter simulator : ∀ i, Gamma i} {R S : Phi}
    (hsupport : ∀ i ∈ Pᶜ, simulator i ∈ H i)
    (hequality : protocol ⇂ P • realFilter ⇂ P • R =
      simulator ⇂ Pᶜ • idealFilter ⇂ P • S) :
    filteredAt P H realFilter R —[protocol ⇂ P]→
      filteredAt P H idealFilter S := by
  ac_filtered using hsupport, hequality

theorem automation_metric_filtered_construction
    [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    {P : Set I} {H : ∀ i, Submonoid (Gamma i)}
    {protocol realFilter idealFilter simulator : ∀ i, Gamma i} {R S : Phi}
    {error : ENNReal} (hsupport : ∀ i ∈ Pᶜ, simulator i ∈ H i)
    (hdistance : protocol ⇂ P • realFilter ⇂ P • R ≈[error]
      simulator ⇂ Pᶜ • idealFilter ⇂ P • S) :
    filteredAt P H realFilter R —[protocol ⇂ P; error]→
      filteredAt P H idealFilter S := by
  ac_filtered using hsupport, hdistance

example (R intermediate S : Phi) (firstError secondError : ENNReal)
    (hfirst : R ≈[firstError] intermediate)
    (hsecond : intermediate ≈[secondError] S) :
    R ≈[firstError + secondError] S := by
  ac_triangle via intermediate
  · exact hfirst
  · exact hsecond

theorem automation_action_nonexpansion
    [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    (protocol : ∀ i, Gamma i) (R S : Phi) :
    protocol • R ≈[edist R S] protocol • S := by
  ac_nonexpand

example [Par Phi] [IsNonexpandingPar Phi] (R S T : Phi) :
    R ∥ T ≈[edist R S] S ∥ T := by
  ac_nonexpand

example [Par Phi] [IsNonexpandingPar Phi] (R S T : Phi) :
    T ∥ R ≈[edist R S] T ∥ S := by
  ac_nonexpand

example [Par Phi] [IsNonexpandingPar Phi] (R R' S S' : Phi) :
    R ∥ S ≈[edist R R' + edist S S'] R' ∥ S' := by
  ac_nonexpand

theorem automation_metric_serial_composition
    [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    {protocol protocol' : ∀ i, Gamma i} {real middle ideal : Set Phi}
    {error error' : ENNReal} (h : real —[protocol; error]→ middle)
    (h' : middle —[protocol'; error']→ ideal) :
    real —[protocol' * protocol; error + error']→ ideal := by
  ac_compose h, h'

omit [PseudoEMetricSpace Phi] in
theorem automation_exact_serial_composition
    {protocol protocol' : ∀ i, Gamma i}
    {real middle ideal : Set Phi} (h : real —[protocol]→ middle)
    (h' : middle —[protocol']→ ideal) :
    real —[protocol' * protocol]→ ideal := by
  ac_compose h, h'

example {protocol protocol' simulator simulator' : ∀ i, Gamma i}
    {real middle ideal : Set Phi}
    (h : real —[protocol]→ simulator • middle)
    (h' : middle —[protocol']→ simulator' • ideal)
    (hcommute : Commute protocol' simulator) :
    real —[protocol' * protocol]→ (simulator * simulator') • ideal := by
  ac_compose_simulators h, h' using hcommute.actCommute

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi]
    {protocol protocol' : ∀ i, Gamma i}
    {real real' ideal ideal' : Set Phi}
    (h : real —[protocol]→ ideal) (h' : real' —[protocol']→ ideal') :
    real ∥ real' —[(protocol ∥ 1) * (1 ∥ protocol')]→ ideal ∥ ideal' := by
  ac_parallel h, h'

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Set Phi}
    (h : real —[protocol]→ ideal) :
    real ∥ context —[protocol ∥ 1]→ ideal ∥ context := by
  ac_context_left context using h

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Set Phi}
    (h : real —[protocol]→ ideal) :
    context ∥ real —[1 ∥ protocol]→ context ∥ ideal := by
  ac_context_right context using h

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal} (h : real —[protocol; error]→ ideal) :
    real ∥ context —[protocol ∥ 1; error]→ ideal ∥ context := by
  ac_context_left context using h

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Phi}
    (h : ⟪real⟫ —[protocol]→ ⟪ideal⟫) :
    ⟪real ∥ context⟫ —[protocol ∥ 1]→ ⟪ideal ∥ context⟫ := by
  ac_context_left context using h

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Phi}
    {error : ENNReal} (h : ⟪real⟫ —[protocol; error]→ ⟪ideal⟫) :
    ⟪real ∥ context⟫ —[protocol ∥ 1; error]→ ⟪ideal ∥ context⟫ := by
  ac_context_left context using h

example [Par Phi] [Par (∀ i, Gamma i)]
    [SMulParClass (∀ i, Gamma i) Phi] [IsNonexpandingPar Phi]
    {protocol : ∀ i, Gamma i} {real ideal context : Set Phi}
    {error : ENNReal} (h : real —[protocol; error]→ ideal) :
    context ∥ real —[1 ∥ protocol; error]→ context ∥ ideal := by
  ac_context_right context using h

example {protocol protocol' protocol'' : ∀ i, Gamma i}
    {first second third fourth : Set Phi}
    (h₁ : first —[protocol]→ second)
    (h₂ : second —[protocol']→ third)
    (h₃ : third —[protocol'']→ fourth) :
    first —[protocol'' * (protocol' * protocol)]→ fourth := by
  ac_chain [h₁, h₂, h₃]

example [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    {protocol protocol' protocol'' : ∀ i, Gamma i}
    {first second third fourth : Set Phi} {error error' error'' : ENNReal}
    (h₁ : first —[protocol; error]→ second)
    (h₂ : second —[protocol'; error']→ third)
    (h₃ : third —[protocol''; error'']→ fourth) :
    first —[protocol'' * (protocol' * protocol);
      (error + error') + error'']→ fourth := by
  ac_chain [h₁, h₂, h₃]

example [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    {P : Set I} {protocol protocol' : ∀ i, Gamma i}
    {first second third : Set Phi} {error error' : ENNReal}
    (h₁ : first —[protocol ⇂ P; error]→ second)
    (h₂ : second —[protocol' ⇂ P; error']→ third) :
    first —[(protocol' * protocol) ⇂ P; error + error']→ third := by
  ac_compose h₁, h₂

example [IsNonexpandingSMul (∀ i, Gamma i) Phi]
    {protocol protocol' : ∀ i, Gamma i} {real middle ideal : Set Phi}
    {error : ENNReal} (h : real —[protocol; error]→ middle)
    (h' : middle —[protocol']→ ideal) :
    real —[protocol' * protocol; error]→ ideal := by
  ac_relax using h, h' with Relaxation.epsilonRelaxation_compatible error

example (simulators : Submonoid (∀ i, Gamma i))
    (specification : Set Phi) (error : ENNReal) :
    (specification ^⋆[simulators]) ^ε[error] =
      Relaxation.epsilonRelaxation error (Relaxation.star simulators specification) :=
  rfl

example [Par Phi] (real ideal : Set Phi) (error : ENNReal) :
    real ∥ ideal ^ε[error] = real ∥ Relaxation.epsilonRelaxation error ideal :=
  rfl

example (P : Set I) (R : Phi) :
    patternAttach P (1 : ∀ i, Gamma i) • R = R := by
  ac_normalize

example (first second : ∀ i, Gamma i) (R : Phi) :
    (second * first) • R = second • (first • R) := by
  ac_normalize

example (protocol : ∀ i, Gamma i) (R : Phi) :
    protocol • ({R} : Set Phi) = ({protocol • R} : Set Phi) := by
  ac_normalize

example [Par (∀ i, Gamma i)] [Par Phi]
    [SMulParClass (∀ i, Gamma i) Phi]
    (left right : ∀ i, Gamma i) (R S : Phi) :
    (left ∥ right) • (R ∥ S) = (left • R) ∥ (right • S) := by
  ac_normalize

example (specification : Set Phi) (error : ENNReal) :
    specification ^ε[error] = Relaxation.epsilonRelaxation error specification := by
  ac_normalize

example (P : Set I) (R S : Phi)
    (h : patternAttach P (1 : ∀ i, Gamma i) • R = S) : R = S := by
  ac_normalize at h
  exact h

example (protocol simulator : ∀ i, Gamma i) (P : Set I) :
    Commute (protocol ⇂ P) (simulator ⇂ Pᶜ) := by
  ac_routine

example (protocol simulator : ∀ i, Gamma i) (P : Set I) :
    Commute (protocol ⇂ P) (simulator ⇂ Pᶜ) := by
  ac_commute

example (protocol simulator : ∀ i, Gamma i) (P Q : Set I)
    (hdisjoint : Disjoint P Q) :
    Commute (protocol ⇂ P) (simulator ⇂ Q) := by
  ac_commute using hdisjoint

example {P : Set I} {H : ∀ i, Submonoid (Gamma i)}
    (protocol gamma : ∀ i, Gamma i)
    (hsupported : gamma ∈ supportedOn Pᶜ H) :
    Commute (protocol ⇂ P) gamma := by
  ac_commute using hsupported

example (D : DistinguisherClass (∀ i, Gamma i) Phi)
    {tests : Set (Phi → ENNReal)} {real ideal : Phi} {error : ENNReal}
    {test : Phi → ENNReal} (hadmitted : tests ⊆ D.tests)
    (hideal : ideal ∈ propSpec tests) (hclose : D.edistD real ideal ≤ error)
    (hdefining : test ∈ tests) :
    1 - error ≤ test real := by
  ac_transfer_property D using hadmitted, hideal, hclose, hdefining

example (D : DistinguisherClass (∀ i, Gamma i) Phi)
    (hseparates : D.tests.SeparatesPoints) (R S : Phi) :
    D.edistD R S = 0 ↔ R = S :=
  D.edistD_eq_zero_iff_of_separatesPoints hseparates R S

example (firstClass secondClass : DistinguisherClass (∀ i, Gamma i) Phi)
    (R S : Phi) :
    ((letI := firstClass.toPseudoEMetricSpace
      edist R S) = firstClass.edistD R S) ∧
    ((letI := secondClass.toPseudoEMetricSpace
      edist R S) = secondClass.edistD R S) := by
  exact ⟨rfl, rfl⟩

example (error bound : ENNReal) (h : error ≤ bound) : error + 0 ≤ bound := by
  ac_routine

example (error : ENNReal) : 0 ≤ error := by
  ac_routine

example {Alpha : Type*} (f g : Alpha → Nat) (h : ∀ x, f x = g x) : f = g := by
  fail_if_success ac_routine
  funext x
  exact h x

/-- trace: [AbstractCryptography.ProofAutomation.rule] AbstractCryptography.smul_congr_protocol -/
#guard_msgs in
set_option trace.AbstractCryptography.ProofAutomation.rule true in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} (R : Phi)
    (same : protocol = protocol') :
    protocol • R = protocol' • R := by
  ac_transport using same

/-- error: ac_transport expected a protocol-action equality or exact/scalar construction equivalence matching the supplied protocol equality -/
#guard_msgs (substring := true) in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i} (same : protocol = protocol')
    (n : Nat) : n + 1 = n := by
  ac_transport using same

/-- info: Canonical AC rule candidates (goal unchanged):
  ac_construct — constructs_singleton_iff -/
#guard_msgs in
set_option linter.unusedTactic false in
example (protocol : ∀ i, Gamma i) (R S : Phi)
    (h : protocol • R = S) :
    ({R} : Set Phi) —[protocol]→ ({S} : Set Phi) := by
  ac?
  exact constructs_singleton_iff.mpr h

/-- error: ac_nonexpand expected a converter-action or ordered parallel edist non-expansion goal -/
#guard_msgs (substring := true) in
example : True := by
  ac_nonexpand

/-- error: ac_simulator expected a singleton construction into an epsilon-ball around an explicit star relaxation -/
#guard_msgs (substring := true) in
example : True := by
  ac_simulator (1 : ∀ i, Gamma i)

/-- error: ac_commute expected a canonical restricted-converter commutation goal -/
#guard_msgs (substring := true) in
example {Alpha : Type*} (f g : Alpha → Nat) : f = g := by
  ac_commute

/-- error: ac_filtered expected a filteredAt construction goal, a matching support proof, and an equality or distance bound -/
#guard_msgs (substring := true) in
example : True := by
  ac_filtered using True.intro, True.intro

/-- error: ac_construct could not use the supplied equality, inclusion, distance bound, or pointwise proof -/
#guard_msgs (substring := true) in
example (irrelevantFact : True) : True := by
  ac_construct using irrelevantFact

/-- error: ac_compose expected two composable exact or scalar-metric construction proofs -/
#guard_msgs (substring := true) in
example (firstFact secondFact : True) : True := by
  ac_compose firstFact, secondFact

/-- error: ac_transport could not replace the protocol in the supplied construction using the supplied equality -/
#guard_msgs (substring := true) in
omit [PseudoEMetricSpace Phi] in
example {protocol protocol' : ∀ i, Gamma i}
    (same : protocol = protocol') (irrelevantFact : True) : True := by
  ac_transport irrelevantFact using same

end AbstractCryptography.ProofAutomation.Tests

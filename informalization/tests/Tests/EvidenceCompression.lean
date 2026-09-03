import Informalization.Semantics.Plan

/-!
# Checked routine-evidence tests

These tests vary proof presentation while keeping the normalized proposition
and proof effect fixed.  No classifier input below is a tactic name or local
identifier.
-/

namespace Tests.EvidenceCompression

open Lean Meta Elab Command
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.EvidenceCompression
open Informalization.Semantics.Plan
open Informalization.Semantics.Registry

structure SingletonCarrier (α : Type) where
  value : α

instance {α : Type} : Singleton α (SingletonCarrier α) :=
  ⟨fun value => ⟨value⟩⟩

instance {α : Type} : Membership α (SingletonCarrier α) :=
  ⟨fun carrier member => member = carrier.value⟩

def normalizedIdentity {α : Type} (value : α) : α := value

theorem normalizationRw {α : Type} (value : α) :
    normalizedIdentity value = value := by
  rw [normalizedIdentity]

theorem normalizationSimpa {α : Type} (value : α) :
    normalizedIdentity value = value := by
  simpa [normalizedIdentity]

theorem normalizationCalc {α : Type} (value : α) :
    normalizedIdentity value = value := by
  calc
    normalizedIdentity value = value := rfl

theorem singletonInline {α : Type} (value : α) :
    value ∈ (Singleton.singleton value : SingletonCarrier α) := by
  exact rfl

theorem singletonNamed {α : Type} (value : α) :
    value ∈ (Singleton.singleton value : SingletonCarrier α) := by
  have equality : value = value := rfl
  exact equality

theorem singletonExplicit {α : Type} (value : α) :
    value ∈ (Singleton.singleton value : SingletonCarrier α) := rfl

theorem singletonAutomation {α : Type} (value : α) :
    value ∈ (Singleton.singleton value : SingletonCarrier α) := by
  simp [Membership.mem, Singleton.singleton]

theorem routinePremisesNormalizationFirst {α : Type} (value : α) :
    normalizedIdentity value = value ∧
      value ∈ (Singleton.singleton value : SingletonCarrier α) := by
  have normalization : normalizedIdentity value = value := by
    rw [normalizedIdentity]
  have membership :
      value ∈ (Singleton.singleton value : SingletonCarrier α) := rfl
  exact ⟨normalization, membership⟩

theorem routinePremisesMembershipFirst {α : Type} (value : α) :
    normalizedIdentity value = value ∧
      value ∈ (Singleton.singleton value : SingletonCarrier α) := by
  have membership :
      value ∈ (Singleton.singleton value : SingletonCarrier α) := rfl
  have normalization : normalizedIdentity value = value := by
    simpa [normalizedIdentity]
  exact ⟨normalization, membership⟩

def MaterialDomain {α : Type} (_value : α) : Prop := True

theorem materialDomainHelper {α : Type} (value : α)
    (evidence : MaterialDomain value) : MaterialDomain value := evidence

theorem materialDomainApplication {α : Type} (value : α)
    (evidence : MaterialDomain value) : MaterialDomain value :=
  materialDomainHelper value evidence

theorem materialExistential : ∃ value : Nat, value = value :=
  ⟨0, rfl⟩

def PrimaryCondition {α : Type} (_value : α) : Prop := True

theorem primaryConditionEvidence {α : Type} (value : α)
    (condition : PrimaryCondition value) : PrimaryCondition value := condition

theorem carrierEvidence (α : Type) [assumption : Nonempty α] : Nonempty α :=
  assumption

private def requirePlan (environment : Environment) (name : Name)
    (profile : DecoderProfile := {}) : MetaM ProofPlan := do
  let some plan ← Plan.fromDeclarationWithProfile? environment #[] profile name
    | throwError "missing proof plan for {name}"
  return plan

private def requireComplete (plan : ProofPlan) : MetaM Unit := do
  unless plan.compression.coverageComplete &&
      plan.compression.coverage.size == plan.allEvidence.size do
    throwError "routine evidence lost complete checked coverage"

run_cmd liftTermElabM do
  let environment ← getEnv

  let rwPlan ← requirePlan environment ``normalizationRw
  let simpaPlan ← requirePlan environment ``normalizationSimpa
  let calcPlan ← requirePlan environment ``normalizationCalc
  requireComplete rwPlan
  requireComplete simpaPlan
  requireComplete calcPlan
  unless rwPlan.compressionFingerprint == simpaPlan.compressionFingerprint &&
      simpaPlan.compressionFingerprint == calcPlan.compressionFingerprint do
    throwError "rw/simpa/calc changed normalized routine-evidence semantics: rw={repr rwPlan.compressionFingerprint}/{repr (rwPlan.fallbackRegions.map fun region => (headDeclaration? region.payload.proof, region.payload.expected.getAppArgs.map headDeclaration?))}, simpa={repr simpaPlan.compressionFingerprint}/{repr (simpaPlan.fallbackRegions.map fun region => (headDeclaration? region.payload.proof, region.payload.expected.getAppArgs.map headDeclaration?))}, calc={repr calcPlan.compressionFingerprint}"
  unless !rwPlan.hasFallback &&
      rwPlan.compression.absorbedEffects.contains
        .definitionalOrCoercionNormalization do
    throwError "definitional normalization did not receive absorbable evidence coverage"

  let inlinePlan ← requirePlan environment ``singletonInline
  let namedPlan ← requirePlan environment ``singletonNamed
  let explicitPlan ← requirePlan environment ``singletonExplicit
  let automationPlan ← requirePlan environment ``singletonAutomation
  requireComplete inlinePlan
  requireComplete namedPlan
  unless inlinePlan.compressionFingerprint == namedPlan.compressionFingerprint do
    throwError "an inline/named local proof changed singleton evidence semantics: inline={repr inlinePlan.compressionFingerprint}/{repr (inlinePlan.fallbackRegions.map fun region => headDeclaration? region.payload.proof)}, named={repr namedPlan.compressionFingerprint}/{repr (namedPlan.fallbackRegions.map fun region => headDeclaration? region.payload.proof)}"
  unless explicitPlan.compressionFingerprint == automationPlan.compressionFingerprint do
    throwError "elementary automation changed singleton evidence semantics"
  unless !inlinePlan.hasFallback &&
      inlinePlan.compression.absorbedEffects.contains .singletonMembership do
    throwError "singleton membership did not receive absorbable evidence coverage"

  let normalizationFirst ←
    requirePlan environment ``routinePremisesNormalizationFirst
  let membershipFirst ←
    requirePlan environment ``routinePremisesMembershipFirst
  requireComplete normalizationFirst
  requireComplete membershipFirst
  unless normalizationFirst.compressionFingerprint ==
      membershipFirst.compressionFingerprint do
    throwError "reordering independent routine premises changed compressed semantics"

  let materialPlan ← requirePlan environment ``materialDomainApplication
  requireComplete materialPlan
  unless materialPlan.hasFallback do
    throwError "a material domain lemma was absorbed as routine evidence"
  unless materialPlan.compression.coverage.any fun entry =>
      headDeclaration? entry.payload.proof == some ``materialDomainHelper &&
        entry.disposition == .uncovered do
    throwError "the material helper application did not remain fail-closed"
  let existentialPlan ← requirePlan environment ``materialExistential
  requireComplete existentialPlan
  unless existentialPlan.hasFallback do
    throwError "an unregistered existential witness was absorbed as logical bookkeeping"

  let primaryProfile : DecoderProfile := {
    primaryHypotheses := #[``PrimaryCondition]
  }
  let primaryPlan ← requirePlan environment ``primaryConditionEvidence primaryProfile
  requireComplete primaryPlan
  unless !primaryPlan.hasFallback && primaryPlan.compression.primaryHypotheses.size == 1 do
    throwError "a primary mathematical hypothesis was not kept visible"

  let carrierPlan ← requirePlan environment ``carrierEvidence
  requireComplete carrierPlan
  unless !carrierPlan.hasFallback && carrierPlan.compression.carrierAssumptions.size == 1 &&
      carrierPlan.compression.carrierAssumptions[0]!.kind == .inhabited do
    throwError "Nonempty was not aggregated as a carrier assumption"

end Tests.EvidenceCompression

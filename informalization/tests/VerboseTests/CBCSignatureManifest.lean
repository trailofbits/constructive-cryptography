/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCMAC.Construction
import LanguageDesign.SignatureManifest

/-!
# CBC signature manifest

This opt-in fixture records the last accepted public CBC theorem propositions.
It follows the live sister dependency and therefore remains separate from the
fixed-interface language suite. Binder names in each example are semantic
roles. Private helpers remain deliberately absent.
-/

set_option autoImplicit false

namespace VerboseTests.CBCSignatureManifest

open CryptoLanguage.LanguageDesign.SignatureManifest

private def binder (position : Nat) (binderInfo : Lean.BinderInfo)
    (typeHead? : Option Lean.Name) (typeHash : UInt64) : BinderSnapshot :=
  { position, binderInfo, typeHead?, typeHash }

private def cbcEndpointBinders : Array BinderSnapshot := #[
  binder 0 .implicit none 1035981358683314461,
  binder 1 .instImplicit (some ``Fintype) 9749367788198690420,
  binder 2 .instImplicit (some ``DecidableEq) 18102223327810114227,
  binder 3 .instImplicit (some ``Nonempty) 4707014254357435129,
  binder 4 .instImplicit (some ``AddCommGroup) 8164892365702467115,
  binder 5 .implicit none 1035981358683314461,
  binder 6 .instImplicit (some ``Fintype) 9749367788198690420,
  binder 7 .instImplicit (some ``DecidableEq) 18102223327810114227,
  binder 8 .instImplicit (some ``Nontrivial) 14232612230014634845,
  binder 9 .default none 5362532319749290618,
  binder 10 .default (some ``Nat) 5553995614846443309,
  binder 11 .default
    (some ``Applications.CBCCombinatorics.PrefixFree) 9091726527030178471]

private def cbcEndpointRoles : Array Lean.Name := #[
  `blockAlphabet, `blockAlphabetFintype, `blockAlphabetDecidableEquality,
  `blockAlphabetNonempty, `blockAlphabetAdditiveGroup, `messageAlphabet,
  `messageAlphabetFintype, `messageAlphabetDecidableEquality,
  `messageAlphabetNontrivial, `blockEncoding, `totalBlockBudget,
  `prefixFreeEvidence]

private def manifest : Array Entry := #[
  {
    snapshot := {
      declaration := ``Applications.CBCMAC.applySystem_theta
      owner := `Applications.CBCMAC.Objects
      visibility := .publicDecl
      universeArity := 1
      binders := #[
        binder 0 .implicit none 1035981358683314461,
        binder 1 .implicit none 1035981358683314461,
        binder 2 .default none 10990624687958319924,
        binder 3 .default (some ``Nat) 5553995614846443309,
        binder 4 .default (some ``RandomSystems.Ambient.DDS)
          2829645528073110506]
      resultHead? := some ``Eq
      resultHash := 1697249760905943346
      signatureHash := 16338351434273076049
    }
    binderRoles := #[`blockAlphabet, `messageAlphabet, `blockEncoding,
      `totalBlockBudget, `system]
  },
  {
    snapshot := {
      declaration :=
        ``Applications.CBCCombinatorics.not_cbcBad_implies_uniform_outputs
      owner := `Applications.CBCCombinatorics
      visibility := .publicDecl
      universeArity := 1
      binders := #[
        binder 0 .implicit none 1035981358683314461,
        binder 1 .implicit none 1035981358683314461,
        binder 2 .instImplicit (some ``AddCommGroup) 42948594764183958,
        binder 3 .instImplicit (some ``Fintype) 2128448743337585390,
        binder 4 .instImplicit (some ``DecidableEq) 11291301696770637791,
        binder 5 .instImplicit (some ``Fintype) 16377571019086576099,
        binder 6 .instImplicit (some ``DecidableEq) 5106969436218795308,
        binder 7 .instImplicit (some ``Nonempty) 3997176915230208244,
        binder 8 .instImplicit (some ``Nontrivial) 6773185141027995503,
        binder 9 .default none 12016313793127251800,
        binder 10 .default
          (some ``Applications.CBCCombinatorics.PrefixFree)
          4535554986213029815,
        binder 11 .default (some ``List) 11276793577237013454,
        binder 12 .default none 470229146391022664]
      resultHead? := some ``Eq
      resultHash := 12681027496361595441
      signatureHash := 8844281982306175875
    }
    binderRoles := #[`blockAlphabet, `messageAlphabet,
      `blockAlphabetAdditiveGroup, `blockAlphabetFintype,
      `blockAlphabetDecidableEquality, `messageAlphabetFintype,
      `messageAlphabetDecidableEquality, `blockAlphabetNonempty,
      `messageAlphabetNontrivial, `blockEncoding, `prefixFreeEvidence,
      `messageList, `answerAssignment]
  },
  {
    snapshot := {
      declaration := ``Applications.CBCCombinatorics.mass_cbcBad_le
      owner := `Applications.CBCCombinatorics
      visibility := .publicDecl
      universeArity := 1
      binders := #[
        binder 0 .implicit none 1035981358683314461,
        binder 1 .implicit none 1035981358683314461,
        binder 2 .instImplicit (some ``AddCommGroup) 42948594764183958,
        binder 3 .instImplicit (some ``Fintype) 7572338366402457727,
        binder 4 .instImplicit (some ``DecidableEq) 11110607340011183607,
        binder 5 .instImplicit (some ``Nonempty) 11463339707730431204,
        binder 6 .default none 10734686122760383799,
        binder 7 .default (some ``Nat) 5553995614846443309,
        binder 8 .default (some ``List) 15543529855687734968,
        binder 9 .default (some ``LE.le) 10223138316917963516]
      resultHead? := some ``LE.le
      resultHash := 3554543776260175074
      signatureHash := 16204941290570932699
    }
    binderRoles := #[`blockAlphabet, `messageAlphabet,
      `blockAlphabetAdditiveGroup, `blockAlphabetFintype,
      `blockAlphabetDecidableEquality, `blockAlphabetNonempty,
      `blockEncoding, `totalBlockBudget, `messageList, `admissionEvidence]
  },
  {
    snapshot := {
      declaration := ``Applications.CBCMAC.cbcPDS_advantage_le
      owner := `Applications.CBCMAC.Probability
      visibility := .publicDecl
      universeArity := 1
      binders := cbcEndpointBinders
      resultHead? := some ``LE.le
      resultHash := 15972186345015294031
      signatureHash := 2240411086932486257
    }
    binderRoles := cbcEndpointRoles
  },
  {
    snapshot := {
      declaration := ``Applications.CBCMAC.realPDS_advantage_le
      owner := `Applications.CBCMAC.Probability
      visibility := .publicDecl
      universeArity := 1
      binders := cbcEndpointBinders
      resultHead? := some ``LE.le
      resultHash := 861808437009341590
      signatureHash := 3607878665060188087
    }
    binderRoles := cbcEndpointRoles
  },
  {
    snapshot := {
      declaration := ``Applications.CBCMAC.cbc_distance_le
      owner := `Applications.CBCMAC.Construction
      visibility := .publicDecl
      universeArity := 1
      binders := cbcEndpointBinders
      resultHead? := some ``LE.le
      resultHash := 5836247599435558702
      signatureHash := 8419972426341295604
    }
    binderRoles := cbcEndpointRoles
  },
  {
    snapshot := {
      declaration := ``Applications.CBCMAC.cbc_constructs_within
      owner := `Applications.CBCMAC.Construction
      visibility := .publicDecl
      universeArity := 1
      binders := cbcEndpointBinders
      resultHead? :=
        some ``AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      resultHash := 3702176435203289246
      signatureHash := 15503354628702104006
    }
    binderRoles := cbcEndpointRoles
  }]

run_cmd Lean.Elab.Command.liftTermElabM do
  for entry in manifest do
    check entry

noncomputable section

open Probability
open RandomSystems
open RandomSystems.Ambient

attribute [local instance]
  RandomSystems.Ambient.Interface.category
  RandomSystems.Ambient.Interface.monoidalCategory

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- Roles: block encoding, total-block budget, and the attached system. -/
example (blockForm : M → List X) (limit : Nat)
    (system : DDS (Interface.single M X)) :
    applySystem (Applications.CBCMAC.theta blockForm limit) system =
      fun history =>
        if Applications.CBCCombinatorics.totalBlocks
            blockForm history.queries ≤ limit then
          system history
        else
          none :=
  Applications.CBCMAC.applySystem_theta blockForm limit system

/-- Roles: block encoding, prefix-free evidence, message schedule, answers. -/
example [Nontrivial M]
    (blockForm : M → List X)
    (prefixFree : Applications.CBCCombinatorics.PrefixFree blockForm)
    (messages : List M) (answers : ↑messages.toFinset → X) :
    (Distribution.uniform (X → X)).mass (fun f =>
        (∀ message : ↑messages.toFinset,
          Applications.CBCCombinatorics.cbcState f (blockForm message.1) =
            answers message) ∧
          ¬ Applications.CBCCombinatorics.cbcBad f blockForm messages) =
      (Distribution.uniform (M → X)).mass (fun g =>
        ∀ message : ↑messages.toFinset, g message.1 = answers message) *
      (Distribution.uniform (X → X)).mass
        (fun f => ¬ Applications.CBCCombinatorics.cbcBad f blockForm messages) :=
  Applications.CBCCombinatorics.not_cbcBad_implies_uniform_outputs
    blockForm prefixFree messages answers

/-- Roles: block encoding, total-block budget, fixed schedule, admission proof. -/
example (blockForm : M → List X) (limit : Nat)
    (messages : List M)
    (admitted : Applications.CBCCombinatorics.totalBlocks blockForm messages ≤ limit) :
    (Distribution.uniform (X → X)).mass
        (fun f => Applications.CBCCombinatorics.cbcBad f blockForm messages) ≤
      (limit : Real) * ((limit : Real) - 1) /
        (2 * Fintype.card X) :=
  Applications.CBCCombinatorics.mass_cbcBad_le
    blockForm limit messages admitted

/-- Roles: block encoding, total-block budget, prefix-free evidence. -/
example [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : Applications.CBCCombinatorics.PrefixFree blockForm) :
    Ambient.PDS.advantage
        (PDS.apply (Applications.CBCMAC.theta blockForm limit)
          (Applications.CBCMAC.cbcPDS blockForm))
        (PDS.apply (Applications.CBCMAC.theta blockForm limit)
          (Applications.CBCMAC.idealFunction (M := M) (X := X))) ≤
      Applications.CBCCombinatorics.cbcEpsilon X limit :=
  Applications.CBCMAC.cbcPDS_advantage_le blockForm limit prefixFree

/-- Roles: block encoding, total-block budget, prefix-free evidence. -/
example [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : Applications.CBCCombinatorics.PrefixFree blockForm) :
    Ambient.PDS.advantage
        (Applications.CBCMAC.realPDS blockForm limit)
        (Applications.CBCMAC.idealPDS blockForm limit) ≤
      Applications.CBCCombinatorics.cbcEpsilon X limit :=
  Applications.CBCMAC.realPDS_advantage_le blockForm limit prefixFree

/-- Roles: block encoding, total-block budget, prefix-free evidence. -/
example [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : Applications.CBCCombinatorics.PrefixFree blockForm) :
    edist
        (RandomSystem.ofPDS
          (Applications.CBCMAC.realPDS blockForm limit))
        (RandomSystem.ofPDS
          (Applications.CBCMAC.idealPDS blockForm limit)) ≤
      Applications.CBCCombinatorics.cbcEpsilon X limit :=
  Applications.CBCMAC.cbc_distance_le blockForm limit prefixFree

/-- Roles: source, serial converter, target, error are fixed by the endpoint. -/
example [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : Applications.CBCCombinatorics.PrefixFree blockForm) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      (Phi := Interface.randomSystems)
      (DDC.serial (Applications.CBCMAC.theta blockForm limit)
        (Applications.CBCMAC.cbc blockForm))
      ({RandomSystem.ofPDS
          (Applications.CBCMAC.restrictedRandomFunction limit)} :
        AbstractCryptography.Categorical.ResourceAlgebra.Specification
          Interface.randomSystems (Interface.single X X))
      ({RandomSystem.ofPDS
          (Applications.CBCMAC.idealPDS blockForm limit)} :
        AbstractCryptography.Categorical.ResourceAlgebra.Specification
          Interface.randomSystems (Interface.single M X))
      (Applications.CBCCombinatorics.cbcEpsilon X limit) :=
  Applications.CBCMAC.cbc_constructs_within blockForm limit prefixFree

end

end VerboseTests.CBCSignatureManifest

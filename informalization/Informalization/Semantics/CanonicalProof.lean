/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Canonical
import Informalization.Semantics.ProofEvidence

/-!
# Recursive canonical proofs

This module joins the canonical claim language to the complete checked
`ProofEvidence.Tree`.  Logical premises and checked macro expansions remain
different edges, fallback wrappers are retained, and every registered rule is
assigned the same stable preorder identifier later used by `ProofPlan.steps`.
-/

namespace Informalization.Semantics.CanonicalProof

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.ProofEvidence

/-- Stable path through the complete checked evidence tree.  Premise segments
use declaration-telescope identity; fallback segments preserve transparent
kernel wrappers without promoting their descendants into fabricated siblings. -/
inductive ProofPathSegment where
  | premise (key : ObligationKey)
  | macroExpansion
  | fallbackChild (index : Nat)
  deriving Inhabited, BEq, Repr

abbrev ProofPath := Array ProofPathSegment

mutual
  /-- A complete recursive proof.  Rule nodes are semantically registered;
  fallback nodes retain every unclassified checked region and its children. -/
  inductive CanonicalProof where
    | rule (node : RuleNode)
    | fallback (node : FallbackNode)

  /-- One registered semantic rule together with the proof of each declaration
  premise and, separately, the checked expansion of a semantic macro. -/
  structure RuleNode where
    stepId : Nat
    path : ProofPath
    goal : CanonicalProposition
    payload : Payload
    application : ProofApplication
    semanticGraph : Graph
    derivation? : Option DerivationApplication := none
    premises : Array PremiseProof := #[]
    macroExpansion? : Option CanonicalProof := none

  /-- A logical premise edge.  `key` is stable even when several premises have
  the same semantic slot.  Instance evidence has no canonical obligation but
  remains present through its descriptor and recursive proof. -/
  structure PremiseProof where
    key : ObligationKey
    descriptor : PremiseDescriptor
    source : Premise
    obligation? : Option ProofObligation := none
    proof : CanonicalProof

  /-- An unclassified checked proof region. -/
  structure FallbackNode where
    path : ProofPath
    goal : CanonicalProposition
    payload : Payload
    children : Array CanonicalProof := #[]
end

instance : Inhabited CanonicalProof := ⟨.fallback {
  path := #[]
  goal := .opaque default
  payload := default
  children := #[]
}⟩

instance : Inhabited RuleNode := ⟨{
  stepId := 0
  path := #[]
  goal := .opaque default
  payload := default
  application := default
  semanticGraph := default
}⟩

instance : Inhabited PremiseProof := ⟨{
  key := default
  descriptor := default
  source := default
  proof := default
}⟩

instance : Inhabited FallbackNode := ⟨{
  path := #[]
  goal := .opaque default
  payload := default
}⟩

def CanonicalProof.path : CanonicalProof → ProofPath
  | .rule node => node.path
  | .fallback node => node.path

def CanonicalProof.goal : CanonicalProof → CanonicalProposition
  | .rule node => node.goal
  | .fallback node => node.goal

/-- Number of registered semantic parent edges represented by a path.
Transparent fallback wrappers do not increase semantic depth. -/
def ProofPath.semanticDepth (path : ProofPath) : Nat :=
  path.countP fun segment =>
    match segment with
    | .premise _ | .macroExpansion => true
    | .fallbackChild _ => false

/-- Primary checked evidence at this exact proof node. -/
def CanonicalProof.primaryEvidence : CanonicalProof → Payload
  | .rule node => node.payload
  | .fallback node => node.payload

/-- Direct children without erasing the distinction available on a rule node.
For generic traversal, logical premises precede the macro expansion. -/
def CanonicalProof.children : CanonicalProof → Array CanonicalProof
  | .rule node =>
      node.macroExpansion?.elim (node.premises.map (·.proof)) fun expansion =>
        (node.premises.map (·.proof)).push expansion
  | .fallback node => node.children

/-- Complete checked evidence beneath a canonical node, in evidence preorder. -/
partial def CanonicalProof.allEvidence (proof : CanonicalProof) : Array Payload :=
  proof.children.foldl
    (fun result child => result ++ child.allEvidence)
    #[proof.primaryEvidence]

/-- All registered rule nodes in stable semantic preorder. -/
partial def CanonicalProof.ruleNodes : CanonicalProof → Array RuleNode
  | .rule node =>
      let premiseNodes := node.premises.foldl
        (fun result premise => result ++ premise.proof.ruleNodes) #[node]
      node.macroExpansion?.elim premiseNodes fun expansion =>
        premiseNodes ++ expansion.ruleNodes
  | .fallback node =>
      node.children.foldl (fun result child => result ++ child.ruleNodes) #[]

/-- Registered roots after looking through fallback wrappers.  The wrappers
remain in the complete tree; this is only the primary semantic presentation
frontier. -/
partial def CanonicalProof.ruleForest : CanonicalProof → Array RuleNode
  | .rule node => #[node]
  | .fallback node =>
      node.children.foldl (fun result child => result ++ child.ruleForest) #[]

private structure BuildState where
  nextStepId : Nat := 0

private abbrev BuildM := StateT BuildState MetaM

private def decodeGoal (profile : DecoderProfile) (payload : Payload) : MetaM
    CanonicalProposition :=
  withLCtx payload.localContext #[] do
    decodeProposition profile payload.expected

private def decodeRule? (profile : DecoderProfile) (payload : Payload)
    (application : ProofApplication) : MetaM (Option DerivationApplication) :=
  withLCtx payload.localContext #[] do
    decodeDerivation? profile application.source

private partial def build (profile : DecoderProfile) (path : ProofPath)
    (tree : Tree) : BuildM CanonicalProof := do
  match tree with
  | .rule payload application semanticGraph premises macroExpansion? =>
      let state ← get
      let stepId := state.nextStepId
      set ({ nextStepId := stepId + 1 } : BuildState)
      let goal ← liftM <| decodeGoal profile payload
      let derivation? ← liftM <| decodeRule? profile payload application
      if let some derivation := derivation? then
        let sameGoal ← liftM <| withLCtx payload.localContext #[] do
          isDefEq derivation.conclusion.source goal.source
        unless sameGoal do
          throwError "canonical rule conclusion does not match its evidence goal"
      let mut canonicalPremises : Array PremiseProof := #[]
      for premiseIndex in [0:premises.size] do
        let premise := premises[premiseIndex]!
        let key : ObligationKey := {
          telescopePosition := premise.descriptor.position
          proofOrdinal := premiseIndex
        }
        let obligation? := derivation?.bind fun derivation =>
          derivation.obligations.find? (·.key == key)
        let proof ← build profile (path.push (.premise key)) premise.evidence
        if let some obligation := obligation? then
          let samePremise ← liftM <| withLCtx
              proof.primaryEvidence.localContext #[] do
            isDefEq obligation.proposition proof.goal.source
          unless samePremise do
            throwError "canonical premise goal does not match its parent obligation"
        canonicalPremises := canonicalPremises.push {
          key
          descriptor := premise.descriptor
          source := premise
          obligation?
          proof
        }
      if let some derivation := derivation? then
        for obligation in derivation.obligations do
          unless canonicalPremises.any (·.key == obligation.key) do
            throwError "canonical obligation has no matching proof-evidence premise"
      let canonicalExpansion? ← match macroExpansion? with
        | some expansion => some <$> build profile (path.push .macroExpansion) expansion
        | none => pure none
      return .rule {
        stepId
        path
        goal
        payload
        application
        semanticGraph
        derivation?
        premises := canonicalPremises
        macroExpansion? := canonicalExpansion?
      }
  | .fallback payload children =>
      let goal ← liftM <| decodeGoal profile payload
      let mut canonicalChildren := #[]
      for childIndex in [0:children.size] do
        canonicalChildren := canonicalChildren.push
          (← build profile (path.push (.fallbackChild childIndex)) children[childIndex]!)
      return .fallback { path, goal, payload, children := canonicalChildren }

/-- Decode a complete checked evidence tree into its recursive canonical form. -/
def ofEvidence (profile : DecoderProfile) (tree : Tree) : MetaM CanonicalProof := do
  let (proof, _) ← (build profile #[] tree).run {}
  return proof

end Informalization.Semantics.CanonicalProof

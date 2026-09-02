/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Checked declaration-signature manifests

This module records the part of an external declaration contract that source
examples alone cannot freeze: the complete elaborated telescope, declaration
owner, visibility, and an alpha-stable fingerprint of the result proposition.

Fingerprints erase metadata and binder spelling, but preserve binder order,
binder information, constants, applications, projections, literals, and the
relative identity of universe parameters.  They deliberately do not unfold
definitions: the manifest guards a public signature, not its implementation.
-/

namespace CryptoLanguage.LanguageDesign.SignatureManifest

open Lean Meta

inductive Visibility where
  | publicDecl
  | privateDecl
  deriving Inhabited, BEq, Repr

/-- One binder in declaration-telescope order. -/
structure BinderSnapshot where
  position : Nat
  binderInfo : BinderInfo
  typeHead? : Option Name
  typeHash : UInt64
  deriving Inhabited, BEq, Repr

/-- The checked public signature of one declaration. -/
structure Snapshot where
  declaration : Name
  owner : Name
  visibility : Visibility
  universeArity : Nat
  binders : Array BinderSnapshot
  resultHead? : Option Name
  resultHash : UInt64
  signatureHash : UInt64
  deriving Inhabited, BEq, Repr

/-- A manifest assigns a stable semantic role to every telescope position.
The role names are identifiers for the language design, never generated
display prose. -/
structure Entry where
  snapshot : Snapshot
  binderRoles : Array Name
  deriving Inhabited, BEq, Repr

private def headDeclaration? (expression : Expr) : Option Name :=
  match expression.consumeMData.getAppFn.consumeMData with
  | .const declaration _ => some declaration
  | _ => none

private def canonicalLevels (parameters : List Name) : List Level :=
  parameters.mapIdx fun index _ => .param <| Name.mkSimple s!"u{index}"

/-- A metadata-free, alpha-stable structural code.  Declaration types are
closed, so free and metavariables are retained only as defensive sentinels. -/
private partial def expressionCode (raw : Expr) : String :=
  match raw.consumeMData with
  | .bvar index => s!"b:{index}"
  | .fvar _ => "f"
  | .mvar _ => "m"
  | .sort level => s!"s:{repr level}"
  | .const declaration levels => s!"c:{declaration}:{repr levels}"
  | .app function argument =>
      s!"a({expressionCode function})({expressionCode argument})"
  | .lam _ domain body info =>
      s!"l:{repr info}({expressionCode domain})({expressionCode body})"
  | .forallE _ domain body info =>
      s!"p:{repr info}({expressionCode domain})({expressionCode body})"
  | .letE _ type value body nondep =>
      s!"e:{nondep}({expressionCode type})({expressionCode value})" ++
        s!"({expressionCode body})"
  | .lit literal => s!"i:{repr literal}"
  | .mdata _ expression => expressionCode expression
  | .proj typeName index expression =>
      s!"j:{typeName}:{index}({expressionCode expression})"

structure LocalEntity where
  id : FVarId
  type : Expr
  value? : Option Expr

private def fvarPosition? (locals : Array LocalEntity) (target : FVarId) : Option Nat :=
  locals.findIdx? (·.id == target)

/-- A metadata- and local-name-free code for expressions recorded inside a
declaration proof. Local definitions are represented by their recursively
canonicalized type and value, so renaming or reordering independent local
definitions does not change an entity while changing its value does. Other
free variables retain telescope position. -/
private partial def localExpressionCode (locals : Array LocalEntity)
    (visiting : Array FVarId) (raw : Expr) : String :=
  match raw.consumeMData with
  | .bvar index => s!"b:{index}"
  | .fvar id =>
      let position := fvarPosition? locals id |>.getD locals.size
      match locals[position]? with
      | some entity =>
          match entity.value? with
          | some value =>
              if visiting.contains id then s!"cycle:{position}"
              else
                let visiting := visiting.push id
                s!"d({localExpressionCode locals visiting entity.type})" ++
                  s!"({localExpressionCode locals visiting value})"
          | none => s!"f:{position}"
      | none => s!"f:{position}"
  | .mvar _ => "m"
  | .sort level => s!"s:{repr level}"
  | .const declaration levels => s!"c:{declaration}:{repr levels}"
  | .app function argument =>
      s!"a({localExpressionCode locals visiting function})({localExpressionCode locals visiting argument})"
  | .lam _ domain body info =>
      s!"l:{repr info}({localExpressionCode locals visiting domain})({localExpressionCode locals visiting body})"
  | .forallE _ domain body info =>
      s!"p:{repr info}({localExpressionCode locals visiting domain})({localExpressionCode locals visiting body})"
  | .letE _ type value body nondep =>
      s!"e:{nondep}({localExpressionCode locals visiting type})({localExpressionCode locals visiting value})" ++
        s!"({localExpressionCode locals visiting body})"
  | .lit literal => s!"i:{repr literal}"
  | .mdata _ expression => localExpressionCode locals visiting expression
  | .proj typeName index expression =>
      s!"j:{typeName}:{index}({localExpressionCode locals visiting expression})"

/-- Alpha-stable structural fingerprint for one expression in a recorded
local telescope. This follows local definition edges but does not unfold
global declarations. -/
def localExpressionFingerprint (locals : Array LocalEntity) (expression : Expr) : UInt64 :=
  (localExpressionCode locals #[] expression).hash

private partial def telescope (type : Expr) (position : Nat := 0) :
    Array BinderSnapshot × Expr :=
  match type.consumeMData with
  | .forallE _ domain body binderInfo =>
      let binder : BinderSnapshot := {
        position
        binderInfo
        typeHead? := headDeclaration? domain
        typeHash := (expressionCode domain).hash
      }
      let (tail, result) := telescope body (position + 1)
      (#[binder] ++ tail, result)
  | result => (#[], result)

private def declarationOwner (environment : Environment) (declaration : Name) : Name :=
  match environment.getModuleIdxFor? declaration with
  | some index => environment.header.moduleNames[index.toNat]!
  | none => environment.mainModule

/-- Compute the checked signature receipt for one live declaration. -/
def snapshot (declaration : Name) : MetaM Snapshot := do
  let environment ← getEnv
  let information ← getConstInfo declaration
  let type := information.instantiateTypeLevelParams
    (canonicalLevels information.levelParams)
  let (binders, result) := telescope type
  return {
    declaration
    owner := declarationOwner environment declaration
    visibility := if isPrivateName declaration then .privateDecl else .publicDecl
    universeArity := information.levelParams.length
    binders
    resultHead? := headDeclaration? result
    resultHash := (expressionCode result).hash
    signatureHash := (expressionCode type).hash
  }

/-- Fail closed if the live declaration differs from its frozen receipt or if
its role assignment no longer covers the telescope exactly. -/
def check (expected : Entry) : MetaM Unit := do
  let actual ← snapshot expected.snapshot.declaration
  unless actual == expected.snapshot do
    throwError "declaration signature drift for {expected.snapshot.declaration}\nexpected:\n{repr expected.snapshot}\nactual:\n{repr actual}"
  unless expected.binderRoles.size == actual.binders.size do
    throwError "role assignment for {actual.declaration} covers {expected.binderRoles.size} of {actual.binders.size} binders"
  if let some duplicate := expected.binderRoles.find? fun role =>
      role.isAnonymous || (expected.binderRoles.filter (· == role)).size != 1 then
    throwError "invalid or duplicate binder role {duplicate} in manifest for {actual.declaration}"

end CryptoLanguage.LanguageDesign.SignatureManifest

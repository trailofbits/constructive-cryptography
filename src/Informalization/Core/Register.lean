/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Shared Cryptographic Register & Paper-Centric Section Scope Contract

Lightweight, zero-dependency core types shared across `Core/*`, `CC/*`, `Verbose/*`,
and `Paper/*` without circular imports:

* `CryptoRegister`: the three empirically grounded cryptographic literature registers
  (`gameBased`, `constructive`, `randomSystems`).
* `PaperSectionSpec`: persistent section-level metadata attached to a namespace or
  declaration (`register`, `settingProse`, `suppressedBinders`, `motivation`,
  `suppressedPropHeads`), enabling Q1–Q5 quantifier economy and zero double declarations.
* `byLeafMDataKey`: zero-cost `Expr.mdata` tag marking strict `⊕` opacity walls
  produced by `by_leaf { ... }` and archetype combinators.
-/

namespace Informalization.Core.Register

open Lean

/-- The three empirically mined cryptographic discourse registers. -/
inductive CryptoRegister
  | gameBased      -- Register A: Boneh–Shoup / Bellare–Rogaway
  | constructive   -- Register B: Maurer–Renner / Banfi / Jost / Tackmann
  | randomSystems  -- Register C: Maurer 2002 / Maurer–Pietrzak / Jha / BDPV08
  deriving DecidableEq, BEq, Repr, Inhabited

def CryptoRegister.toString : CryptoRegister → String
  | .gameBased     => "gameBased"
  | .constructive  => "constructive"
  | .randomSystems => "randomSystems"

def CryptoRegister.ofString? : String → Option CryptoRegister
  | "gameBased" | "game_based" | "A" | "registerA" => some .gameBased
  | "constructive" | "cc" | "B" | "registerB" => some .constructive
  | "randomSystems" | "random_systems" | "hCoeff" | "C" | "registerC" => some .randomSystems
  | _ => none

/-- Section-level paper-centric contract stored per namespace prefix or anchor declaration. -/
structure PaperSectionSpec where
  /-- Namespace prefix or specific declaration name this section contract governs. -/
  scope : Name
  register : CryptoRegister := .constructive
  /-- Optional section title & motivation prose (author-marked non-claiming gloss). -/
  title? : Option String := none
  motivation? : Option String := none
  /-- 1–3 calm prose sentences introducing the section's standing parameters ONCE. -/
  settingProse? : Option String := none
  /-- Binder names introduced in `settingProse?` and therefore omitted from theorem `Let ...` headers. -/
  suppressedBinders : Array String := #[]
  /-- Predicate constant names (e.g., `Supported`, `Admitted`, `ClosedUnder`) already assumed in setting. -/
  suppressedPredicates : Array Name := #[]
  deriving Repr, Inhabited

private def mergeSectionSpec (old new : PaperSectionSpec) : PaperSectionSpec := {
  scope                := new.scope
  register             := new.register
  title?               := new.title? <|> old.title?
  motivation?          := new.motivation? <|> old.motivation?
  settingProse?        := new.settingProse? <|> old.settingProse?
  suppressedBinders    := old.suppressedBinders ++ new.suppressedBinders
  suppressedPredicates := old.suppressedPredicates ++ new.suppressedPredicates
}

/-- Persistent environment extension storing `PaperSectionSpec` records keyed by namespace/decl. -/
initialize paperSectionExt :
    SimplePersistentEnvExtension (Name × PaperSectionSpec) (NameMap PaperSectionSpec) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, spec) =>
      match m.get? n with
      | some prev => m.insert n (mergeSectionSpec prev spec)
      | none => m.insert n spec
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, spec) =>
        match m.get? n with
        | some prev => m.insert n (mergeSectionSpec prev spec)
        | none => m.insert n spec
  }

/-- Look up the most specific `PaperSectionSpec` governing `declName` (exact declaration
overrides enclosing namespace prefixes, longest prefix wins). -/
def getPaperSectionSpec? (env : Environment) (declName : Name) : Option PaperSectionSpec := Id.run do
  let state := paperSectionExt.getState env
  let mut foundMatches : Array (Nat × PaperSectionSpec) := #[]
  for (scope, spec) in state.toList do
    if scope == declName || scope.isPrefixOf declName then
      let score := if scope == declName then 10000 else scope.getNumParts
      foundMatches := foundMatches.push (score, spec)
  if foundMatches.isEmpty then return none
  let sorted := foundMatches.qsort fun a b => a.1 < b.1
  let mut acc := sorted[0]!.2
  for i in [1:sorted.size] do
    acc := mergeSectionSpec acc sorted[i]!.2
  return some acc

/-- Effective `CryptoRegister` for `declName` (defaults to `.constructive` when undeclared). -/
def effectiveRegister (env : Environment) (declName : Name) : CryptoRegister :=
  (getPaperSectionSpec? env declName).map (·.register) |>.getD .constructive

/-- Whether binder `name` is already fixed in `declName`'s section setting and should be omitted
from individual theorem `Let ...` headers (Q1–Q5 economy). -/
def isBinderSuppressedInSection (env : Environment) (declName : Name) (binderName : String) : Bool :=
  match getPaperSectionSpec? env declName with
  | some spec => spec.suppressedBinders.contains binderName
  | none => false

/-- Whether proposition head `predHead` is already a standing section assumption. -/
def isPredicateSuppressedInSection (env : Environment) (declName : Name) (predHead : Name) : Bool :=
  match getPaperSectionSpec? env declName with
  | some spec => spec.suppressedPredicates.contains predHead
  | none => false

/-- `Expr.mdata` key tagging strict `⊕` opacity walls (`by_leaf { ... }`). -/
def byLeafKindKey : Name := `vcc_leaf_kind
def byLeafSummaryKey : Name := `vcc_leaf_summary

/-- Wrap a checked proof term `e` in a zero-cost `by_leaf` opacity wall with a concise
mathematical summary (never expands tactic internals past this wall). -/
def wrapByLeafMData (summary : String) (e : Expr) (kind : String := "leaf") : Expr :=
  let md : MData := ({} : KVMap)
    |>.insert byLeafKindKey (DataValue.ofString kind)
    |>.insert byLeafSummaryKey (DataValue.ofString summary)
  Expr.mdata md e

/-- Unwrap `by_leaf` opacity wall metadata if present, returning `(kind, summary, inner)`. -/
def unwrapByLeafMData? (e : Expr) : Option (String × String × Expr) :=
  match e with
  | .mdata md inner =>
      match md.find byLeafKindKey, md.find byLeafSummaryKey with
      | some (.ofString k), some (.ofString s) => some (k, s, inner)
      | _, _ => none
  | _ => none

end Informalization.Core.Register

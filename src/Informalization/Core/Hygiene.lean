/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Hygiene & Presentation Normalization Firewall

Every `Lean.Expr` and `Name` passes through this firewall before reaching `LeanTeX`,
`Ontology`, or `GoalState`. It eliminates the core leakage defects observed in prior
informalization prototypes:
* macro hygiene suffixes (`_hyg`, `_uniq`, `_@.Module...`, `✝`);
* unreduced beta-redexes `(fun x => body) arg`;
* numeric/set coercion wrappers (`ENNReal.ofReal`, `NNReal.toReal`, `Nat.cast`, `Subtype.val`);
* anonymous hypothesis labels printed as `None`;
* ambient typeclass telescopes repeated on every definition or lemma.
-/

namespace Informalization.Core.Hygiene

open Lean Meta

/-- Erase Lean macro scopes and internal hygiene suffixes to produce a clean human binder name.
Returns `none` for purely synthetic / anonymous names (so callers never print `None` or `_hyg`). -/
def cleanBinderName? (n : Name) : Option String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then none
  else
    let raw := match n with
      | .str _ s => s
      | other => other.toString
    let stripped := (raw.splitOn "✝").headD raw
    let stripped := (stripped.splitOn "._@.").headD stripped
    let stripped := stripped.trimAscii.toString
    if stripped.isEmpty || stripped == "_" ||
        stripped.startsWith "_hyg" || stripped.startsWith "_uniq" ||
        stripped.startsWith "inst" || stripped.startsWith "x_" then
      none
    else
      some stripped

/-- Clean a binder name with a readable fallback if it was anonymous/synthetic. -/
def cleanBinderName (n : Name) (fallback : String := "x") : String :=
  (cleanBinderName? n).getD fallback

/-- Clean a constant name to its short readable leaf (stripping module prefixes & hygiene). -/
def shortConstName (n : Name) : String :=
  let n := n.eraseMacroScopes
  match n with
  | .str _ leaf => (leaf.splitOn "✝").headD leaf
  | other => other.toString

/-- Transparent numeric/coercion wrappers erased during presentation normalization.
These never change the mathematical statement for a human reader; exact Lean terms remain
available one click deeper in the Auditor view. -/
private def transparentUnaryWrappers : List Name :=
  [ `ENNReal.ofReal, `ENNReal.toReal, `NNReal.toReal, `Real.toNNReal,
    `Nat.cast, `Int.cast, `Rat.cast, `NNReal.ofReal,
    `Coe.coe, `CoeHTCT.coe, `CoeTC.coe, `CoeT.coe, `CoeHead.coe, `CoeTail.coe,
    `Subtype.val, `id, `optParam, `outParam, `autoParam ]

/-- Heads of ambient algebraic / Lean-bookkeeping typeclasses that should be factored into
the Ambient Setting once per document/section rather than repeated in every lemma header. -/
def ambientTypeclassHeads : List Name :=
  [ `Fintype, `Finite, `DecidableEq, `Decidable, `DecidablePred, `DecidableRel,
    `Inhabited, `Nonempty, `Nontrivial, `Unique, `Subsingleton,
    `AddCommGroup, `AddGroup, `Group, `CommMonoid, `Monoid, `Semiring, `Ring,
    `CategoryTheory.Category, `CategoryTheory.CategoryStruct,
    `CategoryTheory.MonoidalCategory, `CategoryTheory.MonoidalCategoryStruct,
    `ConstructiveCryptography.ResourceTheory,
    `ConstructiveCryptography.CryptographicAlgebra,
    `ConstructiveCryptography.CompatiblePseudoMetric,
    `ConstructiveCryptography.CompatibleDistinguisherClass,
    `ConstructiveCryptography.Distinguishers,
    `ConstructiveCryptography.DistinguisherAction,
    `ConstructiveCryptography.DistinguisherAdvantage.DominatedByDistance,
    `ConstructiveCryptography.Games,
    `ConstructiveCryptography.GameAction,
    `ConstructiveCryptography.DistinctionGames,
    `ConstructiveCryptography.DistinctionGameAction ]

/-- Is `ty` an ambient typeclass / bookkeeping instance? -/
def isAmbientTypeclass (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  match ty.getAppFn.consumeMData with
  | .const name _ =>
      if ambientTypeclassHeads.contains name then return true
      return (← isClass? ty).isSome
  | _ => return false

/-- Check if a local declaration is an implementation detail, auxiliary decl, or ambient
typeclass instance that should stay out of ordinary human-facing proof contexts. -/
def isSuppressedLocalDecl (d : LocalDecl) : MetaM Bool := do
  if d.isAuxDecl || d.isImplementationDetail then return true
  if d.binderInfo == .instImplicit then return true
  isAmbientTypeclass d.type

/-- Deterministic presentation normalizer:
1. Instantiates metavariables and strips `mdata`;
2. Beta-reduces applied lambdas `(fun x => body) arg` (eliminating kernel lambda clutter);
3. Unwraps transparent numeric/coercion wrappers (`ENNReal.ofReal`, `Nat.cast`, `Subtype.val`, …);
4. Preserves all cryptographic/mathematical definitions without unfolding them. -/
partial def normalizeForPresentation (e : Expr) (fuel : Nat := 128) : MetaM Expr := do
  if fuel == 0 then return e
  let e ← instantiateMVars e
  match e with
  | .mdata _ inner => normalizeForPresentation inner (fuel - 1)
  | .app .. =>
      let fn := e.getAppFn.consumeMData
      let args := e.getAppArgs
      -- Beta-reduce applied lambdas immediately (e.g. `(fun x => ...) v`)
      if fn.isLambda then
        let reduced := e.headBeta
        if reduced != e then
          return ← normalizeForPresentation reduced (fuel - 1)
      -- Unwrap transparent unary coercion wrappers (last explicit argument is the value)
      if let .const name _ := fn then
        if transparentUnaryWrappers.contains name then
          if let some lastArg := args.back? then
            return ← normalizeForPresentation lastArg (fuel - 1)
        -- `Set.mem_ofPred_eq` / `OfNat.ofNat` stays clean; normalize args otherwise
      let fn' ← normalizeForPresentation fn (fuel - 1)
      let args' ← args.mapM (normalizeForPresentation · (fuel - 1))
      return mkAppN fn' args'
  | .lam nm dom body bi =>
      let dom' ← normalizeForPresentation dom (fuel - 1)
      let body' ← normalizeForPresentation body (fuel - 1)
      return .lam nm dom' body' bi
  | .forallE nm dom body bi =>
      let dom' ← normalizeForPresentation dom (fuel - 1)
      let body' ← normalizeForPresentation body (fuel - 1)
      return .forallE nm dom' body' bi
  | .letE nm ty val body nondep =>
      -- Inline synthetic let-bindings whose names are hygienic; keep human-named lets
      let val' ← normalizeForPresentation val (fuel - 1)
      if (cleanBinderName? nm).isNone then
        normalizeForPresentation (body.instantiate1 val') (fuel - 1)
      else
        let ty' ← normalizeForPresentation ty (fuel - 1)
        let body' ← normalizeForPresentation body (fuel - 1)
        return .letE nm ty' val' body' nondep
  | .proj structName idx s =>
      return .proj structName idx (← normalizeForPresentation s (fuel - 1))
  | _ => return e

/-- Forbidden patterns that must NEVER appear in reader-facing output (automated CI gate). -/
def forbiddenLeakPatterns : List String :=
  [ "_hyg", "_uniq", "_@.", "None (", "asHom", "toDDC",
    "interface(s)", "user(s)", "query(s)", "resource(s)",
    "at interface ", "whiskering", "ENNReal.ofReal" ]

/-- Scan all rendered strings of a document and return any leakage violations. -/
def auditZeroLeakage (texts : Array String) : Array String := Id.run do
  let mut violations : Array String := #[]
  for txt in texts do
    for pat in forbiddenLeakPatterns do
      if (txt.splitOn pat).length > 1 then
        let snippet := (txt.take 120).toString
        violations := violations.push s!"Forbidden pattern '{pat}' found in: {snippet}"
  return violations

end Informalization.Core.Hygiene

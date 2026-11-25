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

/-- Pick a binder name that does not collide with any already-visible binder in `getLCtx`
(appending `'`, `''`, etc. when shadowed). -/
def freshShadowFreeName (nm : Name) (fallback : String := "x") : MetaM Name := do
  let base := cleanBinderName nm fallback
  let lctx ← getLCtx
  let mut existing : Std.HashSet String := {}
  for d in lctx do
    if !d.isAuxDecl && !d.isImplementationDetail && d.binderInfo != .instImplicit then
      if let some s := cleanBinderName? d.userName then
        existing := existing.insert s
  if !existing.contains base then
    return Name.mkSimple base
  let mut cand := base ++ "'"
  let mut tries := 0
  while existing.contains cand && tries < 8 do
    cand := cand ++ "'"
    tries := tries + 1
  if existing.contains cand then
    cand := base ++ "_" ++ toString (tries + 1)
  return Name.mkSimple cand

/-- Check whether `disp` appears as a rendered math token inside `mathSegs`. -/
def mathDispAppearsIn (mathSegs : Array String) (disp : String) : Bool :=
  if disp.isEmpty then false
  else if disp.length ≥ 2 then
    mathSegs.any fun seg => (seg.splitOn disp).length > 1
  else
    let ch := disp.toList.head!
    mathSegs.any fun seg =>
      let chars := seg.toList
      let rec check (prevAlpha : Bool) : List Char → Bool
        | [] => false
        | c :: rest =>
            let nextAlpha := match rest with | d :: _ => d.isAlpha | [] => false
            if c == ch && !prevAlpha && !nextAlpha then true
            else check (c.isAlpha || c == '\\') rest
      check false chars

/-- Clean a constant name to its short readable leaf (stripping module prefixes & hygiene).
For structural variant suffixes like `.perPort`, `.mk`, `.toFun`, preserve the meaningful
parent stem (`Real.perPort` -> `"Real"`, `𝓡₁.perPort` -> `"𝓡₁"`). -/
def shortConstName (n : Name) : String :=
  let n := n.eraseMacroScopes
  match n with
  | .str parent leaf =>
      let cleanLeaf := (leaf.splitOn "✝").headD leaf
      if cleanLeaf == "perPort" || cleanLeaf == "mk" || cleanLeaf == "toFun" || cleanLeaf == "val" then
        match parent with
        | .str _ pLeaf => (pLeaf.splitOn "✝").headD pLeaf
        | _ => cleanLeaf
      else cleanLeaf
  | other => other.toString

/-- Transparent numeric/coercion wrappers erased during presentation normalization.
These never change the mathematical statement for a human reader; exact Lean terms remain
available one click deeper in the Auditor view. -/
private def transparentUnaryWrappers : List Name :=
  [ `ENNReal.ofReal, `ENNReal.toReal, `ENNReal.ofNNReal, `ENNReal.coe,
    `NNReal.toReal, `NNReal.coe, `Real.toNNReal, `Real.ofNNReal,
    `Nat.cast, `Int.cast, `Rat.cast, `NNReal.ofReal,
    `Coe.coe, `CoeHTCT.coe, `CoeTC.coe, `CoeT.coe, `CoeHead.coe, `CoeTail.coe,
    `Subtype.val, `id, `outParam ]

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

/-- Is `ty` an ambient typeclass / bookkeeping instance? Uses fast syntactic lookup first
before falling back to `isClass?` (`whnf`). -/
def isAmbientTypeclass (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  match ty.getAppFn.consumeMData with
  | .const name _ =>
      if ambientTypeclassHeads.contains name then return true
      let env ← getEnv
      if Lean.isClass env name then return true
      return (← isClass? ty).isSome
  | _ => return false

/-- Check if a local declaration is an implementation detail, auxiliary decl, or ambient
typeclass instance using fast syntactic lookup (zero `whnf` on every goal context). -/
def isSuppressedLocalDecl (d : LocalDecl) : MetaM Bool := do
  if d.isAuxDecl || d.isImplementationDetail then return true
  if d.binderInfo == .instImplicit then return true
  let ty := d.type.consumeMData
  match ty.getAppFn.consumeMData with
  | .const name _ =>
      let env ← getEnv
      return ambientTypeclassHeads.contains name || Lean.isClass env name
  | _ => return false

/-- Deterministic presentation normalizer (with $O(\text{DAG})$ memoization on closed subterms):
1. Instantiates metavariables once and strips `mdata`;
2. Beta-reduces applied lambdas `(fun x => body) arg` (eliminating kernel lambda clutter);
3. Unwraps transparent numeric/coercion wrappers (`ENNReal.ofReal`, `Nat.cast`, `Subtype.val`, …);
4. Preserves all cryptographic/mathematical definitions without unfolding them. -/
partial def normalizeForPresentation (e : Expr) (fuel : Nat := 128) : MetaM Expr := do
  let e0 ← instantiateMVars e
  let rec go (cur : Expr) (rem : Nat) : StateRefT (Std.HashMap Expr Expr) MetaM Expr := do
    if rem == 0 then return cur
    let cacheKey? := if !cur.hasLooseBVars then some cur else none
    if let some k := cacheKey? then
      if let some hit := (← get).get? k then
        return hit
    let res ← match cur with
      | .mdata _ inner => go inner (rem - 1)
      | .app .. =>
          let fn := cur.getAppFn.consumeMData
          let args := cur.getAppArgs
          if fn.isLambda then
            let reduced := cur.headBeta
            if reduced != cur then
              go reduced (rem - 1)
            else
              let fn' ← go fn (rem - 1)
              let args' ← args.mapM (go · (rem - 1))
              pure (mkAppN fn' args')
          else
            let unwrap? := match fn with
              | .const name _ =>
                  if name == ``optParam || name == ``autoParam then args[0]?
                  else if transparentUnaryWrappers.contains name then args.back?
                  else none
              | _ => none
            match unwrap? with
            | some lastArg => go lastArg (rem - 1)
            | none =>
                let fn' ← go fn (rem - 1)
                let args' ← args.mapM (go · (rem - 1))
                pure (mkAppN fn' args')
      | .lam nm dom body bi =>
          let dom' ← go dom (rem - 1)
          let body' ← go body (rem - 1)
          pure (.lam nm dom' body' bi)
      | .forallE nm dom body bi =>
          let dom' ← go dom (rem - 1)
          let body' ← go body (rem - 1)
          pure (.forallE nm dom' body' bi)
      | .letE nm ty val body nondep =>
          let val' ← go val (rem - 1)
          if (cleanBinderName? nm).isNone then
            go (body.instantiate1 val') (rem - 1)
          else
            let ty' ← go ty (rem - 1)
            let body' ← go body (rem - 1)
            pure (.letE nm ty' val' body' nondep)
      | .proj structName idx s =>
          if structName == ``Subtype && idx == 0 then
            go s (rem - 1)
          else
            pure (.proj structName idx (← go s (rem - 1)))
      | _ => pure cur
    if let some k := cacheKey? then
      modify (·.insert k res)
    return res
  (go e0 fuel).run' {}

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

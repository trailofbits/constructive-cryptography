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
        stripped.startsWith "_vcc_" || stripped.startsWith "_since_" ||
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

/-- Choose a clean binder name without priming (e.g. `\mathcal{B}'`) unless a visible free
variable occurring inside `scopeExprs` already carries the same clean name. -/
def chooseUnshadowedBinderName (nm : Name) (scopeExprs : Array Expr)
    (fallback : String := "x") : MetaM Name := do
  match cleanBinderName? nm with
  | none => freshShadowFreeName nm fallback
  | some base =>
      let lctx ← getLCtx
      let mut conflict := false
      for ex in scopeExprs do
        for fvid in (Lean.collectFVars {} ex).fvarIds do
          if let some d := lctx.find? fvid then
            if !d.isAuxDecl && !d.isImplementationDetail && d.binderInfo != .instImplicit then
              if cleanBinderName? d.userName == some base then
                conflict := true
      if conflict then
        freshShadowFreeName nm fallback
      else
        return Name.mkSimple base

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

/-- Transparent numeric/coercion wrappers erased during presentation normalization, with
exact `(valArgIdx, expectedArity)` so over-applied wrappers like `Subtype.val α p g1 h`
unwrap ONLY the wrapper (`g1`) and re-apply all trailing arguments (`h`). -/
private def transparentWrapperSpecs : List (Name × Nat × Nat) :=
  [ (`ENNReal.ofReal, 0, 1), (`ENNReal.toReal, 0, 1),
    (`ENNReal.ofNNReal, 0, 1), (`ENNReal.coe, 0, 1),
    (`NNReal.toReal, 0, 1), (`NNReal.coe, 0, 1), (`NNReal.ofReal, 0, 1),
    (`Real.toNNReal, 0, 1), (`Real.ofNNReal, 0, 1),
    (`Nat.cast, 2, 3), (`Int.cast, 2, 3), (`Rat.cast, 2, 3),
    (`Coe.coe, 3, 4), (`CoeHTCT.coe, 3, 4), (`CoeTC.coe, 3, 4),
    (`CoeT.coe, 1, 4), (`CoeHead.coe, 3, 4), (`CoeTail.coe, 3, 4),
    (`CoeFun.coe, 3, 4), (`DFunLike.coe, 4, 5),
    (``Subtype.val, 2, 3), (``Subtype.mk, 2, 4), (``Fin.val, 1, 2), (``id, 1, 2),
    (``outParam, 0, 1), (``semiOutParam, 0, 1),
    (``optParam, 0, 2), (``autoParam, 0, 2) ]

/-- Extensible runtime registry for custom `@[math_wrapper]` `(valArgIdx, expectedArity)` entries. -/
initialize extraWrapperSpecsRef : IO.Ref (NameMap (Nat × Nat)) ← IO.mkRef {}

/-- Register a custom transparent wrapper constant `(valArgIdx, expectedArity)`. -/
def registerTransparentWrapper (name : Name) (valArgIdx expectedArity : Nat) : IO Unit :=
  extraWrapperSpecsRef.modify (·.insert name (valArgIdx, expectedArity))

/-- Look up `(valArgIdx, expectedArity)` for a transparent wrapper constant. -/
private def lookupWrapperSpec? (extra : NameMap (Nat × Nat)) (name : Name) : Option (Nat × Nat) :=
  match extra.find? name with
  | some spec => some spec
  | none =>
      match transparentWrapperSpecs.find? (·.1 == name) with
      | some (_, valIdx, arity) => some (valIdx, arity)
      | none => none

/-- Strip `mdata` and macro hygiene scopes from binder names with $O(\text{DAG})$ memoization
without unwrapping coercions/wrappers or beta-reducing terms (used for Auditor `rawLeanGoal`). -/
def stripMacroScopesExpr (e : Expr) : Expr :=
  let rec go (cur : Expr) : StateM (Std.HashMap Expr Expr) Expr := do
    if !cur.hasLooseBVars then
      if let some hit := (← get).get? cur then
        return hit
    let res ← match cur with
      | .mdata _ inner => go inner
      | .app f a => pure (.app (← go f) (← go a))
      | .lam nm dom body bi =>
          pure (.lam nm.eraseMacroScopes (← go dom) (← go body) bi)
      | .forallE nm dom body bi =>
          pure (.forallE nm.eraseMacroScopes (← go dom) (← go body) bi)
      | .letE nm ty val body nd =>
          pure (.letE nm.eraseMacroScopes (← go ty) (← go val) (← go body) nd)
      | .proj s idx inner => pure (.proj s idx (← go inner))
      | other => pure other
    if !cur.hasLooseBVars then
      modify fun m => m.insert cur res
    return res
  (go e).run' {}

/-- Fast O(DAG) check whether an `Expr` references `sorryAx`. -/
def exprContainsSorryAx (e : Expr) : Bool :=
  e.foldConsts (init := false) fun n acc => acc || n == ``sorryAx

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
and reducible-only `isClass?` so large project `def`s are never unfolded by `whnf`. -/
def isAmbientTypeclass (ty : Expr) : MetaM Bool := do
  let ty ← instantiateMVars ty
  match ty.getAppFn.consumeMData with
  | .const name _ =>
      if ambientTypeclassHeads.contains name then return true
      let env ← getEnv
      if Lean.isClass env name then return true
      return (← withTransparency .reducible (isClass? ty)).isSome
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
  let extraWrappers ← extraWrapperSpecsRef.get
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
            let unwrapped? : Option Expr := match fn with
              | .const name _ =>
                  match lookupWrapperSpec? extraWrappers name with
                  | some (valIdx, expectedArity) =>
                      if args.size ≥ expectedArity && valIdx < expectedArity then
                        some (mkAppN args[valIdx]! (args.extract expectedArity args.size))
                      else none
                  | none => none
              | _ => none
            match unwrapped? with
            | some unwrapped => go unwrapped (rem - 1)
            | none =>
                let fn' ← go fn (rem - 1)
                let args' ← args.mapM (go · (rem - 1))
                let combined := mkAppN fn' args'
                if fn'.isLambda && combined.headBeta != combined then
                  go combined.headBeta (rem - 1)
                else
                  pure combined
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
          if (structName == ``Subtype || structName == ``Fin) && idx == 0 then
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
    "at interface ", "whiskering", "ENNReal.ofReal",
    "distinguishing distance", "transcript distance", "Standing conventions." ]

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

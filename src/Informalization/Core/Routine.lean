/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.Overlay

/-!
# Fail-Closed Routine-Proof Classifier

Classifies checked proof subterms that represent pure Lean bookkeeping rather than
substantive cryptographic steps:
* reflexivity & definitional equality (`Eq.refl`, `rfl`, `le_rfl`);
* numeric casts & coercions (`ENNReal.coe_*`, `NNReal.coe_*`, `Nat.cast_*`);
* elementary algebraic/order closure (`ring`, `linarith`, `nlinarith`, `positivity`, `omega`);
* structural congruence/extensionality (`congrArg`, `congrFun`, `funext`, `propext`).

**Fail-closed invariant:** Any term mentioning a cryptographic theorem, a lemma marked
`informal_joint`, or an unknown project-domain theorem is NEVER classified as routine.
-/

namespace Informalization.Core.Routine

open Lean Meta Informalization.Core.Overlay

/-- Coarse category of a compressed routine proof receipt. -/
inductive RoutineKind
  | reflexivity
  | castAndCoercion
  | algebraAndOrder
  | congruenceAndExt
  | bookkeeping
  deriving DecidableEq, Repr, BEq, Inhabited

def RoutineKind.label : RoutineKind → String
  | .reflexivity      => "definitional equality"
  | .castAndCoercion  => "numeric casts and coercions"
  | .algebraAndOrder  => "elementary algebra and inequalities"
  | .congruenceAndExt => "extensionality and substitution of equals"
  | .bookkeeping      => "routine structural bookkeeping"

/-- Namespace prefixes belonging to standard Lean / Mathlib libraries (never expanded into
cryptographic proof trees). -/
def libraryPrefixes : List Name :=
  [ `Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `ProofWidgets,
    `Eq, `Ne, `Iff, `And, `Or, `Not, `True, `False, `Exists, `Subtype,
    `Nat, `Int, `Rat, `Real, `NNReal, `ENNReal, `Fin, `List, `Array, `Option,
    `Prod, `PProd, `Sum, `Sigma, `Set, `Finset, `Fintype, `Finsupp, `Multiset,
    `Function, `Equiv, `BitVec, `ByteArray,
    `Classical, `Decidable, `OfNat, `Add, `Sub, `Mul, `Div, `Pow, `HAdd, `HSub, `HMul, `HDiv, `HPow,
    `LE, `LT, `GE, `GT, `Min, `Max, `LinearOrder, `PartialOrder, `Preorder,
    `IsOrderedAddMonoid, `IsOrderedRing, `PosMulMono, `AddLeftMono, `AddRightMono,
    `Positivity, `NormNum, `Mathlib.Tactic, `Lean.Omega,
    `optParam, `autoParam, `outParam, `semiOutParam, `id, `ite, `dite,
    `congrArg, `congrFun, `congrFun', `congr, `funext, `propext, `of_eq_true, `eq_self, `rfl,
    `add_le_add, `mul_le_mul_of_nonneg_left, `mul_le_mul_of_nonneg_right,
    `le_trans, `le_rfl, `le_refl, `le_add_of_nonneg_left, `le_add_of_nonneg_right,
    `sub_le_sub, `sub_le_sub_left, `div_le_div_of_nonneg_left, `add_pos',
    `one_mul, `mul_one, `one_smul, `zero_add, `add_zero, `sub_zero ]

/-- Library module roots (Lean core and Mathlib) whose theorems are never expanded into
cryptographic sub-proofs. -/
private def libraryModuleRoots : List Name :=
  [ `Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `ProofWidgets ]

/-- Is `n` a Lean compiler-generated auxiliary theorem (`_proof_1`, `_simp_1`, `_eq_1`, etc.)
checking EVERY name component recursively? -/
def isCompilerAuxDecl (n : Name) : Bool :=
  let rec hasAuxComp : Name → Bool
    | .anonymous => false
    | .num p _ => hasAuxComp p
    | .str p s =>
        s.startsWith "_proof_" || s.startsWith "_simp_" ||
        s.startsWith "_eq_" || s.startsWith "_match_" || s.startsWith "_cstage" ||
        hasAuxComp p
  n.isInternal || hasAuxComp n

/-- Does `n` live in Lean core / Mathlib (by namespace prefix or compiler aux check)? -/
def isCoreOrMathlib (n : Name) : Bool :=
  let root := n.getRoot
  libraryPrefixes.contains root || libraryPrefixes.contains n || isCompilerAuxDecl n

/-- Environment-aware check: does `n` live in Lean core / Mathlib (including root-namespace
Mathlib lemmas and typeclass projections such as `IsOrderedAddMonoid.*`, `PosMulMono.*`,
`AddLeftMono.*`, `AddRightMono.*`, `Finsupp.*`, `add_le_add`, etc.)? -/
def isCoreOrMathlibIn (env : Environment) (n : Name) : Bool :=
  if isCoreOrMathlib n then true
  else match env.getModuleIdxFor? n with
    | some idx =>
        match env.header.moduleNames[idx.toNat]? with
        | some modName => libraryModuleRoots.contains modName.getRoot
        | none => false
    | none => false

private def isCastHead (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "ENNReal.coe" || s.startsWith "NNReal.coe" ||
  s.startsWith "Nat.cast" || s.startsWith "Int.cast" ||
  s.startsWith "ENNReal.ofReal" || s.startsWith "Set.mem_ofPred"

private def isReflexivityHead (n : Name) : Bool :=
  n == ``Eq.refl || n == ``rfl || n == `eq_self || n == `le_rfl ||
  n == `le_refl || n == `LE.le.refl

private def isCongrHead (n : Name) : Bool :=
  n == ``congrArg || n == ``congrFun || n == `congrFun' || n == ``congr || n == ``funext ||
  n == ``propext || n == `of_eq_true || n == ``Eq.symm || n == ``Eq.trans ||
  n == ``Eq.mp || n == ``Eq.mpr

private def isTypeclassRoutineHead (env : Environment) (n : Name) : Bool :=
  let root := n.getRoot
  Lean.isClass env n ||
  root == `IsOrderedAddMonoid || root == `IsOrderedRing ||
  root == `PosMulMono || root == `AddLeftMono || root == `AddRightMono

private def isNonRoutineConstructor (n : Name) : Bool :=
  n == ``And.intro || n == ``Exists.intro || n == ``Or.inl || n == ``Or.inr ||
  n == ``Prod.mk || n == ``Sigma.mk || n == ``Iff.intro || n == ``Subtype.mk

/-- Fast $O(\text{DAG})$ check (using Lean's memoized `foldConsts`) whether a proof subterm
references ANY project-level theorem or marked `informal_joint` (fail-closed guard so routine
compression never swallows real math, without exponential traversal on shared-DAG `simp` terms). -/
private def containsNonRoutineProof (env : Environment) (e : Expr) : Bool :=
  e.foldConsts (init := false) fun an acc =>
    if acc then true
    else if (getOverlay env an).isProofJoint then true
    else if isCoreOrMathlibIn env an then false
    else match env.find? an with
      | some (.thmInfo _) => true
      | _ => false

/-- Classify a single proof term node as routine if it stays purely within core/Mathlib
algebra, casts, reflexivity, or congruence, with no project-level cryptographic theorems inside. -/
partial def classifyRoutine? (env : Environment) (proof : Expr) (fuel : Nat := 64) :
    Option RoutineKind :=
  if fuel == 0 then none
  else match proof.consumeMData with
  | .fvar _ => none
  | .lam _ _ body _ => classifyRoutine? env body (fuel - 1)
  | .letE _ _ val body _ =>
      match classifyRoutine? env val (fuel - 1), classifyRoutine? env body (fuel - 1) with
      | some _, some k => some k
      | _, _ => none
  | .const name _ =>
      if isReflexivityHead name then some .reflexivity
      else if isCastHead name then some .castAndCoercion
      else if isCongrHead name then some .congruenceAndExt
      else if isTypeclassRoutineHead env name then some .bookkeeping
      else if isCoreOrMathlibIn env name then some .algebraAndOrder
      else none
  | .app .. =>
      match proof.getAppFn.consumeMData with
      | .const name _ =>
          if (getOverlay env name).isProofJoint || isNonRoutineConstructor name then none
          else if isReflexivityHead name then some .reflexivity
          else if isTypeclassRoutineHead env name then some .bookkeeping
          else if isCoreOrMathlibIn env name then
            -- Recursively verify no proof argument hides ANY project theorem!
            let ok := proof.getAppArgs.all fun arg => !containsNonRoutineProof env arg
            if ok then
              if isCastHead name then some .castAndCoercion
              else if isCongrHead name then some .congruenceAndExt
              else some .algebraAndOrder
            else none
          else none
      | _ => none
  | _ => none

end Informalization.Core.Routine

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
  [ `Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq,
    `Eq, `Ne, `Iff, `And, `Or, `Not, `True, `False, `Exists, `Subtype,
    `Nat, `Int, `Rat, `Real, `NNReal, `ENNReal, `Fin, `List, `Array, `Option,
    `Prod, `Sum, `Sigma, `Set, `Finset, `Fintype, `Function, `Equiv, `BitVec, `ByteArray,
    `Classical, `Decidable, `OfNat, `Add, `Sub, `Mul, `Div, `Pow, `HAdd, `HSub, `HMul, `HDiv, `HPow,
    `LE, `LT, `GE, `GT, `Min, `Max, `LinearOrder, `PartialOrder, `Preorder,
    `Positivity, `NormNum, `Mathlib.Tactic, `Lean.Omega,
    `optParam, `autoParam, `outParam, `semiOutParam, `id, `ite, `dite ]

/-- Is `n` a Lean compiler-generated auxiliary theorem (`_proof_1`, `_simp_1`, `_eq_1`, etc.)? -/
def isCompilerAuxDecl (n : Name) : Bool :=
  n.isInternal ||
  match n with
  | .str _ s =>
      s.startsWith "_proof_" || s.startsWith "_simp_" ||
      s.startsWith "_eq_" || s.startsWith "_match_" || s.startsWith "_cstage"
  | _ => false

/-- Does `n` live in Lean core / Mathlib (as opposed to CC or a downstream crypto project)? -/
def isCoreOrMathlib (n : Name) : Bool :=
  let root := n.getRoot
  libraryPrefixes.contains root || libraryPrefixes.contains n || isCompilerAuxDecl n

private def isCastHead (n : Name) : Bool :=
  let s := n.toString
  s.startsWith "ENNReal.coe" || s.startsWith "NNReal.coe" ||
  s.startsWith "Nat.cast" || s.startsWith "Int.cast" ||
  s.startsWith "ENNReal.ofReal" || s.startsWith "Set.mem_ofPred"

private def isCongrHead (n : Name) : Bool :=
  n == ``congrArg || n == ``congrFun || n == ``congr || n == ``funext ||
  n == ``propext || n == ``Eq.symm || n == ``Eq.trans || n == ``Eq.mp || n == ``Eq.mpr

private def isNonRoutineConstructor (n : Name) : Bool :=
  n == ``And.intro || n == ``Exists.intro || n == ``Or.inl || n == ``Or.inr ||
  n == ``Prod.mk || n == ``Sigma.mk || n == ``Iff.intro || n == ``Subtype.mk

/-- Recursively check whether a proof subterm references ANY project-level theorem or
marked `informal_joint` (fail-closed guard so routine compression never swallows real math). -/
private partial def containsNonRoutineProof (env : Environment) (e : Expr) (fuel : Nat := 32) : Bool :=
  if fuel == 0 then true
  else match e.consumeMData with
  | .const an _ =>
      if (getOverlay env an).isProofJoint then true
      else if isCoreOrMathlib an then false
      else match env.find? an with
        | some (.thmInfo _) => true
        | _ => false
  | .app f a =>
      containsNonRoutineProof env f (fuel - 1) || containsNonRoutineProof env a (fuel - 1)
  | .lam _ _ b _ => containsNonRoutineProof env b (fuel - 1)
  | .letE _ _ v b _ =>
      containsNonRoutineProof env v (fuel - 1) || containsNonRoutineProof env b (fuel - 1)
  | _ => false

/-- Classify a single proof term node as routine if it stays purely within core/Mathlib
algebra, casts, reflexivity, or congruence, with no project-level cryptographic theorems inside. -/
partial def classifyRoutine? (env : Environment) (proof : Expr) (fuel : Nat := 48) :
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
      if name == ``Eq.refl || name == ``rfl || name == `le_rfl || name == `LE.le.refl then
        some .reflexivity
      else if isCastHead name then some .castAndCoercion
      else if isCongrHead name then some .congruenceAndExt
      else if isCoreOrMathlib name then some .algebraAndOrder
      else none
  | .app .. =>
      match proof.getAppFn.consumeMData with
      | .const name _ =>
          if (getOverlay env name).isProofJoint || isNonRoutineConstructor name then none
          else if name == ``Eq.refl || name == `le_rfl then some .reflexivity
          else if isCoreOrMathlib name then
            -- Recursively verify no proof argument hides ANY project theorem!
            let ok := proof.getAppArgs.all fun arg => !containsNonRoutineProof env arg 24
            if ok then
              if isCastHead name then some .castAndCoercion
              else if isCongrHead name then some .congruenceAndExt
              else some .algebraAndOrder
            else none
          else none
      | _ => none
  | _ => none

end Informalization.Core.Routine

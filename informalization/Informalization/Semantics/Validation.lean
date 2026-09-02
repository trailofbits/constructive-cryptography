/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.Semantics.Registry

/-!
# Semantic root validation

Statement admission is based on recovered mathematical roles rather than a
successful pretty-print.  In particular, a generic arithmetic inequality is
not a security statement merely because its root declaration is `LE.le`.
-/

namespace Informalization.Semantics.Validation

open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Registry

/-- Security-statement genres recognized from typed semantic content. -/
inductive SecurityStatementKind where
  | advantageBound
  | distanceBound
  | indistinguishability
  | winningProbabilityBound
  | badEventProbabilityBound
  | construction
  | reduction
  deriving Inhabited, BEq, Repr

/-- A validated security root together with the semantic node that supplied
the cryptographic content. -/
structure SecurityStatementRoot where
  kind : SecurityStatementKind
  proposition : PropositionExpression
  focus : Node
  deriving Inhabited, BEq, Repr

private def directKind? : RelationRole → Option SecurityStatementKind
  | .advantageBound => some .advantageBound
  | .indistinguishability => some .indistinguishability
  | .construction => some .construction
  | .reduction => some .reduction
  | _ => none

private def boundedQuantityKind? : QuantityRole → Option SecurityStatementKind
  | .distinguishingAdvantage => some .advantageBound
  | .statisticalDistance => some .distanceBound
  | .winningProbability | .blindWinningProbability => some .winningProbabilityBound
  | .badEventProbability => some .badEventProbabilityBound
  | _ => none

private def boundedSubject? (proposition : PropositionExpression) : Option Expr :=
  (proposition.arguments.find? (·.role == .subject)).map (·.source)

private def securityStatementRootUsing?
    (recoverNode? : Expr → MetaM (Option Node)) (expression : Expr) :
    MetaM (Option SecurityStatementRoot) := do
  let some (.proposition proposition) ← recoverNode? expression
    | return none
  if let some kind := directKind? proposition.role then
    return some { kind, proposition, focus := .proposition proposition }
  unless proposition.role == .upperBound do return none
  let some subject := boundedSubject? proposition | return none
  let some focus ← recoverNode? subject | return none
  let .quantity quantity := focus | return none
  let some kind := boundedQuantityKind? quantity.role | return none
  return some { kind, proposition, focus }

/-- Validate and classify a theorem root from semantic content.

An upper bound is accepted only when its left side itself recovers as a
registered security quantity. -/
def securityStatementRoot? (environment : Environment) (expression : Expr) :
    MetaM (Option SecurityStatementRoot) :=
  securityStatementRootUsing? (recover? environment) expression

/-- Validate a theorem root against an explicit domain catalog and the source
environment. -/
def securityStatementRootWith? (environment : Environment) (catalog : Catalog)
    (expression : Expr) : MetaM (Option SecurityStatementRoot) :=
  securityStatementRootUsing? (recoverWith? environment catalog) expression

/-- Boolean security-root gate for callers that do not need the recovered
semantic witness. -/
def isSecurityStatementRoot (environment : Environment) (expression : Expr) :
    MetaM Bool := do
  return (← securityStatementRoot? environment expression).isSome

/-- Boolean form of `securityStatementRootWith?`. -/
def isSecurityStatementRootWith (environment : Environment) (catalog : Catalog)
    (expression : Expr) : MetaM Bool := do
  return (← securityStatementRootWith? environment catalog expression).isSome

end Informalization.Semantics.Validation

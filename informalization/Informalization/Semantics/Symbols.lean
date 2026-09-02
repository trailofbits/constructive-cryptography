/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Scoped mathematical symbols

The informalization backend assigns reader-facing symbols to semantic objects,
not to strings produced by the prose renderer.  A scope is persistent: a child
inherits its parent's bindings, while symbols introduced in the child do not
leak back into the parent.

The table deliberately retains the checked expression as identity data but
never renders that expression.  Domain renderers supply conventional preferred
symbols such as `R`, `S`, `k`, and `N`; this module only guarantees reuse and
capture avoidance.
-/

namespace Informalization.Semantics.Symbols

open Lean

/-- Mathematical role of a displayed symbol.  Roles disambiguate the rare
case where one elaborated expression is intentionally viewed in two different
ways. -/
inductive Role where
  | alphabet
  | sourceSpecification
  | targetSpecification
  | converter
  | sourceSystem
  | targetSystem
  | game
  | condition
  | queryBudget
  | querySet
  | sampleSize
  | populationSize
  | scalar
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Stable identity within one elaborated declaration. `binderName?` links
copies of the same theorem binder appearing in independently retained proof
contexts; the exact expression remains the primary identity. -/
structure Key where
  role : Role
  source : Expr
  binderName? : Option Name := none
  deriving Inhabited, BEq, Repr

/-- One symbol introduced at a semantic disclosure depth. -/
structure Binding where
  key : Key
  symbol : String
  introducedAt : Nat
  deriving Inhabited, BEq, Repr

/-- Persistent symbol environment shared by a proof and its nested scopes. -/
structure Scope where
  depth : Nat := 0
  bindings : Array Binding := #[]
  deriving Inhabited, BEq, Repr

/-- Enter one disclosure child without changing inherited bindings. -/
def Scope.child (scope : Scope) : Scope :=
  { scope with depth := scope.depth + 1 }

private def Key.sameReferent (left right : Key) : Bool :=
  left.role == right.role &&
    (left.source == right.source ||
      match left.binderName?, right.binderName? with
      | some leftName, some rightName => leftName == rightName
      | _, _ => false)

private def Scope.lookupBinding? (scope : Scope) (key : Key) : Option Binding :=
  scope.bindings.findSome? fun binding =>
    if binding.key.sameReferent key && binding.introducedAt <= scope.depth then
      some binding
    else
      none

/-- Find a symbol for the same semantic key in the current or an enclosing
scope. -/
def Scope.lookup? (scope : Scope) (key : Key) : Option String :=
  (scope.lookupBinding? key).map (·.symbol)

private def symbolCandidate (preferred : String) (index : Nat) : String :=
  if index == 0 then preferred else preferred ++ "_{" ++ toString index ++ "}"

private partial def freshSymbol (bindings : Array Binding) (preferred : String)
    (index : Nat := 0) : String :=
  let candidate := symbolCandidate preferred index
  if bindings.any (·.symbol == candidate) then
    freshSymbol bindings preferred (index + 1)
  else
    candidate

/-- Introduce a symbol, or reuse the inherited symbol already assigned to the
same semantic object.  The returned string is the only value intended for the
reader surface. -/
def Scope.introduce (scope : Scope) (key : Key) (preferred : String) :
    Scope × String :=
  match scope.lookupBinding? key with
  | some binding =>
      if binding.key.source == key.source then
        (scope, binding.symbol)
      else
        ({ scope with bindings := scope.bindings.push {
            key
            symbol := binding.symbol
            introducedAt := scope.depth
          } }, binding.symbol)
  | none =>
      let symbol := freshSymbol scope.bindings preferred
      ({ scope with bindings := scope.bindings.push {
          key
          symbol
          introducedAt := scope.depth
        } }, symbol)

/-- Return only those bindings visible from this disclosure depth. -/
def Scope.visibleBindings (scope : Scope) : Array Binding :=
  scope.bindings.filter (·.introducedAt <= scope.depth)

end Informalization.Semantics.Symbols

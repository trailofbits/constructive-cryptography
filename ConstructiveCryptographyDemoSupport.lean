/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography
import AbstractCryptography.MR11

/-!
# Presentation headers for the Constructive Cryptography demo

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

This module contains presentation-only command syntax for
`ConstructiveCryptographyDemo.lean`.  It follows Verbose Lean's successful
separation between a paper-like theorem header and the elaborated Lean
declaration.

The commands below do not bundle the AC algebra, add assumptions, or silently
select an algebraic setting.  The demo declares its ambient unbundled context
once.  These commands then expand only the paper-facing binders into ordinary
theorem binders:

* a parallel construction uses a monoid of converters acting on a
  pseudo-emetric resource carrier, together with non-expanding action and
  parallel composition; and
* the two-party algebraic theorem uses one monoid of systems.

The cryptographic inputs remain explicit as resources, protocols, simulator
classes, error bounds, and named assumptions.  Singleton specifications are
inserted only at the AC construction boundary.  This file
is imported only by the non-default demo target; it is not public AC syntax.
-/

open Lean

namespace ConstructiveCryptographyDemo.Presentation

/-- A presentation header for a scalar-metric parallel construction. -/
macro (name := parallelConstructionTheorem)
  doc:docComment
  "Theorem" name:ident
  ppLine "Given" "Resources" parallelResources:ident,+
  ppLine "Given" "Protocols" parallelProtocols:ident,+
  ppLine "Given" "Error" "Bounds" errorBounds:ident,+
  ppLine "Assume" assumptions:(ppSpace bracketedBinder)*
  ppLine "Conclusion" ppSpace conclusion:term
  ppLine "Proof" ppLine proof:tacticSeq
  ppLine "QED" : command => do
      let resourceType := mkIdentFrom name `Resource
      let converterType := mkIdentFrom name `Converter
      let resourceBinders ← parallelResources.getElems.mapM fun resource =>
        `(bracketedBinder| ($resource : $resourceType))
      let protocolBinders ← parallelProtocols.getElems.mapM fun protocol =>
        `(bracketedBinder| ($protocol : $converterType))
      let errorBinders ← errorBounds.getElems.mapM fun errorBound =>
        `(bracketedBinder| ($errorBound : ENNReal))
      `(command|
        $doc:docComment
        theorem $name
            $resourceBinders:bracketedBinder*
            $protocolBinders:bracketedBinder*
            $errorBinders:bracketedBinder*
            $assumptions:bracketedBinder* :
            $conclusion := by
          $proof)

/-- A presentation header for the monoid-level two-party argument in
MauRen11 Appendix C. -/
macro (name := twoPartyAlgebraicTheorem)
  doc:docComment
  "Theorem" name:ident
  ppLine "Given" "Systems" systems:ident,+
  ppLine "Given" "Protocols" partyProtocols:ident,+
  ppLine "Assume" assumptions:(ppSpace bracketedBinder)*
  ppLine "Conclusion" ppSpace conclusion:term
  ppLine "Proof" ppLine proof:tacticSeq
  ppLine "QED" : command => do
      let systemType := mkIdentFrom name `System
      let systemBinders ← systems.getElems.mapM fun system =>
        `(bracketedBinder| ($system : $systemType))
      let protocolBinders ← partyProtocols.getElems.mapM fun protocol =>
        `(bracketedBinder| ($protocol : $systemType))
      `(command|
        $doc:docComment
        theorem $name
            $systemBinders:bracketedBinder*
            $protocolBinders:bracketedBinder*
            $assumptions:bracketedBinder* :
            $conclusion := by
          $proof)

end ConstructiveCryptographyDemo.Presentation

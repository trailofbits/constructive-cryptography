/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.DocString
import Informalization.MassotMiller

/-!
# Static Lean hover information

The editor obtains hover popups from elaborator information carrying a term,
its type, and the declaration docstring.  A standalone informalization has no
live language server, so this module captures the corresponding stable fields
while the elaborated environment and local context are still available.
-/

namespace Informalization.MassotMiller.LeanHoverInfo

open Lean Meta

private def prettyExpr (expression : Expr) : MetaM String := do
  return toString (← ppExpr (← instantiateMVars expression))

private def declarationDocumentation? (name : Name) : MetaM (Option String) :=
  try Lean.findMarkdownDocString? name
  catch _ => pure none

/-- Hover data for a named declaration, using its fully qualified name, exact
declaration type, and current environment docstring. -/
def ofDeclaration (latex : String) (name : Name)
    (description? : Option String := none) : MetaM LeanHoverInfo := do
  let information ← getConstInfo name
  return {
    latex
    name := name.toString
    type := ← prettyExpr information.type
    explicit? := some name.toString
    documentation? := ← declarationDocumentation? name
    description?
  }

/-- Hover data for a checked expression in the active local context.  Exact
constants use their declaration signature; local binders and compound paper
symbols retain the instantiated expression and inferred type. -/
def ofExpr (latex : String) (expression : Expr)
    (description? : Option String := none) : MetaM LeanHoverInfo := do
  let expression := expression.consumeMData
  match expression with
  | .const name _ => ofDeclaration latex name description?
  | .fvar id =>
      let declaration ← id.getDecl
      return {
        latex
        name := declaration.userName.toString
        type := ← prettyExpr declaration.type
        explicit? := some declaration.userName.toString
        description?
      }
  | _ =>
      let explicit ← prettyExpr expression
      let type ← prettyExpr (← inferType expression)
      let documentation? ← match expression.getAppFn.consumeMData with
        | .const name _ => declarationDocumentation? name
        | _ => pure none
      return {
        latex
        name := explicit
        type
        explicit? := some explicit
        documentation?
        description?
      }

end Informalization.MassotMiller.LeanHoverInfo

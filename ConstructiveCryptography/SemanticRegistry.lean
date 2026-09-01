/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import Lean

/-!
# Semantic declaration registry

Declarations opt into machine-facing cryptographic tooling at their point of
definition.  The annotation records only the stable semantic coordinates that
Lean cannot infer from the declaration itself; consumers recover its module,
documentation, type, binders, and axioms from the elaborated environment.
-/

open Lean

namespace CryptoSemantic

/-- The deliberately small payload stored by `@[crypto_rule]`. -/
structure Entry where
  declaration : Name
  id : String
  kind : String
  layer : String
  deriving BEq, Hashable

initialize entries : SimplePersistentEnvExtension Entry (Array (Array Entry)) <-
  registerSimplePersistentEnvExtension {
    addImportedFn imported := imported
    addEntryFn state _ := state
  }

/-- All semantic entries visible in an elaborated environment. -/
def allEntries (environment : Environment) : Array Entry :=
  let state := PersistentEnvExtension.getState entries environment
  state.2.flatten ++ state.1

syntax (name := cryptoRuleAttr)
  "crypto_rule" str ident ident : attr

/-- Mark a declaration as a semantic rule available to proof tooling. -/
initialize registerBuiltinAttribute {
  name := `cryptoRuleAttr
  descr := "register a declaration and its semantic role for cryptographic proof tooling"
  add := fun declaration stx _ => do
    let `(attr| crypto_rule $id:str $kind:ident $layer:ident) := stx
      | throwError "invalid crypto_rule annotation"
    let entry : Entry := {
      declaration
      id := id.getString
      kind := kind.getId.toString
      layer := layer.getId.toString
    }
    let environment <- getEnv
    if (allEntries environment).any (fun old => old.id = entry.id) then
      throwError "duplicate semantic rule id {entry.id}"
    modifyEnv fun environment => entries.addEntry environment entry
}

end CryptoSemantic

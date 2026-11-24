/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Informalization.Core.LeanTeX

/-!
# Compile-Time-Checked Optional Flow & Notation Overlay (~10% Layer)

Any CC proof informalizes cleanly with **zero annotations** (90% pure Kyle Miller).
When an author wants to polish reading flow—adding brief, inconsequential transition or
motivation notes, disambiguating notation clashes (such as `r` for sponge rate vs. `P` for
public queries), or marking low-level bit-slicing lemmas as opaque stops—they attach them
in a lightweight companion module using the commands below.

**Trust boundary:**
* Every declaration name is resolved and checked against the live Lean environment at
  elaboration time (`realizeGlobalConstNoOverloadWithInfo`). If upstream CC renames a
  declaration, the overlay fails loudly at compile time.
* Flow notes are strictly rendered as visually distinct marginalia/signposting and **never**
  replace, suppress, or alter a Lean-checked statement, bound, or dependency edge.
-/

namespace Informalization.Core.Overlay

open Lean Elab Command Informalization.Core.LeanTeX

/-- Presentation-only metadata attached to a resolved Lean declaration. -/
structure DeclOverlay where
  title? : Option String := none
  flowBefore? : Option String := none
  flowAfter? : Option String := none
  symbolLatex? : Option String := none
  binderAliases : Array (String × String) := #[]
  /-- Natural-language `(singular, plural)` noun for a domain type (kills "element of T"). -/
  noun? : Option (String × String) := none
  /-- Natural-language English predicate phrase for a domain proposition (e.g. "is a supported sponge"). -/
  predPhrase? : Option String := none
  /-- 0-based explicit argument positions suppressed when rendering applications of this constant. -/
  hiddenArgs : List Nat := []
  /-- Render applications of this constant purely as its short symbol (e.g. `blockBytes (hash p)` -> `r`). -/
  isZeroArgNotation : Bool := false
  /-- Presentation kind ("Theorem", "Lemma", "Proposition", "Corollary"). -/
  entryKind? : Option String := none
  /-- Optional paper section heading starting at this declaration. -/
  sectionTitle? : Option String := none
  /-- Optional 1-2 sentence Maurer-voice section overview shown under `sectionTitle?`. -/
  sectionIntro? : Option String := none
  /-- Stop cross-lemma recursion at this declaration (e.g., low-level bit-slicing arithmetic). -/
  isOpaqueLeaf : Bool := false
  /-- Treat this declaration as a prominent mathematical proof joint (never auto-inlined). -/
  isProofJoint : Bool := false
  deriving Inhabited, Repr

private def mergeOverlay (old new : DeclOverlay) : DeclOverlay := {
  title?            := new.title? <|> old.title?
  flowBefore?       := new.flowBefore? <|> old.flowBefore?
  flowAfter?        := new.flowAfter? <|> old.flowAfter?
  symbolLatex?      := new.symbolLatex? <|> old.symbolLatex?
  binderAliases     := old.binderAliases ++ new.binderAliases
  noun?             := new.noun? <|> old.noun?
  predPhrase?       := new.predPhrase? <|> old.predPhrase?
  hiddenArgs        := if new.hiddenArgs.isEmpty then old.hiddenArgs else new.hiddenArgs
  isZeroArgNotation := old.isZeroArgNotation || new.isZeroArgNotation
  entryKind?        := new.entryKind? <|> old.entryKind?
  sectionTitle?     := new.sectionTitle? <|> old.sectionTitle?
  sectionIntro?     := new.sectionIntro? <|> old.sectionIntro?
  isOpaqueLeaf      := old.isOpaqueLeaf || new.isOpaqueLeaf
  isProofJoint      := old.isProofJoint || new.isProofJoint
}

initialize overlayExt :
    SimplePersistentEnvExtension (Name × DeclOverlay) (NameMap DeclOverlay) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (n, ov) =>
      match m.get? n with
      | some prev => m.insert n (mergeOverlay prev ov)
      | none => m.insert n ov
    addImportedFn := fun parts => parts.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m (n, ov) =>
        match m.get? n with
        | some prev => m.insert n (mergeOverlay prev ov)
        | none => m.insert n ov
  }

def getOverlay (env : Environment) (decl : Name) : DeclOverlay :=
  (overlayExt.getState env).getD decl {}

/-- Build a `SymbolTable` populated with all registered constant symbols, hidden ambient
argument positions, zero-arg short symbols, and binder aliases scoped to `rootDecl`. -/
def buildSymbolTable (env : Environment) (rootDecl : Name) : SymbolTable := Id.run do
  let state := overlayExt.getState env
  let mut tbl : SymbolTable := {}
  for (n, ov) in state.toList do
    if let some sym := ov.symbolLatex? then
      tbl := tbl.withConst n sym
    if !ov.hiddenArgs.isEmpty then
      tbl := tbl.withHiddenArgs n ov.hiddenArgs
    if ov.isZeroArgNotation then
      tbl := tbl.withZeroArgConst n
  let rootOv := getOverlay env rootDecl
  for (b, sym) in rootOv.binderAliases do
    tbl := tbl.withBinder b sym
  return tbl

private def addCheckedOverlay (id : Ident) (ov : DeclOverlay) : CommandElabM Unit := do
  let decl ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  modifyEnv fun env => overlayExt.addEntry env (decl, ov)

/-- Give a theorem/lemma a clean human title (checked against the Lean environment). -/
elab "informal_title " id:ident title:str : command =>
  addCheckedOverlay id { title? := some title.getString }

/-- Attach a short, inconsequential flow/motivation note before a declaration or proof step. -/
elab "informal_flow_before " id:ident note:str : command =>
  addCheckedOverlay id { flowBefore? := some note.getString }

/-- Attach a short, inconsequential caveat or transition note after a declaration. -/
elab "informal_flow_after " id:ident note:str : command =>
  addCheckedOverlay id { flowAfter? := some note.getString }

/-- Register a clean LaTeX display symbol for a resolved constant (e.g. `Π±`). -/
elab "informal_symbol " id:ident latex:str : command =>
  addCheckedOverlay id { symbolLatex? := some latex.getString }

/-- Register a zero-arg short LaTeX symbol for a record projection or ambient quantity
(e.g. `blockBytes (hash p)` → `r`, `customizationBytes limits` → `L_{\mathrm{cust}}`). -/
elab "informal_short_symbol " id:ident latex:str : command =>
  addCheckedOverlay id { symbolLatex? := some latex.getString, isZeroArgNotation := true }

/-- Register natural English `(singular, plural)` noun phrasing for a domain type
(eliminates `"element of MyStruct"`). -/
elab "informal_noun " id:ident sg:str pl:str : command =>
  addCheckedOverlay id { noun? := some (sg.getString, pl.getString) }

/-- Register natural English predicate phrasing for a unary/ambient domain proposition
(e.g. `supportedSponge p` → `"p is a supported sponge"`). -/
elab "informal_pred " id:ident phrase:str : command =>
  addCheckedOverlay id { predPhrase? := some phrase.getString }

/-- Suppress ambient leading explicit arguments (0-based indices) when printing applications
of a verbose Lean definition (e.g. `informal_hide_args keccakReal 0 1`). -/
elab "informal_hide_args " id:ident idxs:num* : command =>
  addCheckedOverlay id { hiddenArgs := idxs.toList.map (·.getNat) }

/-- Override a local binder's display symbol inside a theorem (e.g. disambiguate `r` → `P`). -/
elab "informal_binder " id:ident binder:str latex:str : command =>
  addCheckedOverlay id { binderAliases := #[(binder.getString, latex.getString)] }

/-- Override the presentation header (`"Theorem"`, `"Lemma"`, `"Proposition"`, `"Corollary"`). -/
elab "informal_kind " id:ident kind:str : command =>
  addCheckedOverlay id { entryKind? := some kind.getString }

/-- Start a named paper section at this declaration, with an optional concise overview sentence. -/
elab "informal_section " id:ident title:str intro:(str)? : command =>
  addCheckedOverlay id {
    sectionTitle? := some title.getString
    sectionIntro? := intro.map (·.getString)
  }

/-- Mark a low-level lemma as an opaque stop-point for cross-lemma recursion. -/
elab "informal_opaque " id:ident : command =>
  addCheckedOverlay id { isOpaqueLeaf := true }

/-- Mark a lemma as a prominent proof joint that Paper mode should never auto-inline. -/
elab "informal_joint " id:ident : command =>
  addCheckedOverlay id { isProofJoint := true }

end Informalization.Core.Overlay

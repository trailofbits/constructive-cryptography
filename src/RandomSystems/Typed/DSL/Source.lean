module

public import Lean

/-!
# Recorded DSL source

The component compiler records a declaration's original pseudocode only after successful
elaboration. The exported metadata contains exact source slices, not reconstructed programs.
It has no dependency on mathematical objects or on a renderer. Imported declarations retain
the source compiled into their module; no potentially stale file is read by a viewer.
-/

@[expose] public meta section

namespace SystemAlgebra.DSL
open Lean Elab Command

/-- One contiguous source slice. `block` distinguishes a procedure/initializer from a clause;
`proof` marks an explicit trailing proof. Neither changes the text. -/
structure SourceSection where
  header : String
  body : String := ""
  block : Bool := false
  proof : Bool := false
  deriving Inhabited, Repr, ToJson, BEq

/-- Original declaration text partitioned at parser boundaries, in source order. -/
structure SourceDocument where
  declaration : Name
  source : String
  header : String
  sections : Array SourceSection
  deriving Inhabited, Repr, ToJson, BEq

/-- Concatenating the presentation slices recovers the recorded source exactly. -/
def SourceDocument.reassemble (doc : SourceDocument) : String :=
  doc.sections.foldl (fun s part => s ++ part.header ++ part.body) doc.header

/-- Source is attached to the exact generated declaration, never to a display name or suffix. -/
initialize sourceDocuments :
    SimplePersistentEnvExtension (Name × SourceDocument) (NameMap SourceDocument) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun state (name, doc) => state.insert name doc
    addImportedFn := fun entries => entries.foldl
      (fun state parts => parts.foldl (fun state (name, doc) => state.insert name doc) state) {}
  }

/-- Refuse synthetic or rewritten tokens: copied source positions alone do not establish
that a macro-generated command was written in the source file. -/
partial def originalSourceTokens (source : String) : Syntax → Bool
  | .missing => true
  | .node _ _ args => args.all (originalSourceTokens source)
  | .atom (.original _ start _ stop) value =>
      String.Pos.Raw.extract source start stop == value
  | .ident (.original _ start _ stop) raw _ _ =>
      String.Pos.Raw.extract source start stop == raw.toString
  | _ => false

/-- Build a lossless partition from the original syntax. Each part supplies its syntax,
optional body start, and whether it is a trailing proof. Unknown syntax stays in the source;
missing or synthetic source information yields no view. -/
def sourceDocument? (source : String) (name : Name) (stx : Syntax)
    (parts : Array (Syntax × Option Syntax × Bool)) : Option SourceDocument := do
  guard (originalSourceTokens source stx)
  let range ← stx.getRange?
  let starts ← parts.mapM fun (part, _, _) => part.getPos?
  let headerEnd := starts[0]?.getD range.stop
  guard (range.start ≤ headerEnd && headerEnd ≤ range.stop)
  let mut sections := #[]
  for i in [:parts.size] do
    let (part, body?, proof) := parts[i]!
    let start ← part.getPos?
    let stop := starts[i + 1]?.getD range.stop
    let mid ← match body? with
      | some body => body.getPos?
      | none => some stop
    guard (range.start ≤ start && start ≤ mid && mid ≤ stop && stop ≤ range.stop)
    sections := sections.push {
      header := String.Pos.Raw.extract source start mid
      body := String.Pos.Raw.extract source mid stop
      block := body?.isSome
      proof }
  let doc : SourceDocument := {
    declaration := name
    source := String.Pos.Raw.extract source range.start range.stop
    header := String.Pos.Raw.extract source range.start headerEnd
    sections }
  guard (doc.reassemble == doc.source)
  return doc

/-- Record source only for a fresh declaration successfully emitted by this command.
The caller also checks that elaboration produced no errors. -/
def recordSource (name : Ident) (before : Environment) (stx : Syntax)
    (parts : Array (Syntax × Option Syntax × Bool)) : CommandElabM Unit := do
  let fullName := (← getCurrNamespace) ++ name.getId
  unless !(before.contains fullName) && (← getEnv).contains fullName do return
  let some doc := sourceDocument? (← getFileMap).source fullName stx parts | return
  modifyEnv fun env => sourceDocuments.addEntry env (fullName, doc)
  -- Anchor the original name to the actual declaration for native hovers and cursor views.
  addConstInfo name fullName

end SystemAlgebra.DSL

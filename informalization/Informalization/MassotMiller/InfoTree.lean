/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import all Init
import all Lean
public import Lean.Server.InfoUtils
public import Lean.Elab.Frontend

public section

/-!
# Live `InfoTree` capture and tactic-tree inference

Importing this module registers a command linter that retains the tactic
`InfoTree` produced for each subsequently elaborated declaration. The capture
uses an `IO.Ref` because Lean intentionally rolls back ordinary linter state.
-/

namespace Informalization.MassotMiller.InfoTree

open Lean Lean.Elab Lean.Elab.Command

/-- One live tactic record together with the complete surrounding context. -/
structure CapturedTactic where
  context : ContextInfo
  info : TacticInfo

/-- One elaborated term together with the complete surrounding context.  Term
records are essential for declarations written directly as terms (including
`calc` proofs): such declarations may contain no `TacticInfo` at all. -/
structure CapturedTerm where
  context : ContextInfo
  info : TermInfo

/-- All tactic records emitted while one command was elaborated. -/
structure CapturedCommand where
  command : Option Syntax
  /-- The unmodified elaborator trees.  Tactic extraction never replaces the
  source of truth used by later entity/proposition explainers. -/
  infoTrees : Array Elab.InfoTree := #[]
  tactics : Array CapturedTactic
  terms : Array CapturedTerm := #[]

builtin_initialize capturedCommands : IO.Ref (Array CapturedCommand) ← IO.mkRef #[]
builtin_initialize captureInstalled : IO.Ref Bool ← IO.mkRef false

/-- Collect tactic nodes in `InfoTree` preorder while propagating contexts. -/
partial def collectTactics (tree : Elab.InfoTree)
    (context? : Option ContextInfo := none) : Array CapturedTactic :=
  match tree with
  | .hole _ => #[]
  | .context inner child => collectTactics child (inner.mergeIntoOuter? context?)
  | .node info children =>
      match context? with
      | none => #[]
      | some context =>
          let here := match info with
            | .ofTacticInfo tactic => #[{ context, info := tactic }]
            | _ => #[]
          let childContext := info.updateContext? (some context)
          children.toArray.foldl
            (fun out child => out ++ collectTactics child childContext) here

/-- Collect term nodes in `InfoTree` preorder while propagating contexts. -/
partial def collectTerms (tree : Elab.InfoTree)
    (context? : Option ContextInfo := none) : Array CapturedTerm :=
  match tree with
  | .hole _ => #[]
  | .context inner child => collectTerms child (inner.mergeIntoOuter? context?)
  | .node info children =>
      match context? with
      | none => #[]
      | some context =>
          let here := match info with
            | .ofTermInfo term => #[{ context, info := term }]
            | _ => #[]
          let childContext := info.updateContext? (some context)
          children.toArray.foldl
            (fun out child => out ++ collectTerms child childContext) here

/-- Capture every command containing at least one tactic node. -/
private def captureLinter : Linter where
  run command := do
    let trees ← Elab.getInfoTrees
    let tactics := trees.toArray.foldl
      (fun out tree => out ++ collectTactics tree) #[]
    let terms := trees.toArray.foldl
      (fun out tree => out ++ collectTerms tree) #[]
    unless tactics.isEmpty && terms.isEmpty do
      capturedCommands.modify (·.push {
        command := some command
        infoTrees := trees.toArray
        tactics
        terms
      })

def installCaptureLinter : IO Unit := do
  unless ← captureInstalled.get do
    addLinter captureLinter
    captureInstalled.set true

/-- Clear process-local captures before elaborating a new input module. -/
def clear : IO Unit := capturedCommands.set #[]

/-- Every captured command in elaboration order. -/
def all : IO (Array CapturedCommand) := capturedCommands.get

/-- Tactic records whose innermost context belongs to declaration `name`. -/
def forDeclaration (name : Name) : IO (Array CapturedTactic) := do
  let commands ← all
  return commands.foldl (init := #[]) fun out command =>
    out ++ command.tactics.filter (·.context.parentDecl? == some name)

/-- An elaboration context belonging to `name`, whether the declaration was
written with tactics or directly as a proof term. -/
def contextForDeclaration (name : Name) : IO (Option ContextInfo) := do
  let commands ← all
  for command in commands do
    if let some tactic := command.tactics.find? (·.context.parentDecl? == some name) then
      return some tactic.context
    if let some term := command.terms.find? (·.context.parentDecl? == some name) then
      return some term.context
  return none

/-- The original source spelling of a tactic, falling back to structural print. -/
def syntaxString (tactic : CapturedTactic) : String :=
  tactic.info.stx.reprint.getD (reprStr tactic.info.stx) |>.trimAscii.toString

/-- Stable textual identifier for a metavariable goal. -/
def goalIdString (goal : MVarId) : String := goal.name.toString

/-! ## Goal-ownership reconstruction -/

/-- A tactic after duplicate macro wrappers have been removed. -/
structure TacticEvent where
  source : CapturedTactic
  target : Option MVarId
  produced : Array MVarId
  /-- The kernel term assigned to `target` by this tactic, before any prose
  interpretation.  This is the proof-term decompiler's trusted input. -/
  proofTerm? : Option Expr

/-- Longest common suffix, used to separate newly produced goals from untouched
goals later in Lean's goal queue. -/
def commonSuffixSize {α : Type} [BEq α] (left right : List α) : Nat :=
  let rec loop : List α → List α → Nat → Nat
    | x :: xs, y :: ys, n => if x == y then loop xs ys (n + 1) else n
    | _, _, n => n
  loop left.reverse right.reverse 0

/-- Goals introduced by a tactic, excluding the untouched suffix of the queue. -/
def producedGoals (info : TacticInfo) : Array MVarId :=
  let suffix := commonSuffixSize info.goalsBefore info.goalsAfter
  let keep := info.goalsAfter.length - suffix
  (info.goalsAfter.take keep).toArray

/-- Two nested `TacticInfo`s can describe one macro-expanded source tactic. -/
def duplicateEvent (a b : CapturedTactic) : Bool :=
  syntaxString a == syntaxString b &&
    a.info.goalsBefore == b.info.goalsBefore &&
    a.info.goalsAfter == b.info.goalsAfter

/-- Parser/control nodes organize tactic syntax but are not mathematical tactic
steps.  Their descendants contain the actual user tactics. -/
def isStructuralTactic (tactic : CapturedTactic) : Bool :=
  let kind := tactic.info.stx.getKind.toString
  let spelling := syntaxString tactic
  kind == "null" || kind == "by" ||
    kind == "Lean.Parser.Term.byTactic" ||
    kind.startsWith "Lean.Parser.Tactic.tacticSeq" ||
    kind == "Lean.calcSteps" ||
    kind == "Lean.cdot" || kind == "Lean.cdotTk" ||
    -- Delimited tactic macros (`rw [...]`, `simp [...]`, and friends) can
    -- leave range-carrying punctuation nodes in the InfoTree.  They organize
    -- syntax but do not constitute proof steps of their own.
    spelling == "" || spelling == "[" || spelling == "]" || spelling == ";"

/-- Only original source nodes become authored tactic steps. Macro-generated
descendants and range-less `autoParam` tactics remain in the retained raw
InfoTrees, while their proof contribution is handled by kernel-term
decompilation. In particular, filtering these nodes does not classify a
declaration as “tactic free”: a term-level `calc` can contain tactic blocks. -/
def isSourceTactic (tactic : CapturedTactic) : Bool :=
  (tactic.info.stx.getRange? (canonicalOnly := true)).isSome &&
    !isStructuralTactic tactic

/-- Remove adjacent/nested duplicate macro wrappers without dropping genuine
repeated tactics whose goal ids differ. -/
def canonicalEvents (captured : Array CapturedTactic) : Array TacticEvent := Id.run do
  let mut result := #[]
  let mut previous : Option CapturedTactic := none
  for tactic in captured do
    if !isSourceTactic tactic then
      continue
    if previous.any (duplicateEvent · tactic) then
      continue
    let target := tactic.info.goalsBefore.head?
    result := result.push
      { source := tactic
        target
        produced := producedGoals tactic.info
        proofTerm? := target.bind tactic.info.mctxAfter.getExprAssignmentCore? }
    previous := some tactic
  return result

/-- A true proof tree. `children` contains later tactics solving goals created
by this node, including side goals that appeared later in the source proof. -/
structure TacticTree where
  event : TacticEvent
  children : Array TacticTree := #[]

private structure MutableNode where
  event : TacticEvent
  parent? : Option Nat
  children : Array Nat := #[]

private def ownerOf (owners : Array (MVarId × Nat)) (goal : MVarId) : Option Nat :=
  (owners.find? (fun entry => entry.1 == goal)).map (·.2)

private def setOwner (owners : Array (MVarId × Nat)) (goal : MVarId) (owner : Nat) :
    Array (MVarId × Nat) :=
  (owners.filter (fun entry => entry.1 != goal)).push (goal, owner)

private partial def freezeNode (nodes : Array MutableNode) (id : Nat) : Option TacticTree := do
  let node ← nodes[id]?
  let children := node.children.filterMap (freezeNode nodes)
  return { event := node.event, children }

/-- Infer goal ownership from before/after queues and re-parent delayed side goals. -/
def inferTacticForest (events : Array TacticEvent) : Array TacticTree := Id.run do
  let mut nodes : Array MutableNode := #[]
  let mut owners : Array (MVarId × Nat) := #[]
  for event in events do
    let id := nodes.size
    let parent? := event.target.bind (ownerOf owners)
    nodes := nodes.push { event, parent? }
    if let some parent := parent? then
      if let some p := nodes[parent]? then
        nodes := nodes.setIfInBounds parent { p with children := p.children.push id }
    for goal in event.produced do
      owners := setOwner owners goal id
  return (Array.range nodes.size).filterMap fun id =>
    match nodes[id]? with
    | some node => if node.parent?.isNone then freezeNode nodes id else none
    | none => none

/-- Full live path from captured `InfoTree`s to a re-parented tactic forest. -/
def tacticForestFor (name : Name) : IO (Array TacticTree) := do
  return inferTacticForest (canonicalEvents (← forDeclaration name))

/-! ## Source-module frontend -/

/-- The elaborated source module and every tactic node retained in its snapshots. -/
structure ElaboratedModule where
  environment : Environment
  commands : Array CapturedCommand

/-- Collect tactic-bearing commands from the incremental snapshot tree. -/
def capturedFromSnapshots (snapshots : Language.SnapshotTree) : Array CapturedCommand :=
  snapshots.getAll.filterMap fun snapshot => do
    let tree ← snapshot.infoTree?
    let tactics := collectTactics tree
    let terms := collectTerms tree
    if tactics.isEmpty && terms.isEmpty then none else some {
      command := none
      infoTrees := #[tree]
      tactics
      terms
    }

/--
The Massot–Miller `print_proof` frontend: parse and elaborate the source module,
retain the same snapshot `InfoTree`s used by Lean's language server, and return
the final environment together with every tactic/context record.  Passing no
instrumentation imports preserves the source's elaboration environment exactly;
semantic profiles should prefer that mode because importing a renderer may add
simp lemmas or instances and thereby perturb an otherwise valid proof.
-/
unsafe def elaborateSourceModule (input fileName : String) (moduleName : Name)
    (options : Options := {}) (moduleSetup? : Option ModuleSetup := none)
    (instrumentationImports : Array Name := #[`Informalization]) :
    IO (Option ElaboratedModule) := do
  clear
  installCaptureLinter
  Lean.enableInitializersExecution
  let options := Elab.async.set options false
  let effectiveName := moduleSetup?.map (·.name) |>.getD moduleName
  -- Miller's printers and linguistic attributes live in the environment of
  -- the module being explained.  External files do not import this package,
  -- so elaborate an in-memory instrumented copy that does.  This changes no
  -- source file and keeps the proof's own imports and declarations intact.
  let importHeader := String.join <| instrumentationImports.toList.map fun moduleName =>
    "import " ++ moduleName.toString ++ "\n"
  let instrumentedInput := importHeader ++ input
  -- `lake setup-file` fixes the original direct-import list.  Let the frontend
  -- reread the instrumented header while retaining Lake's resolved artifacts.
  let moduleSetup? := moduleSetup?.map fun setup => { setup with imports? := none }
  let some environment ← Elab.runFrontend instrumentedInput options fileName effectiveName
      (setup? := moduleSetup?)
    | return none
  return some {
    environment
    commands := ← all
  }

/-- Elaborate a UTF-8 Lean source file. -/
unsafe def elaborateFile (path : System.FilePath) (moduleName : Name)
    (moduleSetup? : Option ModuleSetup := none)
    (instrumentationImports : Array Name := #[`Informalization]) :
    IO (Option ElaboratedModule) := do
  elaborateSourceModule (← IO.FS.readFile path) path.toString moduleName
    (moduleSetup? := moduleSetup?) (instrumentationImports := instrumentationImports)

/-- Tactics for a declaration in an explicitly elaborated source module. -/
def ElaboratedModule.forDeclaration (module : ElaboratedModule) (name : Name) :
    Array CapturedTactic :=
  module.commands.foldl (init := #[]) fun out command =>
    out ++ command.tactics.filter (·.context.parentDecl? == some name)

/-- An exact frontend context for a declaration, including term-only proofs. -/
def ElaboratedModule.contextFor (module : ElaboratedModule) (name : Name) :
    Option ContextInfo :=
  module.commands.findSome? fun command =>
    (command.tactics.find? (·.context.parentDecl? == some name)).map (·.context) <|>
      (command.terms.find? (·.context.parentDecl? == some name)).map (·.context)

/-- Re-parented proof forest for a declaration in an elaborated source module. -/
def ElaboratedModule.tacticForestFor (module : ElaboratedModule) (name : Name) :
    Array TacticTree :=
  inferTacticForest (canonicalEvents (module.forDeclaration name))

end Informalization.MassotMiller.InfoTree

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Informalization.MassotMiller.English
import Informalization.Semantics.Realize

/-!
# Humanized proof-state checkpoints for semantic explanations

The semantic proof plan already retains the exact proposition and local
context of each checked proof-rule application.  This module converts those
backend snapshots into the same `GoalInfo` records used by Miller's tactic
explainer.  The conversion happens while a `MetaM` context is available;
public explanations receive only humanized strings, never kernel expressions,
metavariable identifiers, or semantic evidence identifiers.

The theorem root is kept separately from step checkpoints.  The explanation
bridge can therefore leave exactly one root checkpoint visible when collapsed
and reveal step checkpoints only inside expanded proof branches.
-/

namespace Informalization.Semantics.GoalState

open Lean Meta
open Informalization.Semantics.Discourse
open Informalization.Semantics.Realize
open Informalization.Semantics.Canonical
open Informalization.MassotMiller

/-- One humanized checkpoint indexed by its stable semantic evidence
reference.  The reference remains backend-only and is not rendered. -/
structure Entry where
  reference : EvidenceRef
  goal : GoalInfo
  deriving Inhabited, BEq, Repr

/-- Humanized theorem-root and semantic-step proof states. -/
structure Index where
  root? : Option GoalInfo := none
  entries : Array Entry := #[]
  deriving Inhabited, BEq, Repr

/-- Resolve the checkpoint for one explicitly selected semantic proof step. -/
def Index.forReference? (index : Index) (reference : EvidenceRef) : Option GoalInfo :=
  (index.entries.find? fun entry => entry.reference == reference).map (·.goal)

/-- Resolve the first goal checkpoint supporting a realized sentence or
detail.  Evidence identifiers are used only for this lookup. -/
def Index.forReferences? (index : Index)
    (references : Array EvidenceRef) : Option GoalInfo :=
  references.findSome? index.forReference?

/-! ## Reader-safety boundary

LeanTeX deliberately has an exact fallback for unknown expressions.  That is
useful to a developer, but it means successful pretty-printing alone is not a
reader-safety guarantee: an unsupported goal can still contain declaration
paths or elaborator names.  Proof-state checkpoints therefore fail closed.
Unknown targets stay in the diagnostic evidence graph until the domain
notation layer knows how to render them. -/

private def forbiddenFragments : Array String := #[
  "RandomSystems.", "Probability.", "Distribution.", "System.",
  "Lean.Expr", "Expr.", "_uniq", "_hyg", "✝", "Subtype.val",
  "Nat.cast", "ENNReal.ofReal", "Fintype.card", "HDiv.hDiv",
  "HMul.hMul", "HAdd.hAdd", "OfNat.ofNat", "LE.le", "LT.lt",
  "Eq.ndrec", "Classical.choice", "instOf", "instLE", "instLT",
  "instDecidable", "\\text{Finset.", "\\text{List.", "\\text{Set.",
  "\\text{Nat.", "\\text{Probability.", "\\text{RandomSystems.",
  "\\text{System.", "\\text{Distribution."
]

private def readerSafeText (value : String) : Bool :=
  value.length ≤ 320 &&
    !forbiddenFragments.any fun fragment => value.contains fragment

/-- `English.entityName` may enrich a function name with its type, for
example `f₀ : X → X`.  That is useful in a defining paragraph, but a goal
inspector already has a separate type column.  Keeping the annotation in the
name makes the row read as if the type had been stated twice. -/
private def bareContextName (value : String) : String :=
  match value.splitOn " : " with
  | [] => value
  | head :: _ => head

private def sanitizeContextItem? (item : ContextItem) : Option ContextItem := do
  guard (readerSafeText item.singularType)
  let name := item.name.map bareContextName |>.filter readerSafeText
  -- A local definition can have a useful reader-facing name and type even
  -- when its kernel-expanded value falls outside the notation registry.  In
  -- that case omit only the value; dropping the whole row can leave a symbol
  -- used by the target (for example a cardinality `k`) undeclared.
  let value := item.value.filter readerSafeText
  let pluralType := item.pluralType.filter readerSafeText
  let provides := item.provides.filter readerSafeText
  return { item with name, value, pluralType, provides }

private def sanitizeGoal? (goal : GoalInfo) : Option GoalInfo := do
  guard (readerSafeText goal.target)
  let paragraphForm :=
    if readerSafeText goal.paragraphForm then goal.paragraphForm else goal.target
  return {
    goal with
    paragraphForm
    items := goal.items.filterMap sanitizeContextItem?
    caseName := goal.caseName.filter readerSafeText
  }

private def rootGoal? (theoremType : Expr)
    (config : Informalization.MassotMiller.English.Config) :
    MetaM (Option GoalInfo) := do
  try
    forallTelescope theoremType fun _ conclusion => do
      let localContext ← getLCtx
      return sanitizeGoal? (← Informalization.MassotMiller.English.goalInfoFrom
        localContext conclusion none config)
  catch _ =>
    return none

/-! ## Dependency-directed local contexts

The semantic proof evidence is normally recovered inside the local context of
the enclosing theorem.  Passing that whole context to the public goal
inspector makes a small nested obligation appear to depend on every earlier
`let` and `have`.  A canonical derivation already identifies the conclusion,
its rule obligations, and their proof evidence, so these expressions provide
a declaration-name-independent relevance seed.

The closure below follows declaration types transitively.  A local-definition
value is retained only when all of its dependencies are already part of that
closure.  Thus a rule can expose operands such as the population size and
sample size without recursively importing the implementation which computed
the sample.  Hidden typeclass declarations remain available to the ontology
but are still omitted by `English.contextItems`, exactly as before. -/

private def appendFVars (localContext : LocalContext) (result : Array FVarId)
    (expression : Expr) : Array FVarId :=
  (Lean.collectFVars {} expression).fvarIds.foldl (init := result) fun result id =>
    if localContext.contains id && !result.contains id then result.push id else result

private def declarationDependencies (localContext : LocalContext)
    (result : Array FVarId) (declaration : LocalDecl) : Array FVarId :=
  appendFVars localContext result declaration.type

/-- Transitive local-declaration closure of the expressions which justify one
displayed checkpoint. -/
private def relevantDeclarations (localContext : LocalContext)
    (seeds : Array Expr) : Array FVarId := Id.run do
  let mut relevant := seeds.foldl (appendFVars localContext) #[]
  let mut cursor := 0
  while cursor < relevant.size do
    let id := relevant[cursor]!
    if let some declaration := localContext.find? id then
      relevant := declarationDependencies localContext relevant declaration
    cursor := cursor + 1
  return relevant

private def projectContext (localContext : LocalContext)
    (seeds : Array Expr) : LocalContext :=
  let relevant := relevantDeclarations localContext seeds
  localContext.decls.foldl (init := {}) fun result declaration? =>
    match declaration? with
    | some declaration => if relevant.contains declaration.fvarId then
        match declaration with
        | .ldecl (fvarId := id) (userName := name) (type := type)
            (value := value) (kind := kind) .. =>
            let valueDependencies := (Lean.collectFVars {} value).fvarIds.filter
              localContext.contains
            if valueDependencies.all relevant.contains then
              result.addDecl declaration
            else
              -- The value belongs to an implementation chain outside the
              -- current rule interface.  Keep the same checked local symbol
              -- and type, but present it as an opaque operand rather than
              -- pulling that entire chain into the checkpoint.
              result.mkLocalDecl id name type .default kind
        | _ => result.addDecl declaration
      else result
    | none => result

private def directLocalEvidence? (localContext : LocalContext)
    (evidence : Expr) : Option Expr :=
  match evidence.consumeMData with
  | .fvar id => if localContext.contains id then some evidence else none
  | _ => none

/-- Recover the local hypothesis which represents a canonical obligation.
The proof term stored in an application may have already reduced a small
hypothesis into a large implementation expression.  Following that expression
would make the rule checkpoint inherit every local used to construct the
proof.  Prefer the direct evidence fvar, then an in-scope proposition with the
same checked type. -/
private def obligationWitness? (localContext : LocalContext)
    (obligation : ProofObligation) : MetaM (Option Expr) := do
  if let some evidence := directLocalEvidence? localContext obligation.evidence then
    return some evidence
  for declaration? in localContext.decls do
    let some declaration := declaration? | continue
    if ← isProp declaration.type then
      if ← isDefEq declaration.type obligation.proposition then
        return some (.fvar declaration.fvarId)
  return none

private def derivationSeeds (localContext : LocalContext)
    (derivation : DerivationApplication) : MetaM (Array Expr) := do
  let mut result := #[]
  for obligation in derivation.obligations do
    if let some witness ← obligationWitness? localContext obligation then
      result := result.push witness
  return result

private partial def detailDerivationFor? (details : Array Realize.Detail)
    (reference : EvidenceRef) : Option DerivationApplication :=
  details.findSome? fun detail =>
    if detail.primaryEvidence == reference then detail.derivation?
    else detailDerivationFor? detail.children reference

private partial def detailEvidenceFor? (details : Array Realize.Detail)
    (reference : EvidenceRef) : Option (Array EvidenceRef) :=
  details.findSome? fun detail =>
    if detail.primaryEvidence == reference then some detail.evidence
    else detailEvidenceFor? detail.children reference

/-- The canonical application attached to the sentence/detail supported by an
evidence reference.  No theorem or local-variable names participate. -/
private def derivationFor? (source : Realize.Document)
    (reference : EvidenceRef) : Option DerivationApplication :=
  source.sentences.findSome? fun sentence =>
    if sentence.primaryEvidence? == some reference then sentence.derivation?
    else detailDerivationFor? sentence.details reference

/-- All checked provenance retained on the node selected by `reference`.
Only the explicit primary reference performs this lookup; merged wrapper
references cannot become presentation nodes by themselves. -/
private def evidenceFor? (source : Realize.Document)
    (reference : EvidenceRef) : Option (Array EvidenceRef) :=
  source.sentences.findSome? fun sentence =>
    if sentence.primaryEvidence? == some reference then some sentence.evidence
    else detailEvidenceFor? sentence.details reference

private def evidenceGoal? (item : EvidenceItem)
    (derivation? : Option DerivationApplication)
    (config : Informalization.MassotMiller.English.Config) :
    MetaM (Option GoalInfo) := do
  let some expected := item.expected? | return none
  let some localContext := item.localContext? | return none
  try
    let seeds ← match derivation? with
      | some derivation => withLCtx localContext #[] do
          derivationSeeds localContext derivation
      | none => pure #[expected, item.formal]
    let localContext := projectContext localContext (seeds.push expected)
    -- Entering the retained context first lets `goalInfoFrom` recover its
    -- local typeclass instances before it humanizes the same exact context.
    withLCtx localContext #[] do
      return sanitizeGoal? (← Informalization.MassotMiller.English.goalInfoFrom
        localContext expected none config)
  catch _ =>
    -- A missing notation/ontology entry must not break the informalization.
    -- More importantly, falling back to `repr Expr` here would expose kernel
    -- names, so an unrenderable checkpoint is simply omitted.
    return none

/-- Check that a presentation-safe wrapper proves exactly the primary node's
goal.  This is a semantic equality check on the retained expected
propositions, not a theorem-name or prose heuristic. -/
private def equivalentExpected? (primary candidate : EvidenceItem) : MetaM Bool := do
  let some primaryExpected := primary.expected? | return false
  let some candidateExpected := candidate.expected? | return false
  let some localContext := primary.localContext? | return false
  try
    withLCtx localContext #[] do
      return ← isDefEq primaryExpected candidateExpected
  catch _ =>
    return false

/-- If the preferred derivation's expression cannot be reader-safely
humanized, a normalized wrapper retained on the same node may supply the
presentation checkpoint.  It is accepted only after its expected proposition
has been checked definitionally equal to the primary expected proposition. -/
private def equivalentEvidenceGoal? (source : Realize.Document)
    (primary : EvidenceItem) (config : Informalization.MassotMiller.English.Config) :
    MetaM (Option GoalInfo) := do
  let some references := evidenceFor? source primary.reference | return none
  for reference in references do
    if reference == primary.reference then continue
    let some candidate := source.evidenceIndex.find? (·.reference == reference) | continue
    unless ← equivalentExpected? primary candidate do continue
    if let some goal ← evidenceGoal? candidate (derivationFor? source reference) config then
      return some goal
  return none

/-- Humanize the theorem root and every checked proof obligation retained by
the realized semantic document.  This is presentation enrichment only: it
does not alter discourse planning or the semantic diagnostic JSON. -/
def build (theoremType : Expr) (source : Realize.Document)
    (config : Informalization.MassotMiller.English.Config := {}) :
    MetaM Index := do
  let root? ← rootGoal? theoremType config
  let mut entries := #[]
  for item in source.evidenceIndex do
    let derivation? := derivationFor? source item.reference
    let directGoal? ← evidenceGoal? item derivation? config
    let goal? ← match directGoal? with
      | some goal => pure (some goal)
      | none => equivalentEvidenceGoal? source item config
    if let some goal := goal? then
      entries := entries.push { reference := item.reference, goal }
  return { root?, entries }

end Informalization.Semantics.GoalState

import Lean
import ProofWidgets.Data.Html
import Rendering.TypeNotation
import Rendering.Inspector

/-!
# Source-backed proof presentations

Optional adapters register exact witness types, projections and theorem argument positions.
The engine reads those terms without proving premises, choosing a technique, or identifying
objects by printed text. Chains retain their position binder. Transcript arguments present
their actual comparison using the same drawing as calculation steps; the method and its
source fields live in one inspector. Every mathematical abbreviation retains its original Lean
expression.
-/

namespace CCWidget
open Lean Server Meta ProofWidgets

/-- Calculation navigation mounts one relation at a time. Container queries
control its layout independently of the selected relation. -/
structure CalcStepperProps where
  initialIndex : Nat
  labels : Array String := #[]
  deriving RpcEncodable

@[widget_module]
def CalcStepper : Component CalcStepperProps where
  javascript := "
    import * as React from 'react';
    const e = React.createElement;

    export default function CalcStepper(props) {
      const steps = React.Children.toArray(props.children);
      const clamp = React.useCallback(
        i => Math.max(0, Math.min(i, Math.max(steps.length - 1, 0))),
        [steps.length]);
      const [index, setIndex] = React.useState(() => clamp(props.initialIndex));
      React.useEffect(() => setIndex(clamp(props.initialIndex)),
        [props.initialIndex, clamp]);

      const move = delta => setIndex(i => clamp(i + delta));
      const keyDown = ev => {
        if (ev.target !== ev.currentTarget) return;
        if (ev.key === 'ArrowLeft' || ev.key === 'ArrowUp') {
          ev.preventDefault(); move(-1);
        } else if (ev.key === 'ArrowRight' || ev.key === 'ArrowDown') {
          ev.preventDefault(); move(1);
        }
      };
      if (steps.length === 0) return null;
      return e('div', {
          className: 'calc-stepper',
          tabIndex: 0,
          onKeyDown: keyDown
        },
        e('div', { className: 'calc-step-controls' },
          e('button', { type: 'button', disabled: index === 0,
            onClick: () => move(-1), 'aria-label': 'Previous calculation step' }, '←'),
          e('span', { className: 'calc-step-count', 'aria-live': 'polite',
            'aria-label': `Calculation step ${index + 1} of ${steps.length}` },
            `${index + 1} / ${steps.length}`),
          e('button', { type: 'button', disabled: index + 1 >= steps.length,
            onClick: () => move(1), 'aria-label': 'Next calculation step' }, '→'),
        e('details', {className:'cc-proof-overview'},
          e('summary', {'aria-label':'Choose calculation step',
            title:'Choose calculation step'}, '⋯'),
          e('nav', {'aria-label':'Proof steps'}, steps.map((_, i) =>
            e('button', {type:'button', key:i, onClick:ev=>{
              setIndex(i); ev.currentTarget.closest('details').open=false;},
              title:(props.labels || [])[i] || `Step ${i + 1}`,
              'aria-label':`Go to step ${i + 1}`,
              'aria-current':i === index ? 'step' : undefined}, String(i + 1)))))),
        e('div', { className: 'calc-step-body' }, steps[index]));
    }
  "

/-- One actual structure projection, with its mathematical display label. -/
structure ProofFieldSpec where
  label : String
  projection : Name
  deriving Inhabited

structure ProofGroupSpec where
  label : String
  fields : Array ProofFieldSpec
  deriving Inhabited

/-- The adapter supplies every operation used to read an implication witness. -/
structure ChainSchema where
  carrier : Name
  systemsFromEnd : Nat
  usesFromEnd : Nat
  attach : Name
  targetLeft : Name
  targetRight : Name
  index : Name
  direction : Name
  transformation : Name
  startEq : Name
  linkEq : Name
  endEq : Name
  reductions : Array Name := #[]
  deriving Inhabited

/-- Exact operations and fields of an extended-transcript expectation argument. The optional
semantic adapter owns this correspondence; the renderer imports no systems theory. -/
structure TranscriptSchema where
  sample : Name
  component : Name
  presents : Name
  revealed : Name
  realReveal : Name
  idealReveal : Name
  classes : Name
  classify : Name
  error : Name
  ratio : Name
  bound : Name
  mixture : Name
  realMass : Name
  idealMass : Name
  idealLaw : Name
  deriving Inhabited

/-- A technique with explicit fields, rather than a classification of arbitrary proof syntax. -/
structure ArgumentSchema where
  carrier : Name
  title : String
  parameters : Array (String × Nat)
  groups : Array ProofGroupSpec
  transcript? : Option TranscriptSchema := none
  deriving Inhabited

inductive ProofSchema where
  | chain (schema : ChainSchema)
  | argument (schema : ArgumentSchema)
  deriving Inhabited

def ProofSchema.carrier : ProofSchema → Name
  | .chain s => s.carrier
  | .argument s => s.carrier

initialize proofSchemas : SimpleScopedEnvExtension ProofSchema (NameMap ProofSchema) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m s => m.insert s.carrier s
    initial := {} }

/-- Only registered theorem applications may expose a witness supplied as an argument. -/
structure ProofBridge where
  theoremName : Name
  arity : Nat
  witnessFromEnd : Nat
  /-- Optional per-position bound and its proof, taken from the actual theorem arguments. -/
  errorFromEnd? : Option Nat := none
  premiseFromEnd? : Option Nat := none
  premiseByAssumption : Bool := false
  deriving Inhabited

initialize proofBridges : SimpleScopedEnvExtension ProofBridge (NameMap ProofBridge) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m s => m.insert s.theoremName s
    initial := {} }

/-- Registration validates projections against their owning structure, never its printed name. -/
def registerProofSchema (schema : ProofSchema) : Elab.Command.CommandElabM Unit := do
  let env ← getEnv
  let some _ := getStructureInfo? env schema.carrier
    | throwError "proof view: {schema.carrier} is not a structure"
  let projections : Array Name := match schema with
    | .chain s => #[s.targetLeft, s.targetRight, s.index, s.direction, s.transformation,
        s.startEq, s.linkEq, s.endEq]
    | .argument s => s.groups.flatMap fun (g : ProofGroupSpec) => g.fields.map (·.projection)
  for name in projections do
    let some info := env.getProjectionFnInfo? name
      | throwError "proof view: {name} is not a projection"
    let .ctorInfo ctor ← getConstInfo info.ctorName
      | throwError "proof view: invalid projection constructor"
    unless ctor.induct == schema.carrier do
      throwError "proof view: {name} belongs to a different structure"
  if let .argument s := schema then
    if let some t := s.transcript? then
      for name in #[t.sample, t.component, t.presents, t.revealed, t.realReveal,
          t.idealReveal, t.classes, t.classify, t.error, t.ratio, t.bound] do
        unless projections.contains name do throwError "proof view: missing transcript field {name}"
      for name in #[t.mixture, t.realMass, t.idealMass, t.idealLaw] do
        let _ ← getConstInfo name
      unless s.parameters.size == 4 do
        throwError "proof view: transcript parameters must be real, ideal, error and domain"
  Elab.Command.liftCoreM <| proofSchemas.add schema .global

/-- Store the exact theorem arity; partial applications cannot activate a technique view. -/
def registerProofBridge (name : Name) (witnessFromEnd : Nat)
    (errorFromEnd? premiseFromEnd? : Option Nat := none)
    (premiseByAssumption := false) : Elab.Command.CommandElabM Unit := do
  let info ← getConstInfo name
  let arity := info.type.getNumHeadForalls
  unless witnessFromEnd < arity && errorFromEnd?.all (· < arity) &&
      premiseFromEnd?.all (· < arity) do throwError "proof view: argument index out of range"
  Elab.Command.liftCoreM <| proofBridges.add
    { theoremName := name, arity, witnessFromEnd, errorFromEnd?, premiseFromEnd?,
      premiseByAssumption } .global

structure ProofField where
  label : String
  source : Expr
  value : Expr
  /-- An unreduced projection of an applied witness stays behind a disclosure. -/
  projectionOnly : Bool := false
  /-- A proof field displays its proposition, with the supplied proof under disclosure. -/
  proposition? : Option Expr := none
  deriving Inhabited

structure ProofGroup where
  label : String
  fields : Array ProofField
  deriving Inhabited

structure ChainPosition where
  position : Expr
  assumption : ProofField
  direction : ProofField
  converter : ProofField
  left : Expr
  right : Expr
  error? : Option Expr := none
  premise? : Option Expr := none
  deriving Inhabited

/-- This is presentation data, not a new mathematical witness or proof API. -/
structure ProofView where
  title : String
  original : Expr
  witness : Expr
  parameters : Array ProofField := #[]
  groups : Array ProofGroup := #[]
  positions : Array ChainPosition := #[]
  /-- A symbolic index, retained in the local context of the generated interactive code. -/
  index? : Option Expr := none
  conclusion? : Option Expr := none
  theorem? : Option Expr := none
  transcript? : Option TranscriptSchema := none
  deriving Inhabited

def proofArg? (e : Expr) (fromEnd : Nat) : Option Expr :=
  let args := e.getAppArgs
  if fromEnd < args.size then args[args.size - fromEnd - 1]? else none

/-- Reduce only the registered record projection. Do not unfold the resulting system or law. -/
def proofField (w : Expr) (spec : ProofFieldSpec) : MetaM ProofField := do
  let source ← mkAppM spec.projection #[w]
  let some info := (← getEnv).getProjectionFnInfo? spec.projection
    | throwError "proof view: missing projection"
  let value? ← project? w info.i
  let ty ← inferType source
  return {
    label := spec.label
    source := source
    value := value?.getD source
    projectionOnly := value?.isNone && !w.isFVar
    proposition? := if ← isProp ty then some ty else none }

/-- Reduce the registered witness constructors and finite-index selection only. Components,
converters, probability laws and arbitrary user definitions retain their declared names. -/
def reduceChainField (schema : ChainSchema) (e : Expr) : MetaM Expr :=
  withFreshCache <| withCanUnfoldPred (fun _ info => do
    let name := info.name
    let structural := #[`Fin, `Nat, `Bool, `Prod, `Sigma, `PSigma].any (·.isPrefixOf name)
    let projection := schema.carrier.isPrefixOf name &&
      ((← getEnv).getProjectionFnInfo? name).isSome
    let kernel := match info with
      | .ctorInfo _ | .recInfo _ | .inductInfo _ => true
      | _ => false
    return !info.isTheorem && (kernel || structural || projection ||
      schema.reductions.contains name || #[``ite, ``dite, ``instHAdd, ``instHMod,
        ``instHSub, ``instOfNatNat, ``instAddNat, ``instSubNat, ``HAdd.hAdd,
        ``HMod.hMod, ``HSub.hSub, ``OfNat.ofNat, ``Add.add, ``Mod.mod, ``Sub.sub,
        ``LT.lt, ``LE.le, ``Decidable.decide].contains name)) <| whnf e

/-- Bind the symbolic index while constructing the view, so all native hovers keep its context. -/
def withProofView {α : Type} (e : Expr) (k : ProofView → MetaM α) : MetaM (Option α) := do
  let e ← instantiateMVars e
  if e.hasExprMVar || e.hasSorry then return none
  let mut witness := e
  let mut bridge? := none
  if let some name := e.getAppFn.constName? then
    if let some bridge := (proofBridges.getState (← getEnv)).find? name then
      if e.getAppNumArgs == bridge.arity then
        witness := (proofArg? e bridge.witnessFromEnd).getD e
        bridge? := some bridge
  let ty ← inferType witness
  let some name := ty.getAppFn.constName? | return none
  let some schema := (proofSchemas.getState (← getEnv)).find? name | return none
  let conclusion? ← if bridge?.isSome then pure (some (← inferType e)) else pure none
  let base : ProofView := {
    title := "Substitution chain", original := e, witness := witness
    conclusion? := conclusion?
    theorem? := if bridge?.isSome then some e.getAppFn else none }
  match schema with
  | .argument schema =>
    let parameters ← schema.parameters.mapM fun (label, i) => do
      let some value := proofArg? ty i | throwError "proof view: missing parameter"
      return { label, source := value, value : ProofField }
    let groups ← schema.groups.mapM fun g => do
      return { label := g.label, fields := ← g.fields.mapM (proofField witness) : ProofGroup }
    return some (← k { base with
      title := schema.title, parameters, groups, transcript? := schema.transcript? })
  | .chain schema =>
    let some systems := proofArg? ty schema.systemsFromEnd
      | throwError "proof view: missing system family"
    let some uses := proofArg? ty schema.usesFromEnd
      | throwError "proof view: missing chain length"
    let index ← proofField witness ⟨"i", schema.index⟩
    let direction ← proofField witness ⟨"b", schema.direction⟩
    let converter ← proofField witness ⟨"ρ", schema.transformation⟩
    let position (j : Expr) : MetaM ChainPosition := do
      let applyField (f : ProofField) : MetaM ProofField := do
        let value ← reduceChainField schema (mkApp f.value j)
        return { f with source := mkApp f.source j, value }
      let assumption ← applyField index
      let direction ← applyField direction
      let converter ← applyField converter
      -- Reduce a direction only when it really is a Boolean constructor.
      let b := direction.value
      let nb ← reduceChainField schema (← mkAppM ``Bool.not #[b])
      let left ← reduceChainField schema (mkApp2 systems assumption.value b)
      let right ← reduceChainField schema (mkApp2 systems assumption.value nb)
      return {
        position := j
        assumption := assumption
        direction := { direction with value := b }
        converter := converter
        left := ← mkAppM schema.attach #[converter.value, left]
        right := ← mkAppM schema.attach #[converter.value, right]
        error? := bridge?.bind (·.errorFromEnd?) |>.bind (proofArg? e ·) |>.map (mkApp · j)
        premise? := bridge?.bind (·.premiseFromEnd?) |>.bind (proofArg? e ·) |>.map
          (mkApp · (if bridge?.any (·.premiseByAssumption) then assumption.value else j)) }
    let groups := #[
      { label := "Endpoints", fields := #[← proofField witness ⟨"L", schema.targetLeft⟩,
          ← proofField witness ⟨"R", schema.targetRight⟩] : ProofGroup },
      { label := "Exact joins", fields := #[← proofField witness ⟨"start", schema.startEq⟩,
          ← proofField witness ⟨"join", schema.linkEq⟩,
          ← proofField witness ⟨"end", schema.endEq⟩] : ProofGroup }]
    -- `uses` is one less than the number of positions. No `Fintype` is enumerated.
    if let some n ← finiteTypeLiteral? uses then
      if n < 12 then
        let positions ← (Array.range (n + 1)).mapM fun j => do
          let index ← mkAppM ``Fin.ofNat #[mkNatLit (n + 1), mkNatLit j]
          position index
        return some (← k { base with groups, positions })
    let indexTy ← whnf (← inferType index.source)
    let .forallE _ domain _ _ := indexTy | throwError "proof view: invalid position family"
    withLocalDeclD `j domain fun j => do
      return some (← k { base with groups, positions := #[← position j], index? := some j })

/-- Rendering callbacks keep this module independent of system syntax and mathematical libraries. -/
structure ProofRenderContext where
  code : Expr → Option String → MetaM Html
  diagram : Expr → Array Html → MetaM Html
  interactive : Bool

/-- Exact source text is escaped by the HTML renderer, never treated as markup or math syntax. -/
def proofDiv (cls : String) (children : Array Html) : Html :=
  .element "div" #[("className", .str cls)] children

def proofDetails (label : String) (children : Array Html) : Html :=
  .element "details" #[("className", .str "cc-proof-details")]
    (#[.element "summary" #[] #[.text label]] ++ children)

/-- A field's short symbol is linked to its exact projection, including for symbolic witnesses. -/
def renderProofField (ctx : ProofRenderContext) (f : ProofField) : MetaM Html := do
  let shown := f.proposition?.getD f.value
  let body ← ctx.code shown none
  let body ← if f.proposition?.isSome then do
    pure (proofDetails "Proposition" #[body, proofDetails "Proof" #[← ctx.code f.source none]])
    else if f.projectionOnly then pure (proofDetails "Projection" #[body])
    else pure body
  return proofDiv "cc-proof-field"
    #[← ctx.code f.source (some f.label), body]

/-- Proof expressions are shown as justifications, never classified by pretty-printed names. -/
def proofJustification (ctx : ProofRenderContext) (proof : Expr)
    (source? : Option String := none) : MetaM Html := do
  let proof ← instantiateMVars proof
  let head := proof.getAppFn
  let label? := head.constName?.map (·.getString!)
  let mut obligations := #[]
  for m in ← getMVars proof do
    let obligation ← m.withContext do ctx.code (← m.getType) none
    obligations := obligations.push obligation
  let unresolved := proof.hasSorry || !obligations.isEmpty
  let summary ← if head.isConst || head.isFVar then ctx.code head label?
    else pure (.text (if unresolved then "?" else "Proof"))
  let source ← match source? with
    | some source => pure (.element "pre" #[] #[.text source])
    | none => ctx.code proof none
  return proofDiv "cc-proof-justification" #[
    .element "details" #[] #[.element "summary" #[] #[summary], source],
    if unresolved then proofDiv "cc-proof-obligations"
      (#[.text "Unfinished"] ++ obligations) else .text ""]

/-- Preserve both sides of a premise use without manufacturing an equality between them. -/
def renderChainPosition (ctx : ProofRenderContext) (p : ChainPosition) : MetaM Html := do
  let mut facts := #[← renderProofField ctx p.assumption,
    ← renderProofField ctx p.direction, ← renderProofField ctx p.converter]
  if let some error := p.error? then
    facts := facts.push (proofDiv "cc-proof-field" #[.text "ε", ← ctx.code error none])
  if let some premise := p.premise? then
    facts := facts.push (proofDetails "Premise"
      #[← ctx.code (← inferType premise) none, ← proofJustification ctx premise])
  return proofDiv "cc-proof-position" #[
    proofDiv "cc-proof-transition" #[← ctx.diagram p.left #[],
      .element "span" #[("className", .str "cc-proof-use"),
        ("title", .str "Oriented use of an assumption; its validity is supplied separately.")]
        #[.text "⇝"], ← ctx.diagram p.right #[]],
    proofDiv "cc-proof-facts" facts]

/-- Find a registered field by its declaration, independently of its printed label. -/
def transcriptField (v : ProofView) (name : Name) : MetaM ProofField := do
  let some f := (v.groups.flatMap (·.fields)).find? (·.source.isAppOf name)
    | throwError "proof view: missing field {name}"
  return f

/-- Check the registered transcript contract before labeling its fields as an H argument.
A changed upstream contract must be adapted explicitly, including its systems and budget. -/
def checkTranscriptEquations (v : ProofView) (s : TranscriptSchema)
    (p q : Expr) : MetaM Unit := do
  let ratio ← transcriptField v s.ratio
  let bound ← transcriptField v s.bound
  let classify := (← transcriptField v s.classify).source
  let error := (← transcriptField v s.error).source
  let same (a b : Expr) := withoutModifyingState (isDefEq a b)
  let mismatch := "proof view: unsupported transcript equation"
  let presents ← inferType (← transcriptField v s.presents).source
  unless presents.isAppOf ``Eq do throwError mismatch
  unless ← same (proofArg? presents 1).get! v.parameters[0]!.value do throwError mismatch
  let mixture ← mkAppM s.mixture #[(← transcriptField v s.sample).source,
    (← transcriptField v s.component).source]
  unless ← same (proofArg? presents 0).get! mixture do throwError mismatch
  let some domain := proofArg? (← inferType v.witness) 3 | throwError mismatch
  unless ← same domain v.parameters[3]!.value do throwError mismatch
  forallTelescope (← inferType ratio.source) fun xs body => do
    unless xs.size == 1 && body.isAppOf ``LE.le do throwError mismatch
    let lhs := (proofArg? body 1).get!
    unless lhs.isAppOf ``HMul.hMul do throwError mismatch
    let factor := (proofArg? lhs 1).get!
    unless factor.isAppOf ``HSub.hSub do throwError mismatch
    let one := (proofArg? factor 1).get!
    unless ← same one (← mkNumeral (← inferType one) 1) do throwError mismatch
    unless ← same (proofArg? factor 0).get! (mkApp error (mkApp classify xs[0]!)) do
      throwError mismatch
    unless ← same (proofArg? lhs 0).get! (mkApp q xs[0]!) do throwError mismatch
    unless ← same (proofArg? body 0).get! (mkApp p xs[0]!) do throwError mismatch
  forallTelescope (← inferType bound.source) fun xs body => do
    unless xs.size == 4 && body.isAppOf ``LE.le do throwError mismatch
    unless ← same (proofArg? body 0).get! v.parameters[2]!.value do throwError mismatch
    let sum := (proofArg? body 1).get!
    unless sum.isAppOf `Finset.sum && (proofArg? sum 1).get!.isAppOf `Finset.univ do
      throwError mismatch
    lambdaTelescope (proofArg? sum 0).get! fun cs summand => do
      unless cs.size == 1 && summand.isAppOf ``HMul.hMul do throwError mismatch
      unless ← same (proofArg? summand 1).get! (mkApp error cs[0]!) do throwError mismatch
      let mass := (proofArg? summand 0).get!
      unless mass.isAppOf `Probability.Distribution.mass do throwError mismatch
      let law := (proofArg? mass 1).get!
      unless law.isAppOf s.idealLaw do throwError mismatch
      unless ← same (proofArg? law 3).get! v.parameters[1]!.value do throwError mismatch
      unless ← same (proofArg? law 2).get! (← transcriptField v s.idealReveal).source do
        throwError mismatch
      unless ← same (proofArg? law 0).get! xs[1]! do throwError mismatch
      lambdaTelescope (proofArg? mass 0).get! fun ts event => do
        unless ts.size == 1 && event.isAppOf ``Eq do throwError mismatch
        unless ← same (proofArg? event 1).get! (mkApp classify ts[0]!) do throwError mismatch
        unless ← same (proofArg? event 0).get! cs[0]! do throwError mismatch

/-- One source inspector contains the witness, all fields and the mass abbreviations.
The main argument does not repeat record projections or proof-term disclosures. -/
def transcriptInspector (ctx : ProofRenderContext) (v : ProofView)
    (p q : Expr) (source? : Option String := none) : MetaM Html := do
  let mut entries := #[proofDetails "Argument"
    #[← ctx.code v.original none, .text " : ", ← ctx.code (← inferType v.original) none]]
  for f in v.parameters ++ v.groups.flatMap (·.fields) do
    let value ← if f.value == f.source then pure (.text "") else ctx.code f.value none
    entries := entries.push (proofDetails f.label #[← ctx.code f.source none,
      .text " : ", ← ctx.code (← inferType f.source) none, value])
  for (label, value) in #[("p · real extended mass", p), ("q · ideal extended mass", q)] do
    entries := entries.push (proofDetails label #[← ctx.code value none])
  if let some conclusion := v.conclusion? then
    entries := entries.push (proofDetails "Conclusion"
      #[← ctx.code conclusion none, ← proofJustification ctx v.original source?])
  let content := proofDiv "cc-h-source" entries
  if ctx.interactive then
    return Html.ofComponent Inspector
      { label := "H-coefficient argument", identity := (← ppExpr v.original).pretty,
        symbol := "H" } #[content]
  return .element "details"
    #[("className", .str "cc-inspector cc-inspector-static"),
      ("name", .str "cc-interface-inspector")]
    #[.element "summary" #[("aria-label", .str "H-coefficient argument"),
        ("title", .str "H-coefficient argument")] #[.text "H"],
      proofDiv "cc-inspector-body" #[content]]

/-- Standalone and calculation statements use the same drawing and footer. -/
def proofStep (content : Html) (current := false) : Html :=
  proofDiv (if current then "rgd rgd-cur" else "rgd") #[content]

/-- The method links to the supplied argument. Its fields stay behind the shared inspector. -/
def transcriptJustification (ctx : ProofRenderContext) (v : ProofView)
    (s : TranscriptSchema) (source? : Option String := none) : MetaM Html := do
  let sample := (← transcriptField v s.sample).source
  let component := (← transcriptField v s.component).source
  let realReveal := (← transcriptField v s.realReveal).source
  let idealReveal := (← transcriptField v s.idealReveal).source
  let p ← mkAppM s.realMass #[sample, component, realReveal]
  let q ← mkAppM s.idealMass #[v.parameters[1]!.value, idealReveal]
  checkTranscriptEquations v s p q
  return proofDiv "cc-proof-justification cc-proof-method"
    #[← transcriptInspector ctx v p q source?]

/-- A registered H application uses the same statement renderer and justification row as
calc. Bare arguments retain their two systems without manufacturing a relation or a step. -/
def renderTranscriptArgument (ctx : ProofRenderContext) (v : ProofView)
    (s : TranscriptSchema) : MetaM Html := do
  let justification ← transcriptJustification ctx v s
  let content ← match v.conclusion? with
    | some conclusion => do
      pure (proofStep (← ctx.diagram conclusion #[justification]))
    | none => do
      let systems := proofDiv "cc-proof-transition" #[
        ← ctx.diagram v.parameters[0]!.value #[], ← ctx.diagram v.parameters[1]!.value #[]]
      pure (proofDiv "cc-proof-argument" #[systems, justification])
  return proofDiv "cc-proof-view cc-h-method" #[content]

/-- Only exact registered applications receive a method inspector in a calculation.
Other proofs keep their ordinary source disclosure, including unfinished obligations. -/
def proofMethodJustification (ctx : ProofRenderContext) (proof : Expr)
    (source? : Option String := none) : MetaM Html := do
  let proof ← instantiateMVars proof
  try
    let method? ← withProofView proof fun v => do
      if let some s := v.transcript? then
        if v.conclusion?.isSome then return some (← transcriptJustification ctx v s source?)
      return none
    if let some (some method) := method? then return method
  catch _ => pure ()
  proofJustification ctx proof source?

/-- Compact technique and chain views share disclosures, source links and deterministic fields. -/
def renderProofView (ctx : ProofRenderContext) (v : ProofView) : MetaM Html := do
  if let some s := v.transcript? then return ← renderTranscriptArgument ctx v s
  let sourceLabel? := v.witness.getAppFn.constName?.map (·.getString!)
  let hypothesis ← if v.witness.isFVar then
      pure (!(← getFVarLocalDecl v.witness).isLet)
    else pure false
  let mut body := #[proofDiv "cc-proof-heading" #[.text v.title,
    ← ctx.code v.witness sourceLabel?,
    if hypothesis then .element "span" #[("className", .str "cc-proof-qualifier")]
      #[.text "Hypothesis"] else .text ""]]
  if let some conclusion := v.conclusion? then
    body := body.push (proofDetails "Conclusion" #[← ctx.diagram conclusion #[],
      ← proofJustification ctx v.original])
  if !v.parameters.isEmpty then
    body := body.push (proofDiv "cc-proof-parameters" (← v.parameters.mapM (renderProofField ctx)))
  if !v.positions.isEmpty then
    if v.conclusion?.isNone then
      body := body.push (.element "span" #[("className", .str "cc-proof-qualifier")]
        #[.text "Premises required"])
    if let some j := v.index? then
      body := body.push (proofDiv "cc-proof-index"
        #[← ctx.code j none, .text " : ", ← ctx.code (← inferType j) none])
    let positions ← v.positions.mapM (renderChainPosition ctx)
    let steps := if ctx.interactive && v.positions.size > 1 then
        Html.ofComponent CalcStepper { initialIndex := 0 } positions
      else if positions.size == 1 then positions[0]!
      else proofDiv "cc-proof-static-steps" (positions.mapIdx fun i step =>
        .element "details" #[("open", .bool (i == 0))]
          #[.element "summary" #[] #[.text s!"{i + 1} / {positions.size}"], step])
    body := body.push steps
  for g in v.groups do
    body := body.push (proofDetails g.label (← g.fields.mapM (renderProofField ctx)))
  body := body.push (proofDetails "Lean"
    #[← ctx.code v.original none, .text " : ", ← ctx.code (← inferType v.original) none])
  return proofDiv "cc-proof-view" body

end CCWidget

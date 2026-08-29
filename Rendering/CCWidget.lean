/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Lean.Meta.ExprLens
import ProofWidgets.Component.Panel.Basic
import ProofWidgets.Component.OfRpcMethod
import ProofWidgets.Component.MakeEditLink

/-!
# The constructive-cryptography goal diagram (`CCDiagram`)

A ProofWidgets panel that renders the current goal as a Maurer-style
system diagram.  **Systems are boxes with a variable number of
interfaces**: a fixed-interface random system has one interface (queries in,
answers out); a channel has three (`A`, `B`, `E`); MPC shapes have `n`.
Converters attach *at* an interface and compose serially along its wire;
composite systems (definitions) open into their connected parts inside a
labeled dashed frame.  The diagram is a **pure function of the goal
term** — re-rendered after every tactic step, with no widget state.

**Zero ceremony.**  The module ends with a global
`show_panel_widgets [CCDiagram]`: every module that (transitively)
imports `Rendering.CCWidget` displays the panel automatically, and the panel
renders nothing when there is nothing to draw.

**Theory-free.** Imports only ProofWidgets. It recognizes a small set of
theory-neutral heads, including `edist`, `dist`, `statDist`, and distribution
mass. Semantic adapter modules register the declarations that denote
resources, converters, attachment, parallel composition, constructions, and
relations. Calculation steps render as card bridges. **Unknown terms never
fail**—they degrade to term chips.

**Interactive**: box labels and bounds are the infoview's own
interactive code (hover for types, click to inspect); docstrings appear
as tooltips; inside a `calc` the whole chain renders as a hybrid ladder
of diagrams whose rungs navigate on click; shift-clicking a subterm
highlights and force-expands its box.

Labels: one line at the top of a file —
`cc_diagram_labels cbcReal "CBC 𝖱", Vn "Vₙ"` (names may be defined
later; suffix-matched) — or `@[cc_diagram "KEY"]` on declarations.
`#cc_diagram_check` / `#cc_diagram_view` are build-time guards.
-/

/-- Syntax for the `cc_diagram` attribute: an optional display label,
defaulting to the declaration's short name. -/
syntax (name := Lean.Parser.Attr.ccDiagram) "cc_diagram" (ppSpace str)? : attr

namespace CCWidget

open Lean Server Meta ProofWidgets

/-- Client-side presentation for a calculation.  Only one child rung is
mounted at a time; React retains the selected rung while `ResizeObserver`
tracks the actual infoview width and selects the horizontal/vertical layout. -/
structure CalcStepperProps where
  initialIndex : Nat
  breakpoint : Nat := 720
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
      const [vertical, setVertical] = React.useState(false);
      const root = React.useRef(null);

      React.useEffect(() => setIndex(clamp(props.initialIndex)),
        [props.initialIndex, clamp]);
      React.useLayoutEffect(() => {
        const node = root.current;
        if (!node) return;
        const update = entries => {
          const width = entries?.[0]?.contentRect?.width ?? node.clientWidth;
          setVertical(width < props.breakpoint);
        };
        const observer = new ResizeObserver(update);
        observer.observe(node);
        update();
        return () => observer.disconnect();
      }, [props.breakpoint]);

      const move = delta => setIndex(i => clamp(i + delta));
      const keyDown = ev => {
        if (ev.key === 'ArrowLeft' || ev.key === 'ArrowUp') {
          ev.preventDefault(); move(-1);
        } else if (ev.key === 'ArrowRight' || ev.key === 'ArrowDown') {
          ev.preventDefault(); move(1);
        }
      };
      if (steps.length === 0) return null;
      return e('div', {
          ref: root,
          className: 'calc-stepper cc-adaptive ' + (vertical ? 'vertical' : 'horizontal'),
          tabIndex: 0,
          onKeyDown: keyDown
        },
        e('div', { className: 'calc-step-controls' },
          e('button', { type: 'button', disabled: index === 0,
            onClick: () => move(-1), 'aria-label': 'Previous calculation step' }, '←'),
          e('span', { className: 'calc-step-count', 'aria-live': 'polite' },
            `Step ${index + 1} of ${steps.length}`),
          e('button', { type: 'button', disabled: index + 1 >= steps.length,
            onClick: () => move(1), 'aria-label': 'Next calculation step' }, '→')),
        e('div', { className: 'calc-step-body' }, steps[index]));
    }
  "

/-! ## Recognized head constants

The theory-free renderer recognizes only stable Mathlib and probability
operations directly.  Semantic AC, CC, and RS declarations are registered by
their owning adapters through `DeclRole`. -/

private def nRelaxFun : Name := `AbstractCryptography.Relaxation.toFun
private def nEpsilonRelaxation : Name :=
  `AbstractCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation

private def nStatDist : Name := `Probability.statDist
private def nMass : Name := `Probability.Distribution.mass
private def nFTransform : Name := `Probability.Distribution.fTransform

-- mathlib
private def nMathlibEdist : Name := `EDist.edist
private def nSMul : Name := `SMul.smul
private def nNNRealToReal : Name := `NNReal.toReal
private def nENNRealToReal : Name := `ENNReal.toReal

/-! ## Label registration -/

/-- Display labels used by `CCDiagram` for resource/converter constants
appearing in goals, indexed by constant name. -/
initialize ccDiagramLabels : SimpleScopedEnvExtension (Name × String) (NameMap String) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m (n, s) => m.insert n s
    initial := {}
  }

/-! ## Extensible semantic declaration roles

The renderer must depend on mathematical roles, not a closed list of Lean
implementation heads.  Argument indices are counted from the end of the fully
applied expression (`0` is the last explicit/implicit argument), which keeps
registrations stable across universe and type parameters. -/

inductive DeclRole where
  | application (converterFromEnd resourceFromEnd : Nat)
  | attachment (interfaceFromEnd converterFromEnd resourceFromEnd : Nat)
  | parallel (leftFromEnd rightFromEnd : Nat)
  | game (systemFromEnd eventFromEnd : Nat)
  | transparent (targetFromEnd : Nat)
  | distance (leftFromEnd rightFromEnd : Nat) (symbol : String)
  | winning (systemFromEnd : Nat) (symbol : String)
  | conditional (leftFromEnd rightFromEnd : Nat)
  | construction (realFromEnd converterFromEnd idealFromEnd : Nat)
  deriving Repr, Inhabited

structure DeclRule where
  head : Name
  role : DeclRole
  deriving Repr, Inhabited

initialize ccDiagramRules : SimpleScopedEnvExtension DeclRule (NameMap DeclRole) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m r => m.insert r.head r.role
    initial := {}
  }

private def natOfSyntax (stx : Syntax) : Nat := stx.isNatLit?.getD 0

syntax (name := ccDiagramApplicationCmd)
  "cc_diagram_application " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramAttachmentCmd)
  "cc_diagram_attachment " ident ppSpace num ppSpace num ppSpace num : command
syntax (name := ccDiagramParallelCmd)
  "cc_diagram_parallel " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramGameCmd)
  "cc_diagram_game " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramTransparentCmd)
  "cc_diagram_transparent " ident ppSpace num : command
syntax (name := ccDiagramRuleCheckCmd) "#cc_diagram_rule_check " ident : command
syntax (name := ccDiagramDistanceCmd)
  "cc_diagram_distance " ident ppSpace num ppSpace num ppSpace str : command
syntax (name := ccDiagramWinningCmd)
  "cc_diagram_winning " ident ppSpace num ppSpace str : command
syntax (name := ccDiagramConditionalCmd)
  "cc_diagram_conditional " ident ppSpace num ppSpace num : command
syntax (name := ccDiagramConstructionCmd)
  "cc_diagram_construction " ident ppSpace num ppSpace num ppSpace num : command

/-- Register `head converter resource` as a serial converter application.
Numeric arguments are positions counted from the end. -/
elab_rules : command
  | `(cc_diagram_application $n:ident $c:num $r:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .application (natOfSyntax c) (natOfSyntax r) } .global
  | `(cc_diagram_attachment $n:ident $i:num $c:num $r:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .attachment (natOfSyntax i) (natOfSyntax c) (natOfSyntax r) } .global
  | `(cc_diagram_parallel $n:ident $l:num $r:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .parallel (natOfSyntax l) (natOfSyntax r) } .global
  | `(cc_diagram_game $n:ident $s:num $e:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .game (natOfSyntax s) (natOfSyntax e) } .global
  | `(cc_diagram_transparent $n:ident $t:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .transparent (natOfSyntax t) } .global
  | `(cc_diagram_distance $n:ident $l:num $r:num $s:str) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .distance (natOfSyntax l) (natOfSyntax r) s.getString } .global
  | `(cc_diagram_winning $n:ident $a:num $s:str) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .winning (natOfSyntax a) s.getString } .global
  | `(cc_diagram_conditional $n:ident $l:num $r:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId, role := .conditional (natOfSyntax l) (natOfSyntax r) } .global
  | `(cc_diagram_construction $n:ident $r:num $p:num $i:num) =>
      Elab.Command.liftCoreM <| ccDiagramRules.add
        { head := n.getId,
          role := .construction (natOfSyntax r) (natOfSyntax p) (natOfSyntax i) } .global
  | `(#cc_diagram_rule_check $n:ident) => do
      let present ← Elab.Command.liftCoreM do
        return (ccDiagramRules.getState (← getEnv)).contains n.getId
      unless present do
        throwError "cc_diagram: no semantic rule registered for {n.getId}"

private def declRole? (e : Expr) : CoreM (Option DeclRole) := do
  let .const head _ := e.getAppFn | return none
  return (ccDiagramRules.getState (← getEnv)).find? head

private def argFromEnd? (args : Array Expr) (n : Nat) : Option (Nat × Expr) :=
  if n < args.size then
    let i := args.size - 1 - n
    some (i, args[i]!)
  else none

/-- The `cc_diagram` attribute registers a display label — works on
declarations from imported modules too (`attribute [cc_diagram "KEY"] keyRes`). -/
initialize registerBuiltinAttribute {
    name := `ccDiagram
    descr := "display label for the CCDiagram proof widget"
    add := fun declName stx kind => do
      let label ← match stx with
        | `(attr| cc_diagram $s:str) => pure s.getString
        | `(attr| cc_diagram) =>
          match declName with
          | .str _ s => pure s
          | n => pure n.toString
        | _ => throwError "unexpected cc_diagram attribute syntax"
      ccDiagramLabels.add (declName, label) kind
  }

/-- One item of a `cc_diagram_labels` command. -/
syntax ccDiagramLabelItem := ident ppSpace str

/-- `cc_diagram_labels cbcReal "CBC 𝖱", Vn "Vₙ", …` — register display
labels for the `CCDiagram` widget in one line.  Unlike the
`@[cc_diagram]` attribute, the named constants need not exist yet
(matching is by name suffix), so the command can sit at the top of the
file, before the definitions it labels. -/
elab "cc_diagram_labels " items:ccDiagramLabelItem,+ : command => do
  for item in items.getElems do
    match item with
    | `(ccDiagramLabelItem| $n:ident $l:str) =>
      Elab.Command.liftCoreM <| ccDiagramLabels.add (n.getId, l.getString) .global
    | _ => Elab.throwUnsupportedSyntax

/-! ## View model — one payload per proof state -/

/-- How a diagram node is drawn. -/
inductive BoxKind where
  /-- A resource: plain box, letterspaced serif label. -/
  | res
  /-- An attached converter: blue accent. -/
  | conv
  /-- A simulator (or `∗`-relaxation slot): amber accent. -/
  | sim
  /-- An unrecognized term: dashed chip with its pretty-printed form. -/
  | chip
  deriving BEq, Repr, ToJson, Inhabited

/-- One drawable element, remembering where in the goal it came from so
infoview subterm selection can highlight it (and so its label can be
rendered as interactive code). -/
structure Elem where
  label : String
  kind : BoxKind
  /-- `SubExpr.Pos` of the originating subterm, as a path. -/
  pos : Array Nat := #[]
  /-- A registered game: drawn with a labelled MBO output. -/
  mbo : Bool := false
  /-- First sentence of the head constant's docstring — the tooltip. -/
  descr : Option String := none
  /-- Produced by opening a definition: sits inside the composite frame. -/
  inner : Bool := false
  deriving Repr, ToJson, Inhabited

/-- One interface of a system: its name (empty for the anonymous single
interface of a random system), the converters attached at it — serially,
distinguisher side first — and its I/O alphabets. -/
structure Iface where
  label : String := ""
  chain : Array Elem := #[]
  /-- Adversarial/simulator interface — placed below the system. -/
  adv : Bool := false
  inType : Option String := none
  outType : Option String := none
  deriving Repr, ToJson, Inhabited

/-- One system: center column of resources and a variable number of
interfaces around it. -/
structure SystemView where
  center : Array Elem := #[]
  ifaces : Array Iface := #[]
  /-- Caption for a shift-click definitional expansion. -/
  unfolded? : Option String := none
  /-- Composite frame: a defined system drawn as its connected parts,
  the definition's paper name on the dashed boundary. -/
  frameLabel? : Option String := none
  frameMbo : Bool := false
  frameDescr? : Option String := none
  deriving Repr, ToJson, Inhabited

/-- One card of an advantage expression (`Δ(S,T) + Γᵇ Ŝ + ε`): the
building block of calculation-proof steps. -/
inductive AdvCard where
  /-- A two-system distance, badge `sym` (`Δ`, `δ`, `d`). -/
  | dist (sym : String) (l r : SystemView)
  /-- A one-sided win probability (`Γ`, `Γᵇ`). -/
  | win (sym : String) (s : SystemView)
  /-- The mass of an event under a distribution (the bad-flag picture). -/
  | mass (d : SystemView) (event : String)
  /-- A numeric or unrecognized summand. -/
  | num (label : String) (pos : Array Nat := #[])
  deriving Repr, ToJson, Inhabited

/-- The whole judgment: real vs ideal, related by `rel` within `eps?`.
`ideal? = none` for one-sided bounds; `bridge?` set for calculation
steps relating two advantage expressions. -/
structure JudgmentView where
  real : SystemView := {}
  ideal? : Option SystemView := none
  /-- Divider symbol: `≈`, `=`, `⊑`, `⊆`, `|≡`, `≤`, `Γᵇ ≤`, … -/
  rel : String
  eps? : Option String := none
  /-- Goal position of the bound — rendered as interactive code. -/
  epsPos? : Option (Array Nat) := none
  /-- One-line annotation under the diagram. -/
  note? : Option String := none
  /-- Card rows for advantage-expression steps: LHS cards, RHS cards. -/
  bridge? : Option (Array AdvCard × Array AdvCard) := none
  deriving Repr, ToJson, Inhabited

/-! ## Expression recognizers -/

/-- Arguments of `e` if it is `n` applied to exactly `arity` arguments. -/
private def matchApp? (e : Expr) (n : Name) (arity : Nat) : Option (Array Expr) :=
  if e.isAppOfArity n arity then some e.getAppArgs else none

/-- The last two arguments of `e` if its head is `n` — for heads whose
instance-argument count we do not pin down. -/
private def matchLast2? (e : Expr) (n : Name) : Option (Array Expr × Nat) :=
  if e.isAppOf n then
    let args := e.getAppArgs
    if args.size ≥ 2 then some (args, args.size) else none
  else none

/-- Position of argument `i` (0-based) of an `arity`-ary application at `p`. -/
private def argPos (p : SubExpr.Pos) (arity i : Nat) : SubExpr.Pos :=
  ((arity - 1 - i).fold (fun _ _ q => q.pushAppFn) p).pushAppArg

private def ppShort (e : Expr) : MetaM String := do
  if e.hasLooseBVars then
    -- never print open terms (`#0`); fall back to the head constant
    if let .const c _ := e.getAppFn then
      if let .str _ short := c then return short
    return "…"
  let f ← Meta.ppExpr e
  return (f.pretty (width := 120)).replace "\n" " "

/-- Display label for an interface value: the last name component when the
form is a dotless constructor path (`ABE.A` ↦ `A`, `0` ↦ `0`). -/
private def ppIface (e : Expr) : MetaM String := do
  let s ← ppShort e
  if s.contains ' ' then return s
  match s.splitOn "." with
  | [] => return s
  | parts => return parts.getLast!

/-- See through `Subtype.val` coercions (`↑π` for bundled converters). -/
private partial def stripVal (e : Expr) : Expr :=
  if e.isAppOfArity ``Subtype.val 3 then stripVal e.appArg! else e

/-- Label for a resource/converter term: the `@[cc_diagram]` /
`cc_diagram_labels` label of the head constant when registered,
otherwise its pretty-printed form.  The second component is `true` when
the term should degrade to a chip. -/
private def labelFor (e : Expr) : MetaM (String × Bool) := do
  let e := stripVal e
  if let .const c _ := e.getAppFn then
    let m := ccDiagramLabels.getState (← getEnv)
    if let some l := m.find? c then
      return (l, false)
    -- `cc_diagram_labels` registers names before the definitions exist,
    -- possibly namespace-less: match by suffix
    if let some (_, l) := m.toList.find? fun (n, _) => n.isSuffixOf c then
      return (l, false)
    -- a bare constant: its short name (pretty-printing would add `@`)
    if e.isConst then
      if let .str _ short := c then
        return (short, false)
  let s ← ppShort e
  return (s, s.contains ' ')

/-- First sentence of the head constant's docstring, markdown-stripped —
the narration attached to a box as its tooltip. -/
private def descrFor (e : Expr) : MetaM (Option String) := do
  let .const c _ := (stripVal e).getAppFn | return none
  let some doc ← findDocString? (← getEnv) c | return none
  let doc := doc.replace "**" "" |>.replace "*" "" |>.replace "`" "" |>.replace "\n" " "
  let s := match doc.splitOn ". " with
    | first :: _ :: _ => first ++ "."
    | _ => doc
  let s := s.trimAscii.toString
  return if s.isEmpty then none else some s

/-! ## The goal parser -/

private structure ConvApp where
  iface : String
  label : String
  pos : Array Nat
  chip : Bool
  /-- Query-budget filters (`⌈q⌉`) are converters but never simulators. -/
  filter : Bool := false
  descr : Option String := none
  /-- Produced by opening a definition. -/
  inner : Bool := false
  deriving Inhabited

/-- Split a working-monoid element into converters: products factor
(`π * π'`); anything else is one
converter chip. -/
private partial def convsOfMonoidElem (π : Expr) (p : SubExpr.Pos) :
    MetaM (Array ConvApp) := do
  if let some args := matchApp? π ``HMul.hMul 6 then
    let l ← convsOfMonoidElem args[4]! (argPos p 6 4)
    let r ← convsOfMonoidElem args[5]! (argPos p 6 5)
    return l ++ r
  let (l, chip) ← labelFor π
  return #[{ iface := "", label := l, pos := p.toArray, chip := chip
             descr := ← descrFor π }]

/-- Peel converter attachments off a resource term, outermost first. -/
private partial def peelConvs (e : Expr) (p : SubExpr.Pos) :
    MetaM (Array ConvApp × Expr × SubExpr.Pos) := do
  -- Semantic rules are supplied by the owning adapter.
  if let some role ← declRole? e then
    let args := e.getAppArgs
    match role with
    | .application cf rf =>
      if let some (ci, cexp) := argFromEnd? args cf then
        if let some (ri, resource) := argFromEnd? args rf then
          let cpos := argPos p args.size ci
          let (label, chip) ← labelFor cexp
          let c : ConvApp :=
            { iface := ""
              label := label
              chip := chip
              pos := cpos.toArray
              descr := ← descrFor cexp }
          let (cs, core, corePos) ← peelConvs resource (argPos p args.size ri)
          return (#[c] ++ cs, core, corePos)
    | .attachment inf cf rf =>
      if let some (_, iface) := argFromEnd? args inf then
        if let some (ci, converter) := argFromEnd? args cf then
          if let some (ri, resource) := argFromEnd? args rf then
            let labelI ← ppIface iface
            let (label, chip) ← labelFor converter
            let c : ConvApp :=
              { iface := labelI
                label := label
                chip := chip
                pos := (argPos p args.size ci).toArray
                descr := ← descrFor converter }
            let (cs, core, corePos) ← peelConvs resource (argPos p args.size ri)
            return (#[c] ++ cs, core, corePos)
    | .transparent tf =>
      if let some (ti, target) := argFromEnd? args tf then
        return ← peelConvs target (argPos p args.size ti)
    | _ => pure ()
  -- π • R : monoid element acting on a resource or specification
  let smul? :=
    if let some args := matchApp? e ``HSMul.hSMul 6 then
      some (args[4]!, argPos p 6 4, args[5]!, argPos p 6 5)
    else if let some args := matchApp? e nSMul 5 then
      some (args[3]!, argPos p 5 3, args[4]!, argPos p 5 4)
    else none
  if let some (π, πp, r, rp) := smul? then
    let cs ← convsOfMonoidElem π πp
    let (cs', core, cp) ← peelConvs r rp
    return (cs ++ cs', core, cp)
  return (#[], e, p)

/-- Flatten a resource core into the center column: parallel compositions
stack, everything else is one element (chip when unrecognized). -/
private partial def parseCenter (e : Expr) (p : SubExpr.Pos) : MetaM (Array Elem) := do
  if let some role ← declRole? e then
    let args := e.getAppArgs
    match role with
    | .parallel lf rf =>
      if let some (li, left) := argFromEnd? args lf then
        if let some (ri, right) := argFromEnd? args rf then
          return (← parseCenter left (argPos p args.size li)) ++
            (← parseCenter right (argPos p args.size ri))
    | .game sf ef =>
      if let some (si, system) := argFromEnd? args sf then
        if let some (_, event) := argFromEnd? args ef then
          let nodes ← parseCenter system (argPos p args.size si)
          let (label, _) ← labelFor event
          return nodes.map fun el =>
            { el with
              mbo := true
              descr := match el.descr with
                | some d => some d
                | none => some ("MBO: " ++ label) }
    | .transparent tf =>
      if let some (ti, target) := argFromEnd? args tf then
        return ← parseCenter target (argPos p args.size ti)
    | _ => pure ()
  -- fTransform f seed : a sampled family is one observable system, not a
  -- parallel composition of the family and its distribution.  The seed is
  -- implementation/probability structure and has no external interface.
  if let some (args, n) := matchLast2? e nFTransform then
    let famExpr := args[n-2]!
    let famKey := match famExpr with
      | .lam _ _ b _ => b.getAppFn
      | e' => e'
    let (fl, _) ← labelFor famKey
    let fEl : Elem := { label := fl, kind := .chip, descr := ← descrFor famKey }
    return #[fEl]
  let e' := stripVal e
  let (l, chip) ← labelFor e'
  return #[{ label := l, kind := if chip then .chip else .res, pos := p.toArray
             descr := ← descrFor e' }]

/-- Relaxations peeled off a specification term. -/
private structure Relaxed where
  eps : Array String := #[]
  /-- `∗`-slots: interface label (`""` when unknown) and position. -/
  stars : Array (String × Array Nat) := #[]

/-- Strip `Singleton.singleton` and applied scalar relaxations off a
specification-level term. -/
private partial def peelSpec (e : Expr) (p : SubExpr.Pos) (acc : Relaxed) :
    MetaM (Expr × SubExpr.Pos × Relaxed) := do
  if let some args := matchApp? e ``Singleton.singleton 4 then
    return ← peelSpec args[3]! (argPos p 4 3) acc
  if let some args := matchApp? e nRelaxFun 3 then
    let relax := args[1]!
    let relaxPos := argPos p 3 1
    let inner := args[2]!
    let innerPos := argPos p 3 2
    if let some rargs := matchApp? relax nEpsilonRelaxation 3 then
      let ε ← ppShort rargs[2]!
      return ← peelSpec inner innerPos { acc with eps := acc.eps.push ε }
    -- unknown relaxation: keep it visible as a `∗`-slot named after it
    let (l, _) ← labelFor relax
    return ← peelSpec inner innerPos
      { acc with stars := acc.stars.push (l, relaxPos.toArray) }
  return (e, p, acc)

/-- Systems are connections: recursively open a defined system into its
connection structure — converter applications peel off, and the core
keeps unfolding while doing so exposes further structure.  Stops at
atoms (unfoldings with no converters and a single-part center). -/
private partial def autoPeel (e : Expr) (p : SubExpr.Pos) (fuel : Nat := 3) :
    MetaM (Array ConvApp × Expr × SubExpr.Pos × Bool) := do
  if fuel == 0 then return (#[], e, p, false)
  unless e.getAppFn.isConst do return (#[], e, p, false)
  let u? ← try Meta.unfoldDefinition? e catch _ => pure none
  let some u := u? | return (#[], e, p, false)
  let (cs, core, cp) ← peelConvs u p
  if cs.isEmpty then
    -- no converter surfaced: accept only a multi-part center (seed/family)
    let ce ← parseCenter core cp
    if ce.size ≥ 2 then return (#[], core, cp, true)
    return (#[], e, p, false)
  let (cs', core', cp', _) ← autoPeel core cp (fuel - 1)
  return (cs ++ cs', core', cp', true)

/-- Positions (goal paths) the user has shift-click selected — leaves at
these positions are drawn expanded (definition unfolded one level). -/
private def posSelected (sel : Array (Array Nat)) (p : SubExpr.Pos) : Bool :=
  let pa := p.toArray
  sel.any fun s =>
    s == pa || (s.size > pa.size && (List.range pa.size).all fun i => s[i]! == pa[i]!)

/-- Group converters into interfaces (chains, serially along each
interface's wire, distinguisher side first).  With `simFirst` (ideal
side of a distance judgment), a single non-filter converter is the
simulator; `∗`-slots become adversarial simulator interfaces. -/
private def groupIfaces (convs : Array ConvApp)
    (stars : Array (String × Array Nat)) (advIfaces : Array String)
    (simFirst : Bool) : Array Iface := Id.run do
  let simIdx? : Option Nat :=
    if simFirst && stars.isEmpty then
      match (List.range convs.size).filter (fun i => !(convs[i]!).filter) with
      | [i] => some i
      | _ => none
    else none
  let mut ifaces : Array Iface := #[]
  for i in [0:convs.size] do
    let c := convs[i]!
    let isSim := simIdx? == some i
    let el : Elem :=
      { label := c.label
        kind := if isSim then .sim else if c.chip then .chip else .conv
        pos := c.pos, descr := c.descr, inner := c.inner }
    match ifaces.findIdx? (·.label == c.iface) with
    | some j =>
      ifaces := ifaces.modify j (fun f =>
        { f with chain := f.chain.push el, adv := f.adv || isSim })
    | none =>
      let fresh : Iface :=
        { label := c.iface, chain := #[el]
          adv := isSim || (advIfaces.contains c.iface && !c.iface.isEmpty) }
      ifaces := ifaces.push fresh
  for (z, zp) in stars do
    let star : Elem := { label := "∗", kind := .sim, pos := zp }
    ifaces := ifaces.push { label := z, adv := true, chain := #[star] }
  return ifaces

/-- Both sides of a judgment display the same external port set.  Named ports
are mirrored by name.  A sole anonymous AC port is mirrored positionally; this
is distinct from inventing a second port and keeps one-interface construction
judgments aligned even when their abstract alphabets are unavailable. -/
private def mirrorIfaces (sys other : SystemView) : SystemView := Id.run do
  let mut sys := sys
  if sys.ifaces.isEmpty && other.ifaces.size == 1 && other.ifaces[0]!.label.isEmpty then
    let f := other.ifaces[0]!
    sys := { sys with ifaces := #[{ label := "", adv := f.adv }] }
  for f in other.ifaces do
    if !f.label.isEmpty && sys.ifaces.all (·.label != f.label) then
      sys := { sys with ifaces := sys.ifaces.push { label := f.label, adv := f.adv } }
  return sys

/-- A converter occurring at the same interface on both sides of a distance is
the common converter context, not an ideal-world simulator.  `simFirst` is a
useful fallback for genuinely unmatched ideal-side converters, but without
this reconciliation it incorrectly turns examples such as
`CBC 𝕋` versus `CBC 𝔽` into a vertical simulator attachment. -/
private def reconcileSharedConverters (real ideal : SystemView) : SystemView × SystemView := Id.run do
  let sharedAt (f : Iface) : Array String :=
    match real.ifaces.find? (fun g => g.label == f.label) with
    | some g => f.chain.filterMap fun e =>
        if g.chain.any (fun x => x.label == e.label) then some e.label else none
    | none => #[]
  let ideal := { ideal with ifaces := ideal.ifaces.map fun f =>
    let shared := sharedAt f
    if shared.isEmpty then f
    else
      { f with
        adv := false
        chain := f.chain.map fun e =>
          if shared.contains e.label && e.kind == .sim then { e with kind := .conv } else e } }
  return (real, ideal)

/-- Parse one side of a judgment into a `SystemView` plus relaxation
data.  Composite cores auto-expand into their connection structure;
shift-clicked leaves force one more definitional level. -/
private def parseSide (e : Expr) (p : SubExpr.Pos) (simFirst : Bool)
    (advIfaces : Array String := #[]) (sel : Array (Array Nat) := #[]) :
    MetaM (SystemView × Relaxed) := do
  let (e, p, relaxed) ← peelSpec e p {}
  let (convs, core, corePos) ← peelConvs e p
  let (core, corePos, relaxed') ← peelSpec core corePos relaxed
  let (convs', core, corePos) ← peelConvs core corePos
  let mut core := core
  let mut corePos := corePos
  let (origLabel, _) ← labelFor core
  let origDescr? ← descrFor core
  -- systems are connections: expose the composite's structure by default
  let mut unfolded? : Option String := none
  let mut frameLabel? : Option String := none
  let mut innerConvs : Array ConvApp := #[]
  let (acs, core2, cp2, opened) ← autoPeel core corePos
  if opened then
    innerConvs := acs.map fun c => { c with inner := true }
    core := core2
    corePos := cp2
    frameLabel? := some origLabel
  else if posSelected sel corePos && core.getAppFn.isConst then
    -- shift-click forces one more level even without structure
    if let some u ← try Meta.unfoldDefinition? core catch _ => pure none then
      unfolded? := some s!"{origLabel}  ≐  definition, one level"
      frameLabel? := some origLabel
      let (cs, u', up) ← peelConvs u corePos
      innerConvs := cs.map fun c => { c with inner := true }
      core := u'
      corePos := up
  let center ← parseCenter core corePos
  let outerConvs := convs ++ convs'
  let allConvs := outerConvs ++ innerConvs
  let mut ifaces := groupIfaces allConvs relaxed'.stars advIfaces simFirst
  return ({ center, ifaces, unfolded?
            frameLabel?
            frameDescr? := if frameLabel?.isSome then origDescr? else none }, relaxed')

/-- Construction judgments `R —[π]→ S` / `Constructs π R S`. -/
private def mkConstruction (r : Expr) (rp : SubExpr.Pos) (π : Expr) (πp : SubExpr.Pos)
    (s : Expr) (sp : SubExpr.Pos) (sel : Array (Array Nat) := #[]) :
    MetaM (Option JudgmentView) := do
  let (rSpec, rPos, rrel) ← peelSpec r rp {}
  let (convs, core, corePos) ← peelConvs rSpec rPos
  let πConvs ← convsOfMonoidElem π πp
  let center ← parseCenter core corePos
  let real : SystemView :=
    { center, ifaces := groupIfaces (πConvs ++ convs) rrel.stars #[] false }
  let (ideal, irel) ← parseSide s sp (simFirst := false) (sel := sel)
  let eps := rrel.eps ++ irel.eps
  return some
    { real := mirrorIfaces real ideal, ideal? := some (mirrorIfaces ideal real)
      rel := "⊑", eps? := if eps.isEmpty then none else some (" + ".intercalate eps.toList) }

/-- A symmetric two-sided distance-style judgment. -/
private def mkDistance (l : Expr) (lp : SubExpr.Pos) (r : Expr) (rp : SubExpr.Pos)
    (rel : String) (ε? : Option String) (note? : Option String := none)
    (sel : Array (Array Nat) := #[]) : MetaM (Option JudgmentView) := do
  let (ideal, irel) ← parseSide r rp (simFirst := true) (sel := sel)
  let advIfaces := (ideal.ifaces.filter (·.adv)).map (·.label)
  let (real, rrel) ← parseSide l lp (simFirst := false) advIfaces (sel := sel)
  let (real, ideal) := reconcileSharedConverters real ideal
  let eps := rrel.eps ++ irel.eps ++ (match ε? with | some ε => #[ε] | none => #[])
  return some
    { real := mirrorIfaces real ideal, ideal? := some (mirrorIfaces ideal real)
      rel, eps? := if eps.isEmpty then none else some (" + ".intercalate eps.toList), note? }

/-- Strip outer `↑`-coercions (`NNReal.toReal`, `ENNReal.toReal`). -/
private partial def stripCoe (e : Expr) (p : SubExpr.Pos) : Expr × SubExpr.Pos :=
  if e.isAppOfArity nNNRealToReal 1 || e.isAppOfArity nENNRealToReal 1 then
    stripCoe e.appArg! p.pushAppArg
  else (e, p)

/-- Parse an advantage expression into cards: sums of two-sided
distances, one-sided win probabilities, event masses, and numeric
summands — the vocabulary of calculation-proof steps. -/
private partial def parseAdv (e : Expr) (p : SubExpr.Pos)
    (sel : Array (Array Nat) := #[]) : MetaM (Array AdvCard) := do
  let (e, p) := stripCoe e p
  if let some args := matchApp? e ``HAdd.hAdd 6 then
    return (← parseAdv args[4]! (argPos p 6 4) sel) ++ (← parseAdv args[5]! (argPos p 6 5) sel)
  if let some role ← declRole? e then
    let args := e.getAppArgs
    match role with
    | .distance lf rf sym =>
      if let some (li, left) := argFromEnd? args lf then
        if let some (ri, right) := argFromEnd? args rf then
          let lp := argPos p args.size li
          let rp := argPos p args.size ri
          let (ideal, _) ← parseSide right rp (simFirst := true) (sel := sel)
          let advIfaces := (ideal.ifaces.filter (·.adv)).map (·.label)
          let (real, _) ← parseSide left lp (simFirst := false) advIfaces (sel := sel)
          let (real, ideal) := reconcileSharedConverters real ideal
          return #[.dist sym (mirrorIfaces real ideal) (mirrorIfaces ideal real)]
    | .winning sf sym =>
      if let some (si, system) := argFromEnd? args sf then
        let (view, _) ← parseSide system (argPos p args.size si)
          (simFirst := false) (sel := sel)
        return #[.win sym view]
    | _ => pure ()
  let dist? : Option (String × Expr × SubExpr.Pos × Expr × SubExpr.Pos) :=
    if let some da := matchApp? e nMathlibEdist 4 then
      some ("d", da[2]!, argPos p 4 2, da[3]!, argPos p 4 3)
    else if let some (da, n) := matchLast2? e nStatDist then
      some ("δ", da[n-2]!, argPos p n (n-2), da[n-1]!, argPos p n (n-1))
    else none
  if let some (sym, l, lp, r, rp) := dist? then
    let (ideal, _) ← parseSide r rp (simFirst := true) (sel := sel)
    let advIfaces := (ideal.ifaces.filter (·.adv)).map (·.label)
    let (real, _) ← parseSide l lp (simFirst := false) advIfaces (sel := sel)
    let (real, ideal) := reconcileSharedConverters real ideal
    return #[.dist sym (mirrorIfaces real ideal) (mirrorIfaces ideal real)]
  if let some (da, n) := matchLast2? e nMass then
    let (d, _) ← parseSide da[n-2]! (argPos p n (n-2)) (simFirst := false) (sel := sel)
    let ev ← ppShort da[n-1]!
    return #[.mass d ev]
  return #[.num (← ppShort e) p.toArray]

private def AdvCard.isNum : AdvCard → Bool
  | .num _ _ => true
  | _ => false

/-- `lhs ⟨rel⟩ rhs` between advantage expressions: full-size rendering
when a single card is bounded by a numeric expression, the card-bridge
row otherwise (`Δ(…) ≤ Δ(…) + Δ(…)` calculation steps). -/
private def mkAdvComparison (l : Expr) (lp : SubExpr.Pos) (r : Expr) (rp : SubExpr.Pos)
    (rel : String) (sel : Array (Array Nat) := #[]) : MetaM (Option JudgmentView) := do
  let L ← parseAdv l lp sel
  let R ← parseAdv r rp sel
  if L.all (·.isNum) && R.all (·.isNum) then return none
  let epsOf (cs : Array AdvCard) : String :=
    " + ".intercalate (cs.toList.map fun c => match c with | .num s _ => s | _ => "…")
  if R.all (·.isNum) && L.size == 1 then
    match L[0]! with
    | .dist _ a b =>
      return some { real := a, ideal? := some b, rel := "≈", eps? := some (epsOf R)
                    epsPos? := some rp.toArray }
    | .win sym sys =>
      return some { real := sys, rel := s!"{sym} {rel}", eps? := some (epsOf R)
                    epsPos? := some rp.toArray
                    note? := some "maximal winning probability of the game" }
    | .mass d ev =>
      return some { real := d, rel := s!"mass {rel}", eps? := some (epsOf R)
                    epsPos? := some rp.toArray
                    note? := some s!"probability of the event  {ev}" }
    | .num _ _ => return none
  return some { rel, bridge? := some (L, R) }

/-- Recognize a CC judgment in `e` (a goal type) and produce the view.
`none` when `e` is not a CC statement. -/
partial def parseJudgment? (e : Expr) (p : SubExpr.Pos := .root)
    (sel : Array (Array Nat) := #[]) : MetaM (Option JudgmentView) := do
  let e ← instantiateMVars e
  -- ∃ σE, body — the packaged `security` field's shape
  if let some args := matchApp? e ``Exists 2 then
    if let .lam n ty body bi := args[1]! then
      let inner ← withLocalDecl n bi ty fun fv =>
        parseJudgment? (body.instantiate1 fv) ((argPos p 2 1).pushBindingBody) sel
      if let some jv := inner then
        return some { jv with note? := some s!"∃ {n} — simulator witness pending" }
    return none
  if let some role ← declRole? e then
    let args := e.getAppArgs
    match role with
    | .construction rf pf inf =>
      if let some (ri, real) := argFromEnd? args rf then
        if let some (pi, converter) := argFromEnd? args pf then
          if let some (ii, ideal) := argFromEnd? args inf then
            return ← mkConstruction real (argPos p args.size ri)
              converter (argPos p args.size pi) ideal (argPos p args.size ii) sel
    | .conditional lf rf =>
      if let some (li, left) := argFromEnd? args lf then
        if let some (ri, right) := argFromEnd? args rf then
          return ← mkDistance left (argPos p args.size li) right (argPos p args.size ri)
            "|≡" none (some "conditionally equivalent given no MBO win") sel
    | _ => pure ()
  -- advantage-expression comparisons: `d … ≤ ε`, `Δ(…) ≤ Δ(…) + …`
  if let some args := matchApp? e ``LE.le 4 then
    return ← mkAdvComparison args[2]! (argPos p 4 2) args[3]! (argPos p 4 3) "≤" sel
  -- unfolded form: `π • R ⊆ S`
  if let some args := matchApp? e ``HasSubset.Subset 4 then
    let (real, rrel) ← parseSide args[2]! (argPos p 4 2) (simFirst := false) (sel := sel)
    let (ideal, irel) ← parseSide args[3]! (argPos p 4 3) (simFirst := false) (sel := sel)
    let touched (s : SystemView) :=
      s.ifaces.any (!·.chain.isEmpty) || s.center.size > 1
    if !(touched real || touched ideal) then
      return none  -- an ordinary set inclusion, not a CC statement
    let eps := rrel.eps ++ irel.eps
    return some
      { real := mirrorIfaces real ideal, ideal? := some (mirrorIfaces ideal real)
        rel := "⊆", eps? := if eps.isEmpty then none else some (" + ".intercalate eps.toList) }
  -- equalities: advantage expressions first, then resource terms
  if let some args := matchApp? e ``Eq 3 then
    if let some jv ← mkAdvComparison args[1]! (argPos p 3 1) args[2]! (argPos p 3 2) "=" sel then
      return some jv
    let (real, _) ← parseSide args[1]! (argPos p 3 1) (simFirst := false) (sel := sel)
    let (ideal, _) ← parseSide args[2]! (argPos p 3 2) (simFirst := false) (sel := sel)
    let touched (s : SystemView) :=
      s.ifaces.any (!·.chain.isEmpty) || s.center.size > 1 || s.frameLabel?.isSome
    if !(touched real || touched ideal) then return none
    return some
      { real := mirrorIfaces real ideal, ideal? := some (mirrorIfaces ideal real), rel := "=" }
  return none

/-! ## Interactive code lookups

Boxes and bounds render as the infoview's own interactive code: the RPC
builds, per judgment, a table from goal positions to `InteractiveCode`
components (hover for types, click to inspect). -/

/-- Position-indexed interactive code, built by the RPC per proof state. -/
abbrev Codes := Array (Array Nat × Html)

private def codeFor? (codes : Codes) (pos : Array Nat) : Option Html :=
  if pos.isEmpty then none else (codes.find? (·.1 == pos)).map (·.2)

/-- All goal positions a judgment draws. -/
private def collectPositions (jv : JudgmentView) : Array (Array Nat) := Id.run do
  let ofSys (s : SystemView) : Array (Array Nat) := Id.run do
    let mut ps := s.center.map (·.pos)
    for f in s.ifaces do
      ps := ps ++ f.chain.map (·.pos)
    return ps
  let mut ps := ofSys jv.real
  if let some i := jv.ideal? then ps := ps ++ ofSys i
  if let some (l, r) := jv.bridge? then
    for c in l ++ r do
      match c with
      | .dist _ a b => ps := ps ++ ofSys a ++ ofSys b
      | .win _ a | .mass a _ => ps := ps ++ ofSys a
      | .num _ p => ps := ps.push p
  if let some p := jv.epsPos? then ps := ps.push p
  return (ps.filter (!·.isEmpty)).foldl (init := #[]) fun acc p =>
    if acc.contains p then acc else acc.push p

/-- Build the interactive-code table for a judgment against its root
goal expression.  Positions that fail to resolve are skipped (their
boxes fall back to plain labels). -/
def buildCodes (jv : JudgmentView) (root : Expr) : MetaM Codes := do
  let mut codes : Codes := #[]
  for pos in collectPositions jv do
    try
      let html ← Meta.viewSubexpr
        (fun _ sub => do
          let sub := stripVal sub
          if sub.hasLooseBVars then
            throwError "open term"
          let fmt ← Widget.ppExprTagged sub
          return Html.ofComponent InteractiveCode { fmt } #[])
        (SubExpr.Pos.ofArray pos) root
      codes := codes.push (pos, html)
    catch _ => pure ()
  return codes

/-! ## Rendering

One engine for any interface count: 1 interface → a chain (query/answer
arrows at the left, converters in series, then the core); 2 → left and
right; adversarial and further interfaces hang below.  Natural-pixel
sizing; labels are interactive code in `foreignObject`s when available. -/

private def fmtF (f : Float) : String :=
  let neg := f < 0
  let a := if neg then -f else f
  let t := (a * 2).round / 2
  let n := t.toUInt64.toNat
  let body := if t == Float.ofNat n then toString n else s!"{n}.5"
  if neg then "-" ++ body else body

private def sattr (k v : String) : String × Json := (k, Json.str v)

private def svgLine (x1 y1 x2 y2 : Float) : Html :=
  .element "line" #[sattr "x1" (fmtF x1), sattr "y1" (fmtF y1),
    sattr "x2" (fmtF x2), sattr "y2" (fmtF y2), sattr "className" "wire"] #[]

private def svgRect (x y w h : Float) (cls : String) : Html :=
  .element "rect" #[sattr "x" (fmtF x), sattr "y" (fmtF y),
    sattr "width" (fmtF w), sattr "height" (fmtF h), sattr "rx" "3",
    sattr "className" cls] #[]

private def svgText (x y : Float) (cls s : String) (fs : String)
    (anchor : String := "middle") : Html :=
  .element "text" #[sattr "x" (fmtF x), sattr "y" (fmtF y),
    sattr "className" cls, sattr "textAnchor" anchor,
    ("style", Json.mkObj [("fontSize", Json.str fs)])] #[.text s]

private def svgArrowHead (x y : Float) (toRight : Bool) : Html :=
  let d : Float := if toRight then -6 else 6
  .element "polygon"
    #[sattr "points" (fmtF (x + d) ++ "," ++ fmtF (y - 3.5) ++ " " ++
        fmtF x ++ "," ++ fmtF y ++ " " ++ fmtF (x + d) ++ "," ++ fmtF (y + 3.5)),
      sattr "className" "ah"] #[]

/-- A monotone-bad-event is an observable output, not decoration: draw a
dedicated right-going lane labelled `Aᵢ`, as in Maurer's game diagrams. -/
private def svgMboOutput (x y : Float) : Array Html :=
  #[svgLine x y (x + 34) y,
    svgArrowHead (x + 34) y true,
    svgText (x + 17) (y - 7) "mboout" "Aᵢ" "11px"]

/-- Box + label classes for an element's kind. -/
private def boxCls (kind : BoxKind) : String × String :=
  match kind with
  | .res => ("res", "rlb")
  | .conv => ("cvt c-cvt", "t-cvt lblx")
  | .sim => ("cvt c-sim", "t-sim lblx")
  | .chip => ("chip", "chiptx")

private def selected (sel : Array (Array Nat)) (pos : Array Nat) : Bool :=
  !pos.isEmpty && sel.any fun s =>
    let n := min pos.size s.size
    n > 0 && (List.range n).all fun i => pos[i]! == s[i]!

/-- A drawable box: geometry computed, content rendered as interactive
code when available. -/
private def drawBox (el : Elem) (x y w h : Float) (sel : Array (Array Nat))
    (codes : Codes) (fs : String) : Html := Id.run do
  let (bc, tc) := boxCls el.kind
  let mut g : Array Html := #[]
  let tip := match el.descr with
    | some d => el.label ++ "\n\n" ++ d
    | none => el.label
  if !tip.isEmpty then
    g := g.push <| .element "title" #[] #[.text tip]
  g := g.push (svgRect x y w h bc)
  match codeFor? codes el.pos with
  | some code =>
    -- SVG `switch` is real progressive enhancement: clients supporting
    -- XHTML foreign objects get selectable Lean code; other SVG clients
    -- select the following plain-text label instead of showing an empty box.
    g := g.push <| .element "switch" #[]
      #[.element "foreignObject"
        #[sattr "x" (fmtF (x + 2)), sattr "y" (fmtF y),
          sattr "width" (fmtF (w - 4)), sattr "height" (fmtF h),
          sattr "requiredExtensions" "http://www.w3.org/1999/xhtml"]
        #[.element "div" #[sattr "className" ("fo " ++ tc)] #[code]],
        svgText (x + w/2) (y + h/2 + 4) tc el.label fs]
  | none =>
    g := g.push (svgText (x + w/2) (y + h/2 + 4) tc el.label fs)
  if el.mbo then
    g := g ++ svgMboOutput (x + w) (y + h/2)
  return .element "g"
    #[sattr "className" (if selected sel el.pos then "ccg sel" else "ccg")] g

/-- Render one system.  Interfaces: first honest → left, second → right,
the rest and all adversarial ones → below. -/
private def sysSvg (sys : SystemView) (sel : Array (Array Nat)) (codes : Codes)
    (compact : Bool := false) : Html := Id.run do
  let bh : Float := if compact then 26 else 34         -- converter box height
  let coreH : Float := if compact then 28 else 36      -- core row height
  let gap : Float := 12                                 -- wire length
  let fs := if compact then "10px" else "11.5px"
  let wOf (el : Elem) (isCore : Bool) : Float :=
    -- Italic math labels have wider side bearings than monospace estimates;
    -- 44px keeps short names such as `CBC` off the box stroke while the
    -- Content-based width handles longer converter and simulator names.
    let base := Float.ofNat el.label.length * 7.2 + 16
    if isCore then min 240 (max 64 base) else min 136 (max 44 base)
  let center := if sys.center.isEmpty then
    #[({ label := "?", kind := .chip } : Elem)] else sys.center
  let honest := sys.ifaces.filter (!·.adv)
  let advs := sys.ifaces.filter (·.adv)
  let left? := honest[0]?
  let right? := honest[1]?
  let bottoms := (honest.toList.drop 2).toArray ++ advs
  let framed := sys.frameLabel?.isSome
  let topPad : Float := if framed then 20 else 8
  -- core stack geometry
  let rowGap : Float := 8
  let stackH := Float.ofNat center.size * coreH
    + Float.ofNat (center.size - 1) * rowGap
  let midY := topPad + max (stackH / 2) (bh / 2 + 2)
  let mut kids : Array Html := #[]
  let mut frameX0 : Option Float := none
  let mut x : Float := 6
  -- A typed anonymous system interface has query/answer arrows;
  -- abstract named or untyped ports are undirected wires.
  match left? with
  | some f =>
    if f.label.isEmpty && (f.inType.isSome || f.outType.isSome) then
      kids := kids.push (svgLine x (midY - 7) (x + 30) (midY - 7))
      kids := kids.push (svgArrowHead (x + 30) (midY - 7) true)
      kids := kids.push (svgLine (x + 30) (midY + 7) x (midY + 7))
      kids := kids.push (svgArrowHead x (midY + 7) false)
      if let some t := f.inType then
        kids := kids.push (svgText x (midY - 13) "wt" t "9px" (anchor := "start"))
      if let some t := f.outType then
        kids := kids.push (svgText x (midY + 19) "wt" t "9px" (anchor := "start"))
      x := x + 34
    else
      if !f.label.isEmpty then
        kids := kids.push (svgText (x + 2) (midY - 6) "lbl" f.label "13px" (anchor := "start"))
      kids := kids.push (svgLine x midY (x + 18) midY)
      x := x + 18
    for el in f.chain do
      if el.inner && frameX0.isNone then
        frameX0 := some (x + gap - 5)
      kids := kids.push (svgLine x midY (x + gap) midY)
      let w := wOf el false
      kids := kids.push (drawBox el (x + gap) (midY - bh/2) w bh sel codes fs)
      x := x + gap + w
  | none =>
    kids := kids.push (svgLine x midY (x + 16) midY)
    x := x + 16
  -- the core column
  kids := kids.push (svgLine x midY (x + gap) midY)
  let cx := x + gap
  if framed && frameX0.isNone then
    frameX0 := some (cx - 6)
  let colW := (center.map (wOf · true)).foldl max 64
  -- stacked center (parallel composition): dashed grouping, so the
  -- external interfaces meet a shared bus that visibly reaches every
  -- component.  Merely stacking boxes inside a frame makes composition look
  -- disconnected and lets the main wire float between rows.
  if center.size > 1 then
    if !framed then
      kids := kids.push <| .element "rect"
        #[sattr "x" (fmtF (cx - 6)), sattr "y" (fmtF (midY - stackH/2 - 6)),
          sattr "width" (fmtF (colW + 12)), sattr "height" (fmtF (stackH + 12)),
          sattr "rx" "5", sattr "className" "brk"] #[]
    let firstY := midY - stackH/2 + coreH/2
    let lastY := firstY + Float.ofNat (center.size - 1) * (coreH + rowGap)
    kids := kids.push (svgLine cx firstY cx lastY)
    kids := kids.push (svgLine (cx + colW) firstY (cx + colW) lastY)
    let mut branchY := firstY
    for el in center do
      let w := wOf el true
      let bx0 := cx + (colW - w)/2
      kids := kids.push (svgLine cx branchY bx0 branchY)
      kids := kids.push (svgLine (bx0 + w) branchY (cx + colW) branchY)
      branchY := branchY + coreH + rowGap
  let mut cy := midY - stackH / 2
  for el in center do
    let w := wOf el true
    kids := kids.push (drawBox el (cx + (colW - w)/2) cy w coreH sel codes fs)
    cy := cy + coreH + rowGap
  x := cx + colW
  let mut frameX1 : Float := x + 6
  -- right interface (chain drawn inside-out)
  match right? with
  | some f =>
    for el in f.chain.reverse do
      kids := kids.push (svgLine x midY (x + gap) midY)
      let w := wOf el false
      kids := kids.push (drawBox el (x + gap) (midY - bh/2) w bh sel codes fs)
      if el.inner then frameX1 := x + gap + w + 5
      x := x + gap + w
    kids := kids.push (svgLine x midY (x + 18) midY)
    if !f.label.isEmpty then
      kids := kids.push (svgText (x + 16) (midY - 6) "lbl" f.label "13px" (anchor := "end"))
    x := x + 20
  | none =>
    if left?.any (·.label.isEmpty) then
      -- single-interface system: nothing on the right
      x := x + 4
    else
      kids := kids.push (svgLine x midY (x + 16) midY)
      x := x + 18
  -- bottom interfaces
  let stackBottom := midY + max (stackH / 2) (bh / 2)
  let mut maxY := stackBottom
  let mut minX : Float := 0
  let hasMbo := sys.frameMbo || center.any (·.mbo)
  let mut maxX : Float := x + (if hasMbo then 42 else 4)
  let k := bottoms.size
  -- Several lower ports share one interface trunk at the resource boundary;
  -- without it, every off-center vertical wire begins in empty space.
  if k > 1 then
    let firstBx := cx + colW/2 - Float.ofNat (k-1) / 2 * 146
    let lastBx := cx + colW/2 + Float.ofNat (k-1) / 2 * 146
    kids := kids.push (svgLine firstBx stackBottom lastBx stackBottom)
  for j in [0:k] do
    let f := bottoms[j]!
    -- Converter boxes can be 130px wide.  A 146px pitch leaves a full box
    -- plus an 8px gutter on either side, so lower ports never overlap.
    let bx := cx + colW/2 + (Float.ofNat j - Float.ofNat (k-1) / 2) * 146
    let widest := f.chain.foldl (fun acc el => max acc (wOf el false)) 0
    minX := min minX (bx - widest/2 - 8)
    maxX := max maxX (bx + widest/2 + 42) -- room for a right-anchored port label
    let mut by' := stackBottom
    kids := kids.push (svgLine bx by' bx (by' + 14))
    by' := by' + 14
    for el in f.chain do
      let w := wOf el false
      kids := kids.push (drawBox el (bx - w/2) by' w bh sel codes fs)
      by' := by' + bh
      kids := kids.push (svgLine bx by' bx (by' + 12))
      by' := by' + 12
    if f.chain.isEmpty then
      kids := kids.push (svgLine bx by' bx (by' + 14))
      by' := by' + 14
    if !f.label.isEmpty then
      kids := kids.push (svgText (bx + 6) (by' + 2) "lbl" f.label "13px" (anchor := "start"))
    maxY := max maxY (by' + 8)
  -- composite frame around the inner converters + core
  if framed then
    let fx0 := (frameX0.getD (cx - 6))
    let fy0 := topPad - 6
    let fy1 := stackBottom + 6
    kids := #[(.element "rect"
      #[sattr "x" (fmtF fx0), sattr "y" (fmtF fy0),
        sattr "width" (fmtF (frameX1 - fx0)), sattr "height" (fmtF (fy1 - fy0)),
        sattr "rx" "5", sattr "className" "brk"] #[] : Html)] ++ kids
    let mut g : Array Html := #[]
    if let some d := sys.frameDescr? then
      g := g.push <| .element "title" #[] #[.text d]
    g := g.push (svgText fx0 (fy0 - 4) "frl" (sys.frameLabel?.getD "") "10px"
      (anchor := "start"))
    if sys.frameMbo then
      g := g ++ svgMboOutput frameX1 (fy0 + 10)
    kids := kids.push (.element "g" #[sattr "className" "ccg"] g)
  let vbW := maxX - minX
  let vbH := max maxY (midY + bh/2) + (if left?.any (·.label.isEmpty) then 22 else 10)
  return .element "svg"
    #[sattr "viewBox" s!"{fmtF minX} 0 {fmtF vbW} {fmtF vbH}",
      sattr "width" (fmtF vbW), sattr "className" "ccsvg"] kids

/-- Render a view-model system as a standalone SVG `Html` tree.  This small
public seam is used by visual regression tooling; theorem-facing code normally
uses `renderJudgment`, which adds relations, bounds, notes, and cards. -/
def renderSystem (sys : SystemView) (sel : Array (Array Nat) := #[])
    (codes : Codes := #[]) (compact : Bool := false) : Html :=
  sysSvg sys sel codes compact

/-! ## Intrinsic component renderer

The user-facing renderer is DOM-first: resources, converters, labels, ports,
frames, and expressions are ordinary HTML components whose dimensions come
from their rendered content.  CSS connector primitives draw the straight
blackboard wires.  SVG remains available through `renderSystem` only for
specialized exports and non-rectilinear feedback overlays; proof-panel text
and box geometry are DOM-rendered. -/

private def domLabel (el : Elem) (codes : Codes) : Html :=
  match codeFor? codes el.pos with
  | some code => .element "span" #[sattr "className" "node-code"] #[code]
  | none => .element "span" #[sattr "className" "node-text"] #[.text el.label]

private def domBox (el : Elem) (sel : Array (Array Nat)) (codes : Codes) : Html :=
  let (bc, _) := boxCls el.kind
  let tip := match el.descr with
    | some d => el.label ++ "\n\n" ++ d
    | none => el.label
  .element "div"
    #[sattr "className" ("ccnode " ++ bc ++
        (if selected sel el.pos then " sel" else "")),
      sattr "title" tip]
    #[domLabel el codes]

private def hwire : Html := .element "span" #[sattr "className" "hwire"] #[]
private def vwire : Html := .element "span" #[sattr "className" "vwire"] #[]

private def domChain (els : Array Elem) (sel : Array (Array Nat)) (codes : Codes)
    (reverse : Bool := false) : Array Html := Id.run do
  let els := if reverse then els.reverse else els
  let mut out : Array Html := #[]
  for el in els do
    out := out.push hwire |>.push (domBox el sel codes)
  return out

private def domPort (f : Iface) (side : String) : Html :=
  if f.label.isEmpty && (f.inType.isSome || f.outType.isSome) then
    .element "div" #[sattr "className" ("typed-port " ++ side)]
      #[.element "div" #[sattr "className" "typed-lane lane-in"]
          (f.inType.map (fun t => #[.element "span" #[sattr "className" "port-type"] #[.text t]])
            |>.getD #[]),
        .element "div" #[sattr "className" "typed-lane lane-out"]
          (f.outType.map (fun t => #[.element "span" #[sattr "className" "port-type"] #[.text t]])
            |>.getD #[])]
  else
    .element "div" #[sattr "className" ("named-port " ++ side)]
      (if f.label.isEmpty then #[hwire]
       else #[.element "span" #[sattr "className" "port-name"] #[.text f.label], hwire])

private def domCores (center : Array Elem) (sel : Array (Array Nat)) (codes : Codes) : Html :=
  let center := if center.isEmpty then #[({ label := "?", kind := .chip } : Elem)] else center
  .element "div"
    #[sattr "className" ("core-stack" ++ if center.size > 1 then " parallel" else "")]
    (center.map (fun el => domBox el sel codes))

private def domBottomIface (f : Iface) (sel : Array (Array Nat)) (codes : Codes) : Html := Id.run do
  let mut kids : Array Html := #[vwire]
  for el in f.chain do
    kids := kids.push (domBox el sel codes) |>.push vwire
  if !f.label.isEmpty then
    kids := kids.push <| .element "span" #[sattr "className" "port-name"] #[.text f.label]
  return .element "div" #[sattr "className" ("bottom-iface" ++ if f.adv then " adversarial" else "")] kids

/-- Intrinsically-sized blackboard system component. -/
def renderSystemComponent (sys : SystemView) (sel : Array (Array Nat) := #[])
    (codes : Codes := #[]) (compact : Bool := false) : Html := Id.run do
  let honest := sys.ifaces.filter (!·.adv)
  let advs := sys.ifaces.filter (·.adv)
  let left? := honest[0]?
  let right? := honest[1]?
  let bottoms := (honest.toList.drop 2).toArray ++ advs
  let leftOuter := left?.map (fun f => f.chain.filter (!·.inner)) |>.getD #[]
  let leftInner := left?.map (fun f => f.chain.filter (·.inner)) |>.getD #[]
  let rightOuter := right?.map (fun f => f.chain.filter (!·.inner)) |>.getD #[]
  let rightInner := right?.map (fun f => f.chain.filter (·.inner)) |>.getD #[]
  let hasMbo := sys.frameMbo || sys.center.any (·.mbo)
  let mut row : Array Html := #[]
  match left? with
  | some f => row := row.push (domPort f "left")
  | none => row := row.push <| .element "span" #[sattr "className" "stub-port"] #[hwire]
  row := row ++ domChain leftOuter sel codes
  let innerRow : Array Html :=
    domChain leftInner sel codes ++ #[hwire, domCores sys.center sel codes] ++
      domChain rightInner sel codes (reverse := true)
  let center : Html := match sys.frameLabel? with
    | some label =>
      .element "div" #[sattr "className" "construction-frame"]
        #[.element "span" #[sattr "className" "frame-label"] #[.text label],
          .element "div" #[sattr "className" "frame-row"] innerRow]
    | none => .element "div" #[sattr "className" "frame-row"] innerRow
  row := row.push center
  row := row ++ domChain rightOuter sel codes (reverse := true)
  match right? with
  | some f => row := row.push (domPort f "right")
  | none => pure ()
  if hasMbo then
    row := row.push <| .element "div" #[sattr "className" "mbo-port"]
      #[hwire, .element "span" #[sattr "className" "mbo-label"] #[.text "Aᵢ"]]
  let mut body : Array Html :=
    #[.element "div" #[sattr "className" "system-row"] row]
  if !bottoms.isEmpty then
    body := body.push <| .element "div" #[sattr "className" "bottom-ports"]
      (bottoms.map (fun f => domBottomIface f sel codes))
  return .element "div"
    #[sattr "className" ("system-component" ++ if compact then " compact" else "")] body

/-- The diagram's CSS vocabulary — dark (VS Code) palette with the blue
converter / amber simulator accents, plus the light-theme twin. -/
def stylesheet : String := "
.ccw{margin-top:8px}
.ccw>summary{cursor:pointer;font:600 10px system-ui,sans-serif;letter-spacing:.12em;color:#8a8f98;text-transform:uppercase}
.ccw .bd{padding:6px 2px 4px;max-width:100%;overflow-x:auto;box-sizing:border-box}
.ccw .sect{font:600 10px system-ui,sans-serif;color:#6f7680;letter-spacing:.12em;margin:8px 0 2px}
.ccw svg{display:block;max-width:100%;height:auto}
/* Intrinsic blackboard components.  Text and boxes are DOM, never measured in Lean. */
.ccw .system-component{display:inline-flex;flex-direction:column;align-items:center;max-width:100%;padding:16px 4px 6px;box-sizing:border-box}
.ccw .system-row,.ccw .frame-row{display:flex;align-items:center;min-width:max-content}
.ccw .construction-frame{position:relative;border:1px dashed #5a5d63;border-radius:6px;padding:8px 7px}
.ccw .frame-label{position:absolute;left:4px;top:-15px;padding:0 3px;background:var(--vscode-editor-background,#1e1e1e);font:600 10px ui-monospace,Menlo,monospace;color:#8a8f98;letter-spacing:.08em;white-space:nowrap}
.ccw .ccnode{display:flex;align-items:center;justify-content:center;box-sizing:border-box;min-width:48px;min-height:34px;padding:7px 11px;border-radius:4px;white-space:nowrap;transition:border-color .15s,background .15s;cursor:default}
.ccw .ccnode.res{min-width:64px;background:#2b2d31;border:1.4px solid #bfc4cc;font:600 11.5px 'STIX Two Text','STIX Two Math',Georgia,serif;letter-spacing:.1em;color:#d6d9de}
.ccw .ccnode.cvt{background:#223047;border:1.4px solid #6ca7e8;color:#9cc7f5;font:italic 12px 'STIX Two Text','STIX Two Math',Georgia,serif}
.ccw .ccnode.c-sim{background:#3b2f22;border-color:#d8a35c;color:#eec489}
.ccw .ccnode.chip{background:#26282c;border:1px dashed #5a5d63;font:10px ui-monospace,Menlo,monospace;color:#9aa1ab}
.ccw .ccnode:hover{outline:2px solid rgba(108,167,232,.28);outline-offset:2px}
.ccw .ccnode.sel{outline:2px solid #6ca7e8;outline-offset:1px}
.ccw .node-code{display:inline-flex;align-items:center;white-space:nowrap}
.ccw .node-code>*{white-space:nowrap}
.ccw .node-text{white-space:nowrap}
.ccw .hwire{display:block;flex:0 0 18px;width:18px;height:0;border-top:1.4px solid #bfc4cc}
.ccw .vwire{display:block;flex:0 0 14px;width:0;height:14px;border-left:1.4px solid #bfc4cc}
.ccw .typed-port{display:flex;flex-direction:column;gap:8px;margin-right:2px}
.ccw .typed-lane{position:relative;width:34px;height:0;border-top:1.4px solid #bfc4cc}
.ccw .typed-lane .port-type{position:absolute;left:0;font:9px ui-monospace,Menlo,monospace;color:#7c838d;white-space:nowrap}
.ccw .lane-in .port-type{bottom:4px}.ccw .lane-out .port-type{top:4px}
.ccw .lane-in:after{content:'';position:absolute;right:-1px;top:-4px;border-left:7px solid #bfc4cc;border-top:3.5px solid transparent;border-bottom:3.5px solid transparent}
.ccw .lane-out:before{content:'';position:absolute;left:-1px;top:-4px;border-right:7px solid #bfc4cc;border-top:3.5px solid transparent;border-bottom:3.5px solid transparent}
.ccw .named-port{display:flex;align-items:center;gap:3px}.ccw .named-port.right{flex-direction:row-reverse}
.ccw .port-name{font:italic 13px 'STIX Two Text','STIX Two Math',Georgia,serif;color:#d6d9de;white-space:nowrap}
.ccw .stub-port{display:flex}
.ccw .core-stack{display:flex;flex-direction:column;gap:8px;position:relative}
.ccw .core-stack.parallel{border:1px dashed #5a5d63;border-radius:5px;padding:6px}
.ccw .core-stack.parallel:before,.ccw .core-stack.parallel:after{content:'';position:absolute;top:50%;width:7px;border-top:1.4px solid #bfc4cc}
.ccw .core-stack.parallel:before{right:100%}.ccw .core-stack.parallel:after{left:100%}
.ccw .bottom-ports{position:relative;display:flex;justify-content:space-around;align-items:flex-start;gap:18px;min-width:75%;padding-top:14px}
.ccw .bottom-ports:before{content:'';position:absolute;top:0;left:8%;right:8%;border-top:1.4px solid #bfc4cc}
.ccw .bottom-ports:after{content:'';position:absolute;top:-14px;left:50%;height:14px;border-left:1.4px solid #bfc4cc}
.ccw .bottom-iface{display:flex;flex-direction:column;align-items:center;min-width:max-content}
.ccw .bottom-iface>.vwire:first-child{margin-top:-14px;height:28px;flex-basis:28px}
.ccw .mbo-port{display:flex;align-items:center;position:relative;margin-left:2px}
.ccw .mbo-port .hwire{position:relative}
.ccw .mbo-port .hwire:after{content:'';position:absolute;right:-1px;top:-4px;border-left:7px solid #d8a35c;border-top:3.5px solid transparent;border-bottom:3.5px solid transparent}
.ccw .mbo-label{margin-left:4px;font:italic 600 12px 'STIX Two Text','STIX Two Math',Georgia,serif;color:#eec489;white-space:nowrap}
.ccw .system-component.compact{padding-top:12px}.ccw .compact .ccnode{min-height:28px;padding:4px 8px;font-size:10px}.ccw .compact .hwire{flex-basis:12px;width:12px}
.ccw .wire{stroke:#bfc4cc;stroke-width:1.4;fill:none}
.ccw .ah{fill:#bfc4cc}
.ccw .res,.ccw .cvt{fill:#2b2d31;stroke:#bfc4cc;stroke-width:1.4}
.ccw .brk{fill:none;stroke:#5a5d63;stroke-width:1;stroke-dasharray:5 4}
.ccw .lbl{font:italic 13px 'STIX Two Text','STIX Two Math',Georgia,serif;fill:#d6d9de}
.ccw .rlb{font:600 11.5px 'STIX Two Text','STIX Two Math',Georgia,serif;letter-spacing:.1em;fill:#d6d9de}
.ccw .lblx{font:italic 12px 'STIX Two Text','STIX Two Math',Georgia,serif}
.ccw .c-cvt{fill:#223047;stroke:#6ca7e8}
.ccw text.t-cvt,.ccw .fo.t-cvt{fill:#9cc7f5;color:#9cc7f5}
.ccw .c-sim{fill:#3b2f22;stroke:#d8a35c}
.ccw text.t-sim,.ccw .fo.t-sim{fill:#eec489;color:#eec489}
.ccw .chip{fill:#26282c;stroke:#5a5d63;stroke-width:1;stroke-dasharray:4 3}
.ccw text.chiptx{font:10px ui-monospace,Menlo,monospace;fill:#9aa1ab}
.ccw .fo{display:flex;align-items:center;justify-content:center;width:100%;height:100%;font-size:11px}
.ccw .fo *{white-space:nowrap}
.ccw .mboout{font:italic 600 11px 'STIX Two Text','STIX Two Math',Georgia,serif;fill:#eec489}
.ccw .wt{font:9px ui-monospace,Menlo,monospace;fill:#6f7680}
.ccw .frl{font:600 10px ui-monospace,Menlo,monospace;fill:#8a8f98;letter-spacing:.08em}
.ccw .ccg .wire,.ccw .ccg rect,.ccw .ccg text{transition:stroke .15s,fill .15s}
.ccw .ccg:hover rect{stroke:#6ca7e8}
.ccw .sel rect{stroke:#6ca7e8;stroke-width:2.2}
.ccw .dv{display:flex;align-items:center;gap:10px;margin:6px 0;max-width:420px}
.ccw .dv .rl{flex:1;height:1px;background:#3a3a3a}
.ccw .dv .ap{font:500 13px 'STIX Two Text','STIX Two Math',Georgia,serif;font-style:normal;color:#d4d4d4;display:flex;align-items:center;gap:6px}
.ccw .epsc{font-size:11px;white-space:nowrap}
.ccw .note{font:11px system-ui,sans-serif;color:#8a8f98;margin-top:6px;max-width:420px}
.ccw .cards{display:flex;flex-wrap:nowrap;gap:8px;align-items:center;min-width:max-content;margin:4px 0}
.ccw .card{border:1px solid #3a3a3a;border-radius:6px;padding:3px 6px;display:flex;gap:6px;align-items:center;background:rgba(255,255,255,.02)}
.ccw .badge{font:italic 600 19px 'STIX Two Text','STIX Two Math',Georgia,serif;color:#d4d4d4;flex:none}
.ccw .paren{font:300 24px 'STIX Two Text','STIX Two Math',Georgia,serif;color:#9aa1ab;flex:none;line-height:1}
.ccw .plus{font:13px 'STIX Two Text',serif;color:#8a8f98}
.ccw .numchip{display:inline-flex;align-items:center;font-size:10.5px;color:#9aa1ab;border:1px dashed #5a5d63;border-radius:4px;padding:2px 6px;white-space:nowrap}
.ccw .duo{display:flex;align-items:center;gap:4px}
.ccw .duosym{font:16px 'STIX Two Text',serif;color:#9aa1ab}
.ccw .ev{font:10px ui-monospace,Menlo,monospace;color:#9aa1ab;max-width:170px;overflow-wrap:anywhere}
.ccw .rgd{display:flex;align-items:center;gap:9px;margin-top:5px;padding:4px 8px;background:rgba(255,255,255,.03);border-radius:5px;border:1px solid transparent}
.ccw .rgd-cur{background:rgba(108,167,232,.08);border-color:rgba(108,167,232,.4)}
.ccw .rgn{color:#6ca7e8;font:11px ui-monospace,Menlo,monospace;flex:none;cursor:pointer}
.ccw .rgn:hover{text-decoration:underline}
.ccw .rgrow{display:flex;align-items:center;gap:7px;flex-wrap:nowrap;min-width:max-content;flex:1}
.ccw .calc-stepper{width:100%;min-width:0;outline:none}
.ccw .calc-step-controls{display:flex;align-items:center;justify-content:center;gap:10px;margin:3px 0 7px}
.ccw .calc-step-controls button{border:1px solid #5a5d63;border-radius:4px;background:#2b2d31;color:#d6d9de;min-width:30px;padding:2px 8px;cursor:pointer}
.ccw .calc-step-controls button:hover:not(:disabled){border-color:#6ca7e8;background:#223047}
.ccw .calc-step-controls button:disabled{opacity:.35;cursor:default}
.ccw .calc-step-count{font:600 10px system-ui,sans-serif;color:#8a8f98;letter-spacing:.06em;min-width:82px;text-align:center}
.ccw .calc-step-body{max-width:100%;overflow-x:auto;overflow-y:visible}
.ccw .cc-adaptive.vertical .rgd{align-items:flex-start}
.ccw .cc-adaptive.vertical .rgrow{flex-direction:column;align-items:stretch;min-width:0;width:100%}
.ccw .cc-adaptive.vertical .cards{flex-direction:column;align-items:stretch;min-width:0;width:100%}
.ccw .cc-adaptive.vertical .card{align-items:flex-start;max-width:100%}
.ccw .cc-adaptive.vertical .duo{flex-direction:column;align-items:center;max-width:100%}
.ccw .cc-adaptive.vertical .ap{align-self:center}
body.vscode-light .ccw .wire{stroke:#1c1c1c}
body.vscode-light .ccw .construction-frame,body.vscode-light .ccw .core-stack.parallel{border-color:#a39e93}
body.vscode-light .ccw .frame-label{background:var(--vscode-editor-background,#fff);color:#656a72}
body.vscode-light .ccw .hwire,body.vscode-light .ccw .typed-lane{border-color:#1c1c1c}
body.vscode-light .ccw .vwire,body.vscode-light .ccw .bottom-ports:before,body.vscode-light .ccw .bottom-ports:after{border-color:#1c1c1c}
body.vscode-light .ccw .lane-in:after{border-left-color:#1c1c1c}
body.vscode-light .ccw .lane-out:before{border-right-color:#1c1c1c}
body.vscode-light .ccw .port-name,body.vscode-light .ccw .ccnode.res{color:#1c1c1c}
body.vscode-light .ccw .ccnode.res{background:#fff;border-color:#1c1c1c}
body.vscode-light .ccw .ccnode.cvt{background:oklch(0.97 0.015 250);border-color:oklch(0.5 0.11 250);color:oklch(0.42 0.11 250)}
body.vscode-light .ccw .ccnode.c-sim{background:oklch(0.97 0.015 55);border-color:oklch(0.58 0.12 55);color:oklch(0.47 0.12 55)}
body.vscode-light .ccw .ccnode.chip{background:#f7f7f5;border-color:#b5b5b5;color:#6f6f6f}
body.vscode-light .ccw .typed-lane .port-type{color:#5f6368}
body.vscode-light .ccw .mbo-label{color:#9a530d}
body.vscode-light .ccw .ah{fill:#1c1c1c}
body.vscode-light .ccw .res,body.vscode-light .ccw .cvt{fill:#fff;stroke:#1c1c1c}
body.vscode-light .ccw .lbl,body.vscode-light .ccw .rlb{fill:#1c1c1c}
body.vscode-light .ccw .c-cvt{fill:oklch(0.97 0.015 250);stroke:oklch(0.5 0.11 250)}
body.vscode-light .ccw text.t-cvt,body.vscode-light .ccw .fo.t-cvt{fill:oklch(0.42 0.11 250);color:oklch(0.42 0.11 250)}
body.vscode-light .ccw .c-sim{fill:oklch(0.97 0.015 55);stroke:oklch(0.58 0.12 55)}
body.vscode-light .ccw text.t-sim,body.vscode-light .ccw .fo.t-sim{fill:oklch(0.47 0.12 55);color:oklch(0.47 0.12 55)}
body.vscode-light .ccw .chip{fill:#f7f7f5;stroke:#b5b5b5}
body.vscode-light .ccw text.chiptx{fill:#6f6f6f}
body.vscode-light .ccw .brk{stroke:#a39e93}
body.vscode-light .ccw .frl,body.vscode-light .ccw .wt{fill:#5f6368}
body.vscode-light .ccw .mboout{fill:#9a530d}
body.vscode-light .ccw .dv .rl{background:rgba(0,0,0,.15)}
body.vscode-light .ccw .dv .ap{color:#1c1c1c}
body.vscode-light .ccw>summary{color:#8a8a8a}
body.vscode-light .ccw .sect,body.vscode-light .ccw .note{color:#666b73}
body.vscode-light .ccw .card{border-color:#ddd;background:#fafaf8}
body.vscode-light .ccw .numchip{color:#6f6f6f;border-color:#b5b5b5}
body.vscode-light .ccw .badge{color:#1c1c1c}
body.vscode-light .ccw .paren,body.vscode-light .ccw .plus,body.vscode-light .ccw .duosym,
body.vscode-light .ccw .ev,body.vscode-light .ccw .rgj{color:#60656d}
body.vscode-light .ccw .rgd{background:#f4f4f2}
body.vscode-light .ccw .rgd-cur{background:oklch(0.965 0.012 250);border-color:oklch(0.85 0.04 250)}
body.vscode-light .ccw .calc-step-controls button{background:#fff;color:#1c1c1c;border-color:#a39e93}
body.vscode-light .ccw .calc-step-controls button:hover:not(:disabled){border-color:oklch(0.5 0.11 250);background:oklch(0.97 0.015 250)}
"

private def sect (t : String) : Html :=
  .element "div" #[sattr "className" "sect"] #[.text t]

private def divider (rel : String) (epsHtml? : Option Html) : Html :=
  .element "div" #[sattr "className" "dv"]
    #[.element "div" #[sattr "className" "rl"] #[],
      .element "span" #[sattr "className" "ap"]
        (#[Html.text rel] ++ (match epsHtml? with
          | some h => #[.element "span" #[sattr "className" "epsc"] #[h]]
          | none => #[])),
      .element "div" #[sattr "className" "rl"] #[]]

private def epsHtmlOf (jv : JudgmentView) (codes : Codes) : Option Html :=
  match jv.epsPos?.bind (codeFor? codes) with
  | some h => some h
  | none => jv.eps?.map Html.text

private def paren (t : String) : Html :=
  .element "span" #[sattr "className" "paren"] #[.text t]

/-- One compact advantage card: `Δ( ⟨sys⟩ , ⟨sys⟩ )`. -/
private def renderCard (sel : Array (Array Nat)) (codes : Codes) : AdvCard → Html
  | .dist sym l r =>
    .element "div" #[sattr "className" "card"]
      #[.element "span" #[sattr "className" "badge"] #[.text sym],
        .element "div" #[sattr "className" "duo"]
          #[paren "(",
            renderSystemComponent l sel codes (compact := true),
            .element "span" #[sattr "className" "duosym"] #[.text ","],
            renderSystemComponent r sel codes (compact := true),
            paren ")"]]
  | .win sym sys =>
    .element "div" #[sattr "className" "card"]
      #[.element "span" #[sattr "className" "badge"] #[.text sym],
        .element "div" #[sattr "className" "duo"]
          #[paren "(", renderSystemComponent sys sel codes (compact := true), paren ")"]]
  | .mass d ev =>
    .element "div" #[sattr "className" "card"]
      #[.element "span" #[sattr "className" "badge"] #[.text "mass"],
        .element "div" #[sattr "className" "duo"]
          #[paren "(", renderSystemComponent d sel codes (compact := true),
            .element "div" #[sattr "className" "ev"] #[.text ev], paren ")"]]
  | .num label pos =>
    .element "span" #[sattr "className" "numchip"]
      #[(codeFor? codes pos).getD (.text label)]

/-- A row of cards joined by `+`. -/
private def renderCards (cs : Array AdvCard) (sel : Array (Array Nat))
    (codes : Codes) : Html := Id.run do
  let mut kids : Array Html := #[]
  for i in [0:cs.size] do
    if i > 0 then
      kids := kids.push <| .element "span" #[sattr "className" "plus"] #[.text "+"]
    kids := kids.push (renderCard sel codes cs[i]!)
  return .element "div" #[sattr "className" "cards"] kids

/-! ### Structural renderer regression checks

These use synthetic view models rather than theorem parsing, so a geometry or
fallback regression fails while building the theory-free widget itself.  The
theorem demos separately guard parser coverage. -/

private partial def htmlCountTag (wanted : String) : Html → Nat
  | .element tag _ kids =>
      (if tag == wanted then 1 else 0) + kids.foldl (fun n h => n + htmlCountTag wanted h) 0
  | .component _ _ _ kids => kids.foldl (fun n h => n + htmlCountTag wanted h) 0
  | .text _ => 0

private partial def htmlCountText (wanted : String) : Html → Nat
  | .element _ _ kids | .component _ _ _ kids =>
      kids.foldl (fun n h => n + htmlCountText wanted h) 0
  | .text s => if s == wanted then 1 else 0

private partial def htmlCountClass (wanted : String) : Html → Nat
  | .element _ attrs kids =>
      let here := attrs.foldl (init := 0) fun n kv =>
        match kv with
        | ("className", .str s) => if s.splitOn " " |>.contains wanted then n + 1 else n
        | _ => n
      here + kids.foldl (fun n h => n + htmlCountClass wanted h) 0
  | .component _ _ _ kids => kids.foldl (fun n h => n + htmlCountClass wanted h) 0
  | .text _ => 0

private partial def htmlAttr? (tag key : String) : Html → Option String
  | .element t attrs kids =>
      if t == tag then
        match attrs.findSome? fun
          | (k, .str v) => if k == key then some v else none
          | _ => none with
        | some v => some v
        | none => kids.findSome? (htmlAttr? tag key)
      else kids.findSome? (htmlAttr? tag key)
  | .component _ _ _ kids => kids.findSome? (htmlAttr? tag key)
  | .text _ => none

private def rendererSelfCheck : Except String Unit := do
  let core : Elem := { label := "R", kind := .res, pos := #[1] }
  let typed : Iface := { inType := some "X", outType := some "Y" }
  let typedSvg := sysSvg { center := #[core], ifaces := #[typed] } #[] #[]
  unless htmlCountTag "polygon" typedSvg == 2 do
    throw "typed anonymous ports must render exactly two arrowheads"
  unless htmlCountText "X" typedSvg == 1 && htmlCountText "Y" typedSvg == 1 do
    throw "typed anonymous ports must render both alphabet labels"

  let plain : Iface := {}
  let plainSvg := sysSvg { center := #[core], ifaces := #[plain] } #[] #[]
  unless htmlCountTag "polygon" plainSvg == 0 do
    throw "untyped abstract ports must remain undirected"

  let gameSvg := sysSvg
    { center := #[{ core with mbo := true }], ifaces := #[typed] } #[] #[]
  unless htmlCountText "Aᵢ" gameSvg == 1 && htmlCountTag "polygon" gameSvg == 3 do
    throw "games must expose one labelled MBO output in addition to the two resource lanes"

  let component := renderSystemComponent
    { center := #[core], ifaces := #[typed] } #[] #[]
  unless htmlCountTag "svg" component == 0 && htmlCountClass "ccnode" component == 1 &&
      htmlCountClass "typed-port" component == 1 do
    throw "the proof-panel system renderer must use intrinsic DOM components, not SVG geometry"
  unless (htmlAttr? "div" "title" component).isSome do
    throw "semantic DOM nodes must expose native hover information"

  let shared : Elem := { label := "CBC", kind := .conv }
  let realShared : SystemView :=
    { center := #[core], ifaces := #[{ chain := #[shared] }] }
  let idealShared : SystemView :=
    { center := #[{ core with label := "R" }],
      ifaces := #[{ adv := true, chain := #[{ shared with kind := .sim }] }] }
  let (_, idealShared) := reconcileSharedConverters realShared idealShared
  let sharedComponent := renderSystemComponent idealShared #[] #[]
  unless htmlCountClass "bottom-iface" sharedComponent == 0 &&
      htmlCountClass "cvt" sharedComponent == 1 && htmlCountClass "c-sim" sharedComponent == 0 do
    throw "a converter shared by both sides must remain a horizontal converter"

  if stylesheet.contains "text-overflow" || stylesheet.contains "overflow:hidden" then
    throw "diagram text must never be clipped or replaced by an ellipsis"

  let parallelSvg := sysSvg
    { center := #[core, { core with label := "S", pos := #[2] }] } #[] #[]
  unless htmlCountClass "brk" parallelSvg == 1 && htmlCountClass "wire" parallelSvg >= 7 do
    throw "parallel centers must have a grouping boundary and shared-interface buses"
  let framedParallelSvg := sysSvg
    { center := #[core, { core with label := "S", pos := #[2] }],
      frameLabel? := some "C" } #[] #[]
  unless htmlCountClass "brk" framedParallelSvg == 1 &&
      htmlCountClass "wire" framedParallelSvg >= 7 do
    throw "expanded parallel constructions must retain their shared-interface buses"

  let lower (name : String) : Iface :=
    { label := name, adv := true,
      chain := #[{ label := "wide-converter-label", kind := .sim }] }
  let manySvg := sysSvg
    { center := #[core], ifaces := #[lower "E1", lower "E2", lower "E3", lower "E4"] } #[] #[]
  let some vb := htmlAttr? "svg" "viewBox" manySvg
    | throw "system SVG must expose a viewBox"
  unless vb.startsWith "-" do
    throw "wide lower-interface layouts must expand the viewBox to the left"
  unless htmlCountClass "wire" manySvg >= 11 do
    throw "multiple lower interfaces must connect through a shared trunk"

  let interactiveSvg := sysSvg { center := #[core], ifaces := #[plain] }
    #[] #[(#[1], .text "interactive")]
  unless htmlCountTag "switch" interactiveSvg == 1 &&
      htmlCountTag "foreignObject" interactiveSvg == 1 &&
      htmlCountText "R" interactiveSvg >= 1 do
    throw "interactive labels must retain a plain SVG fallback"

  let card := renderCard #[] #[] (.dist "Δ"
    { center := #[core], ifaces := #[typed] }
    { center := #[{ core with label := "S" }], ifaces := #[typed] })
  unless htmlCountText "Δ" card == 1 && htmlCountText "(" card == 1 &&
      htmlCountText "," card == 1 && htmlCountText ")" card == 1 do
    throw "distance cards must render a full operator and balanced punctuation"

run_cmd
  match rendererSelfCheck with
  | .ok () => pure ()
  | .error msg => throwError "CCWidget renderer self-check failed: {msg}"

private def noteRows (jv : JudgmentView) : Array Html := Id.run do
  let mut rows : Array Html := #[]
  if let some s := jv.note? then
    rows := rows.push <| .element "div" #[sattr "className" "note"] #[.text s]
  let addU (s : SystemView) (rs : Array Html) : Array Html :=
    match s.unfolded? with
    | some u => rs.push (.element "div" #[sattr "className" "note"] #[.text u])
    | none => rs
  rows := addU jv.real rows
  if let some i := jv.ideal? then rows := addU i rows
  return rows

/-- Render a parsed judgment: REAL·LHS diagram, relation divider,
IDEAL·RHS diagram (two-sided) or card rows (calculation steps). -/
def renderJudgment (jv : JudgmentView) (sel : Array (Array Nat))
    (codes : Codes := #[]) : Html :=
  let body : Array Html :=
    match jv.bridge? with
    | some (l, r) =>
      #[sect "LHS", renderCards l sel codes, divider jv.rel none,
        sect "RHS", renderCards r sel codes]
    | none =>
      match jv.ideal? with
      | some ideal =>
        let idealLbl := if jv.rel == "|≡" then "IDEAL · FLAG OFF (Aᵢ = 0)" else "IDEAL · RHS"
        #[sect "REAL · LHS", renderSystemComponent jv.real sel codes,
          divider jv.rel (epsHtmlOf jv codes),
          sect idealLbl, renderSystemComponent ideal sel codes]
      | none =>
        #[sect "SYSTEM", renderSystemComponent jv.real sel codes,
          divider jv.rel (epsHtmlOf jv codes)]
  .element "div" #[sattr "className" "bd"] (body ++ noteRows jv)

/-- One-row rendering for ladder rungs: diagrams inline with the
relation between them. -/
def renderInline (jv : JudgmentView) (sel : Array (Array Nat))
    (codes : Codes := #[]) : Html :=
  let relSpan (withEps : Bool) : Html :=
    .element "span" #[sattr "className" "ap"]
      (#[Html.text jv.rel] ++ (if withEps then
        match epsHtmlOf jv codes with
        | some h => #[.element "span" #[sattr "className" "epsc"] #[h]]
        | none => #[]
      else #[]))
  let kids : Array Html :=
    match jv.bridge? with
    | some (l, r) =>
      #[renderCards l sel codes, relSpan false, renderCards r sel codes]
    | none =>
      match jv.ideal? with
      | some ideal =>
        #[renderSystemComponent jv.real sel codes (compact := true), relSpan true,
          renderSystemComponent ideal sel codes (compact := true)]
      | none =>
        #[renderSystemComponent jv.real sel codes (compact := true), relSpan true]
  .element "div" #[sattr "className" "rgrow"] kids

/-- Invisible: rendered when there is nothing to draw, so the always-on
panel adds nothing to unrelated proofs. -/
private def invisible : Html :=
  .element "span" #[("style", Json.mkObj [("display", Json.str "none")])] #[]

private def panel (inner : Html) : Html :=
  .element "details" #[("open", Json.bool true), sattr "className" "ccw"]
    #[.element "summary" #[] #[.text "constructive cryptography"],
      .element "style" #[] #[.text stylesheet],
      inner]

/-! ## The calc ladder and enclosing-theorem context

A panel RPC can see the surrounding *syntax* through the command
snapshot: the enclosing `calc` block becomes the lecture's hybrid
ladder — every step a rung drawn as diagrams, justification names
between rungs, click a rung's number to move the cursor there. -/

private def rangeContains (stx : Syntax) (pos : String.Pos.Raw) : Bool :=
  match stx.getRange? with
  | some r => r.start ≤ pos && pos ≤ r.stop
  | none => false

/-- Smallest `calcSteps` node containing `pos`. -/
private partial def findCalcSteps? (stx : Syntax) (pos : String.Pos.Raw) : Option Syntax :=
  if !rangeContains stx pos then none
  else
    let deeper := stx.getArgs.findSome? (findCalcSteps? · pos)
    match deeper with
    | some d => some d
    | none => if stx.getKind == `Lean.calcSteps then some stx else none

/-- The elaborated `Expr` (and its elaboration context) recorded for a
syntax range — how the ladder recovers each step's statement with the
`calc` `_` placeholders resolved. -/
private def termInfoFor? (tree : Elab.InfoTree) (target : Syntax) :
    Option (Elab.ContextInfo × Elab.TermInfo) := Id.run do
  let some r := target.getRange? | return none
  let results := tree.foldInfo (init := #[]) fun ci i acc =>
    match i with
    | .ofTermInfo ti =>
      match ti.stx.getRange? with
      | some r' => if r' == r then acc.push (ci, ti) else acc
      | none => acc
    | _ => acc
  return results[0]?

private structure Rung where
  jv? : Option JudgmentView
  codes : Codes
  /-- Interactive mathematical term (fallback when the step does not draw). -/
  code? : Option Html
  /-- Pretty relation text, retained only as a plain fallback. -/
  title : String
  current : Bool
  /-- Step start, for click-to-navigate. -/
  target : Lsp.Range
  deriving Inhabited

/-- Extract the ladder from the calc block containing `pos`. -/
private def calcLadder? (snap : Snapshots.Snapshot) (text : FileMap)
    (pos : String.Pos.Raw) (sel : Array (Array Nat)) :
    RequestM (Option (Array Rung)) := do
  let some steps := findCalcSteps? snap.stx pos | return none
  -- flatten: calcFirstStep :: calcStep*
  let mut stepStxs : Array Syntax := #[]
  for a in steps.getArgs do
    if a.getKind == `Lean.calcFirstStep || a.getKind == `Lean.calcStep then
      stepStxs := stepStxs.push a
    else
      for b in a.getArgs do
        if b.getKind == `Lean.calcFirstStep || b.getKind == `Lean.calcStep then
          stepStxs := stepStxs.push b
  if stepStxs.size ≤ 1 then return none
  let mut rungs : Array Rung := #[]
  for st in stepStxs do
    let termStx := st[0]!
    let title := ((termStx.reprint.getD "…").replace "\n" " ").trimAscii.toString
    let current := rangeContains st pos
    let some stepRange := st.getRange? | continue
    let target : Lsp.Range :=
      { start := text.utf8PosToLspPos stepRange.start
        «end» := text.utf8PosToLspPos stepRange.start }
    let mut jv? : Option JudgmentView := none
    let mut codes : Codes := #[]
    let mut code? : Option Html := none
    if let some (ci, ti) := termInfoFor? snap.infoTree termStx then
      let r ← ci.runMetaM ti.lctx do
        try
          let stmt ← instantiateMVars ti.expr
          let fmt ← Widget.ppExprTagged stmt
          let code := Html.ofComponent InteractiveCode { fmt } #[]
          match ← parseJudgment? stmt (sel := sel) with
          | some jv => pure (some (some jv, ← buildCodes jv stmt, code))
          | none => pure (some (none, #[], code))
        catch _ => pure none
      if let some (parsed, cs, code) := r then
        jv? := parsed
        codes := cs
        code? := some code
    rungs := rungs.push { jv?, codes, code?, title, current, target }
  return some rungs

/-- The enclosing theorem's own statement: shown dimmed when the current
goal is bookkeeping inside a CC proof. -/
private def enclosingJudgment? (snap : Snapshots.Snapshot) :
    RequestM (Option (JudgmentView × Codes)) := do
  let outer := snap.infoTree.foldInfo
      (init := (none : Option (Elab.ContextInfo × Elab.TacticInfo))) fun ci i acc =>
    match i with
    | .ofTacticInfo ti =>
      match acc with
      | none => some (ci, ti)
      | some (_, ti') =>
        let sz  := (ti.stx.getRange?.map fun r => r.stop.byteIdx - r.start.byteIdx).getD 0
        let sz' := (ti'.stx.getRange?.map fun r => r.stop.byteIdx - r.start.byteIdx).getD 0
        if sz > sz' then some (ci, ti) else acc
    | _ => acc
  let some (ci, ti) := outer | return none
  let some g := ti.goalsBefore.head? | return none
  ci.runMetaM {} do
    setMCtx ti.mctxBefore
    g.withContext do
      try
        let stmt ← instantiateMVars (← g.getType)
        match ← parseJudgment? stmt with
        | some jv => pure (some (jv, ← buildCodes jv stmt))
        | none => pure none
      catch _ => pure none

private def renderRungs (rungs : Array Rung) (sel : Array (Array Nat))
    (dm : Lean.Server.DocumentMeta) : Html := Id.run do
  let mut steps : Array Html := #[]
  for i in [0:rungs.size] do
    let r := rungs[i]!
    let num := (if i < 10 then s!"0{i}" else s!"{i}")
    let numLink : Html := .ofComponent MakeEditLink
      (.ofReplaceRange' dm r.target "" (some r.target))
      #[.element "span" #[sattr "className" "rgn"] #[.text num]]
    let content : Html := match r.jv? with
      | some jv => renderInline jv sel r.codes
      | none => .element "span" #[sattr "className" "numchip"]
          #[r.code?.getD (.text r.title)]
    steps := steps.push <| .element "div"
      #[sattr "className" (if r.current then "rgd rgd-cur" else "rgd")]
      #[numLink, content]
  let initialIndex := ((List.range rungs.size).find? fun i => rungs[i]!.current).getD 0
  let stepper := Html.ofComponent CalcStepper { initialIndex } steps
  return .element "div" #[sattr "className" "bd"]
    #[sect "CALC · ONE STEP", stepper]

/-! ## The panel widget -/

@[server_rpc_method]
def CCDiagram.rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) := do
  let doc ← RequestM.readDoc
  let text := doc.meta.text
  let pos := text.lspPosToUtf8Pos props.pos
  RequestM.withWaitFindSnapAtPos props.pos fun snap => do
    -- selections only make sense against the first tactic goal
    let sel := match props.goals[0]? with
      | some g => props.selectedLocations.filterMap fun l =>
          if l.mvarId == g.mvarId then
            match l.loc with
            | .target pos => some pos.toArray
            | _ => none
          else none
      | none => #[]
    -- the current statement: the tactic goal, else the term-mode goal
    let goalJv? ←
      if let some g := props.goals[0]? then
        g.ctx.val.runMetaM {} <| g.mvarId.withContext do
          try
            let stmt ← instantiateMVars (← g.mvarId.getType)
            match ← parseJudgment? stmt (sel := sel) with
            | some jv => pure (some (jv, ← buildCodes jv stmt))
            | none => pure none
          catch _ => pure none
      else if let some tg := props.termGoal? then
        tg.ctx.val.runMetaM tg.term.val.lctx do
          try
            let stmt ← match tg.term.val.expectedType? with
              | some ty => pure ty
              | none => inferType tg.term.val.expr
            let stmt ← instantiateMVars stmt
            match ← parseJudgment? stmt (sel := sel) with
            | some jv => pure (some (jv, ← buildCodes jv stmt))
            | none => pure none
          catch _ => pure none
      else pure none
    -- inside a calc block the ladder renders from the syntax alone
    let ladder? ← try calcLadder? snap text pos sel catch _ => pure none
    if let some rungs := ladder? then
      let rungs := rungs.map fun r =>
        if r.current && r.jv?.isNone then
          match goalJv? with
          | some (jv, cs) => { r with jv? := some jv, codes := cs }
          | none => r
        else r
      if rungs.any fun r => r.jv?.isSome then
        return panel (renderRungs rungs sel doc.meta)
    match goalJv? with
    | some (jv, codes) => return panel (renderJudgment jv sel codes)
    | none =>
      if props.goals.isEmpty && props.termGoal?.isNone then
        return invisible
      -- bookkeeping goal inside a CC theorem — keep the context strip
      let ctx? ← try enclosingJudgment? snap catch _ => pure none
      match ctx? with
      | some (jv, codes) =>
        return panel <| .element "div"
          #[("style", Json.mkObj [("opacity", Json.str "0.66")])]
          #[renderJudgment jv #[] codes]
      | none => return invisible

/-- The constructive-cryptography goal diagram.  Shown automatically in
every module importing `Rendering.CCWidget` (see the trailing
`show_panel_widgets`); renders nothing on non-CC goals. -/
@[widget_module]
def CCDiagram : Component PanelWidgetProps :=
  mk_rpc_widget% CCDiagram.rpc

/-! ## Build-time checks -/

/-- Elaborate `t` to the statement it denotes: a `Prop` stays itself, a
proof term (e.g. a theorem name) contributes its type; leading `∀`
binders are stripped. -/
private def elabStatement (t : Syntax.Term) : Elab.TermElabM (Option JudgmentView) := do
  -- a bare global constant contributes its type, with no metavariables
  if let some n ← observing? (Elab.realizeGlobalConstNoOverloadWithInfo t) then
    let stmt := (← getConstInfo n).type
    return ← forallTelescope stmt fun _ body => parseJudgment? body
  let e ← Elab.Term.elabTerm t none
  Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let stmt ← if (← inferType e).isSort then pure e else inferType e
  forallTelescope stmt fun _ body => parseJudgment? body

/-- `#cc_diagram_check stmt` fails to elaborate unless `stmt` (a `Prop`,
or the name of a theorem whose conclusion is one) is a statement the
`CCDiagram` widget can draw.  Silent on success — a CI guard for the
widget's goal coverage. -/
elab "#cc_diagram_check " t:term : command =>
  Elab.Command.runTermElabM fun _ => do
    match ← elabStatement t with
    | some _ => pure ()
    | none => throwError "cc_diagram: statement not recognized"

/-- `#cc_diagram_view stmt` logs the parsed diagram payload as JSON —
the debugging twin of `#cc_diagram_check`. -/
elab "#cc_diagram_view " t:term : command =>
  Elab.Command.runTermElabM fun _ => do
    match ← elabStatement t with
    | some jv => logInfo m!"{toJson jv}"
    | none => throwError "cc_diagram: statement not recognized"

end CCWidget

open CCWidget in
/- Zero ceremony: every module importing `Rendering.CCWidget` (transitively) shows
the panel; it renders nothing when the goal is not a CC judgment. -/
show_panel_widgets [CCDiagram]

import ConstructiveCryptography.DSL.Syntax
import ConstructiveCryptography.DSL.Converters
import ConstructiveCryptography.DSL.Tactics
import ConstructiveCryptography.Source
import ConstructiveCryptography.Context
import ConstructiveCryptography.InterfaceFilter
import ConstructiveCryptography.InterfaceCoherence
import ConstructiveCryptography.Notation

/-!
# The component compiler

Interfaces, systems, converters and filters are compiled to finite systems at every query
budget. Every sampling statement becomes a call to a source of fresh samples from its law, so a
component is a deterministic program with sources: a converter is its program followed by the
context attaching its sources, and a system is its program attached to its sources; a system
that samples nothing is the deterministic system of its program. Initialization runs in the
first invocation. A converter gets its inferred per-call bound `C.bound` and the arrow from
budget `q` to `C.bound * q` inside queries, plus the exact arrow `C.exact` when its number of
inside calls is a function of the input; a filter is the arrow from the restricted budget.
System definitions take their budget from their outermost component.
-/

namespace SystemAlgebra.DSL

open Lean Elab Command Parser Term
open CategoryTheory MonoidalCategory

/-- Bound names tracked only during elaboration; no runtime environment is generated. -/
def targetNames (t : Syntax) : Array Ident :=
  if t[0].isIdent then #[⟨t[0]⟩] else t[0][1].getSepArgs.map (⟨·⟩)

partial def tupleTerm (xs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) :=
  if xs.isEmpty then `(())
  else if xs.size = 1 then pure xs[0]!
  else do
    let tail ← tupleTerm (xs.extract 1 xs.size)
    `(($(xs[0]!), $tail))

def statements (b : Syntax) : Array Syntax := b[0].getArgs

partial def identifiers (s : Syntax) : Array Name :=
  if s.isIdent then #[s.getId] else s.getArgs.flatMap identifiers

def checkPure (s : Syntax) (calls : Array (Name × TSyntax `term)) : CommandElabM Unit := do
  if (identifiers s).any (fun n => calls.any (·.1 == n)) then
    throwErrorAt s "Inside calls must occupy an entire assignment right-hand side."

/-- Report a wrong reply against the declared alphabet, before pairing it with
private bindings in the generated function. -/
partial def annotateReturns (s : Syntax) (ty : TSyntax `term) : CommandElabM Syntax := do
  if s.getKind == ``returnStmt then
    let rhs ← `(($(⟨s[1]⟩):term : $ty))
    return s.setArg 1 rhs.raw
  match s with
  | .node info kind args => return .node info kind (← args.mapM (annotateReturns · ty))
  | _ => return s

partial def returns (b : Syntax) : Bool :=
  match (statements b).back? with
  | none => false
  | some s =>
    if s.getKind == ``returnStmt then true
    else if s.getKind == ``ifStmt then
      returns s[2] && !s[3].isNone && returns s[3][1]
    else if s.getKind == ``matchStmt then
      s[2][0].getArgs.all (fun c => returns c[3])
    else false

/-- How statements are lowered: the body of a program, the step of a system that samples
nothing, or the initial bindings with each sample replaced by a value of its law. -/
inductive LowerMode
  | program
  | system
  | template
  deriving BEq

def lowerAssignment (s : Syntax) (rest : TSyntax `term)
    (calls : Array (Name × TSyntax `term)) (mode : LowerMode) : CommandElabM (TSyntax `term) := do
    let names := targetNames s[0]
    let pat ← tupleTerm (names.map fun x => ⟨x.raw⟩)
    let rhs : TSyntax `term := ⟨s[3]⟩
    let called ← if rhs.raw.getKind == ``oracleCall then do
        match calls.find? (·.1 == rhs.raw[0].getId) with
        | some (_, label) =>
          pure (some (label, ← tupleTerm (rhs.raw[2].getSepArgs.map (⟨·⟩))))
        | none => pure none
      else match rhs with
        | `($f:ident $arg) => pure ((calls.find? (·.1 == f.getId)).map fun (_,label) => (label,arg))
        | _ => pure none
    let value := Lean.mkIdent (← liftCoreM <| mkFreshUserName `value)
    let k ← if s[1].isNone then `(fun $value:ident => let $pat:term := $value:ident; $rest)
      else `(fun ($value:ident : $(⟨s[1][1]⟩):term) => let $pat:term := $value:ident; $rest)
    if s.getKind == ``sampleStmt then
      checkPure rhs calls
      if mode == .template then return ← `($k (sampleWitness $rhs))
      throwErrorAt s "A sampling statement is compiled into a call to its source."
    if let some (label,arg) := called then
      checkPure arg calls
      if mode == .program then return ← `(callProg $label $arg $k)
      if mode == .template then
        throwErrorAt s "Initialization cannot call inside ports; call them from a procedure."
      throwErrorAt s "Inside calls belong to converters."
    checkPure rhs calls
    if s[1].isNone then return ← `(let $pat:term := $rhs; $rest)
    return ← `(let $pat:term : $(⟨s[1][1]⟩):term := $rhs; $rest)

/-- Build ordinary functions of inside histories. Sequencing is substitution of
Lean functions, and a call consumes a history entry. -/
partial def lowerFunction (ss : Array Syntax) (bound persistent : Array Ident)
    (calls : Array (Name × TSyntax `term)) (finish : TSyntax `term) (mode : LowerMode) :
    CommandElabM (TSyntax `term) := do
  if ss.isEmpty then
    if finish.raw.isMissing then throwError "Every procedure path must return a reply."
    return finish
  let s := ss[0]!
  let tail := ss.extract 1 ss.size
  if s.getKind == ``returnStmt then
    if mode == .template then throwErrorAt s "Initialization has no return; its bindings persist."
    if !tail.isEmpty then throwErrorAt s "Statements after return are unreachable."
    checkPure s[1] calls
    let stored ← tupleTerm (persistent.map fun x => ⟨x.raw⟩)
    if mode == .program then return ← `(returnProg (some $stored, $(⟨s[1]⟩):term))
    return ← `(($stored, $(⟨s[1]⟩):term))
  if s.getKind == ``assignStmt || s.getKind == ``sampleStmt then
    let mut nextBound := bound
    for x in targetNames s[0] do
      if !nextBound.any (·.getId == x.getId) then nextBound := nextBound.push x
    let rest ← lowerFunction tail nextBound persistent calls finish mode
    return ← lowerAssignment s rest calls mode
  if tail.isEmpty && s.getKind == ``ifStmt &&
      returns s[2] && !s[3].isNone && returns s[3][1] then
    checkPure s[1] calls
    let yes ← lowerFunction (statements s[2]) bound persistent calls finish mode
    let no ← lowerFunction (statements s[3][1]) bound persistent calls finish mode
    return ← `(if $(⟨s[1]⟩):term then $yes else $no)
  if tail.isEmpty && s.getKind == ``matchStmt &&
      s[2][0].getArgs.all (fun c => returns c[3]) then
    checkPure s[1] calls
    let alts : Array (TSyntax ``Term.matchAlt) ← s[2][0].getArgs.mapM fun c => do
      let rhs ← lowerFunction (statements c[3]) bound persistent calls finish mode
      `(matchAltExpr| | $(⟨c[1]⟩):term => $rhs)
    return ← `(match $(⟨s[1]⟩):term with $alts:matchAlt*)
  let rest ← lowerFunction tail bound persistent calls finish mode
  let values ← tupleTerm (bound.map fun x => ⟨x.raw⟩)
  let received := Lean.mkIdent (← liftCoreM <| mkFreshUserName `bindings)
  let next := Lean.mkIdent (← liftCoreM <| mkFreshUserName `next)
  let onward ← `($next:ident $values)
  let after ← `(fun $received:ident => let $values:term := $received:ident; $rest)
  if s.getKind == ``ifStmt then
    checkPure s[1] calls
    let yes ← lowerFunction (statements s[2]) bound persistent calls onward mode
    let no ← if s[3].isNone then pure onward
      else lowerFunction (statements s[3][1]) bound persistent calls onward mode
    return ← `(let $next:ident := $after; if $(⟨s[1]⟩):term then $yes else $no)
  if s.getKind == ``matchStmt then
    checkPure s[1] calls
    let alts : Array (TSyntax ``Term.matchAlt) ← s[2][0].getArgs.mapM fun c => do
      let rhs ← lowerFunction (statements c[3]) bound persistent calls onward mode
      `(matchAltExpr| | $(⟨c[1]⟩):term => $rhs)
    return ← `(let $next:ident := $after; match $(⟨s[1]⟩):term with $alts:matchAlt*)
  if s.getKind == ``forStmt then
    checkPure s[3] calls
    let x : Ident := ⟨s[1]⟩
    if bound.any (·.getId == x.getId) then throwErrorAt s "Loop variable shadows an existing binding."
    let body ← lowerFunction (statements s[4]) (bound.push x) persistent calls onward mode
    return ← `(forEach $(⟨s[3]⟩):term
      (fun $x:ident $next:ident $received:ident => let $values:term := $received:ident; $body)
      $after $values)
  throwErrorAt s "Unsupported cryptographic statement."

/-- A sampling site: the source its statement calls, and its law. -/
structure Site where
  name : Ident
  law : TSyntax `term

/-- The names a statement binds: assignment and sampling targets, and loop variables. -/
partial def boundNames (s : Syntax) : Array Name :=
  let own :=
    if s.getKind == ``assignStmt || s.getKind == ``sampleStmt then
      (targetNames s[0]).map (·.getId)
    else if s.getKind == ``forStmt then #[s[1].getId] else #[]
  own ++ s.getArgs.flatMap boundNames

/-- Replace the statements of a block. -/
def replaceStatements (b : Syntax) (ss : Array Syntax) : Syntax :=
  b.setArg 0 (b[0].setArgs ss)

/-- **Sampling as calls.** Every sampling statement becomes a call to a fresh source, whose law
is recorded; the law may depend on declaration parameters only. -/
partial def desugarSampling (bindings : Array Name) (ss : Array Syntax) :
    StateT (Array Site) CommandElabM (Array Syntax) :=
  ss.mapM fun s => do
    if s.getKind == ``sampleStmt then
      let rhs : TSyntax `term := ⟨s[3]⟩
      if (identifiers rhs).any fun x => bindings.contains x || bindings.contains x.getRoot then
        throwErrorAt rhs "A sampled law may depend on declaration parameters only; sample from a \
          fixed law and compute from the sample."
      let site := Lean.mkIdent (← liftCoreM <| mkFreshUserName `sample)
      modify (·.push ⟨site, rhs⟩)
      let call ← `($site:ident ())
      return Syntax.node s.getHeadInfo ``assignStmt #[s[0], s[1], Syntax.atom .none " ← ", call.raw]
    if s.getKind == ``ifStmt then
      let yes ← desugarSampling bindings (statements s[2])
      let s := s.setArg 2 (replaceStatements s[2] yes)
      if s[3].isNone then return s
      let no ← desugarSampling bindings (statements s[3][1])
      return s.setArg 3 (s[3].setArg 1 (replaceStatements s[3][1] no))
    if s.getKind == ``matchStmt then
      let cases ← s[2][0].getArgs.mapM fun c => do
        let body ← desugarSampling bindings (statements c[3])
        return c.setArg 3 (replaceStatements c[3] body)
      return s.setArg 2 (s[2].setArg 0 (s[2][0].setArgs cases))
    if s.getKind == ``forStmt then
      let body ← desugarSampling bindings (statements s[4])
      return s.setArg 4 (replaceStatements s[4] body)
    return s

/-- Declaration parameters: explicit names with a type, or instance arguments. -/
def paramBinder (p : Syntax) : CommandElabM (TSyntax ``Term.bracketedBinder) := do
  if p.getKind == ``instanceParam then `(bracketedBinder| [$(⟨p[1]⟩):term])
  else
    let ids : Array Ident := p[1].getArgs.map (⟨·⟩)
    `(bracketedBinder| ($ids:ident* : $(⟨p[3]⟩):term))

/-- The explicit parameter names, in order. -/
def paramArgs (ps : Array Syntax) : Array (TSyntax `term) :=
  ps.flatMap fun p => if p.getKind == ``instanceParam then #[] else p[1].getArgs.map (⟨·⟩)

/-- The explicit arguments of generated binders, in order. -/
def binderArgs (bs : Array (TSyntax ``Term.bracketedBinder)) : Array (TSyntax `term) :=
  bs.flatMap fun b => match b with
    | `(bracketedBinder| ($ids:ident* : $_)) => ids.map (⟨·.raw⟩)
    | _ => #[]

/-- The names the generated declarations bind for the query budget: `budget` and, on exact
typings, `queries`. They are the only names the elaborator binds without macro scopes, so that
callers can pass the budget by name. -/
def reservedNames : Array Name := #[`budget, `queries]

/-- Reject a component that mentions a reserved name, as a binder or as a reference, so that no
generated binder can capture a name of the component. Every other name the elaborator binds is
hygienic. The name of a named argument, `(budget := k)`, is not a mention. -/
partial def checkReserved (stx : Syntax) : CommandElabM Unit := do
  match stx with
  | .ident _ _ n _ =>
    if reservedNames.contains n.getRoot then
      throwErrorAt stx m!"`{n.getRoot}` is reserved: the generated declarations bind it for the query budget."
  | .node _ kind args =>
    if kind == ``Lean.Parser.Term.namedArgument then checkReserved args[3]!
    else for a in args do checkReserved a
  | _ => pure ()

/-- The identifiers of a piece of syntax, without macro scopes. -/
partial def identsOf : Syntax → Array Name
  | .ident _ _ n _ => #[n.eraseMacroScopes]
  | .node _ _ args => args.flatMap identsOf
  | _ => #[]

/-- The parameters that the types `types` mention, closed under the types and the instance
arguments of the parameters kept. An alphabet takes exactly these, so instance search on the
alphabet at a port determines every argument. -/
def usedParams (params : Array Syntax) (types : Array Syntax) : Array Syntax := Id.run do
  let names : Array Name := params.flatMap fun p =>
    if p.getKind == ``instanceParam then #[] else p[1].getArgs.map (·.getId)
  let mentioned (stx : Syntax) : Array Name := (identsOf stx).filter names.contains
  let mut kept : Array Name := (types.flatMap mentioned).foldl
    (fun acc n => if acc.contains n then acc else acc.push n) #[]
  let mut changed := true
  while changed do
    changed := false
    for p in params do
      let deps : Array Name :=
        if p.getKind == ``instanceParam then
          let ns := mentioned p[1]
          if ns.any kept.contains then ns else #[]
        else if p[1].getArgs.any (kept.contains ·.getId) then mentioned p[3] else #[]
      for n in deps do
        unless kept.contains n do
          kept := kept.push n
          changed := true
  return params.filterMap fun p =>
    if p.getKind == ``instanceParam then
      if (mentioned p[1]).all kept.contains then some p else none
    else
      let ids := p[1].getArgs.filter (kept.contains ·.getId)
      if ids.isEmpty then none else some (p.setArg 1 (mkNullNode ids))

/-- Generate the local labels and their finite input/output families. -/
def declareInterface (name : Ident) (params : Array Syntax)
    (ports : Array (Ident × Array Syntax × TSyntax `term)) :
    CommandElabM (TSyntax `term × TSyntax `term × TSyntax `term ×
      Array (TSyntax ``Term.bracketedBinder) × TSyntax `term × TSyntax `term) := do
  let portName := Lean.mkIdent (name.getId ++ `Port)
  let ctors ← ports.mapM fun (p, _, _) => `(Lean.Parser.Command.ctor| | $p:ident : $portName:ident)
  elabCommand (← `(inductive $portName:ident : Type where $ctors:ctor* deriving DecidableEq))
  let values : Array (TSyntax `term) := ports.map fun (p, _, _) =>
    ⟨(Lean.mkIdent (name.getId ++ `Port ++ p.getId)).raw⟩
  -- Instances named in the interface's namespace, so interfaces of one namespace do not clash.
  let fintypePort := Lean.mkIdent (name.getId ++ `instFintypePort)
  elabCommand (← `(instance $fintypePort:ident : Fintype $portName:ident :=
    Fintype.ofList [$values,*] (by intro i; cases i <;> simp)))
  if let #[value] := values then
    let uniquePort := Lean.mkIdent (name.getId ++ `instUniquePort)
    elabCommand (← `(instance $uniquePort:ident : Unique $portName:ident where
      default := $value
      uniq i := by cases i; rfl))
  let binders ← params.mapM paramBinder
  -- Each alphabet takes only the parameters its ports mention.
  let inParams := usedParams params (ports.flatMap fun (_, arguments, _) => arguments.map (·[2]))
  let outParams := usedParams params (ports.map fun (_, _, result) => result.raw)
  let inBinders ← inParams.mapM paramBinder
  let outBinders ← outParams.mapM paramBinder
  let inArgs := paramArgs inParams
  let outArgs := paramArgs outParams
  let inputName := Lean.mkIdent (name.getId ++ `Input)
  let outputName := Lean.mkIdent (name.getId ++ `Output)
  let mut ins : Array (TSyntax ``Term.matchAlt) := #[]
  let mut outs : Array (TSyntax ``Term.matchAlt) := #[]
  for (p, arguments, result) in ports do
    let types : Array (TSyntax `term) := arguments.map (fun a => ⟨a[2]⟩)
    let mut input ← `(Unit)
    if types.size == 1 then input := types[0]!
    else if types.size > 1 then
      input := types.back!
      for t in types.pop.reverse do input ← `($t × $input)
    let label := Lean.mkIdent (name.getId ++ `Port ++ p.getId)
    ins := ins.push (← `(matchAltExpr| | $label:ident => $input))
    outs := outs.push (← `(matchAltExpr| | $label:ident => $result))
  elabCommand (← `(abbrev $inputName:ident $inBinders:bracketedBinder* : $portName:ident → Type :=
    fun i => match i with $ins:matchAlt*))
  elabCommand (← `(abbrev $outputName:ident $outBinders:bracketedBinder* : $portName:ident → Type :=
    fun i => match i with $outs:matchAlt*))
  let fintypeInput := Lean.mkIdent (name.getId ++ `fintypeInput)
  let fintypeOutput := Lean.mkIdent (name.getId ++ `fintypeOutput)
  elabCommand (← `(@[reducible] def $fintypeInput:ident $inBinders:bracketedBinder* (i : $portName:ident) :
      Fintype ($inputName:ident $inArgs* i) := by cases i <;> infer_instance))
  elabCommand (← `(@[reducible] def $fintypeOutput:ident $outBinders:bracketedBinder* (i : $portName:ident) :
      Fintype ($outputName:ident $outArgs* i) := by cases i <;> infer_instance))
  -- With one port, the alphabet at a port reduces to its declared type, whose instances apply;
  -- with more, the alphabet at a variable port is found by these instances.
  if ports.size ≥ 2 then
    elabCommand (← `(attribute [instance] $fintypeInput:ident $fintypeOutput:ident))
  return (⟨portName.raw⟩, ← `($inputName:ident $inArgs*), ← `($outputName:ident $outArgs*), binders,
    ← `($fintypeInput:ident $inArgs*), ← `($fintypeOutput:ident $outArgs*))

/-- An interface declaration: the family of its query budgets. -/
@[command_elab interfaceDecl] def elabInterface : CommandElab := fun stx => do
  let ports := stx[3][0].getArgs.map fun p =>
    ((⟨p[0]⟩ : Ident), p[2].getSepArgs, (⟨p[5]⟩ : TSyntax `term))
  let (labels, inputs, outputs, params, fx, fy) ← declareInterface ⟨stx[1]⟩ stx[2].getArgs ports
  elabCommand (← `(abbrev $(⟨stx[1]⟩):ident $params:bracketedBinder* (q : ℕ) : Interface :=
    @Interface.queryBudget $labels _ $inputs $outputs $fx $fy q))
  let perPortName := Lean.mkIdent ((⟨stx[1]⟩ : Ident).getId ++ `perPort)
  elabCommand (← `(abbrev $perPortName:ident $params:bracketedBinder* (q : $labels → ℕ) : Interface :=
    @Interface.portBudget $labels _ $inputs $outputs $fx $fy q))

def parameterBinders (ps : Array Syntax) : CommandElabM (Array (TSyntax ``Term.bracketedBinder)) :=
  ps.mapM paramBinder

/-- The inside interfaces at budget `k`, with the proof that they admit every nonempty inside
history of at most `k` queries, and the labels of their calls. -/
partial def insideInterfaces (insideDecls : Array Syntax) (used : Array Name) (k : TSyntax `term) :
    CommandElabM (TSyntax `term × TSyntax `term × Array (Name × TSyntax `term)) := do
  if insideDecls.isEmpty then
    return (← `(Interface.unit),
      ← `(fun xs hne _ => by
        cases xs with
        | nil => exact absurd rfl hne
        | cons x _ => exact x.1.elim), #[])
  let first := insideDecls[0]!
  let ty : TSyntax `term := ⟨first[3]⟩
  let portPrefix := first[1].getId
  let mut calls := #[]
  let sig ← match ty with
    | `($x → $y) =>
      calls := #[(portPrefix, ← `(()))]
      `(Interface.queryBudget Unit (fun _ => $x) (fun _ => $y) $k)
    | _ =>
      for id in used do
        if id.getPrefix == portPrefix then
          let port := Lean.mkIdent (Name.mkSimple id.getString!)
          calls := calls.push (id, ← `(.$port:ident))
      `($ty $k)
  let admits ← `(fun _ hne hl => ⟨hne, hl⟩)
  if insideDecls.size == 1 then return (sig, admits, calls)
  let (rest, restAdmits, restCalls) ← insideInterfaces (insideDecls.extract 1 insideDecls.size) used k
  let leftCalls ← calls.mapM fun (n,l) => return (n, ← `(Sum.inl $l))
  let restCalls ← restCalls.mapM fun (n,l) => return (n, ← `(Sum.inr $l))
  return (← `(Interface.tensor $sig $rest), ← `(parallelInputs_of_length_le $admits $restAdmits),
    leftCalls ++ restCalls)

/-- The number of inside calls of a procedure body, as a function of its inputs: calls count
one, branches and matches choose, and a loop multiplies its body's count by its length. -/
partial def costOf (ss : Array Syntax) (calls : Array (Name × TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  if ss.isEmpty then return ← `(0)
  let s := ss[0]!
  let tail := ss.extract 1 ss.size
  if s.getKind == ``returnStmt then return ← `(0)
  if s.getKind == ``sampleStmt then return ← costOf tail calls
  if s.getKind == ``assignStmt then
    let rhs : TSyntax `term := ⟨s[3]⟩
    let called := (rhs.raw.getKind == ``oracleCall && calls.any (·.1 == rhs.raw[0].getId)) ||
      (match rhs with
        | `($f:ident $_) => calls.any (·.1 == f.getId)
        | _ => false)
    let rest ← costOf tail calls
    if called then return ← `(1 + $rest)
    let pat ← tupleTerm (targetNames s[0] |>.map fun x => ⟨x.raw⟩)
    if s[1].isNone then return ← `(let $pat:term := $rhs; $rest)
    return ← `(let $pat:term : $(⟨s[1][1]⟩):term := $rhs; $rest)
  if s.getKind == ``ifStmt then
    let yes ← costOf (statements s[2]) calls
    let no ← if s[3].isNone then `(0) else costOf (statements s[3][1]) calls
    let rest ← costOf tail calls
    return ← `((if $(⟨s[1]⟩):term then $yes else $no) + $rest)
  if s.getKind == ``matchStmt then
    let alts : Array (TSyntax ``Term.matchAlt) ← s[2][0].getArgs.mapM fun c => do
      let rhs ← costOf (statements c[3]) calls
      `(matchAltExpr| | $(⟨c[1]⟩):term => $rhs)
    let rest ← costOf tail calls
    return ← `((match $(⟨s[1]⟩):term with $alts:matchAlt*) + $rest)
  if s.getKind == ``forStmt then
    let body ← costOf (statements s[4]) calls
    let rest ← costOf tail calls
    return ← `($rest + ($(⟨s[3]⟩):term).length * $body)
  throwErrorAt s "Unsupported cryptographic statement."

/-- The most inside calls along a path of a procedure body without loops: a call counts one,
branches and matches take the largest of their counts. -/
partial def callCount (ss : Array Syntax) (calls : Array (Name × TSyntax `term)) : Option Nat := do
  if ss.isEmpty then return 0
  let s := ss[0]!
  let tail := ss.extract 1 ss.size
  if s.getKind == ``returnStmt then return 0
  if s.getKind == ``assignStmt then
    let rhs : TSyntax `term := ⟨s[3]⟩
    let called := (rhs.raw.getKind == ``oracleCall && calls.any (·.1 == rhs.raw[0].getId)) ||
      (match rhs with
        | `($f:ident $_) => calls.any (·.1 == f.getId)
        | _ => false)
    return (if called then 1 else 0) + (← callCount tail calls)
  if s.getKind == ``ifStmt then
    let yes ← callCount (statements s[2]) calls
    let no ← if s[3].isNone then pure 0 else callCount (statements s[3][1]) calls
    return max yes no + (← callCount tail calls)
  if s.getKind == ``matchStmt then
    let counts ← s[2][0].getArgs.mapM fun c => callCount (statements c[3]) calls
    return counts.foldl max 0 + (← callCount tail calls)
  none

/-- The number of error messages logged so far. -/
def errorCount : CommandElabM Nat := do
  return (← get).messages.toList.countP (·.severity == .error)

/-- What determines a component's outside interface at every budget: a declared interface
family, or its generated labels and finite alphabets with an optional exact domain. -/
structure Signature where
  declared : Option (TSyntax `term)
  labels : TSyntax `term
  inputs : TSyntax `term
  outputs : TSyntax `term
  fintypeInputs : TSyntax `term
  fintypeOutputs : TSyntax `term
  exactDomain : Option (Ident × TSyntax `term × TSyntax `term)

/-- The outside interface at budget `k`. -/
def Signature.at (σ : Signature) (k : TSyntax `term) : CommandElabM (TSyntax `term) := do
  if let some sig := σ.declared then return ← `(($sig $k))
  let labels := σ.labels
  let inputs := σ.inputs
  let outputs := σ.outputs
  let fx := σ.fintypeInputs
  let fy := σ.fintypeOutputs
  match σ.exactDomain with
  | none => `(@Interface.queryBudget $labels _ $inputs $outputs $fx $fy $k)
  | some (x, predicate, proof) =>
    `(({ I := $labels, X := $inputs, Y := $outputs, instFintypeX := $fx, instFintypeY := $fy,
         «domain» := fun h => (fun $x:ident => $predicate) h ∧ h.length ≤ $k,
         nonempty_prefix := budget_nonempty_prefix (P := fun $x:ident => $predicate) $proof,
         bound := $k, length_le := fun _ hd => hd.2 } : Interface))

/-- The outside interface at the per-port budget `q`, when the component has one: a declared
interface family, or its generated labels without an exact domain. -/
def Signature.perPortAt (σ : Signature) (q : TSyntax `term) :
    CommandElabM (Option (TSyntax `term)) := do
  if let some sig := σ.declared then
    match sig with
    | `($f:ident $args*) => return some (← `($(Lean.mkIdent (f.getId ++ `perPort)) $args* $q))
    | `($f:ident) => return some (← `($(Lean.mkIdent (f.getId ++ `perPort)) $q))
    | _ => return none
  if σ.exactDomain.isSome then return none
  return some (← `(@Interface.portBudget $(σ.labels) _ $(σ.inputs) $(σ.outputs)
    $(σ.fintypeInputs) $(σ.fintypeOutputs) $q))

/-- The inside interfaces of a component at budget `k`, with the proof that they admit every
nonempty history of at most `k` queries, and the labels of their calls: the declared inside
interfaces, then the sources of the sampling sites. -/
def componentInside (converting : Bool) (insides sites : Array Syntax) (used : Array Name)
    (k : TSyntax `term) :
    CommandElabM (TSyntax `term × TSyntax `term × Array (Name × TSyntax `term)) := do
  if sites.isEmpty then return ← insideInterfaces insides used k
  let (rand, randAdmits, randCalls) ← insideInterfaces sites used k
  if !converting then return (rand, randAdmits, randCalls)
  let (declared, declaredAdmits, declaredCalls) ← insideInterfaces insides used k
  let leftCalls ← declaredCalls.mapM fun (n, l) => return (n, ← `(Sum.inl $l))
  let rightCalls ← randCalls.mapM fun (n, l) => return (n, ← `(Sum.inr $l))
  return (← `(Interface.tensor $declared $rand),
    ← `(parallelInputs_of_length_le $declaredAdmits $randAdmits), leftCalls ++ rightCalls)

/-- The port map of a converter with one declared inside interface: for each procedure, the
inside label it calls, if any, with that label's name. It exists when each procedure calls at
most one inside label and distinct procedures call distinct labels. -/
def insidePortMap (oracles : Array Syntax) (calls : Array (Name × TSyntax `term)) :
    Option (Array (Ident × Option (Name × TSyntax `term))) := Id.run do
  let mut entries := #[]
  let mut taken : Array Name := #[]
  for p in oracles do
    let called := (identifiers p).foldl (fun acc n =>
      match calls.find? (·.1 == n) with
      | some c => if acc.any (·.1 == c.1) then acc else acc.push c
      | none => acc) #[]
    if called.size > 1 then return none
    let entry := called[0]?
    if let some c := entry then
      if taken.contains c.1 then return none
      taken := taken.push c.1
    entries := entries.push ((⟨p[1]⟩ : Ident), entry)
  return some entries

/-- The per-port typing of a component: a system at every per-port budget, and a converter
whose single inside port has its outside interface, when each procedure calls only its own
inside port, at most once; or whose single inside port has another interface, each of whose
labels one procedure calls, at most once, the other procedures calling none: its budget at a
label is that procedure's (`insideBudget`), along the port map `portMap`. The declarations are
kept only if they elaborate. -/
def elabPerPortDecls (converting : Bool) (name : Ident)
    (params : Array (TSyntax ``Term.bracketedBinder)) (σ : Signature)
    (insides sites oracles : Array Syntax) (used : Array Name) : CommandElabM Unit := do
  let q := Lean.mkIdent `budget
  let some sigPP ← σ.perPortAt q | return
  let args := binderArgs params
  let sigZero ← σ.at (← `(0))
  let bodyName := Lean.mkIdent (name.getId ++ `body)
  let boundName := Lean.mkIdent (name.getId ++ `bound)
  let boundSpecName := Lean.mkIdent (name.getId ++ `bound_spec)
  let randomnessName := Lean.mkIdent (name.getId ++ `randomness)
  let preservingName := Lean.mkIdent (name.getId ++ `preserving)
  let programName := Lean.mkIdent (name.getId ++ `perPortProgram)
  let perPortName := Lean.mkIdent (name.getId ++ `perPort)
  let k ← `($boundName $args* * ∑ i, $q i)
  let saved ← get
  let before ← errorCount
  try
    if !converting then
      let (randK, admitsK, _) ← insideInterfaces sites used k
      elabCommand (← `(noncomputable def $perPortName:ident $params:bracketedBinder*
          {$q : ($sigZero).I → ℕ} : Interface.Resource $sigPP :=
        (Interface.Converter.ofProgram none ($bodyName $args*) ($boundSpecName $args*) $admitsK :
          $sigPP ⟶ $randK) • $randomnessName $args* $k))
    else
      let some declared := σ.declared | return
      unless insides.size == 1 do return
      let insideTy : TSyntax `term := ⟨(insides[0]!)[3]⟩
      let wrap (l : TSyntax `term) : CommandElabM (TSyntax `term) :=
        if sites.isEmpty then pure l else `(Sum.inl $l)
      -- The inside interface at its per-port budget `qIn`, the port map `ι`, and, for an inside
      -- history within the budgets of the port map, its budget at each inside label.
      let (insidePP, qIn, ι, within) ← if insideTy.raw.structEq declared.raw then
          let o := Lean.mkIdent `o
          pure (sigPP, ← `($q), ← `(fun $o:ident => some $(← wrap o)),
            ← `(fun $o:ident => hc $o:ident _ rfl))
        else do
          let (_, _, declaredCalls) ← insideInterfaces insides used (← `(0))
          let some entries := insidePortMap oracles declaredCalls | return
          let qAlts ← entries.filterMapM fun (o, e) => e.mapM fun (_, l) =>
            `(Term.matchAltExpr| | $l => $q .$o:ident)
          let insideBudgetName := Lean.mkIdent (name.getId ++ `insideBudget)
          let qIn ← `($insideBudgetName $args* $q)
          let some insidePP ← ({ σ with declared := some insideTy } : Signature).perPortAt qIn
            | return
          elabCommand (← `(def $insideBudgetName:ident $params:bracketedBinder*
              ($q : ($sigZero).I → ℕ) : ($insideTy 0).I → ℕ := fun j => match j with $qAlts:matchAlt*))
          let ιAlts ← entries.mapM fun (o, e) => do
            match e with
            | some (_, l) => `(Term.matchAltExpr| | .$o:ident => some $(← wrap l))
            | none => `(Term.matchAltExpr| | .$o:ident => none)
          let withinAlts ← entries.filterMapM fun (o, e) => e.mapM fun (_, l) =>
            `(Term.matchAltExpr| | $l => hc .$o:ident _ rfl)
          pure (insidePP, qIn, ← `(fun o => match o with $ιAlts:matchAlt*),
            ← `(fun j => match j with $withinAlts:matchAlt*))
      let (innerZero, _, _) ← componentInside converting insides sites used (← `(0))
      let portMapName := Lean.mkIdent (name.getId ++ `portMap)
      elabCommand (← `(def $portMapName:ident $params:bracketedBinder* :
          ($sigZero).I → Option ($innerZero).I := $ι))
      elabCommand (← `(set_option Elab.async false in
        theorem $preservingName:ident $params:bracketedBinder* :
          ($bodyName $args*).PortPreserving ($portMapName $args*) := by
        unfold $bodyName:ident $portMapName:ident
        program_preserving))
      let (innerPP, admitsPP) ← if sites.isEmpty then
          pure (insidePP, ← `(fun _ hne _ hc => ⟨hne, $within⟩))
        else do
          let (randK, admitsK, _) ← insideInterfaces sites used k
          pure (← `(Interface.tensor $insidePP $randK),
            ← `(fun ys hne hl hc => Interface.perPort_tensor_admits (A := $insidePP) (B := $randK)
              $qIn (fun _ hne' hc' => ⟨hne', hc'⟩) $admitsK ys hne hl $within))
      elabCommand (← `(noncomputable def $programName:ident $params:bracketedBinder*
          {$q : ($sigZero).I → ℕ} : $sigPP ⟶ $innerPP :=
        Interface.Converter.ofPreservingProgram none ($bodyName $args*) ($boundSpecName $args*)
          ($portMapName $args*) ($preservingName $args*) $q (fun _ hd => hd.2) $admitsPP))
      if sites.isEmpty then
        elabCommand (← `(noncomputable def $perPortName:ident $params:bracketedBinder*
            {$q : ($sigZero).I → ℕ} : $sigPP ⟶ $insidePP := $programName $args* (budget := $q)))
      else
        elabCommand (← `(noncomputable def $perPortName:ident $params:bracketedBinder*
            {$q : ($sigZero).I → ℕ} : $sigPP ⟶ $insidePP :=
          CategoryTheory.CategoryStruct.comp ($programName $args* (budget := $q))
            (Interface.rightContext $insidePP ($randomnessName $args* $k))))
    if (← errorCount) > before then set saved
  catch _ => set saved

/-- The inside interface of a sampling site: a source of the law's type. -/
def siteDecl (site : Site) (lawName : Ident) (args : Array (TSyntax `term)) :
    CommandElabM Syntax := do
  let ty ← `(Unit → lawType ($lawName $args*))
  return Syntax.node .none ``insideDecl
    #[Syntax.atom .none "inside ", site.name.raw, Syntax.atom .none " : ", ty.raw]

/-- The parallel composition of the sources of the sites at budget `k`. -/
def sourcesAt (lawNames : Array Ident) (args : Array (TSyntax `term)) (k : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  let mut result ← `(Interface.Resource.source ($(lawNames.back!) $args*) $k)
  for law in lawNames.pop.reverse do
    result ← `(Interface.parallel (Interface.Resource.source ($law $args*) $k) $result)
  return result

/-- The declarations of a component compiled to a program: its body, its inferred per-call
bound, its program from the outside budget `q` to `bound · q` inside queries, and its sources. -/
def elabProgramDecls (converting : Bool) (name : Ident) (params : Array (TSyntax ``Term.bracketedBinder))
    (σ : Signature) (insides sites : Array Syntax) (lawNames : Array Ident) (used : Array Name)
    (state : Ident) (alts : Array (TSyntax ``Term.matchAlt)) (innerZero stateTy : TSyntax `term)
    (displayedBound : Option Nat) : CommandElabM Unit := do
  let args := binderArgs params
  let budget := Lean.mkIdent `budget
  let sigZero ← σ.at (← `(0))
  let bodyName := Lean.mkIdent (name.getId ++ `body)
  let boundedName := Lean.mkIdent (name.getId ++ `bounded)
  let boundName := Lean.mkIdent (name.getId ++ `bound)
  let boundSpecName := Lean.mkIdent (name.getId ++ `bound_spec)
  let programName := Lean.mkIdent (name.getId ++ `program)
  let randomnessName := Lean.mkIdent (name.getId ++ `randomness)
  elabCommand (← `(noncomputable def $bodyName:ident $params:bracketedBinder* :
      Program (Option $stateTy) ($sigZero).I ($innerZero).I ($sigZero).X
        ($sigZero).Y ($innerZero).X ($innerZero).Y :=
    fun $state:ident i => match i with $alts:matchAlt*))
  -- The bound read off the displayed calls, when the procedures have no loops.
  let mut displayed := false
  if let some n := displayedBound then
    let saved ← get
    let before ← errorCount
    try
      elabCommand (← `(abbrev $boundName:ident $params:bracketedBinder* : ℕ := $(quote n)))
      elabCommand (← `(set_option Elab.async false in
        theorem $boundSpecName:ident $params:bracketedBinder* :
            ($bodyName $args*).Bounded ($boundName $args*) := by
          unfold $bodyName:ident
          intro s i x
          cases i <;> dsimp <;> program_bound))
      if (← errorCount) > before then set saved else displayed := true
    catch _ => set saved
  unless displayed do
    elabCommand (← `(theorem $boundedName:ident $params:bracketedBinder* :
        ∃ b, ($bodyName $args*).Bounded b := by
      unfold $bodyName:ident
      program_bounded $sigZero))
    elabCommand (← `(noncomputable def $boundName:ident $params:bracketedBinder* : ℕ :=
      @Nat.find _ (Classical.decPred _) ($boundedName $args*)))
    elabCommand (← `(theorem $boundSpecName:ident $params:bracketedBinder* :
        ($bodyName $args*).Bounded ($boundName $args*) :=
      @Nat.find_spec _ (Classical.decPred _) ($boundedName $args*)))
  let k ← `($boundName $args* * $budget)
  let (innerK, admitsK, _) ← componentInside converting insides sites used k
  let sigB ← σ.at budget
  elabCommand (← `(noncomputable def $programName:ident $params:bracketedBinder* {$budget : ℕ} :
      $sigB ⟶ $innerK :=
    Interface.Converter.ofProgram none ($bodyName $args*) ($boundSpecName $args*) $admitsK))
  if !sites.isEmpty then
    -- A hygienic name, so the budget of the sources captures no parameter of the component.
    let q := Lean.mkIdent (← liftMacroM (Lean.Macro.addMacroScope `sourceBudget))
    let (randQ, _, _) ← insideInterfaces sites used q
    elabCommand (← `(noncomputable def $randomnessName:ident $params:bracketedBinder* ($q : ℕ) :
        Interface.Resource $randQ := $(← sourcesAt lawNames args q)))
  if converting then
    let (declK, _, _) ← insideInterfaces insides used k
    if sites.isEmpty then
      elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
          $sigB ⟶ $declK := $programName $args* (budget := $budget)))
    else
      elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
          $sigB ⟶ $declK :=
        CategoryTheory.CategoryStruct.comp ($programName $args* (budget := $budget))
          (Interface.rightContext $declK ($randomnessName $args* $k))))
  else
    elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
        Interface.Resource $sigB :=
      $programName $args* (budget := $budget) • $randomnessName $args* $k))

/-- The exact typing of a converter that samples nothing, when its number of inside calls is
a function of the input: the outside query budget restricted to total cost `q` into `q` inside
queries. The declarations are kept only if the inferred count elaborates and is proved. -/
def elabExactDecls (name : Ident) (params : Array (TSyntax ``Term.bracketedBinder))
    (σ : Signature) (insides : Array Syntax) (used : Array Name)
    (oracles : Array Syntax) (bodies : Array (Array Syntax))
    (calls : Array (Name × TSyntax `term)) (input : Ident) : CommandElabM Unit := do
  let args := binderArgs params
  let budget := Lean.mkIdent `budget
  let queries := Lean.mkIdent `queries
  let sigZero ← σ.at (← `(0))
  let bodyName := Lean.mkIdent (name.getId ++ `body)
  let boundSpecName := Lean.mkIdent (name.getId ++ `bound_spec)
  let costName := Lean.mkIdent (name.getId ++ `cost)
  let costsName := Lean.mkIdent (name.getId ++ `costs)
  let exactName := Lean.mkIdent (name.getId ++ `exact)
  let saved ← get
  let before ← errorCount
  try
    let mut costAlts : Array (TSyntax ``Term.matchAlt) := #[]
    for (procedure, body) in oracles.zip bodies do
      let procArgs : Array Ident := procedure[3].getSepArgs.map (fun a => ⟨a[0]⟩)
      let label ← if σ.declared.isSome then `(.$(⟨procedure[1]⟩):ident)
        else pure (⟨(Lean.mkIdent (name.getId ++ `Port ++ procedure[1].getId)).raw⟩ : TSyntax `term)
      let mut c ← costOf body calls
      if !procArgs.isEmpty then
        let pat ← tupleTerm (procArgs.map fun x => ⟨x.raw⟩)
        c ← `(let $pat:term := $input:ident; $c)
      costAlts := costAlts.push (← `(matchAltExpr| | $label:term => fun $input:ident => ($c : ℕ)))
    elabCommand (← `(noncomputable def $costName:ident $params:bracketedBinder* :
        ∀ i, ($sigZero).X i → ℕ := fun i => match i with $costAlts:matchAlt*))
    elabCommand (← `(set_option Elab.async false in
      theorem $costsName:ident $params:bracketedBinder* :
        ($bodyName $args*).Costs (fun x => $costName $args* x.1 x.2) := by
      intro s i x
      cases i <;> simp only [$bodyName:ident, $costName:ident] <;> program_cost))
    let (innerB, admitsB, _) ← insideInterfaces insides used budget
    let sigQ ← σ.at queries
    let outside ← `(Interface.restrict $sigQ
      (fun h => (h.map fun x => $costName $args* x.1 x.2).sum ≤ $budget) (cost_prefix_closed _ _))
    elabCommand (← `(noncomputable def $exactName:ident $params:bracketedBinder*
        {$budget $queries : ℕ} : $outside ⟶ $innerB :=
      Interface.Converter.ofCostedProgram none ($bodyName $args*) ($boundSpecName $args*)
        (fun x => $costName $args* x.1 x.2) ($costsName $args*) (fun _ hd => hd.2) $admitsB))
    if (← errorCount) > before then set saved
  catch _ => set saved

/-- The port label, the input type and the reply type of a procedure. -/
def procedureSignature (name : Ident) (typed : Bool) (persistent : Array Ident)
    (procedure : Syntax) :
    CommandElabM (Array Ident × TSyntax `term × TSyntax `term × TSyntax `term) := do
  if !returns procedure[7] then throwErrorAt procedure "Every procedure path must return a reply."
  let procArgs : Array Ident := procedure[3].getSepArgs.map (fun a => ⟨a[0]⟩)
  for a in procArgs do
    if persistent.any (·.getId == a.getId) then
      throwErrorAt a "Oracle parameter shadows persistent binding."
  let label ← if typed then `(.$(⟨procedure[1]⟩):ident)
    else pure (⟨(Lean.mkIdent (name.getId ++ `Port ++ procedure[1].getId)).raw⟩ : TSyntax `term)
  let types : Array (TSyntax `term) := procedure[3].getSepArgs.map (fun a => ⟨a[2]⟩)
  let mut argType ← `(Unit)
  if !types.isEmpty then
    argType := types.back!
    for t in types.pop.reverse do argType ← `($t × $argType)
  return (procArgs, label, argType, ⟨procedure[6]⟩)

/-- The step of a procedure of a system that samples nothing. -/
def systemAlt (name : Ident) (typed : Bool) (persistent : Array Ident) (stored : TSyntax `term)
    (state input : Ident) (procedure : Syntax) : CommandElabM (TSyntax ``Term.matchAlt) := do
  let (procArgs, label, argType, resultType) ← procedureSignature name typed persistent procedure
  let checkedBody ← annotateReturns procedure[7] resultType
  let mut body ← lowerFunction (statements checkedBody) (persistent ++ procArgs) persistent
    #[] ⟨.missing⟩ .system
  if !procArgs.isEmpty then
    let pat ← tupleTerm (procArgs.map fun x => ⟨x.raw⟩)
    body ← `(let $pat:term := $input:ident; $body)
  if !persistent.isEmpty then body ← `(let $stored:term := $state:ident; $body)
  `(matchAltExpr| | $label:term => fun ($input:ident : $argType) => ($body : _ × $resultType))

/-- The program of a procedure: initialization first when no bindings are stored yet. -/
def programAlt (name : Ident) (typed : Bool) (persistent : Array Ident) (stored : TSyntax `term)
    (state input : Ident) (calls : Array (Name × TSyntax `term)) (initD : Array Syntax)
    (resultOf : TSyntax `term → CommandElabM (TSyntax `term)) (procedure : Syntax)
    (bodyD : Array Syntax) : CommandElabM (TSyntax ``Term.matchAlt) := do
  let (procArgs, label, argType, resultType) ← procedureSignature name typed persistent procedure
  let checked ← bodyD.mapM (annotateReturns · resultType)
  let resumed ← lowerFunction checked (persistent ++ procArgs) persistent calls ⟨.missing⟩ .program
  let first ← lowerFunction (initD ++ checked) procArgs persistent calls ⟨.missing⟩ .program
  let mut body ← `(match $state:ident with
    | some $stored:term => $resumed
    | none => $first)
  if !procArgs.isEmpty then
    let pat ← tupleTerm (procArgs.map fun x => ⟨x.raw⟩)
    body ← `(let $pat:term := $input:ident; $body)
  `(matchAltExpr| | $label:term => fun ($input:ident : $argType) =>
    ($body : $(← resultOf resultType)))

@[command_elab systemComponentDecl, command_elab systemComponentTypedDecl,
  command_elab converterDecl, command_elab converterTypedDecl]
def elabComponent : CommandElab := fun stx => do
  checkReserved stx
  let converting := stx.getKind == ``converterDecl || stx.getKind == ``converterTypedDecl
  let typed := stx.getKind == ``systemComponentTypedDecl || stx.getKind == ``converterTypedDecl
  let name : Ident := ⟨stx[1]⟩
  let members := stx[if typed then 5 else 3][0].getArgs
  let proofBlock := if converting then Syntax.missing else stx[if typed then 6 else 4]
  let oracles := members.filter (·.getKind == ``oracleDecl)
  if oracles.isEmpty then throwError "A system must declare at least one procedure."
  let ports := oracles.map fun p =>
    ((⟨p[1]⟩ : Ident), p[3].getSepArgs, (⟨p[6]⟩ : TSyntax `term))
  let (labels, inputs, outputs, params, fx, fy) ← if typed then do
      let sig : TSyntax `term := ⟨stx[4]⟩
      pure (← `(($sig 0).I), ← `(($sig 0).X), ← `(($sig 0).Y), ← parameterBinders stx[2].getArgs,
        ← `(inferInstance), ← `(inferInstance))
    else declareInterface name stx[2].getArgs ports
  let mut params := params
  for m in members do
    if m.getKind == ``requiresDecl then
      params := params.push (← `(bracketedBinder| ($(⟨m[1]⟩):ident : $(⟨m[3]⟩):term)))
    else if !converting && m.getKind == ``insideDecl then
      throwErrorAt m "Inside ports belong to converters."
  let args := binderArgs params
  let domains := members.filter (·.getKind == ``domainDecl)
  if domains.size > 1 then throwError "Declare the domain only once."
  if !domains.isEmpty && (typed || converting) then
    throwError "Use an exact domain on an unannotated system declaration."
  if !domains.isEmpty && proofBlock.isNone then
    throwError "An explicit domain requires a proof of nonempty prefix closure in `by`."
  let exactDomain ← if domains.isEmpty then pure none else do
    let d := domains[0]!
    pure (some ((⟨d[1]⟩ : Ident), (⟨d[3]⟩ : TSyntax `term),
      ← `(by $(⟨proofBlock[1]⟩):tacticSeq)))
  let σ : Signature := {
    declared := if typed then some ⟨stx[4]⟩ else none
    labels, inputs, outputs, fintypeInputs := fx, fintypeOutputs := fy, exactDomain }
  let sigAt := σ.at
  let budget := Lean.mkIdent `budget
  let outerName := Lean.mkIdent (name.getId ++ `outer)
  elabCommand (← `(abbrev $outerName:ident $params:bracketedBinder* (q : ℕ) : Interface :=
    $(← sigAt (← `(q)))))
  let sigZero ← sigAt (← `(0))
  let inits := members.filter (·.getKind == ``initializeDecl)
  if inits.size > 1 then throwError "Declare initialization only once."
  let initStatements := if inits.isEmpty then #[] else statements (inits[0]!)[1]
  let mut persistent : Array Ident := #[]
  for s in initStatements do
    if s.getKind == ``assignStmt || s.getKind == ``sampleStmt then
      for x in targetNames s[0] do
        if !persistent.any (·.getId == x.getId) then persistent := persistent.push x
  let stored ← tupleTerm (persistent.map fun x => ⟨x.raw⟩)
  -- The initial bindings, each sample replaced by a value of its law: their type is the state.
  let initName := Lean.mkIdent (name.getId ++ `initial)
  let insides := members.filter (·.getKind == ``insideDecl)
  let used := members.flatMap identifiers
  let (_, _, declaredCalls) ← insideInterfaces insides used (← `(0))
  let template ← lowerFunction initStatements #[] #[] declaredCalls stored .template
  elabCommand (← `(noncomputable def $initName:ident $params:bracketedBinder* := $template))
  -- The type of the private bindings, from the initial bindings themselves.
  let stateTy ← `(TypeOf $template)
  -- Every sampling statement becomes a call to a source.
  let procArgNames := oracles.flatMap fun p => p[3].getSepArgs.map (·[0].getId)
  let bindings := persistent.map (·.getId) ++ procArgNames ++ members.flatMap boundNames
  let (initD, sites₀) ← (desugarSampling bindings initStatements).run #[]
  let mut siteList := sites₀
  let mut bodies : Array (Array Syntax) := #[]
  for procedure in oracles do
    let (b, s') ← (desugarSampling bindings (statements procedure[7])).run siteList
    siteList := s'
    bodies := bodies.push b
  let lawNames := (Array.range siteList.size).map fun i =>
    Lean.mkIdent (name.getId ++ Name.mkSimple s!"law{i + 1}")
  for (site, law) in siteList.zip lawNames do
    elabCommand (← `(noncomputable def $law:ident $params:bracketedBinder* := $(site.law)))
  let sites ← (siteList.zip lawNames).mapM fun (site, law) => siteDecl site law args
  let state := Lean.mkIdent (← liftCoreM <| mkFreshUserName `stored)
  let input := Lean.mkIdent (← liftCoreM <| mkFreshUserName `query)
  -- A system that samples nothing is the deterministic system of its program.
  if !converting && siteList.isEmpty then
    let alts ← oracles.mapM fun procedure =>
      systemAlt name typed persistent stored state input procedure
    let sig ← sigAt budget
    let stepName := Lean.mkIdent (name.getId ++ `step)
    elabCommand (← `(noncomputable def $stepName:ident $params:bracketedBinder* :
        $stateTy → (i : ($sigZero).I) → ($sigZero).X i → $stateTy × ($sigZero).Y i :=
      fun $state:ident i => match i with $alts:matchAlt*))
    elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
        Interface.Resource $sig :=
      Interface.Resource.ofAutomaton $sig ($stepName $args*)
        (Probability.Distribution.ProbDist.single ($initName $args*))))
    let q := Lean.mkIdent `budget
    if let some sigPP ← σ.perPortAt q then
      let perPortName := Lean.mkIdent (name.getId ++ `perPort)
      elabCommand (← `(noncomputable def $perPortName:ident $params:bracketedBinder*
          {$q : ($sigZero).I → ℕ} : Interface.Resource $sigPP :=
        Interface.Resource.ofAutomaton $sigPP ($stepName $args*)
          (Probability.Distribution.ProbDist.single ($initName $args*))))
    return
  let (innerZero, _, calls) ← componentInside converting insides sites used (← `(0))
  let resultOf (resultType : TSyntax `term) : CommandElabM (TSyntax `term) :=
    `(List ((Sigma ($innerZero).X) × (Sigma ($innerZero).Y)) →
        (Option $stateTy × $resultType) ⊕ Sigma ($innerZero).X)
  let alts ← (oracles.zip bodies).mapM fun (procedure, bodyD) =>
    programAlt name typed persistent stored state input calls initD resultOf procedure bodyD
  let counts := bodies.map fun b => callCount (initD ++ b) calls
  let displayedBound := if counts.all Option.isSome then
      some (counts.foldl (fun m c => max m (c.getD 0)) 0)
    else none
  elabProgramDecls converting name params σ insides sites lawNames used state alts innerZero stateTy
    displayedBound
  elabPerPortDecls converting name params σ insides sites oracles used
  if converting && sites.isEmpty then
    elabExactDecls name params σ insides used oracles bodies calls input

/-- A domain filter: forward the queries whose input history is admitted, and stop on the
others. -/
@[command_elab filterDecl] def elabFilter : CommandElab := fun stx => do
  checkReserved stx
  let name : Ident := ⟨stx[1]⟩
  let params ← parameterBinders stx[2].getArgs
  let sig : TSyntax `term := ⟨stx[4]⟩
  let bound : Ident := ⟨stx[6]⟩
  let admits : TSyntax `term := ⟨stx[8]⟩
  let proofBlock := stx[9]
  let closed ← if proofBlock.isNone then
      `(by
          intro p h hp hh
          obtain ⟨e, he⟩ := hp
          subst he
          simp only [List.map_append, List.sum_append, List.length_append] at hh ⊢
          omega)
    else `(by $(⟨proofBlock[1]⟩):tacticSeq)
  let budget := Lean.mkIdent `budget
  let outerName := Lean.mkIdent (name.getId ++ `outer)
  elabCommand (← `(abbrev $outerName:ident $params:bracketedBinder* (q : ℕ) : Interface :=
    Interface.restrict ($sig q) (fun $bound:ident => $admits) $closed))
  elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
      Interface.restrict ($sig $budget) (fun $bound:ident => $admits) $closed ⟶ ($sig $budget) :=
    Interface.filter ($sig $budget) (fun $bound:ident => $admits) $closed))

/-- The outside interface family of a system expression at budget `k`: the outer family of
its outermost component. -/
partial def outerOf (e : TSyntax `term) (k : TSyntax `term) : CommandElabM (Option (TSyntax `term)) := do
  match e with
  | `(($e)) => outerOf e k
  | `($α • $_) => outerOf α k
  | `($α ≫ $_) => outerOf α k
  | `($a ∥ $b) => do
    let some x ← outerOf a k | return none
    let some y ← outerOf b k | return none
    return some (← `(Interface.tensor $x $y))
  | `($a ⊗ₘ $b) => do
    let some x ← outerOf a k | return none
    let some y ← outerOf b k | return none
    return some (← `($x ⊗ $y))
  | `($f:ident $args*) => return some (← `($(Lean.mkIdent (f.getId ++ `outer)) $args* $k))
  | `($f:ident) => return some (← `($(Lean.mkIdent (f.getId ++ `outer)) $k))
  | _ => return none

/-- Whether a system expression denotes a converter rather than a resource. -/
partial def isConverterExpr (e : TSyntax `term) : Bool :=
  match e with
  | `(($e)) => isConverterExpr e
  | `($_ ≫ $_) | `($_ ⊗ₘ $_) => true
  | _ => false

@[command_elab systemDecl] def elabSystem : CommandElab := fun stx => do
  checkReserved stx
  let params ← parameterBinders stx[2].getArgs
  let name : Ident := ⟨stx[1]⟩
  let rhs : TSyntax `term := ⟨stx[4]⟩
  let budget := Lean.mkIdent `budget
  match ← outerOf rhs budget with
  | some outer =>
    if isConverterExpr rhs then
      elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :=
        ($rhs : $outer ⟶ _)))
    else
      elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* {$budget : ℕ} :
          Interface.Resource $outer := $rhs))
    let outerName := Lean.mkIdent (name.getId ++ `outer)
    let outerQ ← outerOf rhs (← `(q))
    if let some o := outerQ then
      elabCommand (← `(noncomputable abbrev $outerName:ident $params:bracketedBinder* (q : ℕ) :
        Interface := $o))
  | none =>
    elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* := $rhs))

end SystemAlgebra.DSL

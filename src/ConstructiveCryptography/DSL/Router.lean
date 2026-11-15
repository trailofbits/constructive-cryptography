module

public import ConstructiveCryptography.DSL.Elaborator
public import RandomSystems.Typed.QueryRouting

/-!
# One-call router declarations

A procedure sends one request and translates its reply. The declaration elaborates to
`TypedConverter.routingAt` with the generated tables `C.request`, `C.answer` and the
domain certificate `C.request_domain`. Attachment laws therefore apply to the named router.
-/

@[expose] public meta section

namespace SystemAlgebra.DSL

open Lean Elab Command Parser Term

/-- A step of the path from the labels of an interface to one of its ports: the left or the right
component of a tensor, a member of a family, or an index of an indexed port (a field of the
port's constructor, as `derive l`). -/
inductive PortStep
  | inl
  | inr
  | member
  | index
  deriving BEq, Inhabited

/-- The steps of a path that a procedure or a call names by an argument: the members of the
families and the indices of the port. -/
def PortStep.named : PortStep → Bool
  | .member | .index => true
  | _ => false

/-- **Ports by name.** The paths in the label type `ty` to the ports named `port`: through the
components `⊕` of tensors and the members `Σ` of families, to the constructor `port` of a label
type. A constructor with fields is an indexed port (a port family over the fields' types, as
`derive (l : L)`), and its fields are the last steps of the path. With supplied arguments, the
members and indices on a path consume the leading arguments in order, so that a name shared by two
components is told apart by the members its procedure names first. -/
partial def portPaths (ty : Expr) (port : Name) (members : Option (List Expr)) :
    MetaM (Array (List PortStep × Name)) := do
  let ty ← Meta.whnf ty
  if ty.isAppOfArity ``Sum 2 then
    let left ← portPaths ty.appFn!.appArg! port members
    let right ← portPaths ty.appArg! port members
    return left.map (fun (p, c) => (PortStep.inl :: p, c)) ++
      right.map (fun (p, c) => (PortStep.inr :: p, c))
  if ty.isAppOfArity ``Sigma 2 then
    let index := ty.appFn!.appArg!
    let descend (m : Expr) (rest : Option (List Expr)) := do
      let inner ← portPaths (mkApp ty.appArg! m) port rest
      return inner.map fun (p, c) => (PortStep.member :: p, c)
    match members with
    | none => return ← Meta.withLocalDeclD `member index fun m => descend m none
    | some [] => return #[]
    | some (m :: ms) =>
      unless ← Meta.isDefEq index (← Meta.inferType m) do return #[]
      return ← descend m (some ms)
  if let .const n _ := ty.getAppFn then
    let ctor := n ++ port
    if let some (.ctorInfo cv) := (← getEnv).find? ctor then
      if cv.numFields == 0 then return #[([], ctor)]
      -- An indexed port: one index per field, of the field's type.
      let fields ← Meta.instantiateForall cv.type (ty.getAppArgs.extract 0 cv.numParams)
      if let some xs := members then
        if xs.length < cv.numFields then return #[]
        let mut telescope := fields
        for x in xs.take cv.numFields do
          let .forallE _ dom body _ ← Meta.whnf telescope | return #[]
          unless ← Meta.isDefEq dom (← Meta.inferType x) do return #[]
          telescope := body.instantiate1 x
      return #[(List.replicate cv.numFields .index, ctor)]
  return #[]

/-- The path to the port `port` in the labels of the interface `I`, elaborated in the context of
`params`. With a procedure's arguments `arguments`, as
binders (a later type may read an earlier argument, as `x : Q l` after an index `l`), the path
must uniquely match the leading members and indices. -/
def uniquePortPath (params : Array (TSyntax ``Term.bracketedBinder)) (I : TSyntax `term)
    (port : Ident) (arguments : Option (Array (TSyntax ``Term.bracketedBinder))) :
    CommandElabM (List PortStep × Name) := do
  let found ← runTermElabM fun _ => Term.elabBinders (params.map (·.raw)) fun _ => do
    let labels ← Term.elabTerm (← `(Interface.I $I)) none
    Term.synthesizeSyntheticMVarsNoPostponing
    let labels ← instantiateMVars labels
    match arguments with
    | none => portPaths labels port.getId none
    | some bs => Term.elabBinders (bs.map (·.raw)) fun xs => do
      portPaths labels port.getId (some xs.toList)
  match found with
  | #[path] => return path
  | #[] => throwErrorAt port m!"No port `{port.getId}` in `{I}`."
  | _ => throwErrorAt port m!"Ambiguous port `{port.getId}`: several component paths match."

/-- Path to component `i` of the declared right-associated tensor of `n` inside interfaces. -/
def componentPath (i n : Nat) : List PortStep :=
  List.replicate i .inr ++ (if i + 1 < n then [.inl] else [])

/-- The label of the port at the path `p` with the constructor `c`, the members and indices `ms`
on the path in order; the indices are the constructor's arguments. -/
def pathLabel : List PortStep → Name → List (TSyntax `term) → CommandElabM (TSyntax `term)
  | [], c, _ => pure ⟨(mkIdent (`_root_ ++ c)).raw⟩
  | .inl :: p, c, ms => do `(Sum.inl $(← pathLabel p c ms))
  | .inr :: p, c, ms => do `(Sum.inr $(← pathLabel p c ms))
  | .member :: p, c, m :: ms => do `(Sigma.mk $m $(← pathLabel p c ms))
  | .member :: _, _, [] => throwError "A port of a family names its member first."
  | p@(.index :: _), c, ms => do
    if ms.length < p.length then throwError "An indexed port names its indices first."
    let ctor : TSyntax `term := ⟨(mkIdent (`_root_ ++ c)).raw⟩
    `($ctor $(ms.take p.length |>.toArray)*)

/-- The two defining equations of an outside port at its indices and query. -/
structure RouterClause where
  /-- The two branches inserted into the dependent request and answer tables. -/
  requestAlt : TSyntax ``Term.matchAlt
  answerAlt : TSyntax ``Term.matchAlt
  port : Ident
  binders : Array (TSyntax ``Term.bracketedBinder)
  query : TSyntax `term
  request : TSyntax `term
  reply : Ident
  replyBinder : TSyntax ``Term.bracketedBinder
  result : TSyntax `term

/-- Each equation specializes the corresponding table at the port's concrete label. -/
def elabRouterEquations (owner : Ident) (params : Array (TSyntax ``Term.bracketedBinder))
    (request answer : Ident) (clauses : Array RouterClause) : CommandElabM Unit := do
  let args := binderArgs params
  let mut seen : Std.HashMap Name Nat := {}
  for c in clauses do
    let port := c.port.getId
    let n := seen.getD port 0 + 1
    seen := seen.insert port n
    let suffix := if clauses.countP (·.port.getId == port) == 1 then port.toString
      else s!"{port}_{n}"
    let reqEq := mkIdent (owner.getId ++ Name.mkSimple s!"request_{suffix}")
    let ansEq := mkIdent (owner.getId ++ Name.mkSimple s!"answer_{suffix}")
    let binders := params ++ c.binders
    elabCommand (← `(theorem $reqEq:ident $binders:bracketedBinder* :
      $request $args* $(c.query) = $(c.request) := rfl))
    let replyBinder := c.replyBinder
    elabCommand (← `(theorem $ansEq:ident $binders:bracketedBinder* $replyBinder:bracketedBinder :
      $answer $args* $(c.query) $(c.reply) = $(c.result) := rfl))

/-- The binder `x`, or `_` when the names `uses` do not read it. -/
def bindingOr (uses : Array Name) (x : TSyntax `term) : CommandElabM (TSyntax `term) :=
  if uses.any (·.getRoot == x.raw.getId) then pure x else `(_)

/-- `let pat := v; body`, binding only the names `body` reads, and nothing when it reads none. -/
def letReading (uses : Array Name) (xs : Array (TSyntax `term)) (v body : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  if !xs.any (fun x => uses.any (·.getRoot == x.raw.getId)) then return body
  let pat ← tupleTerm (← xs.mapM (bindingOr uses))
  `(let $pat:term := $v; $body)

/-- Compile one clause into the two branches of the routing table and their defining equations. -/
def compileRouterClause (params : Array (TSyntax ``Term.bracketedBinder))
    (outside inside : TSyntax `term) (insides : Array Syntax) (p : Syntax) :
    CommandElabM RouterClause := do
  let input := Lean.mkIdent (← liftCoreM <| mkFreshUserName `query)
  let value := Lean.mkIdent (← liftCoreM <| mkFreshUserName `reply)
  let ss := statements p[7]
  unless ss.size == 2 && ss[0]!.getKind == ``assignStmt &&
      ss[0]!.getArgs[3]!.getKind == ``oracleCall && ss[1]!.getKind == ``returnStmt do
    throwErrorAt p "A procedure of a router makes one call `y ← c.p(…)` and then returns."
  let call := ss[0]!
  let returning := ss[1]!
  let ret : TSyntax `term := ⟨returning[1]⟩
  let procArgs : Array (TSyntax `term) := p[3].getSepArgs.map fun a => ⟨a[0]⟩
  let proc : Ident := ⟨p[1]⟩
  let procBinders ← indexBinders p[3].getSepArgs
  let (outPath, outCtor) ← uniquePortPath params outside proc (some procBinders)
  let nOut := outPath.countP PortStep.named
  let rhs := call[3]
  let callee := rhs[0].getId
  let some i := insides.findIdx? (·[1].getId == callee.getPrefix)
    | throwErrorAt rhs "Call a port of a declared inside interface."
  let port := mkIdent (Name.mkSimple callee.getString!)
  let component := insides[i]!
  let (path, inCtor) ← uniquePortPath params ⟨component[3]⟩ port none
  let inPath := componentPath i insides.size ++ path
  let callArgs : Array (TSyntax `term) := rhs[2].getSepArgs.map (⟨·⟩)
  let nIn := inPath.countP PortStep.named
  if callArgs.size < nIn then throwErrorAt rhs "Supply the family members and port indices first."
  let inLabel ← pathLabel inPath inCtor (callArgs.extract 0 nIn).toList
  let callUses := callArgs.flatMap (identifiers ·.raw)
  -- Input variables may occur in a type annotation as well as in the returned expression.
  let retUses := identifiers ret.raw ++ identifiers p[6] ++ identifiers call[1]
  let target := targetNames call[0]
  let targetTerm ← tupleTerm (target.map fun x => ⟨x.raw⟩)
  -- The request: the inside label and input, reading the procedure's arguments.
  let inInput ← tupleTerm (callArgs.extract nIn callArgs.size)
  let inputArgs := p[3].getSepArgs.extract nOut procArgs.size
  let argumentType ← tupleType (inputArgs.map fun a => ⟨a[2]⟩)
  let outIndices := (procArgs.extract 0 nOut).toList
  let reqUses := callUses ++ identifiers argumentType.raw
  let reqPat ← pathLabel outPath outCtor (← outIndices.mapM (bindingOr reqUses))
  let argsIn := procArgs.extract nOut procArgs.size
  let reqBody ← letReading callUses argsIn input (← `(Sigma.mk $inLabel $inInput))
  let requestAlt ← `(matchAltExpr| | ⟨$reqPat, $input⟩ =>
    let _ : $argumentType := $input; $reqBody)
  let resultType : TSyntax `term := ⟨p[6]⟩
  let returned ← `(($ret : $resultType))
  let readReply ← if !target.any (fun x => retUses.any (·.getRoot == x.getId)) then
      pure returned
    else if call[1].isNone then `(let $targetTerm:term := $value; $returned)
    else `(let $targetTerm:term : $(⟨call[1][1]⟩) := $value; $returned)
  let ansPat ← pathLabel outPath outCtor (← outIndices.mapM (bindingOr retUses))
  let ansBody ← letReading retUses argsIn input readReply
  let answerAlt ← `(matchAltExpr|
    | ⟨$ansPat, $input⟩ => fun $value:ident => $ansBody)
  -- Equations bind every index explicitly. A nullary port accepts an arbitrary Unit input.
  let outLabel ← pathLabel outPath outCtor outIndices
  let (outInput, binders) ← if argsIn.isEmpty then
      let binder ← `(bracketedBinder| ($input : _))
      pure ((⟨input.raw⟩ : TSyntax `term), procBinders.push binder)
    else pure (← tupleTerm argsIn, procBinders)
  let query ← `((Sigma.mk $outLabel $outInput : Σ o, ($outside).X o))
  let replyBinder ← `(bracketedBinder| ($value : ($inside).Y $inLabel))
  return ⟨requestAlt, answerAlt, proc, binders, query, ← `(Sigma.mk $inLabel $inInput), value,
    replyBinder, readReply⟩

/-- Compile each procedure to its request and answer at the selected inside port. -/
@[command_elab routerDecl] def elabRouter : CommandElab := fun stx => do
  checkReserved stx
  let name : Ident := ⟨stx[1]⟩
  let params ← parameterBinders stx[2].getArgs
  let args := binderArgs params
  let outside : TSyntax `term := ⟨stx[4]⟩
  let members := stx[5][0].getArgs
  let oracles := members.filter (·.getKind == ``oracleDecl)
  if oracles.isEmpty then throwError "A router must declare at least one procedure."
  for m in members do
    unless m.getKind == ``oracleDecl || m.getKind == ``insideDecl do
      throwErrorAt m "A router declares an inside interface and one-call procedures."
  let insides := members.filter (·.getKind == ``insideDecl)
  let some last := insides.back? | throwErrorAt name "Declare an inside interface for the router."
  let names := insides.map (·[1].getId)
  unless names.toList.Nodup do throwErrorAt name "Duplicate inside component name."
  let mut inside : TSyntax `term := ⟨last[3]⟩
  let mut admits ← `(fun _ hne hl => ⟨hne, hl⟩)
  for d in insides.pop.reverse do
    inside ← `(Interface.tensor $(⟨d[3]⟩) $inside)
    admits ← `(parallelInputs_of_length_le (fun _ hne hl => ⟨hne, hl⟩) $admits)
  let requestName := Lean.mkIdent (name.getId ++ `request)
  let answerName := Lean.mkIdent (name.getId ++ `answer)
  let domainName := Lean.mkIdent (name.getId ++ `request_domain)
  let clauses ← oracles.mapM (compileRouterClause params outside inside insides)
  let requests := clauses.map (·.requestAlt)
  let answers := clauses.map (·.answerAlt)
  let requestBody ← `(fun u => match u with $requests:matchAlt*)
  elabCommand (← `(noncomputable def $requestName:ident $params:bracketedBinder* :
      (Σ o, ($outside).X o) → Σ j, ($inside).X j := $requestBody))
  elabCommand (← `(noncomputable def $answerName:ident $params:bracketedBinder* :
      (u : Σ o, ($outside).X o) → ($inside).Y ($requestName $args* u).1 → ($outside).Y u.1 :=
    fun u => match u with $answers:matchAlt*))
  let domainProof ← if !stx[6].isNone then `(by $(⟨stx[6][1]⟩):tacticSeq) else
    `(by
      first
      | intro us hus
        have hId : $requestName $args* = id := by
          funext ⟨l, x⟩
          component_cases l <;> rfl
        rw [hId, List.map_id]
        exact hus
      | exact TypedConverter.routingAt_domain_of_length_le _ $admits)
  elabCommand (← `(theorem $domainName:ident $params:bracketedBinder* :
    ∀ us, ($outside).domain us → ($inside).domain (us.map ($requestName $args*)) := $domainProof))
  elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* :
      TypedConverter $outside $inside :=
    TypedConverter.routingAt ($requestName $args*) ($answerName $args*) ($domainName $args*)))
  elabRouterEquations name params requestName answerName clauses

end SystemAlgebra.DSL

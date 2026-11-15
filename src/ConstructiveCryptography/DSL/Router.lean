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

/-- The binder `x`, or `_` when the names `uses` do not read it. -/
def bindingOr (uses : Array Name) (x : TSyntax `term) : CommandElabM (TSyntax `term) :=
  if uses.any (·.getRoot == x.raw.getId) then pure x else `(_)

/-- `let pat := v; body`, binding only the names `body` reads, and nothing when it reads none. -/
def letReading (uses : Array Name) (xs : Array (TSyntax `term)) (v body : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  if !xs.any (fun x => uses.any (·.getRoot == x.raw.getId)) then return body
  let pat ← tupleTerm (← xs.mapM (bindingOr uses))
  `(let $pat:term := $v; $body)

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
  let #[insideDecl] := members.filter (·.getKind == ``insideDecl)
    | throwErrorAt name "Declare one inside interface for the router."
  let inside : TSyntax `term := ⟨insideDecl[3]⟩
  let requestName := Lean.mkIdent (name.getId ++ `request)
  let answerName := Lean.mkIdent (name.getId ++ `answer)
  let domainName := Lean.mkIdent (name.getId ++ `request_domain)
  let input := Lean.mkIdent (← liftCoreM <| mkFreshUserName `query)
  let value := Lean.mkIdent (← liftCoreM <| mkFreshUserName `reply)
  let mut requests : Array (TSyntax ``Term.matchAlt) := #[]
  let mut answers : Array (TSyntax ``Term.matchAlt) := #[]
  for p in oracles do
    let ss := statements p[7]
    unless ss.size == 2 && ss[0]!.getKind == ``assignStmt &&
        ss[0]!.getArgs[3]!.getKind == ``oracleCall && ss[1]!.getKind == ``returnStmt do
      throwErrorAt p "A procedure of a router makes one call `y ← c.p(…)` and then returns."
    let call := ss[0]!
    let returning := ss[1]!
    let ret : TSyntax `term := ⟨returning[1]⟩
    let procArgs : Array (TSyntax `term) := p[3].getSepArgs.map fun a => ⟨a[0]⟩
    let proc : Ident := ⟨p[1]⟩
    let outLabel ← `(.$proc:ident)
    let rhs := call[3]
    let callee := rhs[0].getId
    unless callee.getPrefix == insideDecl[1].getId do
      throwErrorAt rhs "Call a port of the declared inside interface."
    let port := mkIdent (Name.mkSimple callee.getString!)
    let inLabel ← `(.$port:ident)
    let callArgs : Array (TSyntax `term) := rhs[2].getSepArgs.map (⟨·⟩)
    let callUses := callArgs.flatMap (identifiers ·.raw)
    -- Input variables may occur in a type annotation as well as in the returned expression.
    let retUses := identifiers ret.raw ++ identifiers p[6] ++ identifiers call[1]
    let target := targetNames call[0]
    let targetTerm ← tupleTerm (target.map fun x => ⟨x.raw⟩)
    -- The request: the inside label and input, reading the procedure's arguments.
    let inInput ← tupleTerm callArgs
    let argumentType ← tupleType (p[3].getSepArgs.map fun a => ⟨a[2]⟩)
    let reqBody ← letReading callUses procArgs input (← `(Sigma.mk $inLabel $inInput))
    requests := requests.push (← `(matchAltExpr| | ⟨$outLabel, $input⟩ =>
      let _ : $argumentType := $input; $reqBody))
    let resultType : TSyntax `term := ⟨p[6]⟩
    let returned ← `(($ret : $resultType))
    let readReply ← if !target.any (fun x => retUses.any (·.getRoot == x.getId)) then
        pure returned
      else if call[1].isNone then `(let $targetTerm:term := $value; $returned)
      else `(let $targetTerm:term : $(⟨call[1][1]⟩) := $value; $returned)
    let ansBody ← letReading retUses procArgs input readReply
    answers := answers.push (← `(matchAltExpr|
      | ⟨$outLabel, $input⟩ => fun $value:ident => $ansBody))
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
      | exact TypedConverter.routingAt_domain_of_length_le _ (fun _ hne hl => ⟨hne, hl⟩))
  elabCommand (← `(theorem $domainName:ident $params:bracketedBinder* :
    ∀ us, ($outside).domain us → ($inside).domain (us.map ($requestName $args*)) := $domainProof))
  elabCommand (← `(noncomputable def $name:ident $params:bracketedBinder* :
      TypedConverter $outside $inside :=
    TypedConverter.routingAt ($requestName $args*) ($answerName $args*) ($domainName $args*)))

end SystemAlgebra.DSL

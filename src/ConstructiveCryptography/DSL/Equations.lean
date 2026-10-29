import ConstructiveCryptography.DSL.EquationAttributes
import RandomSystems.Typed.Memoryless
import Lean

/-! # Proved equations of component invocations

The compiler supplies one procedure application `lhs`, e.g. `C.body none get x h`, and the rules
that implement it: definitions to unfold (the body or step and the program combinators) and
rewriting lemmas. `component_equation` simplifies `lhs` with only those rules and fixed
`if`/`Sum.elim` reductions, giving `lhs = rhs`. Other definitions and the pure functions called
by the procedure stay opaque. The kernel checks the equality before it enters
`component_equations`.
-/

namespace SystemAlgebra.DSL

open Lean Elab Command Term Meta

/-- Emit the theorem `name : ∀ binders, lhs = rhs`, where `rhs` is obtained using only the
supplied rules, and register it in `component_equations`. This is the compiler's equation
generator; it does not search for mathematical lemmas. -/
elab "component_equation " name:ident binders:bracketedBinder* " : " lhs:term
    " using " rules:ident,+ : command => do
  let declName := (← getCurrNamespace) ++ name.getId
  runTermElabM fun vars =>
    Term.withoutErrToSorry <| Term.elabBinders binders fun xs => do
      let lhs ← Term.elabTerm lhs none
      Term.synthesizeSyntheticMVarsNoPostponing
      let lhs ← instantiateMVars lhs
      -- Reducible normalization, implicit arguments and types included: the implicit interface
      -- types reduce too, so the registered simp rule has no projections in its keys.
      let lhs ← withReducible <| reduce lhs (explicitOnly := false) (skipTypes := false)
      let mut thms ← Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)
      for n in #[``dite_true, ``dite_false, ``ite_true, ``ite_false,
          ``Sum.elim_inl, ``Sum.elim_inr] do
        thms ← thms.addConst n
      -- A supplied proposition is a rewriting lemma; any other constant is unfolded.
      for rule in rules.getElems do
        let n ← realizeGlobalConstNoOverloadWithInfo rule
        if (← isProp (← inferType (← mkConstWithFreshMVarLevels n))) then
          thms ← thms.addConst n
        else
          thms ← thms.addDeclToUnfold n
      let ctx ← Simp.mkContext (simpTheorems := #[thms])
        (congrTheorems := ← getSimpCongrTheorems)
      let (result, _) ← Meta.simp lhs ctx
      let proof ← result.getProof
      let type ← mkForallFVars xs (← mkEq lhs result.expr)
      let type ← mkForallFVars vars type (usedOnly := true)
      let value ← mkLambdaFVars xs proof
      let value ← mkLambdaFVars vars value (usedOnly := true)
      let type ← instantiateMVars type
      let value ← instantiateMVars value
      -- Keep only universes in the type or proof; an unused section universe could not be
      -- inferred from the goal, so `simp` would never apply the equation.
      let usedLevels := collectLevelParams (collectLevelParams {} type) value |>.params
      let levelParams := (← get).levelNames.filter usedLevels.contains
      addDecl <| .thmDecl {
        name := declName
        levelParams := levelParams
        type := type
        value := value }
      let some ext ← getSimpExtension? `component_equations
        | throwError "Missing component equation registry."
      addSimpTheorem ext declName true false .global 1000
      let short := declName.getString!
      let description :=
        if short.startsWith "memorylessReplyLaw_" then
          "The reply law of this invocation against fresh inside replies of `law`. "
        else if short.startsWith "combine_" then
          "The next pair of states and reply from one invocation against `insideStep`. "
        else if short.startsWith "body_" then
          "Given this invocation's inside exchanges, its next query or its next state and reply. "
        else
          "The next private state and reply at this procedure's input. "
      addDocStringCore declName (description ++
        "The starting state is displayed; this equation is generated and kernel-checked.")


end SystemAlgebra.DSL

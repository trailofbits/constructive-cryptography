import ConstructiveCryptography.Tactics.Basic
import ConstructiveCryptography.Substitution.Quantitative

/-!
# Substitution proof commands

Commands that apply the substitution laws to supplied terms (Banfi, Definition 2.3.1 and
§2.3.1).

* `cc_substitute relation through converter using premise` applies preservation.
* `cc_substitution_chain relation using witness, premises` interprets a witness.
* `cc_substitution_chain concrete model using witness, losses, bounds` sums the concrete
  transformed-step bounds.
* `cc_substitution_chain mixed model using witness, selected, losses, errors, domination,
  assumptions, statistical` checks a mixed chain.
* `cc_usage` computes the use counts of a witness built from the named operations.

`cc_calc relation` expands a paper-style calculation, alternating exact equalities and
named substitutions, into a Lean `calc`:

```lean
cc_calc relation
  X = α • R₀ := start
  _ ≃ α • R₁ := hR
  _ = β • S₁ := join
  _ ≃ β • S₀ := ← hS
  _ = Y := finish.symm
```

Inside the block `≃` is the selected relation. A substitution line checks the supplied
proof, then one preservation step through the converter written in the endpoints; `←`
reverses the premise.

`cc_calc counted systems` builds an `Implication`; each substitution line names an index
in `systems`, and the converter is inferred or given with `through α`:

```lean
cc_calc counted systems
  X = α • systems i false := start
  _ ≃ α • systems i true := i
  _ = β • systems j true := join
  _ ≃ β • systems j false := ← j
  _ = Y := finish
```

`cc_calc mixed model using domination` combines distinguisher-indexed steps `≃[loss]` with
statistical steps `≈[ε]`, where `domination` bounds the advantage of admitted
distinguishers by the distance:

```lean
cc_calc mixed model using domination
  X = R := start
  _ ≃[loss₁] S := first
  _ ≈[ε] T := statistical
  _ ≃[loss₂] U := ← second
  _ = Y := finish
```

This proves `model.SubstitutesWithin (fun D => loss₁ D + ε + loss₂ D) X Y`.
`cc_calc quantitative model` allows only concrete steps and `cc_calc statistical` only
statistical steps.
-/

open Lean

syntax (name := ccSubstitute)
  "cc_substitute " term " through " term " using " term : tactic

macro_rules
  | `(tactic| cc_substitute $relation through $converter using $premise) => do
    let label := Syntax.mkStrLit s!"SubstitutionRelation.preserved; transformation={converter.raw.unsetTrailing.reprint.getD "<term>"}; premise={premise.raw.unsetTrailing.reprint.getD "<term>"}"
    `(tactic| cc_exact_rule $label =>
      ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.preserved
        $relation $converter $premise)

open Lean.Parser.Term
open ConstructiveCryptography.CryptographicAlgebra (SubstitutionRelation)

/-- Calculation lines reuse ordinary terms and proofs; reversal is explicit. -/
declare_syntax_cat ccSubstitutionCalcStep
syntax ppIndent(colGe term:51 " = " term " := " term) : ccSubstitutionCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " term) : ccSubstitutionCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " "← " term) : ccSubstitutionCalcStep

syntax ccSubstitutionCalcSteps := ppLine withPosition(
  ccSubstitutionCalcStep (ppLine linebreak ccSubstitutionCalcStep)*)
/-- A Banfi substitution calculation elaborated through Lean's existing `calc`. -/
syntax (name := ccCalc) "cc_calc " term:max ccSubstitutionCalcSteps : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cc_calc $relation $block:ccSubstitutionCalcSteps) => do
    let `(ccSubstitutionCalcSteps|
      $initial:ccSubstitutionCalcStep
      $following*) := block
      | throwUnsupportedSyntax
    let steps := #[initial] ++ following
    let mut first? : Option (TSyntax ``calcFirstStep) := none
    let mut rest : Array (TSyntax ``calcStep) := #[]
    for step in steps do
      let (statement, proof) ← match step with
        | `(ccSubstitutionCalcStep| $previous:term = $next := $proof) =>
            pure (← `($previous = $next), proof)
        | _ => do
            let (previous, next, premise) ← match step with
              | `(ccSubstitutionCalcStep| $previous:term ≃ $next := ← $premise) =>
                  pure (previous, next, ← ``(Iff.mpr
                    (SubstitutionRelation.substitutes_symm_iff $relation) $premise))
              | `(ccSubstitutionCalcStep| $previous:term ≃ $next := $premise) =>
                  pure (previous, next, premise)
              | _ => throwUnsupportedSyntax
            let statement ← ``(SubstitutionRelation.substitutes $relation _ $previous $next)
            let proof ← `(by
              first
              | cc_exact_rule "cc_calc supplied substitution" =>
                  ($premise : SubstitutionRelation.substitutes $relation _ _ _)
              | cc_substitute $relation through _ using $premise)
            pure (statement, proof)
      match first? with
      | none => first? := some (← `(calcFirstStep| $statement := $proof))
      | some _ => rest := rest.push (← `(calcStep| $statement := $proof))
    let some first := first? | throwUnsupportedSyntax
    let calculation ← `(calc
      $first:calcFirstStep
      $rest:calcStep*)
    let assembled ← `(tactic| (
      let := SubstitutionRelation.transitive $relation
      exact $calculation))
    -- Missing mathematics must fail, not recover to a placeholder proof.
    let goal ← getMainGoal
    Term.withoutErrToSorry <| withoutRecover <| Term.withSynthesize <| evalTactic assembled
    if (← instantiateMVars (mkMVar goal)).hasSorry then
      throwError "cc_calc requires a complete proof for every step"

/-! ## Counted calculations -/

declare_syntax_cat ccCountedCalcStep
syntax ppIndent(colGe term:51 " = " term " := " term) : ccCountedCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " term) : ccCountedCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " "← " term) : ccCountedCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " term " through " term) : ccCountedCalcStep
syntax ppIndent(colGe term:51 " ≃ " term " := " "← " term " through " term) : ccCountedCalcStep
syntax ccCountedCalcSteps := ppLine withPosition(
  ccCountedCalcStep (ppLine linebreak ccCountedCalcStep)*)

/-- Build the existing finite implication from named assumption indices. -/
syntax (name := ccCalcCounted) "cc_calc " &"counted" term:max ccCountedCalcSteps : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cc_calc counted $systems $block:ccCountedCalcSteps) => do
    let `(ccCountedCalcSteps|
      $initial:ccCountedCalcStep
      $following*) := block
      | throwUnsupportedSyntax
    let mut start? : Option (TSyntax `term) := none
    let mut current? : Option (TSyntax `term) := none
    let mut prefixProof ← `(rfl)
    let mut chain? : Option (TSyntax `term) := none
    for step in #[initial] ++ following do
      let (previous, next, equality?, entry?) ← match step with
        | `(ccCountedCalcStep| $previous:term = $next := $proof) =>
            pure (previous, next, some proof, none)
        | `(ccCountedCalcStep| $previous:term ≃ $next := $index) =>
            pure (previous, next, none, some (index, ← `(_), false))
        | `(ccCountedCalcStep| $previous:term ≃ $next := ← $index) =>
            pure (previous, next, none, some (index, ← `(_), true))
        | `(ccCountedCalcStep| $previous:term ≃ $next := $index through $converter) =>
            pure (previous, next, none, some (index, converter, false))
        | `(ccCountedCalcStep| $previous:term ≃ $next := ← $index through $converter) =>
            pure (previous, next, none, some (index, converter, true))
        | _ => throwUnsupportedSyntax
      let previous := if previous.raw.isOfKind ``Lean.Parser.Term.hole then
        current?.getD previous else previous
      let start := start?.getD previous
      start? := some start
      let current := current?.getD previous
      let adjacent ← `(show $current = $previous from rfl)
      match equality?, entry? with
      | some proof, _ =>
        let equation ← `(Eq.trans $adjacent (show $previous = $next from $proof))
        match chain? with
        | none => prefixProof ← `(Eq.trans $prefixProof $equation)
        | some chain =>
          chain? := some (← ``(SubstitutionRelation.Implication.withEndpoints
            $chain $start $next rfl (Eq.symm $equation)))
      | _, some (index, converter, reverse) =>
        let direction ← if reverse then `(true) else `(false)
        let entry ← ``(SubstitutionRelation.Implication.withEndpoints
          (SubstitutionRelation.Implication.single (systems := $systems)
            $index $direction $converter) $previous $next rfl rfl)
        match chain? with
        | none =>
          chain? := some (← ``(SubstitutionRelation.Implication.withEndpoints
            $entry $start $next (Eq.trans $prefixProof $adjacent) rfl))
        | some chain =>
          chain? := some (← ``(SubstitutionRelation.Implication.append
            $chain $entry $adjacent))
        trace[ConstructiveCryptography.ProofAutomation.rule]
          "cc_calc counted; assumption={index}; reverse={reverse}; transformation={converter}"
      | _, _ => throwUnsupportedSyntax
      current? := some next
    let some chain := chain? | throwError "cc_calc counted needs an assumption use"
    let goal ← getMainGoal
    Term.withoutErrToSorry <| withoutRecover <| Term.withSynthesize <|
      evalTactic (← `(tactic| exact $chain))
    if (← instantiateMVars (mkMVar goal)).hasSorry then
      throwError "cc_calc counted requires complete exact joins"

open Lean Meta in
/-- Inspect only the head of the supplied witness, stopping at the five known
constructors or an opaque/variable witness. Never unfold their finite indices. Returns the
count rule and the witness exposed at its constructor. -/
partial def ccUsageRule? (witness : Expr) : MetaM (Option (Name × Expr)) := do
  let witness ← instantiateMVars witness
  let rules := [
    (``SubstitutionRelation.Implication.withEndpoints,
      ``SubstitutionRelation.Implication.usageCount_withEndpoints),
    (``SubstitutionRelation.Implication.append,
      ``SubstitutionRelation.Implication.usageCount_append),
    (``SubstitutionRelation.Implication.single,
      ``SubstitutionRelation.Implication.usageCount_single),
    (``SubstitutionRelation.Implication.map,
      ``SubstitutionRelation.Implication.usageCount_map),
    (``SubstitutionRelation.Implication.reverse,
      ``SubstitutionRelation.Implication.usageCount_reverse)]
  if let .const name _ := witness.getAppFn then
    if let some rule := rules.lookup name then return some (rule, witness)
  match witness with
  | .fvar id =>
    if let some value := (← id.getDecl).value? then return ← ccUsageRule? value
    return none
  | .letE _ _ value body _ => ccUsageRule? (body.instantiate1 value)
  | .mdata _ expression => ccUsageRule? expression
  | _ =>
    if let some expression ← unfoldDefinition? witness then
      if expression != witness then return ← ccUsageRule? expression
    return none

open Lean Meta Elab Tactic in
/-- Normalize use counts by constructor-directed structural laws, not by
enumerating positions or trying unrelated count rules at default transparency. -/
elab "cc_usage" : tactic => withMainContext do
  let rec findUsage (expression : Expr) : MetaM (Option (Expr × Name × Expr)) := do
    if expression.isAppOf ``SubstitutionRelation.Implication.usageCount &&
        (← isDefEq (← inferType expression) (mkConst ``Nat)) then
      let rule? ← ccUsageRule? expression.getAppArgs[expression.getAppNumArgs - 2]!
      return rule?.map (expression, ·)
    -- Do not descend into the data or equality proofs inside a counted witness.
    match expression with
    | .app function argument =>
      if let some found ← findUsage function then return some found
      findUsage argument
    | .mdata _ body => findUsage body
    | _ => return none
  while true do
    let goal ← getMainGoal
    let target ← goal.getType
    let some (occurrence, rule, witness) ← findUsage target | break
    -- Instantiate the rule at the exposed witness before comparing the count indices: an
    -- ascribed index such as `1` is then compared with a closed sum such as `0 + 1 + 0`.
    let ruleConst ← mkConstWithFreshMVarLevels rule
    let (arguments, _, ruleType) ← forallMetaTelescopeReducing (← inferType ruleConst)
    let some (_, lhs, _) := ruleType.eq? |
      throwError "cc_usage: {rule} is not an equation"
    let lhsArguments := lhs.getAppArgs
    unless (← isDefEq lhsArguments[lhsArguments.size - 2]! witness) &&
        (← isDefEq lhsArguments[lhsArguments.size - 1]! occurrence.appArg!) &&
        (← isDefEq lhs occurrence) do
      throwError "cc_usage requires a fully specified witness and assumption index"
    let countProof ← instantiateMVars (mkAppN ruleConst arguments)
    if countProof.hasExprMVar then
      throwError "cc_usage requires a fully specified witness and assumption index"
    let exactProof ← mkAppM ``Eq.trans #[← mkEqRefl occurrence, countProof]
    let targetRewrite ← goal.rewrite target exactProof
      (config := { transparency := .reducible })
    trace[ConstructiveCryptography.ProofAutomation.rule] "cc_usage {rule}"
    replaceMainGoal [← goal.replaceTargetEq targetRewrite.eNew targetRewrite.eqProof]
  evalTactic (← `(tactic| try simp only [↓reduceIte, Bool.true_eq_false,
    Bool.false_eq_true, add_zero, zero_add, Nat.reduceAdd]))

/-! ## Statistical and concrete calculations -/

declare_syntax_cat ccQuantitativeCalcStep
syntax ppIndent(colGe term:51 " = " term " := " term) : ccQuantitativeCalcStep
syntax ppIndent(colGe term:51 " ≃[" term "] " term " := " term) : ccQuantitativeCalcStep
syntax ppIndent(colGe term:51 " ≃[" term "] " term " := " "← " term) : ccQuantitativeCalcStep
syntax ppIndent(colGe term:51 " ≈[" term "] " term " := " term) : ccQuantitativeCalcStep
syntax ppIndent(colGe term:51 " ≈[" term "] " term " := " "← " term) : ccQuantitativeCalcStep
syntax ccQuantitativeCalcSteps := ppLine withPosition(
  ccQuantitativeCalcStep (ppLine linebreak ccQuantitativeCalcStep)*)
syntax (name := ccCalcStatistical) "cc_calc " &"statistical" ccQuantitativeCalcSteps : tactic
syntax (name := ccCalcQuantitative) "cc_calc " &"quantitative" term:max
  ccQuantitativeCalcSteps : tactic
syntax (name := ccCalcMixed) "cc_calc " "mixed " term:max " using " term:max
  ccQuantitativeCalcSteps : tactic

open ConstructiveCryptography.CryptographicAlgebra in
open Lean Elab Tactic in
/-- Assemble only the displayed triangle steps, keeping statistical and
distinguisher-dependent budgets distinct. Exact joins contribute no error. -/
def elaborateCCQuantitativeCalc (model? domination? : Option (TSyntax `term))
    (block : TSyntax ``ccQuantitativeCalcSteps) : TacticM Unit := do
  let `(ccQuantitativeCalcSteps|
    $initial:ccQuantitativeCalcStep
    $following*) := block
    | throwUnsupportedSyntax
  let mut start? : Option (TSyntax `term) := none
  let mut current? : Option (TSyntax `term) := none
  let mut prefixProof ← `(rfl)
  let mut result? : Option (TSyntax `term × TSyntax `term) := none
  for step in #[initial] ++ following do
    let (previous, next, budget?, proof, statistical, reverse) ← match step with
      | `(ccQuantitativeCalcStep| $previous:term = $next := $proof) =>
          pure (previous, next, none, proof, false, false)
      | `(ccQuantitativeCalcStep| $previous:term ≃[$budget] $next := $proof) =>
          pure (previous, next, some budget, proof, false, false)
      | `(ccQuantitativeCalcStep| $previous:term ≃[$budget] $next := ← $proof) =>
          pure (previous, next, some budget, proof, false, true)
      | `(ccQuantitativeCalcStep| $previous:term ≈[$budget] $next := $proof) =>
          pure (previous, next, some budget, proof, true, false)
      | `(ccQuantitativeCalcStep| $previous:term ≈[$budget] $next := ← $proof) =>
          pure (previous, next, some budget, proof, true, true)
      | _ => throwUnsupportedSyntax
    let previous := if previous.raw.isOfKind ``Lean.Parser.Term.hole then
      current?.getD previous else previous
    let start := start?.getD previous
    start? := some start
    let current := current?.getD previous
    let adjacent ← `(show $current = $previous from rfl)
    let proposition ← match model? with
      | some model => ``(fun budget left right =>
          DistinguisherAdvantage.SubstitutesWithin $model budget left right)
      | none => ``(fun budget left right => distance left right ≤ budget)
    match budget? with
    | none =>
      let equation ← `(Eq.trans $adjacent (show $previous = $next from $proof))
      match result? with
      | none => prefixProof ← `(Eq.trans $prefixProof $equation)
      | some (budget, result) =>
        result? := some (budget, ← `(Eq.mp
          (congrArg (fun right => $proposition $budget $start right) $equation) $result))
    | some budget =>
      let mut leaf := proof
      let mut loss := budget
      if statistical then
        let original := leaf
        if reverse then
          leaf ← `(by simpa only [distance, ConstructiveCryptography.CryptographicAlgebra.distance,
            edist_comm] using $proof)
        leaf ← `(show distance $previous $next ≤ $budget from by
          first
          | cc_exact_rule "cc_calc supplied distance" => $leaf
          | cc_exact_rule "cc_calc distance_attach_le" =>
              (distance_attach_le _ _ _).trans $leaf)
        if let some model := model? then
          let some domination := domination? |
            throwError "statistical steps need `cc_calc mixed model using domination`"
          let mut observation ← ``(DistinguisherAdvantage.SubstitutesWithin.of_statistical
            $model $domination $original)
          if reverse then
            observation ← ``(DistinguisherAdvantage.SubstitutesWithin.symm $model $observation)
          leaf ← `(show DistinguisherAdvantage.SubstitutesWithin $model
              (fun _ => $budget) $previous $next from by
            first
            | cc_exact_rule "cc_calc supplied statistical observation" => $observation
            | cc_exact_rule "cc_calc statistical distance" =>
                DistinguisherAdvantage.SubstitutesWithin.of_distance $model $domination $leaf)
          loss ← `(fun _ => $budget)
      else
        let some model := model? |
          throwError "a computational premise is not a statistical distance bound"
        if reverse then
          leaf ← ``(DistinguisherAdvantage.SubstitutesWithin.symm $model $leaf)
        leaf ← `(show DistinguisherAdvantage.SubstitutesWithin $model
          $budget $previous $next from by
            cc_exact_rule "cc_calc supplied concrete substitution" => $leaf)
      -- The displayed left endpoint must be the preceding right endpoint.
      leaf ← `(Eq.mpr (congrArg
        (fun left => $proposition $loss left $next) $adjacent) $leaf)
      match result? with
      | none =>
        result? := some (loss, ← `(Eq.mpr (congrArg
          (fun left => $proposition $loss left $next) $prefixProof) $leaf))
      | some (budget, result) =>
        match model? with
        | some model =>
          result? := some (← `(fun distinguisher =>
            $budget distinguisher + $loss distinguisher),
            ← ``(DistinguisherAdvantage.SubstitutesWithin.trans $model $result $leaf))
        | none =>
          result? := some (← `($budget + $loss),
            ← `((distance_triangle $start $current $next).trans
              (add_le_add $result $leaf)))
    current? := some next
  let some (_, result) := result? | throwError "a quantitative calculation needs a bound"
  let goal ← getMainGoal
  Term.withoutErrToSorry <| withoutRecover <| Term.withSynthesize <|
    evalTactic (← `(tactic| exact $result))
  if (← instantiateMVars (mkMVar goal)).hasSorry then
    throwError "cc_calc requires a complete proof for every bound and join"

elab_rules : tactic
  | `(tactic| cc_calc statistical $block:ccQuantitativeCalcSteps) =>
      elaborateCCQuantitativeCalc none none block
  | `(tactic| cc_calc quantitative $model $block:ccQuantitativeCalcSteps) =>
      elaborateCCQuantitativeCalc (some model) none block
  | `(tactic| cc_calc mixed $model using $domination $block:ccQuantitativeCalcSteps) =>
      elaborateCCQuantitativeCalc (some model) (some domination) block

syntax (name := ccSubstitutionChain)
  "cc_substitution_chain " term " using " term "," term : tactic

macro_rules
  | `(tactic| cc_substitution_chain $relation using $witness, $premises) => do
    let label := Syntax.mkStrLit s!"Implication.substitutes; witness={witness.raw.unsetTrailing.reprint.getD "<term>"}; premises={premises.raw.unsetTrailing.reprint.getD "<term>"}"
    `(tactic| cc_exact_rule $label =>
      ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutes
        $relation $witness $premises)

syntax (name := ccSubstitutionChainConcrete)
  "cc_substitution_chain " "concrete " term " using " term "," term "," term : tactic

macro_rules
  | `(tactic| cc_substitution_chain concrete $model using $witness, $losses, $bounds) => do
    let label := Syntax.mkStrLit s!"Implication.substitutesWithin; witness={witness.raw.unsetTrailing.reprint.getD "<term>"}; losses={losses.raw.unsetTrailing.reprint.getD "<term>"}; bounds={bounds.raw.unsetTrailing.reprint.getD "<term>"}"
    `(tactic| cc_exact_rule $label =>
      ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutesWithin
        $model $witness $losses $bounds)

syntax (name := ccSubstitutionChainMixed)
  "cc_substitution_chain " "mixed " term " using " term "," term "," term ","
    term "," term "," term "," term : tactic

macro_rules
  | `(tactic| cc_substitution_chain mixed $model using $witness, $selected, $losses,
      $errors, $domination, $assumptions, $statistical) => do
    let label := Syntax.mkStrLit s!"Implication.substitutesWithin_of_mixed; witness={witness.raw.unsetTrailing.reprint.getD "<term>"}; selected={selected.raw.unsetTrailing.reprint.getD "<term>"}; losses={losses.raw.unsetTrailing.reprint.getD "<term>"}; statistical errors={errors.raw.unsetTrailing.reprint.getD "<term>"}"
    `(tactic| cc_exact_rule $label =>
      ConstructiveCryptography.CryptographicAlgebra.SubstitutionRelation.Implication.substitutesWithin_of_mixed
        $model $witness $selected $losses $errors $domination $assumptions $statistical)

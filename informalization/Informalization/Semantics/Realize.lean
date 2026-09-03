/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean.Data.Json
import Lean.DeclarationRange
import LanguageDesign.SurfaceContract
import Informalization.MassotMiller.Hover
import Informalization.MassotMiller.Ontology
import Informalization.Semantics.Discourse
import Informalization.Semantics.Symbols

/-!
# Generic semantic discourse realization

This is the first language-realization slice over the typed discourse plan.
Its sentences are selected by semantic move constructors, never theorem names
or tactic text.  Exact checked expressions remain available through the
evidence index for expansion and future LeanTeX rendering.
-/

namespace Informalization.Semantics.Realize

open Lean
open Lean Meta
open Informalization.Semantics
open Informalization.Semantics.Canonical
open Informalization.Semantics.Discourse
open CryptoLanguage.LanguageDesign

/-- Mathematical content is retained as typed canonical data until the final
surface pass.  A sentence is therefore not the source of its own formula. -/
inductive MathObject where
  | system (value : SystemTerm)
  | game (value : GameTerm)
  | bound (value : BoundTerm)
  | claim (value : Claim)
  /-- A checked formula selected by a public rule schema. -/
  | formula (value : FormulaTerm)
  /-- Domain proposition produced by the registered fixed-set collision
  rule.  The exact queried-set expression remains an operand even when the
  surface layer assigns it the conventional local symbol `S`. -/
  | fixedSetCollisionBound (alphabet queriedSet : Expr)
  /-- Generic birthday inequality instantiated by a population size and a
  sample size. -/
  | birthdayBound (population sampleSize : Expr)
  /-- Cardinality of the distinct fixed query set under a query budget. -/
  | querySetBudget (budget : Expr)
  /-- A scoped reader symbol for a checked semantic object. -/
  | symbolRef (role : Symbols.Role) (source : Expr) (preferred : String)
  deriving Inhabited, BEq, Repr

/-- Minimal rich-content language used by the reader bridge. -/
inductive Fragment where
  | text (value : String)
  | inlineMath (value : MathObject)
  | displayMath (value : MathObject)
  deriving Inhabited, BEq, Repr

private abbrev SurfaceForm :=
  CryptoLanguage.LanguageDesign.SurfaceContract.CanonicalForm

/-- Instantiate one executable language-contract frame while keeping its
mathematical holes as typed fragments. -/
private def surfaceFragments (form : SurfaceForm)
    (values : Array (Name × Array Fragment)) : Array Fragment :=
  form.template.pieces.foldl (init := #[]) fun result piece =>
    match piece with
    | .literal text => result.push (.text text)
    | .hole hole =>
        match values.find? (·.1 == hole.id) with
        | some value => result ++ value.2
        | none => result

/-- One expandable realized detail, still identified by its original proof
step and semantic depth. -/
structure Detail where
  kind : MoveKind
  semanticDepth : Nat
  content : Array Fragment := #[]
  text : String
  /-- Lean-derived hover information for the mathematical symbols occurring
  in this detail's own rendered formula. -/
  referenceHovers : Array Informalization.MassotMiller.LeanHoverInfo := #[]
  /-- Exact checked evidence available through an independent developer
  disclosure at semantic leaves. -/
  leanEvidence : Array Informalization.MassotMiller.LeanEvidenceInfo := #[]
  /-- The one checked proof step whose conclusion this detail presents.
  Additional references are provenance, not interchangeable candidates for a
  displayed proof-state checkpoint. -/
  primaryEvidence : EvidenceRef
  evidence : Array EvidenceRef
  /-- Checked edge from the parent claim to this local proof node. -/
  supportOrigin? : Option Discourse.SupportOrigin := none
  /-- Evidence attached to that premise or macro-expansion branch. -/
  supportEvidence : Array EvidenceRef := #[]
  /-- Realized semantic subarguments.  This mirrors the checked dependency
  tree instead of flattening every descendant into one disclosure panel. -/
  children : Array Detail := #[]
  /-- The checked, operand-bearing rule application from which this detail was
  realized.  It is retained separately from `content` and `text`, so neither
  prose realization nor later reader transformations erase proof structure. -/
  derivation? : Option DerivationApplication := none
  deriving Inhabited, BEq, Repr

/-- One realized sentence together with the semantic evidence supporting it. -/
structure Sentence where
  moveId : Nat
  kind : MoveKind
  semanticDepth : Nat
  content : Array Fragment := #[]
  text : String
  /-- Lean-derived hover information for the mathematical symbols occurring
  in this sentence's own rendered formula. -/
  referenceHovers : Array Informalization.MassotMiller.LeanHoverInfo := #[]
  /-- Exact checked evidence available through an independent developer
  disclosure at semantic leaves. -/
  leanEvidence : Array Informalization.MassotMiller.LeanEvidenceInfo := #[]
  /-- Primary checked step for this move.  Synthetic discourse transitions
  such as a restatement of the remaining obligation may have none. -/
  primaryEvidence? : Option EvidenceRef := none
  evidence : Array EvidenceRef
  details : Array Detail := #[]
  /-- The checked, operand-bearing rule application from which this sentence
  was realized. -/
  derivation? : Option DerivationApplication := none
  deriving Inhabited, BEq, Repr

/-- A human-facing layer paired with its complete formal evidence index. -/
structure Document where
  security : Option SecurityContext
  /-- The decoded theorem conclusion, retained independently of the opening
  sentence chosen for it. -/
  rootClaim? : Option Claim := none
  /-- Optional checked theorem title and symbol introductions. -/
  theoremPresentation? : Option TheoremPresentation := none
  /-- Hover corresponding to the theorem declaration in the heading. -/
  declarationHover? : Option Informalization.MassotMiller.LeanHoverInfo := none
  /-- Lean-derived theorem binders, registered notations, and profile-linked
  references available throughout the reader document. -/
  theoremReferenceHovers : Array Informalization.MassotMiller.LeanHoverInfo := #[]
  planKind : Plan.Kind
  sentences : Array Sentence
  evidenceIndex : Array EvidenceItem
  deriving Inhabited

/-- Canonical information inherited while realizing one semantic proof tree.
This is deliberately an explicit value rather than an ad-hoc parent fallback:
the symbol-planning layer can extend the scope with stable operand bindings
without changing the recursive presentation bridge. -/
structure Scope where
  primaryEvidence? : Option EvidenceRef := none
  /-- Candidate checked contexts from the current node back to its ancestors.
  Rendering selects a context only when it contains the exact free variables of
  the typed fragments; otherwise it stays in the theorem telescope. -/
  evidencePath : Array EvidenceRef := #[]
  /-- Reader symbols inherited by semantic descendants. -/
  symbols : Symbols.Scope := {}
  /-- Profile-supplied mathematical notation. Keeping it in the realization
  scope makes notation available recursively without teaching the renderer
  any application declaration names. -/
  declarationNotations : Array DeclarationNotation := #[]
  deriving Inhabited

private def symbolBindingForSlot? (slot : Name) :
    Option (Symbols.Role × String) :=
  if slot == `alphabet then some (.alphabet, "X")
  else if slot == `queryBudget then some (.queryBudget, "q")
  else if slot == `blockBudget then some (.queryBudget, "q")
  else if slot == `queriedSet then some (.querySet, "S")
  else if slot == `sampleSize then some (.sampleSize, "k")
  else if slot == `sampleSpaceCardinality then
    some (.populationSize, "N")
  else if slot == `blockForm then some (.custom `blockForm, "B")
  else if slot == `blockLimit then some (.queryBudget, "r")
  else if slot == `system then some (.sourceSystem, "S")
  else if slot == `roundFunction then some (.sourceSystem, "R")
  else if slot == `idealFunction then some (.targetSystem, "V")
  else if slot == `messages then some (.custom `messages, "L")
  else if slot == `answers then some (.custom `answers, "a")
  else if slot == `function then some (.custom `function, "f")
  else if slot == `message then some (.custom `message, "m")
  else if slot == `otherMessage then some (.custom `otherMessage, "m'")
  else if slot == `position then some (.custom `position, "i")
  else if slot == `otherPosition then some (.custom `otherPosition, "j")
  else if slot == `parentMap then some (.custom `parentMap, "p")
  else if slot == `walkStep then some (.custom `walkStep, "g")
  else if slot == `initialState then some (.custom `initialState, "x_0")
  else if slot == `rank then some (.custom `rank, "\\rho")
  else if slot == `siteInput then some (.custom `siteInput, "I")
  else if slot == `lower then some (.custom `lower, "\\delta")
  else if slot == `upper then some (.custom `upper, "\\varepsilon")
  else none

private def symbolBinding? (operand : CanonicalOperand) :
    Option (Symbols.Role × String) :=
  symbolBindingForSlot? operand.slot

/-- Proof reconstruction may retain the same theorem binder in several local
contexts with different internal free-variable identifiers.  Its user name is
the stable identity available at the presentation boundary. -/
private def symbolKey (localContext? : Option LocalContext)
    (role : Symbols.Role) (source : Expr) : Symbols.Key :=
  let binderName? := do
    let localContext ← localContext?
    let .fvar id := source.consumeMData | none
    let declaration ← localContext.find? id
    guard !declaration.userName.isAnonymous
    return declaration.userName
  { role, source, binderName? }

private def bindDerivationSymbols (symbols : Symbols.Scope)
    (localContext? : Option LocalContext)
    (derivation? : Option DerivationApplication) : Symbols.Scope :=
  derivation?.elim symbols fun derivation =>
    derivation.operands.foldl (init := symbols) fun symbols operand =>
      match symbolBinding? operand with
      | some (role, preferred) =>
          (symbols.introduce
            (symbolKey localContext? role operand.value) preferred).1
      | none => symbols

/- Bind only opaque or named leaves. Structured systems keep their visible
converter, restriction, and game structure instead of being collapsed into a
single generic `R` or `S`. Short mathematical declaration names such as `R`
and `V` remain available as the preferred leaf symbols. -/
private def declarationLeafSymbol (declaration : Name)
    (fallback : String) : String :=
  match declaration with
  | .str _ leaf => if leaf.length ≤ 3 then leaf else fallback
  | _ => fallback

mutual
  private partial def bindSystemSymbols (symbols : Symbols.Scope)
      (localContext? : Option LocalContext) (role : Symbols.Role)
      (preferred : String) : SystemTerm → Symbols.Scope
    | .opaque source | .transform source _ _ =>
        (symbols.introduce (symbolKey localContext? role source) preferred).1
    | .named source declaration _ =>
        (symbols.introduce (symbolKey localContext? role source)
          (declarationLeafSymbol declaration preferred)).1
    | .presentationQuotient _ underlying
    | .converterApplication _ _ underlying
    | .queryRestriction _ _ underlying =>
        bindSystemSymbols symbols localContext? role preferred underlying
    | .forgetGame _ game => bindGameSymbols symbols localContext? preferred game
    | .uniformRandomFunction .. | .uniformRandomPermutation .. => symbols

  private partial def bindGameSymbols (symbols : Symbols.Scope)
      (localContext? : Option LocalContext) (preferred : String) :
      GameTerm → Symbols.Scope
    | .opaque source | .transform source _ _ =>
        (symbols.introduce
          (symbolKey localContext? .game source) preferred).1
    | .named source declaration _ =>
        (symbols.introduce (symbolKey localContext? .game source)
          (declarationLeafSymbol declaration preferred)).1
    | .enhanceWithMBO _ system _ =>
        bindSystemSymbols symbols localContext? .sourceSystem "R" system
    | .converterApplication _ _ underlying =>
        bindGameSymbols symbols localContext? preferred underlying
    | .queryRestriction _ _ underlying =>
        bindGameSymbols symbols localContext? preferred underlying
end

private partial def bindBoundSymbols (symbols : Symbols.Scope)
    (localContext? : Option LocalContext) (preferred : String) :
    BoundTerm → Symbols.Scope
  | .expression _ => symbols
  | .named source _ _ =>
      (symbols.introduce
        (symbolKey localContext? .scalar source) preferred).1
  | .quadraticCollision _ queryBudget alphabet =>
      let symbols := (symbols.introduce
        (symbolKey localContext? .queryBudget queryBudget) "q").1
      (symbols.introduce
        (symbolKey localContext? .alphabet alphabet) "X").1
  | .statisticalDistance _ left right
  | .distinguishingAdvantage _ _ left right =>
      let symbols := bindSystemSymbols symbols localContext? .sourceSystem "R" left
      bindSystemSymbols symbols localContext? .targetSystem "S" right
  | .winningProbability _ game | .blindWinningProbability _ game =>
      bindGameSymbols symbols localContext? "G" game
  | .coercion _ inner => bindBoundSymbols symbols localContext? preferred inner

/-- Introduce reader symbols from canonical claim roles.  The expressions are
the identity of the bindings; preferred letters never classify a claim. -/
private def bindClaimSymbols (symbols : Symbols.Scope)
    (localContext? : Option LocalContext) : Claim → Symbols.Scope
  | .systemEquality _ left right =>
      let symbols := bindSystemSymbols symbols localContext? .sourceSystem "R" left
      bindSystemSymbols symbols localContext? .targetSystem "S" right
  | .conditionalEquivalence _ game target =>
      let symbols := bindGameSymbols symbols localContext? "G" game
      bindSystemSymbols symbols localContext? .targetSystem "T" target
  | .distanceBound _ left right upper
  | .advantageBound _ _ left right upper =>
      let symbols := bindSystemSymbols symbols localContext? .sourceSystem "R" left
      let symbols := bindSystemSymbols symbols localContext? .targetSystem "S" right
      bindBoundSymbols symbols localContext? "\\varepsilon" upper
  | .blindWinningBound _ game upper =>
      let symbols := bindGameSymbols symbols localContext? "G" game
      bindBoundSymbols symbols localContext? "\\varepsilon" upper
  | .upperBound _ lower upper =>
      let symbols := bindBoundSymbols symbols localContext? "\\delta" lower
      bindBoundSymbols symbols localContext? "\\varepsilon" upper
  | .construction _ source converter target error =>
      let symbols := (symbols.introduce {
        role := .sourceSpecification
        source := source.source
      } "\\mathcal R").1
      let symbols := (symbols.introduce {
        role := .converter
        source := converter.source
      } "\\pi").1
      let symbols := (symbols.introduce {
        role := .targetSpecification
        source := target.source
      } "\\mathcal S").1
      (symbols.introduce
        (symbolKey localContext? .scalar error.source) "\\varepsilon").1

/-- Enter one checked semantic node.  Parent derivations are deliberately not
inherited: a child without a decoded rule may inherit notation, but it must not
display its parent's conclusion under the child's evidence checkpoint. -/
def Scope.enter (scope : Scope) (primaryEvidence? : Option EvidenceRef)
    (derivation? : Option DerivationApplication)
    (localContext? : Option LocalContext := none) : Scope := {
  primaryEvidence?
  evidencePath := match primaryEvidence? with
    | some reference => #[reference] ++ scope.evidencePath
    | none => scope.evidencePath
  symbols :=
    let symbols := derivation?.bind (·.conclusion.claim?) |>.elim scope.symbols
      (bindClaimSymbols scope.symbols localContext?)
    let symbols := derivation?.elim symbols fun derivation =>
      derivation.obligations.foldl (init := symbols) fun symbols obligation =>
        match obligation.claim? with
        | some claim@(.conditionalEquivalence ..) =>
            bindClaimSymbols symbols localContext? claim
        | _ => symbols
    bindDerivationSymbols symbols localContext? derivation?
  declarationNotations := scope.declarationNotations
}

/-- Enter a semantic disclosure child while retaining inherited symbols. -/
def Scope.descend (scope : Scope) : Scope :=
  { scope with symbols := scope.symbols.child }

private def baseSystemText (description : SystemDescriptor) : String :=
  let base := match description.baseRole with
    | .uniformRandomFunction => "uniform random function"
    | .uniformRandomPermutation => "uniform random permutation"
    | .idealFunctionality => "ideal functionality"
    | _ => "random system"
  if description.queryRestriction?.isSome then "query-restricted " ++ base else base

private def comparedSystemText (role : Option ArgumentRole) (fallback : String)
    (description : Option SystemDescriptor) : String :=
  match role with
  | some .realSystem => match description with
      | some value => s!"the real system, a {baseSystemText value}"
      | none => "the real system"
  | some .idealSystem => match description with
      | some value => s!"the ideal system, a {baseSystemText value}"
      | none => "the ideal system"
  | _ => match description with
      | some value => "a " ++ baseSystemText value
      | none => s!"the {fallback} system"

private def securityGoalText (context : Option SecurityContext) : String :=
  match context with
  | none =>
      "We compare the two systems and bound their distinguishing advantage."
  | some context =>
      let systems :=
        if context.sourceSystem?.isSome && context.targetSystem?.isSome then
          s!"{comparedSystemText context.sourceRole? "source" context.sourceDescription?} with " ++
            comparedSystemText context.targetRole? "target" context.targetDescription?
        else
          "the source system with the target system"
      let scope :=
        if context.queryBudget?.isSome then " under the stated query budget" else ""
      let conclusion :=
        if context.bound?.isSome then
          " The goal is to bound their distinguishing advantage by the stated bound."
        else
          " The goal is to bound their distinguishing advantage."
      s!"We compare {systems}{scope}.{conclusion}"

/-! ## Canonical mathematical rendering -/

private def scopedSymbol (symbols : Symbols.Scope) (role : Symbols.Role)
    (source : Expr) (fallback : String) : String :=
  symbols.lookup? { role, source } |>.getD fallback

private def scopedSystemLeaf? (symbols : Symbols.Scope) (source : Expr) : Option String :=
  symbols.lookup? { role := .sourceSystem, source } |>.orElse fun _ =>
    symbols.lookup? { role := .targetSystem, source }

private def expressionOrSymbol (symbols : Symbols.Scope) (role : Symbols.Role)
    (source : Expr) : MetaM String :=
  match symbols.lookup? { role, source } with
  | some symbol => pure symbol
  | none => Informalization.MassotMiller.Ontology.exprLatex source

private def systemLeafLatex (symbols : Symbols.Scope) (source : Expr) : MetaM String :=
  match scopedSystemLeaf? symbols source with
  | some symbol => pure symbol
  | none => Informalization.MassotMiller.Ontology.exprLatex source

private def conditionLatex (symbols : Symbols.Scope)
    (condition : ConditionTerm) : MetaM String :=
  expressionOrSymbol symbols .condition condition.source

private def declarationNotationLatex? (scope : Scope) (declaration : Name)
    (operands : Array Expr) : MetaM (Option String) := do
  let some entry := scope.declarationNotations.find? (·.declaration == declaration)
    | return none
  let mut renderedOperands : Array String := #[]
  for index in [:Nat.min entry.operandSlots.size operands.size] do
    let slot := entry.operandSlots[index]!
    let operand := operands[index]!
    let rendered ← match symbolBindingForSlot? slot with
      | some (role, preferred) =>
          match operand.consumeMData.getAppFn.consumeMData with
          | .const declaration _ =>
              match scope.declarationNotations.find? fun candidate =>
                  candidate.declaration == declaration &&
                    candidate.style == .atom with
              | some candidate => pure candidate.latex
              | none => pure <| scopedSymbol scope.symbols role operand preferred
          | _ => pure <| scopedSymbol scope.symbols role operand preferred
      | none => Informalization.MassotMiller.Ontology.exprLatex operand
    renderedOperands := renderedOperands.push rendered
  match entry.style with
  | .atom => return some entry.latex
  | .bracketed =>
      return some <| entry.latex ++ "[" ++
        String.intercalate ", " renderedOperands.toList ++ "]"
  | .template =>
      let mut result := ""
      for piece in entry.template do
        match piece with
        | .literal value => result := result ++ value
        | .operand slot =>
            let some index := entry.operandSlots.findIdx? (· == slot)
              | return none
            let some rendered := renderedOperands[index]?
              | return none
            result := result ++ rendered
      return some result

mutual
  private partial def converterLatex (scope : Scope)
      (converter : ConverterTerm) : MetaM String := do
    match converter with
    | .opaque source => expressionOrSymbol scope.symbols .converter source
    | .named source declaration operands | .restriction source declaration operands =>
        match ← declarationNotationLatex? scope declaration operands with
        | some renderedNotation => pure renderedNotation
        | none => expressionOrSymbol scope.symbols .converter source
    | .serialComposition source outer inner =>
        match scope.symbols.lookup? { role := .converter, source } with
        | some symbol => pure symbol
        | none => do
            return (← converterLatex scope outer) ++ "\\circ " ++
              (← converterLatex scope inner)

  private partial def systemLatex (scope : Scope)
      (system : SystemTerm) : MetaM String := do
    match system with
    | .opaque source => systemLeafLatex scope.symbols source
    | .named source declaration operands =>
        match ← declarationNotationLatex? scope declaration operands with
        | some rendered => return rendered
        | none => systemLeafLatex scope.symbols source
    | .uniformRandomFunction _ input output => do
        return "\\mathsf{URF}_{" ++
          (← Informalization.MassotMiller.Ontology.exprLatex input) ++ "," ++
          (← Informalization.MassotMiller.Ontology.exprLatex output) ++ "}"
    | .uniformRandomPermutation _ alphabet => do
        return "\\mathsf{URP}_{" ++
          (← Informalization.MassotMiller.Ontology.exprLatex alphabet) ++ "}"
    | .presentationQuotient _ presentation => systemLatex scope presentation
    | .converterApplication _ converter underlying => do
        return (← converterLatex scope converter) ++ "\\cdot " ++
          (← systemLatex scope underlying)
    | .queryRestriction _ budget underlying => do
        return "[" ++ scopedSymbol scope.symbols .queryBudget budget "q" ++
          "]\\," ++ (← systemLatex scope underlying)
    | .forgetGame _ game => do
        return "(" ++ (← gameLatex scope game) ++ ")^{-}"
    | .transform source _ _ =>
        Informalization.MassotMiller.Ontology.exprLatex source

  private partial def gameLatex (scope : Scope)
      (game : GameTerm) : MetaM String := do
    match game with
    | .opaque source => expressionOrSymbol scope.symbols .game source
    | .named source declaration operands =>
        match ← declarationNotationLatex? scope declaration operands with
        | some rendered => return rendered
        | none => expressionOrSymbol scope.symbols .game source
    | .enhanceWithMBO _ system condition => do
        return "\\widehat{" ++ (← systemLatex scope system) ++ "}^{" ++
          (← conditionLatex scope.symbols condition) ++ "}"
    | .converterApplication _ converter underlying => do
        return (← converterLatex scope converter) ++ "\\cdot " ++
          (← gameLatex scope underlying)
    | .queryRestriction _ budget underlying => do
        return "[" ++ scopedSymbol scope.symbols .queryBudget budget "q" ++
          "]" ++ (← gameLatex scope underlying)
    | .transform source _ _ =>
        Informalization.MassotMiller.Ontology.exprLatex source
end

private def specificationLatex (scope : Scope)
    (role : Symbols.Role) (specification : SpecificationTerm) : MetaM String := do
  if let some symbol := scope.symbols.lookup? { role, source := specification.source } then
    return symbol
  match specification with
  | .opaque source => Informalization.MassotMiller.Ontology.exprLatex source
  | .singleton _ system => return "\\{" ++ (← systemLatex scope system) ++ "\\}"

private partial def boundLatex (scope : Scope)
    (bound : BoundTerm) : MetaM String := do
  if let some symbol := scope.symbols.lookup? { role := .scalar, source := bound.source } then
    return symbol
  match bound with
  | .expression source | .named source _ _ =>
      expressionOrSymbol scope.symbols .scalar source
  | .quadraticCollision _ queryBudget alphabet =>
      let q := scopedSymbol scope.symbols .queryBudget queryBudget "q"
      let x := scopedSymbol scope.symbols .alphabet alphabet "X"
      return "\\frac{" ++ q ++ "^{2}}{2\\cdot\\lvert " ++ x ++ " \\rvert}"
  | .statisticalDistance _ left right => do
      return "\\Delta(" ++ (← systemLatex scope left) ++ "," ++
        (← systemLatex scope right) ++ ")"
  | .distinguishingAdvantage _ kind real ideal => do
      let operator := match kind with
        | .fullyDefined => "\\operatorname{Adv}_{\\bot}"
        | .ambient => "\\operatorname{Adv}"
      return operator ++ "(" ++ (← systemLatex scope real) ++ "," ++
        (← systemLatex scope ideal) ++ ")"
  | .winningProbability _ game => do
      return "\\Gamma(" ++ (← gameLatex scope game) ++ ")"
  | .blindWinningProbability _ game => do
      return "\\Gamma(b(" ++ (← gameLatex scope game) ++ "))"
  | .coercion _ inner => boundLatex scope inner

private def claimLatex (scope : Scope) : Claim → MetaM String
  | .systemEquality _ left right => do
      return (← systemLatex scope left) ++ " = " ++
        (← systemLatex scope right)
  | .conditionalEquivalence _ game target => do
      return (← gameLatex scope game) ++ " \\mathrel{\\mid\\!\\equiv} " ++
        (← systemLatex scope target)
  | .distanceBound _ left right upper => do
      return "\\Delta(" ++ (← systemLatex scope left) ++ "," ++
        (← systemLatex scope right) ++ ") \\leq " ++
        (← boundLatex scope upper)
  | .advantageBound _ kind real ideal upper => do
      let operator := match kind with
        | .fullyDefined => "\\operatorname{Adv}_{\\bot}"
        | .ambient => "\\operatorname{Adv}"
      return operator ++ "(" ++ (← systemLatex scope real) ++ "," ++
        (← systemLatex scope ideal) ++ ") \\leq " ++
        (← boundLatex scope upper)
  | .blindWinningBound _ game upper => do
      return "\\Gamma(b(" ++ (← gameLatex scope game) ++ ")) \\leq " ++
        (← boundLatex scope upper)
  | .upperBound _ lower upper => do
      return (← boundLatex scope lower) ++ " \\leq " ++
        (← boundLatex scope upper)
  | .construction _ source converter target error => do
      return (← specificationLatex scope .sourceSpecification source) ++
        " \\xrightarrow[" ++ (← boundLatex scope error) ++ "]{" ++
        (← converterLatex scope converter) ++ "} " ++
        (← specificationLatex scope .targetSpecification target)

private def readerForbidden : Array String := #[
  "RandomSystems.", "Probability.", "Lean.Expr", "_uniq", "_hyg",
  "Subtype.val", "OfNat.ofNat", "HDiv.hDiv", "HMul.hMul", "LE.le"
]

private def readerSafe (value : String) : Bool :=
  value.length ≤ 1200 && !readerForbidden.any (fun fragment => value.contains fragment)

private def formulaLatex (scope : Scope) : FormulaTerm → MetaM String
  | .converterEquality _ left right => do
      return (← converterLatex scope left) ++ " = " ++
        (← converterLatex scope right)
  | .restrictionAttachment _ blockForm limit system => pure <|
      let blockForm := scopedSymbol scope.symbols (.custom `blockForm) blockForm "B"
      let limit := scopedSymbol scope.symbols .queryBudget limit "r"
      let system := scopedSymbol scope.symbols .sourceSystem system "S"
      "\\theta_{" ++ blockForm ++ "," ++ limit ++ "}\\cdot " ++ system ++
        " = \\bigl(h\\mapsto \\begin{cases}" ++ system ++
        "(h),&\\operatorname{blocks}_{" ++ blockForm ++ "}(h)\\le " ++ limit ++
        ",\\\\ \\bot,&\\text{otherwise}\\end{cases}\\bigr)"
  | .conditionalProductIdentity _ blockForm messages answers => pure <|
      let blockForm := scopedSymbol scope.symbols (.custom `blockForm) blockForm "B"
      let messages := scopedSymbol scope.symbols (.custom `messages) messages "L"
      let answers := scopedSymbol scope.symbols (.custom `answers) answers "a"
      "\\Pr_{f\\leftarrow\\mathsf{URF}(X,X)}[" ++
        "(\\forall m\\in " ++ messages ++ ",\\,\\operatorname{CBC}_f(" ++
        blockForm ++ "(m))=" ++ answers ++ "(m))\\wedge\\neg\\mathsf{Bad}_{" ++
        blockForm ++ "," ++ messages ++ "}(f)] = " ++
        "\\Pr_{g\\leftarrow\\mathsf{URF}(M,X)}[\\forall m\\in " ++
        messages ++ ",\\,g(m)=" ++ answers ++ "(m)]\\," ++
        "\\Pr_{f\\leftarrow\\mathsf{URF}(X,X)}[\\neg\\mathsf{Bad}_{" ++
        blockForm ++ "," ++ messages ++ "}(f)]"
  | .distinctSiteInputs _ function blockForm message other position otherPosition => pure <|
      let function := scopedSymbol scope.symbols (.custom `function) function "f"
      let blockForm := scopedSymbol scope.symbols (.custom `blockForm) blockForm "B"
      let message := scopedSymbol scope.symbols (.custom `message) message "m"
      let other := scopedSymbol scope.symbols (.custom `otherMessage) other "m'"
      let position := scopedSymbol scope.symbols (.custom `position) position "i"
      let otherPosition := scopedSymbol scope.symbols (.custom `otherPosition) otherPosition "j"
      "I_{" ++ function ++ "}(" ++ blockForm ++ "(" ++ message ++ ")," ++
        position ++ ")\\ne I_{" ++ function ++ "}(" ++ blockForm ++ "(" ++
        other ++ ")," ++ otherPosition ++ ")"
  | .terminalInputInjective _ function blockForm messages => pure <|
      let function := scopedSymbol scope.symbols (.custom `function) function "f"
      let blockForm := scopedSymbol scope.symbols (.custom `blockForm) blockForm "B"
      let messages := scopedSymbol scope.symbols (.custom `messages) messages "L"
      "\\operatorname{InjOn}\\!\\left(m\\mapsto I_{" ++ function ++ "}(" ++
        blockForm ++ "(m),\\lvert " ++ blockForm ++ "(m)\\rvert-1)," ++
        messages ++ "\\right)"
  | .walkCollisionBound _ parent step initial rank input => pure <|
      let parent := scopedSymbol scope.symbols (.custom `parentMap) parent "p"
      let step := scopedSymbol scope.symbols (.custom `walkStep) step "g"
      let initial := scopedSymbol scope.symbols (.custom `initialState) initial "x_0"
      let rank := scopedSymbol scope.symbols (.custom `rank) rank "\\rho"
      let input := scopedSymbol scope.symbols (.custom `siteInput) input "I"
      "\\mathcal W=(\\mathcal T," ++ parent ++ "," ++ step ++ "," ++ initial ++
        ";" ++ rank ++ "),\\quad " ++ parent ++ "(t)=u\\Rightarrow " ++
        rank ++ "(u)<" ++ rank ++ "(t),\\quad " ++ input ++ "_f(t)=" ++ step ++
        "_t\\!\\left(\\begin{cases}" ++ initial ++ ",&" ++ parent ++
        "(t)=\\bot,\\\\ f(" ++ input ++ "_f(u)),&" ++ parent ++
        "(t)=u\\end{cases}\\right),\\quad " ++
        "\\Pr_{f\\leftarrow\\mathsf{URF}(X,X)}[\\neg\\operatorname{Injective}(" ++
        input ++ "_f)]\\le\\frac{\\lvert\\mathcal T\\rvert" ++
        "(\\lvert\\mathcal T\\rvert-1)}{2\\lvert X\\rvert}"
  | .collisionMassBound _ blockForm limit messages => pure <|
      let blockForm := scopedSymbol scope.symbols (.custom `blockForm) blockForm "B"
      let limit := scopedSymbol scope.symbols .queryBudget limit "r"
      let messages := scopedSymbol scope.symbols (.custom `messages) messages "L"
      "\\Pr_{f\\leftarrow\\mathsf{URF}(X,X)}[\\mathsf{Bad}_{" ++ blockForm ++
        "," ++ messages ++ "}(f)]\\le\\frac{" ++ limit ++ "(" ++ limit ++
        "-1)}{2\\lvert X\\rvert}"
  | .scalarMonotonicity _ lower upper => pure <|
      let lower := scopedSymbol scope.symbols (.custom `lower) lower "\\delta"
      let upper := scopedSymbol scope.symbols (.custom `upper) upper "\\varepsilon"
      lower ++ "\\le " ++ upper ++ "\\quad\\Longrightarrow\\quad" ++
        "\\operatorname{ofReal}(" ++ lower ++ ")\\le\\operatorname{ofReal}(" ++
        upper ++ ")"

private def mathLatex (scope : Scope) : MathObject → MetaM String
  | .system value => systemLatex scope value
  | .game value => gameLatex scope value
  | .bound value => boundLatex scope value
  | .claim value => claimLatex scope value
  | .formula value => formulaLatex scope value
  | .fixedSetCollisionBound alphabet queriedSet => do
      let alphabet ← Informalization.MassotMiller.Ontology.exprLatex alphabet
      let queriedSet := scopedSymbol scope.symbols .querySet queriedSet "S"
      return "\\Pr_{f\\leftarrow\\mathsf{URF}_{" ++ alphabet ++ "," ++ alphabet ++
        "}}[\\neg\\operatorname{InjOn}(f," ++ queriedSet ++ ")] \\leq " ++
        "\\frac{\\lvert " ++ queriedSet ++ " \\rvert(\\lvert " ++ queriedSet ++
        " \\rvert-1)}{2\\lvert " ++ alphabet ++ " \\rvert}"
  | .birthdayBound population sampleSize => do
      let population := scopedSymbol scope.symbols .populationSize population "N"
      let sampleSize := scopedSymbol scope.symbols .sampleSize sampleSize "k"
      return "1-\\frac{\\prod_{j<" ++ sampleSize ++ "}(" ++ population ++
        "-j)}{" ++ population ++ "^{" ++ sampleSize ++ "}} \\leq " ++
        "\\frac{" ++ sampleSize ++ "(" ++ sampleSize ++ "-1)}{2" ++
        population ++ "}"
  | .querySetBudget budget => do
      let budgetSymbol := scope.symbols.lookup? {
        role := .queryBudget
        source := budget
      }
      let budget ← match budgetSymbol with
        | some symbol => pure symbol
        | none => Informalization.MassotMiller.Ontology.exprLatex budget
      return "k \\leq " ++ budget
  | .symbolRef role source preferred =>
      pure (scopedSymbol scope.symbols role source preferred)

private def renderFragments (scope : Scope)
    (content : Array Fragment) : MetaM String := do
  let mut result := ""
  for fragment in content do
    match fragment with
    | .text value => result := result ++ value
    | .inlineMath value =>
        let rendered ← mathLatex scope value
        if readerSafe rendered then result := result ++ "\\(" ++ rendered ++ "\\)"
    | .displayMath value =>
        let rendered ← mathLatex scope value
        if readerSafe rendered then result := result ++ "\n\\[" ++ rendered ++ ".\\]"
  return result

private def conclusion? (derivation? : Option DerivationApplication) : Option Claim :=
  derivation?.bind (·.conclusion.claim?)

private def upperBound? : Claim → Option BoundTerm
  | .distanceBound _ _ _ upper | .advantageBound _ _ _ _ upper |
      .blindWinningBound _ _ upper => some upper
  | .upperBound _ _ upper => some upper
  | .construction _ _ _ _ error => some error
  | _ => none

/-- Compose the checked paper-level reduction for presentation: the source
root supplies the original system distance, while the registered
conditional-equivalence step supplies the blind-winning upper bound. The
restriction identity and carrier bridge remain separately checked moves. -/
private def rootDistanceWithUpper? (root? reduction? : Option Claim) : Option Claim := do
  let .distanceBound source real ideal _ ← root? | none
  let reduction ← reduction?
  let upper ← upperBound? reduction
  return .distanceBound source real ideal upper

private partial def systemQueryBudget? : SystemTerm → Option Expr
  | .queryRestriction _ budget _ => some budget
  | .presentationQuotient _ underlying => systemQueryBudget? underlying
  | .converterApplication _ _ underlying => systemQueryBudget? underlying
  | .transform _ _ underlying => systemQueryBudget? underlying
  | .forgetGame _ (.queryRestriction _ budget _) => some budget
  | _ => none

private def claimQueryBudget? : Claim → Option Expr
  | .distanceBound _ left right _ =>
      (systemQueryBudget? left).orElse fun _ => systemQueryBudget? right
  | .advantageBound _ _ real ideal _ =>
      (systemQueryBudget? real).orElse fun _ => systemQueryBudget? ideal
  | .blindWinningBound _ (.queryRestriction _ budget _) _ => some budget
  | _ => none

private partial def systemAlphabet? : SystemTerm → Option Expr
  | .uniformRandomFunction _ input _ => some input
  | .uniformRandomPermutation _ alphabet => some alphabet
  | .queryRestriction _ _ underlying => systemAlphabet? underlying
  | .presentationQuotient _ underlying => systemAlphabet? underlying
  | .converterApplication _ _ underlying => systemAlphabet? underlying
  | .forgetGame _ game => gameAlphabet? game
  | .transform _ _ underlying => systemAlphabet? underlying
  | .named _ _ _ | .opaque _ => none
  where
    gameAlphabet? : GameTerm → Option Expr
      | .enhanceWithMBO _ underlying _ => systemAlphabet? underlying
      | .converterApplication _ _ underlying => gameAlphabet? underlying
      | .queryRestriction _ _ underlying => gameAlphabet? underlying
      | .transform _ _ _ | .named _ _ _ | .opaque _ => none

private def claimAlphabet? : Claim → Option Expr
  | .distanceBound _ left right _ =>
      (systemAlphabet? left).orElse fun _ => systemAlphabet? right
  | .advantageBound _ _ real ideal _ =>
      (systemAlphabet? real).orElse fun _ => systemAlphabet? ideal
  | .systemEquality _ left right =>
      (systemAlphabet? left).orElse fun _ => systemAlphabet? right
  | .conditionalEquivalence _ game target =>
      (systemAlphabet? target).orElse fun _ =>
        match game with
        | .enhanceWithMBO _ underlying _ => systemAlphabet? underlying
        | .converterApplication _ _ (.enhanceWithMBO _ underlying _) =>
            systemAlphabet? underlying
        | .queryRestriction _ _ (.enhanceWithMBO _ underlying _) => systemAlphabet? underlying
        | _ => none
  | .blindWinningBound _ game _ =>
      match game with
      | .enhanceWithMBO _ underlying _ => systemAlphabet? underlying
      | .converterApplication _ _ (.enhanceWithMBO _ underlying _) =>
          systemAlphabet? underlying
      | .queryRestriction _ _ (.enhanceWithMBO _ underlying _) => systemAlphabet? underlying
      | _ => none
  | .upperBound _ _ _ => none
  | .construction _ _ _ _ _ => none

private def rootSymbolScope (source : Discourse.Document)
    (localContext : LocalContext) : Symbols.Scope :=
  source.rootClaim?.elim {} fun claim =>
    let symbols := bindClaimSymbols ({} : Symbols.Scope) (some localContext) claim
    let symbols := (claimAlphabet? claim).elim symbols fun alphabet =>
      (symbols.introduce
        (symbolKey (some localContext) .alphabet alphabet) "X").1
    (claimQueryBudget? claim).elim symbols fun budget =>
      (symbols.introduce
        (symbolKey (some localContext) .queryBudget budget) "q").1

/-- Render a proposition through a selected semantic profile without adding
that profile's modules or attributes to the source elaboration environment.
Only propositions recognized by the checked canonical decoder are handled;
all others return `none` to the structural Lean-expression fallback. -/
def checkedPropositionLatex? (profile : DecoderProfile)
    (expression : Expr) : MetaM (Option String) := do
  let expression ← instantiateMVars expression
  let some claim ← decodeClaim? profile expression | return none
  let localContext ← getLCtx
  -- This renderer is used inside the concrete proof tree, where introducing
  -- an unexplained `G` or `T` would lose information.  Keep the canonical
  -- structure visible and abbreviate only theorem-wide scalar/alphabet
  -- binders whose notation is already conventional.
  let emptySymbols : Symbols.Scope := {}
  let symbols := (claimAlphabet? claim).elim emptySymbols fun alphabet =>
    (emptySymbols.introduce
      (symbolKey (some localContext) .alphabet alphabet) "X").1
  let symbols := (claimQueryBudget? claim).elim symbols fun budget =>
    (symbols.introduce
      (symbolKey (some localContext) .queryBudget budget) "q").1
  let scope : Scope := {
    symbols
    declarationNotations := profile.declarationNotations
  }
  return some (← claimLatex scope claim)

private def firstObligationClaim? (derivation? : Option DerivationApplication)
    (slot : ObligationSlot) : Option Claim := do
  let derivation ← derivation?
  let obligation ← derivation.obligations.find? (·.slot == slot)
  obligation.claim?

private def hasObligationSlot (derivation : DerivationApplication)
    (slot : ObligationSlot) : Bool :=
  derivation.obligations.any (·.slot == slot)

private def hasClaimedObligation (derivation : DerivationApplication)
    (slot : ObligationSlot) (predicate : Claim → Bool) : Bool :=
  derivation.obligations.any fun obligation =>
    obligation.slot == slot && obligation.claim?.any predicate

private def isConditionalEquivalenceClaim : Claim → Bool
  | .conditionalEquivalence .. => true
  | _ => false

private def isEstimateClaim : Claim → Bool
  | .distanceBound .. | .advantageBound .. | .blindWinningBound ..
  | .upperBound .. => true
  | _ => false

/-- A stronger connective is licensed only by the construction conclusion and
the checked distance-bound rule used in its proof. -/
private def constructionDistanceConnective? (source : Discourse.Document)
    (derivation? : Option DerivationApplication) : Bool :=
  match source.rootClaim?, derivation? with
  | some (.construction ..), some derivation =>
      derivation.rule == .deriveDistanceBound &&
        derivation.conclusion.claim?.any fun claim => match claim with
          | .distanceBound .. => true
          | _ => false
  | _, _ => false

/-- Common-domain data-processing prose is licensed only by the checked
non-expansion theorem's distance conclusion. -/
private def commonDomainConnective? (derivation? : Option DerivationApplication) : Bool :=
  derivation?.any fun derivation =>
    derivation.rule == .custom `commonDomainDataProcessing &&
      derivation.conclusion.claim?.any (fun claim => match claim with
        | .distanceBound .. => true
        | _ => false)

/-- Conditional-equivalence reduction is connective-bearing only when the
checked rule retains the conditional-equivalence premise it consumes. -/
private def conditionalReductionConnective?
    (derivation? : Option DerivationApplication) : Bool :=
  derivation?.any fun derivation =>
    derivation.rule == .conditionalEquivalenceToBlindWinning &&
      derivation.conclusion.claim?.any isEstimateClaim &&
      hasClaimedObligation derivation .conditionalEquivalence
        isConditionalEquivalenceClaim

/-- Restriction-preservation prose requires its source conditional
equivalence, both total-answer roles, and a conditional-equivalence result. -/
private def restrictionConnective? (derivation? : Option DerivationApplication) : Bool :=
  derivation?.any fun derivation =>
    derivation.rule == .preserveConditionalEquivalence &&
      derivation.conclusion.claim?.any isConditionalEquivalenceClaim &&
      hasClaimedObligation derivation .conditionalEquivalence
        isConditionalEquivalenceClaim &&
      hasObligationSlot derivation .sourceTotal &&
      hasObligationSlot derivation .targetTotal

/-- Scalar closure may connect an estimate to its scalar image only when the
exact scalar-monotonicity Formula AST is the rule conclusion and a checked
estimate premise is retained. -/
private def scalarClosureConnective? (derivation? : Option DerivationApplication) : Bool :=
  derivation?.any fun derivation =>
    derivation.rule == .custom `scalarClosure &&
      (match derivation.formula?, derivation.conclusion.claim? with
      | some (.scalarMonotonicity source ..), some conclusion =>
          source == conclusion.source && isEstimateClaim conclusion
      | _, _ => false) &&
      derivation.obligations.any fun obligation =>
        obligation.claim?.any isEstimateClaim

private def registeredRuleText : ProofRuleRole -> String
  | .construction => "Establish the stated construction."
  | .distanceBound => "Establish the stated distance bound."
  | .advantageBound => "Establish the stated distinguishing-advantage bound."
  | .coupling => "Apply the registered coupling argument."
  | .representativeSelection => "Apply the registered representative-selection argument."
  | .winnability => "Apply the registered winnability argument."
  | .signedExpansion => "Apply the registered signed-expansion argument."
  | .arithmetic => "Discharge the resulting arithmetic bound."
  | .rewriting => "Use the registered exact rewriting step."
  | .monotonicity => "Apply the registered monotonicity step."
  | .custom _ => "Apply the registered semantic proof rule."
  | .exactEquivalence => "Identify the two systems by exact equivalence."
  | .ignoreGameMBO =>
      "Ignoring the game's MBO gives the query-restricted underlying system."
  | .triangleHybrid => "Pass through the registered intermediate system by the triangle inequality."
  | .hTechnique => "Apply the H-technique to the real and ideal systems."
  | .conditionalEquivalence => "Establish conditional equivalence between the game and its target system."
  | .conditionalEquivalenceUnderRestriction =>
      "The query restriction preserves this conditional equivalence."
  | .collisionConditionalEquivalence =>
      "The collision game and its target satisfy the registered conditional-equivalence relation."
  | .conditionalEquivalenceToBlindWinning =>
      "Conditional equivalence reduces the distinguishing advantage to a blind winning probability."
  | .blindWinningBound => "Apply the blind-winning estimate."
  | .blindWinningToNonadaptive =>
      "For blind winning, the inputs may be chosen in advance, before any replies are seen."
  | .nonadaptiveQueriesFixed =>
      "Equivalently, the query list may be fixed in advance, before any replies are seen."
  | .commonDomainDataProcessing =>
      "Applying a common-domain-preserving converter cannot increase distance."
  | .restrictionApplicationEquation =>
      "Use the exact converter-application identity."
  | .conditionalUniformOutputs =>
      "On the collision-free slice, use the output-law factorization."
  | .distinctTerminalInputs =>
      "The no-collision hypothesis gives the required distinct-input statement."
  | .gamePlayingFundamentalLemma => "Apply the game-playing fundamental lemma."
  | .counting => "Apply the registered counting estimate."
  | .collisionProbabilityBound =>
      "Bound the probability of a collision on the fixed queried set."
  | .collisionMassBound =>
      "Bound the collision mass for every admitted message list."
  | .birthdayBound => "Apply the birthday bound."
  | .scalarClosure =>
      "Map the real-valued estimate into the scalar advantage bound."

private def genericMoveText (security : Option SecurityContext) : MoveKind -> String
  | .stateSecurityGoal => securityGoalText security
  | .conditionalEquivalence =>
      "Establish conditional equivalence between the game and its target system."
  | .conditionalEquivalenceReduction =>
      "Conditional equivalence reduces the distinguishing advantage to the game's blind winning probability."
  | .remainingBlindWinningObligation =>
      "It remains to bound this blind winning probability."
  | .blindWinningEstimate =>
      "The blind-winning estimate supplies the required probability bound."
  | .combineConditionalEquivalenceBlind =>
      "Combining the conditional-equivalence reduction with the blind-winning estimate yields the claimed distinguishing-advantage bound."
  | .hTechnique =>
      "Apply the H-technique using its registered systems and bounds."
  | .hybrid =>
      "Pass through the registered intermediate system and apply the triangle inequality."
  | .gameHop =>
      "Apply the game-playing fundamental lemma to this game hop."
  | .counting =>
      "Apply the registered counting estimate."
  | .exactEquivalence =>
      "Identify the corresponding systems by exact equivalence."
  | .ignoreCollisionMBO =>
      "Enhancing the uniform random function with the collision MBO gives the collision game; ignoring its MBO gives the query-restricted underlying system."
  | .registeredRule role => registeredRuleText role
  | .formalFallback =>
      "The remaining proof region is retained in formal form."

private def claimContent (lead : String) (claim? : Option Claim) : Array Fragment :=
  match claim? with
  | some claim => #[.text lead, .displayMath (.claim claim)]
  | none => #[]

private def formulaContent (lead : String)
    (derivation? : Option DerivationApplication) : Array Fragment :=
  match derivation?.bind (·.formula?) with
  | some formula => #[.text lead, .displayMath (.formula formula)]
  | none => #[]

/-- Domain prose for a registered proof node requires exact, publicly licensed
evidence for that declaration and rule.  A generic rule classification or a
checked library signature is not a linguistic attestation. -/
private def registeredMoveLicensed (rootDeclaration? : Option Name)
    (role : ProofRuleRole) (derivation? : Option DerivationApplication) : Bool :=
  derivation?.any fun derivation =>
    derivation.provenance.declaration?.any fun declaration =>
      Informalization.Semantics.Registry.publicLanguageLicenseForOccurrence?
          rootDeclaration? declaration role |>.isSome

/-- Recover the proof role from every discourse promotion that can emit
domain-specific mathematical prose. Promotion changes presentation shape;
it never widens the declaration's linguistic authority. -/
private def promotedProofRole? : MoveKind → Option ProofRuleRole
  | .conditionalEquivalence => some .conditionalEquivalence
  | .conditionalEquivalenceReduction => some .conditionalEquivalenceToBlindWinning
  | .blindWinningEstimate => some .blindWinningBound
  | .combineConditionalEquivalenceBlind =>
      some .conditionalEquivalenceToBlindWinning
  | .hTechnique => some .hTechnique
  | .hybrid => some .triangleHybrid
  | .gameHop => some .gamePlayingFundamentalLemma
  | .counting => some .counting
  | .exactEquivalence => some .exactEquivalence
  | .ignoreCollisionMBO => some .ignoreGameMBO
  | .registeredRule role => some role
  | _ => none

private def moveLicensed (rootDeclaration? : Option Name) (kind : MoveKind)
    (derivation? : Option DerivationApplication) : Bool :=
  match promotedProofRole? kind with
  | some role => registeredMoveLicensed rootDeclaration? role derivation?
  | none => true

/-- The closing sentence of the conditional-equivalence route introduces no
new mathematical predicate: it only composes the already displayed reduction
and blind-winning estimate.  It is licensed exactly when both constituent
moves carry their own declaration-scoped language licenses and the checked
root claim is present. -/
private def moveLicensedInDocument (source : Discourse.Document)
    (kind : MoveKind) (derivation? : Option DerivationApplication) : Bool :=
  if kind == .combineConditionalEquivalenceBlind then
    source.rootClaim?.isSome &&
      source.moves.any (fun move =>
        move.kind == .conditionalEquivalenceReduction &&
          moveLicensed source.rootDeclaration? move.kind move.derivation?) &&
      source.moves.any (fun move =>
        move.kind == .blindWinningEstimate &&
          moveLicensed source.rootDeclaration? move.kind move.derivation?)
  else
    moveLicensed source.rootDeclaration? kind derivation?

private def unlicensedRegisteredContent
    (derivation? : Option DerivationApplication) : Array Fragment :=
  match derivation?.bind (·.formula?), conclusion? derivation? with
  | some formula, _ => surfaceFragments SurfaceContract.informalizationExactFormula #[
      (`formula, #[.displayMath (.formula formula)])]
  | none, some claim => surfaceFragments SurfaceContract.informalizationExactFormula #[
      (`formula, #[.displayMath (.claim claim)])]
  | none, none => #[.text "The formal derivation is retained."]

private def ignoreMboContent (claim? : Option Claim)
    (fallback : String) : Array Fragment :=
  match claim? with
  | some (.systemEquality _ (.forgetGame _ game) system) =>
      surfaceFragments SurfaceContract.informalizationIgnoreCollisionMbo #[
        (`game, #[.inlineMath (.game game)]),
        (`system, #[.inlineMath (.system system)])]
  | some claim => #[.text "The exact forgetting step gives",
      .displayMath (.claim claim)]
  | none => #[.text fallback]

mutual
  /-- Semantic descendants, rather than Lean source order or tactic spelling,
  license a stronger root-level causal explanation. -/
  private partial def detailContainsKind (detail : Discourse.Detail)
      (kind : MoveKind) : Bool :=
    detail.kind == kind || supportsContainKind detail.supports kind

  private partial def supportContainsKind (support : Discourse.Support)
      (kind : MoveKind) : Bool :=
    support.children.any (detailContainsKind · kind)

  private partial def supportsContainKind (supports : Array Discourse.Support)
      (kind : MoveKind) : Bool :=
    supports.any (supportContainsKind · kind)
end

mutual
  /-- A promoted causal frame may consume a descendant role only when that
  exact checked declaration occurrence also carries a public language
  license. -/
  private partial def detailContainsLicensedKind (source : Discourse.Document)
      (detail : Discourse.Detail) (kind : MoveKind) : Bool :=
    (detail.kind == kind &&
      moveLicensedInDocument source detail.kind detail.derivation?) ||
      supportsContainLicensedKind source detail.supports kind

  private partial def supportContainsLicensedKind (source : Discourse.Document)
      (support : Discourse.Support) (kind : MoveKind) : Bool :=
    support.children.any (detailContainsLicensedKind source · kind)

  private partial def supportsContainLicensedKind (source : Discourse.Document)
      (supports : Array Discourse.Support) (kind : MoveKind) : Bool :=
    supports.any (supportContainsLicensedKind source · kind)
end

mutual
  /-- Find the checked conclusion of the first licensed descendant with the
  requested semantic role.  This lets a promoted paper-level argument display
  a supporting formula without reconstructing it from prose or declaration
  names. -/
  private partial def firstLicensedDetailConclusion?
      (source : Discourse.Document) (detail : Discourse.Detail)
      (kind : MoveKind) : Option Claim :=
    if detail.kind == kind &&
        moveLicensedInDocument source detail.kind detail.derivation? then
      conclusion? detail.derivation?
    else
      firstLicensedSupportConclusion? source detail.supports kind

  private partial def firstLicensedSupportConclusion?
      (source : Discourse.Document) (supports : Array Discourse.Support)
      (kind : MoveKind) : Option Claim :=
    supports.findSome? fun support =>
      support.children.findSome? fun detail =>
        firstLicensedDetailConclusion? source detail kind
end

private def canonicalMoveContent (source : Discourse.Document) (kind : MoveKind)
    (derivation? : Option DerivationApplication)
    (foregroundBlindGame? : Option GameTerm := none)
    (supports : Array Discourse.Support := #[]) : Array Fragment :=
  let claim? := conclusion? derivation?
  let licensed := moveLicensedInDocument source kind derivation?
  if !licensed then unlicensedRegisteredContent derivation? else match kind with
  | .stateSecurityGoal =>
      match source.rootClaim? with
      | some claim@(.construction ..) =>
          if source.theoremPresentation?.isSome then
            #[.text "Then the real and ideal systems satisfy", .displayMath (.claim claim)]
          else
            #[.text "Under the theorem's stated hypotheses, the construction claim is",
              .displayMath (.claim claim)]
      | some claim =>
          if source.theoremPresentation?.isSome then
            #[.text "Then the real and ideal systems satisfy", .displayMath (.claim claim)]
          else
            #[.text "The claim is", .displayMath (.claim claim)]
      | none => #[.text (securityGoalText source.security)]
  | .ignoreCollisionMBO =>
      ignoreMboContent claim? (genericMoveText source.security kind)
  | .exactEquivalence =>
      let result := claimContent "The exact identification is" claim?
      if result.isEmpty then #[.text (genericMoveText source.security kind)] else result
  | .conditionalEquivalenceReduction =>
      let ce? := firstObligationClaim? derivation? .conditionalEquivalence
      let baseCe? := firstLicensedSupportConclusion? source supports
        (.registeredRule .collisionConditionalEquivalence)
      match conditionalReductionConnective? derivation?, ce?, claim? with
      | true, some ce, some claim =>
          if supportsContainLicensedKind source supports
                (.registeredRule .collisionConditionalEquivalence) &&
              supportsContainLicensedKind source supports
                (.registeredRule .conditionalEquivalenceUnderRestriction) &&
              supportsContainLicensedKind source supports
                (.registeredRule .conditionalUniformOutputs) &&
              supportsContainLicensedKind source supports
                (.registeredRule .distinctTerminalInputs) then
            let consequence :=
              (rootDistanceWithUpper? source.rootClaim? (some claim)).getD claim
            match baseCe? with
            | some baseCe =>
                surfaceFragments
                  SurfaceContract.informalizationCollisionEquivalenceReduction #[
                    (`baseConditionalEquivalence,
                      #[.displayMath (.claim baseCe)]),
                    (`restrictedConditionalEquivalence,
                      #[.displayMath (.claim ce)]),
                    (`consequence, #[.displayMath (.claim consequence)])]
            | none =>
                surfaceFragments
                  SurfaceContract.informalizationConditionalEquivalenceReduction #[
                    (`conditionalEquivalence, #[.inlineMath (.claim ce)]),
                    (`consequence, #[.displayMath (.claim claim)])]
          else
            surfaceFragments
              SurfaceContract.informalizationConditionalEquivalenceReduction #[
                (`conditionalEquivalence, #[.inlineMath (.claim ce)]),
                (`consequence, #[.displayMath (.claim claim)])]
      | _, _, some claim => #[
          .text "The conditional-equivalence reduction gives",
          .displayMath (.claim claim)
        ]
      | _, _, none => #[.text (genericMoveText source.security kind)]
  | .remainingBlindWinningObligation =>
      match claim?.bind upperBound? with
      | some upper => #[.text "It remains to bound ", .inlineMath (.bound upper), .text "."]
      | none => #[.text (genericMoveText source.security kind)]
  | .blindWinningEstimate =>
      match claim? with
      | some claim =>
        let displayedClaim := match claim, foregroundBlindGame? with
          | .blindWinningBound source _ upper, some game =>
              Claim.blindWinningBound source game upper
          | _, _ => claim
        if supportsContainKind supports (.registeredRule .blindWinningToNonadaptive) &&
            supportsContainKind supports (.registeredRule .collisionMassBound) then
          surfaceFragments SurfaceContract.informalizationBlindCollisionEstimate #[
            (`bound, #[.displayMath (.claim displayedClaim)])]
        else
          #[
            .text "For every blind strategy, the winning probability satisfies",
            .displayMath (.claim displayedClaim)
          ]
      | none => #[.text (genericMoveText source.security kind)]
  | .combineConditionalEquivalenceBlind =>
      match source.rootClaim? with
      | some claim =>
          surfaceFragments SurfaceContract.informalizationBoundConclusion #[
            (`conclusion, #[.displayMath (.claim claim)])]
      | none => #[.text (genericMoveText source.security kind)]
  | .conditionalEquivalence =>
      let result := claimContent "The required conditional equivalence is" claim?
      if result.isEmpty then #[.text (genericMoveText source.security kind)] else result
  | .registeredRule .ignoreGameMBO =>
      ignoreMboContent claim? (registeredRuleText .ignoreGameMBO)
  | .registeredRule .collisionConditionalEquivalence =>
      match claim? with
      | some claim =>
          surfaceFragments
            SurfaceContract.informalizationCollisionConditionalEquivalence #[
              (`conditionalEquivalence, #[.displayMath (.claim claim)])]
      | none => #[.text (registeredRuleText .collisionConditionalEquivalence)]
  | .registeredRule .conditionalEquivalenceUnderRestriction =>
      let premise? := firstObligationClaim? derivation? .conditionalEquivalence
      match restrictionConnective? derivation?, premise?, claim? with
      | true, some _, some claim =>
          surfaceFragments
            SurfaceContract.informalizationPreserveConditionalEquivalence #[
              (`conditionalEquivalence, #[.displayMath (.claim claim)])]
      | _, _, some claim =>
          surfaceFragments
            SurfaceContract.informalizationPreserveConditionalEquivalence #[
              (`conditionalEquivalence, #[.displayMath (.claim claim)])]
      | _, _, none => #[.text (registeredRuleText .conditionalEquivalenceUnderRestriction)]
  | .registeredRule .blindWinningToNonadaptive => #[.text
      "To win blindly is to win non-adaptively: the inputs can be interpreted as being chosen in advance, before any replies are seen. It is therefore enough to prove one uniform bound for every such environment and execution length."]
  | .registeredRule .nonadaptiveQueriesFixed =>
      let budget? := derivation?.bind (·.operandForSlot? `queryBudget) |>.map (·.value)
        |>.orElse fun _ => source.rootClaim?.bind claimQueryBudget?
      match budget? with
      | some budget => #[
          .text "The query sequence can be fixed in advance. Let \\(S\\) be its set of distinct inputs and put \\(k=\\lvert S\\rvert\\). The query restriction gives ",
          .inlineMath (.querySetBudget budget),
          .text "."
        ]
      | none => #[.text
          "The query sequence can be fixed in advance, before replies are seen; repeated queries do not enlarge its set of distinct inputs."]
  | .registeredRule .collisionProbabilityBound =>
      match derivation? with
      | some derivation =>
          match derivation.operandForSlot? `alphabet,
              derivation.operandForSlot? `queriedSet with
          | some alphabet, some queriedSet => #[
              .text "For the fixed set ",
              .text "\\(S\\)",
              .text " of distinct queried inputs, the collision calculation gives",
              .displayMath (.fixedSetCollisionBound alphabet.value queriedSet.value)
            ]
          | _, _ =>
              let result := claimContent
                "For an arbitrary fixed queried set, the collision calculation gives" claim?
              if result.isEmpty then #[.text (registeredRuleText .collisionProbabilityBound)]
              else result
      | none => #[.text (registeredRuleText .collisionProbabilityBound)]
  | .registeredRule .birthdayBound =>
      match derivation? with
      | some derivation =>
          match derivation.operandForSlot? `sampleSpaceCardinality,
              derivation.operandForSlot? `sampleSize with
          | some population, some sampleSize => #[
              .text "Writing \\(N\\) for the population size and \\(k=\\lvert S\\rvert\\), the birthday estimate is",
              .displayMath (.birthdayBound population.value sampleSize.value)
            ]
          | _, _ =>
              let result := claimContent "The birthday estimate gives" claim?
              if result.isEmpty then #[.text (registeredRuleText .birthdayBound)] else result
      | none => #[.text (registeredRuleText .birthdayBound)]
  | .registeredRule .rewriting =>
      let result := claimContent "The exact identification is" claim?
      if result.isEmpty then #[.text "Apply the exact identification."] else result
  | .registeredRule .distanceBound =>
      let lead := if constructionDistanceConnective? source derivation? then
        "For the stated construction, it is therefore enough to prove the distance bound"
      else
        "The distance-bound conclusion is"
      let result := claimContent lead claim?
      if result.isEmpty then #[.text (registeredRuleText .distanceBound)] else result
  | .registeredRule .advantageBound =>
      let result := claimContent
        "The corresponding distinguishing-advantage bound is" claim?
      if result.isEmpty then #[.text (registeredRuleText .advantageBound)] else result
  | .registeredRule .commonDomainDataProcessing =>
      #[]
  | .registeredRule .restrictionApplicationEquation =>
      match derivation?.bind (·.formula?),
          derivation?.bind (·.operandForSlot? `blockBudget)
            |>.orElse fun _ => derivation?.bind (·.operandForSlot? `blockLimit) with
      | some formula, some budget =>
          surfaceFragments SurfaceContract.informalizationRestrictionRedundancy #[
            (`budget, #[.inlineMath
              (.symbolRef .queryBudget budget.value "q")]),
            (`equation, #[.displayMath (.formula formula)])]
      | some formula, none =>
          #[.text "The total-block restriction makes the query restriction redundant:",
            .displayMath (.formula formula)]
      | none, _ =>
          let result := claimContent
            "The converter-application identity is" claim?
          if result.isEmpty then
            #[.text (registeredRuleText .restrictionApplicationEquation)]
          else result
  | .registeredRule .conditionalUniformOutputs =>
      let result := formulaContent
        "On the collision-free slice, the output law factors as follows:" derivation?
      if result.isEmpty then #[.text (registeredRuleText .conditionalUniformOutputs)]
      else result
  | .registeredRule .distinctTerminalInputs =>
      let lead := match derivation?.bind (·.formula?) with
        | some (.terminalInputInjective ..) =>
            "Outside the collision event, the terminal inputs are distinct:"
        | some (.distinctSiteInputs ..) =>
            "Outside the collision event, the following call-site inputs are distinct:"
        | _ => registeredRuleText .distinctTerminalInputs
      let result := formulaContent lead derivation?
      if result.isEmpty then #[.text (registeredRuleText .distinctTerminalInputs)]
      else result
  | .registeredRule .collisionMassBound =>
      let result := formulaContent
        "For every admitted message list, the collision mass satisfies" derivation?
      if result.isEmpty then #[.text (registeredRuleText .collisionMassBound)] else result
  | .registeredRule .scalarClosure =>
      let lead := if scalarClosureConnective? derivation? then
        "Applying scalar monotonicity to the preceding real estimate therefore gives the scalar advantage bound:"
      else
        "The scalar-monotonicity step is:"
      let result := formulaContent lead derivation?
      if result.isEmpty then #[.text (registeredRuleText .scalarClosure)] else result
  | .registeredRule role =>
      let result := claimContent (registeredRuleText role) claim?
      if result.isEmpty then #[.text (registeredRuleText role)] else result
  | .counting =>
      let result := formulaContent
        "The call sites form a rank-decreasing parent walk, and its collision mass obeys" derivation?
      let result := if result.isEmpty then
        claimContent (genericMoveText source.security kind) claim?
      else result
      if result.isEmpty then #[.text (genericMoveText source.security kind)] else result
  | .hTechnique | .hybrid | .gameHop =>
      let result := claimContent (genericMoveText source.security kind) claim?
      if result.isEmpty then #[.text (genericMoveText source.security kind)] else result
  | .formalFallback => #[.text (genericMoveText source.security kind)]

private def contextForReference? (source : Discourse.Document)
    (reference : EvidenceRef) : Option LocalContext := do
    let item ← source.evidenceIndex.find? (·.reference == reference)
    item.localContext?

private def MathObject.sourceExpressions : MathObject → Array Expr
  | .system value => #[value.source]
  | .game value => #[value.source]
  | .bound value => #[value.source]
  | .claim value => #[value.source]
  | .formula value => #[value.source]
  | .fixedSetCollisionBound alphabet queriedSet => #[alphabet, queriedSet]
  | .birthdayBound population sampleSize => #[population, sampleSize]
  | .querySetBudget budget => #[budget]
  | .symbolRef _ source _ => #[source]

private def Fragment.sourceExpressions : Fragment → Array Expr
  | .text _ => #[]
  | .inlineMath value | .displayMath value => value.sourceExpressions

private def contentFVars (content : Array Fragment) : Array FVarId :=
  content.foldl (init := #[]) fun result fragment =>
    fragment.sourceExpressions.foldl (init := result) fun result expression =>
      (Lean.collectFVars {} expression).fvarIds.foldl (init := result) fun result id =>
        if result.contains id then result else result.push id

private def contextContains (localContext : LocalContext)
    (variables : Array FVarId) : Bool :=
  variables.all localContext.contains

private def contextFor? (source : Discourse.Document) (scope : Scope)
    (references : Array EvidenceRef) (content : Array Fragment) : Option LocalContext :=
  let candidates := scope.evidencePath ++ references
  let variables := contentFVars content
  candidates.findSome? fun reference => do
    let localContext ← contextForReference? source reference
    guard (contextContains localContext variables)
    return localContext

private abbrev LeanHover := Informalization.MassotMiller.LeanHoverInfo

/-- Within one formula a printed symbol has one checked referent.  Preserve
the earlier, more specific entry when the theorem and a nested scope both
offer the same notation. -/
private def appendDistinctHovers (initial additions : Array LeanHover) :
    Array LeanHover :=
  additions.foldl (init := initial) fun result hover =>
    if hover.latex.trimAscii.isEmpty then result
    else match result.find? (·.latex == hover.latex) with
      | none => result.push hover
      | some known =>
          if known.description?.isSome ||
              (known.name == hover.name && !hover.description?.isSome) then
            result
          else
            result.map fun entry => if entry.latex == hover.latex then hover else entry

private def localBinderHovers : MetaM (Array LeanHover) := do
  let localContext ← getLCtx
  let mut result := #[]
  for declaration? in localContext.decls do
    if let some declaration := declaration? then
      if !declaration.userName.isAnonymous then
        let latex := Informalization.escapeLatex declaration.userName.toString
        try
          result := appendDistinctHovers result #[←
            Informalization.MassotMiller.LeanHoverInfo.ofExpr
              latex declaration.toExpr]
        catch _ => pure ()
  return result

private def presentationReferenceHover?
    (reference : PresentationReference) : MetaM (Option LeanHover) := do
  let latex := if reference.hoverLatex.trimAscii.isEmpty then
      reference.latex
    else
      reference.hoverLatex
  let description? := some reference.description
  try
    match reference.target with
    | .theoremBinder name =>
        let some declaration := (← getLCtx).findFromUserName? name | return none
        return some (← Informalization.MassotMiller.LeanHoverInfo.ofExpr
          latex declaration.toExpr description?)
    | .declaration name =>
        return some (← Informalization.MassotMiller.LeanHoverInfo.ofDeclaration
          latex name description?)
  catch _ => return none

private def presentationHovers
    (presentation? : Option TheoremPresentation) : MetaM (Array LeanHover) := do
  let some presentation := presentation? | return #[]
  let mut result := #[]
  for paragraph in presentation.introductions do
    for fragment in paragraph.fragments do
      if let .reference reference := fragment then
        if let some hover ← presentationReferenceHover? reference then
          result := appendDistinctHovers result #[hover]
  return result

private def notationHovers
    (notations : Array DeclarationNotation) : MetaM (Array LeanHover) := do
  let mut result := #[]
  for entry in notations do
    if !entry.latex.trimAscii.isEmpty then
      try
        result := appendDistinctHovers result #[←
          Informalization.MassotMiller.LeanHoverInfo.ofDeclaration
            entry.latex entry.declaration]
      catch _ => pure ()
  return result

private def theoremHovers (source : Discourse.Document) : MetaM (Array LeanHover) := do
  let binders ← localBinderHovers
  let presented ← presentationHovers source.theoremPresentation?
  let notations ← notationHovers source.declarationNotations
  -- Presentation mappings come first because they relate conventional paper
  -- symbols such as `B` to Lean binders such as `blockForm`.
  return appendDistinctHovers (appendDistinctHovers presented notations) binders

private def scopeHovers (scope : Scope) : MetaM (Array LeanHover) := do
  let mut result := #[]
  for binding in scope.symbols.visibleBindings do
    try
      result := appendDistinctHovers result #[←
        Informalization.MassotMiller.LeanHoverInfo.ofExpr
          binding.symbol binding.key.source]
    catch _ => pure ()
  return result

private def hoversWithScope (source : Discourse.Document) (scope : Scope)
    (references : Array EvidenceRef) (content : Array Fragment)
    (base : Array LeanHover) : MetaM (Array LeanHover) :=
  match contextFor? source scope references content with
  | some localContext => withLCtx localContext #[] do
      return appendDistinctHovers base (← scopeHovers scope)
  | none => return appendDistinctHovers base (← scopeHovers scope)

private abbrev LeanEvidence := Informalization.MassotMiller.LeanEvidenceInfo
private abbrev LeanSourceLocation :=
  Informalization.MassotMiller.LeanSourceLocation

private def evidenceReferenceLabel : EvidenceRef → String
  | .statementNode node => s!"statement node {node.index}"
  | .statementArgument node position =>
      s!"statement argument {node.index}.{position}"
  | .proofStep step => s!"proof step {step}"
  | .proofPremise step premise => s!"proof premise {step}.{premise}"
  | .formalFallback fallback => s!"formal fallback {fallback}"

private def declarationSource? (declaration : Name) : MetaM (Option LeanSourceLocation) := do
  try
    let some ranges ← Lean.findDeclarationRanges? declaration | return none
    let environment ← getEnv
    let moduleName ← match ← Lean.findModuleOf? declaration with
      | some name => pure name
      | none => pure environment.mainModule
    let range := ranges.selectionRange
    return some {
      moduleName := moduleName.toString
      line := range.pos.line
      column := range.pos.column
      endLine := range.endPos.line
      endColumn := range.endPos.column
    }
  catch _ => return none

private def renderEvidenceExpr (localContext? : Option LocalContext)
    (expression : Expr) : MetaM String :=
  let render : MetaM String := do
    return (← ppExpr (← instantiateMVars expression)).pretty
  match localContext? with
  | some localContext => withLCtx localContext #[] render
  | none => render

private def leanEvidenceInfo? (item : EvidenceItem) : MetaM (Option LeanEvidence) := do
  try
    let term ← renderEvidenceExpr item.localContext? item.formal
    let type ← match item.expected? with
      | some expected => renderEvidenceExpr item.localContext? expected
      | none =>
          let infer : MetaM Expr := inferType item.formal
          let inferred ← match item.localContext? with
            | some localContext => withLCtx localContext #[] infer
            | none => infer
          renderEvidenceExpr item.localContext? inferred
    let expected? ← item.expected?.mapM (renderEvidenceExpr item.localContext?)
    let source? ← match item.declaration? with
      | some declaration => declarationSource? declaration
      | none => pure none
    return some {
      label := evidenceReferenceLabel item.reference
      declaration? := item.declaration?.map (·.toString)
      type
      expected?
      term
      source?
    }
  catch _ => return none

private def leanEvidenceFor (source : Discourse.Document)
    (references : Array EvidenceRef) : MetaM (Array LeanEvidence) := do
  let mut result := #[]
  let mut seen := #[]
  for reference in references do
    if seen.contains reference then continue
    seen := seen.push reference
    let some item := source.evidenceIndex.find? (·.reference == reference) | continue
    if let some evidence ← leanEvidenceInfo? item then
      result := result.push evidence
  return result

private def renderWithScope (source : Discourse.Document) (scope : Scope)
    (references : Array EvidenceRef) (content : Array Fragment) : MetaM String :=
  match contextFor? source scope references content with
  | some localContext => withLCtx localContext #[] <|
      renderFragments scope content
  | none => renderFragments scope content

mutual
  private partial def realizeDetail (source : Discourse.Document) (scope : Scope)
      (baseHovers : Array LeanHover)
      (origin : Discourse.SupportOrigin) (supportEvidence : Array EvidenceRef)
      (detail : Discourse.Detail) : MetaM Detail := do
    let localContext? := contextForReference? source detail.primaryEvidence
    let scope := scope.descend |>.enter
      (some detail.primaryEvidence) detail.derivation? localContext?
    let content := canonicalMoveContent source detail.kind detail.derivation?
    let text ← renderWithScope source scope detail.evidence content
    let referenceHovers ← hoversWithScope source scope detail.evidence content baseHovers
    let leanEvidence ← leanEvidenceFor source detail.evidence
    let children ← realizeSupports source scope baseHovers detail.supports
    return {
      kind := detail.kind
      semanticDepth := detail.semanticDepth
      content
      text
      referenceHovers
      leanEvidence
      primaryEvidence := detail.primaryEvidence
      evidence := detail.evidence
      supportOrigin? := some origin
      supportEvidence
      children
      derivation? := detail.derivation?
    }

  private partial def realizeSupports (source : Discourse.Document) (scope : Scope)
      (baseHovers : Array LeanHover)
      (supports : Array Discourse.Support) : MetaM (Array Detail) := do
    let mut details := #[]
    for support in supports do
      for child in support.children do
        details := details.push (← realizeDetail source scope baseHovers support.origin
          support.evidence child)
    return details
end

/-- Realize a typed discourse plan as concise cryptographic prose.  Prose
frames are selected by generic rule roles, while every displayed formula is
rendered from the canonical operands attached to that rule application. -/
def document (source : Discourse.Document) : MetaM Document := do
  let rootSymbols := rootSymbolScope source (← getLCtx)
  let baseHovers ← theoremHovers source
  let declarationHover? ← match source.rootDeclaration? with
    | some declaration =>
        try
          pure (some (← Informalization.MassotMiller.LeanHoverInfo.ofDeclaration
            "" declaration))
        catch _ => pure none
    | none => pure none
  let mut sentences := #[]
  -- A residual blind-winning obligation establishes the game currently in
  -- focus.  Subsequent estimates reuse that already introduced object even
  -- when their checked proof expands it through a generic helper theorem.
  let mut foregroundBlindGame? : Option GameTerm := none
  for move in source.moves do
    let rootScope : Scope := {
      symbols := rootSymbols
      declarationNotations := source.declarationNotations
    }
    let localContext? := move.primaryEvidence?.bind
      (contextForReference? source)
    let scope : Scope := rootScope.enter move.primaryEvidence? move.derivation?
      localContext?
    let content := canonicalMoveContent source move.kind move.derivation?
      foregroundBlindGame? move.supports
    -- The root claim was decoded in the theorem telescope.  Rendering it in
    -- an inner proof-step context can replace its binders by unrelated local
    -- identifiers (or generated `_uniq` names), so theorem-level moves stay
    -- in that same telescope.  Step-local formulas still use their retained
    -- evidence context below.
    let theoremLevel := move.kind == .stateSecurityGoal ||
      move.kind == .combineConditionalEquivalenceBlind
    unless content.isEmpty do
      let text ← if theoremLevel then
        renderFragments scope content
      else
        renderWithScope source scope move.evidence content
      let referenceHovers ← if theoremLevel then
        pure (appendDistinctHovers baseHovers (← scopeHovers scope))
      else
        hoversWithScope source scope move.evidence content baseHovers
      let leanEvidence ← leanEvidenceFor source move.evidence
      let details ← realizeSupports source scope baseHovers move.supports
      sentences := sentences.push {
        moveId := move.id
        kind := move.kind
        semanticDepth := move.semanticDepth
        content
        text
        referenceHovers
        leanEvidence
        primaryEvidence? := move.primaryEvidence?
        evidence := move.evidence
        details
        derivation? := move.derivation?
      }
    if move.kind == .remainingBlindWinningObligation then
      foregroundBlindGame? :=
        (conclusion? move.derivation?).bind upperBound? |>.bind
          BoundTerm.blindWinningGame?
  return {
    security := source.security
    rootClaim? := source.rootClaim?
    theoremPresentation? := source.theoremPresentation?
    declarationHover?
    theoremReferenceHovers := baseHovers
    planKind := source.planKind
    sentences
    evidenceIndex := source.evidenceIndex
  }

private def proofRuleCode : ProofRuleRole -> String
  | .exactEquivalence => "exact-equivalence"
  | .construction => "construction"
  | .distanceBound => "distance-bound"
  | .advantageBound => "advantage-bound"
  | .ignoreGameMBO => "ignore-game-mbo"
  | .triangleHybrid => "triangle-hybrid"
  | .hTechnique => "h-technique"
  | .conditionalEquivalence => "conditional-equivalence"
  | .conditionalEquivalenceUnderRestriction => "conditional-equivalence-under-restriction"
  | .collisionConditionalEquivalence => "collision-conditional-equivalence"
  | .conditionalEquivalenceToBlindWinning => "conditional-equivalence-to-blind-winning"
  | .blindWinningBound => "blind-winning-bound"
  | .blindWinningToNonadaptive => "blind-winning-to-nonadaptive"
  | .nonadaptiveQueriesFixed => "nonadaptive-queries-fixed"
  | .commonDomainDataProcessing => "common-domain-data-processing"
  | .restrictionApplicationEquation => "restriction-application-equation"
  | .conditionalUniformOutputs => "conditional-uniform-outputs"
  | .distinctTerminalInputs => "distinct-terminal-inputs"
  | .gamePlayingFundamentalLemma => "game-playing-fundamental-lemma"
  | .coupling => "coupling"
  | .representativeSelection => "representative-selection"
  | .winnability => "winnability"
  | .signedExpansion => "signed-expansion"
  | .counting => "counting"
  | .collisionProbabilityBound => "collision-probability-bound"
  | .collisionMassBound => "collision-mass-bound"
  | .birthdayBound => "birthday-bound"
  | .scalarClosure => "scalar-closure"
  | .arithmetic => "arithmetic"
  | .rewriting => "rewriting"
  | .monotonicity => "monotonicity"
  | .custom name => "custom:" ++ name.toString

private def moveKindCode : MoveKind -> String
  | .stateSecurityGoal => "state-security-goal"
  | .conditionalEquivalence => "conditional-equivalence"
  | .conditionalEquivalenceReduction => "conditional-equivalence-reduction"
  | .remainingBlindWinningObligation => "remaining-blind-winning-obligation"
  | .blindWinningEstimate => "blind-winning-estimate"
  | .combineConditionalEquivalenceBlind => "combine-conditional-equivalence-blind"
  | .hTechnique => "h-technique"
  | .hybrid => "hybrid"
  | .gameHop => "game-hop"
  | .counting => "counting"
  | .exactEquivalence => "exact-equivalence"
  | .ignoreCollisionMBO => "ignore-collision-mbo"
  | .registeredRule role => "registered-rule/" ++ proofRuleCode role
  | .formalFallback => "formal-fallback"

private def planKindCode : Plan.Kind -> String
  | .conditionalEquivalenceBlind => "conditional-equivalence/blind-winning"
  | .exactEquivalence => "exact-equivalence"
  | .conditionalEquivalence => "conditional-equivalence"
  | .blindWinningBound => "blind-winning-bound"
  | .hTechnique => "h-technique"
  | .hybrid => "hybrid"
  | .gameHop => "game-hop"
  | .counting => "counting"
  | .generic => "generic"
  | .fallback => "fallback"

private def evidenceRefJson : EvidenceRef -> Json
  | .statementNode node => Json.mkObj [
      ("kind", .str "statement-node"), ("id", .num node.index)]
  | .statementArgument node position => Json.mkObj [
      ("kind", .str "statement-argument"),
      ("node", .num node.index), ("position", .num position)]
  | .proofStep step => Json.mkObj [
      ("kind", .str "proof-step"), ("id", .num step)]
  | .proofPremise step premise => Json.mkObj [
      ("kind", .str "proof-premise"),
      ("step", .num step), ("premise", .num premise)]
  | .formalFallback fallback => Json.mkObj [
      ("kind", .str "formal-fallback"), ("id", .num fallback)]

private def optionEvidenceRefJson : Option EvidenceRef -> Json
  | some reference => evidenceRefJson reference
  | none => .null

private def comparedRoleCode : ArgumentRole -> String
  | .sourceSystem => "source-system"
  | .targetSystem => "target-system"
  | .realSystem => "real-system"
  | .idealSystem => "ideal-system"
  | role => reprStr role

private def optionComparedRoleJson : Option ArgumentRole -> Json
  | some role => .str (comparedRoleCode role)
  | none => .null

private def securityJson (context : SecurityContext) : Json := Json.mkObj [
  ("proposition", evidenceRefJson (.statementNode context.proposition)),
  ("advantage", optionEvidenceRefJson (context.advantage?.map .statementNode)),
  ("sourceSystem", optionEvidenceRefJson (context.sourceSystem?.map .statementNode)),
  ("targetSystem", optionEvidenceRefJson (context.targetSystem?.map .statementNode)),
  ("sourceRole", optionComparedRoleJson context.sourceRole?),
  ("targetRole", optionComparedRoleJson context.targetRole?),
  ("sourceBaseSystem", optionEvidenceRefJson
    (context.sourceDescription?.map fun value => .statementNode value.base)),
  ("targetBaseSystem", optionEvidenceRefJson
    (context.targetDescription?.map fun value => .statementNode value.base)),
  ("sourceQueryRestriction", optionEvidenceRefJson
    (context.sourceDescription?.bind (·.queryRestriction?) |>.map .statementNode)),
  ("targetQueryRestriction", optionEvidenceRefJson
    (context.targetDescription?.bind (·.queryRestriction?) |>.map .statementNode)),
  ("queryBudget", optionEvidenceRefJson (context.queryBudget?.map (·.evidenceRef))),
  ("bound", optionEvidenceRefJson (context.bound?.map (·.evidenceRef)))
]

/-! ## Canonical artifact serialization

The realized artifact deliberately serializes the canonical operand tree in
addition to prose.  Exact Lean expressions are capabilities of the in-memory
artifact, not a wire format: the JSON boundary exposes only their structural
hashes.  This prevents generated names and kernel-internal syntax from leaking
into a reader-facing report while preserving a stable link for diagnostics. -/

private def exprHashJson (expression : Expr) : Json :=
  .str (toString expression.hash)

private def evidenceKindCode : EvidenceKind → String
  | .declaration => "declaration"
  | .application => "application"
  | .binder => "binder"
  | .proposition => "proposition"
  | .proofTerm => "proof-term"

private def provenanceJson (provenance : Provenance) : Json := Json.mkObj [
  ("expressionHash", exprHashJson provenance.expression),
  ("declaration", match provenance.declaration? with
    | some declaration => .str declaration.toString
    | none => .null),
  ("evidenceKind", .str (evidenceKindCode provenance.evidenceKind))
]

private def transformationJson (transformation : TransformationTerm) : Json :=
  Json.mkObj [
    ("sourceHash", exprHashJson transformation.source),
    ("declaration", match transformation.declaration? with
      | some declaration => .str declaration.toString
      | none => .null),
    ("operandHashes", .arr (transformation.operands.map exprHashJson))
  ]

/-- Serialize a canonical condition without printing its exact Lean source. -/
private def conditionTermJson : ConditionTerm → Json
  | .opaque source => Json.mkObj [
      ("kind", .str "opaque"),
      ("sourceHash", exprHashJson source)
    ]
  | .named source declaration operands => Json.mkObj [
      ("kind", .str "named"),
      ("sourceHash", exprHashJson source),
      ("declaration", .str declaration.toString),
      ("operandHashes", .arr (operands.map exprHashJson))
    ]

mutual
  /-- Serialize a canonical converter as an operand tree without printing its
  checked Lean expression. -/
  private partial def converterTermJson : ConverterTerm → Json
    | .opaque source => Json.mkObj [
        ("kind", .str "opaque"),
        ("sourceHash", exprHashJson source)
      ]
    | .named source declaration operands => Json.mkObj [
        ("kind", .str "named"),
        ("sourceHash", exprHashJson source),
        ("declaration", .str declaration.toString),
        ("operandHashes", .arr (operands.map exprHashJson))
      ]
    | .restriction source declaration operands => Json.mkObj [
        ("kind", .str "restriction"),
        ("sourceHash", exprHashJson source),
        ("declaration", .str declaration.toString),
        ("operandHashes", .arr (operands.map exprHashJson))
      ]
    | .serialComposition source outer inner => Json.mkObj [
        ("kind", .str "serial-composition"),
        ("sourceHash", exprHashJson source),
        ("outer", converterTermJson outer),
        ("inner", converterTermJson inner)
      ]

  /-- Serialize a canonical system as a structural operand tree. -/
  private partial def systemTermJson : SystemTerm → Json
    | .opaque source => Json.mkObj [
        ("kind", .str "opaque"),
        ("sourceHash", exprHashJson source)
      ]
    | .named source declaration operands => Json.mkObj [
        ("kind", .str "named"),
        ("sourceHash", exprHashJson source),
        ("declaration", .str declaration.toString),
        ("operandHashes", .arr (operands.map exprHashJson))
      ]
    | .uniformRandomFunction source inputSpace outputSpace => Json.mkObj [
        ("kind", .str "uniform-random-function"),
        ("sourceHash", exprHashJson source),
        ("inputSpaceHash", exprHashJson inputSpace),
        ("outputSpaceHash", exprHashJson outputSpace)
      ]
    | .uniformRandomPermutation source alphabet => Json.mkObj [
        ("kind", .str "uniform-random-permutation"),
        ("sourceHash", exprHashJson source),
        ("alphabetHash", exprHashJson alphabet)
      ]
    | .presentationQuotient source presentation => Json.mkObj [
        ("kind", .str "presentation-quotient"),
        ("sourceHash", exprHashJson source),
        ("presentation", systemTermJson presentation)
      ]
    | .converterApplication source converter underlying => Json.mkObj [
        ("kind", .str "converter-application"),
        ("sourceHash", exprHashJson source),
        ("converter", converterTermJson converter),
        ("underlying", systemTermJson underlying)
      ]
    | .transform source transformation underlying => Json.mkObj [
        ("kind", .str "transform"),
        ("sourceHash", exprHashJson source),
        ("transformation", transformationJson transformation),
        ("underlying", systemTermJson underlying)
      ]
    | .queryRestriction source budget underlying => Json.mkObj [
        ("kind", .str "query-restriction"),
        ("sourceHash", exprHashJson source),
        ("budgetHash", exprHashJson budget),
        ("underlying", systemTermJson underlying)
      ]
    | .forgetGame source game => Json.mkObj [
        ("kind", .str "forget-game"),
        ("sourceHash", exprHashJson source),
        ("game", gameTermJson game)
      ]

  /-- Serialize a canonical game as a structural operand tree. -/
  private partial def gameTermJson : GameTerm → Json
    | .opaque source => Json.mkObj [
        ("kind", .str "opaque"),
        ("sourceHash", exprHashJson source)
      ]
    | .named source declaration operands => Json.mkObj [
        ("kind", .str "named"),
        ("sourceHash", exprHashJson source),
        ("declaration", .str declaration.toString),
        ("operandHashes", .arr (operands.map exprHashJson))
      ]
    | .enhanceWithMBO source system condition => Json.mkObj [
        ("kind", .str "enhance-with-mbo"),
        ("sourceHash", exprHashJson source),
        ("system", systemTermJson system),
        ("condition", conditionTermJson condition)
      ]
    | .converterApplication source converter underlying => Json.mkObj [
        ("kind", .str "converter-application"),
        ("sourceHash", exprHashJson source),
        ("converter", converterTermJson converter),
        ("underlying", gameTermJson underlying)
      ]
    | .transform source transformation underlying => Json.mkObj [
        ("kind", .str "transform"),
        ("sourceHash", exprHashJson source),
        ("transformation", transformationJson transformation),
        ("underlying", gameTermJson underlying)
      ]
    | .queryRestriction source budget underlying => Json.mkObj [
        ("kind", .str "query-restriction"),
        ("sourceHash", exprHashJson source),
        ("budgetHash", exprHashJson budget),
        ("underlying", gameTermJson underlying)
      ]
end

/-- Serialize a construction specification without rendering its set
implementation. -/
private def specificationTermJson : SpecificationTerm → Json
  | .opaque source => Json.mkObj [
      ("kind", .str "opaque"),
      ("sourceHash", exprHashJson source)
    ]
  | .singleton source system => Json.mkObj [
      ("kind", .str "singleton"),
      ("sourceHash", exprHashJson source),
      ("system", systemTermJson system)
    ]

/-- Serialize a canonical bound without rendering an opaque scalar formula. -/
private partial def boundTermJson : BoundTerm → Json
  | .expression source => Json.mkObj [
      ("kind", .str "expression"),
      ("sourceHash", exprHashJson source)
    ]
  | .named source declaration operands => Json.mkObj [
      ("kind", .str "named"),
      ("sourceHash", exprHashJson source),
      ("declaration", .str declaration.toString),
      ("operandHashes", .arr (operands.map exprHashJson))
    ]
  | .quadraticCollision source queryBudget alphabet => Json.mkObj [
      ("kind", .str "quadratic-collision"),
      ("sourceHash", exprHashJson source),
      ("queryBudgetHash", exprHashJson queryBudget),
      ("alphabetHash", exprHashJson alphabet)
    ]
  | .statisticalDistance source left right => Json.mkObj [
      ("kind", .str "statistical-distance"),
      ("sourceHash", exprHashJson source),
      ("left", systemTermJson left),
      ("right", systemTermJson right)
    ]
  | .distinguishingAdvantage source kind real ideal => Json.mkObj [
      ("kind", .str "distinguishing-advantage"),
      ("advantageKind", .str (match kind with
        | .fullyDefined => "fully-defined"
        | .ambient => "ambient")),
      ("sourceHash", exprHashJson source),
      ("real", systemTermJson real),
      ("ideal", systemTermJson ideal)
    ]
  | .winningProbability source game => Json.mkObj [
      ("kind", .str "winning-probability"),
      ("sourceHash", exprHashJson source),
      ("game", gameTermJson game)
    ]
  | .blindWinningProbability source game => Json.mkObj [
      ("kind", .str "blind-winning-probability"),
      ("sourceHash", exprHashJson source),
      ("game", gameTermJson game)
    ]
  | .coercion source inner => Json.mkObj [
      ("kind", .str "coercion"),
      ("sourceHash", exprHashJson source),
      ("inner", boundTermJson inner)
    ]

/-- Serialize a canonical mathematical claim and all of its operands. -/
private def claimJson : Claim → Json
  | .systemEquality source left right => Json.mkObj [
      ("kind", .str "system-equality"),
      ("sourceHash", exprHashJson source),
      ("left", systemTermJson left),
      ("right", systemTermJson right)
    ]
  | .conditionalEquivalence source game target => Json.mkObj [
      ("kind", .str "conditional-equivalence"),
      ("sourceHash", exprHashJson source),
      ("game", gameTermJson game),
      ("target", systemTermJson target)
    ]
  | .distanceBound source left right upper => Json.mkObj [
      ("kind", .str "distance-bound"),
      ("sourceHash", exprHashJson source),
      ("left", systemTermJson left),
      ("right", systemTermJson right),
      ("upper", boundTermJson upper)
    ]
  | .advantageBound source kind real ideal upper => Json.mkObj [
      ("kind", .str "advantage-bound"),
      ("advantageKind", .str (match kind with
        | .fullyDefined => "fully-defined"
        | .ambient => "ambient")),
      ("sourceHash", exprHashJson source),
      ("real", systemTermJson real),
      ("ideal", systemTermJson ideal),
      ("upper", boundTermJson upper)
    ]
  | .blindWinningBound source game upper => Json.mkObj [
      ("kind", .str "blind-winning-bound"),
      ("sourceHash", exprHashJson source),
      ("game", gameTermJson game),
      ("upper", boundTermJson upper)
    ]
  | .upperBound source lower upper => Json.mkObj [
      ("kind", .str "upper-bound"),
      ("sourceHash", exprHashJson source),
      ("lower", boundTermJson lower),
      ("upper", boundTermJson upper)
    ]
  | .construction source sourceSpecification converter targetSpecification error =>
      Json.mkObj [
        ("kind", .str "construction"),
        ("sourceHash", exprHashJson source),
        ("sourceSpecification", specificationTermJson sourceSpecification),
        ("converter", converterTermJson converter),
        ("targetSpecification", specificationTermJson targetSpecification),
        ("error", boundTermJson error)
      ]

private def canonicalPropositionJson : CanonicalProposition → Json
  | .claim claim => Json.mkObj [
      ("kind", .str "claim"),
      ("value", claimJson claim)
    ]
  | .opaque source => Json.mkObj [
      ("kind", .str "opaque"),
      ("sourceHash", exprHashJson source)
    ]

private def formulaTermJson : FormulaTerm → Json
  | .converterEquality source left right => Json.mkObj [
      ("kind", .str "converter-equality"),
      ("sourceHash", exprHashJson source),
      ("left", converterTermJson left),
      ("right", converterTermJson right)
    ]
  | .restrictionAttachment source blockForm limit system => Json.mkObj [
      ("kind", .str "restriction-attachment"),
      ("sourceHash", exprHashJson source),
      ("blockFormHash", exprHashJson blockForm),
      ("limitHash", exprHashJson limit),
      ("systemHash", exprHashJson system)
    ]
  | .conditionalProductIdentity source blockForm messages answers => Json.mkObj [
      ("kind", .str "conditional-product-identity"),
      ("sourceHash", exprHashJson source),
      ("blockFormHash", exprHashJson blockForm),
      ("messagesHash", exprHashJson messages),
      ("answersHash", exprHashJson answers)
    ]
  | .distinctSiteInputs source function blockForm message other position
      otherPosition => Json.mkObj [
      ("kind", .str "distinct-site-inputs"),
      ("sourceHash", exprHashJson source),
      ("functionHash", exprHashJson function),
      ("blockFormHash", exprHashJson blockForm),
      ("messageHash", exprHashJson message),
      ("otherMessageHash", exprHashJson other),
      ("positionHash", exprHashJson position),
      ("otherPositionHash", exprHashJson otherPosition)
    ]
  | .terminalInputInjective source function blockForm messages => Json.mkObj [
      ("kind", .str "terminal-input-injective"),
      ("sourceHash", exprHashJson source),
      ("functionHash", exprHashJson function),
      ("blockFormHash", exprHashJson blockForm),
      ("messagesHash", exprHashJson messages)
    ]
  | .walkCollisionBound source parent step initial rank input => Json.mkObj [
      ("kind", .str "walk-collision-bound"),
      ("sourceHash", exprHashJson source),
      ("parentHash", exprHashJson parent),
      ("stepHash", exprHashJson step),
      ("initialHash", exprHashJson initial),
      ("rankHash", exprHashJson rank),
      ("inputHash", exprHashJson input)
    ]
  | .collisionMassBound source blockForm limit messages => Json.mkObj [
      ("kind", .str "collision-mass-bound"),
      ("sourceHash", exprHashJson source),
      ("blockFormHash", exprHashJson blockForm),
      ("limitHash", exprHashJson limit),
      ("messagesHash", exprHashJson messages)
    ]
  | .scalarMonotonicity source lower upper => Json.mkObj [
      ("kind", .str "scalar-monotonicity"),
      ("sourceHash", exprHashJson source),
      ("lowerHash", exprHashJson lower),
      ("upperHash", exprHashJson upper)
    ]

private def obligationSlotJson : ObligationSlot → Json
  | .sourceTotal => Json.mkObj [("kind", .str "source-total")]
  | .targetTotal => Json.mkObj [("kind", .str "target-total")]
  | .sourceNonnegative => Json.mkObj [("kind", .str "source-nonnegative")]
  | .targetNonnegative => Json.mkObj [("kind", .str "target-nonnegative")]
  | .nonnegative => Json.mkObj [("kind", .str "nonnegative")]
  | .equalWeight => Json.mkObj [("kind", .str "equal-weight")]
  | .conditionalEquivalence => Json.mkObj [("kind", .str "conditional-equivalence")]
  | .monotonicity => Json.mkObj [("kind", .str "monotonicity")]
  | .queryBudget => Json.mkObj [("kind", .str "query-budget")]
  | .sideCondition => Json.mkObj [("kind", .str "side-condition")]
  | .custom name => Json.mkObj [
      ("kind", .str "custom"),
      ("name", .str name.toString)
    ]

/-- Serialize the paper-level rule independently of any prose frame. -/
private def derivationRuleJson : DerivationRule → Json
  | .establishSystemEquality => Json.mkObj [("kind", .str "establish-system-equality")]
  | .establishConstruction => Json.mkObj [("kind", .str "establish-construction")]
  | .establishConditionalEquivalence =>
      Json.mkObj [("kind", .str "establish-conditional-equivalence")]
  | .preserveConditionalEquivalence =>
      Json.mkObj [("kind", .str "preserve-conditional-equivalence")]
  | .conditionalEquivalenceToWinning =>
      Json.mkObj [("kind", .str "conditional-equivalence-to-winning")]
  | .conditionalEquivalenceToBlindWinning =>
      Json.mkObj [("kind", .str "conditional-equivalence-to-blind-winning")]
  | .establishBlindWinningBound =>
      Json.mkObj [("kind", .str "establish-blind-winning-bound")]
  | .deriveDistanceBound => Json.mkObj [("kind", .str "derive-distance-bound")]
  | .deriveAdvantageBound => Json.mkObj [("kind", .str "derive-advantage-bound")]
  | .combineBounds => Json.mkObj [("kind", .str "combine-bounds")]
  | .custom name => Json.mkObj [
      ("kind", .str "custom"),
      ("name", .str name.toString)
    ]

/-- Serialize a proof obligation with its mathematical role, optional
canonical proposition, and hashed checked evidence. -/
private def proofObligationJson (obligation : ProofObligation) : Json := Json.mkObj [
  ("slot", obligationSlotJson obligation.slot),
  ("propositionHash", exprHashJson obligation.proposition),
  ("evidenceHash", exprHashJson obligation.evidence),
  ("claim", match obligation.claim? with
    | some claim => claimJson claim
    | none => .null),
  ("provenance", provenanceJson obligation.provenance)
]

/-- Serialize a non-proof rule operand by its stable semantic slot.  The
checked expression and optional type remain hash-addressed backend data. -/
private def canonicalOperandJson (operand : CanonicalOperand) : Json := Json.mkObj [
  ("slot", .str operand.slot.toString),
  ("valueHash", exprHashJson operand.value),
  ("typeHash", match operand.type? with
    | some type => exprHashJson type
    | none => .null)
]

/-- Serialize the canonical application that generated a discourse move. -/
private def derivationApplicationJson (application : DerivationApplication) : Json :=
  Json.mkObj [
    ("rule", derivationRuleJson application.rule),
    ("sourceHash", exprHashJson application.source),
    ("conclusion", canonicalPropositionJson application.conclusion),
    ("formula", match application.formula? with
      | some formula => formulaTermJson formula
      | none => .null),
    ("operands", .arr (application.operands.map canonicalOperandJson)),
    ("obligations", .arr (application.obligations.map proofObligationJson)),
    ("provenance", provenanceJson application.provenance)
  ]

private def optionDerivationJson : Option DerivationApplication → Json
  | some derivation => derivationApplicationJson derivation
  | none => .null

private def supportOriginJson : Discourse.SupportOrigin → Json
  | .macroExpansion => Json.mkObj [("kind", .str "macro-expansion")]
  | .premise position role salience slot? => Json.mkObj [
      ("kind", .str "premise"),
      ("position", .num position),
      ("role", .str (reprStr role)),
      ("salience", .str (reprStr salience)),
      ("semanticSlot", match slot? with
        | some slot => obligationSlotJson slot
        | none => .null)
    ]

private partial def detailJson (detail : Detail) : Json := Json.mkObj [
  ("kind", .str (moveKindCode detail.kind)),
  ("semanticDepth", .num detail.semanticDepth),
  ("text", .str detail.text),
  ("primaryEvidence", evidenceRefJson detail.primaryEvidence),
  ("evidence", .arr (detail.evidence.map evidenceRefJson)),
  ("supportOrigin", match detail.supportOrigin? with
    | some origin => supportOriginJson origin
    | none => .null),
  ("supportEvidence", .arr (detail.supportEvidence.map evidenceRefJson)),
  ("derivation", optionDerivationJson detail.derivation?),
  ("children", .arr (detail.children.map detailJson))
]

private def sentenceJson (sentence : Sentence) : Json := Json.mkObj [
  ("id", .num sentence.moveId),
  ("kind", .str (moveKindCode sentence.kind)),
  ("semanticDepth", .num sentence.semanticDepth),
  ("text", .str sentence.text),
  ("primaryEvidence", match sentence.primaryEvidence? with
    | some reference => evidenceRefJson reference
    | none => .null),
  ("evidence", .arr (sentence.evidence.map evidenceRefJson)),
  ("derivation", optionDerivationJson sentence.derivation?),
  ("details", .arr (sentence.details.map detailJson))
]

/-! The typed `Document` retains exact `Expr` values.  The diagnostic JSON uses
cached structural hashes rather than duplicating large kernel proof terms for
each overlapping fallback region.  A renderer with access to the document can
resolve the stable evidence reference to the exact expression on demand. -/
private def evidenceJson (item : EvidenceItem) : Json := Json.mkObj [
  ("reference", evidenceRefJson item.reference),
  ("declaration", match item.declaration? with
    | some name => .str name.toString
    | none => .null),
  ("formalHash", .str (toString item.formal.hash)),
  ("expectedHash", match item.expected? with
    | some expected => .str (toString expected.hash)
    | none => .null)
  ]

private def presentationTargetJson : PresentationReferenceTarget → Json
  | .theoremBinder name => Json.mkObj [
      ("kind", .str "binder"),
      ("name", .str name.toString)
    ]
  | .declaration name => Json.mkObj [
      ("kind", .str "declaration"),
      ("name", .str name.toString)
    ]

private def presentationFragmentJson : PresentationFragment → Json
  | .text value => Json.mkObj [
      ("kind", .str "text"),
      ("value", .str value)
    ]
  | .reference reference => Json.mkObj [
      ("kind", .str "reference"),
      ("target", presentationTargetJson reference.target),
      ("latex", .str reference.latex),
      ("hoverLatex", .str reference.hoverLatex),
      ("description", .str reference.description)
    ]

private def theoremPresentationJson (presentation : TheoremPresentation) : Json :=
  Json.mkObj [
    ("declaration", .str presentation.declaration.toString),
    ("title", .str presentation.title),
    ("introductions", .arr <| presentation.introductions.map fun paragraph =>
      .arr (paragraph.fragments.map presentationFragmentJson))
  ]

/-- Serialize the semantic discourse artifact.  The prose and its formal
evidence references are deliberately shipped together. -/
def Document.toJson (result : Document) : Json := Json.mkObj [
  ("planKind", .str (planKindCode result.planKind)),
  ("security", match result.security with
    | some context => securityJson context
    | none => .null),
  ("rootClaim", match result.rootClaim? with
    | some claim => claimJson claim
    | none => .null),
  ("theoremPresentation", match result.theoremPresentation? with
    | some presentation => theoremPresentationJson presentation
    | none => .null),
  ("moves", .arr (result.sentences.map sentenceJson)),
  ("evidenceIndex", .arr (result.evidenceIndex.map evidenceJson))
]

def Document.toJsonString (result : Document) : String :=
  result.toJson.pretty

end Informalization.Semantics.Realize

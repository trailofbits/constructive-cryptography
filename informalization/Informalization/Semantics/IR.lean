/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# Semantic intermediate representation

This module is the typed boundary between elaborated Lean expressions and
language planning.  It deliberately contains no rendered prose.  Every node
retains the expression from which it was recovered, together with the
declaration that supplied its semantic role when one is known.
-/

namespace Informalization.Semantics

open Lean

/-- How a semantic fact was recovered from elaborated Lean. -/
inductive EvidenceKind where
  | declaration
  | application
  | binder
  | proposition
  | proofTerm
  deriving Inhabited, BEq, Repr

/-- Traceability from a semantic node back to checked Lean.

`expression` is the exact elaborated expression represented by the node.
`declaration?` identifies the registered declaration that justified the
classification.  Neither field is a display string. -/
structure Provenance where
  expression : Expr
  declaration? : Option Name := none
  evidenceKind : EvidenceKind := .application
  deriving Inhabited, BEq, Repr

/-- Mathematical roles played by named objects in a theorem context. -/
inductive EntityRole where
  | carrier
  | randomSystem
  | game
  | converter
  | distinguisher
  | environment
  | transcript
  | event
  | collisionCondition
  | queryBudget
  | probability
  | distribution
  | errorBound
  | simulator
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Semantic constructors for system-valued expressions. -/
inductive SystemRole where
  | atom
  | uniformRandomFunction
  | uniformRandomPermutation
  | presentationQuotient
  | converterApplication
  | queryRestriction
  | forgetGame
  | transform
  | parallelComposition
  | serialComposition
  | idealFunctionality
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Semantic constructors for game-valued expressions. A game obtained by
enhancing a system with an MBO is not classified as a kind of system. -/
inductive GameRole where
  | atom
  | enhanceWithMBO
  | queryRestriction
  | transform
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Semantic constructors for converter-valued expressions. -/
inductive ConverterRole where
  | atom
  | queryRestriction
  | blockRestriction
  | serialComposition
  | parallelComposition
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Scalar quantities that occur in security statements and proofs. -/
inductive QuantityRole where
  | distinguishingAdvantage
  | statisticalDistance
  | winningProbability
  | blindWinningProbability
  | badEventProbability
  | systemWeight
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Relations between the mathematical objects represented by arguments. -/
inductive RelationRole where
  | equality
  | upperBound
  | indistinguishability
  | advantageBound
  | conditionalEquivalence
  | gameEquivalence
  | construction
  | reduction
  | eventImplication
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Paper-level roles of proof-producing declarations.

These constructors classify mathematical proof moves, not Lean tactics. -/
inductive ProofRuleRole where
  | exactEquivalence
  | construction
  | distanceBound
  | advantageBound
  | ignoreGameMBO
  | triangleHybrid
  | hTechnique
  | conditionalEquivalence
  | conditionalEquivalenceUnderRestriction
  | collisionConditionalEquivalence
  | conditionalEquivalenceToBlindWinning
  | blindWinningBound
  | blindWinningToNonadaptive
  | nonadaptiveQueriesFixed
  | commonDomainDataProcessing
  | restrictionApplicationEquation
  | conditionalUniformOutputs
  | distinctTerminalInputs
  | gamePlayingFundamentalLemma
  | coupling
  | representativeSelection
  | winnability
  | signedExpansion
  | counting
  | collisionProbabilityBound
  | collisionMassBound
  | birthdayBound
  | scalarClosure
  | arithmetic
  | rewriting
  | monotonicity
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- The semantic use of an argument of a registered declaration. -/
inductive ArgumentRole where
  | subject
  | inputSpace
  | outputSpace
  | alphabet
  | realSystem
  | idealSystem
  | sourceSystem
  | targetSystem
  | transformedSystem
  | converter
  | game
  | condition
  | queryBudget
  | distinguisher
  | environment
  | transcript
  | event
  | badEvent
  | bound
  | errorTerm
  | probabilityLaw
  | premise (index : Nat)
  | conclusion
  | custom (name : Name)
  deriving Inhabited, BEq, Repr

/-- Importance to a later discourse planner.  This is not a request to hide
Lean evidence; non-primary arguments remain available in expanded views. -/
inductive Salience where
  | primary
  | supporting
  | implementation
  | implicit
  deriving Inhabited, BEq, Repr

/-- A semantically classified argument with exact Lean provenance. -/
structure SemanticArgument where
  role : ArgumentRole
  source : Expr
  provenance : Provenance
  salience : Salience := .primary
  deriving Inhabited, BEq, Repr

/-- A context entity recovered from a binder or declaration. -/
structure EntityExpression where
  role : EntityRole
  source : Expr
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A system expression and the semantically relevant parts used to build it. -/
structure SystemExpression where
  role : SystemRole
  source : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A game expression and the system, MBO, or restriction used to build it. -/
structure GameExpression where
  role : GameRole
  source : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A converter expression and its semantically relevant arguments. -/
structure ConverterExpression where
  role : ConverterRole
  source : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A scalar security quantity such as advantage or bad-event probability. -/
structure QuantityExpression where
  role : QuantityRole
  source : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- A proposition classified independently of its eventual wording. -/
structure PropositionExpression where
  role : RelationRole
  source : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- An application of a mathematically meaningful proof rule.

`source` is the proof term (usually a theorem application) and `conclusion` is
its inferred proposition. -/
structure ProofApplication where
  role : ProofRuleRole
  source : Expr
  conclusion : Expr
  arguments : Array SemanticArgument := #[]
  provenance : Provenance
  deriving Inhabited, BEq, Repr

/-- Nodes passed from semantic recovery to proof and discourse planning. -/
inductive Node where
  | entity (value : EntityExpression)
  | system (value : SystemExpression)
  | game (value : GameExpression)
  | converter (value : ConverterExpression)
  | quantity (value : QuantityExpression)
  | proposition (value : PropositionExpression)
  | proofApplication (value : ProofApplication)
  deriving Inhabited, BEq, Repr

/-- The role of a node, erased only to its declaration-level classification. -/
inductive NodeRole where
  | entity (role : EntityRole)
  | system (role : SystemRole)
  | game (role : GameRole)
  | converter (role : ConverterRole)
  | quantity (role : QuantityRole)
  | proposition (role : RelationRole)
  | proofRule (role : ProofRuleRole)
  deriving Inhabited, BEq, Repr

def Node.role : Node → NodeRole
  | .entity value => .entity value.role
  | .system value => .system value.role
  | .game value => .game value.role
  | .converter value => .converter value.role
  | .quantity value => .quantity value.role
  | .proposition value => .proposition value.role
  | .proofApplication value => .proofRule value.role

def Node.arguments : Node → Array SemanticArgument
  | .entity _ => #[]
  | .system value => value.arguments
  | .game value => value.arguments
  | .converter value => value.arguments
  | .quantity value => value.arguments
  | .proposition value => value.arguments
  | .proofApplication value => value.arguments

def Node.provenance : Node → Provenance
  | .entity value => value.provenance
  | .system value => value.provenance
  | .game value => value.provenance
  | .converter value => value.provenance
  | .quantity value => value.provenance
  | .proposition value => value.provenance
  | .proofApplication value => value.provenance

/-- Stable index of a node in a compositional semantic graph. -/
structure NodeId where
  index : Nat
  deriving Inhabited, BEq, Repr

/-- A decoded argument edge.  `argument` retains the exact source expression
and role; `child` points to that expression's recovered semantic node. -/
structure Edge where
  parent : NodeId
  child : NodeId
  argument : SemanticArgument
  deriving Inhabited, BEq, Repr

/-- Structurally compositional semantic recovery.

Nodes retain their local declaration arguments, while edges record which of
those arguments were themselves decoded.  The flat representation avoids
duplicating shared subexpressions and is directly consumable by proof and
discourse planners. -/
structure Graph where
  root : NodeId
  nodes : Array Node
  edges : Array Edge := #[]
  deriving Inhabited, BEq, Repr

def Graph.rootNode? (graph : Graph) : Option Node :=
  graph.nodes[graph.root.index]?

def Graph.children (graph : Graph) (parent : NodeId) : Array (SemanticArgument × Node) :=
  graph.edges.filterMap fun edge => do
    guard (edge.parent == parent)
    return (edge.argument, ← graph.nodes[edge.child.index]?)

end Informalization.Semantics

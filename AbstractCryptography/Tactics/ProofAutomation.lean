/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomationAttributes
import AbstractCryptography.Categorical.ResourceAlgebra.ConverterTuple
import AbstractCryptography.Categorical.ResourceAlgebra.Filtered

/-!
# Abstract Cryptography proof automation

This opt-in module supplies deterministic assembly commands for the typed
`ResourceAlgebra` presentation.  Every semantic choice remains an explicit
Lean term. Every command targets the typed `ResourceAlgebra` presentation.

The commands implement the paper-level steps of Maurer--Renner 2016.  Jost's
typed attachment and ordered context laws provide the heterogeneous theorem
heads used here; no symmetry or implicit interface rearrangement is assumed.
-/

namespace AbstractCryptography.Categorical

attribute [ac_normalization]
  ResourceAlgebra.attach_identity
  ResourceAlgebra.attach_serial
  ResourceAlgebra.converter_parallel_identity
  ResourceAlgebra.converter_parallel_serial
  ResourceAlgebra.attach_parallel
  ResourceAlgebra.Specification.parallel_singleton
  ResourceAlgebra.Specification.star_idem
  CategoryTheory.Category.id_comp
  CategoryTheory.Category.comp_id
  CategoryTheory.Category.assoc
  zero_add
  add_zero
  Set.mem_singleton_iff

end AbstractCryptography.Categorical

open Lean.Parser.Tactic

/-- Opt-in trace class for the exact public theorem selected by an AC
construction assembler. -/
initialize Lean.registerTraceClass `AbstractCryptography.ProofAutomation.rule

/-- Elaborate the supplied proof against the target before reporting the
selected theorem. -/
syntax (name := acExactRule)
  "ac_exact_rule " str " => " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| ac_exact_rule $label:str => $proof) =>
      closeMainGoalUsing `ac_exact_rule fun target _ => do
        let value ← elabTermEnsuringType proof target
        trace[AbstractCryptography.ProofAutomation.rule] "{label.getString}"
        pure value

/-- Normalize selected categorical AC expressions using only the curated
registry. -/
syntax (name := acNormalize) "ac_normalize" (location)? : tactic

macro_rules
  | `(tactic| ac_normalize $[at $location]?) =>
      `(tactic| simp -failIfUnchanged only [ac_normalization] $[at $location]?)

/-- Trace every rewrite used by `ac_normalize`. -/
syntax (name := acNormalizeTrace) "ac_normalize?" (location)? : tactic

macro_rules
  | `(tactic| ac_normalize? $[at $location]?) =>
      `(tactic|
        set_option trace.Meta.Tactic.simp.rewrite true in
          ac_normalize $[at $location]?)

/-- Close a bookkeeping goal using only assumptions, reflexivity, or the two
curated registries. -/
syntax (name := acRoutine) "ac_routine" : tactic

macro_rules
  | `(tactic| ac_routine) =>
      `(tactic|
        first
          | (solve
              | assumption
              | rfl
              | exact le_rfl
              | exact zero_le _
              | simp_all only [ac_normalization, ac_side_condition])
          | fail "ac_routine could not close the goal with assumptions or the curated AC registries")

/-- Expose the canonical equality, distance, or pointwise obligation for a
singleton or scalar-error construction. -/
syntax (name := acConstruct) "ac_construct" : tactic

macro_rules
  | `(tactic| ac_construct) =>
      `(tactic|
        first
          | apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr
          | apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr
          | apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr
          | apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr
          | apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr
          | fail "ac_construct expected a typed singleton or scalar-error construction goal")

/-- Close a supported construction goal from one explicit mathematical
witness. -/
syntax (name := acConstructUsing) "ac_construct" " using " term : tactic

macro_rules
  | `(tactic| ac_construct using $fact) =>
      `(tactic|
        first
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr $fact
               | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr $fact
               | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr $fact
               | exact $fact)
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr $fact
               | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr $fact
               | exact $fact)
          | fail "ac_construct could not use the supplied equality, distance bound, or pointwise proof")

/-- Close a typed attachment or construction consequence of one explicit
converter equality. -/
syntax (name := acTransport) "ac_transport" " using " term : tactic

macro_rules
  | `(tactic| ac_transport using $same) =>
      `(tactic|
        first
          | exact $same
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq
                $same _
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                $same
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                $same
          | fail "ac_transport expected attachment equality or construction equivalence induced by the supplied converter equality")

/-- Replace the converter in a supplied construction using one explicit
equality. -/
syntax (name := acReplaceConverterInConstruction)
  "ac_transport " term " using " term : tactic

macro_rules
  | `(tactic| ac_transport $construction using $same) =>
      `(tactic|
        first
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | ac_exact_rule "replace converter in exact construction, left-to-right" =>
                   (AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mp $construction
               | ac_exact_rule "replace converter in exact construction, right-to-left" =>
                   (AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mpr $construction)
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | ac_exact_rule "replace converter in approximate construction, left-to-right" =>
                   (AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mp $construction
               | ac_exact_rule "replace converter in approximate construction, right-to-left" =>
                   (AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mpr $construction)
          | fail "ac_transport could not replace the converter in the supplied construction using the supplied equality")

/-- Apply Maurer--Renner's explicit simulator proof step. -/
syntax (name := acSimulator) "ac_simulator " term : tactic

macro_rules
  | `(tactic| ac_simulator $simulator) =>
      `(tactic|
        first
          | refine AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_of_simulator
              $simulator ?_ ?_
          | fail "ac_simulator expected a typed singleton construction into the scalar relaxation of a star specification")

/-- Pull an explicitly compatible relaxation through the outer leg of a
serial construction. -/
syntax (name := acRelax) "ac_relax" " using " term "," term " with " term : tactic

macro_rules
  | `(tactic| ac_relax using $inner, $outer with $compatibility) =>
      `(tactic|
        first
          | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_serial
              $compatibility $inner $outer
          | fail "ac_relax could not apply the typed serial relaxation theorem to the supplied constructions and compatibility proof")

/-- Prove an exact or scalar-error filtered-endpoint construction from
explicit commutation, simulator membership, and equality or distance. -/
syntax (name := acFiltered)
  "ac_filtered" " using " term "," term "," term : tactic

macro_rules
  | `(tactic| ac_filtered using $commutes, $admitted, $fact) =>
      `(tactic|
        first
          | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_of_eq
              $commutes $admitted $fact
          | exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_epsilonRelaxation_of_distance_le
              $commutes $admitted $fact
          | fail "ac_filtered expected a filtered-endpoint construction and matching commutation, simulator-membership, and equality or distance proofs")

/-- Apply the selected fibre-distance triangle inequality through an explicit
intermediate resource. -/
syntax (name := acTriangle) "ac_triangle" " via " term : tactic

macro_rules
  | `(tactic| ac_triangle via $intermediate) =>
      `(tactic|
        first
          | refine (AbstractCryptography.Categorical.ResourceAlgebra.distance_triangle
              _ $intermediate _).trans (add_le_add ?_ ?_)
          | fail "ac_triangle expected a typed resource-distance goal with an additive bound")

/-- Select converter-attachment or ordered-parallel non-expansion. -/
syntax (name := acNonexpand) "ac_nonexpand" : tactic

macro_rules
  | `(tactic| ac_nonexpand) =>
      `(tactic|
        first
          | exact AbstractCryptography.Categorical.ResourceAlgebra.distance_attach_le _ _ _
          | exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_left_le _ _ _
          | exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_right_le _ _ _
          | exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_le _ _ _ _
          | fail "ac_nonexpand expected a converter-attachment or ordered-parallel distance goal")

/-- Derive commutation of two assembled partial converter tuples from
explicit disjoint party sets. -/
syntax (name := acCommuteUsing) "ac_commute" " using " term : tactic

macro_rules
  | `(tactic| ac_commute using $disjoint) =>
      `(tactic|
        first
          | exact AbstractCryptography.Categorical.ResourceAlgebra.Finite.ConverterTuple.converter_partial_commute_of_disjoint
              _ _ _ _ $disjoint
          | fail "ac_commute expected assembled partial converter tuples and explicit disjointness")

/-- Compose two constructions in execution order. -/
syntax (name := acCompose) "ac_compose " term "," term : tactic

macro_rules
  | `(tactic| ac_compose $inner, $outer) =>
      `(tactic|
        first
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial" =>
                   AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                     $inner $outer
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
                   AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                     $inner $outer
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc] using
                       (AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                         $inner $outer))
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                         $inner $outer)))
          | (change AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial" =>
                   AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                     $inner $outer
               | ac_exact_rule
                   "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                         $inner $outer)))
          | fail "ac_compose expected two composable typed construction proofs")

/-- Compose two simulator-target constructions using one explicit
composition-order commutation equality. -/
syntax (name := acComposeSimulators)
  "ac_compose_simulators " term "," term " using " term : tactic

macro_rules
  | `(tactic| ac_compose_simulators $inner, $outer using $commutes) =>
      `(tactic|
        first
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators
                $inner $outer $commutes
          | fail "ac_compose_simulators expected two typed simulator-target constructions and an explicit composition-order commutation equality")

/-- Compose two construction proofs in ordered parallel. -/
syntax (name := acParallel) "ac_parallel " term "," term : tactic

macro_rules
  | `(tactic| ac_parallel $left, $right) =>
      `(tactic|
        first
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel
                $left $right
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel
                $left $right
          | fail "ac_parallel expected two typed constructions for ordered parallel composition")

/-- Extend a construction by a fixed right specification context. -/
syntax (name := acContextLeft)
  "ac_context_left " term " using " term : tactic

macro_rules
  | `(tactic| ac_context_left $context using $construction) =>
      `(tactic|
        first
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context
                $construction $context
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context
                $construction $context
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context
                (AbstractCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $construction $context
          | fail "ac_context_left expected a typed construction and a fixed right specification context")

/-- Extend a construction by a fixed left specification context. -/
syntax (name := acContextRight)
  "ac_context_right " term " using " term : tactic

macro_rules
  | `(tactic| ac_context_right $context using $construction) =>
      `(tactic|
        first
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context
                $context $construction
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context
                $context $construction
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context" =>
              AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context
                (AbstractCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $context $construction
          | fail "ac_context_right expected a typed construction and a fixed left specification context")

open Lean in
/-- Build the proof term underlying `ac_chain` by folding named constructions
from left to right. -/
private meta partial def mkACConstructionChainTerm
    {m : Type → Type} [Monad m] [MonadQuotation m]
    (constructions : TSyntaxArray `term) (kind : Nat) : m Term := do
  if h : 0 < constructions.size then
    let rec go (index : Nat) (accumulator : Term) : m Term := do
      if hindex : index < constructions.size then
        let next := constructions[index]
        let combined ← match kind with
          | 0 =>
              ``(AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                  $accumulator $next)
          | 1 =>
              ``(AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                  $accumulator $next)
          | _ =>
              ``(AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                  $accumulator $next)
        go (index + 1) combined
      else
        pure accumulator
    go 1 constructions[0]
  else
    ``(by fail "ac_chain requires at least two named construction proofs")

/-- Compose an explicit list of at least two named typed constructions. -/
syntax (name := acChain) "ac_chain" "[" term,* "]" : tactic

macro_rules
  | `(tactic| ac_chain [$constructions:term,*]) => do
      let constructionArray := constructions.getElems
      if constructionArray.size < 2 then
        Lean.Macro.throwError
          "ac_chain requires at least two named construction proofs"
      let exactChain ← mkACConstructionChainTerm constructionArray 0
      let scalarChain ← mkACConstructionChainTerm constructionArray 1
      let approximateChain ← mkACConstructionChainTerm constructionArray 2
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial" =>
              $exactChain
          | ac_exact_rule "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
              $scalarChain
          | ac_exact_rule "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial" =>
              $approximateChain
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc] using $exactChain)
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $scalarChain)
          | ac_exact_rule
              "AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $approximateChain)
          | fail "ac_chain could not compose the supplied typed construction proofs")

open Lean Elab Tactic in
/-- Check one bounded candidate while restoring the complete tactic state. -/
private def acRuleAppliesWithoutChangingGoal
    (candidate : TSyntax `tactic) : TacticM Bool := do
  let saved ← saveState
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic candidate
    restoreState saved
    pure true
  catch _ =>
    restoreState saved
    pure false

open Lean Elab Tactic

/-- Report the categorical AC rules whose conclusions match the current goal.
The fixed table performs no environment search. -/
elab "ac?" : tactic => withMainContext do
  let exactSingleton ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr)
  let scalarSingleton ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr)
  let scalarGeneral ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr)
  let approximateSingleton ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr)
  let approximateGeneral ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr)
  let simulator ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_of_simulator)
  let relaxation ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_serial)
  let filteredExact ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_of_eq)
  let filteredScalar ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_epsilonRelaxation_of_distance_le)
  let exactSerial ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial)
  let scalarSerial ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation)
  let approximateSerial ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial)
  let simulatorSerial ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators)
  let exactParallel ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel)
  let approximateParallel ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel)
  let exactLeftContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context)
  let exactRightContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context)
  let approximateLeftContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context)
  let approximateRightContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context)
  let relaxedLeftContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context)
  let relaxedRightContext ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context)
  let distanceTriangle ← `(tactic|
    refine (AbstractCryptography.Categorical.ResourceAlgebra.distance_triangle
      _ ?_ _).trans (add_le_add ?_ ?_))
  let attachmentNonexpansion ← `(tactic|
    exact AbstractCryptography.Categorical.ResourceAlgebra.distance_attach_le _ _ _)
  let parallelLeftNonexpansion ← `(tactic|
    exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_left_le _ _ _)
  let parallelRightNonexpansion ← `(tactic|
    exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_right_le _ _ _)
  let parallelJointNonexpansion ← `(tactic|
    exact AbstractCryptography.Categorical.ResourceAlgebra.distance_parallel_le _ _ _ _)
  let tupleCommutation ← `(tactic|
    apply AbstractCryptography.Categorical.ResourceAlgebra.Finite.ConverterTuple.converter_partial_commute_of_disjoint)
  let candidates := #[
    ("ac_construct — constructs_singleton_iff", exactSingleton),
    ("ac_construct — constructs_singleton_epsilonRelaxation_iff", scalarSingleton),
    ("ac_construct — constructs_epsilonRelaxation_iff", scalarGeneral),
    ("ac_construct — constructsWithin_singleton_iff", approximateSingleton),
    ("ac_construct — constructsWithin_iff", approximateGeneral),
    ("ac_simulator simulator — constructs_of_simulator", simulator),
    ("ac_relax using inner, outer with compatibility — Constructs.relax_serial", relaxation),
    ("ac_filtered using commutation, membership, equality — filteredAt_constructs_of_eq", filteredExact),
    ("ac_filtered using commutation, membership, distance — filteredAt_constructs_epsilonRelaxation_of_distance_le", filteredScalar),
    ("ac_compose inner, outer — Constructs.serial", exactSerial),
    ("ac_compose inner, outer — Constructs.serial_epsilonRelaxation", scalarSerial),
    ("ac_compose inner, outer — ConstructsWithin.serial", approximateSerial),
    ("ac_compose_simulators inner, outer using commutation — Constructs.serial_simulators", simulatorSerial),
    ("ac_parallel left, right — Constructs.parallel", exactParallel),
    ("ac_parallel left, right — ConstructsWithin.parallel", approximateParallel),
    ("ac_context_left context using construction — Constructs.left_context", exactLeftContext),
    ("ac_context_right context using construction — Constructs.right_context", exactRightContext),
    ("ac_context_left context using construction — ConstructsWithin.left_context", approximateLeftContext),
    ("ac_context_right context using construction — ConstructsWithin.right_context", approximateRightContext),
    ("ac_context_left context using construction — Constructs.relax_left_context", relaxedLeftContext),
    ("ac_context_right context using construction — Constructs.relax_right_context", relaxedRightContext),
    ("ac_triangle via intermediate — distance_triangle", distanceTriangle),
    ("ac_nonexpand — distance_attach_le", attachmentNonexpansion),
    ("ac_nonexpand — distance_parallel_left_le", parallelLeftNonexpansion),
    ("ac_nonexpand — distance_parallel_right_le", parallelRightNonexpansion),
    ("ac_nonexpand — distance_parallel_le", parallelJointNonexpansion),
    ("ac_commute using disjointness — converter_partial_commute_of_disjoint", tupleCommutation)
  ]
  let mut applicable : Array String := #[]
  for (label, candidate) in candidates do
    if ← acRuleAppliesWithoutChangingGoal candidate then
      applicable := applicable.push label
  if applicable.isEmpty then
    logInfo "No categorical AC rule in the bounded diagnostic table matches this goal."
  else
    logInfo m!"Categorical AC rule candidates (goal unchanged):\n  {
      "\n  ".intercalate applicable.toList}"

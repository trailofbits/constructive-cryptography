/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptography.Tactics.ProofAutomationAttributes
import ConstructiveCryptography.Categorical.ResourceAlgebra.ConverterTuple
import ConstructiveCryptography.Categorical.ResourceAlgebra.Filtered

/-!
# Constructive Cryptography proof automation

This opt-in module supplies deterministic assembly commands for the typed
`ResourceAlgebra` presentation.  Every semantic choice remains an explicit
Lean term. Every command targets the typed `ResourceAlgebra` presentation.

The commands implement the paper-level steps of Maurer--Renner 2016.  Jost's
typed attachment and ordered context laws provide the heterogeneous theorem
heads used here; no symmetry or implicit interface rearrangement is assumed.
-/

namespace ConstructiveCryptography.Categorical

attribute [cc_normalization]
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

end ConstructiveCryptography.Categorical

open Lean.Parser.Tactic

/-- Opt-in trace class for the exact public theorem selected by a CC
construction assembler. -/
initialize Lean.registerTraceClass `ConstructiveCryptography.ProofAutomation.rule

/-- Elaborate the supplied proof against the target before reporting the
selected theorem. -/
syntax (name := ccExactRule)
  "cc_exact_rule " str " => " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| cc_exact_rule $label:str => $proof) =>
      closeMainGoalUsing `cc_exact_rule fun target _ => do
        let value ← elabTermEnsuringType proof target
        trace[ConstructiveCryptography.ProofAutomation.rule] "{label.getString}"
        pure value

/-- Normalize selected categorical CC expressions using only the curated
registry. -/
syntax (name := ccNormalize) "cc_normalize" (location)? : tactic

macro_rules
  | `(tactic| cc_normalize $[at $location]?) =>
      `(tactic| simp -failIfUnchanged only [cc_normalization] $[at $location]?)

/-- Trace every rewrite used by `cc_normalize`. -/
syntax (name := ccNormalizeTrace) "cc_normalize?" (location)? : tactic

macro_rules
  | `(tactic| cc_normalize? $[at $location]?) =>
      `(tactic|
        set_option trace.Meta.Tactic.simp.rewrite true in
          cc_normalize $[at $location]?)

/-- Close a bookkeeping goal using only assumptions, reflexivity, or the two
curated registries. -/
syntax (name := ccRoutine) "cc_routine" : tactic

macro_rules
  | `(tactic| cc_routine) =>
      `(tactic|
        first
          | (solve
              | assumption
              | rfl
              | exact le_rfl
              | exact zero_le _
              | simp_all only [cc_normalization, cc_side_condition])
          | fail "cc_routine could not close the goal with assumptions or the curated CC registries")

/-- Expose the canonical equality, distance, or pointwise obligation for a
singleton or scalar-error construction. -/
syntax (name := ccConstruct) "cc_construct" : tactic

macro_rules
  | `(tactic| cc_construct) =>
      `(tactic|
        first
          | apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr
          | apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr
          | apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr
          | fail "cc_construct expected a typed singleton or scalar-error construction goal")

/-- Close a supported construction goal from one explicit mathematical
witness. -/
syntax (name := ccConstructUsing) "cc_construct" " using " term : tactic

macro_rules
  | `(tactic| cc_construct using $fact) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr $fact
               | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr $fact
               | exact $fact)
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr $fact
               | exact $fact)
          | fail "cc_construct could not use the supplied equality, distance bound, or pointwise proof")

/-- Close a typed attachment or construction consequence of one explicit
converter equality. -/
syntax (name := ccTransport) "cc_transport" " using " term : tactic

macro_rules
  | `(tactic| cc_transport using $same) =>
      `(tactic|
        first
          | exact $same
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.attach_eq_of_converter_eq
                $same _
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                $same
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                $same
          | fail "cc_transport expected attachment equality or construction equivalence induced by the supplied converter equality")

/-- Replace the converter in a supplied construction using one explicit
equality. -/
syntax (name := ccReplaceConverterInConstruction)
  "cc_transport " term " using " term : tactic

macro_rules
  | `(tactic| cc_transport $construction using $same) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule "replace converter in exact construction, left-to-right" =>
                   (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in exact construction, right-to-left" =>
                   (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mpr $construction)
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule "replace converter in approximate construction, left-to-right" =>
                   (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in approximate construction, right-to-left" =>
                   (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mpr $construction)
          | fail "cc_transport could not replace the converter in the supplied construction using the supplied equality")

/-- Apply Maurer--Renner's explicit simulator proof step. -/
syntax (name := ccSimulator) "cc_simulator " term : tactic

macro_rules
  | `(tactic| cc_simulator $simulator) =>
      `(tactic|
        first
          | refine ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_of_simulator
              $simulator ?_ ?_
          | fail "cc_simulator expected a typed singleton construction into the scalar relaxation of a star specification")

/-- Pull an explicitly compatible relaxation through the outer leg of a
serial construction. -/
syntax (name := ccRelax) "cc_relax" " using " term "," term " with " term : tactic

macro_rules
  | `(tactic| cc_relax using $inner, $outer with $compatibility) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_serial
              $compatibility $inner $outer
          | fail "cc_relax could not apply the typed serial relaxation theorem to the supplied constructions and compatibility proof")

/-- Prove an exact or scalar-error filtered-endpoint construction from
explicit commutation, simulator membership, and equality or distance. -/
syntax (name := ccFiltered)
  "cc_filtered" " using " term "," term "," term : tactic

macro_rules
  | `(tactic| cc_filtered using $commutes, $admitted, $fact) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_of_eq
              $commutes $admitted $fact
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_epsilonRelaxation_of_distance_le
              $commutes $admitted $fact
          | fail "cc_filtered expected a filtered-endpoint construction and matching commutation, simulator-membership, and equality or distance proofs")

/-- Apply the selected fibre-distance triangle inequality through an explicit
intermediate resource. -/
syntax (name := ccTriangle) "cc_triangle" " via " term : tactic

macro_rules
  | `(tactic| cc_triangle via $intermediate) =>
      `(tactic|
        first
          | refine (ConstructiveCryptography.Categorical.ResourceAlgebra.distance_triangle
              _ $intermediate _).trans (add_le_add ?_ ?_)
          | fail "cc_triangle expected a typed resource-distance goal with an additive bound")

/-- Select converter-attachment or ordered-parallel non-expansion. -/
syntax (name := ccNonexpand) "cc_nonexpand" : tactic

macro_rules
  | `(tactic| cc_nonexpand) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_attach_le _ _ _
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_left_le _ _ _
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_right_le _ _ _
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_le _ _ _ _
          | fail "cc_nonexpand expected a converter-attachment or ordered-parallel distance goal")

/-- Derive commutation of two assembled partial converter tuples from
explicit disjoint party sets. -/
syntax (name := ccCommuteUsing) "cc_commute" " using " term : tactic

macro_rules
  | `(tactic| cc_commute using $disjoint) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.Categorical.ResourceAlgebra.Finite.ConverterTuple.converter_partial_commute_of_disjoint
              _ _ _ _ $disjoint
          | fail "cc_commute expected assembled partial converter tuples and explicit disjointness")

/-- Compose two constructions in execution order. -/
syntax (name := ccCompose) "cc_compose " term "," term : tactic

macro_rules
  | `(tactic| cc_compose $inner, $outer) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial" =>
                   ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
                   ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc] using
                       (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                         $inner $outer))
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                         $inner $outer)))
          | (change ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial" =>
                   ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                         $inner $outer)))
          | fail "cc_compose expected two composable typed construction proofs")

/-- Compose two simulator-target constructions using one explicit
composition-order commutation equality. -/
syntax (name := ccComposeSimulators)
  "cc_compose_simulators " term "," term " using " term : tactic

macro_rules
  | `(tactic| cc_compose_simulators $inner, $outer using $commutes) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators
                $inner $outer $commutes
          | fail "cc_compose_simulators expected two typed simulator-target constructions and an explicit composition-order commutation equality")

/-- Compose two construction proofs in ordered parallel. -/
syntax (name := ccParallel) "cc_parallel " term "," term : tactic

macro_rules
  | `(tactic| cc_parallel $left, $right) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel
                $left $right
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel
                $left $right
          | fail "cc_parallel expected two typed constructions for ordered parallel composition")

/-- Extend a construction by a fixed right specification context. -/
syntax (name := ccContextLeft)
  "cc_context_left " term " using " term : tactic

macro_rules
  | `(tactic| cc_context_left $context using $construction) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context
                (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $construction $context
          | fail "cc_context_left expected a typed construction and a fixed right specification context")

/-- Extend a construction by a fixed left specification context. -/
syntax (name := ccContextRight)
  "cc_context_right " term " using " term : tactic

macro_rules
  | `(tactic| cc_context_right $context using $construction) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context" =>
              ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context
                (ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $context $construction
          | fail "cc_context_right expected a typed construction and a fixed left specification context")

open Lean in
/-- Build the proof term underlying `cc_chain` by folding named constructions
from left to right. -/
meta partial def mkCCConstructionChainTerm
    {m : Type → Type} [Monad m] [MonadQuotation m]
    (constructions : TSyntaxArray `term) (kind : Nat) : m Term := do
  if h : 0 < constructions.size then
    let rec go (index : Nat) (accumulator : Term) : m Term := do
      if hindex : index < constructions.size then
        let next := constructions[index]
        let combined ← match kind with
          | 0 =>
              ``(ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial
                  $accumulator $next)
          | 1 =>
              ``(ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation
                  $accumulator $next)
          | _ =>
              ``(ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial
                  $accumulator $next)
        go (index + 1) combined
      else
        pure accumulator
    go 1 constructions[0]
  else
    ``(by fail "cc_chain requires at least two named construction proofs")

/-- Compose an explicit list of at least two named typed constructions. -/
syntax (name := ccChain) "cc_chain" "[" term,* "]" : tactic

macro_rules
  | `(tactic| cc_chain [$constructions:term,*]) => do
      let constructionArray := constructions.getElems
      if constructionArray.size < 2 then
        Lean.Macro.throwError
          "cc_chain requires at least two named construction proofs"
      let exactChain ← mkCCConstructionChainTerm constructionArray 0
      let scalarChain ← mkCCConstructionChainTerm constructionArray 1
      let approximateChain ← mkCCConstructionChainTerm constructionArray 2
      `(tactic|
        first
          | cc_exact_rule "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial" =>
              $exactChain
          | cc_exact_rule "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
              $scalarChain
          | cc_exact_rule "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial" =>
              $approximateChain
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc] using $exactChain)
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $scalarChain)
          | cc_exact_rule
              "ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $approximateChain)
          | fail "cc_chain could not compose the supplied typed construction proofs")

open Lean Elab Tactic in
/-- Check one bounded candidate while restoring the complete tactic state. -/
def ccRuleAppliesWithoutChangingGoal
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

/-- Report the categorical CC rules whose conclusions match the current goal.
The fixed table performs no environment search. -/
elab "cc?" : tactic => withMainContext do
  let exactSingleton ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_iff.mpr)
  let scalarSingleton ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr)
  let scalarGeneral ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr)
  let approximateSingleton ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_singleton_iff.mpr)
  let approximateGeneral ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_iff.mpr)
  let simulator ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.constructs_of_simulator)
  let relaxation ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_serial)
  let filteredExact ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_of_eq)
  let filteredScalar ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.filteredAt_constructs_epsilonRelaxation_of_distance_le)
  let exactSerial ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial)
  let scalarSerial ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_epsilonRelaxation)
  let approximateSerial ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.serial)
  let simulatorSerial ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.serial_simulators)
  let exactParallel ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel)
  let approximateParallel ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel)
  let exactLeftContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.left_context)
  let exactRightContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.right_context)
  let approximateLeftContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.left_context)
  let approximateRightContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.right_context)
  let relaxedLeftContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_left_context)
  let relaxedRightContext ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Specification.Constructs.relax_right_context)
  let distanceTriangle ← `(tactic|
    refine (ConstructiveCryptography.Categorical.ResourceAlgebra.distance_triangle
      _ ?_ _).trans (add_le_add ?_ ?_))
  let attachmentNonexpansion ← `(tactic|
    exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_attach_le _ _ _)
  let parallelLeftNonexpansion ← `(tactic|
    exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_left_le _ _ _)
  let parallelRightNonexpansion ← `(tactic|
    exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_right_le _ _ _)
  let parallelJointNonexpansion ← `(tactic|
    exact ConstructiveCryptography.Categorical.ResourceAlgebra.distance_parallel_le _ _ _ _)
  let tupleCommutation ← `(tactic|
    apply ConstructiveCryptography.Categorical.ResourceAlgebra.Finite.ConverterTuple.converter_partial_commute_of_disjoint)
  let candidates := #[
    ("cc_construct — constructs_singleton_iff", exactSingleton),
    ("cc_construct — constructs_singleton_epsilonRelaxation_iff", scalarSingleton),
    ("cc_construct — constructs_epsilonRelaxation_iff", scalarGeneral),
    ("cc_construct — constructsWithin_singleton_iff", approximateSingleton),
    ("cc_construct — constructsWithin_iff", approximateGeneral),
    ("cc_simulator simulator — constructs_of_simulator", simulator),
    ("cc_relax using inner, outer with compatibility — Constructs.relax_serial", relaxation),
    ("cc_filtered using commutation, membership, equality — filteredAt_constructs_of_eq", filteredExact),
    ("cc_filtered using commutation, membership, distance — filteredAt_constructs_epsilonRelaxation_of_distance_le", filteredScalar),
    ("cc_compose inner, outer — Constructs.serial", exactSerial),
    ("cc_compose inner, outer — Constructs.serial_epsilonRelaxation", scalarSerial),
    ("cc_compose inner, outer — ConstructsWithin.serial", approximateSerial),
    ("cc_compose_simulators inner, outer using commutation — Constructs.serial_simulators", simulatorSerial),
    ("cc_parallel left, right — Constructs.parallel", exactParallel),
    ("cc_parallel left, right — ConstructsWithin.parallel", approximateParallel),
    ("cc_context_left context using construction — Constructs.left_context", exactLeftContext),
    ("cc_context_right context using construction — Constructs.right_context", exactRightContext),
    ("cc_context_left context using construction — ConstructsWithin.left_context", approximateLeftContext),
    ("cc_context_right context using construction — ConstructsWithin.right_context", approximateRightContext),
    ("cc_context_left context using construction — Constructs.relax_left_context", relaxedLeftContext),
    ("cc_context_right context using construction — Constructs.relax_right_context", relaxedRightContext),
    ("cc_triangle via intermediate — distance_triangle", distanceTriangle),
    ("cc_nonexpand — distance_attach_le", attachmentNonexpansion),
    ("cc_nonexpand — distance_parallel_left_le", parallelLeftNonexpansion),
    ("cc_nonexpand — distance_parallel_right_le", parallelRightNonexpansion),
    ("cc_nonexpand — distance_parallel_le", parallelJointNonexpansion),
    ("cc_commute using disjointness — converter_partial_commute_of_disjoint", tupleCommutation)
  ]
  let mut applicable : Array String := #[]
  for (label, candidate) in candidates do
    if ← ccRuleAppliesWithoutChangingGoal candidate then
      applicable := applicable.push label
  if applicable.isEmpty then
    logInfo "No categorical CC rule in the bounded diagnostic table matches this goal."
  else
    logInfo m!"Categorical CC rule candidates (goal unchanged):\n  {
      "\n  ".intercalate applicable.toList}"

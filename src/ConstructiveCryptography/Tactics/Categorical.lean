import ConstructiveCryptography.Tactics.Basic
import ConstructiveCryptography.CryptographicAlgebra.Star
import ConstructiveCryptography.Specification
import ConstructiveCryptography.Specification.Action
import ConstructiveCryptography.Specification.Parallel
import ConstructiveCryptography.Specification.Star.Metric
import ConstructiveCryptography.Specification.Game

/-!
# Constructive Cryptography proof automation

This opt-in module supplies deterministic assembly commands for the typed
`CryptographicAlgebra` presentation.  Every semantic choice remains an explicit
Lean term. Every command targets the typed `CryptographicAlgebra` presentation.

The commands implement the paper-level steps of Maurer--Renner 2016.  Jost's
typed attachment and ordered context laws provide the heterogeneous theorem
heads used here; no symmetry or implicit interface rearrangement is assumed.
-/

namespace ConstructiveCryptography

attribute [cc_normalization]
  CryptographicAlgebra.attach_identity
  CryptographicAlgebra.attach_serial
  CryptographicAlgebra.converter_parallel_identity
  CryptographicAlgebra.converter_parallel_serial
  CryptographicAlgebra.attach_parallel
  CryptographicAlgebra.Specification.parallel_singleton
  CryptographicAlgebra.Specification.star_idem
  CategoryTheory.Category.id_comp
  CategoryTheory.Category.comp_id
  CategoryTheory.Category.assoc
  zero_add
  add_zero
  Set.mem_singleton_iff

end ConstructiveCryptography

/-- Expose the canonical equality, distance, or pointwise obligation for a
singleton or scalar-error construction. -/
syntax (name := ccConstruct) "cc_construct" : tactic

macro_rules
  | `(tactic| cc_construct) =>
      `(tactic|
        first
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr
          | fail "cc_construct expected a typed singleton or scalar-error construction goal")

/-- Close a supported construction goal from one explicit mathematical
witness. -/
syntax (name := ccConstructUsing) "cc_construct" " using " term : tactic

macro_rules
  | `(tactic| cc_construct using $fact) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr $fact
               | exact $fact)
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr $fact
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
              "ConstructiveCryptography.CryptographicAlgebra.Specification.attach_eq_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.attach_eq_of_converter_eq
                $same _
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                $same
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
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
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule "replace converter in exact construction, left-to-right" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in exact construction, right-to-left" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mpr $construction)
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule "replace converter in approximate construction, left-to-right" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in approximate construction, right-to-left" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mpr $construction)
          | fail "cc_transport could not replace the converter in the supplied construction using the supplied equality")

/-- Apply Maurer--Renner's explicit simulator proof step. -/
syntax (name := ccSimulator) "cc_simulator " term : tactic

macro_rules
  | `(tactic| cc_simulator $simulator) =>
      `(tactic|
        first
          | refine ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator
              $simulator ?_ ?_
          | fail "cc_simulator expected a typed singleton construction into the scalar relaxation of a star specification")

/-- Pull an explicitly compatible relaxation through the outer leg of a
serial construction. -/
syntax (name := ccRelax) "cc_relax" " using " term "," term " with " term : tactic

macro_rules
  | `(tactic| cc_relax using $inner, $outer with $compatibility) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_serial
              $compatibility $inner $outer
          | fail "cc_relax could not apply the typed serial relaxation theorem to the supplied constructions and compatibility proof")

/-- Apply the selected fibre-distance triangle inequality through an explicit
intermediate resource. -/
syntax (name := ccTriangle) "cc_triangle" " via " term : tactic

macro_rules
  | `(tactic| cc_triangle via $intermediate) =>
      `(tactic|
        first
          | refine (ConstructiveCryptography.CryptographicAlgebra.distance_triangle
              _ $intermediate _).trans (add_le_add ?_ ?_)
          | fail "cc_triangle expected a typed resource-distance goal with an additive bound")

/-- Select converter-attachment or ordered-parallel non-expansion. -/
syntax (name := ccNonexpand) "cc_nonexpand" : tactic

macro_rules
  | `(tactic| cc_nonexpand) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le _ _ _ _
          | fail "cc_nonexpand expected a converter-attachment or ordered-parallel distance goal")

/-- Compose two constructions in execution order. -/
syntax (name := ccCompose) "cc_compose " term "," term : tactic

macro_rules
  | `(tactic| cc_compose $inner, $outer) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                         $inner $outer))
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                         $inner $outer)))
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
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
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators
                $inner $outer $commutes
          | fail "cc_compose_simulators expected two typed simulator-target constructions and an explicit composition-order commutation equality")

/-- Compose two construction proofs in ordered parallel. -/
syntax (name := ccParallel) "cc_parallel " term "," term : tactic

macro_rules
  | `(tactic| cc_parallel $left, $right) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel
                $left $right
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel
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
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context
                (ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
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
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context
                (ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
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
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                  $accumulator $next)
          | 1 =>
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                  $accumulator $next)
          | _ =>
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
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
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial" =>
              $exactChain
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
              $scalarChain
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial" =>
              $approximateChain
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc] using $exactChain)
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $scalarChain)
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $approximateChain)
          | fail "cc_chain could not compose the supplied typed construction proofs")


open Lean Elab Tactic

/-- Report the categorical CC rules whose conclusions match the current goal.
The fixed table performs no environment search. -/
elab "cc?" : tactic => withMainContext do
  let exactSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr)
  let scalarSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr)
  let scalarGeneral ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr)
  let approximateSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr)
  let approximateGeneral ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr)
  let simulator ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator)
  let relaxation ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_serial)
  let exactSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial)
  let scalarSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation)
  let approximateSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial)
  let simulatorSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators)
  let exactParallel ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel)
  let approximateParallel ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel)
  let exactLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context)
  let exactRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context)
  let approximateLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context)
  let approximateRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context)
  let relaxedLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context)
  let relaxedRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context)
  let distanceTriangle ← `(tactic|
    refine (ConstructiveCryptography.CryptographicAlgebra.distance_triangle
      _ ?_ _).trans (add_le_add ?_ ?_))
  let attachmentNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _)
  let parallelLeftNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _)
  let parallelRightNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _)
  let parallelJointNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le _ _ _ _)
  let candidates := #[
    ("cc_construct — constructs_singleton_iff", exactSingleton),
    ("cc_construct — constructs_singleton_epsilonRelaxation_iff", scalarSingleton),
    ("cc_construct — constructs_epsilonRelaxation_iff", scalarGeneral),
    ("cc_construct — constructsWithin_singleton_iff", approximateSingleton),
    ("cc_construct — constructsWithin_iff", approximateGeneral),
    ("cc_simulator simulator — constructs_of_simulator", simulator),
    ("cc_relax using inner, outer with compatibility — Constructs.relax_serial", relaxation),
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
    ("cc_nonexpand — distance_parallel_le", parallelJointNonexpansion)
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

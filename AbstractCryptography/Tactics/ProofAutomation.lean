/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import AbstractCryptography.Tactics.ProofAutomationAttributes
import AbstractCryptography.Specification.Filtered

/-!
# Abstract Cryptography proof automation

This opt-in module supplies a deterministic paper-normalization layer for the
selected AC surface.  It imports no CC, MPC, random-system, event-algebra,
application, widget, or compatibility module.

`ac_normalization` contains only definitional paper wrappers and oriented
algebraic equations with a documented normal form. `ac_side_condition`
contains facts whose conclusions are recurring explicit AC obligations; local
consumer lemmas may be registered with
`attribute [local ac_side_condition] theoremName`.
-/

namespace AbstractCryptography

attribute [ac_normalization]
  WithinEDistance
  Relaxation.relaxedBy
  Relaxation.epsilonRelaxed
  Relaxation.starRelaxed
  ApproximatelyConstructs
  one_smul
  mul_smul
  one_mul
  mul_one
  zero_add
  add_zero
  Set.smul_set_singleton
  Set.mem_singleton_iff
  compl_compl
  patternAttach_one
  patternAttach_mul
  smul_par

attribute [ac_side_condition]
  disjoint_compl_left
  disjoint_compl_right
  commute_patternAttach_of_disjoint
  commute_patternAttach_supportedOn
  patternAttach_mem_supportedOn

end AbstractCryptography

open Lean.Parser.Tactic

/-- Opt-in trace class for the exact public theorem selected by an AC
composition assembler. -/
initialize Lean.registerTraceClass `AbstractCryptography.ProofAutomation.rule

/-- Internal closing primitive used by the public assemblers.  It elaborates
the supplied proof against the target before emitting a theorem-selection
trace, so failed branches never claim to have selected a rule. -/
syntax (name := acExactRule)
  "ac_exact_rule " str " => " term : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| ac_exact_rule $label:str => $proof) =>
      closeMainGoalUsing `ac_exact_rule fun target _ => do
        let value ← elabTermEnsuringType proof target
        trace[AbstractCryptography.ProofAutomation.rule] "{label.getString}"
        pure value

/-- Normalize an AC goal or selected hypotheses using only the curated
`ac_normalization` registry. -/
syntax (name := acNormalize) "ac_normalize" (location)? : tactic

macro_rules
  | `(tactic| ac_normalize $[at $location]?) =>
      `(tactic| simp -failIfUnchanged only [ac_normalization] $[at $location]?)

/-- Trace every rewrite used by `ac_normalize`, using Lean's simp-rewrite
trace class.  This is diagnostic and intentionally separate from the quiet
default command. -/
syntax (name := acNormalizeTrace) "ac_normalize?" (location)? : tactic

macro_rules
  | `(tactic| ac_normalize? $[at $location]?) =>
      `(tactic|
        set_option trace.Meta.Tactic.simp.rewrite true in
          ac_normalize $[at $location]?)

/-- Close a routine AC goal using, in order, an exact assumption,
definitional equality, or simplification by only the two curated AC
registries plus local hypotheses.  It performs no global simp, search, or
unbounded arithmetic. -/
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

/-- Select the canonical public introduction theorem for an exact singleton,
singleton epsilon-ball, or general epsilon-ball construction goal.  The
corresponding equality, distance, or pointwise witness remains explicit. -/
syntax (name := acConstruct) "ac_construct" : tactic

macro_rules
  | `(tactic| ac_construct) =>
      `(tactic|
        first
          | apply AbstractCryptography.constructs_singleton_iff.mpr
          | apply AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr
          | apply AbstractCryptography.constructs_epsilonRelaxation_iff.mpr
          | fail "ac_construct expected an exact singleton or scalar epsilon-ball construction goal")

/-- Close a supported construction goal from an explicit equality, inclusion,
distance bound, or pointwise metric proof. -/
syntax (name := acConstructUsing) "ac_construct" " using " term : tactic

macro_rules
  | `(tactic| ac_construct using $fact) =>
      `(tactic|
        first
          | (change AbstractCryptography.Constructs _ _ _
             first
               | exact AbstractCryptography.constructs_singleton_iff.mpr $fact
               | exact AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr $fact
               | exact AbstractCryptography.constructs_epsilonRelaxation_iff.mpr $fact
               | exact $fact)
          | fail "ac_construct could not use the supplied equality, inclusion, distance bound, or pointwise proof")

/-- Close a canonical consequence of protocol equality using exactly the
supplied equation.  The bounded candidates are protocol-action congruence and
the exact or scalar-approximate construction congruence lemmas; the command
performs no recursive rewriting or environment search. -/
syntax (name := acTransport) "ac_transport" " using " term : tactic

macro_rules
  | `(tactic| ac_transport using $same) =>
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.smul_congr_protocol" =>
              AbstractCryptography.smul_congr_protocol $same _
          | ac_exact_rule "AbstractCryptography.constructs_congr_protocol" =>
              AbstractCryptography.constructs_congr_protocol $same
          | ac_exact_rule
              "AbstractCryptography.approximately_constructs_congr_protocol" =>
              AbstractCryptography.approximately_constructs_congr_protocol $same
          | fail "ac_transport expected a protocol-action equality or exact/scalar construction equivalence matching the supplied protocol equality")

/-- Replace the protocol in an explicitly supplied construction proof using
exactly one supplied equality.  This is the proof-bearing counterpart of
`ac_transport using same`. -/
syntax (name := acReplaceProtocolInConstruction)
  "ac_transport " term " using " term : tactic

macro_rules
  | `(tactic| ac_transport $construction using $same) =>
      `(tactic|
        first
          | (change AbstractCryptography.Constructs _ _ _
             first
               | ac_exact_rule
                   "replace protocol in supplied construction, left-to-right" =>
                   (by
                     have supplied := $same
                     exact supplied ▸ $construction)
               | ac_exact_rule
                   "replace protocol in supplied construction, right-to-left" =>
                   (by
                     have reversed := Eq.symm $same
                     exact reversed ▸ $construction))
          | fail "ac_transport could not replace the protocol in the supplied construction using the supplied equality")

/-- Apply MauRen16's explicit simulator-to-star construction theorem.  The
simulator is supplied by the caller; membership in the simulator class and the
distance bound remain as the two visible goals. -/
syntax (name := acSimulator) "ac_simulator " term : tactic

macro_rules
  | `(tactic| ac_simulator $simulator) =>
      `(tactic|
        first
          | refine AbstractCryptography.constructs_of_simulator $simulator ?_ ?_
          | fail "ac_simulator expected a singleton construction into an epsilon-ball around an explicit star relaxation")

/-- Pull a compatible relaxation through one explicit construction step.
Both component constructions and the compatibility proof are supplied; no
intermediate specification is inferred by search. -/
syntax (name := acRelax) "ac_relax" " using " term "," term " with " term : tactic

macro_rules
  | `(tactic| ac_relax using $firstConstruction, $secondConstruction with $compatibility) =>
      `(tactic|
        first
          | exact AbstractCryptography.Constructs.relax_trans
              $firstConstruction $secondConstruction $compatibility
          | fail "ac_relax could not apply Constructs.relax_trans to the supplied constructions and compatibility proof")

/-- Close an exact or scalar-metric `filteredAt` construction from explicit
simulator-support evidence and the corresponding equality or distance
bound. -/
syntax (name := acFiltered) "ac_filtered" " using " term "," term : tactic

macro_rules
  | `(tactic| ac_filtered using $support, $fact) =>
      `(tactic|
        first
          | exact AbstractCryptography.filteredAt_constructs_of_eq $support $fact
          | exact AbstractCryptography.filteredAt_constructs_epsilonRelaxation_of_edist_le
              $support $fact
          | fail "ac_filtered expected a filteredAt construction goal, a matching support proof, and an equality or distance bound")

/-- Apply the pseudo-emetric triangle inequality through an explicit
intermediate resource and split an additive target into exactly two distance
legs. -/
syntax (name := acTriangle) "ac_triangle" " via " term : tactic

macro_rules
  | `(tactic| ac_triangle via $intermediate) =>
      `(tactic|
        first
          | refine (edist_triangle _ $intermediate _).trans (add_le_add ?_ ?_)
          | fail "ac_triangle expected an edist/closeness goal with an additive error bound")

/-- Select the named non-expansion theorem for converter action, two-sided
parallel composition, a fixed right context, or a fixed left context. -/
syntax (name := acNonexpand) "ac_nonexpand" : tactic

macro_rules
  | `(tactic| ac_nonexpand) =>
      `(tactic|
        first
          | exact AbstractCryptography.edist_smul_le _ _ _
          | exact AbstractCryptography.edist_par_left_le _ _ _
          | exact AbstractCryptography.edist_par_right_le _ _ _
          | exact AbstractCryptography.edist_par_par_le _ _ _ _
          | fail "ac_nonexpand expected a converter-action or ordered parallel edist non-expansion goal")

/-- Close a canonical restricted-converter commutation goal using only the
curated AC normalization and side-condition registries.  This covers, in
particular, converter restrictions to complementary interface patterns. -/
syntax (name := acCommute) "ac_commute" : tactic

macro_rules
  | `(tactic| ac_commute) =>
      `(tactic|
        first
          | ac_routine
          | fail "ac_commute expected a canonical restricted-converter commutation goal")

/-- Close a restricted-converter commutation goal from explicit disjointness
or supported-converter evidence.  The interface pattern and converters are
read from the goal; the semantically relevant evidence is never searched. -/
syntax (name := acCommuteUsing) "ac_commute" " using " term : tactic

macro_rules
  | `(tactic| ac_commute using $evidence) =>
      `(tactic|
        first
          | exact AbstractCryptography.commute_patternAttach_of_disjoint
              $evidence _ _
          | exact AbstractCryptography.commute_patternAttach_supportedOn
              $evidence _
          | fail "ac_commute could not use the supplied disjointness or supported-converter evidence")

/-- Transfer one defining property test across an explicit distinguisher-class
distance bound.  All semantic choices remain visible: the class, admitted-test
inclusion, ideal property witness, distance bound, and defining test.

**MR11-DEFERRED rule.**  Its leaf, `one_tsub_le_test_of_close`, lives in
`AbstractCryptography.Metric.Distinguisher` — MauRen11 Definition 15/16
provenance — which is behind the provenance fence, and which this MR16-track
automation module therefore does not import.  The rule name is consequently
built with `Lean.mkIdent` and resolved at the **use site**: the tactic fires in
a file that imports `AbstractCryptography.MR11`, and reports its ordinary
failure message in one that does not.  Nothing is deleted; see `LEDGER.md`
PROVENANCE FENCE. -/
syntax (name := acTransferProperty)
  "ac_transfer_property " term " using " term "," term "," term "," term : tactic

macro_rules
  | `(tactic| ac_transfer_property $distinguisherClass using
        $admittedTests, $idealProperty, $distance, $definingTest) => do
      let transferRule :=
        Lean.mkIdent `AbstractCryptography.one_tsub_le_test_of_close
      `(tactic|
        first
          | exact $transferRule
              $distinguisherClass $admittedTests $idealProperty $distance
              $definingTest
          | fail "ac_transfer_property expected a quantitative property-test goal and the matching explicit hypotheses")

/-- Compose two named construction proofs in execution order.  Exact
goals use `Constructs.trans`; scalar-metric goals use
`Constructs.epsilonRelaxation_trans`, so protocol order and error addition remain the
paper's visible conclusion rather than tactic-generated choices. -/
syntax (name := acCompose) "ac_compose " term "," term : tactic

macro_rules
  | `(tactic| ac_compose $firstConstruction, $secondConstruction) =>
      `(tactic|
        first
          | (change AbstractCryptography.Constructs _ _ _
             first
               | ac_exact_rule "AbstractCryptography.Constructs.trans" =>
                   AbstractCryptography.Constructs.trans
                     $firstConstruction $secondConstruction
               | ac_exact_rule "AbstractCryptography.Constructs.epsilonRelaxation_trans" =>
                   AbstractCryptography.Constructs.epsilonRelaxation_trans
                     $firstConstruction $secondConstruction
               | ac_exact_rule
                   "AbstractCryptography.Constructs.trans + AC association normalization" =>
                   (by
                     simpa only [mul_assoc, add_assoc,
                       AbstractCryptography.patternAttach_mul] using
                       (AbstractCryptography.Constructs.trans
                         $firstConstruction $secondConstruction))
               | ac_exact_rule
                   "AbstractCryptography.Constructs.epsilonRelaxation_trans + AC association normalization" =>
                   (by
                     simpa only [mul_assoc, add_assoc,
                       AbstractCryptography.patternAttach_mul] using
                       (AbstractCryptography.Constructs.epsilonRelaxation_trans
                         $firstConstruction $secondConstruction)))
          | fail "ac_compose expected two composable exact or scalar-metric construction proofs")

/-- Compose two simulator-target construction proofs using the
caller's explicit protocol/simulator commutation proof. -/
syntax (name := acComposeSimulators)
  "ac_compose_simulators " term "," term " using " term : tactic

macro_rules
  | `(tactic| ac_compose_simulators $firstConstruction, $secondConstruction
        using $commutation) =>
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.Constructs.simulator_trans" =>
              AbstractCryptography.Constructs.simulator_trans
                $firstConstruction $secondConstruction $commutation
          | fail "ac_compose_simulators expected two simulator-target constructions and matching explicit commutation evidence")

/-- Assemble MauRen11 Definition 7's selected exact parallel construction
rule from two explicit component constructions.  The target must display the
derived serial constructor `(left ∥ 1) * (1 ∥ right)`. -/
syntax (name := acParallel) "ac_parallel " term "," term : tactic

macro_rules
  | `(tactic| ac_parallel $leftConstruction, $rightConstruction) =>
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.red_par" =>
              AbstractCryptography.red_par
                $leftConstruction $rightConstruction
          | fail "ac_parallel expected two exact component constructions and the selected derived parallel constructor")

/-- Extend an exact or scalar-metric construction by a fixed right resource
context.  The context is explicit and the converter extension remains
visible as `protocol ∥ 1`. -/
syntax (name := acContextLeft)
  "ac_context_left " term " using " term : tactic

macro_rules
  | `(tactic| ac_context_left $context using $construction) =>
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.Constructs.par_left_resource" =>
              AbstractCryptography.Constructs.par_left_resource
                $context $construction
          | ac_exact_rule "AbstractCryptography.Constructs.epsilonRelaxation_par_resource" =>
              AbstractCryptography.Constructs.epsilonRelaxation_par_resource
                $construction $context
          | ac_exact_rule "AbstractCryptography.Constructs.par_left" =>
              AbstractCryptography.Constructs.par_left
                $context $construction
          | ac_exact_rule "AbstractCryptography.Constructs.epsilonRelaxation_par" =>
              AbstractCryptography.Constructs.epsilonRelaxation_par
                $construction $context
          | fail "ac_context_left expected an exact or scalar-metric construction and a fixed right context")

/-- Ordered counterpart of `ac_context_left`: extend an exact or
scalar-metric construction by a fixed left resource context, with converter
extension `1 ∥ protocol`. -/
syntax (name := acContextRight)
  "ac_context_right " term " using " term : tactic

macro_rules
  | `(tactic| ac_context_right $context using $construction) =>
      `(tactic|
        first
          | ac_exact_rule "AbstractCryptography.red_one_par" =>
              AbstractCryptography.red_one_par
                $context $construction
          | ac_exact_rule
              "AbstractCryptography.Constructs.relax_par_right + Relaxation.epsilonRelaxation_parCompatible" =>
              AbstractCryptography.Constructs.relax_par_right
                $construction $context
                (AbstractCryptography.Relaxation.epsilonRelaxation_parCompatible _)
          | fail "ac_context_right expected an exact or scalar-metric construction and a fixed left context")

open Lean in
/-- Build the proof term underlying `ac_chain` by folding the named
constructions from left to right. -/
private meta partial def mkACConstructionChainTerm
    {m : Type → Type} [Monad m] [MonadQuotation m]
    (constructions : TSyntaxArray `term) (metric : Bool) : m Term := do
  if h : 0 < constructions.size then
    let rec go (index : Nat) (accumulator : Term) : m Term := do
      if hindex : index < constructions.size then
        let next := constructions[index]
        let combined ← if metric then
          ``(AbstractCryptography.Constructs.epsilonRelaxation_trans $accumulator $next)
        else
          ``(AbstractCryptography.Constructs.trans $accumulator $next)
        go (index + 1) combined
      else
        pure accumulator
    go 1 constructions[0]
  else
    ``(by fail "ac_chain requires at least two named construction proofs")

/-- Compose an explicit list of at least two named exact or scalar-metric
construction proofs.  This is a syntax-level fold, not finite-interface
enumeration or proof search. -/
syntax (name := acChain) "ac_chain" "[" term,* "]" : tactic

macro_rules
  | `(tactic| ac_chain [$constructions:term,*]) => do
      let constructionArray := constructions.getElems
      if constructionArray.size < 2 then
        Lean.Macro.throwError
          "ac_chain requires at least two named construction proofs"
      let exactChain ← mkACConstructionChainTerm constructionArray false
      let metricChain ← mkACConstructionChainTerm constructionArray true
      `(tactic|
        first
          | ac_exact_rule "left fold of AbstractCryptography.Constructs.trans" =>
              $exactChain
          | ac_exact_rule
              "left fold of AbstractCryptography.Constructs.epsilonRelaxation_trans" =>
              $metricChain
          | ac_exact_rule
              "left fold of AbstractCryptography.Constructs.trans + AC association normalization" =>
              (by
                simpa only [mul_assoc, add_assoc,
                  AbstractCryptography.patternAttach_mul] using $exactChain)
          | ac_exact_rule
              "left fold of AbstractCryptography.Constructs.epsilonRelaxation_trans + AC association normalization" =>
              (by
                simpa only [mul_assoc, add_assoc,
                  AbstractCryptography.patternAttach_mul] using $metricChain)
          | fail "ac_chain could not compose the supplied exact or scalar-metric construction proofs")

open Lean Elab Tactic in
/-- Check whether a bounded candidate tactic applies, restoring the complete
tactic state whether it succeeds or fails. -/
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

/-- Report the named AC paper rules whose conclusion matches the current
goal, without changing that goal.  This performs a fixed finite probe of the
public theorem list; it does not search the environment, infer cryptographic
choices, or run any solver. -/
elab "ac?" : tactic => withMainContext do
  let exactSingleton ←
    `(tactic| apply AbstractCryptography.constructs_singleton_iff.mpr)
  let metricSingleton ←
    `(tactic| apply AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr)
  let metricGeneral ←
    `(tactic| apply AbstractCryptography.constructs_epsilonRelaxation_iff.mpr)
  let simulator ←
    `(tactic| apply AbstractCryptography.constructs_of_simulator)
  let relaxation ←
    `(tactic| apply AbstractCryptography.Constructs.relax_trans)
  let filteredExact ←
    `(tactic| apply AbstractCryptography.filteredAt_constructs_of_eq)
  let filteredMetric ←
    `(tactic| apply AbstractCryptography.filteredAt_constructs_epsilonRelaxation_of_edist_le)
  let exactComposition ←
    `(tactic| apply AbstractCryptography.Constructs.trans)
  let metricComposition ←
    `(tactic| apply AbstractCryptography.Constructs.epsilonRelaxation_trans)
  let simulatorComposition ←
    `(tactic| apply AbstractCryptography.Constructs.simulator_trans)
  let parallel ←
    `(tactic| apply AbstractCryptography.red_par)
  let leftContext ←
    `(tactic| apply AbstractCryptography.Constructs.par_left)
  let leftMetricContext ←
    `(tactic| apply AbstractCryptography.Constructs.epsilonRelaxation_par)
  let resourceLeftContext ←
    `(tactic| apply AbstractCryptography.Constructs.par_left_resource)
  let resourceLeftMetricContext ←
    `(tactic| apply AbstractCryptography.Constructs.epsilonRelaxation_par_resource)
  let rightContext ←
    `(tactic| apply AbstractCryptography.red_one_par)
  let rightMetricContext ←
    `(tactic| apply AbstractCryptography.Constructs.relax_par_right)
  let distanceTriangle ←
    `(tactic|
      refine (edist_triangle _ ?_ _).trans (add_le_add ?_ ?_))
  let actionNonexpansion ←
    `(tactic| exact AbstractCryptography.edist_smul_le _ _ _)
  let parallelLeftNonexpansion ←
    `(tactic| exact AbstractCryptography.edist_par_left_le _ _ _)
  let parallelRightNonexpansion ←
    `(tactic| exact AbstractCryptography.edist_par_right_le _ _ _)
  let parallelJointNonexpansion ←
    `(tactic| exact AbstractCryptography.edist_par_par_le _ _ _ _)
  let disjointCommutation ←
    `(tactic| apply AbstractCryptography.commute_patternAttach_of_disjoint)
  let supportedCommutation ←
    `(tactic| apply AbstractCryptography.commute_patternAttach_supportedOn)
  -- MR11-DEFERRED leaf, resolved at the use site; see `acTransferProperty`.
  let propertyTransfer ←
    `(tactic| apply $(mkIdent `AbstractCryptography.one_tsub_le_test_of_close))
  let candidates := #[
    ("ac_construct — constructs_singleton_iff", exactSingleton),
    ("ac_construct — constructs_singleton_epsilonRelaxation_iff", metricSingleton),
    ("ac_construct — constructs_epsilonRelaxation_iff", metricGeneral),
    ("ac_simulator simulator — constructs_of_simulator", simulator),
    ("ac_relax using first, second with compatibility — Constructs.relax_trans",
      relaxation),
    ("ac_filtered using support, equality — filteredAt_constructs_of_eq",
      filteredExact),
    ("ac_filtered using support, distance — filteredAt_constructs_epsilonRelaxation_of_edist_le",
      filteredMetric),
    ("ac_compose first, second — Constructs.trans", exactComposition),
    ("ac_compose first, second — Constructs.epsilonRelaxation_trans", metricComposition),
    ("ac_compose_simulators first, second using commutation — Constructs.simulator_trans",
      simulatorComposition),
    ("ac_parallel left, right — red_par", parallel),
    ("ac_context_left context using construction — Constructs.par_left",
      leftContext),
    ("ac_context_left context using construction — Constructs.epsilonRelaxation_par",
      leftMetricContext),
    ("ac_context_left resource using construction — Constructs.par_left_resource",
      resourceLeftContext),
    ("ac_context_left resource using construction — Constructs.epsilonRelaxation_par_resource",
      resourceLeftMetricContext),
    ("ac_context_right context using construction — red_one_par", rightContext),
    ("ac_context_right context using construction — Constructs.relax_par_right",
      rightMetricContext),
    ("ac_triangle via intermediate — edist_triangle + add_le_add",
      distanceTriangle),
    ("ac_nonexpand — edist_smul_le", actionNonexpansion),
    ("ac_nonexpand — edist_par_left_le", parallelLeftNonexpansion),
    ("ac_nonexpand — edist_par_right_le", parallelRightNonexpansion),
    ("ac_nonexpand — edist_par_par_le", parallelJointNonexpansion),
    ("ac_commute using disjointness — commute_patternAttach_of_disjoint",
      disjointCommutation),
    ("ac_commute using support — commute_patternAttach_supportedOn",
      supportedCommutation),
    ("ac_transfer_property D using admitted, ideal, close, test — one_tsub_le_test_of_close",
      propertyTransfer)
  ]
  let mut applicable : Array String := #[]
  for (label, candidate) in candidates do
    if ← acRuleAppliesWithoutChangingGoal candidate then
      applicable := applicable.push label
  if applicable.isEmpty then
    logInfo "No canonical AC paper rule in the bounded diagnostic table matches this goal."
  else
    logInfo m!"Canonical AC rule candidates (goal unchanged):\n  {
      "\n  ".intercalate applicable.toList}"

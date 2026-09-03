/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.Simp
import RandomSystems.Converter.RandomSystemAction
import RandomSystems.Game.Filter
import RandomSystems.Tactics.ProofAutomationAttributes
import RandomSystems.Technique.ConditionalEquivalence.Advantage
import RandomSystems.Uniform

/-!
# Random Systems proof automation

This opt-in implementation uses finite, inspectable simp registries.  It
normalizes standard constructors and discharges their probability-law and
common-domain closure obligations.  It never selects a system, domain,
conditional-equivalence witness, game condition, or probability bound.
-/

namespace RandomSystems

attribute [rs_normalization]
  System.filterQueries_eq_filterDom
  PDS.filterQueries_eq_filterDom
  PDG.underlying_filterDom

attribute [rs_side_condition]
  Probability.Distribution.uniform_isProbDist
  Probability.Distribution.fTransform_isProbDist
  PDS.isProbDist_urf
  PDS.isProbDist_urp
  PDS.isProbDist_unif
  PDS.isProbDist_finiteBeacon
  PDS.hasDomain_fTransform_functionEvaluator
  PDS.hasDomain_urf
  PDS.hasDomain_urp
  PDS.hasDomain_unif
  PDS.hasDomain_finiteBeacon
  PDS.isProbDist_filterDom
  PDS.hasDomain_filterDom
  PDG.isProbDist_underlying
  PDG.hasDomain_underlying
  PDG.isProbDist_filterDom
  PDG.hasDomain_filterDom

end RandomSystems

open Lean.Parser.Tactic

/-- Normalize distributions, filters, and game-underlying projections using
only the two curated shrinking registries. -/
syntax (name := rsNormalize) "rs_normalize" (location)? : tactic

macro_rules
  | `(tactic| rs_normalize $[at $location]?) =>
      `(tactic| simp -failIfUnchanged only [dist_simp, rs_normalization]
        $[at $location]?)

/-- Trace every rewrite used by `rs_normalize`. -/
syntax (name := rsNormalizeTrace) "rs_normalize?" (location)? : tactic

macro_rules
  | `(tactic| rs_normalize? $[at $location]?) =>
      `(tactic|
        set_option trace.Meta.Tactic.simp.rewrite true in
          rs_normalize $[at $location]?)

/-- Close a structural Random Systems obligation without lowering converter
attachment to its `PDS.apply` implementation. -/
syntax (name := rsRoutine) "rs_routine" : tactic

/-- Close a routine structural consequence of the supplied equality. -/
syntax (name := rsRoutineUsing) "rs_routine" "using" term : tactic

macro_rules
  | `(tactic| rs_routine) =>
      `(tactic|
        first
          | (solve
              | assumption
              | rfl
              | simp_all only [dist_simp, rs_side_condition,
                  ← RandomSystems.Ambient.DDC.comp_smul,
                  CategoryTheory.Category.assoc])
          | fail "rs_routine could not close the goal with assumptions or the curated Random Systems registries")

  | `(tactic| rs_routine using $fact) =>
      `(tactic|
        first
          | exact $fact
          | (simp only [RandomSystems.Ambient.DDC.hom_smul_randomFunction_eq]
             rw [← RandomSystems.Ambient.DDC.comp_smul, ← $fact])
          | fail "rs_routine could not derive the goal from the supplied fact using Random Systems action laws")

/-- Apply the conditional-equivalence advantage bound with an explicit common
domain, conditional-equivalence proof, and blind winning bound.  Only the
probability-law and common-domain side conditions are discharged
automatically. -/
syntax (name := rsConditionalEquivalence)
  "rs_conditional_equivalence " term " using " term ", " term : tactic

macro_rules
  | `(tactic| rs_conditional_equivalence $domain using $equivalent, $winning) =>
      `(tactic|
        refine
          RandomSystems.PDS.advantage_le_of_conditionallyEquivalent_of_supWinProb_blind_le
            _ _ $domain ?_ ?_ ?_ ?_ $equivalent _ $winning <;>
          rs_routine)

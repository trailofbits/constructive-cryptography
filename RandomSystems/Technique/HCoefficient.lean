/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Probability.StatisticalDistance
import RandomSystems.TranscriptFactor

set_option autoImplicit false

/-!
# H-coefficient bounds for deterministic environments

`Probability.StatisticalDistance` owns the system-independent H-coefficient
kernel on finitely supported distributions. In particular,
`Probability.hTechnique_partition_finiteSupport` allows an arbitrary sample
carrier and a finite family of ratio-defect cells.

`RandomSystems.TranscriptFactor` separately owns the exact factorization of a
transcript law into its system and environment factors. This module combines
those two generic results: it applies the distribution-level partition bound
to transcript laws, cancels the common environment factor, and then takes the
supremum over compatible stopping deterministic environments. The resulting
theorems bound fixed-interface Random Systems advantage; no converter or
Constructive Cryptography layer is involved.
-/

noncomputable section

open scoped NNReal BigOperators

namespace RandomSystems

open Probability
open Classical

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-- Cell-wise transcript bound for partial compatible and stopping DDE
observation.  The ratio premise mentions only the system factor; the common
environment factor cancels. -/
theorem trLaw_partition_finiteSupport_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : PDS X Y) (environment : System.DDE Y X)
    (cell : Option (System.Transcript X Y) → ι) (eps : ι → NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (hSc : Compatible environment S) (hSs : Stops environment S)
    (hTc : Compatible environment T) (hTs : Stops environment T)
    (h_ratio : ∀ transcript,
      (1 - eps (cell (some transcript))) *
          transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript) :
    statDist (trLaw environment S) (trLaw environment T) ≤
      ∑ i, (eps i : ℝ) *
        (trLaw environment T).mass (fun observed => cell observed = i) := by
  -- Apply the finite-support partition inequality to the two transcript laws.
  apply Probability.hTechnique_partition_finiteSupport
  · unfold trLaw
    exact hS.fTransform _
  · unfold trLaw
    exact hT.fTransform _
  · simp only [trLaw, Distribution.weight_fTransform, hw]
  · intro observed
    cases observed with
    -- Stopping removes the undefined-transcript cell from both laws.
    | none =>
        rw [trLaw_none_eq_zero environment S hSs,
          trLaw_none_eq_zero environment T hTs]
        simp
    -- A concrete transcript shares one nonnegative environment factor.
    | some transcript =>
        rw [trLaw_some_factorization environment S hSc,
          trLaw_some_factorization environment T hTc]
        -- Reassociate that common factor, then apply the system-only ratio.
        calc
          (1 - (eps (cell (some transcript)) : ℝ)) *
              (transcriptEnvironmentFactorPartial environment transcript *
                transcriptSystemFactor T transcript) =
              transcriptEnvironmentFactorPartial environment transcript *
                ((1 - (eps (cell (some transcript)) : ℝ)) *
                  transcriptSystemFactor T transcript) := by ring
          _ ≤ transcriptEnvironmentFactorPartial environment transcript *
                transcriptSystemFactor S transcript :=
            mul_le_mul_of_nonneg_left (h_ratio transcript)
              (transcriptEnvironmentFactorPartial_nonneg environment transcript)

/-- A finite partition of transcript observations bounds the pair-specific
auxiliary advantage. Each cell contributes its ratio defect multiplied by a
uniform upper bound on that cell's ideal transcript mass. -/
theorem advantage_le_weighted_cells
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S T : PDS X Y)
    (cell : Option (System.Transcript X Y) → ι)
    (eps delta : ι → NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (h_ratio : ∀ transcript,
      (1 - eps (cell (some transcript))) *
          transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript)
    (h_cells : ∀ environment : {e : System.DDE Y X //
        (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)},
      ∀ i, (trLaw environment.1 T).mass
        (fun observed => cell observed = i) ≤ delta i) :
    advantage S T ≤ ∑ i, (eps i : ℝ) * (delta i : ℝ) := by
  unfold advantage
  -- It suffices to prove the weighted bound for each admissible DDE.
  refine Real.sSup_le ?_ (Finset.sum_nonneg fun i _ =>
    mul_nonneg (eps i).coe_nonneg (delta i).coe_nonneg)
  rintro value ⟨environment, _, rfl⟩
  calc
    -- The transcript factorization supplies the cellwise partition bound.
    statDist (trLaw environment.1 S) (trLaw environment.1 T) ≤
        ∑ i, (eps i : ℝ) *
          (trLaw environment.1 T).mass (fun observed => cell observed = i) :=
      trLaw_partition_finiteSupport_le S T environment.1 cell eps hS hT hw
        environment.2.1.1 environment.2.1.2
        environment.2.2.1 environment.2.2.2 h_ratio
    -- Replace every ideal cell mass by its uniform upper bound.
    _ ≤ ∑ i, (eps i : ℝ) * (delta i : ℝ) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (h_cells environment i) (eps i).coe_nonneg

/-- A uniform transcript-system-factor ratio bounds distinguishing advantage.
This is the one-cell specialization of `advantage_le_weighted_cells`; normalization
of the ideal PDS makes the cell mass at most one. -/
theorem advantage_le_of_ratio
    (S T : PDS X Y) (eps : NNReal)
    (hS : S.NonNeg) (hT : T.NonNeg)
    (hw : S.weight = T.weight) (hTWeight : T.weight = 1)
    (h_ratio : ∀ transcript,
      (1 - (eps : ℝ)) * transcriptSystemFactor T transcript ≤
        transcriptSystemFactor S transcript) :
    advantage S T ≤ (eps : ℝ) := by
  have bound := advantage_le_weighted_cells S T
    (fun _ => Unit.unit)
    (fun _ => eps) (fun _ => 1) hS hT hw
    (fun transcript => by simpa using h_ratio transcript)
    (fun environment cell => by
      cases cell
      have nonnegative : (trLaw environment.1 T).NonNeg := by
        unfold trLaw
        exact hT.fTransform _
      calc
        (trLaw environment.1 T).mass
            (fun observed => (fun _ => Unit.unit) observed = Unit.unit) ≤
          (trLaw environment.1 T).weight :=
            Distribution.mass_le_weight nonnegative _
        _ = T.weight := by
          unfold trLaw
          exact Distribution.weight_fTransform _ _
        _ = 1 := hTWeight)
  simpa using bound

end PDS

end RandomSystems

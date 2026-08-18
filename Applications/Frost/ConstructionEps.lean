/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Frost.Construction
import ConstructiveCryptography.Multiparty.GameMetric

/-!
# FROST end-to-end at a distinguisher-class error

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

Split out of `Applications.Frost.Construction` on 2026-08-17: it was that
file's only declaration taking an `AbstractCryptography.DistinguisherClass`
parameter.  The exact two-rung ladder, the threshold instance and the
`∗Z`-calculus stay on the MR16 track in `Applications.Frost.Construction`.
-/

namespace AbstractCryptography

open Pointwise
open scoped ENNReal

/-- **The real (ε-relaxed) FROST theorem** (the L4 fix): the two stages'
simulators are only `edist ≤ ε`-close (statistical / computational), not exact,
so the construction lands in the `ε`-ball of the `∗Z`-relaxed ideal and the
errors accumulate.  For every tolerated `Z`: (1) the composed protocol
constructs the gated TSS from `[NET, BC, RO]` within `εd + εs` (the two
simulator distances), and (2) the real constructed system meets the per-`Z`
unforgeability bound `εg + (εd + εs)` — the ideal's game bound `εg` plus the
simulation slack, via the distinguisher-class metric (`gameSpec_of_edistD_le`).
Equality leaves for `frost_end_to_end` imply the zero-error simulator premises
here, and then the game bound reduces to `εg`. On a pseudo-emetric carrier the
construction still lands in the zero-distance closure of the exact target;
recovering the exact packaged `ConstructsForAdversaryStructure` conclusion
also requires zero-distance separation (or quotienting) and the corresponding
adversary-structure packaging.

The metric is any `PseudoEMetricSpace Φ` dominating the class distance
(`hDedist`); in the carrier it *is* the class distance (`edist = edistD`, the
distinguisher-class metric ported in `AbstractCryptography/Metric/Distinguisher.lean`), so
`hDedist` holds with equality. -/
theorem frost_end_to_end_eps {I : Type*} {Γ : I → Type*} {Φ : Type*}
    [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ] [PseudoEMetricSpace Φ]
    [IsNonexpandingSMul (∀ i, Γ i) Φ]
    (𝒵 : AdversaryStructure I) (πdkg πsign : ∀ i, Γ i)
    (NETspec : Set I → Set Φ) (KEYS TSS : Φ)
    (D : DistinguisherClass (∀ i, Γ i) Φ)
    (hDedist : ∀ q q' : Φ, D.edistD q q' ≤ edist q q')
    (Ts : Set I → Set (Φ → ℝ≥0∞)) (εd εs εg : ℝ≥0∞)
    (hTs : ∀ Z, Ts Z ⊆ D.tests)
    (hdkg : ∀ Z ∈ 𝒵.sets, ∀ R ∈ NETspec Z, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      edist (patternAttach Zᶜ πdkg • R) (s • KEYS) ≤ εd)
    (hsign : ∀ Z ∈ 𝒵.sets, ∀ R ∈ zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS},
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      edist (patternAttach Zᶜ πsign • R) (s • TSS) ≤ εs)
    (hcl : ∀ Z ∈ 𝒵.sets, ZClosed (Sigma := ∀ j, Γ j) tupleGamma Z (Ts Z))
    (hunforg : ∀ Z ∈ 𝒵.sets, TSS ∈ gameSpec (Ts Z) εg) :
    ∀ Z ∈ 𝒵.sets, ∀ R ∈ NETspec Z,
      patternAttach Zᶜ (πsign * πdkg) • R ∈
        Relaxation.epsilonRelaxation (εd + εs) (zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS})
      ∧ patternAttach Zᶜ (πsign * πdkg) • R ∈ gameSpec (Ts Z) (εg + (εd + εs)) := by
  intro Z hZ R hR
  have h2 : zStar (Sigma := ∀ j, Γ j) tupleGamma Z (NETspec Z) —[patternAttach Zᶜ πdkg]→
      Relaxation.epsilonRelaxation εd (zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS}) :=
    constructs_zStar_eps_of_leaf πdkg (hdkg Z hZ)
  have h1 : zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS} —[patternAttach Zᶜ πsign]→
      Relaxation.epsilonRelaxation εs (zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS}) := by
    have h := constructs_zStar_eps_of_leaf πsign (hsign Z hZ)
    rwa [zStar_idem tupleGamma Z {KEYS}] at h
  have hcomp := Constructs.epsilonRelaxation_trans h2 h1
  rw [← patternAttach_mul] at hcomp
  have hmem := hcomp (Set.smul_mem_smul_set
    ((zStar (Sigma := ∀ j, Γ j) tupleGamma Z).le_toFun (NETspec Z) hR))
  refine ⟨hmem, ?_⟩
  obtain ⟨w, hw, hdw⟩ := Relaxation.mem_epsilonRelaxation_iff.mp hmem
  have hwg : w ∈ gameSpec (Ts Z) εg :=
    zStar_subset_gameSpec tupleGamma (hcl Z hZ) (hunforg Z hZ) hw
  exact gameSpec_of_edistD_le D (hTs Z) hwg (le_trans (hDedist _ _) hdw)
end AbstractCryptography

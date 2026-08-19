/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography.Multiparty.Basic
import AbstractCryptography.Metric.Distinguisher

/-!
# Game bounds against a distinguisher-class distance

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

Split out of `ConstructiveCryptography.Multiparty.Basic` on 2026-08-17: it was
that file's only declaration indexed by an
`AbstractCryptography.DistinguisherClass`, which carries MauRen11 Definition
15/16 provenance.  The `∗Z`-calculus, the game specification itself, the
dishonest closure, the gate hierarchy and the adversary structures are
LiuMau20 §2.4/§2.5 and stay on the MR16 track.
-/

namespace AbstractCryptography

section GameMetric
open scoped ENNReal
variable {Sigma Φ : Type*} [SMul Sigma Φ]

/-- A resource within class-distance `εs` of one that meets the game bound
`εg` meets it up to `εg + εs`: the forger's advantage on the real system is
its advantage on the ideal plus the simulation distance. -/
theorem gameSpec_of_edistD_le (D : DistinguisherClass Sigma Φ)
    {Ts : Set (Φ → ℝ≥0∞)} (hTs : Ts ⊆ D.tests) {q q' : Φ}
    {εg εs : ℝ≥0∞} (hq' : q' ∈ gameSpec Ts εg) (hd : D.edistD q q' ≤ εs) :
    q ∈ gameSpec Ts (εg + εs) := by
  intro t ht
  have hadv : t q - t q' ≤ εs :=
    D.test_left_tsub_right_le_of_edistD_le (hTs ht) hd
  calc t q ≤ (t q - t q') + t q' := le_tsub_add
    _ ≤ εs + εg := add_le_add hadv (hq' t ht)
    _ = εg + εs := add_comm ..

end GameMetric

end AbstractCryptography

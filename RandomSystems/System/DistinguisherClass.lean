/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ProbabilisticSystem
import AbstractCryptography.Metric.Distinguisher

/-!
# The resource carrier as a distinguisher class

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

Split out of `RandomSystems.System.ProbabilisticSystem` on 2026-08-17.
`AbstractCryptography.DistinguisherClass` is MauRen11 Definition 15/16
provenance, and this instantiation was the *sole* reason the whole
`RandomSystems` tree imported `AbstractCryptography.Metric.Simulation`, and
through it the MauRen11 metric.  The construction itself is unchanged: the
admitted tests are CR18 Definition 3.8's systems into the one-shot Boolean
signature, and Definition 16's emulation closure is `exists_absorb_smul`,
which stays where it is proved.

The MR16-track distance on the same carrier is `PDS.maxEDist` (MauRen16
fn. 9), and it needs none of this.
-/

namespace RandomSystems

open scoped ENNReal

universe u v

namespace PDS.Resource

variable {X : Type u} {Y : Type v}

/-- **Jost Definition 2.2.8 on the resource carrier.**  The admitted
distinguishers are CR18 Definition 3.8's systems into the one-shot Boolean
signature, and closure under protocol emulation is `exists_absorb_smul`. -/
noncomputable def distinguishers : AbstractCryptography.DistinguisherClass
    (Protocol X Y) (Resource X Y) where
  tests := Set.range fun d : Distinguisher X Y =>
    fun S : Resource X Y => ENNReal.ofReal (outputOne d S.1)
  test_le_one := by
    rintro _ ⟨d, rfl⟩ S
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal
      ((outputOne_le_weight S.2.nonNeg d).trans S.2.weight_le_one)
  test_attach := by
    rintro w _ ⟨d, rfl⟩
    obtain ⟨d', hd'⟩ := exists_absorb_smul w d
    exact ⟨d', funext fun S => by
      show ENNReal.ofReal (outputOne d' S.1) = ENNReal.ofReal (outputOne d (w • S).1)
      rw [coe_smul, hd' S.1]⟩

end PDS.Resource

end RandomSystems

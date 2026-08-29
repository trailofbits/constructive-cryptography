/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.RandomSystem
import Probability.StatisticalDistance
import Mathlib.Data.ENNReal.BigOperators

/-!
# Fixed-interface random-system distance

Lanzenberger, Definition 2.26 (printed p. 18), defines distinguishing
advantage for random systems with one common domain.  `CommonDomain.Presentation.Adv`
makes that common domain part of the type.  The broader `PDS.advantage` is an
auxiliary supremum whose observation family is determined separately by each
pair of laws.
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-- The pair-specific distinguishing advantage over DDEs compatible with, and
stopping on, both laws.  This broader auxiliary is useful before a common
domain has been fixed; it is not Lanzenberger's literal Definition 2.26. -/
def advantage (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ e : {e : System.DDE Y X //
      (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)},
    ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 T))

@[simp]
theorem advantage_self (S : PDS X Y) : advantage S S = 0 :=
  le_antisymm
    (iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

/-- The advantage over DDEs compatible with one named domain and halting on
every answer history. This global halting condition is stronger than the
pair-specific `Stops` condition used by `PDS.advantage`; both are Lean
extensions beyond the thesis's standing finite-system setting. This is an
auxiliary observation family rather than Definition 2.26. -/
def advantageOnDomain (D : Set (List X)) (S T : PDS X Y) : ℝ≥0∞ :=
  ⨆ e : {e : System.DDE Y X // System.CompatibleD e D ∧ System.DDE.Halts e},
    ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 T))

@[simp]
theorem advantageOnDomain_self (D : Set (List X)) (S : PDS X Y) : advantageOnDomain D S S = 0 :=
  le_antisymm
    (iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

/-- Triangle inequality for advantage over one fixed-domain observation
family.  The three terms use the same compatible, halting environments, so
the distribution-level statistical-distance triangle inequality applies at
each environment before taking the supremum. -/
theorem advantageOnDomain_triangle (D : Set (List X)) (S T U : PDS X Y) :
    advantageOnDomain D S U ≤ advantageOnDomain D S T + advantageOnDomain D T U := by
  refine iSup_le fun e => ?_
  calc
    ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 U)) ≤
        ENNReal.ofReal (statDist (trLaw e.1 S) (trLaw e.1 T)) +
          ENNReal.ofReal (statDist (trLaw e.1 T) (trLaw e.1 U)) := by
      rw [← ENNReal.ofReal_add (Probability.statDist_nonneg _ _)
        (Probability.statDist_nonneg _ _)]
      exact ENNReal.ofReal_le_ofReal
        (Probability.statDist_triangle _ _ _)
    _ ≤ advantageOnDomain D S T + advantageOnDomain D T U :=
      add_le_add (le_iSup_of_le e le_rfl) (le_iSup_of_le e le_rfl)

/-- The globally halting fixed-domain observation family is included in the
pair-specific auxiliary family when both laws present `D`. -/
theorem advantageOnDomain_le_advantage {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) : advantageOnDomain D S T ≤ advantage S T :=
  iSup_le fun e =>
    le_iSup_of_le
      ⟨e.1, ⟨compatible_of_compatibleD e.2.1 hS, stops_of_halts e.2.2 S⟩,
        ⟨compatible_of_compatibleD e.2.1 hT, stops_of_halts e.2.2 T⟩⟩ le_rfl

end PDS

namespace CommonDomain.Presentation

/-- Lanzenberger, Definition 2.26 (printed p. 18): “For two random
`(X,Y)`-systems `S` and `T` with the same domain,” the distinguishing
advantage is the supremum over DDEs compatible with both systems.  The common
domain is enforced by placing both presentations in the same fibre. Lean does
not bundle the thesis's standing finite-system assumption, so the underlying
formula records stopping explicitly on the broader carrier. -/
def Adv {D : Set (List X)}
    (S T : {P : CommonDomain.Presentation X Y // P.domain = D}) : ℝ≥0∞ :=
  PDS.advantage S.1.law T.1.law

/-- Lanzenberger's notation `Adv(S,T)` for two presentations in one
common-domain fibre. -/
scoped notation "Adv(" S ", " T ")" => Adv S T

@[simp]
theorem Adv_self {D : Set (List X)}
    (S : {P : CommonDomain.Presentation X Y // P.domain = D}) : Adv S S = 0 :=
  PDS.advantage_self S.1.law

end CommonDomain.Presentation

end


end RandomSystems

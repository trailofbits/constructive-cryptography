module

public import ConstructiveCryptography.Specification.Metric.Separation

/-!
# Separating a two-ideal specification

The real output is `none`. The target permits `some false` or `some true`. Each equality
test recognizes one of these outputs. Restoring `none` to the target permits construction.
-/

@[expose] public section

namespace Tests.MetricSeparation

open ConstructiveCryptography Specification

/-- Distinct outputs can be distinguished perfectly. -/
local instance : EDist (Option Bool) where
  edist r i := if r = i then 0 else 1

/-- Observer `b` tests equality with `some b`; its gap is one when the decisions differ. -/
noncomputable def gap (b : Bool) (r i : Option Bool) : ENNReal :=
  if r = some b ↔ i = some b then 0 else 1

/-- The construction may incur half a unit of distinguishing error. -/
noncomputable def tolerance : ENNReal := 1 / 2

/-- Equality tests have gap at most the discrete resource distance. -/
lemma gap_le (b : Bool) (r i : Option Bool) : gap b r i ≤ edist r i := by
  change gap b r i ≤ if r = i then 0 else 1
  by_cases equal : r = i
  · subst i
    simp only [gap, iff_self, ite_true, le_refl]
  · simp only [equal, ite_false]
    unfold gap
    split <;> norm_num

/-- Against each permitted ideal, choose the test for its tag. -/
example : Construction.Unconstructible
    (fun (_ : Unit) s t => ConstructsWithin (fun _ : Unit => (none : Option Bool)) s t tolerance)
    Set.univ Set.univ (Set.range some) := by
  apply unconstructible_of_test_gap _ _ _ _ _ Set.univ gap (fun d _ => gap_le d)
  intro _ _
  refine ⟨(), Set.mem_univ _, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact ⟨b, Set.mem_univ _, by norm_num [gap, tolerance]⟩

/-- No single test separates both ideals: the other tag and `none` both fail its test. -/
example : ¬ ∃ b, ∀ i ∈ Set.range some, tolerance < gap b none i := by
  rintro ⟨b, separates⟩
  have other := separates (some (!b)) ⟨!b, rfl⟩
  cases b <;> norm_num [gap, tolerance] at other

/-- The test for `some false` still separates that ideal; `none` witnesses construction. -/
example : tolerance < gap false none (some false) ∧
    ConstructsWithin (fun _ : Unit => (none : Option Bool)) Set.univ {none, some false}
      tolerance := by
  refine ⟨by norm_num [gap, tolerance], fun _ _ => ⟨none, by simp, ?_⟩⟩
  change (if (none : Option Bool) = none then (0 : ENNReal) else 1) ≤ tolerance
  simp only [ite_true, zero_le]

end Tests.MetricSeparation

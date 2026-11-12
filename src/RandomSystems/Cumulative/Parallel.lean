module

public import RandomSystems.Cumulative.CumulativeOperations
public import RandomSystems.Cumulative.FiniteCuts

/-!
# Independent parallel composition through total observation cuts

`cutDomain_parallel_cutDomain` identifies the domain after a total horizon is imposed.
`cutMass_parallelMass` retains that total cut when cutting both components.
`parallelMass_isRandomSystem` then glues the existing bounded parallel systems; the bounded
operation is identified by `RandomSystem.parallel_eq_parallelMass`.
-/

@[expose] public section

namespace SystemAlgebra

open RandomSystem

-- `D`, `E` admit queries at the two component histories; `p`, `r` are their cumulative masses.
variable {A B C F : Type}

/-- At a total horizon, the component bounds in the bounded parallel domain are redundant. -/
lemma cutDomain_parallel_cutDomain
    (D : List (A × B) → A → Prop) (E : List (C × F) → C → Prop) (q : ℕ) :
    cutDomain ((cutDomain D q).parallel (cutDomain E q)) q =
      cutDomain (fun h x => parallelConsistent h ∧ parallelAdmits D E h x) q := by
  unfold cutDomain
  congr 1
  funext h x
  apply propext
  by_cases hc : parallelConsistent h
  · have lengths := length_of_parallelConsistent hc
    rcases x with ⟨_ | ⟨⟩, x⟩ <;>
      simp only [Domain.parallel, hc, true_and, parallelAdmits]
    · constructor
      · rintro ⟨⟨_, hd, _⟩, hq⟩
        exact ⟨hd, hq⟩
      · rintro ⟨hd, hq⟩
        exact ⟨⟨by omega, hd, by omega⟩, hq⟩
    · constructor
      · rintro ⟨⟨_, he, _⟩, hq⟩
        exact ⟨he, hq⟩
      · rintro ⟨he, hq⟩
        exact ⟨⟨by omega, he, by omega⟩, hq⟩
  · simp only [Domain.parallel, hc, false_and]

/-- Cutting each component preserves parallel masses after the same total cut. -/
lemma cutMass_parallelMass (p : List (A × B) → ℝ) (r : List (C × F) → ℝ) (q : ℕ) :
    cutMass (parallelMass p r) q =
      cutMass (parallelMass (cutMass p q) (cutMass r q)) q := by
  funext h
  by_cases hq : h.length ≤ q
  · rw [cutMass, cutMass, ite_eq_left hq, ite_eq_left hq]
    by_cases hc : parallelConsistent h
    · have lengths := length_of_parallelConsistent hc
      simp only [parallelMass, ite_eq_left hc, cutMass,
        ite_eq_left (by omega : (parallelLeft h).length ≤ q),
        ite_eq_left (by omega : (parallelRight h).length ≤ q)]
    · simp only [parallelMass, ite_eq_right hc]
  · simp only [cutMass, ite_eq_right hq]

/-- The bounded parallel operation has the same independent cumulative formula. -/
lemma RandomSystem.parallel_eq_parallelMass [Fintype A] [Fintype B] [Fintype C] [Fintype F]
    {D : Domain A B} {E : Domain C F} (R : RandomSystem A B D) (S : RandomSystem C F E) :
    (RandomSystem.parallel R S : List ((Two A C) × (Two B F)) → ℝ) = parallelMass R S := rfl

/-- Independent normalized behaviors normalize on their consistent parallel query domain. -/
theorem parallelMass_isRandomSystem
    -- `A`, `B` are finite left query/reply types; `C`, `F` are the right types.
    [_root_.Finite A] [_root_.Finite B] [_root_.Finite C] [_root_.Finite F]
    {D : List (A × B) → A → Prop} {E : List (C × F) → C → Prop}
    {p : List (A × B) → ℝ} {r : List (C × F) → ℝ}
    -- `hp`, `hr` normalize the component masses on their respective domains `D`, `E`.
    (hp : IsRandomSystem D p) (hr : IsRandomSystem E r) :
    IsRandomSystem (fun h x => parallelConsistent h ∧ parallelAdmits D E h x)
      (parallelMass p r) := by
  let := Fintype.ofFinite A
  let := Fintype.ofFinite B
  let := Fintype.ofFinite C
  let := Fintype.ofFinite F
  let domain := fun h x => parallelConsistent h ∧ parallelAdmits D E h x
  -- The total cut of bounded parallel supplies each finite normalization certificate.
  have bounded (q : ℕ) : IsRandomSystem (cutDomain domain q) (cutMass (parallelMass p r) q) := by
    let T := RandomSystem.parallel (IsRandomSystem.cut D p hp q) (IsRandomSystem.cut E r hr q)
    have cut := IsRandomSystem.cutMass _ T T.2 q
    rw [cutDomain_parallel_cutDomain] at cut
    change IsRandomSystem (cutDomain domain q)
      (cutMass (parallelMass (cutMass p q) (cutMass r q)) q) at cut
    rw [← cutMass_parallelMass] at cut
    exact cut
  let R (q : ℕ) : RandomSystem (Two A C) (Two B F) (cutDomain domain q) :=
    ⟨cutMass (parallelMass p r) q, bounded q⟩
  -- These are total cuts of one mass function, so earlier transcript masses stabilize.
  have coherent (q : ℕ) (h) (hh : h.length ≤ q) : R (q + 1) h = R q h := by
    exact (ite_eq_left (hh.trans (Nat.le_succ q))).trans (ite_eq_left hh).symm
  have same : RandomSystem.limitMass domain R = parallelMass p r := by
    funext h
    exact ite_eq_left le_rfl
  exact same ▸ RandomSystem.limitMass_isRandomSystem domain R coherent

end SystemAlgebra

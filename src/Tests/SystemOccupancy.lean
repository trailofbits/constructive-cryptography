module

public import RandomSystems.Cumulative.Occupancy
public import Tests.ObservationKernel
public import Mathlib.Data.Finsupp.Multiset

/-!
# Occupancy under an adaptive observer

Fresh fair replies enter bins 7 and 8. The observer stops after a false first reply and
otherwise queries adaptively on the same input-dependent domain as the kernel test.
The two-round repeated-bin bound is one half; all count and mass contracts are discharged.
-/

@[expose] public section

noncomputable section

namespace Tests.SystemOccupancy

open SystemAlgebra Probability Probability.Distribution
open ObservationKernel (queries observer)

/-- Every admitted query receives an independent fair bit. -/
def coins : RandomSystem Bool Bool queries :=
  RandomSystem.ofConditional (fun _ _ _ => 𝒰[Bool])

/-- Count true replies in bin 7 and false replies in bin 8. -/
def counts (h : List (Bool × Bool)) : ℕ →₀ ℕ :=
  Multiset.toFinsupp (h.map (fun p => if p.2 then 7 else 8) : Multiset ℕ)

/-- A reply contributes to its corresponding bin. -/
def pick (_ : List (Bool × Bool)) (_ : Bool) (y : Bool) : Option ℕ :=
  some (if y then 7 else 8)

/-- The observer's admission guarantee is independent of the reply law. -/
lemma compatible : coins.Compatible observer := by
  intro h x _ _ selected
  change h.length < 3 ∧ (h ≠ [] → x = true)
  rcases h with _ | ⟨⟨a, b⟩, h⟩
  · exact ⟨by norm_num, fun impossible => (impossible rfl).elim⟩
  rcases h with _ | ⟨⟨a', b'⟩, h⟩
  · cases b <;> simp only [List.map_cons, List.map_nil, observer, Part.mem_some_iff,
      Part.notMem_none] at selected
    exact ⟨by simp only [List.length_cons, List.length_nil]; norm_num, fun _ => selected⟩
  rcases h with _ | ⟨z, h⟩
  · cases b' <;> simp only [List.map_cons, List.map_nil, observer, Part.mem_some_iff,
      Part.notMem_none] at selected
    exact ⟨by simp only [List.length_cons, List.length_nil]; norm_num, fun _ => selected⟩
  · simp only [List.map_cons, observer, Part.notMem_none] at selected

/-- Appending an exchange adds exactly the selected bin. -/
lemma counts_snoc (h : List (Bool × Bool)) (x y : Bool) :
    counts (h ++ [(x, y)]) = (counts h).addDraw (pick h x y) := by
  simp only [counts, List.map_append, List.map_cons, List.map_nil, ← Multiset.coe_add,
    Multiset.coe_singleton,
    Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, pick, Finsupp.addDraw, Option.elim]

/-- Each reply bin has conditional mass at most one half. -/
lemma extension_mass (h : List (Bool × Bool)) (x : Bool) (admitted : queries h x)
    (b : ℕ) :
    (coins.extensionLaw h x).mass (fun y => pick h x y = some b) ≤ (1 / 2 : ℝ) * coins h := by
  have extension : coins.extensionLaw h x = coins h • (𝒰[Bool]).1 := by
    ext y
    rw [RandomSystem.extensionLaw_apply]
    change RandomSystem.ofConditional _ (h ++ [(x, y)]) = _
    rw [RandomSystem.ofConditional_snoc, dite_eq_left admitted]
    rfl
  rw [extension, mass_smul]
  have cap : (𝒰[Bool]).1.mass (fun y => pick h x y = some b) ≤ (1 / 2 : ℝ) := by
    norm_num [mass_eq_sum, ProbDist.uniform, uniform_apply, Fintype.sum_bool, pick]
    split_ifs <;> norm_num at *
    omega
  exact (mul_le_mul_of_nonneg_left cap (coins.mass_nonneg h)).trans_eq (mul_comm _ _)

/-- The adaptive first two rounds repeat a reply bin with probability at most one half. -/
example : (coins.sLaw observer 2).mass (fun h => ∃ b, 2 ≤ counts h b) ≤ 1 / 2 := by
  have bound := coins.sLaw_mass_occupancy_ge_le observer compatible counts pick
    (Q := 2) (by exact Multiset.toFinsupp_zero)
    (fun _ _ _ _ x _ y _ => counts_snoc _ x y)
    (δ := 1 / 2) (by norm_num) (fun i _ h hh x hx b _ => by
      have member : h ∈ coins.tSupp observer i := Finsupp.support_onFinset_subset hh
      exact extension_mass h x
        (compatible h x (RandomSystem.tSupp_good member).1
          (RandomSystem.tSupp_possible member) hx) b)
    (m := 2) (by norm_num)
  norm_num at bound ⊢
  exact bound

#print axioms RandomSystem.sLaw_mass_occupancy_ge_le

end Tests.SystemOccupancy

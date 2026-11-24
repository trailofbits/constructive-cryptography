module

public import ConstructiveCryptography.Instances.FilteredDistance
public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Parallel

/-!
# Ratio checks on a filtered domain

A two-query interface is filtered to one query or none. The ratio assumption applies only to
histories inside that limit; the cost function and its original budget are passed unchanged.
A Boolean-query test has positive loss `1/2` and a ratio that fails on an excluded input.
-/

@[expose] public section

namespace Tests.FilteredRatio

open SystemAlgebra Probability
open scoped SystemAlgebra NNReal BigOperators

/-- Boolean replies on at most two unit queries. -/
abbrev replies := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

/-- Retain only input histories of length at most `n`. -/
noncomputable def atMost (n : ℕ) :=
  TypedConverter.filter replies (fun h => h.length ≤ n)
    (fun _ _ hp hn => hp.length_le.trans hn)

/-- A ratio on the first `n` replies suffices after the matching filter. -/
lemma prefix_bound (n : ℕ) (R S : TypedSystem replies)
    (g : List ((Σ i, replies.X i) × (Σ i, replies.Y i)) → ℝ) (ε δ : ℝ≥0)
    (nonneg : ∀ h, 0 ≤ g h) (below : ∀ h, g h ≤ S.1 h) (whole : g [] = 1)
    (ratio : ∀ h, h.length ≤ n → (1 - (ε : ℝ)) * g h ≤ R.1 h)
    (cost : List ((Σ i, replies.X i) × (Σ i, replies.Y i)) → (Σ i, replies.X i) → ℝ)
    (loss : ∀ h x, S.1 h ≠ 0 → replies.inputDomain h x →
      g h - ∑ y, g (h ++ [(x, y)]) ≤ cost h x * S.1 h)
    (budget : ∀ h, S.1 h ≠ 0 → transcriptCost cost h ≤ δ) :
    (atMost n • R).1.transcriptDistance (atMost n • S).1 ≤ (ε : ENNReal) + δ := by
  apply RandomSystem.filtered_distance_le_of_ratio_and_cost R S _ _ g ε δ
    nonneg below whole ?_ cost loss budget
  intro h hh
  apply ratio h
  obtain he | hd :=
    (admitted_ofInputs_iff (replies.restrict _ _).nonempty_prefix h).mp hh
  · simp only [he, List.length_nil, Nat.zero_le]
  · simpa only [List.length_map] using hd.2

/-- With no admitted query, the ratio premise is needed only at the empty transcript. -/
example (R : TypedSystem replies) (g : List ((Σ i, replies.X i) × (Σ i, replies.Y i)) → ℝ)
    (whole : g [] = 1) : ∀ h, h.length ≤ 0 → (1 - ((0 : ℝ≥0) : ℝ)) * g h ≤ R.1 h := by
  intro h hh
  have he : h = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hh)
  simp only [he, whole, RandomSystem.mass_nil, NNReal.coe_zero, sub_zero, one_mul, le_refl]

/-! ## Positive loss with a ratio that fails outside the filter -/

/-- One Boolean query and reply on a single port. -/
abbrev bitQuery := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1

/-- `constantReplies(x) = false`, whereas `echoReplies(x) = x`. -/
noncomputable def constantReplies : TypedSystem bitQuery :=
  TypedSystem.ofFunction (fun _ _ => false)

/-- The echo system retains no state and answers its sole query unchanged. -/
noncomputable def echoReplies : TypedSystem bitQuery :=
  TypedSystem.ofFunction (fun _ x => x)

/-- Admit only false queries, on which the two reply functions coincide. -/
def falseInputs (xs : List (Σ i, bitQuery.X i)) : Prop := ∀ x ∈ xs, x.2 = false

lemma falseInputs_prefix {xs ys} (hp : xs <+: ys) (hy : falseInputs ys) :
    falseInputs xs := fun x hx => hy x (hp.subset hx)

open Classical in
/-- Keep all empty-history mass and half the ideal mass after its one query. -/
noncomputable def halfMass (h : List ((Σ i, bitQuery.X i) × (Σ i, bitQuery.Y i))) : ℝ :=
  if h = [] then 1 else constantReplies.1 h / 2

/-- Each possible nonempty ideal history has length one, hence costs exactly `1/2`. -/
lemma half_cost_bound (h) (hh : constantReplies.1 h ≠ 0) :
    transcriptCost (fun _ _ => (1 / 2 : ℝ)) h ≤ (1 / 2 : ℝ) := by
  have hl : h.length ≤ 1 := by
    rcases constantReplies.possible_domain hh with he | hd
    · simp only [List.map_eq_nil_iff] at he
      simp only [he, List.length_nil, Nat.zero_le]
    · simpa only [List.length_map] using hd.2
  cases h with
  | nil => norm_num [transcriptCost]
  | cons z tail =>
    have ht : tail = [] := List.length_eq_zero_iff.mp (by simpa using hl)
    subst tail
    norm_num [transcriptCost]

/-- The retained submass loses `1/2` at the admitted query, independently of its input. -/
lemma halfMass_loss (h) (x : Σ i, bitQuery.X i) (hx : bitQuery.inputDomain h x) :
    halfMass h - ∑ y, halfMass (h ++ [(x, y)]) ≤ (1 / 2 : ℝ) * constantReplies.1 h := by
  classical
  have he : h = [] := List.length_eq_zero_iff.mp
    (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Interface.queryBudget_inputDomain_iff.mp hx)))
  subst h
  have normal : (∑ y, constantReplies.1 [(x, y)]) = 1 := by
    calc
      _ = (constantReplies.1.extensionLaw [] x).weight := by
        rw [Distribution.weight_eq_sum]
        exact Finset.sum_congr rfl fun y _ =>
          (constantReplies.1.extensionLaw_apply [] x y).symm
      _ = 1 := by rw [constantReplies.1.extensionLaw_weight, ite_eq_left hx,
        RandomSystem.mass_nil]
  simp only [List.nil_append, halfMass, List.cons_ne_nil, reduceIte,
    RandomSystem.mass_nil, div_eq_mul_inv]
  rw [← Finset.sum_mul, normal]
  norm_num

/-- On false inputs the two function systems coincide; the ratio uses only those inputs. -/
lemma halfMass_ratio (h) (hh : Admitted (bitQuery.restrict falseInputs
    (fun _ _ => falseInputs_prefix)).inputDomain h) :
    (1 - (1 / 4 : ℝ)) * halfMass h ≤ echoReplies.1 h := by
  classical
  rcases (admitted_ofInputs_iff (bitQuery.restrict falseInputs
    (fun _ _ => falseInputs_prefix)).nonempty_prefix h).mp hh with he | hd
  · subst h
    norm_num [halfMass, RandomSystem.mass_nil]
  · have eq : echoReplies.1 h = constantReplies.1 h := by
      rw [echoReplies, constantReplies, TypedSystem.ofFunction_mass,
        TypedSystem.ofFunction_mass]
      congr 2
      apply propext
      apply forall_congr'
      intro z
      apply imp_congr_right
      intro hz
      rw [hd.2 z.1 (List.mem_map_of_mem hz)]
    have hn := constantReplies.1.mass_nonneg h
    have hne : h ≠ [] := fun he => hd.1.1 (by simp only [he, List.map_nil])
    rw [eq, halfMass, ite_eq_right hne]
    linarith

/-- The excluded true query has ideal good mass `1/2` but real mass zero. -/
example : ¬ (1 - (1 / 4 : ℝ)) * halfMass [(⟨(), true⟩, ⟨(), false⟩)] ≤
    echoReplies.1 [(⟨(), true⟩, ⟨(), false⟩)] := by
  norm_num [halfMass, echoReplies, constantReplies, TypedSystem.ofFunction_mass,
    Interface.queryBudget]

/-- The filter permits the ratio-and-cost bound `1/4 + 1/2`, with the original positive cost. -/
lemma filtered_positive_cost :
    Δ (TypedConverter.filter bitQuery falseInputs (fun _ _ => falseInputs_prefix) • echoReplies)
      (TypedConverter.filter bitQuery falseInputs (fun _ _ => falseInputs_prefix) • constantReplies)
      ≤ ((1 / 4 : ℝ≥0) : ENNReal) + (1 / 2 : ℝ≥0) := by
  apply Interface.distance_filter_le_of_ratio_and_cost echoReplies constantReplies
    falseInputs (fun _ _ => falseInputs_prefix) halfMass (1 / 4) (1 / 2)
  · intro h
    classical
    unfold halfMass
    split
    · norm_num
    · exact div_nonneg (constantReplies.1.mass_nonneg h) (by norm_num)
  · intro h
    classical
    unfold halfMass
    split
    · rename_i he
      simp only [he, RandomSystem.mass_nil, le_refl]
    · have hn := constantReplies.1.mass_nonneg h
      linarith
  · exact ite_eq_left rfl
  · simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using halfMass_ratio
  · exact fun h x _ hx => halfMass_loss h x hx
  · simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using half_cost_bound

/-- Even before restricting inputs, normalized transcript laws give the unit upper bound. -/
example : Δ echoReplies constantReplies ≤ 1 :=
  Interface.distance_le_one echoReplies constantReplies

#print axioms filtered_positive_cost

#print axioms prefix_bound
#print axioms RandomSystem.filtered_distance_le_of_ratio_and_cost

end Tests.FilteredRatio

module

public import RandomSystems.Cumulative.Parallel
public import RandomSystems.Converter.ConverterTensor

/-!
# Independent parallel behavior on input domains

`parallelMass_admits_iff_ofInputs` identifies the guarded parallel domain on nonzero
histories. `parallelMass_isRandomSystem_ofInputs` transports normalization to the combined
input domain and moves the component tag into the port label.
-/

@[expose] public section

namespace SystemAlgebra

open RandomSystem

-- `I`, `J` carry component ports; `X`, `Y` are queries and `Z`, `W` their replies.
variable {I J : Type} {X Z : I → Type} {Y W : J → Type}
-- `E`, `F` admit component input histories; `p`, `r` are their cumulative masses.
variable {E : List (Σ i, X i) → Prop} {F : List (Σ j, Y j) → Prop}
  {p : List ((Σ i, X i) × (Σ i, Z i)) → ℝ}
  {r : List ((Σ j, Y j) × (Σ j, W j)) → ℝ}

/-- On a possible history, parallel admission is exactly componentwise input admission. -/
lemma parallelMass_admits_iff_ofInputs
    -- `hp`, `hr` normalize the components on their input-only domains.
    (hp : IsRandomSystem (fun h x => E (h.map Prod.fst ++ [x])) p)
    (hr : IsRandomSystem (fun h x => F (h.map Prod.fst ++ [x])) r)
    (h : List (Two (Σ i, X i) (Σ j, Y j) × Two (Σ i, Z i) (Σ j, W j)))
    (hh : parallelMass p r h ≠ 0) (x : Two (Σ i, X i) (Σ j, Y j)) :
    (parallelConsistent h ∧ parallelAdmits
      (fun h x => E (h.map Prod.fst ++ [x]))
      (fun h x => F (h.map Prod.fst ++ [x])) h x) ↔
    parallelInputs E F ((h.map Prod.fst).map (sumAlphabet (Sum.rec X Y)) ++
      [sumAlphabet (Sum.rec X Y) x]) := by
  classical
  -- Nonzero product mass supplies consistency and possible component histories.
  have hc : parallelConsistent h := by
    by_contra hn
    exact hh (by simp only [parallelMass, ite_eq_right hn])
  have components : p (parallelLeft h) ≠ 0 ∧ r (parallelRight h) ≠ 0 := by
    simpa only [parallelMass, ite_eq_left hc, ne_eq, mul_eq_zero, not_or] using hh
  have left := hp.possible_inputs components.1
  have right := hr.possible_inputs components.2
  rw [parallelLeft_queries hc] at left
  rw [parallelRight_queries hc] at right
  -- Alphabet renaming cancels before the selected query is appended.
  have inverse : (sumAlphabet (Sum.rec X Y)).symm ∘ sumAlphabet (Sum.rec X Y) = id :=
    funext (fun z => (sumAlphabet (Sum.rec X Y)).symm_apply_apply z)
  have mapped : ((h.map Prod.fst).map (sumAlphabet (Sum.rec X Y))).map
      (sumAlphabet (Sum.rec X Y)).symm = h.map Prod.fst := by
    rw [List.map_map, inverse, List.map_id]
  simp only [parallelInputs, List.map_append, List.map_singleton, mapped,
    Equiv.symm_apply_apply]
  rcases x with ⟨(_ | ⟨⟩), x⟩ <;>
    simp only [hc, true_and, parallelAdmits, parallelLeft_queries hc,
      parallelRight_queries hc, restrict_append, restrict_cons_self, restrict_cons_ne,
      restrict_nil, List.append_nil, List.append_eq_nil_iff, List.cons_ne_nil, and_false,
      not_false_eq_true, false_or, left, right, and_true, true_and, ne_eq,
      reduceCtorEq]

/-- Independent component laws normalize on the combined input-only domain. -/
theorem parallelMass_isRandomSystem_ofInputs
    -- Finite component alphabets supply the existing finite-cut parallel normalization.
    [_root_.Finite (Σ i, X i)] [_root_.Finite (Σ i, Z i)]
    [_root_.Finite (Σ j, Y j)] [_root_.Finite (Σ j, W j)]
    (hp : IsRandomSystem (fun h x => E (h.map Prod.fst ++ [x])) p)
    (hr : IsRandomSystem (fun h x => F (h.map Prod.fst ++ [x])) r) :
    IsRandomSystem (fun h x => parallelInputs E F (h.map Prod.fst ++ [x]))
      (fun h => parallelMass p r (h.map
        ((sumAlphabet (Sum.rec X Y)).symm.prodCongr
          (sumAlphabet (Sum.rec Z W)).symm))) := by
  let eX := sumAlphabet (Sum.rec X Y)
  let eY := sumAlphabet (Sum.rec Z W)
  -- Relabel the normalized product, then identify its domain on nonzero histories.
  apply ((parallelMass_isRandomSystem hp hr).relabel eX eY).congr_domain
  intro h hh x
  have he := parallelMass_admits_iff_ofInputs hp hr
    (h.map (eX.symm.prodCongr eY.symm)) hh (eX.symm x)
  have hf : ((h.map (eX.symm.prodCongr eY.symm)).map Prod.fst).map eX =
      h.map Prod.fst := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro z hz
    exact eX.apply_symm_apply z.1
  rw [hf, eX.apply_symm_apply] at he
  exact he

/-- Parallel composition preserves replies at the queried component port. -/
lemma parallelMass_repliesAtQueriedInterface
    -- `hp`, `hr` give zero mass to a wrong-port reply in each component.
    (hp : ∀ h (x : Σ i, X i) (y : Σ i, Z i), y.1 ≠ x.1 → p (h ++ [(x, y)]) = 0)
    (hr : ∀ h (x : Σ j, Y j) (y : Σ j, W j), y.1 ≠ x.1 → r (h ++ [(x, y)]) = 0)
    -- `h` is the parallel prefix; `x`, `y` are the next query/reply at distinct ports.
    (h : List ((Σ l, Sum.rec X Y l) × (Σ l, Sum.rec Z W l)))
    (x : Σ l, Sum.rec X Y l) (y : Σ l, Sum.rec Z W l) (hne : y.1 ≠ x.1) :
    parallelMass p r ((h ++ [(x, y)]).map
      ((sumAlphabet (Sum.rec X Y)).symm.prodCongr
        (sumAlphabet (Sum.rec Z W)).symm)) = 0 := by
  classical
  rw [List.map_append, List.map_singleton]
  let t := h.map ((sumAlphabet (Sum.rec X Y)).symm.prodCongr
    (sumAlphabet (Sum.rec Z W)).symm)
  rcases x with ⟨(i | j), x⟩ <;> rcases y with ⟨(k | l), y⟩
  · -- Within the left component, its wrong-port mass is zero.
    have hz := hp (parallelLeft t) ⟨i, x⟩ ⟨k, y⟩ (fun he => hne (congrArg Sum.inl he))
    change parallelMass p r (t ++ [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) = 0
    simp only [parallelMass]
    split_ifs
    · simpa only [parallelLeft, parallelRight, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.append_nil] using mul_eq_zero.mpr (Or.inl hz)
    · rfl
  · -- A reply from the other component violates parallel consistency.
    change parallelMass p r (t ++ [(⟨none, ⟨i, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) = 0
    simp only [parallelMass, parallelConsistent_snoc, reduceCtorEq, and_false, ite_false]
  · -- The opposite cross-component direction also violates consistency.
    change parallelMass p r (t ++ [(⟨some (), ⟨j, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) = 0
    simp only [parallelMass, parallelConsistent_snoc, reduceCtorEq, and_false, ite_false]
  · -- Within the right component, its wrong-port mass is zero.
    have hz := hr (parallelRight t) ⟨j, x⟩ ⟨l, y⟩ (fun he => hne (congrArg Sum.inr he))
    change parallelMass p r (t ++ [(⟨some (), ⟨j, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) = 0
    simp only [parallelMass]
    split_ifs
    · simpa only [parallelLeft, parallelRight, List.filterMap_append, List.filterMap_cons,
        List.filterMap_nil, List.append_nil] using mul_eq_zero.mpr (Or.inr hz)
    · rfl

end SystemAlgebra

module

public import RandomSystems.Typed.Interface
public import RandomSystems.Converter.ConverterTensor

/-!
# Parallel interfaces and parallel typed systems

The parallel interface of `A` and `B` has both label sets, the parallel domain of the two
domains, and the sum of the two bounds. The parallel composition of two typed systems is the
parallel composition of their random systems, with the component tag moved into the
interface label. The parallel composition of two typed converters is the parallel composition
of their PDC behaviors.

## Main definitions

* `Interface.parallelDomain A B`: the parallel domain of two interfaces
* `Interface.tensor A B`: the parallel interface
* `TypedSystem.parallel R S`: the parallel composition of typed systems
* `TypedConverter.parallel α β`: the parallel composition of typed converters

## Main results

* `TypedSystem.parallel_admits_iff`: on possible histories, the parallel domain of the random
  systems is the domain of the parallel interface
* `tensor_inputDomain_inl_iff`: a left query projects to its component domain on every
  consistent history
* `TypedSystem.parallel_mass_snoc_inl`: a left extension factors into its left mass and
  the unchanged right prefix mass, including zero-probability histories
-/

@[expose] public section

namespace SystemAlgebra.RandomSystem

open Classical in
/-- Admission at impossible histories has no effect on cumulative behavior. -/
def withDomain {A B : Type} [Fintype A] [Fintype B] {D E : Domain A B}
    (R : RandomSystem A B D)
    (he : ∀ h, R h ≠ 0 → ∀ x, D h x ↔ E h x) : RandomSystem A B E :=
  ⟨R.1, R.mass_nil, R.mass_nonneg, fun h x => by
    obtain ⟨μ, hm, hw⟩ := R.2.2.2 h x
    refine ⟨μ, hm, hw.trans ?_⟩
    by_cases hz : R h = 0
    · simp only [hz, ite_self]
    · rw [he h hz x]⟩

end SystemAlgebra.RandomSystem

namespace SystemAlgebra

open Probability

namespace Interface

/-- Exchange the two local interface families, retaining each message value. -/
def swapAlphabet {I J : Type} (F : I → Type) (G : J → Type) :
    (Σ l, Sum.rec F G l) ≃ (Σ l, Sum.rec G F l) where
  toFun
    | ⟨.inl i, x⟩ => ⟨.inr i, x⟩
    | ⟨.inr j, y⟩ => ⟨.inl j, y⟩
  invFun
    | ⟨.inl j, y⟩ => ⟨.inr j, y⟩
    | ⟨.inr i, x⟩ => ⟨.inl i, x⟩
  left_inv := by rintro ⟨(i | j), x⟩ <;> rfl
  right_inv := by rintro ⟨(j | i), x⟩ <;> rfl

/-- The parallel domain of two interfaces. -/
abbrev parallelDomain (A B : Interface) : List (Σ l, Sum.rec A.X B.X l) → Prop :=
  parallelInputs (F := Sum.rec A.X B.X) A.domain B.domain

open Classical in
lemma parallelDomain_swap (A B : Interface) (h : List (Σ l, Sum.rec A.X B.X l)) :
    parallelDomain B A (h.map (swapAlphabet A.X B.X)) ↔ parallelDomain A B h := by
  have hp :
      restrict none ((h.map (swapAlphabet A.X B.X)).map (sumAlphabet (Sum.rec B.X A.X)).symm) =
        restrict (some ()) (h.map (sumAlphabet (Sum.rec A.X B.X)).symm) ∧
      restrict (some ()) ((h.map (swapAlphabet A.X B.X)).map (sumAlphabet (Sum.rec B.X A.X)).symm) =
        restrict none (h.map (sumAlphabet (Sum.rec A.X B.X)).symm) := by
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | cons x h ih =>
      rcases x with ⟨(i | j), x⟩ <;>
        simpa only [List.map_cons, swapAlphabet, sumAlphabet, Equiv.coe_fn_mk,
          Equiv.coe_fn_symm_mk, restrict_cons_self,
          restrict_cons_ne (by simp : (none : Option Unit) ≠ some ()),
          restrict_cons_ne (by simp : (some () : Option Unit) ≠ none),
          List.cons.injEq, true_and] using ih
  simp only [parallelDomain, parallelInputs, hp.1, hp.2]
  have hn : h.map (swapAlphabet A.X B.X) ≠ [] ↔ h ≠ [] := not_congr List.map_eq_nil_iff
  rw [hn]
  tauto

/-- The parallel interface: both label sets, with the combined domain. -/
abbrev tensor (A B : Interface) : Interface where
  I := A.I ⊕ B.I
  X := Sum.rec A.X B.X
  Y := Sum.rec A.Y B.Y
  domain := parallelDomain A B
  nonempty_prefix := parallelInputs_nonempty_prefix A.nonempty_prefix.2 B.nonempty_prefix.2
  bound := A.bound + B.bound
  length_le := parallelInputs_length_le A.length_le B.length_le

end Interface

-- Retag exchanges by component: left is `none`, right is `some ()`.
local notation:max "sides " A:max B:max h:max =>
  List.map (Equiv.prodCongr (Equiv.symm (sumAlphabet (Sum.rec (Interface.X A) (Interface.X B))))
    (Equiv.symm (sumAlphabet (Sum.rec (Interface.Y A) (Interface.Y B))))) h

/-- After a consistent transcript `h`, the tensor admits a left query `inl i(x)` exactly when `A`
admits `i(x)` after the left transcript and the right inputs are empty or lie in `B`'s domain. -/
lemma tensor_inputDomain_inl_iff {A B : Interface}
    -- `h` is a transcript of `A ⊗ B` whose exchanges are each with one side (`hc`).
    (h : List ((Σ l, (A.tensor B).X l) × (Σ l, (A.tensor B).Y l)))
    (hc : RandomSystem.parallelConsistent (sides A B h)) (i : A.I) (x : A.X i) :
    (A.tensor B).inputDomain h ⟨.inl i, x⟩ ↔
      A.inputDomain (RandomSystem.parallelLeft (sides A B h)) ⟨i, x⟩ ∧
        ((RandomSystem.parallelRight (sides A B h)).map Prod.fst = [] ∨
          B.domain ((RandomSystem.parallelRight (sides A B h)).map Prod.fst)) := by
  -- Both sides read the inputs of `h` split by side; `i(x)` extends the left inputs only.
  have hq : (sides A B h).map Prod.fst =
      (h.map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X)).symm := by
    simp only [List.map_map]
    rfl
  change parallelInputs A.domain B.domain (h.map Prod.fst ++ [⟨.inl i, x⟩]) ↔
    A.domain ((RandomSystem.parallelLeft (sides A B h)).map Prod.fst ++ [⟨i, x⟩]) ∧ _
  rw [RandomSystem.parallelLeft_queries hc, RandomSystem.parallelRight_queries hc, hq]
  have hx : (sumAlphabet (Sum.rec A.X B.X)).symm ⟨.inl i, x⟩ = ⟨none, ⟨i, x⟩⟩ := rfl
  -- The extended history and its left part are nonempty; its right part is unchanged.
  simp only [parallelInputs, List.map_append, List.map_cons, List.map_nil, hx, restrict_append,
    restrict_cons_self, restrict_cons_ne, restrict_nil, List.append_nil, ne_eq,
    List.append_eq_nil_iff, List.cons_ne_nil, reduceCtorEq, and_false, not_false_eq_true,
    false_or, true_and]

namespace TypedSystem

open Interface

lemma possible_domain {A : Interface} (R : TypedSystem A)
    {h : List ((Σ i, A.X i) × (Σ i, A.Y i))} (hp : R.1 h ≠ 0) :
    h.map Prod.fst = [] ∨ A.domain (h.map Prod.fst) := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨x, y⟩, rfl⟩
  · exact Or.inl rfl
  · apply Or.inr
    simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hp ⊢
    by_contra hd
    exact hp (R.1.mass_eq_zero_of_not_admitted hd y)

open Classical in
lemma parallel_admits_iff (A B : Interface) (R : TypedSystem A) (S : TypedSystem B)
    (h : List (Two (Σ i, A.X i) (Σ j, B.X j) × Two (Σ i, A.Y i) (Σ j, B.Y j)))
    (hp : RandomSystem.parallel R.1 S.1 h ≠ 0)
    (x : Two (Σ i, A.X i) (Σ j, B.X j)) :
    A.inputDomain.parallel B.inputDomain h x ↔
    parallelDomain A B
      ((h.map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X)) ++
        [sumAlphabet (Sum.rec A.X B.X) x]) := by
  have hh : RandomSystem.parallelConsistent h := by
    by_contra hn
    exact hp (by simp [RandomSystem.parallel_mass, hn])
  have hab : R.1 (RandomSystem.parallelLeft h) ≠ 0 ∧
      S.1 (RandomSystem.parallelRight h) ≠ 0 := by
    simpa only [RandomSystem.parallel_mass, ite_eq_left hh, ne_eq, mul_eq_zero, not_or] using hp
  have hla : (RandomSystem.parallelLeft h).length ≤ A.bound := by
    by_contra hl
    exact hab.1 (R.1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl))
  have hlb : (RandomSystem.parallelRight h).length ≤ B.bound := by
    by_contra hl
    exact hab.2 (S.1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl))
  have ha := R.possible_domain hab.1
  have hb := S.possible_domain hab.2
  rw [RandomSystem.parallelLeft_queries hh] at ha
  rw [RandomSystem.parallelRight_queries hh] at hb
  have inv : (sumAlphabet (Sum.rec A.X B.X)).symm ∘
      (sumAlphabet (Sum.rec A.X B.X)) = id := by
    funext z
    exact (sumAlphabet (Sum.rec A.X B.X)).symm_apply_apply z
  simp only [parallelDomain, parallelInputs, List.map_append, List.map_singleton]
  have hm : ((h.map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X))).map
      (sumAlphabet (Sum.rec A.X B.X)).symm = h.map Prod.fst := by
    rw [List.map_map, inv, List.map_id]
  rw [hm]
  have hx := (sumAlphabet (Sum.rec A.X B.X)).symm_apply_apply x
  rw [hx]
  rcases x with ⟨(_ | ⟨⟩), ⟨i, x⟩⟩
  · have hlb' : (RandomSystem.parallelRight h).length ≤ B.inputDomain.bound := hlb
    simp [Domain.parallel, hh, hlb', hb, RandomSystem.parallelLeft_queries hh]
  · have hla' : (RandomSystem.parallelLeft h).length ≤ A.inputDomain.bound := hla
    simp [Domain.parallel, hh, hla', ha, RandomSystem.parallelRight_queries hh]

open Classical in
/-- Parallel typed systems use the product cumulative behavior. The two domain
descriptions agree on every possible history, including rejected next queries. -/
noncomputable def parallel {A B : Interface} (R : TypedSystem A) (S : TypedSystem B) :
    TypedSystem (tensor A B) := by
  let eX := sumAlphabet (Sum.rec A.X B.X)
  let eY := sumAlphabet (Sum.rec A.Y B.Y)
  let T := (RandomSystem.parallel R.1 S.1).relabel eX eY
  have hd : ∀ h, T h ≠ 0 → ∀ x,
      (A.inputDomain.parallel B.inputDomain).relabel eX eY h x ↔
        (tensor A B).inputDomain h x := by
    intro h hp x
    have he := parallel_admits_iff A B R S (h.map (eX.symm.prodCongr eY.symm)) hp (eX.symm x)
    have hf : ((h.map (eX.symm.prodCongr eY.symm)).map Prod.fst).map eX =
        h.map Prod.fst := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro z hz
      exact eX.apply_symm_apply z.1
    rw [hf, eX.apply_symm_apply] at he
    exact he
  refine ⟨T.withDomain hd, ?_⟩
  intro h x y hne
  change RandomSystem.parallel R.1 S.1
    ((h ++ [(x, y)]).map (eX.symm.prodCongr eY.symm)) = 0
  rw [List.map_append, List.map_singleton]
  let p := h.map (eX.symm.prodCongr eY.symm)
  rcases x with ⟨(i | j), x⟩ <;> rcases y with ⟨(k | l), y⟩
  · have hy : k ≠ i := fun he => hne (congrArg Sum.inl he)
    have hr := R.2 (RandomSystem.parallelLeft p) ⟨i, x⟩ ⟨k, y⟩ hy
    change RandomSystem.parallel R.1 S.1 (p ++ [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) = 0
    simp only [RandomSystem.parallel_mass]
    split_ifs
    · simpa only [RandomSystem.parallelLeft, RandomSystem.parallelRight,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        List.append_nil] using mul_eq_zero.mpr (Or.inl hr)
    · rfl
  · change RandomSystem.parallel R.1 S.1 (p ++ [(⟨none, ⟨i, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) = 0
    simp [RandomSystem.parallel_mass, RandomSystem.parallelConsistent_snoc]
  · change RandomSystem.parallel R.1 S.1 (p ++ [(⟨some (), ⟨j, x⟩⟩, ⟨none, ⟨k, y⟩⟩)]) = 0
    simp [RandomSystem.parallel_mass, RandomSystem.parallelConsistent_snoc]
  · have hy : l ≠ j := fun he => hne (congrArg Sum.inr he)
    have hs := S.2 (RandomSystem.parallelRight p) ⟨j, x⟩ ⟨l, y⟩ hy
    change RandomSystem.parallel R.1 S.1 (p ++ [(⟨some (), ⟨j, x⟩⟩, ⟨some (), ⟨l, y⟩⟩)]) = 0
    simp only [RandomSystem.parallel_mass]
    split_ifs
    · simpa only [RandomSystem.parallelLeft, RandomSystem.parallelRight,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        List.append_nil] using mul_eq_zero.mpr (Or.inr hs)
    · rfl

lemma parallel_mass {A B : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (h : List ((Σ i, (tensor A B).X i) × (Σ i, (tensor A B).Y i))) :
    (parallel R S).1 h = RandomSystem.parallel R.1 S.1
      (h.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
        (sumAlphabet (Sum.rec A.Y B.Y)).symm)) := rfl

/-- A left reply extends the left transcript and retains the right prefix mass. -/
lemma parallel_mass_snoc_inl {A B : Interface}
    -- `R` and `S` are the independent resources at interfaces `A` and `B`.
    (R : TypedSystem A) (S : TypedSystem B)
    -- Every exchange in `h` stays on one side; its probability may be zero.
    (h : List ((Σ l, (A.tensor B).X l) × (Σ l, (A.tensor B).Y l)))
    (hc : RandomSystem.parallelConsistent (sides A B h))
    -- `x` and `y` are a query and reply at the left port `i`.
    (i : A.I) (x : A.X i) (y : A.Y i) :
    (parallel R S).1 (h ++ [(⟨.inl i, x⟩, ⟨.inl i, y⟩)]) =
      R.1 (RandomSystem.parallelLeft (sides A B h) ++ [(⟨i, x⟩, ⟨i, y⟩)]) *
        S.1 (RandomSystem.parallelRight (sides A B h)) := by
  -- Retag the new exchange, then factor its two projected histories.
  rw [parallel_mass, List.map_append, List.map_singleton]
  change RandomSystem.parallel R.1 S.1
    (sides A B h ++ [(⟨none, ⟨i, x⟩⟩, ⟨none, ⟨i, y⟩⟩)]) = _
  rw [RandomSystem.parallel_mass,
    ite_eq_left (RandomSystem.parallelConsistent_snoc.mpr ⟨hc, rfl⟩)]
  simp only [RandomSystem.parallelLeft, RandomSystem.parallelRight,
    List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.append_nil]

end TypedSystem

open Classical in
/-- **Parallel typed converters**: the parallel composition of the two PDC behaviors. -/
noncomputable def TypedConverter.parallel {A B C D : Interface} (α : TypedConverter A B)
    (β : TypedConverter C D) : TypedConverter (Interface.tensor A C) (Interface.tensor B D) :=
  PDCBehavior.tensor α β

end SystemAlgebra

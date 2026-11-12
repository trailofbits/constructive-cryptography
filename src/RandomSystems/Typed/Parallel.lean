module

public import RandomSystems.Typed.Interface
public import RandomSystems.Cumulative.ParallelInputs

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
-/

@[expose] public section

namespace SystemAlgebra.RandomSystem

/-- Admission at impossible histories has no effect on cumulative behavior. -/
def withDomain {A B : Type} [Fintype A] [Fintype B] {D E : Domain A B}
    (R : RandomSystem A B D)
    (he : ∀ h, R h ≠ 0 → ∀ x, D h x ↔ E h x) : RandomSystem A B E :=
  ⟨R.1, R.2.congr_domain he⟩

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

namespace TypedSystem

open Interface

lemma possible_domain {A : Interface} (R : TypedSystem A)
    {h : List ((Σ i, A.X i) × (Σ i, A.Y i))} (hp : R.1 h ≠ 0) :
    h.map Prod.fst = [] ∨ A.domain (h.map Prod.fst) :=
  R.1.2.possible_inputs hp

lemma parallel_admits_iff (A B : Interface) (R : TypedSystem A) (S : TypedSystem B)
    (h : List (Two (Σ i, A.X i) (Σ j, B.X j) × Two (Σ i, A.Y i) (Σ j, B.Y j)))
    (hp : RandomSystem.parallel R.1 S.1 h ≠ 0)
    (x : Two (Σ i, A.X i) (Σ j, B.X j)) :
    A.inputDomain.parallel B.inputDomain h x ↔
    parallelDomain A B
      ((h.map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X)) ++
        [sumAlphabet (Sum.rec A.X B.X) x]) := by
  classical
  have hh : RandomSystem.parallelConsistent h := by
    by_contra hn
    exact hp (by simp [RandomSystem.parallel_mass, hn])
  have hab : R.1 (RandomSystem.parallelLeft h) ≠ 0 ∧
      S.1 (RandomSystem.parallelRight h) ≠ 0 := by
    simpa only [RandomSystem.parallel_mass, ite_eq_left hh, ne_eq, mul_eq_zero, not_or] using hp
  have hla : (RandomSystem.parallelLeft h).length ≤ A.inputDomain.bound := by
    by_contra hl
    exact hab.1 (R.1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl))
  have hlb : (RandomSystem.parallelRight h).length ≤ B.inputDomain.bound := by
    by_contra hl
    exact hab.2 (S.1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl))
  have admission := parallelMass_admits_iff_ofInputs R.1.2 S.1.2 h hp x
  change _ ↔ parallelDomain A B
    ((h.map Prod.fst).map (sumAlphabet (Sum.rec A.X B.X)) ++
      [sumAlphabet (Sum.rec A.X B.X) x]) at admission
  rw [← admission]
  rcases x with ⟨(_ | ⟨⟩), x⟩ <;>
    simp only [Domain.parallel, hh, true_and, RandomSystem.parallelAdmits, hla, hlb] <;> rfl

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
  exact parallelMass_repliesAtQueriedInterface R.2 S.2

lemma parallel_mass {A B : Interface} (R : TypedSystem A) (S : TypedSystem B)
    (h : List ((Σ i, (tensor A B).X i) × (Σ i, (tensor A B).Y i))) :
    (parallel R S).1 h = RandomSystem.parallel R.1 S.1
      (h.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
        (sumAlphabet (Sum.rec A.Y B.Y)).symm)) := rfl

end TypedSystem

/-- **Parallel typed converters**: the parallel composition of the two PDC behaviors. -/
noncomputable def TypedConverter.parallel {A B C D : Interface} (α : TypedConverter A B)
    (β : TypedConverter C D) : TypedConverter (Interface.tensor A C) (Interface.tensor B D) :=
  PDCBehavior.tensor α β

end SystemAlgebra

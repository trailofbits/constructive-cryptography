import ConstructiveCryptography.InterfaceRelabel

/-!
# Regrouping interfaces

The associator and the unitors keep every message and regroup its interface label; each
component sees the same inputs in either grouping, so the domains correspond exactly. The
unit interface has no labels.

## Main definitions

* `Interface.unit`: the interface without labels
* `Interface.associator`, `Interface.leftUnitor`, `Interface.rightUnitor`: the regrouping
  isomorphisms

## Main results

* `Interface.parallelDomain_assoc`, `Interface.parallelDomain_unit_left`,
  `Interface.parallelDomain_unit_right`: regrouping transports the parallel domain
-/

namespace SystemAlgebra.Interface

open Classical CategoryTheory

def assocAlphabet {I J K : Type} (F : I → Type) (G : J → Type) (H : K → Type) :
    (Σ l, Sum.rec (Sum.rec F G) H l) ≃ (Σ l, Sum.rec F (Sum.rec G H) l) where
  toFun
    | ⟨.inl (.inl i), x⟩ => ⟨.inl i, x⟩
    | ⟨.inl (.inr j), x⟩ => ⟨.inr (.inl j), x⟩
    | ⟨.inr k, x⟩ => ⟨.inr (.inr k), x⟩
  invFun
    | ⟨.inl i, x⟩ => ⟨.inl (.inl i), x⟩
    | ⟨.inr (.inl j), x⟩ => ⟨.inl (.inr j), x⟩
    | ⟨.inr (.inr k), x⟩ => ⟨.inr k, x⟩
  left_inv := by rintro ⟨((i | j) | k), x⟩ <;> rfl
  right_inv := by rintro ⟨(i | j | k), x⟩ <;> rfl

theorem assocAlphabet_fst {I J K : Type} (F : I → Type) (G : J → Type) (H : K → Type)
    (x : Σ l, Sum.rec (Sum.rec F G) H l) :
    (assocAlphabet F G H x).1 = Equiv.sumAssoc I J K x.1 := by
  rcases x with ⟨((i | j) | k), x⟩ <;> rfl

theorem empty_or_parallelDomain (A B : Interface)
    (h : List (Σ l, Sum.rec A.X B.X l)) :
    (h = [] ∨ parallelDomain A B h) ↔
      (restrict none (h.map (sumAlphabet (Sum.rec A.X B.X)).symm) = [] ∨
        A.domain (restrict none (h.map (sumAlphabet (Sum.rec A.X B.X)).symm))) ∧
      (restrict (some ()) (h.map (sumAlphabet (Sum.rec A.X B.X)).symm) = [] ∨
        B.domain (restrict (some ()) (h.map (sumAlphabet (Sum.rec A.X B.X)).symm))) := by
  by_cases hn : h = []
  · simp only [hn, List.map_nil, restrict_nil, true_or, true_and]
  · simp only [parallelDomain, parallelInputs, ne_eq, hn, not_false_eq_true, true_and, false_or]

theorem parallelDomain_assoc (A B C : Interface)
    (h : List (Σ l, Sum.rec (Sum.rec A.X B.X) C.X l)) :
    parallelDomain A (tensor B C) (h.map (assocAlphabet A.X B.X C.X)) ↔
      parallelDomain (tensor A B) C h := by
  let left := h.map (sumAlphabet (Sum.rec (Sum.rec A.X B.X) C.X)).symm
  let right := (h.map (assocAlphabet A.X B.X C.X)).map
    (sumAlphabet (Sum.rec A.X (Sum.rec B.X C.X))).symm
  have projections :
      restrict none right =
        restrict none ((restrict none left).map (sumAlphabet (Sum.rec A.X B.X)).symm) ∧
      restrict none ((restrict (some ()) right).map (sumAlphabet (Sum.rec B.X C.X)).symm) =
        restrict (some ()) ((restrict none left).map (sumAlphabet (Sum.rec A.X B.X)).symm) ∧
      restrict (some ()) ((restrict (some ()) right).map (sumAlphabet (Sum.rec B.X C.X)).symm) =
        restrict (some ()) left := by
    dsimp only [left, right]
    induction h with
    | nil => exact ⟨rfl, rfl, rfl⟩
    | cons x h ih =>
      rcases x with ⟨((i | j) | k), x⟩ <;>
        simpa only [List.map_cons, assocAlphabet, sumAlphabet, Equiv.coe_fn_mk,
          Equiv.coe_fn_symm_mk, restrict_cons_self,
          restrict_cons_ne (by simp : (none : Option Unit) ≠ some ()),
          restrict_cons_ne (by simp : (some () : Option Unit) ≠ none),
          List.cons.injEq, true_and] using ih
  change ((h.map (assocAlphabet A.X B.X C.X)) ≠ [] ∧
      (restrict none right = [] ∨ A.domain (restrict none right)) ∧
      (restrict (some ()) right = [] ∨ parallelDomain B C (restrict (some ()) right))) ↔
    (h ≠ [] ∧ (restrict none left = [] ∨ parallelDomain A B (restrict none left)) ∧
      (restrict (some ()) left = [] ∨ C.domain (restrict (some ()) left)))
  rw [empty_or_parallelDomain, empty_or_parallelDomain, projections.1,
    projections.2.1, projections.2.2]
  simp only [ne_eq, List.map_eq_nil_iff]
  tauto

instance instFintypeEmptyElim : ∀ e : Empty, Fintype (Empty.elim e) := fun e => e.elim

abbrev unit : Interface where
  I := Empty
  X := Empty.elim
  Y := Empty.elim
  domain := fun _ => False
  nonempty_prefix := ⟨id, fun _ _ h => h⟩
  bound := 0
  length_le _ h := h.elim

def leftUnitAlphabet {I : Type} (F : I → Type) :
    (Σ l, Sum.rec (fun e : Empty => Empty.elim e) F l) ≃ (Σ i, F i) where
  toFun
    | ⟨.inl e, _⟩ => e.elim
    | ⟨.inr i, x⟩ => ⟨i, x⟩
  invFun | ⟨i, x⟩ => ⟨.inr i, x⟩
  left_inv := by rintro ⟨(e | i), x⟩; exact e.elim; rfl
  right_inv := by rintro ⟨i, x⟩; rfl

theorem leftUnitAlphabet_fst {I : Type} (F : I → Type)
    (x : Σ l, Sum.rec (fun e : Empty => Empty.elim e) F l) :
    (leftUnitAlphabet F x).1 = Equiv.emptySum Empty I x.1 := by
  rcases x with ⟨(e | i), x⟩
  · exact e.elim
  · rfl

def rightUnitAlphabet {I : Type} (F : I → Type) :
    (Σ l, Sum.rec F (fun e : Empty => Empty.elim e) l) ≃ (Σ i, F i) where
  toFun
    | ⟨.inl i, x⟩ => ⟨i, x⟩
    | ⟨.inr e, _⟩ => e.elim
  invFun | ⟨i, x⟩ => ⟨.inl i, x⟩
  left_inv := by rintro ⟨(i | e), x⟩; rfl; exact e.elim
  right_inv := by rintro ⟨i, x⟩; rfl

theorem rightUnitAlphabet_fst {I : Type} (F : I → Type)
    (x : Σ l, Sum.rec F (fun e : Empty => Empty.elim e) l) :
    (rightUnitAlphabet F x).1 = Equiv.sumEmpty I Empty x.1 := by
  rcases x with ⟨(i | e), x⟩
  · rfl
  · exact e.elim

theorem parallelDomain_unit_left (A : Interface)
    (h : List (Σ l, Sum.rec unit.X A.X l)) :
    A.domain (h.map (leftUnitAlphabet A.X)) ↔ parallelDomain unit A h := by
  change A.domain (h.map (leftUnitAlphabet A.X)) ↔
    h ≠ [] ∧
      (restrict none (h.map (sumAlphabet (Sum.rec (fun e : Empty => e.elim) A.X)).symm) = [] ∨ False) ∧
      (restrict (some ()) (h.map (sumAlphabet (Sum.rec (fun e : Empty => e.elim) A.X)).symm) = [] ∨
        A.domain (restrict (some ()) (h.map (sumAlphabet (Sum.rec (fun e : Empty => e.elim) A.X)).symm)))
  dsimp only [unit] at h
  have hp : restrict none (h.map (sumAlphabet (Sum.rec unit.X A.X)).symm) = [] ∧
      restrict (some ()) (h.map (sumAlphabet (Sum.rec unit.X A.X)).symm) =
        h.map (leftUnitAlphabet A.X) := by
    induction h with
    | nil => exact ⟨rfl, rfl⟩
    | cons x h ih =>
      rcases x with ⟨(e | i), x⟩
      · exact e.elim
      · simpa only [List.map_cons, sumAlphabet, leftUnitAlphabet, Equiv.coe_fn_mk,
          Equiv.coe_fn_symm_mk, restrict_cons_self,
          restrict_cons_ne (by simp : (some () : Option Unit) ≠ none),
          List.cons.injEq, true_and] using ih
  dsimp only [unit] at hp
  simp only [hp.1, hp.2, true_or, true_and, List.map_eq_nil_iff]
  constructor
  · intro hd
    exact ⟨fun he => A.nonempty_prefix.1 (by simpa only [he, List.map_nil] using hd), Or.inr hd⟩
  · rintro ⟨hn, hd⟩
    exact hd.resolve_left hn

theorem parallelDomain_unit_right (A : Interface)
    (h : List (Σ l, Sum.rec A.X unit.X l)) :
    A.domain (h.map (rightUnitAlphabet A.X)) ↔ parallelDomain A unit h := by
  dsimp only [unit] at h
  rw [← parallelDomain_swap]
  have he := parallelDomain_unit_left A (h.map (swapAlphabet A.X unit.X))
  have hm : (h.map (swapAlphabet A.X unit.X)).map (leftUnitAlphabet A.X) =
      h.map (rightUnitAlphabet A.X) := by
    rw [List.map_map]
    apply List.map_congr_left
    rintro ⟨(i | e), x⟩ _
    · rfl
    · exact e.elim
  rwa [hm] at he

noncomputable def associator (A B C : Interface) :
    tensor (tensor A B) C ≅ tensor A (tensor B C) :=
  isoOf (Equiv.sumAssoc A.I B.I C.I) (assocAlphabet A.X B.X C.X) (assocAlphabet A.Y B.Y C.Y)
    (assocAlphabet_fst A.X B.X C.X) (assocAlphabet_fst A.Y B.Y C.Y) (parallelDomain_assoc A B C)

noncomputable def leftUnitor (A : Interface) : tensor unit A ≅ A :=
  isoOf (Equiv.emptySum Empty A.I) (leftUnitAlphabet A.X) (leftUnitAlphabet A.Y)
    (leftUnitAlphabet_fst A.X) (leftUnitAlphabet_fst A.Y) (parallelDomain_unit_left A)

noncomputable def rightUnitor (A : Interface) : tensor A unit ≅ A :=
  isoOf (Equiv.sumEmpty A.I Empty) (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y)
    (rightUnitAlphabet_fst A.X) (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A)

end SystemAlgebra.Interface

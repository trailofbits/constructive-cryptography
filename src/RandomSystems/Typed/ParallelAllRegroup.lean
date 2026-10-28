import RandomSystems.Typed.ParallelAll
import RandomSystems.Cumulative.ParallelAllRegroup

/-!
# Regrouping a typed pair as a finite family

The alphabet equivalence moves the two component tags into the binary interface sum.
The cumulative-mass equation is the explicit bridge between n-ary and binary products;
no identification of different interface types is implicit.
-/

namespace SystemAlgebra

open Interface

open Classical in
/-- Move the two family tags into the binary interface sum, retaining every local port
and message value. -/
def Interface.optionFamilyAlphabet {I : Option Unit → Type} (F : ∀ k, I k → Type) :
    (Σ l : Σ k, I k, F l.1 l.2) ≃
      Σ l, Sum.rec (F none) (F (some ())) l :=
  (Equiv.sigmaAssoc F).trans ((optionPair (fun k => Σ i, F k i)).trans
    (sumAlphabet (Sum.rec (F none) (F (some ())))))

open Classical in
/-- The n-ary independent system with two components is their binary independent system,
after the displayed alphabet regrouping. Jost, Thesis, printed p. 17, treats a finite set
of disjoint-interface resources as one; this specializes that view to two components. -/
lemma TypedSystem.parallelAll_option_mass {A : Option Unit → Interface}
    (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (tensorAll A).X l) × (Σ l, (tensorAll A).Y l))) :
    (TypedSystem.parallelAll R).1 h =
      (TypedSystem.parallel (R none) (R (some ()))).1
        (h.map ((optionFamilyAlphabet fun k => (A k).X).prodCongr
          (optionFamilyAlphabet fun k => (A k).Y))) := by
  -- Apply cumulative locality before regrouping the interface alphabets.
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_option_mass,
    TypedSystem.parallel_mass]
  apply congrArg (fun t => RandomSystem.parallel (R none).1 (R (some ())).1 t)
  simp only [List.map_map]
  apply List.map_congr_left
  intro z _
  -- The binary alphabet map cancels its inverse on each message.
  apply Prod.ext <;> simp [optionFamilyAlphabet]

end SystemAlgebra

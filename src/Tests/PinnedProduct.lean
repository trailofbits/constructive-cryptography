module

public import Probability.PinnedProduct
public import Tests.Conditioning

/-!
# Pinned-product checks

Signed laws on `ℕ` and `ℤ` exercise heterogeneous infinite outcomes. A prescribed value
outside the original support replaces its factor. A nonuniform probability example
retains the observed coordinate jointly with its completed table.
-/

@[expose] public section

namespace Tests.PinnedProduct

open Probability Probability.Distribution

/-- The first coordinate is natural-valued; the second is integer-valued. -/
abbrev Value : Bool → Type
  | false => ℕ
  | true => ℤ

/-- Signed laws: `3δ₀ - δ₁` on the natural coordinate,
and `2δ₋₂ - δ₇` on the integer coordinate. -/
noncomputable def signed : ∀ k, Distribution (Value k)
  | false => Finsupp.single 0 3 - Finsupp.single 1 1
  | true => Finsupp.single (-2) 2 - Finsupp.single 7 1

/-- Fix the natural coordinate to `9`, outside its original support. -/
def pin : ∀ k, Option (Value k)
  | false => some 9
  | true => none

/-- The heterogeneous tuple with coordinates `n` and `z`. -/
def row (n : ℕ) (z : ℤ) : ∀ k, Value k
  | false => n
  | true => z

example : signed false 9 = 0 ∧ pinnedProduct signed pin (row 9 7) = -1 := by
  norm_num [signed, pin, row, pinnedProduct, piDep_apply, Fintype.prod_bool,
    Finsupp.single_apply]

/-- Pinning one coordinate preserves the signed mass at the other one. -/
example : pinnedProduct signed pin (row 9 (-2)) = 2 := by
  norm_num [signed, pin, row, pinnedProduct, piDep_apply, Fintype.prod_bool,
    Finsupp.single_apply]

/-- Every supported tuple has the prescribed value, including tuples with negative mass. -/
example {f : ∀ k, Value k} (supported : f ∈ (pinnedProduct signed pin).support) :
    f false = 9 :=
  pinnedProduct_apply_eq_of_pin signed pin false 9 rfl supported

/-- A biased natural coordinate and a deterministic integer coordinate. -/
noncomputable def probabilities : ∀ k, ProbDist (Value k)
  | false => ConditioningTests.biased
  | true => ProbDist.single (-4)

/-- Fix the integer coordinate to `12`, leaving the biased coordinate to be sampled. -/
def integerPin : ∀ k, Option (Value k)
  | false => none
  | true => some 12

example : (ProbDist.pinnedProduct probabilities integerPin) (row 1 12) = 1 / 3 := by
  norm_num [ProbDist.pinnedProduct_val, pinnedProduct, piDep_apply, Fintype.prod_bool,
    probabilities, integerPin, row, ConditioningTests.biased, Finsupp.single_apply]

/-- Observe the fresh nonuniform coordinate, then retain precisely that value in the table. -/
example :
    fTransform (fun f : ∀ k, Value k => (f, f false))
        (ProbDist.pinnedProduct probabilities integerPin).1 =
      bindK ConditioningTests.biased.1 (fun n =>
        fTransform (fun f : ∀ k, Value k => (f, n))
          (ProbDist.pinnedProduct probabilities
            (Function.update integerPin false (some n))).1) := by
  simpa only [ProbDist.pinnedProduct_val, integerPin, Option.elim_none, probabilities]
    using fTransform_pinnedProduct_apply (fun k => (probabilities k).1) integerPin false

example : ProbDist.pinnedProduct probabilities (fun _ => none) = ProbDist.piDep probabilities :=
  ProbDist.pinnedProduct_none probabilities

#print axioms pinnedProduct_update
#print axioms pinnedProduct_apply_eq_of_pin
#print axioms pinnedProduct_eq_bindK_update
#print axioms fTransform_pinnedProduct_apply
#print axioms ProbDist.pinnedProduct

end Tests.PinnedProduct

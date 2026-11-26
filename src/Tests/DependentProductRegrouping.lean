module

public import Probability.Kernel
public import Mathlib.Tactic.NormNum

/-!
# Regrouping dependent independent tables

The first group is empty. The second group contains a natural-number outcome and a bit.
Uncurrying preserves their full joint law, for normalized and signed coordinate laws.
-/

@[expose] public section

namespace Probability.Distribution.DependentProductRegroupingTests

/-- `false` indexes no entries; `true` indexes the two entries `false, true`. -/
def groupIndex : Bool → Type
  | false => Empty
  | true => Bool

instance (k : Bool) : Fintype (groupIndex k) := by
  cases k <;> dsimp only [groupIndex] <;> infer_instance

/-- The populated group has a natural-number entry and a bit entry. -/
def outcome : (k : Bool) → groupIndex k → Type
  | false, e => nomatch e
  | true, false => ℕ
  | true, true => Bool

/-- A nonuniform law on the infinite carrier `ℕ`: masses `1/3, 2/3` at `7, 9`. -/
noncomputable def numberLaw : ProbDist ℕ :=
  ⟨Finsupp.single 7 (1 / 3) + Finsupp.single 9 (2 / 3), by
    constructor
    · intro n
      simp only [Finsupp.add_apply, Finsupp.single_apply]
      split <;> split <;> norm_num
    · norm_num only [weight_add, weight_single]⟩

/-- The populated group samples `numberLaw` and an independent uniform bit. -/
noncomputable def coordinateLaw : (k : Bool) → (l : groupIndex k) → ProbDist (outcome k l)
  | false, e => nomatch e
  | true, false => numberLaw
  | true, true => 𝒰[Bool]

/-- Regroup the full normalized joint law using only the public map equation. -/
example :
    (ProbDist.piDep fun k => ProbDist.piDep (coordinateLaw k)).map
        (Equiv.piCurry outcome).symm =
      ProbDist.piDep (fun p : Σ k, groupIndex k => coordinateLaw p.1 p.2) :=
  ProbDist.map_piDep_uncurry coordinateLaw

/-- The signed variant replaces the number law by `-2 δ₇ + 4 δ₉`, of total weight two. -/
noncomputable def signedCoordinateLaw :
    (k : Bool) → (l : groupIndex k) → Distribution (outcome k l)
  | false, e => nomatch e
  | true, false => Finsupp.single (7 : ℕ) (-2) + Finsupp.single (9 : ℕ) 4
  | true, true => (𝒰[Bool]).1

example :
    fTransform (Equiv.piCurry outcome).symm (piDep fun k => piDep (signedCoordinateLaw k)) =
      piDep (fun p : Σ k, groupIndex k => signedCoordinateLaw p.1 p.2) :=
  fTransform_piDep_uncurry signedCoordinateLaw

/-- The outer indices, inner indices and infinite outcomes can occupy distinct universes. -/
example :
    fTransform (Equiv.piCurry fun _ : ULift.{1} Unit => fun _ : ULift.{2} Unit =>
        ULift.{3} ℕ).symm
      (piDep fun _ : ULift.{1} Unit => piDep fun _ : ULift.{2} Unit =>
        Finsupp.single (⟨7⟩ : ULift.{3} ℕ) (-2 : ℝ)) =
      piDep (fun _ : Σ _ : ULift.{1} Unit, ULift.{2} Unit =>
        Finsupp.single (⟨7⟩ : ULift.{3} ℕ) (-2 : ℝ)) :=
  fTransform_piDep_uncurry _

#print axioms fTransform_piDep_uncurry
#print axioms ProbDist.map_piDep_uncurry

end Probability.Distribution.DependentProductRegroupingTests

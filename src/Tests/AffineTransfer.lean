module

public import Probability.AffineEvaluation
public import Mathlib.Algebra.Field.ZMod

/-!
# Affine transfer with a correlated collision outcome

The reference outcome is a uniform bit. At secret zero the actual law instead always
returns `true`; elsewhere it is unchanged. The expressions `0` and `x` collide exactly
where the law changes. The resulting guessing bound is `2/3` over `ZMod 3`.
-/

@[expose] public section

namespace Probability.Distribution.AffineTransferTests

-- `F` carries secrets; a bit is the experiment's output.
variable {F : Type*} [Field F] [DecidableEq F]

/-- Return `true` at secret zero; otherwise sample an independent uniform bit. -/
noncomputable def actual (x : F) : ProbDist Bool :=
  if x = 0 then ProbDist.single true else 𝒰[Bool]

/-- Every outcome carries the two affine expressions `0` and `x`. -/
def expressions (_ : Bool) : Finset (F × F) := {(0, 0), (1, 0)}

/-- The returned bit selects candidate zero on `true` and candidate one on `false`. -/
def candidate (b : Bool) : F := if b then 0 else 1

lemma agrees_of_injective (x : F) (b : Bool)
    (injective : Set.InjOn (fun c : F × F => c.1 * x + c.2)
      (expressions (F := F) b : Set (F × F))) : (actual x).1 b = (𝒰[Bool]).1 b := by
  by_cases hx : x = 0
  · subst x
    have equal := injective
      (x₁ := (0, 0)) (Finset.mem_insert_self _ _)
      (x₂ := (1, 0)) (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      (by simp only [mul_zero, add_zero])
    exact (zero_ne_one (congrArg Prod.fst equal)).elim
  · simp only [actual, hx, ite_false]

/-- At the collision secret, the actual outcome law really differs from the reference law. -/
example : actual (0 : F) ≠ 𝒰[Bool] := by
  intro equal
  have atom := congrArg (fun μ : ProbDist Bool => μ.1 true) equal
  norm_num [actual, ProbDist.single, ProbDist.uniform, uniform_apply] at atom

/-- The transfer result gives a useful bound even though the law changes on collisions. -/
example :
    (uniform (ZMod 3)).expect (fun x => (actual x).1.mass
      (fun b => x = candidate b)) ≤ 2 / 3 := by
  have bound := expect_mass_le_of_affine_injOn_eq 𝒰[Bool]
    (actual (F := ZMod 3)) expressions candidate
    (fun x b => x = candidate b) (fun _ _ h => h) agrees_of_injective
    (M := 2) (fun _ _ => Finset.card_le_two)
  norm_num only [Nat.choose_self, Nat.cast_one, ZMod.card] at bound
  exact bound

#print axioms expect_mass_le_of_affine_injOn_eq

end Probability.Distribution.AffineTransferTests

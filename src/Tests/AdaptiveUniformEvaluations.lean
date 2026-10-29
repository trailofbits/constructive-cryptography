import Probability.Counting

/-!
# Reply-dependent fresh coordinates

Tests of `uniform_mass_adaptive_eval_eq_mul`: for a uniform table `F`, base coordinates
`base`, reveal `b = F ∘ base`, and a batch `next b` selected from that reveal,

```text
Pr[good(b) ∧ F ∘ next(b) = values] = Pr[good(b)] · (1/|Y|)^|I|
```

whenever `Sum.elim base (next b)` is injective on `good b`.

## Cases

* one selected coordinate on `Fin 3 → Bool`, fresh for every reveal: mass `1/2`
* reading coordinate `0` twice: the freshness hypothesis fails
* two selected coordinates on `Fin 4 → Bool`, fresh only on `good`: mass `1/2 · (1/2)^2 = 1/8`
* outside `good`, the selected batch repeats coordinate `0`
* an empty good event with repeated base queries: mass `0`, no base injectivity needed
* four independent universes for base indices, outputs, selected indices and coordinates
-/

namespace Probability.Counting.Tests

open Probability.Counting

/-- Base coordinate of the one-output test: `adaptiveBase () = 0` in a table `Fin 3 → Bool`. -/
def adaptiveBase : Unit → Fin 3 := fun _ => 0

/-- Selected coordinate: `adaptiveNext b () = if b () then 1 else 2`, never the base `0`. -/
def adaptiveNext : (Unit → Bool) → Unit → Fin 3 := fun b _ => if b () then 1 else 2

/-- With `good = True`, `Pr[F(next(F(0))) = true] = Pr[True] · (1/2)^1 = 1/2`. -/
example : (Distribution.uniform (Fin 3 → Bool)).mass (fun f =>
    f (adaptiveNext (fun _ => f (adaptiveBase ())) ()) = true) = (1 / 2 : ℝ) := by
  -- Freshness for every reveal: the coordinates are `0` and `1` or `2`.
  have hfresh (b : Unit → Bool) :
      Function.Injective (Sum.elim adaptiveBase (adaptiveNext b)) := by
    refine Sum.elim_injective.mpr ⟨?_, ?_, ?_⟩
    · exact fun _ _ _ => Subsingleton.elim _ _
    · exact fun _ _ _ => Subsingleton.elim _ _
    · intro u v
      change (0 : Fin 3) ≠ (if b () then 1 else 2)
      split_ifs <;> simp
  -- The adaptive law with the trivial good event and selected reply `true`.
  have h := uniform_mass_adaptive_eval_eq_mul adaptiveBase adaptiveNext
    (fun _ => True) (fun b _ => hfresh b) (fun _ => true)
  -- A `Unit`-indexed reply tuple is its single reply.
  have he (f : Fin 3 → Bool) :
      ((fun i : Unit => f (adaptiveNext (fun b => f (adaptiveBase b)) i)) =
        (fun _ => true)) ↔
        f (adaptiveNext (fun b => f (adaptiveBase b)) ()) = true := by
    simp only [funext_iff, Unique.forall_iff]
  -- `Pr[True]` is the total weight `1` of the uniform law.
  simp only [true_and] at h
  rw [Distribution.mass_congr _ he, Distribution.mass_true,
    Distribution.weight_uniform] at h
  simpa using h

/-- Repeat counterexample: base and selected coordinates both `0`, so `Sum.elim` is not
injective and the adaptive law does not apply. -/
example : ¬ Function.Injective
    (Sum.elim (fun _ : Unit => (0 : Fin 3)) (fun _ : Unit => (0 : Fin 3))) := by
  intro h
  exact ((Sum.elim_injective.mp h).2.2 () ()) rfl

/-- Base coordinate of the two-output test: `adaptiveGoodBase () = 0` in a table
`Fin 4 → Bool`. -/
def adaptiveGoodBase : Unit → Fin 4 := fun _ => 0

/-- Selected batch indexed by `Bool`: `next b false = if b () then 1 else 0` and
`next b true = 3`. Both coordinates come from the one reveal `b = F(0)`. -/
def adaptiveGoodNext (b : Unit → Bool) : Bool → Fin 4 :=
  fun i => if i then 3 else if b () then 1 else 0

/-- Good event on the reveal: `good b ↔ b () = true`, i.e. `F(0) = true`. -/
def adaptiveGood (b : Unit → Bool) : Prop := b () = true

/-- Conditional freshness: on `good`, the combined coordinates are `0, 1, 3`, hence distinct. -/
lemma adaptiveGoodNext_fresh (b : Unit → Bool) (hb : adaptiveGood b) :
    Function.Injective (Sum.elim adaptiveGoodBase (adaptiveGoodNext b)) := by
  change b () = true at hb
  refine Sum.elim_injective.mpr ⟨?_, ?_, ?_⟩
  · exact fun _ _ _ => Subsingleton.elim _ _
  -- The selected coordinates `1` and `3` are distinct.
  · intro i j hij
    cases i <;> cases j <;> simp [adaptiveGoodNext, hb] at hij ⊢
  -- Neither selected coordinate is the base coordinate `0`.
  · intro u i
    cases i <;> simp [adaptiveGoodBase, adaptiveGoodNext, hb]

/-- Outside `good`, `F(0) = false` selects coordinate `0` again, so freshness fails there. -/
example : ¬ Function.Injective
    (Sum.elim adaptiveGoodBase (adaptiveGoodNext (fun _ => false))) := by
  intro h
  exact ((Sum.elim_injective.mp h).2.2 () false) rfl

/-- Prescribing the selected replies `id : Bool → Bool`, i.e. `F(1) = false` and
`F(3) = true` on `good`, gives `Pr[F(0) = true] · (1/2)^2 = 1/2 · 1/4 = 1/8`. -/
example : (Distribution.uniform (Fin 4 → Bool)).mass (fun f =>
    adaptiveGood (fun b => f (adaptiveGoodBase b)) ∧
      (fun i => f (adaptiveGoodNext (fun b => f (adaptiveGoodBase b)) i)) = id) =
        (1 / 8 : ℝ) := by
  -- `Pr[F(0) = true] = 1/2`: one uniform evaluation at a single coordinate.
  have hgood : (Distribution.uniform (Fin 4 → Bool)).mass
      (fun f => adaptiveGood (fun b => f (adaptiveGoodBase b))) = (1 / 2 : ℝ) := by
    have h := uniform_mass_eval_eq adaptiveGoodBase
      (fun _ _ _ => Subsingleton.elim _ _) (fun _ => true)
    simpa only [adaptiveGood, funext_iff, Unique.forall_iff, Fintype.card_unit,
      Fintype.card_bool, Nat.cast_ofNat, pow_one] using h
  -- The adaptive law, then `1/2 · (1/2)^2 = 1/8`.
  rw [uniform_mass_adaptive_eval_eq_mul adaptiveGoodBase adaptiveGoodNext adaptiveGood
    adaptiveGoodNext_fresh id, hgood]
  norm_num

/-- Empty good event on `Bool → Bool` with base `false, false` (a repeat) and selected
coordinate `false`: freshness holds vacuously, and the law gives
`Pr[False ∧ F(false) = true] = Pr[False] · 1/2`, both sides `0`. No base injectivity is
needed. -/
example : (Distribution.uniform (Bool → Bool)).mass (fun f =>
    False ∧ (fun _ : Unit => f false) = (fun _ => true)) =
      (Distribution.uniform (Bool → Bool)).mass (fun _ => False) * (1 / 2 : ℝ) := by
  -- The adaptive law with `good = False`; `(1/|Bool|)^|Unit|` reduces to `1/2`.
  simpa only [Fintype.card_bool, Fintype.card_unit, Nat.cast_ofNat, pow_one] using
    uniform_mass_adaptive_eval_eq_mul (fun _ : Bool => false)
      (fun _ (_ : Unit) => false) (fun _ => False) (fun _ h => h.elim) (fun _ => true)

/-- The adaptive law with base indices, outputs, selected indices and table coordinates in four
independent universes (`3`, `2`, `4`, `1`). -/
example (base : ULift.{3} Unit → ULift.{1} (Fin 3))
    (next : (ULift.{3} Unit → ULift.{2} Bool) → ULift.{4} Unit → ULift.{1} (Fin 3))
    (good : (ULift.{3} Unit → ULift.{2} Bool) → Prop)
    (hfresh : ∀ b, good b → Function.Injective (Sum.elim base (next b)))
    (values : ULift.{4} Unit → ULift.{2} Bool) :
    (Distribution.uniform (ULift.{1} (Fin 3) → ULift.{2} Bool)).mass (fun f =>
      good (fun b => f (base b)) ∧ (fun i => f (next (fun b => f (base b)) i)) = values) =
        (Distribution.uniform (ULift.{1} (Fin 3) → ULift.{2} Bool)).mass
            (fun f => good (fun b => f (base b))) *
          (1 / (Fintype.card (ULift.{2} Bool) : ℝ)) ^ Fintype.card (ULift.{4} Unit) := by
  exact uniform_mass_adaptive_eval_eq_mul base next good hfresh values

#print axioms Probability.Counting.uniform_mass_adaptive_eval_eq_mul

end Probability.Counting.Tests

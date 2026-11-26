module

public import Probability.AffineEvaluation
public import Mathlib.Algebra.Field.ZMod
public import Tests.PolynomialEvaluation

/-!
# Affine collision and guessing checks

An empty expression set still allows one fixed guess with probability `1 / |F|`.
Repeating one coefficient pair creates no collision, and repeating a pair in a two-expression
list leaves the bound `1 / |F|`. The seed test uses a law on `ℕ`, so the averaging result
requires no finite seed type. A prime-field specialization checks the intended secret carrier.
-/

@[expose] public section

namespace Probability.Distribution.Tests

/-- A nonuniform law on the integers uses the same affine bound without a field structure. -/
example : biasedInteger.mass (fun x => x = 1) ≤ 2 / 5 := by
  have bound := mass_affine_eq_le biasedInteger biasedInteger_nonNeg
    (show (0 : ℝ) ≤ 2 / 5 by norm_num) biasedInteger_apply_le
    (c := ((1 : ℤ), 0)) (d := (0, 1)) (by
      intro equal
      have := congrArg Prod.fst equal
      norm_num at this)
  simpa only [affineEvaluation, one_mul, zero_add, zero_mul, add_zero] using bound

-- `F` is the finite field from which the hidden argument is sampled uniformly.
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- With no affine expressions, guessing `guess` succeeds with exactly one uniform atom. -/
example (guess : F) :
    (uniform F).mass (fun x => x = guess ∨
      ¬ Set.InjOn (affineEvaluation x) (∅ : Set (F × F))) =
        1 / (Fintype.card F : ℝ) := by
  simp only [Set.injOn_empty, not_true_eq_false, or_false]
  rw [mass_singleton, uniform_apply]

/-- The three occurrences of `c` describe one expression and cannot collide with each other. -/
example (c : F × F) :
    (uniform F).mass (fun x => ¬ Set.InjOn (affineEvaluation x)
      (([c, c, c].toFinset : Finset (F × F)) : Set (F × F))) = 0 := by
  classical
  apply mass_eq_zero_of_forall_not
  intro x collision
  apply collision
  simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
    Finset.pair_eq_singleton, Finset.coe_singleton, Set.injOn_singleton]

/-- Repeated coefficients do not enlarge the pair count of two distinct expressions. -/
example (c d : F × F) (hne : c ≠ d) :
    (uniform F).mass (fun x => ¬ Set.InjOn (affineEvaluation x)
      (([c, c, d].toFinset : Finset (F × F)) : Set (F × F))) ≤
        1 / (Fintype.card F : ℝ) := by
  classical
  have bound := uniform_mass_affine_not_injOn_le_choose [c, c, d].toFinset
  simpa only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty,
    Finset.insert_idem, Finset.card_pair hne, Nat.choose_self, Nat.cast_one] using bound

/-- A seed from an arbitrary law on `ℕ` selects two coefficients and its own guess. -/
example (μ : ProbDist ℕ) :
    (prodProbDist μ 𝒰[F]).1.mass (fun nx => nx.2 = (nx.1 : F) ∨
      ¬ Set.InjOn (affineEvaluation nx.2)
        ({((nx.1 : F), 0), ((nx.1 : F), 1)} : Set (F × F))) ≤
          2 / (Fintype.card F : ℝ) := by
  classical
  have bound := mass_prod_uniform_eq_or_affine_not_injOn_le μ
    (fun n => {((n : F), 0), ((n : F), 1)}) (fun n => (n : F))
    (M := 2) (fun _ _ => Finset.card_le_two)
  simpa only [Finset.coe_insert, Finset.coe_singleton, Nat.choose_self, Nat.cast_one,
    one_add_one_eq_two] using bound

/-- The collision bound specializes to `ZMod p`, with denominator the prime `p`. -/
example (p : ℕ) [Fact p.Prime] (s : Finset (ZMod p × ZMod p)) (guess : ZMod p) :
    (uniform (ZMod p)).mass (fun x => x = guess ∨
      ¬ Set.InjOn (affineEvaluation x) (s : Set _)) ≤
        (1 + (s.card.choose 2 : ℝ)) / p := by
  simpa only [ZMod.card] using uniform_mass_eq_or_affine_not_injOn_le s guess

#print axioms mass_prod_uniform_eq_or_affine_not_injOn_le
#print axioms mass_affine_eq_le
#print axioms mass_affine_not_injOn_le_choose

end Probability.Distribution.Tests

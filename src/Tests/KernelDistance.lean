module

public import Probability.StatisticalDistance

/-!
# Kernel distance bounds

A mixing law of mass two checks the unnormalized bound with signed conditional laws.
The normalized checks compose two kernel replacements and use a support-only error bound.
-/

@[expose] public section

namespace Probability.Tests.KernelDistance

open Distribution

/-- Mixing signed kernels at one input of weight two doubles their conditional distance. -/
example (K L : ℕ → Distribution (List ℕ)) :
    statDist (bindK (Finsupp.single 0 2) K) (bindK (Finsupp.single 0 2) L) ≤
      2 * statDist (K 0) (L 0) := by
  simpa only [expect, Finsupp.sum_single_index, zero_mul] using
    statDist_bindK_le_expect (Finsupp.single 0 2)
      (by intro n; simp only [Finsupp.single_apply]; split <;> norm_num) K L

/-- Two conditional replacements add their mean errors under the same retained first draw. -/
example (P : ProbDist ℕ) (K L M : ℕ → ProbDist (List ℕ))
    (ε η : ℕ → ℝ)
    (firstBound : ∀ n, statDist (K n).1 (L n).1 ≤ ε n)
    (secondBound : ∀ n, statDist (L n).1 (M n).1 ≤ η n) :
    statDist (P.bind K).1 (P.bind M).1 ≤ P.1.expect (ε + η) := by
  calc
    _ ≤ statDist (P.bind K).1 (P.bind L).1 + statDist (P.bind L).1 (P.bind M).1 :=
      statDist_triangle _ _ _
    _ ≤ P.1.expect ε + P.1.expect η := add_le_add
      ((statDist_bind_le_expect P K L).trans (expect_mono P.2.1 firstBound))
      ((statDist_bind_le_expect P L M).trans (expect_mono P.2.1 secondBound))
    _ = _ := (expect_add_right P.1 ε η).symm

/-- The off-support conditional laws need no error bound. -/
example (K L : ℕ → ProbDist (List ℕ)) {ε : ℝ}
    (bound : statDist (K 7).1 (L 7).1 ≤ ε) :
    statDist ((ProbDist.single 7).bind K).1 ((ProbDist.single 7).bind L).1 ≤ ε := by
  apply statDist_bind_le_of_forall_le
  intro n supported
  have hn : n = 7 := (Finsupp.mem_support_single n 7 (1 : ℝ)).mp supported |>.1
  subst n
  exact bound

/-- Unequal signed masses have directed distance one, whereas their half-L1 difference is `1/2`. -/
example :
    statDist (Finsupp.single () (-1) : Distribution Unit) (Finsupp.single () (-2)) = 1 ∧
      (∑ a : Unit, |(Finsupp.single () (-1) : Distribution Unit) a -
        Finsupp.single () (-2) a|) / 2 = (1 : ℝ) / 2 := by
  norm_num [statDist_eq_sum_univ, Finsupp.single_apply]

/-- A kernel of mass `1/2` contracts unequal signed input masses. -/
example :
    statDist (bindK (Finsupp.single () (-1)) (fun _ => Finsupp.single (0 : ℕ) (1 / 2)))
      (bindK (Finsupp.single () (-2)) (fun _ => Finsupp.single (0 : ℕ) (1 / 2))) ≤ 1 := by
  calc
    _ ≤ statDist (Finsupp.single () (-1)) (Finsupp.single () (-2)) :=
      statDist_bindK_le _ _ _
        (by intro a n; simp only [Finsupp.single_apply]; split <;> norm_num)
        (by intro a; norm_num)
    _ = 1 := by norm_num [statDist_eq_sum_univ, Finsupp.single_apply]

/-- Changing both the first law and the conditional law adds their two errors. -/
example (P Q : ProbDist ℕ) (K L : ℕ → ProbDist (List ℕ)) {ε : ℝ}
    (bound : ∀ n ∈ Q.1.support, statDist (K n).1 (L n).1 ≤ ε) :
    statDist (P.bind K).1 (Q.bind L).1 ≤ statDist P.1 Q.1 + ε :=
  (statDist_triangle _ (Q.bind K).1 _).trans
    (add_le_add (statDist_bind_le P Q K) (statDist_bind_le_of_forall_le Q K L bound))

#print axioms expect_sub_expect_le_mul_statDist_of_nonneg
#print axioms statDist_bindK_le
#print axioms statDist_bind_le
#print axioms statDist_bindK_le_expect
#print axioms statDist_bind_le_expect
#print axioms statDist_bind_le_of_forall_le

end Probability.Tests.KernelDistance

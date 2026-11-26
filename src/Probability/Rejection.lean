module

public import Probability.Conditioning

/-!
# Truncated rejection sampling

`ProbDist.rejection P E fallback T` returns the first draw satisfying `E` in `T` independent
trials from `P`, or draws from `fallback` when every trial fails. For [1, p. 19]'s instruction
"accept the sample if it is in X⊥", use `E` for membership and a point law for the fixed default.

`rejection_eq` gives the exact law, with `θ = P(E)` and `C = P.conditionOn E fallback`:

```text
rejection = (1 − (1−θ)^T) • C + (1−θ)^T • fallback.
```

`mem_support_rejection` keeps accepted trial outcomes and fallback outcomes distinct.
The zero- and full-acceptance equations specialize the mixture at the two boundary masses.

## References

1. G. Herold, D. Khovratovich, M. Kudinov, S. Tessaro, B. Wagner. *Aborting Random Oracles:
   How to Build them, How to Use them*. July 17, 2026. Cryptology ePrint Archive 2026/016.
-/

@[expose] public section

namespace Probability.Distribution.ProbDist

-- `A` carries outcomes; all laws have finite support, even when `A` is infinite.
variable {A : Type*}
-- `P` is drawn freshly at every trial; `E` selects accepted outcomes.
variable (P : ProbDist A) (E : A → Prop) [DecidablePred E]
-- `fallback` is drawn only after the selected number of trials all fail.
variable (fallback : ProbDist A)

/-- Return the first accepted draw within `T` independent trials; at exhaustion use `fallback`.
The recurrence is `R₀ = fallback`, `Rₜ₊₁ = P.bind (a ↦ if E a then δₐ else Rₜ)`. -/
noncomputable def rejection : ℕ → ProbDist A
  | 0 => fallback
  | T + 1 => P.bind (fun a => if E a then single a else rejection T)

/-- Zero trials draw directly from the fallback. -/
@[simp] lemma rejection_zero : rejection P E fallback 0 = fallback := rfl

/-- Every returned outcome is an accepted trial outcome or a fallback outcome. -/
lemma mem_support_rejection
    -- `T` counts trials; `a` is a possible returned outcome.
    (T : ℕ) {a : A} (ha : a ∈ (rejection P E fallback T).1.support) :
    (a ∈ P.1.support ∧ E a) ∨ a ∈ fallback.1.support := by
  induction T with
  | zero => exact Or.inr ha
  | succ T ih =>
    obtain ⟨x, hx, hout⟩ := mem_support_bindK ha
    change a ∈ (if E x then single x else rejection P E fallback T).1.support at hout
    -- A successful trial returns its sampled value; otherwise the remaining trials apply.
    split_ifs at hout with accepted
    · have same : a = x := by
        simpa only [single, Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hout
      exact Or.inl (same.symm ▸ ⟨hx, accepted⟩)
    · exact ih hout

/-- If the fallback is supported on `E`, every returned outcome also satisfies `E`. -/
lemma rejection_support
    -- `hF` makes fallback outcomes accepted as well; `T` may be zero.
    (T : ℕ) (hF : ∀ a ∈ fallback.1.support, E a) :
    ∀ a ∈ (rejection P E fallback T).1.support, E a := by
  intro a ha
  exact (mem_support_rejection P E fallback T ha).elim And.right (hF a)

/-- The exact law has conditional weight `1 − (1−P(E))^T` and fallback weight `(1−P(E))^T`.
The same equation includes zero acceptance mass and zero trials. -/
theorem rejection_eq
    -- `T` is the number of independent trials; conditioning uses the same explicit fallback.
    (T : ℕ) :
    (rejection P E fallback T).1 =
      (1 - (1 - P.1.mass E) ^ T) • (P.conditionOn E fallback).1 +
        (1 - P.1.mass E) ^ T • fallback.1 := by
  have complement : P.1.mass (fun a => ¬ E a) = 1 - P.1.mass E := by
    have partition := mass_add_compl P.1 E
    rw [P.2.2] at partition
    linarith
  induction T with
  | zero => simp only [rejection, pow_zero, sub_self, zero_smul, one_smul, zero_add]
  | succ T ih =>
    -- One trial retains accepted mass and scales the remaining mixture by the failure mass.
    change bindK P.1 (fun a => (if E a then single a else rejection P E fallback T).1) = _
    simp only [apply_ite Subtype.val, single]
    rw [bindK_ite_single, complement, ih, ← mass_smul_conditionOn P E fallback]
    -- Collect the two conditional contributions; the fallback requires one more failed trial.
    rw [smul_add, smul_smul, smul_smul, ← add_assoc, ← add_smul]
    congr 1 <;> congr 1 <;> rw [pow_succ] <;> ring

/-- Zero acceptance mass returns the fallback at every trial count. -/
lemma rejection_of_mass_zero
    -- `hE` says no trial can succeed; `T` remains arbitrary.
    (T : ℕ) (hE : P.1.mass E = 0) : rejection P E fallback T = fallback := by
  apply Subtype.ext
  rw [rejection_eq, hE]
  simp only [sub_zero, one_pow, sub_self, zero_smul, one_smul, zero_add]

/-- At acceptance mass one, any positive trial count returns the conditional law. -/
lemma rejection_of_mass_one
    -- `hE` says a first trial succeeds with certainty.
    (T : ℕ) (hE : P.1.mass E = 1) :
    rejection P E fallback (T + 1) = P.conditionOn E fallback := by
  apply Subtype.ext
  rw [rejection_eq, hE]
  simp only [sub_self, pow_succ, mul_zero, sub_zero, one_smul, zero_smul, add_zero]

end Probability.Distribution.ProbDist

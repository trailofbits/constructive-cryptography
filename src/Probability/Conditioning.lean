module

public import Probability.Kernel
public import Probability.Lift

/-!
# Conditional laws on finite supports

An observation partitions a finitely supported law into fibers. Normalizing each fiber
and mixing with its mass recovers the original law, including zero-mass fibers. The explicit
fallback of `normalizeOr` is multiplied by zero there. `ProbDist.uniformOn E fallback` names
the normalized uniform restriction to an event, with the explicit fallback at an empty event.

`bindK_fTransform_normalizeOr_restrict` gives this disintegration before normalization;
`normalizeOr_eq_bindK_restrict` gives it after normalization.
`ProbDist.eq_uniformOn_of_constant` identifies a conditional law from
its support and equal point masses; `fTransform_uniform_restrict_of_equiv` supplies those
equalities when a sample-space symmetry preserves the event. These identities express a
"conditional probability distribution" [1, §3.6.1, p. 65] using the existing finite-support
restrictions and normalized laws.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Probability.Distribution

-- `A` carries latent outcomes; `B` carries observed values. Both types may be infinite.
variable {A B : Type*}

/-- Uniform on the event `E`, with `fallback` at an empty event. Its mass on a nonempty
`E` is `1 / |E|` at each retained outcome and zero elsewhere. -/
noncomputable def ProbDist.uniformOn
    -- `A` is a finite nonempty alphabet; `E` selects the allowed outcomes.
    [Fintype A] [Nonempty A] (E : A → Prop)
    -- `fallback` totalizes the law when the allowed set is empty.
    (fallback : ProbDist A) : ProbDist A :=
  ((Distribution.uniform A).restrict E).normalizeOr (uniform_nonNeg.restrict E) fallback

/-- A nonempty event has positive mass under a finite uniform law. -/
lemma weight_restrict_uniform_ne_zero
    -- `E` is an event in the finite uniform alphabet; `hE` supplies a retained atom.
    [Fintype A] [Nonempty A] (E : A → Prop) (hE : ∃ a, E a) :
    ((Distribution.uniform A).restrict E).weight ≠ 0 := by
  obtain ⟨a, ha⟩ := hE
  apply weight_ne_zero_of_apply_ne_zero _ (uniform_nonNeg.restrict E) (a := a)
  rw [restrict_apply, ite_eq_left ha, uniform_apply]
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

/-- Conditioning a uniform finite law on a nonempty event keeps exactly that event. -/
lemma ProbDist.mem_support_uniformOn_iff
    -- `hE` makes the restriction to `E` nonzero, so `fallback` does not affect the atom `a`.
    [Fintype A] [Nonempty A] (E : A → Prop) (hE : ∃ a, E a)
    (fallback : ProbDist A) (a : A) :
    a ∈ (uniformOn E fallback).1.support ↔ E a := by
  unfold uniformOn
  rw [mem_support_normalizeOr_iff _ _ _ (weight_restrict_uniform_ne_zero E hE)]
  simp only [Finsupp.mem_support_iff, restrict_apply]
  split_ifs with ha
  · exact iff_of_true (one_div_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) ha
  · exact iff_of_false (not_ne_iff.mpr rfl) ha

/-- A symmetry of an event preserves its restricted uniform law. -/
lemma fTransform_uniform_restrict_of_equiv
    -- `e` permutes the uniform alphabet; `he` says precisely that it preserves the event `E`.
    [Fintype A] [Nonempty A] (E : A → Prop) (e : A ≃ A)
    (he : ∀ a, E (e a) ↔ E a) :
    fTransform e ((uniform A).restrict E) = (uniform A).restrict E := by
  calc
    _ = (fTransform e (uniform A)).restrict E := by
      rw [restrict_fTransform]
      exact congrArg (fTransform e) (restrict_congr _ fun a => (he a).symm)
    _ = _ := by rw [fTransform_equiv_uniform]

/-- A normalized law constant on an event and zero outside it is its uniform restriction. -/
lemma ProbDist.eq_uniformOn_of_constant
    -- `μ` is the candidate probability law on finite `A`; `E` selects its possible outcomes.
    [Fintype A] [Nonempty A] (μ : ProbDist A) (E : A → Prop)
    -- `hsupport` confines every possible draw to `E`, so this event is nonempty.
    (hsupport : ∀ a ∈ μ.1.support, E a)
    -- `hconstant` equates all retained point masses; `fallback` cannot affect nonempty `E`.
    (hconstant : ∀ a, E a → ∀ b, E b → μ a = μ b) (fallback : ProbDist A) :
    μ = uniformOn E fallback := by
  classical
  have hE : ∃ a, E a := by
    have hne : μ.1 ≠ 0 := by
      intro hz
      have hw := μ.2.weight_eq
      rw [hz] at hw
      change (0 : ℝ) = 1 at hw
      exact zero_ne_one hw
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr hne
    exact ⟨a, hsupport a ha⟩
  let ν := uniformOn E fallback
  have hv (a : A) : ν.1 a =
      ((Distribution.uniform A).restrict E).weight⁻¹ *
        (if E a then (1 : ℝ) / Fintype.card A else 0) := by
    change (((Distribution.uniform A).restrict E).normalizeOr _ _).1 a = _
    rw [normalizeOr_val_of_weight_ne_zero _ _ _ (weight_restrict_uniform_ne_zero E hE)]
    simp only [Finsupp.smul_apply, smul_eq_mul, restrict_apply, uniform_apply]
  have hz (a : A) (ha : ¬E a) : μ.1 a = 0 :=
    Finsupp.notMem_support_iff.mp (fun hm => ha (hsupport a hm))
  apply Subtype.ext
  ext a
  by_cases ha : E a
  · -- Equal masses on `E` and zero masses elsewhere determine the normalization constant.
    have cross (b : A) : μ.1 a * ν.1 b = ν.1 a * μ.1 b := by
      by_cases hb : E b
      · rw [hconstant a ha b hb, hv a, hv b, ite_eq_left ha, ite_eq_left hb, mul_comm]
      · rw [hz b hb, hv b, ite_eq_right hb, mul_zero, mul_zero, mul_zero]
    calc
      μ.1 a = μ.1 a * ν.1.weight := by rw [ν.2.weight_eq, mul_one]
      _ = ν.1 a * μ.1.weight := by
        rw [weight_eq_sum, weight_eq_sum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => cross b
      _ = ν.1 a := by rw [μ.2.weight_eq, mul_one]
  · rw [hz a ha, hv a, ite_eq_right ha, mul_zero]

/-- A symmetry of a nonempty event preserves its normalized uniform law. -/
lemma ProbDist.map_uniformOn_of_equiv
    -- `hE` excludes the fallback; `he` says the alphabet permutation `e` preserves `E`.
    [Fintype A] [Nonempty A] (E : A → Prop) (hE : ∃ a, E a)
    (fallback : ProbDist A) (e : A ≃ A) (he : ∀ a, E (e a) ↔ E a) :
    (uniformOn E fallback).map e = uniformOn E fallback := by
  apply Subtype.ext
  simp only [map_val, uniformOn, normalizeOr_val_of_weight_ne_zero _ _ _
    (weight_restrict_uniform_ne_zero E hE), fTransform_smul,
    fTransform_uniform_restrict_of_equiv E e he]

/-- Allowing every outcome gives the original uniform law. -/
lemma ProbDist.uniformOn_of_forall
    -- `E` retains the whole finite alphabet by `hE`; `fallback` is therefore unused.
    [Fintype A] [Nonempty A] (E : A → Prop) (hE : ∀ a, E a) (fallback : ProbDist A) :
    uniformOn E fallback = 𝒰[A] := by
  apply (eq_uniformOn_of_constant 𝒰[A] E (fun a _ => hE a) _ fallback).symm
  exact fun a _ b _ => by simp only [uniform, uniform_apply]

/-- An empty allowed set returns exactly the supplied fallback. -/
lemma ProbDist.uniformOn_of_forall_not
    -- `hE` excludes every outcome from `E`; its restricted law has zero weight.
    [Fintype A] [Nonempty A] (E : A → Prop) (hE : ∀ a, ¬ E a) (fallback : ProbDist A) :
    uniformOn E fallback = fallback := by
  have hz : (Distribution.uniform A).restrict E = 0 := by
    rw [restrict_congr _ (fun a => iff_false_intro (hE a)), restrict_false]
  simp only [uniformOn, hz, normalizeOr, show (0 : Distribution A).weight = 0 from rfl,
    dite_true]

/-- Recover a law by observing `f` and then drawing from its normalized fiber. -/
lemma bindK_fTransform_normalizeOr_restrict
    -- `f` observes the latent outcome drawn from nonnegative `μ`; no finite alphabet is needed.
    (μ : Distribution A) (hμ : μ.NonNeg) (f : A → B)
    -- `fallback b` fills the fiber `f = b` when its mass is zero.
    (fallback : B → ProbDist A) :
    bindK (fTransform f μ)
      (fun b => ((μ.restrict (fun a => f a = b)).normalizeOr
        (hμ.restrict _) (fallback b)).1) = μ := by
  classical
  ext a
  rw [bindK_apply, Finsupp.sum]
  -- Each observation mass times its conditional law is exactly the restricted original law.
  simp_rw [fTransform_apply_eq_mass, ← weight_restrict μ]
  have scale (b : B) := congrArg (fun ν : Distribution A => ν a)
    (weight_smul_normalizeOr (μ.restrict (fun a => f a = b)) (hμ.restrict _) (fallback b))
  simp only [Finsupp.smul_apply, smul_eq_mul] at scale
  simp_rw [scale, restrict_apply]
  -- The fibers partition the outcome space; precisely the fiber `f a` retains `a`.
  rw [Finset.sum_eq_single (f a)]
  · exact ite_eq_left rfl
  · intro b _ hb
    exact ite_eq_right (Ne.symm hb)
  · intro h
    rw [ite_eq_left rfl]
    -- An observation outside the pushforward support has a zero-mass fiber.
    apply le_antisymm _ (hμ a)
    calc
      μ a ≤ μ.mass (fun a' => f a' = f a) := apply_le_mass hμ rfl
      _ = 0 := by
        rw [← fTransform_apply_eq_mass]
        exact Finsupp.notMem_support_iff.mp h

/-- Normalizing before revealing `f` gives the same mixture of normalized original fibers. -/
lemma normalizeOr_eq_bindK_restrict
    -- `μ` is nonnegative by `hμ`; `fallback` fills each zero-mass observation fiber.
    (μ : Distribution A) (hμ : μ.NonNeg) (fallback : ProbDist A)
    -- `hw` permits normalization of `μ`; `f` is the value revealed before the conditional draw.
    (hw : μ.weight ≠ 0) (f : A → B) :
    (μ.normalizeOr hμ fallback).1 =
      bindK (fTransform f (μ.normalizeOr hμ fallback).1)
        (fun b => ((μ.restrict (fun a => f a = b)).normalizeOr
          (hμ.restrict _) fallback).1) := by
  rw [normalizeOr_val_of_weight_ne_zero μ hμ fallback hw, fTransform_smul]
  -- The common scalar normalization factors out of the mixture.
  rw [show bindK (μ.weight⁻¹ • fTransform f μ) _ =
      μ.weight⁻¹ • bindK (fTransform f μ) _ from map_smul _ _ _]
  rw [bindK_fTransform_normalizeOr_restrict _ hμ]

end Probability.Distribution

import Probability.Kernel

/-!
# Probability laws on a chosen finite support

A probability law `P` on a possibly infinite type `A` whose support lies in a finite set
`s : Finset A` is re-indexed by the subtype `s` without changing any mass:
`onFinset P s hs ⟨a, ha⟩ = P a`, and decoding by `Subtype.val` returns `P`. Several laws share
one finite alphabet when `s` contains the union of their supports.

## Main definitions

* `ProbDist.onFinset P s hs`: `P` as a law on the finite alphabet `s`

## Main results

* `ProbDist.map_onFinset_val`: `val_* (onFinset P s hs) = P`, an exact presentation
-/

namespace Probability.Distribution.ProbDist

-- `A`: the outcome type of the law; it need not be finite.
variable {A : Type*}

open Classical in
/-- `P` re-indexed by the finite alphabet `s`: `onFinset P s hs ⟨a, ha⟩ = P a`. Its weight is
`∑_{a ∈ s} P a = 1`, because `hs` keeps every positive-mass outcome inside `s`. -/
noncomputable def onFinset
    -- `P : ProbDist A`: a probability law on `A`.
    (P : ProbDist A)
    -- `s : Finset A`: the chosen finite alphabet; `hs`: it contains the support of `P`.
    (s : Finset A) (hs : P.1.support ⊆ s) :
    ProbDist s :=
  ⟨ofFiniteMassFunction (fun a : s => P.1 a.1), by
    -- The masses are those of `P`, hence nonnegative.
    refine ⟨fun a => P.2.1 a.1, ?_⟩
    -- `∑_{a ∈ s} P a = ∑_{a ∈ supp P} P a = 1`, since `supp P ⊆ s`.
    rw [weight_ofFiniteMassFunction, ← P.2.weight_eq,
      weight_eq_sum_of_support_subset P.1 hs]
    exact Finset.sum_attach s (fun a => P.1 a)⟩

/-- Decoding the finite alphabet is an exact presentation of `P`:
`val_* (onFinset P s hs) = P`. -/
lemma map_onFinset_val (P : ProbDist A) (s : Finset A) (hs : P.1.support ⊆ s) :
    ProbDist.map Subtype.val (onFinset P s hs) = P := by
  classical
  -- Compare the masses at each `a : A`.
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ s
  · -- `a ∈ s`: `val` is injective, so the decoded mass at `a` is the mass of `⟨a, ha⟩`, `P a`.
    exact fTransform_injective_apply (onFinset P s hs).1 Subtype.val
      Subtype.val_injective ⟨a, ha⟩
  · -- `a ∉ s`: `P a = 0` because `supp P ⊆ s`, and no element of `s` decodes to `a`.
    have hzero : P.1 a = 0 := Finsupp.notMem_support_iff.mp (fun h => ha (hs h))
    rw [hzero]
    exact fTransform_apply_of_forall_ne (onFinset P s hs).1 Subtype.val a
      (fun x he => ha (he ▸ x.2))

end Probability.Distribution.ProbDist

module

public import Probability.Counting

/-!
# Restriction of a uniform permutation

`permutation_restriction_uniform` gives the uniform law on injections at distinct inputs.
`permutation_constraints_mass` evaluates that law at a prescribed tuple. A repeated input
in `permutation_agreement_mass` contributes a single factor.
-/

@[expose] public section

namespace Probability.Counting

noncomputable section

-- `J` indexes distinct prescribed inputs of the permuted alphabet `S`.
variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq S]

/-- Restriction `j ↦ π (x j)` of a permutation `π` of `S` to the distinct points `x : J ↪ S`. -/
def restrictPermutation (x : J ↪ S) (π : Equiv.Perm S) : J ↪ S :=
  x.trans π.toEmbedding

/-- Every injective output tuple has the same number of permutation completions: post-composing
with a permutation `σ` extending `y j ↦ z j` is a bijection between the two fibres. -/
lemma permutation_fiber_card_eq (x y z : J ↪ S) :
    (Finset.univ.filter (fun π : Equiv.Perm S => restrictPermutation x π = y)).card =
      (Finset.univ.filter (fun π : Equiv.Perm S => restrictPermutation x π = z)).card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair y z y.injective z.injective
  refine Finset.card_bij (fun π _ => π.trans σ) ?_ ?_ ?_
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
    ext j
    change σ (π (x j)) = z j
    have he : π (x j) = y j := DFunLike.congr_fun hπ j
    rw [he, hσ]
  · intro π _ ρ _ he
    ext s
    exact σ.injective (Equiv.congr_fun he s)
  · intro π hπ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    refine ⟨π.trans σ.symm, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      ext j
      change σ.symm (π (x j)) = y j
      have he : π (x j) = z j := DFunLike.congr_fun hπ j
      rw [he, ← hσ j, σ.symm_apply_apply]
    · ext s
      exact σ.apply_symm_apply (π s)

/-- A uniform permutation restricted to distinct points `x` is uniform on injective tuples:
`(restrictPermutation x)_* 𝒰(Perm S) = 𝒰(J ↪ S)`. -/
lemma permutation_restriction_uniform [Nonempty (J ↪ S)] (x : J ↪ S) :
    Distribution.fTransform (restrictPermutation x) (Distribution.uniform (Equiv.Perm S)) =
      Distribution.uniform (J ↪ S) := by
  classical
  apply Distribution.fTransform_uniform_eq_uniform_of_card_fiber_mul
  intro y
  -- The fibres partition the permutations and all have the same size.
  have htotal := Fintype.card_congr (Equiv.sigmaFiberEquiv (restrictPermutation x))
  rw [Fintype.card_sigma] at htotal
  simp only [Fintype.card_subtype] at htotal
  have hs : (∑ z : J ↪ S,
      (Finset.univ.filter (fun π : Equiv.Perm S => restrictPermutation x π = z)).card) =
      (Finset.univ.filter (fun π : Equiv.Perm S => restrictPermutation x π = y)).card *
        Fintype.card (J ↪ S) := by
    simp only [permutation_fiber_card_eq x _ y, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, mul_comm]
  exact hs.symm.trans htotal

/-- Prescribing distinct outputs `y j` at distinct inputs `x j` has probability
`1 / (|S|)_{|J|}`. All injective tuples are equally likely, and there are
`(|S|)_{|J|} = |S| (|S| - 1) ⋯ (|S| - |J| + 1)` such tuples. -/
theorem permutation_constraints_mass (x y : J ↪ S) :
    (Distribution.uniform (Equiv.Perm S)).mass (fun π => ∀ j, π (x j) = y j) =
      1 / ((Fintype.card S).descFactorial (Fintype.card J) : ℝ) := by
  classical
  let : Nonempty (J ↪ S) := ⟨x⟩
  -- Evaluate the uniform restricted law at the tuple `y`.
  have he := congrArg (fun μ : Distribution (J ↪ S) => μ y)
    (permutation_restriction_uniform x)
  rw [Distribution.fTransform_apply_eq_mass, Distribution.uniform_apply,
    Fintype.card_embedding_eq] at he
  rw [← he]
  apply Distribution.mass_congr
  intro π
  exact ⟨fun h => DFunLike.ext _ _ h, fun h j => DFunLike.congr_fun h j⟩

/-- Agreement with a reference permutation on a list of points: repeated observations of an
edge impose one constraint, so the falling factorial has one factor per distinct point. -/
theorem permutation_agreement_mass (reference : Equiv.Perm S) (points : List S) :
    (Distribution.uniform (Equiv.Perm S)).mass
      (fun π => ∀ x ∈ points, π x = reference x) =
        1 / ((Fintype.card S).descFactorial points.toFinset.card : ℝ) := by
  classical
  let inputs : points.toFinset ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  let outputs : points.toFinset ↪ S := inputs.trans reference.toEmbedding
  have hm := permutation_constraints_mass inputs outputs
  rw [Fintype.card_coe] at hm
  refine (Distribution.mass_congr _ (fun π => ?_)).trans hm
  constructor
  · intro h x
    exact h x.val (List.mem_toFinset.mp x.property)
  · intro h x hx
    exact h ⟨x, List.mem_toFinset.mpr hx⟩

end

end Probability.Counting

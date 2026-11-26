module

public import RandomSystems.Cumulative.CumulativeObservation
public import Probability.Kernel
public import RandomSystems.Cumulative.Conditional

/-!
# One-round observation kernels

`observationKernel R σ h` extends transcript `h` by the next query of `σ` and the conditional
reply of `R`. A stopped strategy retains `h`. Impossible or inadmissible histories use the
same point mass to define the kernel outside observed support.

`sLaw_succ_eq_bindK` identifies one more observation round with this kernel mixture.
Conditional normalization connects cumulative extension masses to the kernel's event masses.
-/

@[expose] public section

noncomputable section

namespace SystemAlgebra.RandomSystem

open Probability
open Probability.Distribution
open scoped BigOperators

variable {A B : Type} [Fintype A] [Fintype B] {D : Domain A B}

open Classical in
/-- The next transcript is `h ++ [(x,y)]` for the selected query and conditional reply;
a stopped or undefined interaction keeps `h`. -/
def observationKernel
    -- `R` is the resource; `σ` chooses queries from replies; `h` is the current transcript.
    (R : RandomSystem A B D) (σ : List B →. A) (h : List (A × B)) :
    ProbDist (List (A × B)) :=
  ((σ (h.map Prod.snd)).bind fun x =>
    (R.conditional h x).map fun replyLaw =>
      replyLaw.map (fun y => h ++ [(x, y)])).getOrElse (ProbDist.single h)

/-- A selected query with a defined conditional reply appends exactly that exchange. -/
lemma observationKernel_eq_map
    (R : RandomSystem A B D) (σ : List B →. A) (h : List (A × B)) {x : A}
    (query : x ∈ σ (h.map Prod.snd)) (defined : (R.conditional h x).Dom) :
    R.observationKernel σ h =
      ((R.conditional h x).get defined).map (fun y => h ++ [(x, y)]) := by
  classical
  have selected : ((R.conditional h x).get defined).map (fun y => h ++ [(x, y)]) ∈
      (σ (h.map Prod.snd)).bind (fun x => (R.conditional h x).map
        (fun replyLaw => replyLaw.map (fun y => h ++ [(x, y)]))) :=
    Part.mem_bind query (Part.mem_map _ (Part.get_mem defined))
  exact (Part.getOrElse_of_dom _ selected.1 _).trans (Part.get_eq_of_mem selected _)

/-- A stopped strategy keeps the current transcript with probability one. -/
lemma observationKernel_eq_single_of_stopped
    (R : RandomSystem A B D) (σ : List B →. A) (h : List (A × B))
    (stopped : ¬ (σ (h.map Prod.snd)).Dom) :
    R.observationKernel σ h = ProbDist.single h := by
  classical
  simp only [observationKernel, Part.eq_none_iff'.mpr stopped, Part.bind_none,
    Part.getOrElse_none]

/-- An undefined conditional reply uses the point mass on the current history. -/
lemma observationKernel_eq_single_of_undefined
    (R : RandomSystem A B D) (σ : List B →. A) (h : List (A × B)) {x : A}
    (query : x ∈ σ (h.map Prod.snd)) (undefined : ¬ (R.conditional h x).Dom) :
    R.observationKernel σ h = ProbDist.single h := by
  classical
  simp only [observationKernel, Part.bind_of_mem query, Part.eq_none_iff'.mpr undefined,
    Part.map_none, Part.getOrElse_none]

/-- A horizon law is the sum of its possible transcript point masses. -/
lemma sLaw_eq_sum_tSupp (R : RandomSystem A B D) (σ : List B →. A) (n : ℕ) :
    R.sLaw σ n = ∑ h ∈ R.tSupp σ n, Finsupp.single h (R h) := by
  classical
  calc
    _ = (R.sLaw σ n).sum Finsupp.single := (Finsupp.sum_single _).symm
    _ = _ := by
      rw [sLaw, Finsupp.onFinset_sum _ (fun h => Finsupp.single_zero h)]
      exact Finset.sum_congr rfl fun h hh => by rw [ite_eq_left (tSupp_good hh)]

/-- Before any observation, the only transcript is empty. -/
lemma sLaw_zero (R : RandomSystem A B D) (σ : List B →. A) :
    R.sLaw σ 0 = (ProbDist.single []).1 := by
  rw [sLaw_eq_sum_tSupp]
  simp only [tSupp, Finset.sum_singleton, R.mass_nil, ProbDist.single]

open Classical in
/-- At a possible strategy transcript, weighting the next observation by `R h` gives the
unnormalized extension law, or the retained point mass after stopping. -/
lemma smul_observationKernel
    (R : RandomSystem A B D) (σ : List B →. A) (compatible : R.Compatible σ)
    (h : List (A × B)) (follows : FollowsStrategy σ h) (possible : R h ≠ 0) :
    R h • (R.observationKernel σ h).1 =
      if hd : (σ (h.map Prod.snd)).Dom then
        fTransform (fun y => h ++ [((σ (h.map Prod.snd)).get hd, y)])
          (R.extensionLaw h ((σ (h.map Prod.snd)).get hd))
      else Finsupp.single h (R h) := by
  classical
  split_ifs with hd
  · have defined : (R.conditional h ((σ (h.map Prod.snd)).get hd)).Dom :=
      ⟨compatible h _ follows possible (Part.get_mem hd), possible⟩
    rw [observationKernel_eq_map R σ h (Part.get_mem hd) defined, ProbDist.map_val,
      ← fTransform_smul, smul_conditional_eq_extensionLaw]
  · rw [observationKernel_eq_single_of_stopped R σ h hd]
    simp only [ProbDist.single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- One more observation round is a mixture of the conditional transcript kernels. -/
theorem sLaw_succ_eq_bindK
    -- `σ` asks admitted queries on possible histories; it may stop before the horizon.
    (R : RandomSystem A B D) (σ : List B →. A) (compatible : R.Compatible σ) (n : ℕ) :
    R.sLaw σ (n + 1) = bindK (R.sLaw σ n) (fun h => (R.observationKernel σ h).1) := by
  classical
  calc
    _ = ∑ h ∈ R.tSupp σ (n + 1), Finsupp.single h (R h) := sLaw_eq_sum_tSupp R σ _
    -- The existing partition separates one-round extensions from stopped histories.
    _ = ∑ h ∈ R.tSupp σ n, R h • (R.observationKernel σ h).1 := by
      rw [sum_tSupp_succ]
      apply Finset.sum_congr rfl
      intro h hh
      rw [smul_observationKernel R σ compatible h (tSupp_good hh).1 (tSupp_possible hh)]
      split_ifs with hd
      · change _ = (R.extensionLaw h _).sum
          (fun y w => Finsupp.single (h ++ [((σ (h.map Prod.snd)).get hd, y)]) w)
        exact Finset.sum_congr rfl fun y _ => by rw [extensionLaw_apply]
      · rfl
    -- Mixing the point masses is exactly `bindK` of the current law.
    _ = _ := by
      rw [bindK, Finsupp.linearCombination_apply, sLaw,
        Finsupp.onFinset_sum _
          (fun h => (zero_smul ℝ (R.observationKernel σ h).1))]
      exact Finset.sum_congr rfl fun h hh => by rw [ite_eq_left (tSupp_good hh)]

end SystemAlgebra.RandomSystem

module

public import Probability.Kernel
public import Mathlib.Tactic.NormNum

/-!
# Dependent transport of correlated draws

The first draw is positive and nonuniform; the second is the first plus a biased bit.
Subtracting the first draw recovers that bit even when all first outcomes are mapped to `()`.
At the unreachable first outcome `0`, the conditional law deliberately fails the same equation.
-/

@[expose] public section

noncomputable section

namespace Probability.Distribution.Tests.JointLawTransport

/-- `noise` has masses `2/3,1/3` at `0,1`, on the infinite carrier `ℕ`. -/
def noise : ProbDist ℕ :=
  (𝒰[Fin 3]).map fun i => if i = 0 then 1 else 0

/-- `first` has masses `2/3,1/3` at `1,2`; in particular, `0` is unreachable. -/
def first : ProbDist ℕ := noise.map Nat.succ

/-- Given positive `h`, return `h+b` for `b ← noise`; at `0`, return `999`. -/
def shifted (h : ℕ) : ProbDist ℕ :=
  if h = 0 then ProbDist.single 999 else noise.map fun b => h + b

lemma first_ne_zero {h : ℕ} (hh : h ∈ first.1.support) : h ≠ 0 := by
  obtain ⟨b, _, rfl⟩ := mem_support_fTransform Nat.succ noise.1 hh
  exact Nat.succ_ne_zero b

/-- The second map depends on `h`, so the correlated pair becomes a fixed first value and noise. -/
theorem subtract_first :
    (ProbDist.jointLaw first shifted).map (fun hz => ((), hz.2 - hz.1)) =
      ProbDist.jointLaw (first.map (fun _ => ())) (fun _ => noise) := by
  apply ProbDist.jointLaw_map_dependent (fun _ => ()) (fun h z => z - h)
    (first.map (fun _ => ())) first (fun _ => noise) shifted rfl
  intro h hh
  rw [shifted, ite_eq_right (first_ne_zero hh), ProbDist.map_map]
  have cancel : (fun z => z - h) ∘ (fun b => h + b) = id := by
    funext b
    exact Nat.add_sub_cancel_left h b
  rw [cancel, ProbDist.map_id]

/-- Conditional transport really fails off the support; its omission from the contract matters. -/
example : (shifted 0).map (fun z => z - 0) ≠ noise := by
  have hn : noise.1 999 = 0 := by
    apply fTransform_apply_of_forall_ne
    intro i
    split_ifs <;> norm_num
  have hs : ((shifted 0).map (fun z => z - 0)).1 999 = 1 := by
    simp only [shifted, ProbDist.map_val, ProbDist.single,
      fTransform_single, Nat.sub_zero, Finsupp.single_apply, ite_true]
  intro equal
  have contradiction := congrArg (fun P : ProbDist ℕ => P.1 999) equal
  rw [hs, hn] at contradiction
  norm_num at contradiction

/-- Both first outcomes merged by the map to `()` have positive, unequal masses. -/
example : first.1 1 = 2 / 3 ∧ first.1 2 = 1 / 3 := by
  change fTransform Nat.succ noise.1 (Nat.succ 0) = 2 / 3 ∧
    fTransform Nat.succ noise.1 (Nat.succ 1) = 1 / 3
  rw [fTransform_injective_apply _ _ Nat.succ_injective 0,
    fTransform_injective_apply _ _ Nat.succ_injective 1]
  norm_num [noise, ProbDist.map_val, fTransform_apply_eq_mass, mass_eq_sum,
    ProbDist.uniform, uniform_apply, Fin.sum_univ_succ]

#print axioms ProbDist.jointLaw_map_dependent
#print axioms ProbDist.jointLaw_map
#print axioms subtract_first

end Probability.Distribution.Tests.JointLawTransport

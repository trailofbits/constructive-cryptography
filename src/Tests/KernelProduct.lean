module

public import Probability.Kernel
public import Probability.Expectation

/-!
# Independent kernels and retained pairs

Two coordinates use different infinite outcome types and signed laws. Their kernels depend
on the first outcome. The empty product has unit mass, and normalized joint sampling retains
the correlation between each sampled bit and its copied output.
-/

@[expose] public section

namespace Tests.KernelProduct

open Probability Probability.Distribution

/-- The first coordinate carries a natural number; the second carries a bit. -/
abbrev First : Bool → Type
  | false => ℕ
  | true => Bool

/-- The corresponding reply carriers are integers and natural numbers. -/
abbrev Second : Bool → Type
  | false => ℤ
  | true => ℕ

/-- First masses are `−2` at natural number 4 and `3` at bit false. -/
noncomputable def firstLaw : (i : Bool) → Distribution (First i)
  | false => Finsupp.single 4 (-2)
  | true => Finsupp.single false 3

/-- The integer reply is `n+1` with weight `−3`; the bit selects 7 or 9 with weight 2. -/
noncomputable def replyLaw : (i : Bool) → First i → Distribution (Second i)
  | false, n => Finsupp.single ((n : ℤ) + 1) (-3)
  | true, b => Finsupp.single (if b then 7 else 9) 2

/-- The resulting tuple at the support points is integer 5 and natural number 9. -/
def reply : (i : Bool) → Second i
  | false => 5
  | true => 9

/-- The product of coordinate mixtures also represents the two-stage table draw. -/
example : bindK (piDep firstLaw) (fun f => piDep (fun i => replyLaw i (f i))) =
    piDep (fun i => bindK (firstLaw i) (replyLaw i)) :=
  bindK_piDep firstLaw replyLaw

/-- Signed factors multiply to `((−2)(−3)) · (3 · 2) = 36` at this tuple. -/
example : bindK (piDep firstLaw) (fun f => piDep (fun i => replyLaw i (f i))) reply = 36 := by
  rw [bindK_piDep, piDep_apply]
  simp only [Fintype.prod_bool, firstLaw, replyLaw, reply, bindK_single,
    Finsupp.smul_apply, smul_eq_mul]
  norm_num [Finsupp.single_apply]

/-- With no coordinates, the kernel product is the unit point law on the empty tuple. -/
example :
    bindK (piDep (fun _ : Fin 0 => (Finsupp.single 7 (-2) : Distribution ℕ)))
        (fun f => piDep (fun i => (Finsupp.single (f i + 1) 3 : Distribution ℕ))) =
      Finsupp.single (fun i : Fin 0 => (Fin.elim0 i : ℕ)) 1 := by
  exact (bindK_piDep (fun _ : Fin 0 => (Finsupp.single 7 (-2) : Distribution ℕ))
    (fun (_ : Fin 0) (n : ℕ) => (Finsupp.single (n + 1) 3 : Distribution ℕ))).trans
      (piDep_fin_zero _)

/-- Independent bit–copy pairs can be regrouped into two perfectly correlated tables. -/
lemma copied_tables :
    ((ProbDist.piDep (fun _ : Bool => ProbDist.jointLaw 𝒰[Bool] ProbDist.single)).map
      (fun p => ((fun i => (p i).1), (fun i => (p i).2)))).1.mass
        (fun p => p.1 = p.2) = 1 := by
  rw [← ProbDist.jointLaw_piDep, ProbDist.jointLaw_mass_eq_expect]
  simp only [ProbDist.piDep_val, ProbDist.single, piDep_single, mass_single, ite_true,
    expect_const]
  simpa only [one_mul, ProbDist.piDep_val] using
    (ProbDist.piDep (fun _ : Bool => 𝒰[Bool])).2.weight_eq

#print axioms Probability.Distribution.bindK_piDep
#print axioms Probability.Distribution.bindK_piDep_pair
#print axioms Probability.Distribution.ProbDist.jointLaw_piDep
#print axioms copied_tables

end Tests.KernelProduct

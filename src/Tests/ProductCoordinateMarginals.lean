module

public import Probability.Kernel

/-! Injective coordinate selection retains differing laws and handles an empty selected table. -/

@[expose] public section

namespace Tests.ProductCoordinateMarginals

open Probability Probability.Distribution

/-- Coordinate `i` chooses uniformly between natural-number outcomes `i` and `i + 3`. -/
noncomputable def coordinateLaw (i : Fin 3) : ProbDist ℕ :=
  (𝒰[Bool]).map (fun b => i.val + if b then 3 else 0)

/-- The last two of three coordinates keep their distinct independent laws. -/
lemma last_two_coordinates :
    (ProbDist.pi coordinateLaw).map (fun f (j : Fin 2) => f j.succ) =
      ProbDist.pi (fun j : Fin 2 => coordinateLaw j.succ) :=
  ProbDist.map_pi_comp coordinateLaw Fin.succ
    (fun _ _ h => Fin.ext (Nat.succ.inj (congrArg Fin.val h)))

/-- Selecting no coordinates leaves the independent law on the empty tuple. -/
lemma empty_selection :
    (ProbDist.pi coordinateLaw).map (fun f (j : Fin 0) => f (Fin.elim0 j)) =
      ProbDist.pi (fun j : Fin 0 => coordinateLaw (Fin.elim0 j)) :=
  ProbDist.map_pi_comp coordinateLaw Fin.elim0 (fun j => Fin.elim0 j)

#print axioms Probability.Distribution.fTransform_pi_comp
#print axioms Probability.Distribution.ProbDist.map_pi_comp
#print axioms last_two_coordinates
#print axioms empty_selection

end Tests.ProductCoordinateMarginals

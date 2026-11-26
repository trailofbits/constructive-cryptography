module

public import RandomSystems.Cumulative.CumulativeObservation

/-!
# Distribution-valued transcript partitions

One observation round partitions the law of weighted transcript point masses into conditional
extensions and histories retained after stopping. The summands are distributions on lists,
whose carrier is infinite even when query and reply alphabets are finite.
-/

@[expose] public section

noncomputable section

namespace Tests.TranscriptPartition

open SystemAlgebra Probability
open scoped BigOperators

open Classical in
/-- The one-round partition holds for complete transcript laws as summands. -/
example {A B : Type} [Fintype A] [Fintype B] {D : Domain A B}
    (R : RandomSystem A B D) (σ : List B →. A) (n : ℕ) :
    (∑ h ∈ R.tSupp σ (n + 1), Finsupp.single h (R h) : Distribution (List (A × B))) =
      ∑ h ∈ R.tSupp σ n,
        if hd : (σ (h.map Prod.snd)).Dom then
          ∑ y ∈ (R.extensionLaw h ((σ (h.map Prod.snd)).get hd)).support,
            Finsupp.single (h ++ [((σ (h.map Prod.snd)).get hd, y)])
              (R (h ++ [((σ (h.map Prod.snd)).get hd, y)]))
        else Finsupp.single h (R h) :=
  RandomSystem.sum_tSupp_succ (R := R) (σ := σ) (fun h => Finsupp.single h (R h)) n

#print axioms RandomSystem.sum_tSupp_succ

end Tests.TranscriptPartition

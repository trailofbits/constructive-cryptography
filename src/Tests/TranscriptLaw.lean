module

public import RandomSystems.Typed.TranscriptLaw

/-!
# Observer transcript laws

An arbitrary adaptive, randomized observer stays within a two-query interface. An empty bad
event gives zero distinguishing gap, also after an independent retained initial choice.
-/

@[expose] public section

namespace Tests.TranscriptLaw

open SystemAlgebra Probability.Distribution

/-- A Boolean response interface allowing at most two queries. -/
abbrev replies := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 2

example (D : replies.inputDomain.Distinguisher) (R : TypedSystem replies)
    (h : List ((Σ i, replies.X i) × (Σ i, replies.Y i)))
    (hh : h ∈ (D.transcriptLaw R).1.support) : h.length ≤ 2 := by
  obtain he | hd := D.transcriptLaw_mem_support R h hh
  · simp only [he, List.length_nil, Nat.zero_le]
  · simpa only [List.length_map] using hd.2

example (D : replies.inputDomain.Distinguisher) (R : TypedSystem replies) :
    |D.probability R.1 - D.probability R.1| ≤ 0 := by
  exact (D.probability_gap_le_bad_mass R R (fun _ => False) (fun _ _ => rfl)).trans_eq
    (mass_eq_zero_of_forall_not _ (fun _ h => h))

example (D : replies.inputDomain.Distinguisher) (R : TypedSystem replies) :
    |D.probability (TypedSystem.sample (𝒰[Bool]).1 (fun _ => R)).1 -
      D.probability R.1| ≤ 0 := by
  exact (D.sample_probability_gap_le_bad_mass 𝒰[Bool] (fun _ => R) R
    (fun _ _ => False) (fun _ _ _ => rfl)).trans_eq
      (mass_eq_zero_of_forall_not _ (fun _ h => h))

#print axioms Domain.Distinguisher.sample_probability_gap_le_bad_mass

end Tests.TranscriptLaw

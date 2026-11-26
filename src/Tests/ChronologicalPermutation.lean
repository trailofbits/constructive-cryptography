module

public import RandomSystems.Converter.ChronologicalLabeling.Uniform
public import Tests.ChronologicalLabeling
public import Tests.ListPermutation

/-!
# Repeated queries to one retained permutation

Inputs `7,9,7` impose two distinct permutation constraints. Replies `0,1,0` have mass `1/2`;
replies `0,1,1` have mass zero. Both checks use the original three-query domain certificate.
-/

@[expose] public section

namespace Tests.ChronologicalPermutation

open Probability Probability.Distribution SystemAlgebra
open Tests.ChronologicalLabeling Tests.ListPermutation

-- `labels` chooses either enumeration of the two-label pool.
variable (labels : Fin (Fintype.card (Fin 2)) ≃ Fin 2)

/-- On `7,9,7`, the permutation coefficient equals that of the fixed evaluation `7↦0,9↦1`. -/
lemma coefficient_eq (ys : List (Σ _ : Unit, Fin 2)) :
    (uniform (Equiv.Perm (Fin 2))).mass (fun π => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain 3))
      (DDS.ofFunction (insideDomain 3) (insideDomain_prefix 3)
        (fun b => ⟨b.1, π b.2⟩)).1)) [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] ys) =
    (uniform (Equiv.Perm (Fin 2))).mass (fun π => Replies
      (DDS.ofFunction (outsideDomain 3) (outsideDomain_prefix 3)
        (fun a => ⟨a.1, π (evaluate a.2)⟩)).1 [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] ys) := by
  apply chronologicalLabelingProgram_uniform_mass_replies_eq_of_injOn
    labels 0 (insideDomain_prefix 3) (outsideDomain_prefix 3)
    (chronologicalLabelingProgram_isDDCFrom labels 0 3) evaluate
  apply evaluate_injOn.mono
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢
  rcases ha with from_first | from_second | from_repeat
  · exact Or.inl from_first
  · exact Or.inr from_second
  · exact Or.inl from_repeat

/-- A consistent repeat imposes the same two constraints, of mass `1/(2·1)`. -/
lemma consistent_replies :
    (uniform (Equiv.Perm (Fin 2))).mass (fun π => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain 3))
      (DDS.ofFunction (insideDomain 3) (insideDomain_prefix 3)
        (fun b => ⟨b.1, π b.2⟩)).1))
      [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] [⟨(), 0⟩, ⟨(), 1⟩, ⟨(), 0⟩]) = 1 / 2 := by
  rw [coefficient_eq]
  calc
    _ = (uniform (Equiv.Perm (Fin 2))).mass (fun π => π 0 = 0 ∧ π 1 = 1) := by
      apply mass_congr
      intro π
      rw [DDS.replies_ofFunction_iff]
      constructor
      · rintro ⟨_, equal⟩
        have hfirst := congrArg
          (fun h : List (Σ _ : Unit, Fin 2) => h.head?.map Sigma.snd) equal
        have hsecond := congrArg
          (fun h : List (Σ _ : Unit, Fin 2) => h.tail.head?.map Sigma.snd) equal
        norm_num [evaluate] at hfirst hsecond
        exact ⟨hfirst.symm, hsecond.symm⟩
      · rintro ⟨hzero, hone⟩
        refine ⟨Or.inr ?_, ?_⟩
        · norm_num [outsideDomain]
        · norm_num [evaluate, hzero, hone]
    _ = 1 / 2 := by
      have counted := Probability.Counting.permutation_agreement_mass
        (Equiv.refl (Fin 2)) [0, 1]
      norm_num [Nat.descFactorial] at counted
      exact counted

/-- The first and third replies cannot disagree on the same retained input. -/
lemma conflicting_replies :
    (uniform (Equiv.Perm (Fin 2))).mass (fun π => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels 0) (outsideDomain 3))
      (DDS.ofFunction (insideDomain 3) (insideDomain_prefix 3)
        (fun b => ⟨b.1, π b.2⟩)).1))
      [⟨(), 7⟩, ⟨(), 9⟩, ⟨(), 7⟩] [⟨(), 0⟩, ⟨(), 1⟩, ⟨(), 1⟩]) = 0 := by
  rw [coefficient_eq]
  apply mass_eq_zero_of_forall_not
  intro π replies
  have equal := (DDS.replies_ofFunction_iff _ _ _ _ _).mp replies |>.2
  have hfirst := congrArg
    (fun h : List (Σ _ : Unit, Fin 2) => h.head?.map Sigma.snd) equal
  have hlast := congrArg
    (fun h : List (Σ _ : Unit, Fin 2) => h.getLast?.map Sigma.snd) equal
  norm_num [evaluate] at hfirst hlast
  have impossible : (0 : Fin 2) = 1 := hfirst.trans hlast.symm
  norm_num at impossible

#print axioms chronologicalLabelingProgram_uniform_mass_replies_eq_of_injOn
#print axioms coefficient_eq
#print axioms consistent_replies
#print axioms conflicting_replies

end Tests.ChronologicalPermutation

module

public import Commons.Definitions.AbstractModel.DomainExpansion.Laws
public import Commons.Definitions.AbstractModel.ObservationRefinement

/-!
# An empty observation schedule and a terminal submission

One computation initializes register 1, a zero-operand observation expands to no commands,
and a final submission remains final. Its allowance counts the two source ordinary commands.
-/

@[expose] public section

namespace Tests.DomainExpansion

open Commons Commons.AbstractModel

/-- The computation writes 1; the zero-operand observation returns unit. -/
abbrev model : AbstractModel Nat Unit where
  Operation := Unit
  Query := Unit
  arity _ := 0
  queryArity _ := 0
  Reply _ := Unit
  operate _ _ _ := 1
  evaluate _ _ _ := ()

/-- Preserve computation/submission and erase the observation with no operands. -/
def expand : model.Command Nat → List (model.Command Nat) :=
  model.observationCommandSchedule (fun _ : Unit => 0) (fun _ => 0)
    (fun _ i => Fin.elim0 i) (fun _ i => Fin.elim0 i)

/-- The source computes into register 1, observes no operands, then submits 7. -/
def commands : List (model.Command Nat) :=
  [⟨.compute (), ((fun i => Fin.elim0 i), 1)⟩,
    ⟨.query (), fun i => Fin.elim0 i⟩, ⟨.submit, 7⟩]

lemma source_admitted : model.Admitted 0 2 commands := by
  apply (model.admitted_iff_forallScan 0 2 commands).mpr
  refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
  · change 2 ≤ 2
    exact Nat.le_refl _
  · simp only [commands, List.ForallScan, admissionAllowed, admissionUpdate, reads, target,
      ordinary, Option.elim_some, Option.elim_none, Bool.true_and, Finset.univ_eq_empty,
      Finset.image_empty, Finset.empty_subset, and_self]

lemma expand_targets (z : model.Command Nat) :
    (expand z).filterMap model.target = (model.target z).toList := by
  rcases z with ⟨port, value⟩
  cases port <;> rfl

lemma expand_reads (z u : model.Command Nat) (member : u ∈ expand z) :
    model.reads u ⊆ model.reads z := by
  rcases z with ⟨port, value⟩
  cases port with
  | compute o =>
    simp only [expand, observationCommandSchedule, List.mem_singleton] at member
    subst u
    exact Finset.Subset.refl _
  | query ρ =>
    simp only [expand, observationCommandSchedule, List.ofFn_zero, List.not_mem_nil] at member
  | submit =>
    simp only [expand, observationCommandSchedule, List.mem_singleton] at member
    subst u
    exact Finset.Subset.refl _

lemma expand_terminal (z u : model.Command Nat) (member : u ∈ (expand z).dropLast) :
    model.ordinary u = true := by
  rcases z with ⟨port, value⟩
  cases port <;> simp only [expand, observationCommandSchedule, List.ofFn_zero,
    List.dropLast_singleton, List.dropLast_nil,
    List.not_mem_nil] at member

lemma expand_ordinary (z : model.Command Nat) :
    (expand z).all model.ordinary = model.ordinary z := by
  rcases z with ⟨port, value⟩
  cases port <;> rfl

lemma expand_cost (z : model.Command Nat) :
    (expand z).countP model.ordinary ≤ 1 * (if model.ordinary z then 1 else 0) := by
  rcases z with ⟨port, value⟩
  cases port with
  | compute o => exact Nat.le_refl _
  | query ρ => exact Nat.zero_le _
  | submit => exact Nat.le_refl _

/-- The empty observation disappears; the destination and terminal submission remain legal. -/
theorem expanded_admission : model.Admitted 0 2
    [⟨.compute (), ((fun i => Fin.elim0 i), 1)⟩, ⟨.submit, 7⟩] := by
  rcases Admitted.flatMap model model expand expand_targets expand_reads expand_terminal
      expand_ordinary 1 expand_cost source_admitted with empty | admitted
  · change ([⟨.compute (), ((fun i => Fin.elim0 i), 1)⟩, ⟨.submit, 7⟩] :
      List (model.Command Nat)) = [] at empty
    exact False.elim (List.cons_ne_nil _ _ empty)
  · exact admitted

example : expand ⟨.query (), fun i : Fin 0 => Fin.elim0 i⟩ = [] := rfl

example : ¬ model.Admitted 0 2 [⟨.submit, 7⟩, ⟨.submit, 8⟩] := by
  intro admitted
  have earlier := admitted.2.2.1 ⟨.submit, 7⟩ List.mem_cons_self
  exact Bool.false_ne_true earlier

#print axioms admitted_iff_forallScan
#print axioms Admitted.flatMap
#print axioms expanded_admission

end Tests.DomainExpansion

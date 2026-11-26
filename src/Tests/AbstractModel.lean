module

public import Commons.Definitions.AbstractModel.Domain

/-!
# Abstract-model domain checks

The model uses natural-number registers and parameters, with Boolean and natural-number
observations. Tests cover initialized reads, overwriting, the separate final submission,
and rejection of commands after submission or beyond the ordinary-query allowance.
-/

@[expose] public section

namespace Tests.AbstractModel

open Commons Commons.AbstractModel

/-- Increment the selected operand; observe equality to parameter `p`, or return `p` itself. -/
abbrev model : Commons.AbstractModel ℕ ℕ where
  Operation := Unit
  Query := Bool
  arity _ := 1
  queryArity
    | false => 1
    | true => 0
  Reply
    | false => Bool
    | true => ℕ
  operate _ _ values := values 0 + 1
  evaluate p
    | false, values => values 0 == p
    | true, _ => p

/-- Compute from initially populated address 0 and store the result at address 7. -/
def store : model.Command ℕ := ⟨.compute (), (fun _ => 0, 7)⟩

/-- Observe the value at address 7. -/
def observe : model.Command ℕ := ⟨.query false, fun _ => 7⟩

/-- Submit 3 as the candidate for the initial secret. -/
def submit : model.Command ℕ := ⟨.submit, 3⟩

/-- A terminal guess consumes no ordinary-query allowance. -/
lemma zero_budget_submit : model.Admitted 0 0 [submit] := by
  change model.Admitted 0 0 ([] ++ [submit])
  rw [admitted_snoc_iff]
  simp [submit, ordinary, reads]

/-- One legal computation initializes its destination, with no finiteness on register names. -/
lemma store_admitted : model.Admitted 0 1 [store] := by
  change model.Admitted 0 1 ([] ++ [store])
  rw [admitted_snoc_iff]
  simp [store, reads, initialized, ordinary]

/-- The query may read 7 after a computation has initialized it. -/
lemma store_observe_admitted : model.Admitted 0 2 [store, observe] := by
  change model.Admitted 0 2 ([store] ++ [observe])
  rw [admitted_snoc_iff]
  refine ⟨Or.inr ?_, ?_, ?_, ?_⟩
  · exact ⟨store_admitted.1, store_admitted.2.1.trans (by omega), store_admitted.2.2⟩
  · simp [store, observe, ordinary, List.countP_cons, List.countP_nil]
  · simp [store, ordinary]
  · simp [store, observe, reads, initialized, target]

/-- Final submission adds one command after the two ordinary interactions. -/
lemma complete_admitted : model.Admitted 0 2 [store, observe, submit] := by
  change model.Admitted 0 2 ([store, observe] ++ [submit])
  rw [admitted_snoc_iff]
  refine ⟨Or.inr store_observe_admitted, ?_, ?_, ?_⟩
  · simp [store, observe, submit, ordinary, List.countP_cons, List.countP_nil]
  · simp [store, observe, ordinary]
  · exact Finset.empty_subset _

example : ([store, observe, submit] : List (model.Command ℕ)).length ≤ 2 + 1 :=
  complete_admitted.length_le

/-- A query before initialization cannot read address 7. -/
example : ¬ model.Admitted 0 1 [observe] := by
  intro h
  have arguments := h.2.2.2 [] observe (List.prefix_refl _)
  have bad := arguments (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  simp [initialized] at bad

/-- A completed submission prevents any further command, including another submission. -/
example : ¬ model.Admitted 0 1 [submit, store] := by
  intro h
  have ordinary := h.2.2.1 submit (by simp)
  simp [submit, Commons.AbstractModel.ordinary] at ordinary

/-- Computations consume the same ordinary-query allowance as observations. -/
example : ¬ model.Admitted 0 1 [store, observe] := by
  intro h
  have count := h.2.1
  simp [store, observe, ordinary, List.countP_cons, List.countP_nil] at count

/-- A computation may overwrite the already initialized input register. -/
example : model.Admitted 0 1 [⟨.compute (), (fun _ => 0, 0)⟩] := by
  change model.Admitted 0 1 ([] ++ [⟨.compute (), (fun _ => 0, 0)⟩])
  rw [admitted_snoc_iff]
  simp [reads, initialized, ordinary]

example : model.Output (.query false) = Bool := rfl
example : model.Output (.query true) = ℕ := rfl

#print axioms zero_budget_submit
#print axioms complete_admitted
#print axioms Commons.AbstractModel.Admitted.prefix
#print axioms Commons.AbstractModel.Admitted.length_le
#print axioms Commons.AbstractModel.admitted_snoc_iff

end Tests.AbstractModel

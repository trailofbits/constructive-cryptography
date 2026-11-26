module

public import Commons.Definitions.AbstractModel.RegisterProgram
public import Commons.Definitions.AbstractModel.Registers.Laws

/-!
# Query costs of the register program

`registerProgram_costs` and `registerProgram_bounded` derive the exact 0/1/0 call pattern
from the call/return laws. `observationCost_sum_le` compares its total with the ordinary-command
budget. These are the certificates used by the typed register converter.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
  -- `M` gives the commands and interpretations; `ι` names registers.
  {S P ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- Every invocation makes at most one observation call. -/
lemma registerProgram_bounded (input : ι) (p : P) (x : S) :
    (M.registerProgram input p x).Bounded 1 := by
  intro h i u
  cases i with
  | compute o => exact callBound_return 1 _
  | query ρ => exact callBound_call _ _ _ (fun _ => callBound_return 0 _)
  | submit => exact callBound_return 1 _

/-- The exact observation cost is 0 for compute/submit and 1 for query, including pending calls. -/
lemma registerProgram_costs (input : ι) (p : P) (x : S) :
    (M.registerProgram input p x).Costs M.observationCost := by
  intro h i u
  cases i with
  | compute o => exact callCost_return _
  | query ρ => exact callCost_call _ _ _ (fun _ => callCost_return _)
  | submit => exact callCost_return _

/-- On an admitted history, observation calls are among the at most `k` ordinary commands. -/
lemma observationCost_sum_le
    -- `input` is initially populated; `k` bounds ordinary commands in `h`.
    (input : ι) (k : ℕ) (h : List (M.Command ι)) (admitted : M.Admitted input k h) :
    (h.map M.observationCost).sum ≤ k := by
  let observed : M.Command ι → Bool := fun z => M.observationCost z == 1
  have count : h.countP observed = (h.map M.observationCost).sum := by
    have eq := List.countP_flatMap (p := observed) (l := h) (f := fun z => [z])
    rw [List.flatMap_singleton'] at eq
    convert eq using 2
    apply List.map_congr_left
    rintro ⟨i, u⟩ _
    cases i <;> rfl
  rw [← count]
  exact (List.countP_mono_left (fun ⟨i, u⟩ _ hz => by
    cases i with
    | compute _ => rfl
    | query _ => rfl
    | submit => cases hz)).trans
      admitted.2.1

/-- On an admitted observation, totalization returns exactly the initialized operand tuple. -/
lemma read_registers_getD
    -- `input` starts with `x`; `p` fixes operations and `h` contains completed commands.
    (input : ι) (p : P) (x : S) (h : List (M.Command ι))
    -- `ρ(a)` is the next observation, admitted with ordinary allowance `k`.
    (ρ : M.Query) (a : Fin (M.queryArity ρ) → ι) (k : ℕ)
    (admitted : M.Admitted input k (h ++ [⟨.query ρ, a⟩])) :
    some ((read (M.registers (M.operate p) (initial input x) h) a).getD (fun _ => x)) =
      read (M.registers (M.operate p) (initial input x) h) a := by
  have live := M.registers_isSome (M.operate p) (initial input x) input
    (initial_isSome input x) h (fun t z hp =>
      admitted.2.2.2 t z (hp.trans (List.prefix_append _ _)))
  have ready : (read (M.registers (M.operate p) (initial input x) h) a).isSome := by
    apply (read_isSome _ a).mpr
    intro j
    apply (live (a j)).mpr
    exact admitted.2.2.2 h ⟨.query ρ, a⟩ (List.prefix_refl _)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  apply Option.getD_of_ne_none
  intro missing
  simp only [missing, Option.isSome_none, Bool.false_eq_true] at ready

end Commons.AbstractModel

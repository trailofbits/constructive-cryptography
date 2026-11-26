module

public import Commons.Definitions.AbstractModel.RegisterProgram
public import Commons.Definitions.AbstractModel.Registers.Laws
public import RandomSystems.Converter.ProgramTrace

/-!
# Laws of the register program

`registerProgram_queryMap` transports an internal interpretation through every observation call.
The outside command history and replies stay fixed. `registerProgram_costs` and
`registerProgram_bounded` derive the exact 0/1/0 call pattern
from the call/return laws. `observationCost_sum_le` compares its total with the ordinary-command
budget. These are the certificates used by the typed register converter.
`registerProgram_combine_query` identifies one successful read against a deterministic inside
component, retaining both its updated state and the appended command history.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra SystemAlgebra.DSL

variable
  -- `M` gives the commands and interpretations; `ι` names registers.
  {S P W ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- The register program transports its internal interpretation with unchanged outside data. -/
lemma registerProgram_queryMap
    -- `V` carries interpreted values; `input` names the same initialized register.
    {V : Type} (input : ι)
    -- `opW` and `opV` interpret the same operation symbols on their respective values.
    (opW : (o : M.Operation) → (Fin (M.arity o) → W) → W)
    (opV : (o : M.Operation) → (Fin (M.arity o) → V) → V)
    -- `f` interprets values; `hom` says this interpretation commutes with every operation.
    (f : W → V) (hom : ∀ o a, opV o (f ∘ a) = f (opW o a))
    -- `initialValue` matches both initial contents and the fallback for missing reads.
    (w : W) (v : V) (initialValue : f w = v)
    -- `h` records completed outside commands; `o` selects a port and `u` is its request.
    -- `t` records this invocation's inside queries and replies.
    (h : List (M.Command ι)) (o : Port M.Operation M.Query) (u : M.Input ι o)
    (t : List ((Σ ρ, Fin (M.queryArity ρ) → W) × (Σ ρ, M.Reply ρ))) :
    Sum.map id (Sigma.map id (fun _ a => f ∘ a))
        (M.registerProgram input opW w h o u t) =
      M.registerProgram input opV v h o u
        (t.map (Prod.map (Sigma.map id (fun _ a => f ∘ a)) id)) := by
  cases o with
  | compute o => rfl
  | submit => rfl
  | query ρ =>
    -- Initial contents and every subsequent register update commute with interpretation.
    have initialMap : initial input v = Option.map f ∘ initial input w := by
      rw [← initialValue]
      exact initial_map f input w
    have contents : M.registers opV (initial input v) h =
        Option.map f ∘ M.registers opW (initial input w) h := by
      rw [initialMap]
      exact registers_map opW opV f hom _ _
    -- Read tuples and their fallback are interpreted by the same map.
    have operands : (read (M.registers opV (initial input v) h) u).getD (fun _ => v) =
        f ∘ (read (M.registers opW (initial input w) h) u).getD (fun _ => w) := by
      rw [contents, read_map, ← initialValue]
      exact Option.getD_map (fun a => f ∘ a) (fun _ => w) _
    -- Only the observation query changes; the reply and appended command are identical.
    simp only [registerProgram]
    rw [operands]
    exact SystemAlgebra.DSL.callProg_queryMap (fun _ a => f ∘ a) ρ _ _ _ (fun _ _ => rfl) t

/-- Every invocation makes at most one observation call. -/
lemma registerProgram_bounded (input : ι)
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W) :
    (M.registerProgram input op w).Bounded 1 := by
  intro h i u
  cases i with
  | compute o => exact callBound_return 1 _
  | query ρ => exact callBound_call _ _ _ (fun _ => callBound_return 0 _)
  | submit => exact callBound_return 1 _

/-- A successful register read supplies the one observation call; both retained states advance. -/
lemma registerProgram_combine_query
    -- `input` starts with `w`; `op` interprets the computation symbols.
    (input : ι) (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W)
    -- `stepR` is the inside component on its retained state `R`.
    {R : Type} (stepR : R → (ρ : M.Query) → (Fin (M.queryArity ρ) → W) → R × M.Reply ρ)
    -- `h` is the completed command history; `ρ` reads the selected `addresses`.
    (h : List (M.Command ι)) (ρ : M.Query) (addresses : Fin (M.queryArity ρ) → ι)
    -- `present` certifies that the complete read succeeds with operand tuple `values`.
    (values : Fin (M.queryArity ρ) → W)
    (present : read (M.registers op (initial input w) h) addresses = some values)
    -- `r` is the inside state before the observation call; `stepR` supplies its next state.
    (r : R) :
    (M.registerProgram input op w).combine stepR (M.registerProgram_bounded input op w)
        (h, r) (.query ρ) addresses =
      ((h ++ [⟨.query ρ, addresses⟩], (stepR r ρ values).1), (stepR r ρ values).2) := by
  let q : Σ ρ, Fin (M.queryArity ρ) → W := ⟨ρ, values⟩
  let t := [(q, (⟨ρ, (stepR r ρ values).2⟩ : Σ ρ, M.Reply ρ))]
  have issued : M.registerProgram input op w h (.query ρ) addresses [] = .inr q := by
    simp only [registerProgram, present, Option.getD_some, callProg, q]
  have consistent : (M.registerProgram input op w).Consistent h (.query ρ) addresses t :=
    (Program.consistent_nil (M.registerProgram input op w) h (.query ρ) addresses).snoc
      (q := q) issued (stepR r ρ values).2
  have actual : Replies (automatonSystem stepR r) (t.map Prod.fst) (t.map Prod.snd) := by
    change Replies (automatonSystem stepR r) ([] ++ [q])
      ([] ++ [⟨ρ, (stepR r ρ values).2⟩])
    refine replies_snoc.mpr ⟨replies_nil _, ?_⟩
    rw [automatonSystem_snoc]
    rfl
  have returned : M.registerProgram input op w h (.query ρ) addresses t =
      .inl (h ++ [⟨.query ρ, addresses⟩], (stepR r ρ values).2) := by
    simp only [registerProgram, t, callProg, ↓reduceDIte, returnProg]
  exact (M.registerProgram input op w).combine_eq_of_consistent_replies stepR
    (M.registerProgram_bounded input op w) h (.query ρ) addresses r t
    consistent actual returned

/-- The exact observation cost is 0 for compute/submit and 1 for query, including pending calls. -/
lemma registerProgram_costs (input : ι)
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W) :
    (M.registerProgram input op w).Costs M.observationCost := by
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
    -- `input` starts with `w`; `op` interprets operations and `h` contains completed commands.
    (input : ι) (op : (o : M.Operation) → (Fin (M.arity o) → W) → W)
    (w : W) (h : List (M.Command ι))
    -- `ρ(a)` is the next observation, admitted with ordinary allowance `k`.
    (ρ : M.Query) (a : Fin (M.queryArity ρ) → ι) (k : ℕ)
    (admitted : M.Admitted input k (h ++ [⟨.query ρ, a⟩])) :
    some ((read (M.registers op (initial input w) h) a).getD (fun _ => w)) =
      read (M.registers op (initial input w) h) a := by
  have live := M.registers_isSome op (initial input w) input
    (initial_isSome input w) h (fun t z hp =>
      admitted.2.2.2 t z (hp.trans (List.prefix_append _ _)))
  have ready : (read (M.registers op (initial input w) h) a).isSome := by
    apply (read_isSome _ a).mpr
    intro j
    apply (live (a j)).mpr
    exact admitted.2.2.2 h ⟨.query ρ, a⟩ (List.prefix_refl _)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
  apply Option.getD_of_ne_none
  intro missing
  simp only [missing, Option.isSome_none, Bool.false_eq_true] at ready

end Commons.AbstractModel

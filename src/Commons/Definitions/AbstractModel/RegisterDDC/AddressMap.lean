module

public import Commons.Definitions.AbstractModel.RegisterDDC

/-!
# Register converter address embeddings

`registerProgram_mapCommand` transports the completed-history body through an address
embedding. Register pullback identifies its operand tuples; the call-map law transports its
continuation. `registersDDC_mapCommand` then applies the compiler's input/state transport,
with the exact admitted-domain equation from `admitted_mapCommand_iff`.
Inside observations, replies, initial values, and submitted guesses remain unchanged.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra
open SystemAlgebra.DSL (callProg_map returnProg)

variable
  -- `M` fixes commands and replies over values `S` and parameters `P`; `W` carries internal values.
  {S P W ι κ : Type} (M : Commons.AbstractModel S P)
  -- `ι` and `κ` index the source and target registers; neither is required to be finite.
  [DecidableEq ι] [DecidableEq κ]

/-- The register body commutes with embedding every address in its completed history. -/
lemma registerProgram_mapCommand
    -- `d` embeds addresses; `input` names the initially populated source register.
    (d : ι ↪ κ) (input : ι)
    -- `op` interprets computations on `W`; the same initial value `w` is used on both sides.
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W)
    -- `h` contains completed commands; `o` selects the next port and `u` its input.
    (h : List (M.Command ι)) (o : Port M.Operation M.Query) (u : M.Input ι o)
    -- `t` records the invocation's inside exchanges, including histories outside its execution.
    (t : List ((Σ ρ, Fin (M.queryArity ρ) → W) × (Σ ρ, M.Reply ρ))) :
    Sum.map (Prod.map (List.map (M.mapCommand d)) id) id
        (M.registerProgram input op w h o u t) =
      M.registerProgram (d input) op w (h.map (M.mapCommand d)) o (M.mapInput d o u) t := by
  cases o with
  | compute o =>
    simp only [registerProgram, mapInput, returnProg, Sum.map_inl, Prod.map,
      List.map_append, List.map_singleton, id_eq, mapCommand, Sigma.map]
  | submit =>
    simp only [registerProgram, mapInput, returnProg, Sum.map_inl, Prod.map,
      List.map_append, List.map_singleton, id_eq, mapCommand, Sigma.map]
  | query ρ =>
    -- Corresponding addresses retain the same contents after every completed command.
    have contents : M.registers op (initial (d input) w) (h.map (M.mapCommand d)) ∘ d =
        M.registers op (initial input w) h := by
      rw [registers_mapCommand, initial_comp_embedding]
    -- The query reads the same tuple, with the same fallback when a read is undefined.
    have operands : read (M.registers op (initial (d input) w)
          (h.map (M.mapCommand d))) (d ∘ u) =
        read (M.registers op (initial input w) h) u := by
      rw [← read_comp, contents]
    simp only [registerProgram, mapInput]
    rw [operands]
    have identity : Sigma.map id
        (fun ρ => (id : (Fin (M.queryArity ρ) → W) → (Fin (M.queryArity ρ) → W))) = id := rfl
    have exchanges : Prod.map (id : (Σ ρ, Fin (M.queryArity ρ) → W) → _)
        (id : (Σ ρ, M.Reply ρ) → _) = id := rfl
    -- The call and its reply stay fixed; only the continuation's completed history is mapped.
    have calls := callProg_map (Prod.map (List.map (M.mapCommand d)) id)
      (fun _ => id) ρ
      ((read (M.registers op (initial input w) h) u).getD (fun _ => w))
      (fun y => returnProg (h ++ [⟨.query ρ, u⟩], y))
      (fun y => returnProg (h.map (M.mapCommand d) ++ [⟨.query ρ, d ∘ u⟩], y))
      (fun y v => by
        simp only [returnProg, Sum.map_inl, Prod.map, List.map_append,
          List.map_singleton, id_eq, mapCommand, Sigma.map, mapInput]) t
    simpa only [identity, exchanges, List.map_id, id_eq] using calls

/-- The complete raw DDC is the same after mapping input commands along an address embedding. -/
lemma registersDDC_mapCommand
    -- `d` embeds addresses; `input` starts populated and `k` bounds ordinary commands.
    (d : ι ↪ κ) (input : ι) (k : ℕ)
    -- The interpretation `op` and initial value `w` are unchanged by address renaming.
    (op : (o : M.Operation) → (Fin (M.arity o) → W) → W) (w : W)
    -- `xs` contains outside commands and inside replies, including pending invocations.
    (xs : List (Σ l, twoFam (M.Input ι) M.Reply l)) :
    (M.registersDDC input k op w).1 xs =
      (M.registersDDC (d input) k op w).1 (xs.map (outsideMap (M.mapCommand d))) := by
  let H := List.map (M.mapCommand d)
  have body := registerProgram_mapCommand M d input op w
  have steps := Program.step_stateInputMap H (M.mapInput d) body
  -- Address embeddings preserve the exact outside domain used by the compiler's filter.
  have allowed : ∀ ys : List (Σ l, twoFam (M.Input ι) M.Reply l),
      (outsideInputs ys = [] ∨ M.Admitted input k (outsideInputs ys)) ↔
      (outsideInputs (ys.map (outsideMap (M.mapCommand d))) = [] ∨
        M.Admitted (d input) k (outsideInputs (ys.map (outsideMap (M.mapCommand d))))) := by
    intro ys
    rw [outsideInputs_map_outsideMap]
    simp only [List.map_eq_nil_iff, admitted_mapCommand_iff]
  calc
    (M.registersDDC input k op w).1 xs =
        ((M.registersDDC input k op w).1 xs).map id :=
      (Part.map_id' (f := id) (fun _ => rfl) _).symm
    _ = _ := DDC.ofProgramOn_map_inputs_of_stepMap
      (M.registerProgram input op w) (M.registerProgram (d input) op w)
      (outsideMap (M.mapCommand d)) (Program.Mode.mapStateInput H (M.mapInput d)) id
      steps [] [] rfl (M.Admitted input k) (M.Admitted (d input) k) allowed xs

end Commons.AbstractModel

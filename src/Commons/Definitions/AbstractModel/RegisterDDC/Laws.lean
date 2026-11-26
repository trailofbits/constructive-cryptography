module

public import Commons.Definitions.AbstractModel.RegisterDDC
public import RandomSystems.Converter.ProgramQueryMap

/-!
# Transporting register interpretations

`registersDDC_relabel_of_map` interprets inside operands by a map preserving computations
and initial values. The completed converter retains its outside commands, submitted values,
and domain. The program equation supplies the generic compiler's query-map contract.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `M` fixes outside commands and replies; `ι` names registers, and `W`, `V` carry values.
  {S P W V ι : Type} (M : Commons.AbstractModel S P) [DecidableEq ι]

/-- Interpreting register contents relabels only inside queries on the same outside domain. -/
lemma registersDDC_relabel_of_map
    -- `input` is initially occupied, and `k` is the unchanged ordinary-command allowance.
    (input : ι) (k : ℕ)
    -- `opW` and `opV` interpret the same computations on `W` and `V`.
    (opW : (o : M.Operation) → (Fin (M.arity o) → W) → W)
    (opV : (o : M.Operation) → (Fin (M.arity o) → V) → V)
    -- `f` preserves the computations and maps initial contents `w` to `v`.
    (f : W → V) (hom : ∀ o a, opV o (f ∘ a) = f (opW o a))
    (w : W) (v : V) (initialValue : f w = v) :
    (M.registersDDC input k opV v).1 =
      relabel (M.registersDDC input k opW w).1 id
        (insideMap (Sigma.map id (fun _ a => f ∘ a))) :=
  DDC.ofProgramOn_relabel_of_queryMap
    (M.registerProgram input opW w) (M.registerProgram input opV v)
    (Sigma.map id (fun _ a => f ∘ a)) (fun _ => rfl)
    (M.registerProgram_queryMap input opW opV f hom w v initialValue) [] (M.Admitted input k)

end Commons.AbstractModel

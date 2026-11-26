module

public import Commons.Definitions.AbstractModel.ExtractionPresentation.AddressMap
public import RandomSystems.System.QueryRelabel.Laws
public import RandomSystems.System.Transcript

/-!
# Recoding extraction transcripts

`extractionDDS_tr_relabelQueries` identifies the decoded interaction with the
original caller's interaction at every horizon. `extractionDDS_mapCommand` transports the
fixed system; the support-local decoder law transports its caller. Both keep the same
parameter, original secret, replies, and submitted value.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `M` interprets operations on `S` at parameter `P`; `ι` and `κ` name the two register carriers.
  {S P ι κ : Type} (M : Commons.AbstractModel S P) [DecidableEq ι] [DecidableEq κ]

/-- A supported query code gives the same decoded transcript for every retained sample. -/
lemma extractionDDS_tr_relabelQueries
    -- `D` is the original raw caller; `valid` supplies its bounded partial strategy.
    (D : DDD (Port M.Operation M.Query) (M.Input ι) M.Output) (valid : IsDDD D)
    -- `decode` is injective; `initial` retains the initially populated address `input`.
    (code : ι → κ) (decode : κ ↪ ι) (input : ι)
    (initial : decode (code input) = input)
    -- `inverse` decodes only commands that the source caller can propose.
    (inverse : ∀ ys q, q ∈ (ddeOf valid).1 ys →
      M.mapCommand decode (M.mapCommand code q) = q)
    -- `k` bounds ordinary commands; `z=(p,x)` is retained and `n` is the transcript horizon.
    (k : ℕ) (z : P × S) (n : ℕ) :
    ((M.extractionDDS (code input) k z).1.tr
      (ddeOf (IsDDD.relabelQueries valid (M.mapInput code))).1 n).map
        (Prod.map (M.mapCommand decode) id) =
      (M.extractionDDS input k z).1.tr (ddeOf valid).1 n := by
  -- Fixed attachment respects address decoding without changing the retained sample.
  have presentation := extractionDDS_mapCommand M decode (code input) k z
  rw [initial] at presentation
  -- The decoder recovers exactly the source strategy on its supported queries.
  have strategy : (fun ys =>
      ((ddeOf (IsDDD.relabelQueries valid (M.mapInput code))).1 ys).map
        (M.mapCommand decode)) = (ddeOf valid).1 := by
    funext ys
    refine ddeOf_relabelQueries_map_decode valid (M.mapInput code) (M.mapInput decode)
      {q | ∃ ys, q ∈ (ddeOf valid).1 ys} (fun ys q hq => ⟨ys, hq⟩) ?_ ys
    intro q present
    obtain ⟨ys, hq⟩ := present
    exact eq_of_heq (Sigma.mk.inj_iff.mp (inverse ys q hq)).2
  rw [presentation]
  exact (System.tr_relabel_input (M.extractionDDS input k z).1
    (M.mapCommand decode) _ n).trans
      (congrArg (fun σ => (M.extractionDDS input k z).1.tr σ n) strategy)

end Commons.AbstractModel

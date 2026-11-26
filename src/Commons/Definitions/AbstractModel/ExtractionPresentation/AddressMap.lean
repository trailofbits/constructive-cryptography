module

public import Commons.Definitions.AbstractModel.RegisterDDC.AddressMap
public import Commons.Definitions.AbstractModel.ExtractionPresentation

/-!
# Address embeddings of extraction systems

`extractionDDS_mapCommand` lifts the register-converter address law through fixed
observations and canonical attachment. `submitted_mapCommand` preserves the first terminal
guess, so the same sampled secret defines the winning event after address recoding.
-/

@[expose] public section

namespace Commons.AbstractModel

open SystemAlgebra

variable
  -- `M` interprets computations on `S` with parameter `P`; `ι` and `κ` name registers.
  {S P ι κ : Type} (M : Commons.AbstractModel S P) [DecidableEq ι] [DecidableEq κ]

/-- Address embeddings preserve the attached extraction DDS, retaining the same `(p,x)`. -/
lemma extractionDDS_mapCommand
    -- `d` embeds addresses and `input` selects the initial source register.
    (d : ι ↪ κ) (input : ι) (k : ℕ)
    -- `z=(p,x)` fixes the same operation parameter and original secret in both systems.
    (z : P × S) :
    (M.extractionDDS input k z).1 =
      relabel (M.extractionDDS (d input) k z).1 (M.mapCommand d) id := by
  have converter : (M.registersDDC input k (M.operate z.1) z.2).1 =
      relabel (M.registersDDC (d input) k (M.operate z.1) z.2).1
        (outsideMap (M.mapCommand d)) id := by
    funext xs
    exact (registersDDC_mapCommand M d input k (M.operate z.1) z.2 xs).trans
      (Part.map_id' (f := id) (fun _ => rfl) _).symm
  change trim (apply (M.registersDDC input k (M.operate z.1) z.2).1
      (M.observationsDDS k z.1).1) =
    relabel (trim (apply (M.registersDDC (d input) k (M.operate z.1) z.2).1
      (M.observationsDDS k z.1).1)) (M.mapCommand d) id
  rw [← trim_relabel, relabel_apply_outside_both, outsideMap_id, ← converter]

omit [DecidableEq ι] [DecidableEq κ] in
/-- Each command's submitted value is unchanged by every address map. -/
lemma submitted_mapCommand
    -- `f` changes register addresses in the completed command history `h`.
    (f : ι → κ) (h : List (M.Command ι)) :
    M.submitted (h.map (M.mapCommand f)) = M.submitted h := by
  unfold submitted
  rw [List.findSome?_map]
  congr 1
  funext z
  obtain ⟨o | ρ | _, u⟩ := z <;> rfl

end Commons.AbstractModel

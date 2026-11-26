module

public import RandomSystems.Converter.ChronologicalLabeling.Sampling
public import Probability.List.Permutation
public import Probability.Permutation
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Chronological labels under a uniform permutation

`chronologicalLabelingProgram_uniform_mass_replies_eq_of_injOn` compares the coefficients of
chronological and evaluated inputs for one retained uniform permutation. List positions supply
an extending permutation; the retained-law theorem in `ChronologicalLabeling.Sampling` then
transports the complete reply event, including repeated queries.
-/

@[expose] public section

open Probability Probability.Distribution

namespace SystemAlgebra

-- `A` carries outside inputs; the finite alphabet `B` carries permutation labels and replies.
variable {A B : Type} [BEq A] [LawfulBEq A]
  -- The finite permutation alphabet uses the selected equality on `B`.
  [Fintype B] [DecidableEq B]

/-- A uniform retained permutation hides injective evaluation of the observed distinct inputs. -/
theorem chronologicalLabelingProgram_uniform_mass_replies_eq_of_injOn
    -- `labels` enumerates `B`; positions beyond this pool use `fallback`.
    (labels : Fin (Fintype.card B) ≃ B) (fallback : B)
    -- `E` and `F` are the inside and outside domains.
    {E : List (Σ _ : Unit, B) → Prop} {F : List (Σ _ : Unit, A) → Prop}
    -- `hE` and `hF` admit all nonempty prefixes and exclude the empty history.
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    -- `domain` certifies one inside call for each admitted outside input.
    (domain : IsDDCFrom E F 1
      (DDC.ofProgramOn [] (chronologicalLabelingProgram (C := B) labels fallback) F))
    -- `evaluate` interprets inputs; `us` is the fixed outside history.
    (evaluate : A → B) (us : List (Σ _ : Unit, A))
    -- `good` requires distinct evaluated values only for distinct inputs occurring in `us`.
    (good : Set.InjOn evaluate {a | a ∈ us.map Sigma.snd})
    -- `ys` retains every candidate reply, including replies on repeated inputs.
    (ys : List (Σ _ : Unit, B)) :
    (uniform (Equiv.Perm B)).mass (fun π => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels fallback) F)
      (DDS.ofFunction E hE (fun b => ⟨b.1, π b.2⟩)).1)) us ys) =
    (uniform (Equiv.Perm B)).mass (fun π =>
      Replies (DDS.ofFunction F hF (fun a => ⟨a.1, π (evaluate a.2)⟩)).1 us ys) := by
  classical
  let inputs := us.map Sigma.snd
  have distinctGood : Set.InjOn evaluate {a | a ∈ inputs.eraseDups} := by
    intro a ha b hb equal
    exact good (List.mem_eraseDups.mp ha) (List.mem_eraseDups.mp hb) equal
  -- Extend the two labelings of distinct observed inputs to one input permutation.
  obtain ⟨capacity, θ, agrees⟩ := List.exists_perm_apply_idxOf_eq inputs.eraseDups
    (List.nodup_eraseDups inputs) labels evaluate distinctGood
  -- First-occurrence positions stay fixed as the outside prefix grows.
  have aligned : ∀ vs a, vs ++ [⟨(), a⟩] <+: us → F (vs ++ [⟨(), a⟩]) →
      θ (if h : (vs.map Sigma.snd ++ [a]).eraseDups.idxOf a < Fintype.card B then
        labels ⟨(vs.map Sigma.snd ++ [a]).eraseDups.idxOf a, h⟩ else fallback) = evaluate a := by
    intro vs a preceding _
    have earlier : vs.map Sigma.snd ++ [a] <+: inputs := by
      simpa only [List.map_append, List.map_singleton] using preceding.map Sigma.snd
    have here : a ∈ (vs.map Sigma.snd ++ [a]).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_append_right _ (List.mem_singleton_self _))
    have there := earlier.eraseDups.subset here
    have rank := earlier.eraseDups.idxOf_eq_of_mem here
    have bound : (vs.map Sigma.snd ++ [a]).eraseDups.idxOf a < Fintype.card B := by
      rw [rank]; exact (List.idxOf_lt_length_of_mem there).trans_le capacity
    rw [dite_eq_left bound]
    exact (congrArg (fun n : Fin (Fintype.card B) => θ (labels n)) (Fin.ext rank)).trans
      (agrees a there)
  -- Reindex one retained uniform permutation; each query still reads that same draw.
  let μ := fTransform (fun π : Equiv.Perm B => (π : B → B)) (uniform (Equiv.Perm B))
  have invariant : fTransform (fun g => g ∘ θ) μ = μ := by
    calc
      _ = fTransform (fun π : Equiv.Perm B => (π : B → B))
          (fTransform (Equiv.mulRight θ) (uniform (Equiv.Perm B))) := by
            rw [fTransform_comp, fTransform_comp]; rfl
      _ = μ := by rw [fTransform_equiv_uniform]
  have equality := chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq
    labels fallback hE hF domain θ evaluate us aligned μ invariant ys
  dsimp only [μ] at equality
  rw [mass_fTransform, mass_fTransform] at equality
  exact equality

end SystemAlgebra

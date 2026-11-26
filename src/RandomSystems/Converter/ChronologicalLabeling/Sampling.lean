module

public import RandomSystems.Converter.ChronologicalLabeling.Laws
public import RandomSystems.System.Replies
public import Probability.Distribution

/-!
# Chronological labeling under a retained function law

`chronologicalLabelingProgram_replies_iff_of_prefix_alignment` compares chronological and
evaluated inputs on one history. Its one-call replay law supplies the deterministic comparison.
`chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq` then transports this comparison
through any retained function law invariant under the selected input map.

```text
outside a ── chronological label ── θ ── retained g ── reply
          = evaluated input a ────────── retained g ── reply
```
-/

@[expose] public section

open Probability Probability.Distribution

namespace SystemAlgebra

-- `A` carries outside inputs, `B` the finite labels, and `C` the forwarded replies.
variable {A B C : Type} [BEq A] [Fintype B]
  -- `labels` orders the label pool; exhausted fresh inputs use `fallback`.
  (labels : Fin (Fintype.card B) ≃ B) (fallback : B)
  -- `E` admits inside histories and `F` outside histories.
  {E : List (Σ _ : Unit, B) → Prop} {F : List (Σ _ : Unit, A) → Prop}
  -- `hE` and `hF` exclude empty histories and admit every nonempty prefix.
  (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
  -- `domain` certifies the encoder's one-call action from `E` to `F`.
  (domain : IsDDCFrom E F 1
    (DDC.ofProgramOn [] (chronologicalLabelingProgram (C := C) labels fallback) F))
  -- `θ` maps label inputs; `evaluate` maps the original outside inputs to inside inputs.
  (θ : B → B) (evaluate : A → B)
  -- `us` is the fixed outside history whose coefficient is compared.
  (us : List (Σ _ : Unit, A))
  -- `aligned` identifies the label mapped by `θ` with `evaluate a` at admitted prefixes of `us`.
  (aligned : ∀ vs a, vs ++ [⟨(), a⟩] <+: us → F (vs ++ [⟨(), a⟩]) →
    θ (if h : (vs.map Sigma.snd ++ [a]).eraseDups.idxOf a < Fintype.card B then
      labels ⟨(vs.map Sigma.snd ++ [a]).eraseDups.idxOf a, h⟩ else fallback) = evaluate a)

include domain aligned

/-- On the selected prefixes, input relabeling turns chronological replies into evaluation. -/
lemma chronologicalLabelingProgram_replies_iff_of_prefix_alignment
    -- `g` is retained across all calls; `ys` lists their candidate replies.
    (g : B → C) (ys : List (Σ _ : Unit, C)) :
    Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels fallback) F)
      (DDS.ofFunction E hE (fun b => ⟨b.1, g (θ b.2)⟩)).1)) us ys ↔
    Replies (DDS.ofFunction F hF (fun a => ⟨a.1, g (evaluate a.2)⟩)).1 us ys := by
  classical
  -- Every completed reply depends only on its input prefix.
  apply replies_congr_of_prefix
  intro p hp
  rcases List.eq_nil_or_concat p with rfl | ⟨vs, ⟨o, a⟩, rfl⟩
  · simp only [trim, reach_nil, ite_true, apply_eq, interconnect_nil]
    exact (Part.eq_none_iff'.mpr (DDS.ofFunction F hF
      (fun a => (⟨a.1, g (evaluate a.2)⟩ : Σ _ : Unit, C))).2.1).symm
  · cases o
    simp only [List.concat_eq_append] at hp ⊢
    -- The replay law keeps the original domain; alignment identifies its admitted reply.
    rw [chronologicalLabelingProgram_apply_ofFunction_snoc labels fallback hE hF domain
      (fun b => g (θ b)) vs a, DDS.ofFunction_snoc]
    by_cases legal : F (vs ++ [⟨(), a⟩])
    · simp only [legal, ↓reduceIte, aligned vs a hp legal]
    · simp only [legal, ↓reduceIte]

/-- A retained function law invariant under `g ↦ g ∘ θ` has equal transcript coefficients. -/
theorem chronologicalLabelingProgram_mass_replies_eq_of_fTransform_eq
    -- `μ` assigns finite signed weights to functions retained across all calls.
    (μ : Distribution (B → C))
    -- `invariant` says replacing `g` by `g ∘ θ` preserves this same retained law.
    (invariant : fTransform (fun g => g ∘ θ) μ = μ)
    -- `ys` is the fixed reply history, including any repeated replies.
    (ys : List (Σ _ : Unit, C)) :
    μ.mass (fun g => Replies (trim (apply
      (DDC.ofProgramOn [] (chronologicalLabelingProgram labels fallback) F)
      (DDS.ofFunction E hE (fun b => ⟨b.1, g b.2⟩)).1)) us ys) =
    μ.mass (fun g =>
      Replies (DDS.ofFunction F hF (fun a => ⟨a.1, g (evaluate a.2)⟩)).1 us ys) := by
  let event := fun g : B → C => Replies (trim (apply
    (DDC.ofProgramOn [] (chronologicalLabelingProgram labels fallback) F)
    (DDS.ofFunction E hE (fun b => ⟨b.1, g b.2⟩)).1)) us ys
  -- Reindex the retained draw, then use deterministic prefix agreement at each function.
  calc
    μ.mass event = (fTransform (fun g => g ∘ θ) μ).mass event := by rw [invariant]
    _ = μ.mass (fun g => event (g ∘ θ)) := mass_fTransform _ _ _
    _ = _ := mass_congr μ fun g =>
      chronologicalLabelingProgram_replies_iff_of_prefix_alignment
        labels fallback hE hF domain θ evaluate us aligned g ys

end SystemAlgebra

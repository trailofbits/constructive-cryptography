import RandomSystems.Converter.ParallelAllAttachment
import RandomSystems.Typed.ParallelAllPresentation

/-!
# Locality of independent n-ary attachment

`(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k)` for arbitrary typed converters and
resources. Both sides independently sample the same family of converter/resource pairs,
then use deterministic componentwise locality. A shared sample outside the whole family
stays outside this law.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” The explicit independent product supplies the stochastic law for
that view; Jost's locality does not itself assert independence of arbitrary resources.
-/

namespace SystemAlgebra.TypedConverter

open Probability Interface

variable {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}

open Classical in
/-- Independently composed converters attach componentwise to independently composed
resources. This is Jost's disjoint-interface locality (Thesis, printed p. 17), specialized
to the explicit independent stochastic products. -/
lemma parallelAll_attach (α : ∀ k, TypedConverter (A k) (B k))
    (R : ∀ k, TypedSystem (B k)) :
    (parallelAll α • TypedSystem.parallelAll R : TypedSystem (tensorAll A)) =
      TypedSystem.parallelAll (fun k => (α k • R k : TypedSystem (A k))) := by
  -- Choose presentations only for the proof; the endpoint is behavioral equality.
  let P := fun k => (α k).2.choose_spec.choose
  have hP := fun k => (α k).2.choose_spec.choose_spec
  let T := fun k => (R k).exists_ofPDS.choose
  have hT : R = fun k => TypedSystem.ofPDS (T k) :=
    funext fun k => (R k).exists_ofPDS.choose_spec.symm
  rw [hT]
  have haT : (fun k => (α k • TypedSystem.ofPDS (T k) : TypedSystem (A k))) =
      fun k => TypedSystem.ofPDS (attachPDS (A k).nonempty_prefix (P k) (T k)) := by
    funext k
    exact Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents (B k).nonempty_prefix (A k).nonempty_prefix (α k)
        (TypedSystem.ofPDS (T k)).1 (TypedSystem.ofPDS (T k)).2
        (P k) (T k) (hP k) (fun _ => rfl) h)
  rw [haT, TypedSystem.parallelAll_ofPDS, TypedSystem.parallelAll_ofPDS]
  -- Both sides are cumulative masses of deterministic attachments.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [smul_val, PDCBehavior.attach_presents (tensorAll B).nonempty_prefix
    (tensorAll A).nonempty_prefix (parallelAll α)
    (TypedSystem.ofPDS (TypedSystem.parallelAllPDS T)).1
    (TypedSystem.ofPDS (TypedSystem.parallelAllPDS T)).2
    (tensorAllPDC P) (TypedSystem.parallelAllPDS T)
    (fun h => (PDCBehavior.tensorAll_presents α P hP h).symm) (fun _ => rfl) h,
    behaviorMass_attachPDS]
  change _ = behaviorMass _ _ _
  simp only [behaviorMass, tensorAllPDC, TypedSystem.parallelAllPDS, attachPDS,
    Distribution.mass_fTransform, Distribution.fTransform_prod_left,
    Distribution.fTransform_prod_right]
  -- Regroup the independent samples into one converter/resource pair per component.
  rw [Distribution.independent_product_piDep, Distribution.mass_fTransform,
    ← Distribution.fTransform_piDep, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro p
  -- Deterministic locality preserves the complete outside transcript.
  exact iff_of_eq (congrArg (fun t => Replies t (h.map Prod.fst) (h.map Prod.snd))
    (trim_apply_tensorAllL_parAll (fun k => (p k).1.2.isDDC) (fun k => (p k).2.2.2.1)))

open Classical in
/-- Fixed-function realizations assemble by the same general stochastic locality law.
The component realization hypotheses retain their actual functional specifications. -/
lemma parallelAll_attach_ofFunction (α : ∀ k, TypedConverter (A k) (B k))
    (f : ∀ k i, (B k).X i → (B k).Y i)
    (g : ∀ k i, (A k).X i → (A k).Y i)
    (h : ∀ k, α k • TypedSystem.ofFunction (f k) = TypedSystem.ofFunction (g k)) :
    parallelAll α • TypedSystem.ofFunction (A := tensorAll B) (fun l x => f l.1 l.2 x) =
      TypedSystem.ofFunction (A := tensorAll A) (fun l x => g l.1 l.2 x) := by
  -- Assemble the component equalities at the attachment layer.
  rw [TypedSystem.ofFunction_parallelAll f, parallelAll_attach]
  simp only [h]
  exact (TypedSystem.ofFunction_parallelAll g).symm

end SystemAlgebra.TypedConverter

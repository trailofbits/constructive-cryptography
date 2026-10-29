import RandomSystems.Converter.ParallelAllAttachment
import RandomSystems.Typed.ParallelAllPresentation

/-!
# Componentwise attachment of independent families

For a finite family of typed converters `α k : TypedConverter (A k) (B k)` and typed systems
`R k : TypedSystem (B k)`,

  `(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k)`.

Both families are independent products: `⨂ₘ` and `∥` sample their components independently.
A sample shared by several components outside the family, as in `sample μ (c ↦ ∥ k, R c k)`,
is not of this form and stays outside the law.

```text
  (⨂ₘ k, α k) • (∥ k, R k)                  ∥ k, (α k • R k)
  ┌─────────────┐    ┌─────────────┐        ┌──────────────────────┐
  │ (a k)_k     │ ⇄  │ (r k)_k     │   =    │ (a k ⇄ r k)_k        │
  │ a k ← P k   │    │ r k ← T k   │        │ a k ← P k, r k ← T k │
  └─────────────┘    └─────────────┘        └──────────────────────┘
  all samples independent                   all samples independent
```

Proof: choose presentations `P k` of `α k` and `T k` of `R k`; regroup the two independent
families as one independent family of pairs; for each sampled pair family, deterministic
componentwise attachment (`trim_apply_tensorAllL_parAll`) gives the same outside replies.
Only cumulative behavior is compared.

## Main results

* `TypedConverter.parallelAll_attach`: `(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k)`
* `TypedConverter.parallelAll_attach_ofFunction`: the same for fixed-function realizations

Source: Jost, Thesis, printed p. 17, views finite disjoint-interface resources as one; the
stochastic law is derived here from the independent products.
-/

namespace SystemAlgebra.TypedConverter

open Probability Interface

variable {K : Type} [Fintype K] [DecidableEq K] {A B : K → Interface}

open Classical in
/-- **Componentwise attachment of independent families**:

  `(⨂ₘ k, α k) • (∥ k, R k) = ∥ k, (α k • R k)`.

Both families are independent products; a sample shared outside the family is not covered.
Jost, Thesis, printed p. 17, views finite disjoint-interface resources as one but states no
independence or locality law; this equation is derived from the chosen independent products
and the `Induces` semantics of attachment. -/
theorem parallelAll_attach (α : ∀ k, TypedConverter (A k) (B k))
    (R : ∀ k, TypedSystem (B k)) :
    (parallelAll α • TypedSystem.parallelAll R : TypedSystem (tensorAll A)) =
      TypedSystem.parallelAll (fun k => (α k • R k : TypedSystem (A k))) := by
  -- Proof chain on a transcript `h`, with `a ← piDep P`, `r ← piDep T`, `p ← piDep (P × T)`
  -- and `Rep S` the event that `S` replies `h`:
  --
  --   ((⨂ₘ α) • ∥ R)(h) = Pr_{(a, r)}[Rep (trim (apply (⨂ a) (∥ r)))]    presentations
  --                     = Pr_{p}[Rep (trim (apply (⨂ p.1) (∥ p.2)))]      regroup samples
  --                     = Pr_{p}[Rep (∥ k, trim (apply (p k).1 (p k).2))]  deterministic
  --                     = (∥ k, (α k • R k))(h)                            presentations
  --
  -- Choose presentations `P k` of `α k` and `T k` of `R k`, for the proof only.
  let P := fun k => (α k).2.choose_spec.choose
  have hP := fun k => (α k).2.choose_spec.choose_spec
  let T := fun k => (R k).exists_ofPDS.choose
  have hT : R = fun k => TypedSystem.ofPDS (T k) :=
    funext fun k => (R k).exists_ofPDS.choose_spec.symm
  rw [hT]
  -- Right side: `α k • R k` is presented by `attachPDS (P k) (T k)`, i.e. `a ← P k`,
  -- `r ← T k` independently, then attached; `∥` of PDSs is the PDS of the independent family.
  have haT : (fun k => (α k • TypedSystem.ofPDS (T k) : TypedSystem (A k))) =
      fun k => TypedSystem.ofPDS (attachPDS (A k).nonempty_prefix (P k) (T k)) := by
    funext k
    exact Subtype.ext (RandomSystem.ext fun h =>
      PDCBehavior.attach_presents (B k).nonempty_prefix (A k).nonempty_prefix (α k)
        (TypedSystem.ofPDS (T k)).1 (TypedSystem.ofPDS (T k)).2
        (P k) (T k) (hP k) (fun _ => rfl) h)
  rw [haT, TypedSystem.parallelAll_ofPDS, TypedSystem.parallelAll_ofPDS]
  -- Left side: `⨂ₘ α` is presented by `tensorAllPDC P` and `∥ R` by `parallelAllPDS T`, so the
  -- attachment is presented by `attachPDS` of the two; both sides are now masses of events.
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
  -- Regroup: `prod (piDep P) (piDep T)` is `piDep (k ↦ prod (P k) (T k))` pushed to the
  -- pair of families, and `piDep` of the component attachment laws is the pushforward of
  -- `piDep (k ↦ prod (P k) (T k))`. Both sides are masses over the same pair family `p`.
  rw [Distribution.independent_product_piDep, Distribution.mass_fTransform,
    ← Distribution.fTransform_piDep, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro p
  -- For fixed `p`, each `(p k).1` is a DDC and each `(p k).2` replies at its queried port, so
  -- `trim_apply_tensorAllL_parAll` equates the trimmed systems; they reply to the same `h`.
  exact iff_of_eq (congrArg (fun t => Replies t (h.map Prod.fst) (h.map Prod.snd))
    (trim_apply_tensorAllL_parAll (fun k => (p k).1.2.isDDC) (fun k => (p k).2.2.2.1)))

omit [DecidableEq K] in
open Classical in
/-- **Fixed-function realizations assemble componentwise**: if
`α k • ofFunction (f k) = ofFunction (g k)` for every `k`, then on `⨂ k, B k` and `⨂ k, A k`

  `(⨂ₘ k, α k) • ofFunction (⟨k, i⟩(x) ⇒ f k i x) = ofFunction (⟨k, i⟩(x) ⇒ g k i x)`. -/
lemma parallelAll_attach_ofFunction (α : ∀ k, TypedConverter (A k) (B k))
    (f : ∀ k i, (B k).X i → (B k).Y i)
    (g : ∀ k i, (A k).X i → (A k).Y i)
    (h : ∀ k, α k • TypedSystem.ofFunction (f k) = TypedSystem.ofFunction (g k)) :
    parallelAll α • TypedSystem.ofFunction (A := tensorAll B) (fun l x => f l.1 l.2 x) =
      TypedSystem.ofFunction (A := tensorAll A) (fun l x => g l.1 l.2 x) := by
  -- `ofFunction f̂ = ∥ k, ofFunction (f k)`, attach componentwise, rewrite each component by
  -- `h k`, and fold `∥ k, ofFunction (g k) = ofFunction ĝ`.
  rw [TypedSystem.ofFunction_parallelAll f, parallelAll_attach]
  simp only [h]
  exact (TypedSystem.ofFunction_parallelAll g).symm

end SystemAlgebra.TypedConverter

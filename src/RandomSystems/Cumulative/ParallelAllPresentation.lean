import Probability.DependentProduct
import RandomSystems.Cumulative.ParallelAll

/-!
# Presentations of finite parallel random systems

A presentation of `R k` is a finitely supported raw law `P k` on a sample carrier `ι k`
and a deterministic system `s k i` per sample, with
`R k h = (P k).mass {i | s k i answers h}`. Sampling the components independently,
`st ∼ piDep P`, and answering by `parAll (fun k => s k (st k))` presents
`RandomSystem.parallelAll R`:

  `(parallelAll R) h = (piDep P).mass {st | parAll (fun k => s k (st k)) answers h}`.

```text
  st = (st k)ₖ ∼ piDep P            (one independent sample per tag)

        k₁(x) ──▶ ┌──────────────┐
       k₁ ⇒ y ◀── │ s k₁ (st k₁) │   answers h|k₁
                  └──────────────┘
           ⋮              ⋮
        k₂(x') ─▶ ┌──────────────┐
      k₂ ⇒ y' ◀── │ s k₂ (st k₂) │   answers h|k₂
                  └──────────────┘
```

## Main results

* `RandomSystem.parallelAll_mass_of_presentations`: independent presentations present
  `parallelAll R`

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one”. `parallelAll` is this repository's independent specialization of
that view; the presentation law here is derived from it, not stated in the source.
-/

namespace SystemAlgebra.RandomSystem

open Probability

variable {K : Type} [Fintype K] [DecidableEq K]
  {A B : K → Type} [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
  {D : ∀ k, Domain (A k) (B k)}

/-- **Independent presentations present the n-ary product.** If every cumulative mass of
`R k` is the `P k`-mass of the samples `i` with `s k i` answering the transcript,
`R k h = (P k).mass {i | Replies (s k i) h}`, then

  `parallelAll R h = (piDep P).mass {st | Replies (parAll (fun k => s k (st k))) h}`.

Each `P k` is a raw `Distribution` on an arbitrary, possibly infinite carrier `ι k`, and the
`s k i` need not be DDSs. There is no separate nonnegativity, normalization or `ProbDist`
hypothesis; `hR` at `[]` gives `(P k).weight = R k [] = 1`, but `P k` may be signed when its
transcript-event masses match those of `R k`. `hR` fixes only the transcript events, so
presentations differing off the transcript tree are allowed.
The independence of the samples is the chosen product `piDep P`, matching the chosen product
formula of `parallelAll`; disjoint tags alone do not imply it.

Proof: `replies_parAll_iff` splits the joint event; `piDep_mass_forall` factors its mass. -/
lemma parallelAll_mass_of_presentations {ι : K → Type*}
    (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (P : ∀ k, Distribution (ι k)) (s : ∀ k, ι k → System (A k) (B k))
    (hR : ∀ k h, R k h = (P k).mass (fun i =>
      Replies (s k i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h = (Distribution.piDep P).mass (fun st =>
      Replies (parAll (fun k => s k (st k))) (h.map Prod.fst) (h.map Prod.snd)) := by
  -- Left: `[h consistent] · ∏ k, R k (h|k)`. Right, by `replies_parAll_iff`, the event
  --   {st | h consistent ∧ ∀ k, s k (st k) answers h|k}.
  rw [parallelAll_mass, Distribution.mass_congr (Distribution.piDep P)
    (fun st => replies_parAll_iff (fun k => s k (st k)) h)]
  by_cases hh : parallelAllConsistent h
  · -- Consistent `h`: the event is the rectangle `∀ k, st k ∈ {i | s k i answers h|k}`, so
    --   (piDep P).mass rectangle = ∏ k, (P k).mass {i | s k i answers h|k} = ∏ k, R k (h|k)
    -- by `piDep_mass_forall` and then `hR` at each `h|k`.
    simp only [hh, if_true, true_and]
    rw [Distribution.piDep_mass_forall P (fun k i =>
      Replies (s k i) ((restrictExchanges k h).map Prod.fst)
        ((restrictExchanges k h).map Prod.snd))]
    exact Finset.prod_congr rfl fun k _ => hR k _
  · -- Inconsistent `h`: the left side is `0`, and the event is empty, of mass `0`.
    simp only [hh, if_false, false_and]
    exact (Distribution.mass_eq_zero_of_forall_not _ (fun _ hf => hf)).symm

end SystemAlgebra.RandomSystem

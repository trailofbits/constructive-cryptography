import RandomSystems.Typed.Functional
import RandomSystems.Typed.Parallel

/-!
# Algebra of retained samples

An initial sample chooses the system used for the whole interaction. For normalized laws
`P` and `Q`, independent choices can be grouped or reordered while preserving that system:

```text
  k ← P, once ──┐
                ├──► retain R(k,l) for all queries
  l ← Q, once ──┘

  sample (P.prod Q) R = sample P (fun k => sample Q (fun l => R(k,l)))
```

`R` may use both samples. Independence concerns the initial laws: `Q` does not depend on
`k`. The laws may be nonuniform, and the sample types need not be finite; their supports are.

In a parallel system, a choice used only by the right component can be sampled outside:

```text
       R ∥ sample P S                  sample P (fun k => R ∥ S k)
  ┌────────┬─────────────────┐       ┌─────────────────────────┐
  │   R    │ k ← P, once     │   =   │ k ← P, once             │
  │        │ retain S k      │       │ retain R ∥ S k          │
  └────────┴─────────────────┘       └─────────────────────────┘
```

The left system `R` is fixed independently of the initial draw and may itself be stochastic.
Sampling adds no input carrying `k` to `R`; an environment may still adapt its queries to
either component's replies.

## Main results and proof

* `sample_prod`: compare cumulative probabilities on each transcript, then use
  `Distribution.sum_prod_mul` to split the product-weighted sum.
* `sample_comm`: regroup with `sample_prod`, swap the product coordinates using
  `Distribution.fTransform_swap_prod`, and carry that swap through `sample_fTransform`.
* `parallel_sample_right`: `parallel_mass` expresses the typed system on its underlying
  transcript; `RandomSystem.parallel_mix_right` supplies the mixture identity there.
-/

namespace SystemAlgebra.TypedSystem

open Probability

/-- **Grouping independent initial choices**: sampling a pair from `P.prod Q` is sampling
`k` from `P` and `l` from the fixed law `Q`, then retaining `R (k, l)`. The component system
may depend on both values; normalization makes each sampling operation a typed system. -/
lemma sample_prod {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem A) :
    TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => R (k, l))) := by
  -- Equality of typed systems is equality of their cumulative probabilities on every transcript.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- Both probabilities average the same component mass, with weight P(k) · Q(l).
  exact Distribution.sum_prod_mul P Q (fun kl => (R kl).1 h)

/-- **Reordering independent initial choices** preserves the system, even when `R` uses
both values. The law `Q` is fixed independently of `k`; this is not a rule for exchanging
a draw with a later draw whose law depends on it. -/
lemma sample_comm {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K → L → TypedSystem A) :
    TypedSystem.sample P (fun k => TypedSystem.sample Q (R k)) =
      TypedSystem.sample Q (fun l => TypedSystem.sample P (fun k => R k l)) := by
  -- Group the first order into a single product draw.
  calc
    _ = TypedSystem.sample (P.prod Q) (fun kl => R kl.1 kl.2) := (sample_prod P Q _).symm
    -- Swapping the product coordinates preserves which value is passed to each argument of R.
    _ = TypedSystem.sample (Q.prod P) (fun lk => R lk.2 lk.1) := by
      simpa only [Distribution.fTransform_swap_prod, Prod.swap] using
        (sample_fTransform (P.prod Q) Prod.swap (fun lk => R lk.2 lk.1)).symm
    -- Split the swapped product into the opposite sampling order.
    _ = _ := sample_prod Q P _

/-- **Moving a right-side initial choice outside parallel composition** preserves the
system: both sides retain one draw from `P` and use it only in `S k`. The same left system
`R` is used for every `k`, with its own randomness independent of the initial draw. -/
lemma parallel_sample_right {A B : Interface} {K : Type}
    (R : TypedSystem A) (P : Distribution K) [Distribution.IsProbability P]
    (S : K → TypedSystem B) :
    parallel R (TypedSystem.sample P S) =
      TypedSystem.sample P (fun k => parallel R (S k)) := by
  -- Compare the cumulative probabilities of the same typed transcript.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- The typed parallel law performs the common alphabet conversion on both sides.
  rw [parallel_mass, sample_mass, TypedSystem.sample, RandomSystem.parallel_mix_right,
    RandomSystem.mix_mass]
  simp only [parallel_mass]

end SystemAlgebra.TypedSystem

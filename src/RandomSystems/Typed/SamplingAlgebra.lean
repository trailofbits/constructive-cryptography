import RandomSystems.Typed.Functional
import RandomSystems.Typed.Parallel

/-!
# Algebra of retained samples

`TypedSystem.sample P R` draws `k ← P` once, before the first query, and answers every query
with the same system `R k`. For normalized laws `P` and `Q` on possibly infinite types (their
supports are finite), independent initial draws can be grouped, reordered, and moved out of a
parallel composition. `Q` is fixed independently of `k`; the retained system may use both values.
These are consequences of the product law of finite-support distributions and of the cumulative
mixture semantics of `sample`.

```text
     A ┌──────────────────────┐              A ┌─────────────┐
  ─────┤ (k, l) ← P × Q, once │     =     ─────┤ k ← P, once │
       │ R (k, l)             │                │ l ← Q, once │
       └──────────────────────┘                │ R (k, l)    │
                                               └─────────────┘
```

## Main results

* `sample_prod`: a product draw is two successive independent draws
* `sample_comm`: two independent draws may be taken in either order
* `parallel_sample_right`: a draw used only by the right component of `R ∥ sample P S` is
  taken outside the parallel composition
-/

namespace SystemAlgebra.TypedSystem

open Probability

/-- **Grouping independent initial draws**: drawing `(k, l) ← P × Q` once is drawing `k ← P`,
then `l` from the fixed law `Q`, and retaining `R (k, l)`; `R` may depend on both values. At
every transcript `h`, `∑_{(k,l)} P(k) Q(l) · R(k,l)(h) = ∑_k P(k) · ∑_l Q(l) · R(k,l)(h)`. -/
lemma sample_prod {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K × L → TypedSystem A) :
    TypedSystem.sample (P.prod Q) R =
      TypedSystem.sample P (fun k => TypedSystem.sample Q (fun l => R (k, l))) := by
  -- Typed systems are equal when their cumulative probabilities agree at every transcript `h`.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- The product weight `P(k) Q(l)` splits the sum into an iterated sum.
  exact Distribution.sum_prod_mul P Q (fun kl => (R kl).1 h)

/-- **Reordering independent initial draws**: drawing `k ← P` then `l ← Q` and retaining
`R k l` is drawing them in the opposite order, even when `R` uses both values. The law `Q` is
fixed independently of `k`; a draw whose law depends on an earlier draw is not covered. -/
lemma sample_comm {A : Interface} {K L : Type}
    (P : Distribution K) [Distribution.IsProbability P]
    (Q : Distribution L) [Distribution.IsProbability Q]
    (R : K → L → TypedSystem A) :
    TypedSystem.sample P (fun k => TypedSystem.sample Q (R k)) =
      TypedSystem.sample Q (fun l => TypedSystem.sample P (fun k => R k l)) := by
  -- `P` then `Q`  =  `P × Q`  =  `Q × P` (pushforward by swap)  =  `Q` then `P`.
  -- Group the first order into a single product draw.
  calc
    _ = TypedSystem.sample (P.prod Q) (fun kl => R kl.1 kl.2) := (sample_prod P Q _).symm
    -- `swap(P × Q) = Q × P`, and `sample_fTransform` retains `R` at the swapped-back pair.
    _ = TypedSystem.sample (Q.prod P) (fun lk => R lk.2 lk.1) := by
      simpa only [Distribution.fTransform_swap_prod, Prod.swap] using
        (sample_fTransform Prod.swap (P.prod Q) (fun lk => R lk.2 lk.1)).symm
    -- Split the swapped product into the opposite sampling order.
    _ = _ := sample_prod Q P _

/-- **A right-side initial draw moves outside parallel composition**: both sides draw `k ← P`
once and use it only in `S k`. The left system `R` is the same for every `k` and may be
stochastic; the environment may still adapt its queries at `A` to replies at `B` and back.

```text
     A ┌─────────────┐                 A ┌─────────────┐
  ─────┤ R           │              ─────┤ k ← P, once │
       └─────────────┘        =          │             │
     B ┌─────────────┐                 B │ R ∥ S k     │
  ─────┤ k ← P, once │              ─────┤             │
       │ S k         │                   └─────────────┘
       └─────────────┘
``` -/
lemma parallel_sample_right {A B : Interface} {K : Type}
    (R : TypedSystem A) (P : Distribution K) [Distribution.IsProbability P]
    (S : K → TypedSystem B) :
    parallel R (TypedSystem.sample P S) =
      TypedSystem.sample P (fun k => parallel R (S k)) := by
  -- Compare the cumulative probabilities at every transcript `h` of `tensor A B`.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  -- On the untyped parallel composition, `R ∥ ∑_k P(k) S_k = ∑_k P(k) (R ∥ S_k)`
  -- (`RandomSystem.parallel_mix_right`).
  rw [parallel_mass, sample_mass, TypedSystem.sample, RandomSystem.parallel_mix_right,
    RandomSystem.mix_mass]
  -- Each summand is the typed parallel mass of `R ∥ S k` at `h`.
  simp only [parallel_mass]

end SystemAlgebra.TypedSystem

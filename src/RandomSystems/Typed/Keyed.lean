module

public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.Functional

/-!
# Keyed reply laws

`TypedSystem.keyed P ν` draws one parameter `k ∼ P` and retains it. Each query `i(x)`
then receives a fresh reply from `ν k i x`. The ports share `k`; their reply draws are
independent conditional on `k`.

`keyed_snoc` gives the cumulative reply equation, averaging each fixed-key history and
its next reply over the same key. `keyed_single` specializes to deterministic keyed functions.
`keyed_snoc_snoc_eq_of_support` transfers a fixed-key support implication to cumulative
probabilities: a first reply that forces the next reply makes that next exchange preserve the
prefix mass. These laws reuse `sample` and `ofMemoryless` on the declared domain.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution RandomSystem

-- `A` fixes the ports, query/reply types and admitted input histories; `K` carries retained keys.
variable {A : Interface} {K : Type}

/-- Draw `k ∼ P` once; on each admitted query `i(x)`, draw `y ∼ ν k i x` freshly.
For each fixed key, the replies use a “discrete memoryless channel” [1, §3.6.1, p. 65]. -/
noncomputable def keyed
    -- `P` is the key law; every port uses the same sampled `k : K`.
    (P : ProbDist K)
    -- `ν k i x` is the reply law at port `i` on query `x`, with retained key `k`.
    (ν : K → ∀ i, A.X i → ProbDist (A.Y i)) : TypedSystem A :=
  TypedSystem.sample P fun k => ofMemoryless A (ν k)

/-- For `R = keyed P ν` and `Rₖ = ofMemoryless A (ν k)`,
`R(h) = ∑ k ∈ supp P, P(k) Rₖ(h)`. -/
lemma keyed_mass
    -- `P` gives the retained key; `ν k i x` gives its fresh reply law at query `i(x)`.
    (P : ProbDist K) (ν : K → ∀ i, A.X i → ProbDist (A.Y i))
    -- `h` lists the past queries and their port-tagged replies.
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (keyed P ν).1 h = ∑ k ∈ P.1.support, P k * (ofMemoryless A (ν k)).1 h :=
  sample_mass (K := K) P _ h

/-- For an admitted next query `i(x)`,
`R(h ++ [(i(x), i(y))]) = ∑ k ∈ supp P, P(k) Rₖ(h) ν(k,i,x)(y)`,
where `R = keyed P ν` and `Rₖ = ofMemoryless A (ν k)`. -/
lemma keyed_snoc
    -- `P` is sampled once; `ν k` supplies fresh replies conditional on that key.
    (P : ProbDist K) (ν : K → ∀ i, A.X i → ProbDist (A.Y i))
    -- `h` is the past transcript; `i(x)` is the next query and `y` its reply at port `i`.
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) (i : A.I) (x : A.X i) (y : A.Y i)
    -- `hd` admits this query after the inputs of `h`.
    (hd : A.inputDomain h ⟨i, x⟩) :
    (keyed P ν).1 (h ++ [(⟨i, x⟩, ⟨i, y⟩)]) =
      ∑ k ∈ P.1.support, P k * (ofMemoryless A (ν k)).1 h * (ν k i x) y := by
  -- Expand the key average, then apply the fixed-key chain rule to each summand.
  rw [keyed_mass]
  apply Finset.sum_congr rfl
  intro k _
  rw [ofMemoryless_val, memoryless_snoc, ite_eq_left hd, portLaw_apply_mk, mul_assoc]

/-- If `y ∈ supp (ν k i x)` implies `ν k j x' y' = 1` for every `k ∈ supp P`, then
`R(h ++ [i(x) → y] ++ [j(x') → y']) = R(h ++ [i(x) → y])`, where `R = keyed P ν`. -/
lemma keyed_snoc_snoc_eq_of_support
    -- `P` retains one key; `ν k i x` supplies fresh replies conditional on that key.
    (P : ProbDist K) (ν : K → ∀ i, A.X i → ProbDist (A.Y i))
    -- `h` is the prior transcript; the two exchanges are `i(x) → y` and `j(x') → y'`.
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (i : A.I) (x : A.X i) (y : A.Y i) (j : A.I) (x' : A.X j) (y' : A.Y j)
    -- `hd`, `hd'` admit the successive queries after `h` and `h ++ [i(x) → y]` in `A`.
    (hd : A.inputDomain h ⟨i, x⟩)
    (hd' : A.inputDomain (h ++ [(⟨i, x⟩, ⟨i, y⟩)]) ⟨j, x'⟩)
    -- `hreply`: for `k ∈ supp P`, support of `y` under `ν k i x` gives unit mass to `y'`.
    (hreply : ∀ k ∈ P.1.support, y ∈ (ν k i x).1.support → (ν k j x') y' = 1) :
    (keyed P ν).1 ((h ++ [(⟨i, x⟩, ⟨i, y⟩)]) ++ [(⟨j, x'⟩, ⟨j, y'⟩)]) =
      (keyed P ν).1 (h ++ [(⟨i, x⟩, ⟨i, y⟩)]) := by
  -- Average both histories over the same retained key, then use the fixed-key chain rule.
  rw [keyed_mass, keyed_mass]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1
  rw [ofMemoryless_val, memoryless_snoc, ite_eq_left hd', portLaw_apply_mk]
  by_cases hy : y ∈ (ν k i x).1.support
  · -- A supported first reply gives unit probability to the specified next reply.
    rw [hreply k hk hy, mul_one]
  · -- An unsupported first reply already makes the prefix probability zero.
    rw [memoryless_snoc, ite_eq_left hd, portLaw_apply_mk, Finsupp.notMem_support_iff.mp hy]
    simp only [mul_zero, zero_mul]

/-- Point-mass reply laws retain one keyed function: every query returns `f k i x`. -/
lemma keyed_single
    -- `P` gives the retained key; `f k i x` is its deterministic answer at query `i(x)`.
    (P : ProbDist K) (f : K → ∀ i, A.X i → A.Y i) :
    keyed P (fun k i x => ProbDist.single (f k i x)) =
      TypedSystem.sample P (fun k => ofFunction (f k)) := rfl

end SystemAlgebra.TypedSystem

module

public import RandomSystems.Typed.ParallelAll
public import RandomSystems.Typed.Memoryless

/-!
# Finite families of memoryless systems

`parallelAll_ofMemoryless` identifies the independent family `∥ k, ofMemoryless (B k) (ν k)`
with the memoryless law `ν k i x` at its tagged port `⟨k, i⟩`. Its domain is exactly
`tensorAll B`: it admits the nonempty input histories whose component projections are each
empty or admitted. The family may be empty.

For a nonzero transcript, `parallelAll_admits_iff` transfers the next query's domain guarantee
to the selected component. That component's memoryless chain rule multiplies its factor in
`parallelAll_mass` by the next-reply probability; every other factor stays unchanged.
A zero-mass prefix keeps mass zero, so the equality holds at every transcript.

The component laws are the “discrete memoryless channel” of [1, §3.6.1, p. 65], repeated
with fresh replies. The independent `parallelAll` specializes the finite-interface
view of [2, p. 17]: “A finite set of resources with disjoint interface sets can be viewed
as a single one”.

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis,
   Diss. ETH No. 26723, ETH Zurich, 2020.
-/

@[expose] public section

open Probability Probability.Distribution
open SystemAlgebra.RandomSystem
open scoped SystemAlgebra

namespace SystemAlgebra.TypedSystem

/-- An independent finite family of memoryless components uses the queried component's reply law. -/
theorem parallelAll_ofMemoryless
    -- `K` indexes the finite family, possibly empty.
    -- `B k` fixes the component's ports, query/reply types and admitted input histories.
    {K : Type} [Fintype K] [DecidableEq K] {B : K → Interface}
    -- `ν k i x` is the fresh reply law of component `k` at its local port `i` on query `x`.
    (ν : ∀ k i, (B k).X i → ProbDist ((B k).Y i)) :
    (∥ k, ofMemoryless (B k) (ν k)) =
      ofMemoryless (Interface.tensorAll B) (fun l x => ν l.1 l.2 x) := by
  classical
  let R : ∀ k, TypedSystem (B k) := fun k => ofMemoryless (B k) (ν k)
  apply Subtype.ext
  change (parallelAll R).1 = memoryless (Interface.tensorAll B).inputDomain
    (portLaw (fun l x => ν l.1 l.2 x))
  -- It suffices to multiply each admitted transcript mass by its next-reply law.
  refine eq_memoryless_of_snoc fun h x y hd => ?_
  -- An impossible prefix remains impossible after the next exchange.
  by_cases hz : (parallelAll R).1 h = 0
  · rw [hz, zero_mul]
    exact (parallelAll R).1.mass_eq_zero_of_prefix (List.prefix_append _ _) hz
  -- Replies at a different full port have zero mass on both sides.
  by_cases hy : y.1 = x.1
  swap
  · rw [(parallelAll R).2 h x y hy, portLaw_apply_of_ne _ hy, mul_zero]
  obtain ⟨⟨k, i⟩, x⟩ := x
  obtain ⟨l, y⟩ := y
  cases hy
  rw [portLaw_apply_mk]
  -- Regroup the typed ports to the component-tagged alphabets of the cumulative product.
  let eX := Equiv.sigmaAssoc fun k i => (B k).X i
  let eY := Equiv.sigmaAssoc fun k i => (B k).Y i
  let h' := h.map (eX.prodCongr eY)
  have hp : RandomSystem.parallelAll (fun k => (R k).1) h' ≠ 0 := hz
  -- Positive mass transfers admission to component `k`, on its own projected history.
  have hadm := (parallelAll_admits_iff R h' hp ⟨k, ⟨i, x⟩⟩).mpr (by
    have hround : (h'.map Prod.fst).map eX.symm = h.map Prod.fst := by
      simp only [h', List.map_map]
      exact List.map_congr_left fun z _ => eX.symm_apply_apply z.1
    change parallelAllInputs (fun k => (B k).domain)
      ((h'.map Prod.fst).map eX.symm ++ [eX.symm ⟨k, ⟨i, x⟩⟩])
    rw [hround]
    exact hd)
  -- Expand the product and separate the queried component from all other factors.
  rw [parallelAll_mass, parallelAll_mass, List.map_append, List.map_singleton]
  change RandomSystem.parallelAll (fun k => (R k).1)
      (h' ++ [(⟨k, ⟨i, x⟩⟩, ⟨k, ⟨i, y⟩⟩)]) =
    RandomSystem.parallelAll (fun k => (R k).1) h' * (ν k i x).1 y
  rw [RandomSystem.parallelAll_mass, RandomSystem.parallelAll_mass,
    ite_eq_left (parallelAllConsistent_snoc.mpr ⟨hadm.1, rfl⟩), ite_eq_left hadm.1,
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k),
    ← Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  -- The queried projection gains this exchange, so its mass obeys the memoryless chain rule.
  have hself : restrictExchanges k (h' ++ [(⟨k, ⟨i, x⟩⟩, ⟨k, ⟨i, y⟩⟩)]) =
      restrictExchanges k h' ++ [(⟨i, x⟩, ⟨i, y⟩)] := by
    simp only [restrictExchanges, List.filterMap_append, ↓reduceDIte,
      Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil]
  rw [hself]
  change _ * memoryless (B k).inputDomain (portLaw (ν k))
      (restrictExchanges k h' ++ [(⟨i, x⟩, ⟨i, y⟩)]) = _
  rw [memoryless_snoc, ite_eq_left hadm.2.2, portLaw_apply_mk]
  -- Every other projection is unchanged; reassemble the original product and the reply factor.
  have hother : ∀ j ∈ Finset.univ.erase k,
      restrictExchanges j (h' ++ [(⟨k, ⟨i, x⟩⟩, ⟨k, ⟨i, y⟩⟩)]) =
        restrictExchanges j h' := by
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    simp only [restrictExchanges, List.filterMap_append, Ne.symm hne, ↓reduceDIte,
      List.filterMap_cons_none, List.filterMap_nil, List.append_nil]
  rw [Finset.prod_congr rfl (fun j hj => congrArg (R j).1 (hother j hj)), mul_assoc]
  rfl

end SystemAlgebra.TypedSystem

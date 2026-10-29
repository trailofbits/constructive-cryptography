import RandomSystems.Cumulative.ParallelAll

/-!
# The two-component view of a parallel family

A family `R : ∀ k : Option Unit, RandomSystem (A k) (B k) (D k)` has two components. Its
n-ary independent product and the binary product of `R none` and `R (some ())` live on
different alphabet types, `Σ k, A k` and `Two (A none) (A (some ()))`; the explicit
equivalence `optionPair` relates them, and on corresponding transcripts

  `parallelAll R h = parallel (R none) (R (some ())) (h.map (optionPair A × optionPair B))`.

## Main definitions

* `optionPair A`: `(Σ k : Option Unit, A k) ≃ Two (A none) (A (some ()))`

## Main results

* `RandomSystem.optionPair_transcripts`: regrouping preserves consistency and both projections
* `RandomSystem.parallelAll_option_mass`: the n-ary product of two is the binary product
-/

namespace SystemAlgebra


open Classical in
/-- An `Option Unit`-tagged alphabet as a pair of alphabets: `⟨none, a⟩ ↦ ⟨none, a⟩`,
`⟨some (), a⟩ ↦ ⟨some (), a⟩`, an explicit equivalence between the two types. -/
def optionPair (A : Option Unit → Type) : (Σ k, A k) ≃ Two (A none) (A (some ())) where
  toFun
    | ⟨none, a⟩ => ⟨none, a⟩
    | ⟨some (), a⟩ => ⟨some (), a⟩
  invFun
    | ⟨none, a⟩ => ⟨none, a⟩
    | ⟨some (), a⟩ => ⟨some (), a⟩
  left_inv := by rintro ⟨(_ | ⟨⟨⟩⟩), a⟩ <;> rfl
  right_inv := by rintro ⟨(_ | ⟨⟨⟩⟩), a⟩ <;> rfl

namespace RandomSystem

variable {A B : Option Unit → Type}

open Classical in
/-- With `h' = h.map (optionPair A × optionPair B)`: `parallelConsistent h' ↔
parallelAllConsistent h`, `parallelLeft h' = h|none` and `parallelRight h' = h|some ()`. -/
lemma optionPair_transcripts (h : List ((Σ k, A k) × (Σ k, B k))) :
    (parallelConsistent (h.map ((optionPair A).prodCongr (optionPair B))) ↔
      parallelAllConsistent h) ∧
    parallelLeft (h.map ((optionPair A).prodCongr (optionPair B))) =
      restrictExchanges none h ∧
    parallelRight (h.map ((optionPair A).prodCongr (optionPair B))) =
      restrictExchanges (some ()) h := by
  -- `optionPair` keeps each tag and value, so an exchange is consistent (input and reply
  -- tags equal) and kept by a projection in one view iff in the other. Each part splits on
  -- the input and reply tags, four cases.
  refine ⟨?_, ?_, ?_⟩
  · simp only [parallelConsistent, parallelAllConsistent, List.forall_mem_map]
    apply forall_congr'
    intro z
    apply imp_congr_right
    intro _
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), x⟩, ⟨(_ | ⟨⟨⟩⟩), y⟩⟩ <;> rfl
  · rw [parallelLeft, List.filterMap_map, restrictExchanges]
    apply List.filterMap_congr
    intro z _
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), x⟩, ⟨(_ | ⟨⟨⟩⟩), y⟩⟩ <;>
      simp only [optionPair, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
        Prod.map_apply, ↓reduceDIte, reduceCtorEq]
  · rw [parallelRight, List.filterMap_map, restrictExchanges]
    apply List.filterMap_congr
    intro z _
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), x⟩, ⟨(_ | ⟨⟨⟩⟩), y⟩⟩ <;>
      simp only [optionPair, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
        Prod.map_apply, ↓reduceDIte, reduceCtorEq]

open Classical in
/-- **The n-ary product of two components is the binary product**, after the explicit
regrouping:

  `parallelAll R h = parallel (R none) (R (some ())) (h.map (optionPair A × optionPair B))`.

Both sides are `R none (h|none) · R (some ()) (h|some ())` on consistent `h`, `0` otherwise. -/
lemma parallelAll_option_mass [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
    {D : ∀ k, Domain (A k) (B k)} (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h = parallel (R none) (R (some ()))
      (h.map ((optionPair A).prodCongr (optionPair B))) := by
  -- `∏ k : Option Unit, R k (h|k) = R none (h|none) * R (some ()) (h|some ())`, and the
  -- binary consistency and projections are those of `h` by `optionPair_transcripts`.
  obtain ⟨hc, hl, hr⟩ := optionPair_transcripts h
  rw [parallelAll_mass, parallel_mass, hc, hl, hr]
  simp only [Fintype.prod_option, Fintype.prod_unique]

end RandomSystem
end SystemAlgebra

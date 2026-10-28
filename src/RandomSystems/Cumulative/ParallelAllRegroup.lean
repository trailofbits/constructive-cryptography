import RandomSystems.Cumulative.ParallelAll

/-!
# The two-component view of a parallel family

The equivalence below makes the alphabet regrouping explicit. On the corresponding
transcripts, the n-ary and binary independent products have exactly the same cumulative
mass. Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets
can be viewed as a single one.” Binary composition is its two-component specialization.
-/

namespace SystemAlgebra


open Classical in
/-- The two tags of an option-indexed family, viewed as a pair of alphabets. -/
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
/-- Regrouping does not change consistency or either component transcript. -/
lemma optionPair_transcripts (h : List ((Σ k, A k) × (Σ k, B k))) :
    (parallelConsistent (h.map ((optionPair A).prodCongr (optionPair B))) ↔
      parallelAllConsistent h) ∧
    parallelLeft (h.map ((optionPair A).prodCongr (optionPair B))) =
      restrictExchanges none h ∧
    parallelRight (h.map ((optionPair A).prodCongr (optionPair B))) =
      restrictExchanges (some ()) h := by
  -- Each exchange keeps its tag and value; cross-tag replies are rejected in both views.
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
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), x⟩, ⟨(_ | ⟨⟨⟩⟩), y⟩⟩ <;> simp [optionPair]
  · rw [parallelRight, List.filterMap_map, restrictExchanges]
    apply List.filterMap_congr
    intro z _
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), x⟩, ⟨(_ | ⟨⟨⟩⟩), y⟩⟩ <;> simp [optionPair]

open Classical in
/-- The binary independent product is the two-component n-ary product after explicit
alphabet regrouping. -/
lemma parallelAll_option_mass [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
    {D : ∀ k, Domain (A k) (B k)} (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h = parallel (R none) (R (some ()))
      (h.map ((optionPair A).prodCongr (optionPair B))) := by
  -- Factor the two-coordinate product and identify its two projected histories.
  obtain ⟨hc, hl, hr⟩ := optionPair_transcripts h
  rw [parallelAll_mass, parallel_mass, hc, hl, hr]
  simp only [Fintype.prod_option, Fintype.prod_unique]

end RandomSystem
end SystemAlgebra

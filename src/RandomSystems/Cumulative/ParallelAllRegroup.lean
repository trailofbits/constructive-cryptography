module

public import RandomSystems.Cumulative.ParallelAllRegroup.Defs

/-!
# Reindexing and splitting finite parallel systems

The independent product `parallelAll R` is invariant under an explicit bijection of its
family indices (`parallelAll_sigmaCongrLeft_mass`). A family over `Option J` splits into
its `none` component beside the remaining family (`parallelAll_optionSplit_mass`).

The proofs identify the projected transcripts and their consistency conditions before
reindexing or splitting the finite product of component probabilities. `optionSplit` is
owned by `ParallelAllRegroup.Defs`; `optionPair` retains the two-component presentation.
-/

@[expose] public section

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

section OptionSplit

variable {J : Type} {A B : Option J → Type}

open Classical in
/-- The left part of a split transcript is its projection at `none`. -/
lemma optionSplit_left (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelLeft (h.map ((optionSplit A).prodCongr (optionSplit B))) =
      restrictExchanges none h := by
  rw [parallelLeft, List.filterMap_map, restrictExchanges]
  apply List.filterMap_congr
  intro z _
  rcases z with ⟨⟨(_ | j), x⟩, ⟨(_ | j'), y⟩⟩ <;>
    simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
      Prod.map_apply, ↓reduceDIte, reduceCtorEq]

open Classical in
/-- The projection at `j` of the right part of a split transcript is its projection at
`some j`. -/
lemma optionSplit_right (h : List ((Σ k, A k) × (Σ k, B k))) (j : J) :
    restrictExchanges j (parallelRight (h.map ((optionSplit A).prodCongr (optionSplit B)))) =
      restrictExchanges (some j) h := by
  rw [parallelRight, restrictExchanges, restrictExchanges, List.filterMap_filterMap,
    List.filterMap_map]
  apply List.filterMap_congr
  intro z _
  rcases z with ⟨⟨(_ | j₁), x⟩, ⟨(_ | j₂), y⟩⟩
  · simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
    Prod.map_apply, Option.bind_none, reduceCtorEq, ↓reduceDIte]
  · simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
    Prod.map_apply, Option.bind_none, reduceCtorEq, ↓reduceDIte]
  · simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
    Prod.map_apply, Option.bind_none, Option.some.injEq, reduceCtorEq, ↓reduceDIte,
    dite_eq_ite, ite_self]
  · by_cases h₁ : j₁ = j
    · subst h₁
      by_cases h₂ : j₂ = j₁
      · subst h₂
        simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
          Prod.map_apply, Option.bind_some, ↓reduceDIte]
      · simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
        Prod.map_apply, Option.bind_some, ↓reduceDIte, h₂, Option.some.injEq]
    · simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Function.comp_apply,
      Prod.map_apply, Option.bind_some, h₁, ↓reduceDIte, Option.some.injEq]

open Classical in
/-- A transcript is tag consistent iff its split is, and so is the split's right part. -/
lemma optionSplit_consistent (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAllConsistent h ↔
      parallelConsistent (h.map ((optionSplit A).prodCongr (optionSplit B))) ∧
        parallelAllConsistent
          (parallelRight (h.map ((optionSplit A).prodCongr (optionSplit B)))) := by
  simp only [parallelAllConsistent, parallelConsistent, parallelRight, List.forall_mem_map,
    List.mem_filterMap, forall_exists_index, and_imp]
  constructor
  · intro hc
    refine ⟨fun z hz => ?_, fun w z hz hw => ?_⟩
    · have h1 := hc z hz
      rcases z with ⟨⟨(_ | j₁), x⟩, ⟨(_ | j₂), y⟩⟩ <;>
        simp_all only [Prod.forall, optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk,
        Prod.map_apply, reduceCtorEq, Option.some.injEq]
    · have h1 := hc z hz
      rcases z with ⟨⟨(_ | j₁), x⟩, ⟨(_ | j₂), y⟩⟩ <;>
        simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Prod.map_apply,
        reduceCtorEq, Option.some.injEq] at hw h1
      subst hw
      exact h1
  · rintro ⟨hl, hr⟩ z hz
    rcases z with ⟨⟨(_ | j₁), x⟩, ⟨(_ | j₂), y⟩⟩
    · rfl
    · have h1 := hl _ hz
      simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Prod.map_apply,
        reduceCtorEq] at h1
    · have h1 := hl _ hz
      simp only [optionSplit, Equiv.prodCongr_apply, Equiv.coe_fn_mk, Prod.map_apply,
        reduceCtorEq] at h1
    · exact congrArg some (hr _ _ hz rfl)

open Classical in
/-- **The n-ary product over `Option J` is the binary product** of the component at `none` and
the product over `J`, on the split transcript. -/
lemma parallelAll_optionSplit_mass [Fintype J] [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
    {D : ∀ k, Domain (A k) (B k)} (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k, A k) × (Σ k, B k))) :
    parallelAll R h = parallel (R none) (parallelAll fun j => R (some j))
      (h.map ((optionSplit A).prodCongr (optionSplit B))) := by
  rw [parallelAll_mass, parallel_mass, parallelAll_mass, optionSplit_left, Fintype.prod_option]
  simp only [optionSplit_right, optionSplit_consistent h]
  split_ifs <;> simp_all only [Equiv.prodCongr_apply, not_true_eq_false, not_and, not_false_eq_true,
    mul_zero]

end OptionSplit

section Reindex

variable {K K' : Type} [Fintype K] [Fintype K'] (e : K' ≃ K) {A B : K → Type}

omit [Fintype K] [Fintype K'] in
open Classical in
/-- **A projection after reindexing** is the projection at the image index. -/
lemma restrictExchanges_sigmaCongrLeft (h : List ((Σ k', A (e k')) × (Σ k', B (e k'))))
    (k' : K') :
    restrictExchanges (e k') (h.map ((Equiv.sigmaCongrLeft e).prodCongr (Equiv.sigmaCongrLeft e))) =
      restrictExchanges k' h := by
  -- Exchange by exchange: the tag `e a` is `e k'` exactly when `a` is `k'`.
  rw [restrictExchanges, restrictExchanges, List.filterMap_map]
  refine List.filterMap_congr fun z _ => ?_
  obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := z
  by_cases ha : a = k'
  · subst ha
    by_cases hb : b = a
    · subst hb
      simp only [Equiv.prodCongr_apply, Function.comp_apply, Prod.map_apply,
        Equiv.sigmaCongrLeft_apply, ↓reduceDIte, Option.some.injEq]
      rfl
    · simp only [Equiv.prodCongr_apply, Function.comp_apply, Prod.map_apply,
      Equiv.sigmaCongrLeft_apply, ↓reduceDIte, e.injective.ne hb, hb]
  · simp only [Equiv.prodCongr_apply, Function.comp_apply, Prod.map_apply,
    Equiv.sigmaCongrLeft_apply, e.injective.ne ha, ↓reduceDIte, ha]

open Classical in
/-- **The n-ary product reindexed along `e : K' ≃ K`** is the product over `K`, on the
reindexed transcript. -/
lemma parallelAll_sigmaCongrLeft_mass [∀ k, Fintype (A k)] [∀ k, Fintype (B k)]
    {D : ∀ k, Domain (A k) (B k)}
    (R : ∀ k, RandomSystem (A k) (B k) (D k))
    (h : List ((Σ k', A (e k')) × (Σ k', B (e k')))) :
    parallelAll R (h.map ((Equiv.sigmaCongrLeft e).prodCongr (Equiv.sigmaCongrLeft e))) =
      parallelAll (fun k' => R (e k')) h := by
  have hc : parallelAllConsistent
      (h.map ((Equiv.sigmaCongrLeft e).prodCongr (Equiv.sigmaCongrLeft e))) ↔
      parallelAllConsistent h := by
    simp only [parallelAllConsistent, List.forall_mem_map]
    exact forall₂_congr fun z _ => by
      obtain ⟨⟨a, x⟩, ⟨b, y⟩⟩ := z
      simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.sigmaCongrLeft_apply,
        e.injective.eq_iff]
  rw [parallelAll_mass, parallelAll_mass, propext hc,
    ← e.prod_comp fun k => R k (restrictExchanges k _)]
  simp only [restrictExchanges_sigmaCongrLeft]

end Reindex

end RandomSystem
end SystemAlgebra

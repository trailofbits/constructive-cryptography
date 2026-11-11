module

public import RandomSystems.Typed.ParallelAllRegroup.Defs
public import RandomSystems.Cumulative.ParallelAllRegroup
public import RandomSystems.Typed.SystemCoherence

/-!
# Finite-family interface presentations

`TypedSystem.parallelAll_reindex` presents a family through a bijection of its indices.
`TypedSystem.parallelAll_optionSplit` separates the `none` resource from its `some` family;
`TypedSystem.parallelAll_empty` identifies the empty family with the dummy resource.
Each equation attaches an explicit domain-preserving alphabet renaming.

The domain lemmas compare the same component query histories. The resource equations apply
the cumulative regrouping laws from `Cumulative.ParallelAllRegroup` and identify the typed
alphabet maps. `ParallelAllRegroup.Defs` owns the general wiring; `optionFamilyAlphabet`
and `parallelAll_option_mass` retain the two-component transcript presentation.
-/

@[expose] public section

namespace SystemAlgebra

open Interface

open Classical in
/-- The two family tags as the binary label sum, keeping every local port and value:

```text
  ⟨⟨none, i⟩, x⟩ ↦ ⟨none, ⟨i, x⟩⟩ ↦ ⟨none, ⟨i, x⟩⟩ ↦ ⟨inl i, x⟩
                sigmaAssoc      optionPair       sumAlphabet
```
-/
def Interface.optionFamilyAlphabet {I : Option Unit → Type} (F : ∀ k, I k → Type) :
    (Σ l : Σ k, I k, F l.1 l.2) ≃
      Σ l, Sum.rec (F none) (F (some ())) l :=
  (Equiv.sigmaAssoc F).trans ((optionPair (fun k => Σ i, F k i)).trans
    (sumAlphabet (Sum.rec (F none) (F (some ())))))

open Classical in
/-- **The typed n-ary product of two components is the binary product**: with
`φ = optionFamilyAlphabet`,

  `(∥ k, R k)(h) = (parallel (R none) (R (some ())))(h.map (φ_X × φ_Y))`. -/
lemma TypedSystem.parallelAll_option_mass {A : Option Unit → Interface}
    (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (tensorAll A).X l) × (Σ l, (tensorAll A).Y l))) :
    (TypedSystem.parallelAll R).1 h =
      (TypedSystem.parallel (R none) (R (some ()))).1
        (h.map ((optionFamilyAlphabet fun k => (A k).X).prodCongr
          (optionFamilyAlphabet fun k => (A k).Y))) := by
  -- Unfold both typed products to cumulative ones and apply the cumulative bridge. The left
  -- reads `h` through `optionPair ∘ sigmaAssoc`, the right through `sumAlphabet⁻¹ ∘ φ`.
  rw [TypedSystem.parallelAll_mass, RandomSystem.parallelAll_option_mass,
    TypedSystem.parallel_mass]
  apply congrArg (fun t => RandomSystem.parallel (R none).1 (R (some ())).1 t)
  simp only [List.map_map]
  apply List.map_congr_left
  intro z _
  -- On each exchange `sumAlphabet⁻¹ ∘ φ = optionPair ∘ sigmaAssoc`, since `φ` ends in
  -- `sumAlphabet`.
  apply Prod.ext <;>
    simp only [Equiv.prodCongr_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd,
      optionFamilyAlphabet, Equiv.coe_trans, Equiv.symm_apply_apply]

end SystemAlgebra

namespace SystemAlgebra

/-! ### Reindexing a family along `e : K' ≃ K` -/

section Reindex

variable {K K' : Type} (e : K' ≃ K)

open Classical in
/-- **The restriction after reindexing** at `e k'` is the restriction at `k'`. -/
lemma restrict_map_sigmaCongrLeft {F : K → Type} (l : List (Σ k', F (e k'))) (k' : K') :
    restrict (e k') (l.map (Equiv.sigmaCongrLeft e)) = restrict k' l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, x⟩ := x
    -- `sigmaCongrLeft e ⟨a, x⟩` is `⟨e a, x⟩`.
    change restrict (e k') (⟨e a, x⟩ :: l.map (Equiv.sigmaCongrLeft e)) = restrict k' (⟨a, x⟩ :: l)
    by_cases ha : a = k'
    · subst ha
      rw [restrict_cons_self, restrict_cons_self, ih]
    · rw [restrict_cons_ne (e.injective.ne ha), restrict_cons_ne ha, ih]


open Classical in
/-- **The domain of the reindexed family** on the reindexed history is the domain of the family. -/
lemma tensorAll_domain_reindexLabels [Fintype K] [Fintype K'] (A : K → Interface)
    (h : List (Σ i, (Interface.tensorAll A).X i)) :
    (Interface.tensorAll fun k' => A (e k')).domain
        (h.map (reindexLabels e A fun k i => (A k).X i)) ↔
      (Interface.tensorAll A).domain h := by
  -- Each restriction at `k'` of the reindexed history is the restriction at `e k'`.
  have hr : ∀ k', restrict k' ((h.map (reindexLabels e A fun k i => (A k).X i)).map
      (Equiv.sigmaAssoc fun k' i => (A (e k')).X i)) =
      restrict (e k') (h.map (Equiv.sigmaAssoc fun k i => (A k).X i)) := fun k' => by
    have hX : h.map (Equiv.sigmaAssoc fun k i => (A k).X i) =
        ((h.map (Equiv.sigmaAssoc fun k i => (A k).X i)).map (Equiv.sigmaCongrLeft e).symm).map
          (Equiv.sigmaCongrLeft e) := by
      simp only [List.map_map, Function.comp_def, Equiv.apply_symm_apply]
    rw [hX, restrict_map_sigmaCongrLeft, List.map_map, List.map_map]
    congr 1
  simp only [Interface.tensorAll, parallelAllInputs, hr]
  rw [Ne, List.map_eq_nil_iff]
  refine and_congr_right fun _ => ?_
  simpa only [Equiv.symm_symm] using (e.symm.forall_congr_left (p := fun k =>
    restrict k (h.map (Equiv.sigmaAssoc fun k i => (A k).X i)) = [] ∨
      (A k).domain (restrict k (h.map (Equiv.sigmaAssoc fun k i => (A k).X i))))).symm

/-- The reindexing of labels keeps the reindexed tag. -/
lemma reindexLabels_fst (A : K → Interface) (F : ∀ k, (A k).I → Type)
    (x : Σ l : Σ k, (A k).I, F l.1 l.2) :
    (reindexLabels e A F x).1 = (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm x.1 := by
  obtain ⟨⟨k, i⟩, a⟩ := x
  obtain ⟨k', rfl⟩ := e.surjective k
  -- `(sigmaCongrLeft e)⁻¹ ⟨e k', b⟩ = ⟨k', b⟩`.
  have key : ∀ {G : K → Type} (b : G (e k')),
      (Equiv.sigmaCongrLeft (β := G) e).symm ⟨e k', b⟩ = ⟨k', b⟩ :=
    fun _ => (Equiv.symm_apply_eq _).mpr rfl
  change ((Equiv.sigmaAssoc fun k' i => F (e k') i).symm
    ((Equiv.sigmaCongrLeft (β := fun k => Σ i, F k i) e).symm ⟨e k', ⟨i, a⟩⟩)).1 = _
  rw [key, key]
  rfl

/-- Regrouping a reindexed label, then reindexing back, is regrouping it. -/
lemma reindexLabels_assoc (A : K → Interface) (F : ∀ k, (A k).I → Type)
    (x : Σ l : Σ k, (A k).I, F l.1 l.2) :
    Equiv.sigmaCongrLeft (β := fun k => Σ i, F k i) e
        ((Equiv.sigmaAssoc fun k' i => F (e k') i) (reindexLabels e A F x)) =
      Equiv.sigmaAssoc F x := by
  simp only [reindexLabels, Equiv.trans_apply, Equiv.apply_symm_apply]

open Classical in
/-- **A family is its reindexing along `e`, renamed**: `∥ k, R k = rename • ∥ k', R (e k')`. -/
theorem TypedSystem.parallelAll_reindex [Fintype K] [Fintype K']
    {A : K → Interface} (R : ∀ k, TypedSystem (A k)) :
    TypedSystem.parallelAll R =
      TypedConverter.rename (A := Interface.tensorAll A)
        (B := Interface.tensorAll fun k' => A (e k'))
        (Equiv.sigmaCongrLeft (β := fun k => (A k).I) e).symm
        (reindexLabels e A fun k i => (A k).X i) (reindexLabels e A fun k i => (A k).Y i)
        (reindexLabels_fst e A fun k i => (A k).X i) (reindexLabels_fst e A fun k i => (A k).Y i)
        (tensorAll_domain_reindexLabels e A) •
        TypedSystem.parallelAll fun k' => R (e k') := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedConverter.rename_mass, TypedSystem.parallelAll_mass, TypedSystem.parallelAll_mass]
  refine Eq.trans ?_ (RandomSystem.parallelAll_sigmaCongrLeft_mass e (A := fun k => Σ i, (A k).X i)
    (B := fun k => Σ i, (A k).Y i) (fun k => (R k).1) _)
  rw [List.map_map, List.map_map]
  refine congrArg _ (List.map_congr_left fun x _ => ?_)
  exact Prod.ext (reindexLabels_assoc e A (fun k i => (A k).X i) x.1).symm
    (reindexLabels_assoc e A (fun k i => (A k).Y i) x.2).symm

end Reindex

end SystemAlgebra

namespace SystemAlgebra

/-! ### Splitting a family over `Option J` -/

section OptionSplit

variable {J : Type} (A : Option J → Interface)



/-- The split of labels keeps the split tag. -/
lemma optionSplitLabels_fst (F : ∀ o, (A o).I → Type) (x : Σ l : Σ o, (A o).I, F l.1 l.2) :
    (optionSplitLabels A F x).1 = optionSplitPorts A x.1 := by
  obtain ⟨⟨(_ | j), i⟩, x⟩ := x <;> rfl

open Classical in
/-- The left part of a split history is its restriction at `none`. -/
lemma restrict_none_optionSplitLabels (F : ∀ o, (A o).I → Type)
    (h : List (Σ l : Σ o, (A o).I, F l.1 l.2)) :
    restrict none ((h.map (optionSplitLabels A F)).map
        (sumAlphabet (Sum.rec (F none) fun l : (Σ j, (A (some j)).I) => F (some l.1) l.2)).symm) =
      restrict none (h.map (Equiv.sigmaAssoc F)) := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨⟨(_ | j), i⟩, x⟩ := x
    · rw [List.map_cons, List.map_cons, List.map_cons]
      erw [restrict_cons_self, restrict_cons_self, ih]
    · rw [List.map_cons, List.map_cons, List.map_cons]
      erw [restrict_cons_ne (Option.some_ne_none ()), restrict_cons_ne (Option.some_ne_none j), ih]

open Classical in
/-- The right part of a split history, restricted at `j`, is its restriction at `some j`. -/
lemma restrict_some_optionSplitLabels (F : ∀ o, (A o).I → Type)
    (h : List (Σ l : Σ o, (A o).I, F l.1 l.2)) (j : J) :
    restrict j ((restrict (some ()) ((h.map (optionSplitLabels A F)).map
        (sumAlphabet (Sum.rec (F none)
          fun l : (Σ j, (A (some j)).I) => F (some l.1) l.2)).symm)).map
          (Equiv.sigmaAssoc fun j i => F (some j) i)) =
      restrict (some j) (h.map (Equiv.sigmaAssoc F)) := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨⟨(_ | j₁), i⟩, x⟩ := x
    · rw [List.map_cons, List.map_cons]
      erw [restrict_cons_ne (Option.some_ne_none ()).symm,
        restrict_cons_ne (Option.some_ne_none j).symm, ih]
    · rw [List.map_cons, List.map_cons]
      erw [restrict_cons_self, List.map_cons]
      by_cases hj : j₁ = j
      · subst hj
        erw [restrict_cons_self, restrict_cons_self, ih]
      · erw [restrict_cons_ne hj, restrict_cons_ne (fun h => hj (Option.some_inj.mp h)), ih]

open Classical in
/-- **The domain of the split family** on the split history is the domain of the family. -/
lemma tensor_domain_optionSplitLabels [Fintype J] (h : List (Σ i, (Interface.tensorAll A).X i)) :
    ((A none).tensor (Interface.tensorAll fun j => A (some j))).domain
        (h.map (optionSplitLabels A fun o i => (A o).X i)) ↔
      (Interface.tensorAll A).domain h := by
  simp only [Interface.tensor, Interface.parallelDomain, parallelInputs]
  rw [restrict_none_optionSplitLabels A (fun o i => (A o).X i)]
  -- The right part is empty exactly when every `some j` restriction is.
  unfold parallelAllInputs
  simp only [Ne, List.map_eq_nil_iff, Option.forall]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨?_, fun hp => ?_⟩
  · rintro (hR | ⟨-, hp⟩)
    · intro j
      left
      rw [← restrict_some_optionSplitLabels A (fun o i => (A o).X i), hR]
      rfl
    · intro j
      have := hp j
      rwa [restrict_some_optionSplitLabels A (fun o i => (A o).X i)] at this
  · exact Classical.or_iff_not_imp_left.mpr fun hR => ⟨hR, fun j => by
      rw [restrict_some_optionSplitLabels A (fun o i => (A o).X i)]
      exact hp j⟩

open Classical in
/-- **A family over `Option J` is the component at `none` beside the family over `J`, renamed.** -/
theorem TypedSystem.parallelAll_optionSplit [Fintype J] (R : ∀ o, TypedSystem (A o)) :
    TypedSystem.parallelAll R =
      TypedConverter.rename (A := Interface.tensorAll A)
        (B := (A none).tensor (Interface.tensorAll fun j => A (some j))) (optionSplitPorts A)
        (optionSplitLabels A fun o i => (A o).X i) (optionSplitLabels A fun o i => (A o).Y i)
        (optionSplitLabels_fst A fun o i => (A o).X i)
        (optionSplitLabels_fst A fun o i => (A o).Y i) (tensor_domain_optionSplitLabels A) •
        TypedSystem.parallel (R none) (TypedSystem.parallelAll fun j => R (some j)) := by
  -- Apply the cumulative split law, then identify its maps with the typed alphabet wiring.
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedConverter.rename_mass, TypedSystem.parallelAll_mass,
    RandomSystem.parallelAll_optionSplit_mass, TypedSystem.parallel_mass,
    RandomSystem.parallel_mass,
    RandomSystem.parallel_mass]
  -- Both splits have the same tags, the same left part, and right parts related by `sigmaAssoc`.
  refine if_congr ?_ (congrArg₂ _ (congrArg _ ?_) ?_) rfl
  · simp only [RandomSystem.parallelConsistent, List.forall_mem_map]
    refine forall₂_congr fun z _ => ?_
    rcases z with ⟨⟨⟨(_ | j), i⟩, x⟩, ⟨⟨(_ | j'), i'⟩, y⟩⟩ <;> rfl
  · rw [RandomSystem.parallelLeft, RandomSystem.parallelLeft, List.map_map, List.map_map,
      List.filterMap_map,
      List.filterMap_map]
    refine List.filterMap_congr fun z _ => ?_
    rcases z with ⟨⟨⟨(_ | j), i⟩, x⟩, ⟨⟨(_ | j'), i'⟩, y⟩⟩ <;> rfl
  · rw [TypedSystem.parallelAll_mass]
    refine congrArg _ ?_
    rw [RandomSystem.parallelRight, RandomSystem.parallelRight, List.map_map, List.map_map,
      List.filterMap_map,
      List.filterMap_map, List.map_filterMap]
    refine List.filterMap_congr fun z _ => ?_
    rcases z with ⟨⟨⟨(_ | j), i⟩, x⟩, ⟨⟨(_ | j'), i'⟩, y⟩⟩ <;> rfl

end OptionSplit

end SystemAlgebra

namespace SystemAlgebra

/-- The empty family has no nonempty query history, hence its declared domain is empty. -/
lemma tensorAll_domain_empty (A : PEmpty → Interface)
    (h : List (Σ i, (Interface.tensorAll A).X i)) :
    ¬ (Interface.tensorAll A).domain h := by
  cases h with
  | nil => exact fun hh => hh.1 rfl
  | cons x _ => exact x.1.1.elim

/-- The empty family is the dummy resource through the unique empty-alphabet renaming. -/
lemma TypedSystem.parallelAll_empty (A : PEmpty → Interface) (R : ∀ k, TypedSystem (A k)) :
    TypedSystem.parallelAll R =
      TypedConverter.rename (A := Interface.tensorAll A) (B := Interface.unit)
        (Equiv.equivEmpty _) (Equiv.equivOfIsEmpty _ _) (Equiv.equivOfIsEmpty _ _)
        (fun x => x.1.1.elim) (fun y => y.1.1.elim)
        (fun h => iff_of_false id (tensorAll_domain_empty A h)) • TypedSystem.dummy := by
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedConverter.rename_mass]
  cases h with
  | nil => exact (TypedSystem.parallelAll R).1.mass_nil.trans TypedSystem.dummy.1.mass_nil.symm
  | cons x _ => exact x.1.1.1.elim

end SystemAlgebra

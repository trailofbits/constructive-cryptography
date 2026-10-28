import RandomSystems.Converter.ParallelAll
import RandomSystems.Typed.Functional
import RandomSystems.Typed.Parallel

/-!
# Typed finite parallel interfaces and systems

The n-ary interface tags each component label, and its domain admits an interleaving only
when each nonempty component input history is admitted. The n-ary typed system is the
independent cumulative product after regrouping the tagged alphabets. The n-ary typed
converter uses the independently sampled PDC behavior.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” This module provides that finite view for current typed interfaces.
Sampling a shared primitive once before constructing this family is a separate operation.

## Main definitions

* `Interface.tensorAll`: tagged finite interface family
* `TypedSystem.parallelAll`: independent family of typed systems
* `TypedConverter.parallelAll`: independent family of typed converters

## Main results

* `TypedSystem.ofFunction_parallelAll`: fixed component functions assemble directly
-/

namespace SystemAlgebra

open Probability
open scoped SystemAlgebra

variable {K : Type} [Fintype K] [DecidableEq K]

namespace Interface

open Classical in
/-- **The n-ary parallel interface** `⨂ₖ A k`: the labels of all components, regrouped
flat, with the n-ary parallel domain. Jost, Thesis, printed p. 17: “A finite set of resources
with disjoint interface sets can be viewed as a single one.” -/
abbrev tensorAll (A : K → Interface) : Interface where
  I := Σ k, (A k).I
  X l := (A l.1).X l.2
  Y l := (A l.1).Y l.2
  domain := parallelAllInputs (F := fun k i => (A k).X i) fun k => (A k).domain
  nonempty_prefix := parallelAllInputs_nonempty_prefix fun k => (A k).nonempty_prefix.2
  bound := ∑ k, (A k).bound
  length_le := parallelAllInputs_length_le fun k => (A k).length_le


end Interface

namespace TypedSystem

open Interface

open Classical in
/-- On a possible history of the product, the n-ary product domain admits exactly the
queries of the n-ary parallel domain. -/
lemma parallelAll_admits_iff {A : K → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ k, Σ i, (A k).X i) × (Σ k, Σ i, (A k).Y i)))
    (hp : RandomSystem.parallelAll (fun k => (R k).1) h ≠ 0) (x : Σ k, Σ i, (A k).X i) :
    Domain.parallelAll (fun k => (A k).inputDomain) h x ↔
      parallelAllInputs (F := fun k i => (A k).X i) (fun k => (A k).domain)
        ((h.map Prod.fst).map (Equiv.sigmaAssoc fun k i => (A k).X i).symm ++
          [(Equiv.sigmaAssoc fun k i => (A k).X i).symm x]) := by
  have hh : RandomSystem.parallelAllConsistent h := by
    by_contra hn
    exact hp (by rw [RandomSystem.parallelAll_mass, if_neg hn])
  have hab : ∀ k, (R k).1 (RandomSystem.restrictExchanges k h) ≠ 0 := by
    intro k hk
    apply hp
    rw [RandomSystem.parallelAll_mass, if_pos hh]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  have hl : ∀ k, (RandomSystem.restrictExchanges k h).length ≤ (A k).bound := fun k => by
    by_contra hl'
    exact hab k ((R k).1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl'))
  have hq := fun k => RandomSystem.restrictExchanges_queries hh k
  have hposs : ∀ k, SystemAlgebra.restrict k (h.map Prod.fst) = [] ∨
      (A k).domain (SystemAlgebra.restrict k (h.map Prod.fst)) := fun k => by
    rw [← hq k]
    exact (R k).possible_domain (hab k)
  have hm : ((h.map Prod.fst).map (Equiv.sigmaAssoc fun k i => (A k).X i).symm).map
      (Equiv.sigmaAssoc fun k i => (A k).X i) = h.map Prod.fst := by
    rw [List.map_map]
    simp
  simp only [parallelAllInputs, List.map_append, List.map_singleton, hm, Equiv.apply_symm_apply]
  obtain ⟨k₀, x₀⟩ := x
  constructor
  · rintro ⟨-, -, hd⟩
    refine ⟨by simp, fun k => ?_⟩
    by_cases hk : k = k₀
    · subst hk
      right
      simpa [restrict_append, Domain.ofInputs_apply, hq] using hd
    · rw [restrict_append, restrict_cons_ne (Ne.symm hk), restrict_nil, List.append_nil]
      exact hposs k
  · rintro ⟨-, hk⟩
    refine ⟨hh, fun k _ => hl k, ?_⟩
    have h₀ := hk k₀
    rw [restrict_append, restrict_cons_self, restrict_nil] at h₀
    simpa [Domain.ofInputs_apply, hq] using h₀.resolve_left (by simp)

open Classical in
/-- **n-ary parallel resources** `∥ₖ R k`: the independent product of the components, on
the regrouped labels. Jost, Thesis, printed p. 17, treats a finite disjoint-interface
family as one resource; this construction additionally chooses independent component laws. -/
noncomputable def parallelAll {A : K → Interface} (R : ∀ k, TypedSystem (A k)) :
    TypedSystem (tensorAll A) := by
  let eX := (Equiv.sigmaAssoc fun k i => (A k).X i).symm
  let eY := (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
  let T := (RandomSystem.parallelAll fun k => (R k).1).relabel eX eY
  have hd : ∀ h, T h ≠ 0 → ∀ x,
      (Domain.parallelAll fun k => (A k).inputDomain).relabel eX eY h x ↔
        (tensorAll A).inputDomain h x := by
    intro h hp x
    have he := parallelAll_admits_iff R (h.map (eX.symm.prodCongr eY.symm)) hp (eX.symm x)
    have hf : ((h.map (eX.symm.prodCongr eY.symm)).map Prod.fst).map eX = h.map Prod.fst := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro z _
      exact eX.apply_symm_apply z.1
    rw [hf, eX.apply_symm_apply] at he
    exact he
  refine ⟨T.withDomain hd, ?_⟩
  intro h x y hne
  change RandomSystem.parallelAll (fun k => (R k).1)
    ((h ++ [(x, y)]).map (eX.symm.prodCongr eY.symm)) = 0
  rw [List.map_append, List.map_singleton]
  obtain ⟨⟨k, i⟩, x⟩ := x
  obtain ⟨⟨k', j⟩, y⟩ := y
  change RandomSystem.parallelAll (fun k => (R k).1)
    (h.map (eX.symm.prodCongr eY.symm) ++ [(⟨k, ⟨i, x⟩⟩, ⟨k', ⟨j, y⟩⟩)]) = 0
  rw [RandomSystem.parallelAll_mass]
  by_cases hk : k' = k
  · subst hk
    have hij : j ≠ i := fun he => hne (congrArg (Sigma.mk k') he)
    have hr := (R k').2 (RandomSystem.restrictExchanges k' (h.map (eX.symm.prodCongr eY.symm)))
      ⟨i, x⟩ ⟨j, y⟩ hij
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ k') ?_
      simpa [RandomSystem.restrictExchanges, List.filterMap_append] using hr
    · rfl
  · rw [if_neg]
    intro hc
    exact hk (hc _ (List.mem_append_right _ (List.mem_singleton_self _))).symm

open Classical in
lemma parallelAll_mass {A : K → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (tensorAll A).X l) × (Σ l, (tensorAll A).Y l))) :
    (parallelAll R).1 h = RandomSystem.parallelAll (fun k => (R k).1)
      (h.map ((Equiv.sigmaAssoc fun k i => (A k).X i).prodCongr
        (Equiv.sigmaAssoc fun k i => (A k).Y i))) := rfl


end TypedSystem

namespace TypedConverter

open Interface

open Classical in
/-- **n-ary parallel converters** `⨂ₖ α k : ⨂ₖ A k ⟶ ⨂ₖ B k`: the n-ary parallel
composition of the PDC behaviors. Jost, Thesis, printed p. 17: “A finite set of resources
with disjoint interface sets can be viewed as a single one.” -/
noncomputable def parallelAll {A B : K → Interface} (α : ∀ k, TypedConverter (A k) (B k)) :
    TypedConverter (tensorAll A) (tensorAll B) :=
  PDCBehavior.tensorAll (O := fun k => (A k).I) (J := fun k => (B k).I)
    (U := fun k => (A k).X) (V := fun k => (A k).Y) (X := fun k => (B k).X)
    (Y := fun k => (B k).Y) α


end TypedConverter

/-- The n-ary parallel interface `⨂ k, A k`. -/
scoped notation3 "⨂ "(...)", "r:(scoped A => Interface.tensorAll A) => r

/-- The n-ary parallel composition of resources `∥ k, R k`. -/
scoped notation3 "∥ "(...)", "r:(scoped R => TypedSystem.parallelAll R) => r

/-- The n-ary parallel composition of converters `⨂ₘ k, α k`. -/
scoped notation3 "⨂ₘ "(...)", "r:(scoped α => TypedConverter.parallelAll α) => r


namespace TypedSystem

open Interface

open Classical in
/-- A fixed function on the joint interface is the parallel family of its restrictions. -/
lemma ofFunction_parallelAll {A : K → Interface} (f : ∀ k i, (A k).X i → (A k).Y i) :
    TypedSystem.ofFunction (A := ⨂ k, A k) (fun l x => f l.1 l.2 x) =
      ∥ k, TypedSystem.ofFunction (f k) := by
  symm
  apply TypedSystem.eq_ofFunction
  intro h hd hf
  rw [parallelAll_mass, RandomSystem.parallelAll_mass]
  have hc : RandomSystem.parallelAllConsistent (h.map ((Equiv.sigmaAssoc fun k i => (A k).X
      i).prodCongr (Equiv.sigmaAssoc fun k i => (A k).Y i))) := by
    intro z hz
    obtain ⟨⟨⟨⟨k, i⟩, x⟩, ⟨⟨k', j⟩, y⟩⟩, hw, rfl⟩ := List.mem_map.mp hz
    have hl : (⟨k', j⟩ : Σ k, (A k).I) = ⟨k, i⟩ := (Sigma.mk.inj_iff.mp (hf _ hw)).1
    exact (Sigma.mk.inj_iff.mp hl).1.symm
  rw [if_pos hc]
  refine Finset.prod_eq_one fun k _ => TypedSystem.ofFunction_mass_eq_one (f k) _ ?_ ?_
  · have hq : (h.map ((Equiv.sigmaAssoc fun k i => (A k).X i).prodCongr
        (Equiv.sigmaAssoc fun k i => (A k).Y i))).map Prod.fst =
        (h.map Prod.fst).map (Equiv.sigmaAssoc fun k i => (A k).X i) := by
      simp only [List.map_map]
      rfl
    rw [← List.map_eq_nil_iff (f := Prod.fst), RandomSystem.restrictExchanges_queries hc k, hq]
    by_cases hn : h = []
    · subst hn
      exact Or.inl rfl
    · exact (hd.resolve_left hn).2 k
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := List.mem_filterMap.mp hz
    obtain ⟨⟨⟨⟨k₁, i⟩, x⟩, ⟨⟨k₂, j⟩, y⟩⟩, hw0, rfl⟩ := List.mem_map.mp hw
    obtain ⟨hl, hv⟩ := Sigma.mk.inj_iff.mp (hf _ hw0)
    have hl' : (⟨k₂, j⟩ : Σ k, (A k).I) = ⟨k₁, i⟩ := hl
    obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.mp hl'
    obtain rfl := eq_of_heq hij
    have hv' : y = f k₂ j x := eq_of_heq hv
    subst hv'
    by_cases hk : k₂ = k
    · subst hk
      change (if hx : k₂ = k₂ then if hy : k₂ = k₂ then
        some (hx ▸ (⟨j, x⟩ : Σ i, (A k₂).X i), hy ▸ (⟨j, f k₂ j x⟩ : Σ i, (A k₂).Y i))
          else none else none) = some z at hwz
      rw [dif_pos rfl, dif_pos rfl] at hwz
      obtain rfl := Option.some.inj hwz
      rfl
    · split at hwz
      · exact absurd ‹_› hk
      · exact absurd hwz (by simp)


end TypedSystem

end SystemAlgebra

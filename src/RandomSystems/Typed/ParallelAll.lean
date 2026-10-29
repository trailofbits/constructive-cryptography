import RandomSystems.Converter.ParallelAll
import RandomSystems.Typed.Functional
import RandomSystems.Typed.Parallel

/-!
# Typed finite parallel interfaces and systems

A finite family `A : K → Interface` is one interface `⨂ k, A k`: its labels are the tagged
pairs `⟨k, i⟩`, with the alphabets `(A k).X i`, `(A k).Y i` of the components. For a history
`h`, write `h|k` for its entries tagged `k`, untagged. A nonempty input history is admitted iff
each `h|k` is empty or admitted by `A k`; the bound is `∑ k, (A k).bound`.

On this interface, `∥ k, R k` runs the components independently, each on its own projection:

                 ┌─────────────────────┐
  ── ⟨k, i⟩(x) ─▶│ R k   (own coins)   │       (∥ k, R k)(h) = ∏ k, (R k)(h|k)
  ◀─ ⟨k, i⟩ ⇒ y ─│                     │
  ── ⟨k', j⟩(x')▶│ R k'  (own coins)   │
  ◀─ ⟨k', j⟩ ⇒ y'│                     │
                 └─────────────────────┘

and `⨂ₘ k, α k` composes the converter behaviors in the same way. The family is indexed by `K`;
it is not identified with nested binary compositions, and no unitor is stated.

## Main definitions

* `Interface.tensorAll`: the tagged finite interface family `⨂ k, A k`
* `TypedSystem.parallelAll`: the independent family of typed systems `∥ k, R k`
* `TypedConverter.parallelAll`: the independent family of typed converters `⨂ₘ k, α k`

## Main results

* `TypedSystem.parallelAll_admits_iff`: on positive-mass histories, the product's domain is
  the interface domain
* `TypedSystem.ofFunction_parallelAll`: fixed component functions assemble componentwise

Source: Jost, Thesis, printed p. 17.
-/

namespace SystemAlgebra

open Probability
open scoped SystemAlgebra

variable {K : Type} [Fintype K] [DecidableEq K]

namespace Interface

open Classical in
/-- **The n-ary parallel interface** `⨂ k, A k` of a finite family:
* labels `⟨k, i⟩ : Σ k, (A k).I`, with `X ⟨k, i⟩ = (A k).X i` and `Y ⟨k, i⟩ = (A k).Y i`;
* domain: `h ≠ []` and, for every `k`, `h|k = []` or `(A k).domain (h|k)`;
* bound `∑ k, (A k).bound`.

The tag `k` makes the component label sets disjoint. `K` is a genuinely finite index set; the
label and alphabet finiteness is that of each `A k`. Jost, Thesis, printed p. 17: “A finite
set of resources with disjoint interface sets can be viewed as a single one that provides
each party access to the corresponding interfaces of all subsystems.” -/
abbrev tensorAll (A : K → Interface) : Interface where
  I := Σ k, (A k).I
  X l := (A l.1).X l.2
  Y l := (A l.1).Y l.2
  domain := parallelAllInputs (F := fun k i => (A k).X i) fun k => (A k).domain
  -- Each `h|k` of a prefix is a prefix of `h|k`, so admission passes to nonempty prefixes.
  nonempty_prefix := parallelAllInputs_nonempty_prefix fun k => (A k).nonempty_prefix.2
  bound := ∑ k, (A k).bound
  -- `|h| = ∑ k, |h|k| ≤ ∑ k, (A k).bound`.
  length_le := parallelAllInputs_length_le fun k => (A k).length_le

end Interface

namespace TypedSystem

open Interface

open Classical in
/-- **The two domains agree on positive-mass histories.** Let `h` be a history in the grouped
alphabets with `(parallelAll R)(h) ≠ 0`, and `x = ⟨k₀, x₀⟩` the next query. Then

  `Domain.parallelAll` admits `x` after `h`
    ⟺  consistent h ∧ (∀ k ≠ k₀, |h|k| ≤ (A k).bound) ∧ `A k₀` admits `h|k₀ ++ [x₀]`
    ⟺  ∀ k, (h ++ [x])|k = [] ∨ (A k).domain ((h ++ [x])|k)      (interface domain).

Positive mass supplies what the interface domain does not mention: tag consistency, every
component bound, and every projection `h|k` empty or admitted. Off the support the two
domains need not agree, and are not claimed to. -/
lemma parallelAll_admits_iff {A : K → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ k, Σ i, (A k).X i) × (Σ k, Σ i, (A k).Y i)))
    (hp : RandomSystem.parallelAll (fun k => (R k).1) h ≠ 0) (x : Σ k, Σ i, (A k).X i) :
    Domain.parallelAll (fun k => (A k).inputDomain) h x ↔
      parallelAllInputs (F := fun k i => (A k).X i) (fun k => (A k).domain)
        ((h.map Prod.fst).map (Equiv.sigmaAssoc fun k i => (A k).X i).symm ++
          [(Equiv.sigmaAssoc fun k i => (A k).X i).symm x]) := by
  -- An inconsistent history has mass 0, so `h` is tag consistent.
  have hh : RandomSystem.parallelAllConsistent h := by
    by_contra hn
    exact hp (by rw [RandomSystem.parallelAll_mass, if_neg hn])
  -- The mass is `∏ k, (R k)(h|k)`, so every factor is nonzero.
  have hab : ∀ k, (R k).1 (RandomSystem.restrictExchanges k h) ≠ 0 := by
    intro k hk
    apply hp
    rw [RandomSystem.parallelAll_mass, if_pos hh]
    exact Finset.prod_eq_zero (Finset.mem_univ k) hk
  -- A nonzero factor bounds its projection: `|h|k| ≤ (A k).bound`.
  have hl : ∀ k, (RandomSystem.restrictExchanges k h).length ≤ (A k).bound := fun k => by
    by_contra hl'
    exact hab k ((R k).1.mass_eq_zero_of_bound_lt (Nat.lt_of_not_le hl'))
  -- On a consistent history, the inputs of `h|k` are the inputs of `h` restricted to `k`.
  have hq := fun k => RandomSystem.restrictExchanges_queries hh k
  -- A nonzero factor also makes `h|k` empty or admitted by `A k`.
  have hposs : ∀ k, SystemAlgebra.restrict k (h.map Prod.fst) = [] ∨
      (A k).domain (SystemAlgebra.restrict k (h.map Prod.fst)) := fun k => by
    rw [← hq k]
    exact (R k).possible_domain (hab k)
  -- Flattening and regrouping the labels cancel.
  have hm : ((h.map Prod.fst).map (Equiv.sigmaAssoc fun k i => (A k).X i).symm).map
      (Equiv.sigmaAssoc fun k i => (A k).X i) = h.map Prod.fst := by
    rw [List.map_map]
    simp only [Equiv.self_comp_symm, List.map_map, CompTriple.comp_eq]
  -- The interface domain on `h ++ [x]`, read in the grouped alphabet.
  simp only [parallelAllInputs, List.map_append, List.map_singleton, hm, Equiv.apply_symm_apply]
  obtain ⟨k₀, x₀⟩ := x
  constructor
  -- (⇒) `(h ++ [x])|k₀ = h|k₀ ++ [x₀]` is admitted by `A k₀`; for `k ≠ k₀` the projection is
  -- `h|k`, empty or admitted by positive mass.
  · rintro ⟨-, -, hd⟩
    refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), fun k => ?_⟩
    by_cases hk : k = k₀
    · subst hk
      right
      simpa only [restrict_append, restrict_cons_self, restrict_nil, Domain.ofInputs_apply, hq]
        using hd
    · rw [restrict_append, restrict_cons_ne (Ne.symm hk), restrict_nil, List.append_nil]
      exact hposs k
  -- (⇐) Consistency and the bounds come from positive mass; admission of `x₀` is the
  -- `k₀` projection, which ends in `x₀` and so is nonempty.
  · rintro ⟨-, hk⟩
    refine ⟨hh, fun k _ => hl k, ?_⟩
    have h₀ := hk k₀
    rw [restrict_append, restrict_cons_self, restrict_nil] at h₀
    simpa only [Domain.ofInputs_apply, hq] using
      h₀.resolve_left (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))

open Classical in
/-- **n-ary parallel resources** `∥ k, R k : TypedSystem (⨂ k, A k)`: the independent
product of the component behaviors on the regrouped alphabets,

  (∥ k, R k)(h) = ∏ k, (R k)(h|k)   if every reply in `h` carries its query's tag `k`,
                = 0                 otherwise.

Each component keeps its own randomness and state and sees only its own exchanges `h|k`; a
query at `⟨k, i⟩` is answered at `⟨k, i⟩`. Jost's finite view (printed p. 17, see
`Interface.tensorAll`) applies to any family with disjoint interfaces; this definition is
the independent specialization. A component sample drawn once and shared,
`sample μ (fun c => ∥ k, R k c)`, is a different system. -/
noncomputable def parallelAll {A : K → Interface} (R : ∀ k, TypedSystem (A k)) :
    TypedSystem (tensorAll A) := by
  -- `eX`, `eY` flatten the alphabets, `⟨k, ⟨i, x⟩⟩ ↦ ⟨⟨k, i⟩, x⟩`; `T` is the cumulative
  -- product moved onto the flat labels.
  let eX := (Equiv.sigmaAssoc fun k i => (A k).X i).symm
  let eY := (Equiv.sigmaAssoc fun k i => (A k).Y i).symm
  let T := (RandomSystem.parallelAll fun k => (R k).1).relabel eX eY
  -- On positive-mass histories the product's domain is the interface domain
  -- (`parallelAll_admits_iff`); `withDomain` needs agreement only there.
  have hd : ∀ h, T h ≠ 0 → ∀ x,
      (Domain.parallelAll fun k => (A k).inputDomain).relabel eX eY h x ↔
        (tensorAll A).inputDomain h x := by
    intro h hp x
    have he := parallelAll_admits_iff R (h.map (eX.symm.prodCongr eY.symm)) hp (eX.symm x)
    -- Regrouping then flattening the inputs gives back `h`.
    have hf : ((h.map (eX.symm.prodCongr eY.symm)).map Prod.fst).map eX = h.map Prod.fst := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro z _
      exact eX.apply_symm_apply z.1
    rw [hf, eX.apply_symm_apply] at he
    exact he
  refine ⟨T.withDomain hd, ?_⟩
  -- Replies at the queried label: a last exchange `(⟨⟨k, i⟩, x⟩, ⟨⟨k', j⟩, y⟩)` with
  -- `⟨k', j⟩ ≠ ⟨k, i⟩` has mass 0.
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
  -- Same component, wrong port `j ≠ i`: `R k` itself replies at `i`, so the factor at `k`,
  -- `(R k)(h|k ++ [(⟨i, x⟩, ⟨j, y⟩)])`, is 0 (if `h` is inconsistent, the mass is 0 anyway).
  · subst hk
    have hij : j ≠ i := fun he => hne (congrArg (Sigma.mk k') he)
    have hr := (R k').2 (RandomSystem.restrictExchanges k' (h.map (eX.symm.prodCongr eY.symm)))
      ⟨i, x⟩ ⟨j, y⟩ hij
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ k') ?_
      simpa only [RandomSystem.restrictExchanges, List.filterMap_append, Equiv.prodCongr_apply,
        List.filterMap_map, Function.comp_apply, Prod.map_fst, Prod.map_snd, ↓reduceDIte,
        Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil] using hr
    · rfl
  -- Wrong component `k' ≠ k`: the history is not tag consistent, so its mass is 0.
  · rw [if_neg]
    intro hc
    exact hk (hc _ (List.mem_append_right _ (List.mem_singleton_self _))).symm

open Classical in
/-- The defining equation on the flat labels: `(∥ k, R k)(h)` is the product's mass on `h`
regrouped, `⟨⟨k, i⟩, x⟩ ↦ ⟨k, ⟨i, x⟩⟩`; by `RandomSystem.parallelAll_mass` this is
`∏ k, (R k)(h|k)` on tag-consistent histories and 0 otherwise. -/
lemma parallelAll_mass {A : K → Interface} (R : ∀ k, TypedSystem (A k))
    (h : List ((Σ l, (tensorAll A).X l) × (Σ l, (tensorAll A).Y l))) :
    (parallelAll R).1 h = RandomSystem.parallelAll (fun k => (R k).1)
      (h.map ((Equiv.sigmaAssoc fun k i => (A k).X i).prodCongr
        (Equiv.sigmaAssoc fun k i => (A k).Y i))) := rfl

end TypedSystem

namespace TypedConverter

open Interface

open Classical in
/-- **n-ary parallel converters** `⨂ₘ k, α k` from `⨂ k, A k` (outside) to `⨂ k, B k`
(inside): the PDC behaviors of the `α k` composed independently (`PDCBehavior.tensorAll`).
An outside query at `⟨k, o⟩` is handled by `α k` alone, with its own randomness and state;
it queries only inside labels `⟨k, j⟩` and replies at `⟨k, o⟩`:

                 ┌────────┐
  ── ⟨k, o⟩(u) ─▶│  α k   │── ⟨k, j⟩(x) ─▶
  ◀─ ⟨k, o⟩ ⇒ v ─│        │◀─ ⟨k, j⟩ ⇒ y ─
                 ├────────┤
  ── ⟨k', o'⟩ ──▶│  α k'  │── ⟨k', j'⟩ ──▶
                 └────────┘

Converters are not resources; Jost's finite view (printed p. 17) concerns resources. This is
the corresponding wiring of converters (Definition 2.2.2, printed pp. 17–18), taken as the
definition. -/
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
/-- **Fixed functions assemble componentwise**: the function `⟨k, i⟩(x) ⇒ f k i x` on
`⨂ k, A k` is the parallel family of the component functions,

  ofFunction (fun ⟨k, i⟩ x => f k i x) = ∥ k, ofFunction (f k).

A typed corollary of the definitions; with no randomness, independence plays no role. -/
lemma ofFunction_parallelAll {A : K → Interface} (f : ∀ k i, (A k).X i → (A k).Y i) :
    TypedSystem.ofFunction (A := ⨂ k, A k) (fun l x => f l.1 l.2 x) =
      ∥ k, TypedSystem.ofFunction (f k) := by
  -- A system is `ofFunction f` once it gives mass 1 to every empty or admitted history
  -- answered by `f`.
  symm
  apply TypedSystem.eq_ofFunction
  intro h hd hf
  -- On such `h`, the mass is the product `∏ k, (ofFunction (f k))(h|k)`.
  rw [parallelAll_mass, RandomSystem.parallelAll_mass]
  -- Answered by `f`, each reply carries its query's label, hence its tag: `h` is consistent.
  have hc : RandomSystem.parallelAllConsistent (h.map ((Equiv.sigmaAssoc fun k i => (A k).X
      i).prodCongr (Equiv.sigmaAssoc fun k i => (A k).Y i))) := by
    intro z hz
    obtain ⟨⟨⟨⟨k, i⟩, x⟩, ⟨⟨k', j⟩, y⟩⟩, hw, rfl⟩ := List.mem_map.mp hz
    have hl : (⟨k', j⟩ : Σ k, (A k).I) = ⟨k, i⟩ := (Sigma.mk.inj_iff.mp (hf _ hw)).1
    exact (Sigma.mk.inj_iff.mp hl).1.symm
  rw [if_pos hc]
  -- Each factor is 1: `h|k` is empty or admitted by `A k`, and answered by `f k`.
  refine Finset.prod_eq_one fun k _ => TypedSystem.ofFunction_mass_eq_one (f k) _ ?_ ?_
  -- The inputs of `h|k` are `(h.map Prod.fst)|k`, empty or admitted since `h` is.
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
  -- An exchange of `h|k` comes from an exchange `(⟨⟨k₂, j⟩, x⟩, ⟨⟨k₂, j⟩, f k₂ j x⟩)` of `h`.
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
    -- `k₂ = k`: the projection keeps it as `(⟨j, x⟩, ⟨j, f k j x⟩)`, answered by `f k`.
    · subst hk
      change (if hx : k₂ = k₂ then if hy : k₂ = k₂ then
        some (hx ▸ (⟨j, x⟩ : Σ i, (A k₂).X i), hy ▸ (⟨j, f k₂ j x⟩ : Σ i, (A k₂).Y i))
          else none else none) = some z at hwz
      rw [dif_pos rfl, dif_pos rfl] at hwz
      obtain rfl := Option.some.inj hwz
      rfl
    -- `k₂ ≠ k`: the projection to `k` drops it.
    · split at hwz
      · exact absurd ‹_› hk
      · cases hwz

end TypedSystem

end SystemAlgebra

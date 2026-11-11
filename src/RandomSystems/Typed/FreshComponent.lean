module

public import RandomSystems.Typed.FreshComponent.Defs
public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.SystemParallel

/-!
# Freshness through sources, parallel composition and renaming

`AnswersFresh.ofMemoryless` multiplies a local reply-event bound by the prefix mass;
`AnswersFresh.source` specializes it to the existing source. `AnswersFresh.parallel_left`
factors each left extension using `parallel_mass_snoc_inl`, applies the component bound,
and restores the joint prefix mass. `AnswersFresh.rename` transports the admitted query
and reindexes its replies. These laws preserve the observer's explicit selected value.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

-- `A` is the resource interface; `C` carries observed values and `μ` bounds their reply masses.
variable {A : Interface} {C : Type} [DecidableEq C]
variable {pick : (Σ i, A.X i) × (Σ i, A.Y i) → Option C} {μ : Distribution C}

/-- **A memoryless system is fresh** where its reply laws are: if every reply law `ν i x` gives
the component `v` mass at most `μ v`, then `ofMemoryless A ν` answers with the fresh component
`pick`. -/
lemma AnswersFresh.ofMemoryless (ν : ∀ i, A.X i → ProbDist (A.Y i))
    (hν : ∀ x v, (ν x.1 x.2).1.mass (fun y => pick (x, ⟨x.1, y⟩) = some v) ≤ μ v) :
    (TypedSystem.ofMemoryless A ν).AnswersFresh pick μ := by
  classical
  set M := TypedSystem.ofMemoryless A ν
  intro h x v hx
  -- The chain rule of the memoryless system at the admitted query `x`.
  have hsnoc : ∀ y : A.Y x.1, M.1 (h ++ [(x, ⟨x.1, y⟩)]) = M.1 h * (ν x.1 x.2).1 y :=
    fun y => by
    rw [ofMemoryless_val, RandomSystem.memoryless_snoc,
      ite_eq_left (show A.inputDomain h x from hx)]
    obtain ⟨i, u⟩ := x
    rw [RandomSystem.portLaw_apply_mk]
  simp only [hsnoc]
  have hm := hν x v
  rw [Distribution.mass_eq_sum] at hm
  calc ∑ y : A.Y x.1, (if pick (x, ⟨x.1, y⟩) = some v then M.1 h * (ν x.1 x.2).1 y else 0)
      = M.1 h * ∑ y : A.Y x.1, (if pick (x, ⟨x.1, y⟩) = some v then (ν x.1 x.2).1 y else 0) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by split_ifs <;> simp only [mul_zero]
    _ ≤ M.1 h * μ v := mul_le_mul_of_nonneg_left
        (by convert hm)
        (M.1.mass_nonneg h)
    _ = μ v * M.1 h := mul_comm _ _

/-- A source's observed samples are fresh with their pushforward law. -/
lemma AnswersFresh.source {Z : Type} [Fintype Z]
    -- `law` is sampled afresh at each query; `q` bounds the admitted number of queries.
    (law : ProbDist Z) (q : ℕ)
    -- `G` extracts the observed component of each sample.
    (G : Z → C) :
    (TypedSystem.source law q).AnswersFresh (fun e => some (G e.2.2))
      (fTransform G law.1) := by
  rw [source_eq_ofMemoryless]
  refine AnswersFresh.ofMemoryless _ fun x v => ?_
  rw [fTransform_apply_eq_mass]
  exact le_of_eq (Distribution.mass_congr _ fun z => Option.some_inj)

/-- A fresh component of `R` remains fresh on left exchanges of `R ∥ S`. -/
lemma AnswersFresh.parallel_left {B : Interface} {R : TypedSystem A}
    -- `S` is an independent resource; `hμ` makes unselected exchanges satisfy the bound.
    (S : TypedSystem B) (hμ : μ.NonNeg) (hR : R.AnswersFresh pick μ) :
    (TypedSystem.parallel R S).AnswersFresh
      (fun e => match e with
        | (⟨.inl i, x⟩, ⟨.inl i', y⟩) => pick (⟨i, x⟩, ⟨i', y⟩)
        | _ => none) μ := by
  classical
  intro h x v hx
  obtain ⟨i | j, x⟩ := x
  · let e := (sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
      (sumAlphabet (Sum.rec A.Y B.Y)).symm
    by_cases hc : RandomSystem.parallelConsistent (h.map e)
    · dsimp only [e] at hc
      have hadm := ((tensor_inputDomain_inl_iff h hc i x).mp hx).1
      have hb := hR (RandomSystem.parallelLeft (h.map e)) ⟨i, x⟩ v hadm
      -- Factor every selected extension, then apply the component bound.
      simp only [parallel_mass_snoc_inl R S h hc]
      calc
        _ = (∑ y : A.Y i, if pick (⟨i, x⟩, ⟨i, y⟩) = some v then
              R.1 (RandomSystem.parallelLeft (h.map e) ++ [(⟨i, x⟩, ⟨i, y⟩)]) else 0) *
            S.1 (RandomSystem.parallelRight (h.map e)) := by
          simp only [e, Finset.sum_mul, ite_mul, zero_mul]
        _ ≤ (μ v * R.1 (RandomSystem.parallelLeft (h.map e))) *
            S.1 (RandomSystem.parallelRight (h.map e)) :=
          mul_le_mul_of_nonneg_right hb (S.1.mass_nonneg _)
        _ = μ v * (parallel R S).1 h := by
          rw [parallel_mass, RandomSystem.parallel_mass, ite_eq_left hc, mul_assoc]
    · dsimp only [e] at hc
      -- Inconsistent prefixes and all their extensions have zero mass.
      simp only [parallel_mass, List.map_append, List.map_singleton,
        RandomSystem.parallel_mass, ite_eq_right hc, mul_zero]
      exact le_of_eq (Finset.sum_eq_zero fun y _ => by
        rw [ite_eq_right fun hc' => hc (RandomSystem.parallelConsistent_snoc.mp hc').1,
          ite_self])
  · -- Right exchanges select no value; their bound follows from nonnegativity.
    change (∑ _y : B.Y j, (0 : ℝ)) ≤ μ v * (parallel R S).1 h
    rw [Finset.sum_const_zero]
    exact mul_nonneg (hμ v) ((parallel R S).1.mass_nonneg h)

/-- Renaming preserves freshness with the observer transported through queries and replies. -/
lemma AnswersFresh.rename {B : Interface}
    -- `e` renames ports; `f` and `g` transport queries and replies.
    (e : A.I ≃ B.I) (f : (Σ i, A.X i) ≃ (Σ j, B.X j))
    (g : (Σ i, A.Y i) ≃ (Σ j, B.Y j))
    -- `hf` and `hg` preserve the corresponding port; `hd` identifies admitted histories.
    (hf : ∀ x, (f x).1 = e x.1) (hg : ∀ y, (g y).1 = e y.1)
    (hd : ∀ h, B.domain (h.map f) ↔ A.domain h) {W : TypedSystem B}
    {pick : (Σ j, B.X j) × (Σ j, B.Y j) → Option C} (hW : W.AnswersFresh pick μ) :
    (TypedConverter.rename e f g hf hg hd • W).AnswersFresh (fun z => pick (f z.1, g z.2)) μ := by
  classical
  -- Sum a fixed reply fiber by inserting its label indicator in the whole alphabet.
  have fiber {I : Type} [Fintype I] {T : I → Type} [∀ i, Fintype (T i)]
      (F : (Σ i, T i) → ℝ) (i : I) :
      ∑ y : T i, F ⟨i, y⟩ = ∑ z : Σ i, T i, if z.1 = i then F z else 0 := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single i
      (fun j _ hj => Finset.sum_eq_zero fun _ _ => ite_eq_right hj)
      (fun hi => absurd (Finset.mem_univ i) hi)]
    exact Finset.sum_congr rfl fun _ _ => (ite_eq_left rfl).symm
  intro h x v hx
  simp only [TypedConverter.rename_mass, List.map_append, List.map_singleton]
  have hx' : B.domain ((h.map (f.prodCongr g)).map Prod.fst ++ [f x]) := by
    have he := (hd (h.map Prod.fst ++ [x])).mpr hx
    have hm : (h.map (f.prodCongr g)).map Prod.fst = (h.map Prod.fst).map f := by
      rw [List.map_map, List.map_map]
      rfl
    rw [List.map_append, List.map_singleton] at he
    rwa [hm]
  refine le_of_eq_of_le ?_ (hW (h.map (f.prodCongr g)) (f x) v hx')
  -- Reindex the replies at `x` by `g`; they are the replies of `W` at `f x`.
  let Φ : (Σ j, B.Y j) → ℝ := fun w =>
    if pick (f x, w) = some v then W.1 (h.map (f.prodCongr g) ++ [(f x, w)]) else 0
  change ∑ y : A.Y x.1, Φ (g ⟨x.1, y⟩) = ∑ y : B.Y (f x).1, Φ ⟨(f x).1, y⟩
  rw [fiber (fun z => Φ (g z)) x.1, fiber Φ (f x).1]
  refine Fintype.sum_equiv g _ _ fun z => ?_
  have hz : z.1 = x.1 ↔ (g z).1 = (f x).1 := by
    rw [hg, hf]
    exact e.injective.eq_iff.symm
  by_cases h₁ : z.1 = x.1
  · rw [ite_eq_left h₁, ite_eq_left (hz.mp h₁)]
  · rw [ite_eq_right h₁, ite_eq_right (mt hz.mpr h₁)]

end SystemAlgebra.TypedSystem

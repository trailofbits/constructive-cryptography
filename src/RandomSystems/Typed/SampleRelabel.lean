module

public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Game

/-!
# Relabeling retained draws on visible transcripts

A system that hides part of each reply sums over the internal histories displayed as a given
visible transcript `h`. `sumMBO_eq_sum_tagMBOs` in `RandomSystems.Game.MBO` supplies
this expansion for hidden MBO bits. When two systems draw `k` once from the same law `P`, their
visible probabilities at `h` agree if each contributing internal history `u` admits its own
`P`-preserving relabeling `s` matching the two systems' contributions on `supp P`.

## Main results

* `TypedSystem.sample_mass_eq_of_map`: one `P`-preserving relabeling matches transcript masses
* `TypedSystem.sample_mass_eq_of_sum_relabel`: per-history relabeling over a finite sum `S`
* `TypedSystem.sample_mass_eq_of_display_relabel`: explicit display-map specialization
* `TypedGame.sample_visible_mass_eq_of_relabel`: visible-system specialization for `TypedGame`
-/

@[expose] public section

namespace SystemAlgebra

open Probability
open scoped BigOperators

namespace TypedSystem

variable {A : Interface}

/-- Relabeling a retained draw by a `P`-preserving map `s` preserves the transcript mass at `h`
whenever `(R₀ k)(h) = (R₁ (s k))(h)` on `supp P`; `s` need not be bijective. -/
lemma sample_mass_eq_of_map
    -- `P` is the shared initial draw; `R₀`, `R₁` are the compared sampled systems on `A`.
    {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R₀ R₁ : K → TypedSystem A) (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    -- `s` preserves `P` and matches the transcript masses on `supp P`.
    (s : K → K) (hs : Distribution.fTransform s P = P)
    (heq : ∀ k ∈ P.support, (R₀ k).1 h = (R₁ (s k)).1 h) :
    (TypedSystem.sample P R₀).1 h = (TypedSystem.sample P R₁).1 h :=
  Distribution.sum_mul_eq_of_fTransform_eq P s hs (fun k => (R₀ k).1 h)
    (fun k => (R₁ k).1 h) heq

/-- Two sampled systems give visible transcript `h` the same probability when each system's mass
at `h` sums internal contributions `w₀ k u`, `w₁ k u` over `u ∈ S`, and every `u ∈ S` admits a
`P`-preserving relabeling `s` matching `w₀ k u` to `w₁ (s k) u` on `supp P`. -/
lemma sample_mass_eq_of_sum_relabel
    -- `P` is the shared initial draw; `S` indexes the internal histories contributing to `h`.
    {K U : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R₀ R₁ : K → TypedSystem A) (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (S : Finset U) (w₀ w₁ : K → U → ℝ)
    -- `h₀`, `h₁` decompose each system's visible mass at `h` over `S`.
    (h₀ : ∀ k ∈ P.support, (R₀ k).1 h = ∑ u ∈ S, w₀ k u)
    (h₁ : ∀ k ∈ P.support, (R₁ k).1 h = ∑ u ∈ S, w₁ k u)
    -- Each `u ∈ S` has its own `P`-preserving relabeling `s` matching `w₀` to `w₁`.
    (hmatch : ∀ u ∈ S, ∃ s : K → K, Distribution.fTransform s P = P ∧
      ∀ k ∈ P.support, w₀ k u = w₁ (s k) u) :
    (TypedSystem.sample P R₀).1 h = (TypedSystem.sample P R₁).1 h := by
  rw [sample_mass, sample_mass]
  calc
    ∑ k ∈ P.support, P k * (R₀ k).1 h
        = ∑ k ∈ P.support, P k * ∑ u ∈ S, w₀ k u :=
          Finset.sum_congr rfl fun k hk => by rw [h₀ k hk]
    _   = ∑ k ∈ P.support, P k * ∑ u ∈ S, w₁ k u :=
          Distribution.sum_mul_sum_eq_of_fTransform_eq P S w₀ w₁ hmatch
    _   = ∑ k ∈ P.support, P k * (R₁ k).1 h :=
          Finset.sum_congr rfl fun k hk => by rw [h₁ k hk]

open Classical in
/-- Visible transcript probabilities agree when each system sums internal probabilities `p₀`,
`p₁` over internal histories `u ∈ S` displayed as `h` (`display u = h`), and each such `u`
admits its own `P`-preserving relabeling `s` matching `p₀ k u` to `p₁ (s k) u` on `supp P`. -/
lemma sample_mass_eq_of_display_relabel
    -- `P` is the shared initial draw; `S` contains all internal histories displayed as `h`.
    {K U : Type} (P : Distribution K) [Distribution.IsProbability P]
    (R₀ R₁ : K → TypedSystem A) (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    -- `display` projects internal histories to visible ones; `p₀`, `p₁` give internal masses.
    (S : Finset U) (display : U → List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (p₀ p₁ : K → U → ℝ)
    (h₀ : ∀ k ∈ P.support, (R₀ k).1 h = ∑ u ∈ S, if display u = h then p₀ k u else 0)
    (h₁ : ∀ k ∈ P.support, (R₁ k).1 h = ∑ u ∈ S, if display u = h then p₁ k u else 0)
    -- Only internal histories displayed as `h` need a `P`-preserving relabeling `s`.
    (hmatch : ∀ u ∈ S, display u = h →
      ∃ s : K → K, Distribution.fTransform s P = P ∧
        ∀ k ∈ P.support, p₀ k u = p₁ (s k) u) :
    (TypedSystem.sample P R₀).1 h = (TypedSystem.sample P R₁).1 h := by
  refine sample_mass_eq_of_sum_relabel P R₀ R₁ h S
    (fun k u => if display u = h then p₀ k u else 0)
    (fun k u => if display u = h then p₁ k u else 0) h₀ h₁ fun u hu => ?_
  by_cases hd : display u = h
  · obtain ⟨s, hs, hEq⟩ := hmatch u hu hd
    exact ⟨s, hs, fun k hk => by simp only [hd, ↓reduceIte, hEq k hk]⟩
  · exact ⟨id, Distribution.fTransform_id P, fun _ _ => by simp only [hd, ↓reduceIte]⟩

end TypedSystem

namespace TypedGame

/-- Two sampled typed games induce the same visible probability on `h` when every internal
MBO-tagged transcript `u` displayed as `h` admits a `P`-preserving relabeling matching `G₀`
to `G₁` on `supp P`. -/
lemma sample_visible_mass_eq_of_relabel
    -- `A` is the visible interface; `P` is the shared initial draw of `G₀` and `G₁`.
    {A : Interface} {K : Type} (P : Distribution K) [Distribution.IsProbability P]
    (G₀ G₁ : K → TypedGame A) (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    -- Each internal history `u` displayed as `h` has its own `P`-preserving relabeling `s`.
    (hmatch : ∀ u, forgetMBOs u = h →
      ∃ s : K → K, Distribution.fTransform s P = P ∧
        ∀ k ∈ P.support, (G₀ k).1.1 u = (G₁ (s k)).1.1 u) :
    (TypedSystem.sample P fun k => (G₀ k).visible).1 h =
      (TypedSystem.sample P fun k => (G₁ k).visible).1 h := by
  refine TypedSystem.sample_mass_eq_of_sum_relabel P (fun k => (G₀ k).visible)
    (fun k => (G₁ k).visible) h Finset.univ
    (fun k bs => (G₀ k).1.1 (tagMBOs h bs))
    (fun k bs => (G₁ k).1.1 (tagMBOs h bs))
    (fun k _ => sumMBO_eq_sum_tagMBOs (G₀ k).1.1 h)
    (fun k _ => sumMBO_eq_sum_tagMBOs (G₁ k).1.1 h)
    fun bs _ => hmatch (tagMBOs h bs) (forgetMBOs_tagMBOs h bs)

end TypedGame

end SystemAlgebra

module

public import Probability.Kernel

/-!
# Dependent coordinate selection

A retained vector can contain keys of different byte lengths. Selecting active users preserves
its independent coordinate laws, including when no users are active. Repeated reads of one
selected coordinate use the same draw.
-/

@[expose] public section

namespace Tests.DependentCoordinateMarginals

open Probability.Distribution

open Classical in
/-- Active coordinates of a heterogeneous uniform vector remain uniformly distributed. -/
lemma restrict_uniform
    -- `X i` carries the outcome at index `i`; alphabets may have different sizes.
    {I : Type*} [Fintype I] (X : I → Type*) [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    -- `active` selects retained coordinates, possibly none.
    (active : I → Prop) [Fintype {i // active i}] :
    fTransform (fun values : ∀ i, X i => fun i : {i // active i} => values i.val)
      (uniform (∀ i, X i)) = uniform (∀ i : {i // active i}, X i.val) := by
  rw [← piDep_uniform, ← piDep_uniform]
  exact fTransform_piDep_comp_of_weight_eq_one (fun i => uniform (X i))
    Subtype.val Subtype.val_injective (fun _ _ => weight_uniform)

open Classical in
/-- Each key is a byte vector of its own length; zero-length keys are allowed. -/
example {I : Type} [Fintype I] (bytes : I → ℕ) (active : I → Prop)
    [Fintype {i // active i}] :
    fTransform (fun keys : ∀ i, Fin (bytes i) → Fin 256 =>
      fun i : {i // active i} => keys i.val)
      (uniform (∀ i, Fin (bytes i) → Fin 256)) =
        uniform (∀ i : {i // active i}, Fin (bytes i.val) → Fin 256) :=
  restrict_uniform _ active

/-- An empty selection produces the unique empty tuple with probability one. -/
example {I : Type} [Fintype I] {X : I → Type} (μ : ∀ i, ProbDist (X i)) :
    (ProbDist.piDep μ).map (fun f (j : Fin 0) => f (Fin.elim0 j)) =
      ProbDist.piDep (fun j : Fin 0 => μ (Fin.elim0 j)) :=
  ProbDist.map_piDep_comp μ Fin.elim0 (fun j => Fin.elim0 j)

/-- Two reads of coordinate `j` return the same retained value, before and after restriction. -/
example {I J : Type} [Fintype I] [Fintype J] {X : I → Type}
    (μ : ∀ i, ProbDist (X i)) (e : J → I) (he : Function.Injective e) (j : J) :
    (ProbDist.piDep μ).map (fun f => (f (e j), f (e j))) =
      (ProbDist.piDep fun j => μ (e j)).map (fun f => (f j, f j)) := by
  rw [← ProbDist.map_piDep_comp μ e he, ProbDist.map_map]
  rfl

/-- Selecting one coordinate twice is not an injective selection. -/
example : ¬ Function.Injective (fun _ : Bool => ()) := by
  intro hinj
  have h : false = true := hinj (a₁ := false) (a₂ := true) rfl
  cases h

#print axioms restrict_uniform
#print axioms fTransform_piDep_comp_of_weight_eq_one
#print axioms ProbDist.map_piDep_comp

end Tests.DependentCoordinateMarginals

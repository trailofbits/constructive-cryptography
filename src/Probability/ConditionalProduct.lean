module

public import Probability.Kernel

/-!
# Conditional products from independent tables

Draw an observation table `f` and an independent table `ψ` with entries indexed by `(i,o)`.
Selecting `ψ(i,f(i))` has the conditional product law, jointly with the same `f`:

```text
f ← P; ψ(i,o) ← κᵢ(o) independently; return (f, i ↦ ψ(i,f(i)))
  = f ← P; xᵢ ← κᵢ(f(i)) independently; return (f,x).
```

`map_prod_piDep_select` gives this identity. `map_prod_piDep_eq_of_jointLaw` reconstructs
an independent latent table and its observations from the corresponding coordinate joint
laws. `map_prod_piDep_pair_eq_of_jointLaw` uses ordinary pair indices for common alphabets.
The latent outcome types may be infinite; only the table's indices are finite.
-/

@[expose] public section

namespace Probability.Distribution.ProbDist

-- `I` indexes coordinates; `O i` carries their observations and `X i` their latent outcomes.
variable {I : Type*} [Fintype I] {O X : I → Type*} [∀ i, Fintype (O i)]

/-- Selecting one private entry per coordinate gives its conditional law while retaining
all observations: `(f,ψ) ↦ (f, i ↦ ψ(i,f(i)))`. -/
lemma map_prod_piDep_select
    -- `P` may correlate the observations; `κ i o` is the law of private entry `(i,o)`.
    (P : ProbDist (∀ i, O i)) (κ : ∀ i, O i → ProbDist (X i)) :
    (prodProbDist P (ProbDist.piDep (fun j : Σ i, O i => κ j.1 j.2))).map
      (fun pair => (pair.1, fun i => pair.2 ⟨i, pair.1 i⟩)) =
      jointLaw P (fun f => ProbDist.piDep (fun i => κ i (f i))) := by
  have product : prodProbDist P (ProbDist.piDep (fun j : Σ i, O i => κ j.1 j.2)) =
      jointLaw P (fun _ => ProbDist.piDep (fun j : Σ i, O i => κ j.1 j.2)) :=
    Subtype.ext (prod_eq_bindK _ _)
  rw [product]
  apply jointLaw_map_dependent id (fun f ψ i => ψ ⟨i, f i⟩)
    P P (fun f => ProbDist.piDep (fun i => κ i (f i)))
    (fun _ => ProbDist.piDep (fun j : Σ i, O i => κ j.1 j.2)) (map_id P)
  intro f _
  -- Distinct coordinates select distinct cells of the one private table.
  exact map_piDep_comp (fun j : Σ i, O i => κ j.1 j.2)
    (fun i => ⟨i, f i⟩) (fun _ _ equal => congrArg Sigma.fst equal)

/-- Coordinate joint reconstruction gives the full joint law of the latent table and its
observations. Both sides retain the observations used to select the private entries. -/
theorem map_prod_piDep_eq_of_jointLaw
    -- `μ i` is the latent law; `ν i` is the observation law and `κ i o` its conditional law.
    (μ : ∀ i, ProbDist (X i)) (ν : ∀ i, ProbDist (O i))
    (κ : ∀ i, O i → ProbDist (X i))
    -- `F i` observes a latent outcome at coordinate `i`.
    (F : ∀ i, X i → O i)
    -- `coordinate` identifies the complete observation/latent joint law at each coordinate.
    (coordinate : ∀ i, jointLaw (ν i) (κ i) = (μ i).map (fun x => (F i x, x))) :
    (prodProbDist (ProbDist.piDep ν)
      (ProbDist.piDep (fun j : Σ i, O i => κ j.1 j.2))).map
        (fun pair => ((fun i => pair.2 ⟨i, pair.1 i⟩), pair.1)) =
      (ProbDist.piDep μ).map (fun x => (x, fun i => F i (x i))) := by
  -- The coordinate joint laws combine independently, keeping both complete tables.
  have graph : jointLaw (ProbDist.piDep ν)
      (fun f => ProbDist.piDep (fun i => κ i (f i))) =
      (ProbDist.piDep μ).map (fun x => ((fun i => F i (x i)), x)) := by
    calc
      _ = (ProbDist.piDep (fun i => jointLaw (ν i) (κ i))).map
          (fun p => ((fun i => (p i).1), (fun i => (p i).2))) := jointLaw_piDep ν κ
      _ = (ProbDist.piDep (fun i => (μ i).map (fun x => (F i x, x)))).map
          (fun p => ((fun i => (p i).1), (fun i => (p i).2))) := by
        exact congrArg
          (fun laws : ∀ i, ProbDist (O i × X i) => (ProbDist.piDep laws).map
            (fun p => ((fun i => (p i).1), (fun i => (p i).2)))) (funext coordinate)
      _ = _ := by
        apply Subtype.ext
        change fTransform _
          (Distribution.piDep (fun i => fTransform (fun x => (F i x, x)) (μ i).1)) =
          fTransform _ (Distribution.piDep (fun i => (μ i).1))
        rw [← fTransform_piDep, fTransform_fTransform]
        rfl
  -- Select the private entries, then put the reconstructed latent table first.
  have joint := (map_prod_piDep_select (ProbDist.piDep ν) κ).trans graph
  have swapped := congrArg (ProbDist.map Prod.swap) joint
  simpa only [map_map, Function.comp_def, Prod.swap_prod_mk] using swapped

/-- With common alphabets, the same reconstruction indexes the private table by `D × O`. -/
lemma map_prod_piDep_pair_eq_of_jointLaw
    -- `D` indexes coordinates, `O` their observations, and `X` their latent outcomes.
    {D O X : Type*} [Fintype D] [Fintype O]
    (μ : D → ProbDist X) (ν : D → ProbDist O) (κ : D → O → ProbDist X)
    -- `F z` observes coordinate `z`; `coordinate` reconstructs its full joint law.
    (F : D → X → O)
    (coordinate : ∀ z, jointLaw (ν z) (κ z) = (μ z).map (fun x => (F z x, x))) :
    (prodProbDist (ProbDist.piDep ν)
      (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2))).map
        (fun pair => ((fun z => pair.2 (z, pair.1 z)), pair.1)) =
      (ProbDist.piDep μ).map (fun x => (x, fun z => F z (x z))) := by
  -- Reindex the common-alphabet private table by dependent pairs.
  have privateTable :
      (ProbDist.piDep (fun zo : D × O => κ zo.1 zo.2)).map
        (fun ψ (j : Σ _ : D, O) => ψ (j.1, j.2)) =
      ProbDist.piDep (fun j : Σ _ : D, O => κ j.1 j.2) := by
    apply map_piDep_comp
    intro a b equal
    exact Sigma.ext (congrArg Prod.fst equal) (heq_of_eq (congrArg Prod.snd equal))
  calc
    _ = (prodProbDist (ProbDist.piDep ν)
        (ProbDist.piDep (fun j : Σ _ : D, O => κ j.1 j.2))).map
          (fun pair => ((fun z => pair.2 ⟨z, pair.1 z⟩), pair.1)) := by
      rw [← privateTable, prodProbDist_map_right, map_map]
      rfl
    _ = _ := map_prod_piDep_eq_of_jointLaw μ ν κ F coordinate

end Probability.Distribution.ProbDist

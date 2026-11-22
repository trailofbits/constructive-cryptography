module

public import RandomSystems.Typed.RandomFunctionCollision

/-!
# Uniform-table collision bound

The dependent entry law specializes to uniform functions on a hidden coordinate type `K t`,
with arbitrary outside reply processing. Caller tags in `User × Word` keep different users
separate in the collision event.
-/

@[expose] public section

namespace Tests.RandomFunctionCollision

open SystemAlgebra Probability Probability.Distribution

open Classical in
/-- A retained Boolean table uses the uniform-table corollary directly. -/
lemma uniform_map_bound
    -- `t` selects the coordinate type and map; the entries are uniform bits.
    {A : Interface} {T : Type} {K : T → Type}
    [∀ t, Fintype (K t)]
    (P : ProbDist T) (input : (t : T) → (Σ i, A.X i) → K t)
    (output : ∀ i, Bool → A.Y i) (D : A.inputDomain.Distinguisher) :
    let R := TypedSystem.sample P.1 fun t =>
      TypedSystem.sample (uniform (K t → Bool)) fun table =>
        TypedSystem.ofFunction (fun i x => output i (table (input t ⟨i, x⟩)))
    let S := TypedSystem.sample (uniform ((Σ i, A.X i) → Bool)) fun table =>
      TypedSystem.ofFunction (fun i x => output i (table ⟨i, x⟩))
    D.advantage R.1 S.1 ≤ ENNReal.ofReal
      ((P.1.prod (D.transcriptLaw S).1).mass fun pair =>
        ¬ Set.InjOn (input pair.1) {x | x ∈ pair.2.map Prod.fst}) :=
  TypedSystem.sample_uniform_comp_advantage_le_collision_mass P input output D

/-- Including the user tag in the table coordinate prevents cross-user collisions. -/
example {User X Word : Type} (f : User → X → Word) (u v : User) (x y : X)
    (hne : u ≠ v) : (u, f u x) ≠ (v, f v y) := by
  intro he
  exact hne (congrArg Prod.fst he)

#print axioms uniform_map_bound
#print axioms TypedSystem.sample_piDep_comp_advantage_le_collision_mass

end Tests.RandomFunctionCollision

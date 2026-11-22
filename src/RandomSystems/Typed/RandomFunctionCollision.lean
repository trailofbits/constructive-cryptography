module

public import RandomSystems.Typed.RandomFunction
public import RandomSystems.Typed.TranscriptLaw

/-!
# Input collisions in the ideal transcript

`sample_piDep_comp_advantage_le_collision_mass` compares a retained table read through a
random input map with an independent outside table. Each mapped entry must have the same
outside marginal law `ν x`, independently of the hidden choice `t`.

The distinguishing advantage is at most the probability of a collision between distinct
queried inputs under `P × transcriptLaw D S`. `D` may adapt every query to earlier replies;
only the hidden map choice and the ideal interaction are independent. Repeats of one input
are not collisions. The proof applies the good-transcript bound to the table restriction law.
`sample_uniform_comp_advantage_le_collision_mass` exposes the same bound for uniform tables.
-/

@[expose] public section

namespace SystemAlgebra.TypedSystem

open Probability Probability.Distribution

/-- Distinct-input collisions under an independently sampled map bound table replacement. -/
theorem sample_piDep_comp_advantage_le_collision_mass
    -- `A` is the outside interface; `t : T` selects inside coordinates `K t` and their types.
    {A : Interface} {T : Type} {K : T → Type} [∀ t, Fintype (K t)]
    {Z : (t : T) → K t → Type}
    -- `P` selects `t` once; `μ t k` is the independent retained law at inside entry `k`.
    (P : ProbDist T) (μ : ∀ t k, ProbDist (Z t k))
    (input : (t : T) → (Σ i, A.X i) → K t)
    (output : (t : T) → (x : Σ i, A.X i) → Z t (input t x) → A.Y x.1)
    -- `ν x` is the ideal entry law; `marginal` makes it independent of `t`.
    (ν : (x : Σ i, A.X i) → ProbDist (A.Y x.1))
    (marginal : ∀ t x, (μ t (input t x)).map (output t x) = ν x)
    -- `D` is any stopping randomized observer compatible with the outside domain.
    (D : A.inputDomain.Distinguisher) :
    let R := TypedSystem.sample P.1 fun t =>
      TypedSystem.sample (ProbDist.piDep (μ t)).1 fun table =>
      ofFunction (fun i x => output t ⟨i, x⟩ (table (input t ⟨i, x⟩)))
    let S := TypedSystem.sample (ProbDist.piDep ν).1 fun table =>
      ofFunction (fun i x => table ⟨i, x⟩)
    D.advantage R.1 S.1 ≤ ENNReal.ofReal
      ((P.1.prod (D.transcriptLaw S).1).mass fun pair =>
        ¬ Set.InjOn (input pair.1) {x | x ∈ pair.2.map Prod.fst}) := by
  intro R S
  apply ENNReal.ofReal_le_ofReal
  apply D.sample_probability_gap_le_bad_mass P _ S
    (fun t h => ¬ Set.InjOn (input t) {x | x ∈ h.map Prod.fst})
  intro t h good
  -- On the distinct queried inputs, table restriction gives the independent ideal entries.
  simpa only [marginal] using
    sample_piDep_comp_mass_eq (μ t) (input t) (output t) h (not_not.mp good)

open Classical in
/-- Uniform retained tables with arbitrary output processing fit the generic collision bound. -/
lemma sample_uniform_comp_advantage_le_collision_mass
    -- `t` selects the coordinate type and map; `Z` carries uniform table values.
    {A : Interface} {Z T : Type} {K : T → Type}
    [∀ t, Fintype (K t)] [Fintype Z] [Nonempty Z]
    (P : ProbDist T) (input : (t : T) → (Σ i, A.X i) → K t)
    (output : ∀ i, Z → A.Y i) (D : A.inputDomain.Distinguisher) :
    let R := TypedSystem.sample P.1 fun t =>
      TypedSystem.sample (uniform (K t → Z)) fun table =>
        TypedSystem.ofFunction (fun i x => output i (table (input t ⟨i, x⟩)))
    let S := TypedSystem.sample (uniform ((Σ i, A.X i) → Z)) fun table =>
      TypedSystem.ofFunction (fun i x => output i (table ⟨i, x⟩))
    D.advantage R.1 S.1 ≤ ENNReal.ofReal
      ((P.1.prod (D.transcriptLaw S).1).mass fun pair =>
        ¬ Set.InjOn (input pair.1) {x | x ∈ pair.2.map Prod.fst}) := by
  intro R S
  let ν := fun x : Σ i, A.X i => (𝒰[Z]).map (output x.1)
  have ideal : TypedSystem.sample (ProbDist.piDep ν).1
      (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩)) = S := by
    have mappedLaw : ProbDist.piDep ν =
        (ProbDist.piDep fun _ : Σ i, A.X i => 𝒰[Z]).map
          (fun table x => output x.1 (table x)) :=
      Subtype.ext (fTransform_piDep _ _).symm
    let base : ProbDist ((Σ i, A.X i) → Z) := ProbDist.piDep fun _ => 𝒰[Z]
    let read := fun table : (Σ i, A.X i) → Z =>
      TypedSystem.ofFunction (A := A) (fun i x => output i (table ⟨i, x⟩))
    have base_eq : base = 𝒰[(Σ i, A.X i) → Z] :=
      Subtype.ext (piDep_uniform (A := fun _ : Σ i, A.X i => Z))
    calc
      _ = TypedSystem.sample
          (base.map (fun table x => output x.1 (table x))).1
          (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩)) :=
        congrArg (fun law => TypedSystem.sample law.1
          (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩))) mappedLaw
      _ = TypedSystem.sample base.1 read := TypedSystem.sample_fTransform _ _ _
      _ = S := congrArg (fun law : ProbDist ((Σ i, A.X i) → Z) =>
        TypedSystem.sample law.1 read) base_eq
  have bound := TypedSystem.sample_piDep_comp_advantage_le_collision_mass
    P (fun t (_ : K t) => 𝒰[Z]) input (fun _ x => output x.1) ν (fun _ _ => rfl) D
  dsimp only at bound
  rw [ideal] at bound
  simpa only [ProbDist.piDep_val, ProbDist.uniform, piDep_uniform] using bound

end SystemAlgebra.TypedSystem

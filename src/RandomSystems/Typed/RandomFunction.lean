module

public import RandomSystems.Typed.QueryRouting
public import Probability.Kernel

/-!
# Reading independent tables through an input map

A table is drawn once, with independent entry laws `μ k`. On input `x`, the system reads
entry `e x` and returns `output x` of that value. `sample_piDep_comp_mass_eq` identifies its
cumulative probability with independently sampled outside entries on every transcript where
`e` is injective on the queried inputs. Repeated queries read the same retained entry.

`routing_smul_sample_piDep_mass_eq` gives the corresponding attachment equation for a
router with a domain guarantee. The proof uses coordinate selection, then the router's
fixed-function attachment law; it preserves the original outside domain.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

/-- Reading `e x` agrees with independent outside entries until distinct queried inputs collide.
The outside law at `x` is `(μ (e x)).map (output x)`. -/
theorem TypedSystem.sample_piDep_comp_mass_eq
    -- `A` is the outside interface; `K` indexes inside entries of types `Z k`.
    {A : Interface} {K : Type} [Fintype K] {Z : K → Type}
    -- `μ k` is the normalized entry law; `e` selects the entry read on an outside input.
    (μ : ∀ k, ProbDist (Z k)) (e : (Σ i, A.X i) → K)
    -- `output x` translates the selected entry to the reply alphabet of input `x`.
    (output : (x : Σ i, A.X i) → Z (e x) → A.Y x.1)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    -- `hinj` forbids collisions only among distinct inputs actually appearing in `h`.
    (hinj : Set.InjOn e {x | x ∈ h.map Prod.fst}) :
    (TypedSystem.sample (ProbDist.piDep μ).1 (fun table =>
      TypedSystem.ofFunction (fun i x => output ⟨i, x⟩ (table (e ⟨i, x⟩))))).1 h =
    (TypedSystem.sample
      (ProbDist.piDep fun x : Σ i, A.X i => (μ (e x)).map (output x)).1
      (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩))).1 h := by
  classical
  let s := (h.map Prod.fst).toFinset
  have hmem (z) (hz : z ∈ h) : z.1 ∈ s :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨z, hz, rfl⟩)
  let event (values : (x : s) → A.Y x.val.1) :=
    (h = [] ∨ A.domain (h.map Prod.fst)) ∧
      ∀ z, ∀ hz : z ∈ h, z.2 = ⟨z.1.1, values ⟨z.1, hmem z hz⟩⟩
  have hi : Function.Injective (fun x : s => e x.val) := by
    intro a b hab
    exact Subtype.ext (hinj (List.mem_toFinset.mp a.2) (List.mem_toFinset.mp b.2) hab)
  -- Restrict the retained table, then translate its selected replies.
  have leftLaw :
      ((ProbDist.piDep μ).map (fun table (x : s) => output x.val (table (e x.val)))).1 =
        (ProbDist.piDep fun x : s => (μ (e x.val)).map (output x.val)).1 := by
    have selected := ProbDist.map_piDep_comp μ (fun x : s => e x.val) hi
    have mapped := congrArg
      (ProbDist.map (fun (values : (x : s) → Z (e x.val)) x => output x.val (values x)))
      selected
    rw [ProbDist.map_map] at mapped
    exact (congrArg Subtype.val mapped).trans (fTransform_piDep _ _)
  have rightLaw := congrArg Subtype.val (ProbDist.map_piDep_comp
    (fun x : Σ i, A.X i => (μ (e x)).map (output x))
    (fun x : s => x.val) Subtype.val_injective)
  rw [TypedSystem.sample_ofFunction_mass_eq, TypedSystem.sample_ofFunction_mass_eq]
  -- Both response events are the same event on the restricted outside table.
  calc
    _ = (((ProbDist.piDep μ).map
        (fun table (x : s) => output x.val (table (e x.val)))).1).mass event := by
      rw [ProbDist.map_val, Distribution.mass_fTransform]
    _ = (ProbDist.piDep fun x : s => (μ (e x.val)).map (output x.val)).1.mass event :=
      congrArg (fun P => P.mass event) leftLaw
    _ = _ := by
      rw [← rightLaw, ProbDist.map_val, Distribution.mass_fTransform]

/-- A domain-preserving router reads the same outside table away from input collisions. -/
lemma TypedConverter.routing_smul_sample_piDep_mass_eq
    -- `A`, `B` are outside and inside interfaces, with their original domains.
    {A B : Interface} (request : (Σ i, A.X i) → Σ j, B.X j)
    (answer : (x : Σ i, A.X i) → (Σ j, B.Y j) → A.Y x.1)
    (hmap : ∀ xs, A.domain xs → B.domain (xs.map request))
    -- `μ x` is the law of the retained inside entry at query `x`.
    (μ : (x : Σ j, B.X j) → ProbDist (B.Y x.1))
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    (hinj : Set.InjOn request {x | x ∈ h.map Prod.fst}) :
    (routing request answer hmap • TypedSystem.sample (ProbDist.piDep μ).1
      (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩))).1 h =
    (TypedSystem.sample (ProbDist.piDep fun x : Σ i, A.X i =>
      (μ (request x)).map (fun y => answer x ⟨(request x).1, y⟩)).1
      (fun table => TypedSystem.ofFunction (fun i x => table ⟨i, x⟩))).1 h := by
  rw [smul_sample]
  simp only [routing_smul_ofFunction]
  exact TypedSystem.sample_piDep_comp_mass_eq μ request
    (fun x y => answer x ⟨(request x).1, y⟩) h hinj

end SystemAlgebra

import Probability.DependentProduct

/-!
# Finite heterogeneous products

Regression tests for `Distribution.piDep`. Over the empty index type the product has total
mass one, the empty product of coordinate masses. On the family indexed by `Bool` with
carriers `A false = Bool` and `A true = Unit`, a rectangular event factors coordinatewise:
fixing the `Bool` coordinate and leaving the `Unit` coordinate free has mass `1/2 · 1`.
With one index in `ULift.{u} Unit`, the infinite carrier `ULift.{v} ℕ` and the raw,
unnormalized law `2 · δ₇`, the rectangle `{f | f k = 7}` has mass `2`: the event law
needs neither finite carriers, normalization, nor a shared universe. Pushing the singleton
product of `-2 · δ₇` on `ULift.{2} ℕ` by the noninjective parity `n ↦ n % 2` into `ℕ`
(`fTransform_piDep`) gives the rectangle `{f | f k = 1}` mass `-2`: the pushforward law
holds for signed weights across universes.
-/

namespace Probability.Distribution.Tests

noncomputable section

-- `K = Empty`: `(piDep μ).mass (fun _ => True) = ∏_{k ∈ ∅} (μ k).mass (fun _ => True) = 1`.
example : (Distribution.piDep (K := Empty) (A := fun _ => Unit)
    (fun k => nomatch k)).mass (fun _ => True) = 1 := by
  simpa only [implies_true, Finset.univ_eq_empty, Finset.prod_empty] using
    Distribution.piDep_mass_forall (K := Empty) (A := fun _ => Unit)
    (fun k => nomatch k) (fun _ _ => True)

/-- A heterogeneous family on `K = Bool`, with carrier `A b = if b then Unit else Bool`:
`μ false = uniform Bool`, mass `1/2` at each bit, and `μ true = uniform Unit`, mass `1`
at `()`. -/
def heteroLaw : (b : Bool) → Distribution (if b then Unit else Bool)
  | false => Distribution.uniform Bool
  | true => Distribution.uniform Unit

/-- A rectangle for `heteroLaw`: `Q false x ↔ x = true` on the `Bool` coordinate, and
`Q true _ ↔ True`, leaving the `Unit` coordinate free. -/
def heteroEvent : (b : Bool) → (if b then Unit else Bool) → Prop
  | false => fun x => x = true
  | true => fun _ => True

-- `(piDep heteroLaw).mass {f | f false = true} = Pr[x = true] · Pr[True] = 1/2 · 1`.
example : (Distribution.piDep heteroLaw).mass
    (fun f => ∀ b, heteroEvent b (f b)) = (1 / 2 : ℝ) := by
  -- Factor the rectangle, then evaluate each uniform coordinate mass.
  rw [Distribution.piDep_mass_forall]
  simp only [Fintype.univ_bool, heteroLaw, heteroEvent, Bool.false_eq_true, ↓dreduceIte,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.prod_insert, mass_true,
    weight_uniform, Finset.prod_singleton, mass_singleton, uniform_apply, Fintype.card_bool,
    Nat.cast_ofNat, one_div, one_mul]

universe u v

-- `K = ULift.{u} Unit`, carrier `ULift.{v} ℕ`, `μ = 2 · δ₇` of raw weight `2`:
-- `(piDep μ).mass {f | f k = 7} = ∏_{k} μ({7}) = 2`.
example : (piDep (K := ULift.{u} Unit) fun _ =>
    Finsupp.single (⟨7⟩ : ULift.{v} ℕ) (2 : ℝ)).mass (fun f => ∀ k, f k = ⟨7⟩) = 2 := by
  -- Factor the rectangle; the product has one factor, the mass `2` of `2 · δ₇` at `7`.
  rw [piDep_mass_forall (fun _ : ULift.{u} Unit =>
    Finsupp.single (⟨7⟩ : ULift.{v} ℕ) (2 : ℝ)) (fun _ x => x = ⟨7⟩)]
  simp only [Fintype.prod_unique, mass_singleton, Finsupp.single_eq_same]

/-- `K = ULift.{1} Unit`, carrier `ULift.{2} ℕ`, raw law `μ = -2 · δ₇`, parity `p n = n % 2`
into `ℕ` (noninjective, crossing universes): `(p_* piDep μ).mass {f | f k = 1} = -2`. -/
example : (fTransform (fun a : ULift.{1} Unit → ULift.{2} ℕ => fun k => (a k).down % 2)
    (piDep fun _ : ULift.{1} Unit => Finsupp.single (⟨7⟩ : ULift.{2} ℕ) (-2 : ℝ))).mass
      (fun f => ∀ k, f k = 1) = -2 := by
  -- Push each coordinate, factor the rectangle; the one factor is `p_*(-2 · δ₇) = -2 · δ₁`.
  rw [fTransform_piDep (fun _ : ULift.{1} Unit =>
    Finsupp.single (⟨7⟩ : ULift.{2} ℕ) (-2 : ℝ))
    (fun _ a => a.down % 2)]
  rw [piDep_mass_forall (fun _ : ULift.{1} Unit =>
    fTransform (fun a : ULift.{2} ℕ => a.down % 2) (Finsupp.single ⟨7⟩ (-2 : ℝ)))
    (fun _ n => n = 1)]
  simp only [Fintype.prod_unique, mass_singleton, fTransform_single]
  norm_num

#print axioms Probability.Distribution.fTransform_piDep
#print axioms Probability.Distribution.independent_product_piDep
#print axioms Probability.Distribution.piDep_eq_pi
#print axioms Probability.Distribution.piDep_isProbDist
#print axioms Probability.Distribution.piDep_mass_forall

end
end Probability.Distribution.Tests

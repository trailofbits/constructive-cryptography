import Probability.DependentProduct

/-!
# Finite heterogeneous products

Regression tests for `Distribution.piDep`. Over the empty index type the product has total
mass one, the empty product of coordinate masses. On the family indexed by `Bool` with
carriers `A false = Bool` and `A true = Unit`, a rectangular event factors coordinatewise:
fixing the `Bool` coordinate and leaving the `Unit` coordinate free has mass `1/2 · 1`.
-/

namespace Probability.Distribution.Tests

noncomputable section

-- `K = Empty`: `(piDep μ).mass (fun _ => True) = ∏_{k ∈ ∅} (μ k).mass (fun _ => True) = 1`.
example : (Distribution.piDep (K := Empty) (A := fun _ => Unit)
    (fun k => nomatch k)).mass (fun _ => True) = 1 := by
  simpa using Distribution.piDep_mass_forall (K := Empty) (A := fun _ => Unit)
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
  simp [heteroLaw, heteroEvent, Distribution.mass_singleton,
    Distribution.uniform_apply, Distribution.mass_true, Distribution.weight_uniform]

#print axioms Probability.Distribution.piDep_isProbDist
#print axioms Probability.Distribution.piDep_mass_forall

end
end Probability.Distribution.Tests

import Probability.DependentProduct

/-!
# Finite heterogeneous products

The empty product has unit mass. In a heterogeneous Bool-indexed product, constraining the
Bool coordinate while leaving the Unit coordinate free has mass one half.
-/

namespace Probability.Distribution.Tests

noncomputable section

example : (Distribution.piDep (K := Empty) (A := fun _ => Unit)
    (fun k => nomatch k)).mass (fun _ => True) = 1 := by
  simpa using Distribution.piDep_mass_forall (K := Empty) (A := fun _ => Unit)
    (fun k => nomatch k) (fun _ _ => True)

def heteroLaw : (b : Bool) → Distribution (if b then Unit else Bool)
  | false => Distribution.uniform Bool
  | true => Distribution.uniform Unit

def heteroEvent : (b : Bool) → (if b then Unit else Bool) → Prop
  | false => fun x => x = true
  | true => fun _ => True

example : (Distribution.piDep heteroLaw).mass
    (fun f => ∀ b, heteroEvent b (f b)) = (1 / 2 : ℝ) := by
  rw [Distribution.piDep_mass_forall]
  simp [heteroLaw, heteroEvent, Distribution.mass_singleton,
    Distribution.uniform_apply, Distribution.mass_true, Distribution.weight_uniform]

#print axioms Probability.Distribution.piDep_isProbDist
#print axioms Probability.Distribution.piDep_mass_forall

end
end Probability.Distribution.Tests

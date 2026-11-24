module

public import ConstructiveCryptography.Construction.TwoPartyObstruction
public import ConstructiveCryptography.Notation.Basic

/-!
# Tests for the two-party algebraic construction obstruction

We instantiate `TwoPartySetup` and `TwoPartyPlugging` on a concrete one-object algebraic category
`TwoSided` whose morphisms are two-sided integer shifts `(l, r) : ℤ × ℤ` acting on `ℤ` by
`(l, r) • x = l + x + r`, with neutral channel `source = 0 : ℤ`.

Two tests verify that the obstruction retains the admitted bridge class:

* Under congruence modulo 4 (`mod4Relation`) with bridge class `multipleOfFour := {γ | 4 ∣ γ}`,
  `target = 1` is `Unconstructible` from `0`, whereas removing the bridge restriction makes `1`
  `Constructible` with an unadmitted composite bridge `γ = -1 ∉ multipleOfFour`.
* Under the translation-invariant extended metric `edist x y = |(x - y)|` with bridge class
  `nonnegBridges := {γ | 0 ≤ γ}`, `target = 3` is `Unconstructible` from `0` within budgets
  `(1, 1, 0)`, whereas `γ = -3 ∉ nonnegBridges` achieves distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.TwoPartyObstruction

open CategoryTheory CategoryTheory.MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open ConstructiveCryptography.Construction
open scoped SystemAlgebra

/-- Single-object interface type for the concrete two-sided shift algebra. -/
inductive TwoSided : Type
  | obj

/-- Resource carrier at each `TwoSided` interface wrapping an integer value. -/
@[ext]
structure IntResource (_ : TwoSided) : Type where
  /-- Underlying integer value of the resource. -/
  val : ℤ

/-- Morphisms `(l, r) : ℤ × ℤ` act on `x : ℤ` by two-sided translation `l + x + r`. -/
instance : Category.{0} TwoSided where
  Hom _ _ := ℤ × ℤ
  id _ := (0, 0)
  comp f g := (f.1 + g.1, g.2 + f.2)
  id_comp f := by
    change (0 + f.1, f.2 + 0) = f
    cases f
    simp only [zero_add, add_zero]
  comp_id f := by
    change (f.1 + 0, 0 + f.2) = f
    cases f
    simp only [add_zero, zero_add]
  assoc f g h := by
    change ((f.1 + g.1) + h.1, h.2 + (g.2 + f.2)) = (f.1 + (g.1 + h.1), (h.2 + g.2) + f.2)
    simp only [add_assoc]

/-- The single-object monoidal structure with pointwise addition on shifts. -/
instance : MonoidalCategoryStruct TwoSided where
  tensorObj _ _ := TwoSided.obj
  tensorHom f g := (f.1 + g.1, f.2 + g.2)
  whiskerLeft _ _ _ g := g
  whiskerRight f _ := f
  tensorUnit := TwoSided.obj
  associator _ _ _ := Iso.refl TwoSided.obj
  leftUnitor _ := Iso.refl TwoSided.obj
  rightUnitor _ := Iso.refl TwoSided.obj

instance : MonoidalCategory TwoSided where
  tensorHom_def f g := by
    change (f.1 + g.1, f.2 + g.2) = (f.1 + g.1, g.2 + f.2)
    exact Prod.ext rfl (by omega)
  id_tensorHom_id _ _ := by
    change ((0 : ℤ) + 0, (0 : ℤ) + 0) = (0, 0)
    simp only [add_zero]
  tensorHom_comp_tensorHom f₁ f₂ g₁ g₂ := by
    change ((f₁.1 + f₂.1) + (g₁.1 + g₂.1), (g₁.2 + g₂.2) + (f₁.2 + f₂.2)) =
      ((f₁.1 + g₁.1) + (f₂.1 + g₂.1), (g₁.2 + f₁.2) + (g₂.2 + f₂.2))
    ext <;> dsimp only <;> omega
  whiskerLeft_id _ _ := rfl
  id_whiskerRight _ _ := rfl
  associator_naturality f₁ f₂ f₃ := by
    change (((f₁.1 + f₂.1) + f₃.1) + 0, 0 + ((f₁.2 + f₂.2) + f₃.2)) =
      (0 + (f₁.1 + (f₂.1 + f₃.1)), (f₁.2 + (f₂.2 + f₃.2)) + 0)
    ext <;> dsimp only <;> omega
  leftUnitor_naturality f := by
    change (f.1 + 0, 0 + f.2) = (0 + f.1, f.2 + 0)
    ext <;> dsimp only <;> omega
  rightUnitor_naturality f := by
    change (f.1 + 0, 0 + f.2) = (0 + f.1, f.2 + 0)
    ext <;> dsimp only <;> omega
  pentagon _ _ _ _ := by
    change ((0 : ℤ) + (0 + 0), (0 + 0) + 0) = ((0 : ℤ) + 0, (0 : ℤ) + 0)
    simp only [add_zero]
  triangle _ _ := by
    change ((0 : ℤ) + 0, (0 : ℤ) + 0) = (0, 0)
    simp only [add_zero]

/-- Resources on `TwoSided.obj` wrap integers; `(l, r)` attaches as `x ↦ l + x + r`. -/
instance : ResourceTheory TwoSided IntResource where
  attach f x := ⟨f.1 + x.val + f.2⟩
  attach_identity x := by
    ext
    change (0 : ℤ) + x.val + 0 = x.val
    omega
  attach_serial f g x := by
    ext
    change (f.1 + g.1) + x.val + (g.2 + f.2) = f.1 + (g.1 + x.val + g.2) + f.2
    omega

/-- Parallel composition of integer resources is addition. -/
noncomputable instance twoSidedLaxMonoidal :
    (ResourceTheory.functor TwoSided IntResource).LaxMonoidal where
  ε := TypeCat.ofHom fun _ => ⟨0⟩
  μ _ _ := TypeCat.ofHom fun p => ⟨p.1.val + p.2.val⟩
  μ_natural_left f _ := by
    ext p
    apply IntResource.ext
    change (f.unop.1 + p.1.val + f.unop.2) + p.2.val =
      f.unop.1 + (p.1.val + p.2.val) + f.unop.2
    omega
  μ_natural_right _ f := by
    ext p
    apply IntResource.ext
    change p.1.val + (f.unop.1 + p.2.val + f.unop.2) =
      f.unop.1 + (p.1.val + p.2.val) + f.unop.2
    omega
  associativity _ _ _ := by
    ext p
    apply IntResource.ext
    change (0 : ℤ) + ((p.1.1.val + p.1.2.val) + p.2.val) + 0 =
      p.1.1.val + (p.1.2.val + p.2.val)
    omega
  left_unitality _ := by
    ext p
    apply IntResource.ext
    change p.2.val = (0 : ℤ) + (0 + p.2.val) + 0
    omega
  right_unitality _ := by
    ext p
    apply IntResource.ext
    change p.1.val = (0 : ℤ) + (p.1.val + 0) + 0
    omega

noncomputable instance : CryptographicAlgebra TwoSided IntResource where
  laxMonoidal := twoSidedLaxMonoidal

/-- Translation-invariant extended pseudo-metric `edist x y = |x.val - y.val|` on `IntResource`. -/
@[instance_reducible]
noncomputable def intPseudoEMetric (A : TwoSided) : PseudoEMetricSpace (IntResource A) where
  edist x y := (Int.natAbs (x.val - y.val) : ENNReal)
  edist_self x := by
    simp only [sub_self, Int.natAbs_zero, Nat.cast_zero]
  edist_comm x y := by
    rw [← neg_sub y.val x.val, Int.natAbs_neg]
  edist_triangle x y z := by
    have h : Int.natAbs (x.val - z.val) ≤
        Int.natAbs (x.val - y.val) + Int.natAbs (y.val - z.val) := by
      omega
    exact_mod_cast h

noncomputable instance : CompatiblePseudoMetric TwoSided IntResource where
  fibreMetric := intPseudoEMetric
  edist_smul_le f x y := by
    have h : (f.1 + x.val + f.2) - (f.1 + y.val + f.2) = x.val - y.val := by omega
    change ((Int.natAbs ((f.1 + x.val + f.2) - (f.1 + y.val + f.2)) : ℕ) : ENNReal) ≤
      (Int.natAbs (x.val - y.val) : ENNReal)
    rw [h]
  edist_parallel_le x x' y y' := by
    have h : Int.natAbs ((x.val + y.val) - (x'.val + y'.val)) ≤
        Int.natAbs (x.val - x'.val) + Int.natAbs (y.val - y'.val) := by
      omega
    change ((Int.natAbs ((x.val + y.val) - (x'.val + y'.val)) : ℕ) : ENNReal) ≤
      (Int.natAbs (x.val - x'.val) : ENNReal) + (Int.natAbs (y.val - y'.val) : ENNReal)
    exact_mod_cast h

/-- Concrete two-party additive setup: protocols and simulators shift the channel by integers. -/
def intSetup :
    TwoPartySetup TwoSided (Phi := IntResource) TwoSided.obj TwoSided.obj TwoSided.obj
      ℤ ℤ ℤ ℤ ℤ where
  realHonest π₁ π₂ R := ⟨π₁ + R + π₂⟩
  realRight π₂ R := ⟨R + π₂⟩
  realLeft π₁ R := ⟨π₁ + R⟩
  simulatedLeft σ₁ S := ⟨σ₁ + S.val⟩
  simulatedRight S σ₂ := ⟨S.val + σ₂⟩

/-- At the neutral channel `R = 0`, two-ended plugging satisfies all three algebraic equations. -/
def intNeutralPlugging : TwoPartyPlugging intSetup (0 : ℤ) ℤ where
  plugRight π₂ := (0, π₂)
  plugLeft S σ₂ := (S.val + σ₂, 0)
  composeBridge σ₂ σ₁ := σ₂ + σ₁
  plugBridge S γ S' := ⟨S.val + γ + S'.val⟩
  plug_honest π₁ π₂ := by
    ext
    change (0 : ℤ) + (π₁ + 0) + π₂ = π₁ + 0 + π₂
    omega
  plug_assoc π₂ σ₂ S := by
    ext
    change (0 : ℤ) + (S.val + σ₂) + π₂ = (S.val + σ₂) + (0 + π₂) + 0
    omega
  plug_compose σ₁ σ₂ S := by
    ext
    change (S.val + σ₂) + (σ₁ + S.val) + 0 = S.val + (σ₂ + σ₁) + S.val
    omega

/-- Non-equality substitution relation on `TwoSided`: congruence modulo 4. -/
def mod4Relation : SubstitutionRelation TwoSided (Phi := IntResource) where
  substitutes _ x y := (4 : ℤ) ∣ (x.val - y.val)
  symmetric _ := { symm := fun _ _ ⟨k, hk⟩ => ⟨-k, by omega⟩ }
  transitive _ := { trans := fun _ _ _ ⟨k₁, h₁⟩ ⟨k₂, h₂⟩ => ⟨k₁ + k₂, by omega⟩ }
  preserved f _ _ := fun ⟨k, hk⟩ => ⟨k, by
    change (f.1 + _ + f.2) - (f.1 + _ + f.2) = 4 * k
    omega⟩

/-- Proper admitted bridge/simulator class: multiples of 4. -/
def multipleOfFour : Set ℤ := {γ | (4 : ℤ) ∣ γ}

lemma multipleOfFour_closed :
    ∀ σ₂ ∈ multipleOfFour, ∀ σ₁ ∈ multipleOfFour,
      intNeutralPlugging.composeBridge σ₂ σ₁ ∈ multipleOfFour := by
  intro σ₂ ⟨k₂, h₂⟩ σ₁ ⟨k₁, h₁⟩
  exact ⟨k₂ + k₁, by change σ₂ + σ₁ = 4 * (k₂ + k₁); omega⟩

/-- Separation from every admitted bridge `γ ∈ multipleOfFour` rules out constructing `1` from
the neutral channel `0` under `mod4Relation`. -/
lemma unconstructible_one_mod4 :
    Unconstructible (intSetup.Constructs mod4Relation multipleOfFour multipleOfFour)
      Set.univ (0 : ℤ) ⟨1⟩ := by
  apply unconstructible_of_bridge_separation intNeutralPlugging mod4Relation multipleOfFour_closed
  intro γ ⟨k, hk⟩ ⟨m, hm⟩
  -- `1 + γ + 1 - 1 = 1 + 4k` cannot be a multiple of 4.
  change (1 + γ + 1) - 1 = 4 * m at hm
  omega

/-- Lifting the simulator restriction makes `1` constructible from `0`: the admitted bridge class
`multipleOfFour` is genuinely retained and load-bearing. -/
lemma constructible_one_mod4_unrestricted :
    Constructible (intSetup.Constructs mod4Relation Set.univ Set.univ)
      Set.univ (0 : ℤ) ⟨1⟩ := by
  refine ⟨(1, 0), trivial, ⟨0, by change (1 + 0 + 0) - 1 = 4 * 0; omega⟩,
    ⟨-1, trivial, ⟨0, by change (0 + 0) - (-1 + 1) = 4 * 0; omega⟩⟩,
    ⟨0, trivial, ⟨0, by change (1 + 0) - (1 + 0) = 4 * 0; omega⟩⟩⟩

/-- Every unrestricted construction yields a composite bridge `γ` (here `γ = -1 ∉ multipleOfFour`)
satisfying `1 + γ + 1 ≡ 1 [mod 4]`. -/
lemma bridge_witness_unrestricted :
    ∃ γ ∈ (Set.univ : Set ℤ),
      mod4Relation.substitutes TwoSided.obj
        (intNeutralPlugging.plugBridge ⟨1⟩ γ ⟨1⟩) ⟨1⟩ :=
  twoParty_bridge_substitutes intNeutralPlugging mod4Relation
    (bridges := Set.univ) (fun _ _ _ _ => trivial) constructible_one_mod4_unrestricted

/-- Proper admitted bridge/simulator class for the quantitative test: nonnegative shifts. -/
def nonnegBridges : Set ℤ := {γ | 0 ≤ γ}

lemma nonnegBridges_closed :
    ∀ σ₂ ∈ nonnegBridges, ∀ σ₁ ∈ nonnegBridges,
      intNeutralPlugging.composeBridge σ₂ σ₁ ∈ nonnegBridges := by
  intro σ₂ h₂ σ₁ h₁
  change 0 ≤ σ₂ at h₂
  change 0 ≤ σ₁ at h₁
  change 0 ≤ σ₂ + σ₁
  omega

/-- Quantitative obstruction: every nonnegative bridge keeps `3 + γ + 3` at distance at least `3`
from `3`, ruling out construction from `0` within budgets `(1, 1, 0)` (sum `2`). -/
lemma unconstructible_three_within :
    Unconstructible (intSetup.ConstructsWithin 1 1 0 nonnegBridges nonnegBridges)
      Set.univ (0 : ℤ) ⟨3⟩ := by
  apply unconstructible_of_bridge_distance_gt intNeutralPlugging nonnegBridges_closed
  intro γ hγ
  change 0 ≤ γ at hγ
  have hlt : 2 < Int.natAbs ((3 + γ + 3) - 3) := by omega
  have hcast : ((2 : ℕ) : ENNReal) < (Int.natAbs ((3 + γ + 3) - 3) : ENNReal) :=
    Nat.cast_lt.mpr hlt
  have htwo : (1 : ENNReal) + 0 + 1 = ((2 : ℕ) : ENNReal) := by
    rw [add_zero, Nat.cast_ofNat, one_add_one_eq_two]
  change (1 : ENNReal) + 0 + 1 < (Int.natAbs ((3 + γ + 3) - 3) : ENNReal)
  rw [htwo]
  exact hcast

/-- Without the `nonnegBridges` restriction, the unadmitted bridge `γ = -3` achieves distance `0`.
-/
lemma unadmitted_bridge_distance_zero :
    Δ (intNeutralPlugging.plugBridge ⟨3⟩ (-3) ⟨3⟩) ⟨3⟩ = 0 := by
  change (Int.natAbs ((3 + (-3) + 3) - 3) : ENNReal) = 0
  have hz : (3 + (-3) + 3 : ℤ) - 3 = 0 := by omega
  rw [hz]
  simp only [Int.natAbs_zero, Nat.cast_zero]

/-- Neutral-channel plugging uses converter attachment notation `•`. -/
example (π₁ π₂ : ℤ) :
    intNeutralPlugging.plugRight π₂ • intSetup.realLeft π₁ (0 : ℤ) =
      intSetup.realHonest π₁ π₂ (0 : ℤ) :=
  intNeutralPlugging.plug_honest π₁ π₂

#print axioms ConstructiveCryptography.Construction.bridge_substitutes_of_equations
#print axioms ConstructiveCryptography.Construction.twoParty_bridge_substitutes
#print axioms ConstructiveCryptography.Construction.unconstructible_of_bridge_separation
#print axioms ConstructiveCryptography.Construction.bridge_distance_le_of_bounds
#print axioms ConstructiveCryptography.Construction.twoParty_bridge_distance_le
#print axioms ConstructiveCryptography.Construction.unconstructible_of_bridge_distance_gt

end Tests.TwoPartyObstruction

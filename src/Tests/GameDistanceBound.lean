module

public import ConstructiveCryptography

/-!
# Abstract and typed distance bounds from distinction-game performance

Exercises `DistinctionGames.distance_visible_le`, `distance_visible_le_of_winners`, and
`distance_visible_le_of_solvers` under CC custom notation (`Δ`, `|≡`, `•`, `≫`), checks the
typed corollaries `Interface.dist_visible_le_of_winners` and `Interface.dist_visible_le_of_win`
with `cc_normalize` and `cc_calc statistical`, and gives a concrete counterexample showing that
a compatible pseudo-metric without solver coverage is insufficient.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.GameDistanceBound

open CategoryTheory CategoryTheory.MonoidalCategory ConstructiveCryptography SystemAlgebra
open scoped SystemAlgebra NNReal

section Abstract

universe u v w x

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CompatibleDistinguisherClass C Phi]
variable {Game : C → Type x} [DistinctionGames C Phi Game]

/-- Conditional equivalence, explicit solver coverage, and a uniform winning bound imply
`Δ (visible G) S ≤ ε` in any `CompatibleDistinguisherClass`. -/
example {A : C} {G : Game A} {S : Phi A} (hc : G |≡ S)
    (hcover : ∀ d ∈ CompatibleDistinguisherClass.distinguishers (Phi := Phi) A,
      ∃ w : Game A → ℝ, (d, w) ∈ DistinctionGames.solvers A)
    {ε : ℝ≥0} (hwin : ∀ w ∈ Games.winners A, w G ≤ ε) :
    Δ (DistinctionGames.visible G) S ≤ ε :=
  DistinctionGames.distance_visible_le hc hcover hwin

/-- The `ENNReal` winner-bound variant and the direct solver-bound variant agree cleanly. -/
example {A : C} {G : Game A} {S : Phi A} (hc : G |≡ S)
    (hcover : ∀ d ∈ CompatibleDistinguisherClass.distinguishers (Phi := Phi) A,
      ∃ w : Game A → ℝ, (d, w) ∈ DistinctionGames.solvers A)
    {ε : ℝ≥0} (hwin : ∀ w ∈ Games.winners A, w G ≤ ε)
    (hsolv : ∀ s ∈ DistinctionGames.solvers A, s.2 G ≤ ε) :
    Δ (DistinctionGames.visible G) S ≤ (ε : ENNReal) ∧
      Δ (DistinctionGames.visible G) S ≤ ε :=
  ⟨DistinctionGames.distance_visible_le_of_winners hc hcover fun w hw =>
      (ENNReal.ofReal_le_ofReal (hwin w hw)).trans (by simp),
    DistinctionGames.distance_visible_le_of_solvers hc hcover hsolv⟩

/-- Abstract distance bounds compose with converter attachment and `cc_calc statistical`. -/
example {A B D : C} (α : A ⟶ B) (β : B ⟶ D) {G : Game D} {S : Phi D} (hc : G |≡ S)
    (hcover : ∀ d ∈ CompatibleDistinguisherClass.distinguishers (Phi := Phi) D,
      ∃ w : Game D → ℝ, (d, w) ∈ DistinctionGames.solvers D)
    {ε : ℝ≥0} (hwin : ∀ w ∈ Games.winners D, w G ≤ ε) :
    Δ ((α ≫ β) • DistinctionGames.visible G) ((α ≫ β) • S) ≤ ε := by
  have hdist : Δ (DistinctionGames.visible G) S ≤ ε :=
    DistinctionGames.distance_visible_le hc hcover hwin
  cc_calc statistical
    (α ≫ β) • DistinctionGames.visible G = α • (β • DistinctionGames.visible G) :=
      ResourceTheory.attach_serial α β _
    _ ≈[ε] α • (β • S) := by
      exact (CryptographicAlgebra.distance_attach_le α _ _).trans
        ((CryptographicAlgebra.distance_attach_le β _ _).trans hdist)
    _ = (α ≫ β) • S := (ResourceTheory.attach_serial α β _).symm

end Abstract

section TypedCorollaries

/-- Typed corollaries derive `Δ G.visible T ≤ ε` from conditional equivalence and a uniform
winner or distinguisher bound without unfolding transcript distance, and compose with
`cc_normalize` and `cc_calc statistical`. -/
example {A B D : Interface} (α : A ⟶ B) (β : B ⟶ D) {G : TypedGame D} {T : TypedSystem D}
    (hc : G |≡ T) {ε : ℝ≥0}
    (hW : ∀ P : D.inputDomain.Distinguisher, P.winProbability G.1.1 ≤ ε) :
    Δ G.visible T ≤ ε ∧
      Δ (α • (β • G.visible)) ((α ≫ β) • T) ≤ ε := by
  have hdist : Δ G.visible T ≤ ε := Interface.dist_visible_le_of_win hc hW
  refine ⟨hdist, ?_⟩
  cc_calc statistical
    α • (β • G.visible) = (α ≫ β) • G.visible := by cc_normalize
    _ ≈[ε] (α ≫ β) • T := hdist

/-- `Interface.dist_visible_le_of_winners` accepts a uniform bound on `Games.winners A` directly. -/
example {A : Interface} {G : TypedGame A} {T : TypedSystem A}
    (hc : G |≡ T) {ε : ℝ≥0}
    (hwin : ∀ w ∈ Games.winners A, w G ≤ ε) :
    Δ G.visible T ≤ ε :=
  Interface.dist_visible_le_of_winners hc hwin

end TypedCorollaries

section Counterexample

/-- Trivial one-object discrete category for the solver-coverage counterexample. -/
inductive OneObj : Type
  | pt

instance : Category OneObj where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()

instance : MonoidalCategoryStruct OneObj where
  tensorObj _ _ := .pt
  tensorHom _ _ := ()
  whiskerLeft _ _ _ _ := ()
  whiskerRight _ _ := ()
  tensorUnit := .pt
  associator _ _ _ := Iso.refl OneObj.pt
  leftUnitor _ := Iso.refl OneObj.pt
  rightUnitor _ := Iso.refl OneObj.pt

instance : MonoidalCategory OneObj :=
  MonoidalCategory.ofTensorHom (fun _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ => rfl)

/-- Constant `Bool` resource family on `OneObj` with `parallel = xor` and `dummy = false`. -/
abbrev BoolRes : OneObj → Type := fun _ => Bool

instance : ResourceTheory OneObj BoolRes where
  attach _ := id
  attach_identity _ := rfl
  attach_serial _ _ _ := rfl

/-- `BoolRes` carries a lax monoidal structure with `parallel = Bool.xor` and `dummy = false`. -/
instance boolLaxMonoidal :
    (ResourceTheory.functor OneObj BoolRes).LaxMonoidal where
  ε := TypeCat.ofHom fun _ => false
  μ _ _ := TypeCat.ofHom fun p : Bool × Bool => xor p.1 p.2
  μ_natural_left _ _ := rfl
  μ_natural_right _ _ := rfl
  associativity _ _ _ := by
    ext ⟨⟨a, b⟩, c⟩
    cases a <;> cases b <;> cases c <;> rfl
  left_unitality _ := by
    ext ⟨_, b⟩
    cases b <;> rfl
  right_unitality _ := by
    ext ⟨b, _⟩
    cases b <;> rfl

instance : CryptographicAlgebra OneObj BoolRes where
  laxMonoidal := boolLaxMonoidal

/-- Two indicator distinguishers on `Bool`: closed under `id` and `xor`. -/
def boolDistinguishers : OneObj → Set (Bool → ℝ)
  | .pt => {fun b => if b then 1 else 0, fun b => if b then 0 else 1}

lemma boolDistinguishers_closed_parallel_left (T : BoolRes .pt) {d : BoolRes .pt → ℝ}
    (hd : d ∈ boolDistinguishers .pt) :
    (fun R : BoolRes .pt =>
      d (CryptographicAlgebra.parallel (C := OneObj) (Phi := BoolRes)
        (A := .pt) (B := .pt) R T)) ∈ boolDistinguishers .pt := by
  change (fun R : Bool => d (xor R T)) ∈ boolDistinguishers .pt
  rcases hd with rfl | rfl <;> cases T
  · left; funext b; cases b <;> rfl
  · right; funext b; cases b <;> rfl
  · right; funext b; cases b <;> rfl
  · left; funext b; cases b <;> rfl

lemma boolDistinguishers_closed_parallel_right (T : BoolRes .pt) {d : BoolRes .pt → ℝ}
    (hd : d ∈ boolDistinguishers .pt) :
    (fun S : BoolRes .pt =>
      d (CryptographicAlgebra.parallel (C := OneObj) (Phi := BoolRes)
        (A := .pt) (B := .pt) T S)) ∈ boolDistinguishers .pt := by
  change (fun S : Bool => d (xor T S)) ∈ boolDistinguishers .pt
  rcases hd with rfl | rfl <;> cases T
  · left; funext b; cases b <;> rfl
  · right; funext b; cases b <;> rfl
  · right; funext b; cases b <;> rfl
  · left; funext b; cases b <;> rfl

/-- Full `CompatibleDistinguisherClass` whose advantage metric separates `false` and `true`
at distance `1`. -/
noncomputable instance : CompatibleDistinguisherClass OneObj BoolRes :=
  CompatibleDistinguisherClass.ofClosure boolDistinguishers
    (fun {A B} _ _ hd => by
      cases A; cases B
      exact hd)
    (fun {A B} T _ hd => by
      cases A; cases B
      exact boolDistinguishers_closed_parallel_left T hd)
    (fun {A B} T _ hd => by
      cases A; cases B
      exact boolDistinguishers_closed_parallel_right T hd)

/-- Constant `Unit` game family whose only admitted solver is `(0, 0)`: every winner scores `0`,
every conditional equivalence holds, yet solver coverage fails. -/
abbrev ZeroGame : OneObj → Type := fun _ => Unit

instance : Games OneObj ZeroGame ℝ where
  winners _ := {fun _ => 0}

instance : DistinctionGames OneObj BoolRes ZeroGame where
  solvers _ := {(fun _ => 0, fun _ => 0)}
  solvers_winner := by
    rintro _ _ rfl
    rfl
  visible _ := false
  ConditionallyEquivalent _ _ := True
  advantage_le_win := by
    rintro _ _ _ _ _ rfl
    simp

/-- Counterexample: `CompatibleDistinguisherClass` (hence `CompatiblePseudoMetric`),
`G |≡ S`, and `∀ w ∈ Games.winners .pt, w G ≤ 0` all hold, yet `Δ (visible G) S = 1 ≰ 0`
because solver coverage fails. -/
theorem coverage_required_counterexample :
    DistinctionGames.ConditionallyEquivalent (I := OneObj) (Phi := BoolRes) (Game := ZeroGame)
        (A := .pt) () true ∧
      (∀ w ∈ Games.winners (I := OneObj) (Game := ZeroGame) .pt, w () ≤ (0 : ℝ≥0)) ∧
      ¬ (CryptographicAlgebra.distance (C := OneObj) (Phi := BoolRes) (A := .pt)
          (DistinctionGames.visible (I := OneObj) (Phi := BoolRes) (Game := ZeroGame) (A := .pt) ())
          true ≤ (0 : ℝ≥0)) := by
  refine ⟨trivial, fun w hw => by simp [Games.winners] at hw; simp [hw], ?_⟩
  intro hle
  have h1 : ENNReal.ofReal |(if false then (1 : ℝ) else 0) - (if true then 1 else 0)| ≤
      CryptographicAlgebra.distance (C := OneObj) (Phi := BoolRes) (A := .pt)
        (DistinctionGames.visible (I := OneObj) (Phi := BoolRes) (Game := ZeroGame) (A := .pt) ())
        true := by
    change ENNReal.ofReal _ ≤ advantageDistance (boolDistinguishers .pt) false true
    exact le_advantageDistance
      (show (fun b : Bool => if b then (1 : ℝ) else 0) ∈ boolDistinguishers .pt from Or.inl rfl)
      false true
  have hge : (1 : ENNReal) ≤ 0 := by
    have h01 : ENNReal.ofReal |(if false then (1 : ℝ) else 0) - (if true then 1 else 0)| = 1 := by
      norm_num
    rw [h01] at h1
    exact h1.trans (by simpa using hle)
  exact not_le_of_gt (zero_lt_one (α := ENNReal)) hge

end Counterexample

#print axioms ConstructiveCryptography.DistinctionGames.distance_visible_le_of_winners
#print axioms ConstructiveCryptography.DistinctionGames.distance_visible_le
#print axioms ConstructiveCryptography.DistinctionGames.distance_visible_le_of_solvers
#print axioms SystemAlgebra.Interface.distinguishers_covered_by_solvers
#print axioms SystemAlgebra.Interface.dist_visible_le_of_winners
#print axioms SystemAlgebra.Interface.dist_visible_le_of_win
#print axioms Tests.GameDistanceBound.coverage_required_counterexample

end Tests.GameDistanceBound

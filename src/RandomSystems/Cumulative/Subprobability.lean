import RandomSystems.Cumulative.Cumulative
import Probability.Lift

/-!
# Random systems with stopping

When a system may stop, the reply probabilities at a query sum to at most the
probability of the preceding transcript; the difference is the probability of
stopping. Exact normalization on a domain is a separate property.

## Main definitions

* `IsSubprobabilistic p`: cumulative probabilities that may lose mass
* `NormalizedOn D p`: exact normalization on the domain `D`
* `IsSubprobabilistic.replyChoice`: the law of the next reply or of stopping

## Main results

* `isRandomSystem_iff_normalizedOn`: a random system is a normalized system with
  stopping
* `isSubprobabilistic_behaviorMass`: every finite mixture has this form
-/

namespace SystemAlgebra

open Classical Probability

variable {A B : Type}

/-- Finite next-reply laws may lose mass when interaction stops. -/
def IsSubprobabilistic (p : List (A × B) → ℝ) : Prop :=
  p [] = 1 ∧ (∀ h, 0 ≤ p h) ∧
    ∀ h x, ∃ μ : Distribution B,
      (∀ y, μ y = p (h ++ [(x, y)])) ∧ μ.weight ≤ p h

/-- Exact response probability on an advertised domain. -/
def NormalizedOn (D : List (A × B) → A → Prop) (p : List (A × B) → ℝ) : Prop :=
  ∀ h x (μ : Distribution B), (∀ y, μ y = p (h ++ [(x, y)])) →
    μ.weight = if D h x then p h else 0

theorem IsRandomSystem.isSubprobabilistic {D : List (A × B) → A → Prop}
    {p : List (A × B) → ℝ} (hp : IsRandomSystem D p) : IsSubprobabilistic p := by
  refine ⟨hp.1, hp.2.1, fun h x => ?_⟩
  obtain ⟨μ, hμ, hw⟩ := hp.2.2 h x
  refine ⟨μ, hμ, ?_⟩
  rw [hw]
  split_ifs
  · exact le_rfl
  · exact hp.2.1 h

theorem isRandomSystem_iff_normalizedOn {D : List (A × B) → A → Prop}
    {p : List (A × B) → ℝ} :
    IsRandomSystem D p ↔ IsSubprobabilistic p ∧ NormalizedOn D p := by
  constructor
  · intro hp
    refine ⟨hp.isSubprobabilistic, fun h x μ hμ => ?_⟩
    obtain ⟨ν, hν, hw⟩ := hp.2.2 h x
    have he : μ = ν := Finsupp.ext (fun y => (hμ y).trans (hν y).symm)
    exact he.symm ▸ hw
  · rintro ⟨hp, hd⟩
    refine ⟨hp.1, hp.2.1, fun h x => ?_⟩
    obtain ⟨μ, hμ, _⟩ := hp.2.2 h x
    exact ⟨μ, hμ, hd h x μ hμ⟩

theorem isSubprobabilistic_behaviorMass {P : System A B → Prop}
    (μ : Distribution {s : System A B // P s}) (hμ : μ.isProbDist) :
    IsSubprobabilistic (fun h => behaviorMass μ (h.map Prod.fst) (h.map Prod.snd)) := by
  refine ⟨?_, fun h => hμ.1.mass_nonneg _, fun h x => ?_⟩
  · simpa using (PDS.behaviorMass_nil μ).trans hμ.2
  · exact ⟨PDS.nextReply μ (h.map Prod.fst) (h.map Prod.snd) x,
      fun y => by simpa using PDS.nextReply_apply μ (h.map Prod.fst) (h.map Prod.snd) x y,
      PDS.nextReply_weight_le μ hμ.1 _ _ _⟩

namespace IsSubprobabilistic

variable {p : List (A × B) → ℝ} (hp : IsSubprobabilistic p)

noncomputable def extensionLaw (h : List (A × B)) (x : A) : Distribution B :=
  (hp.2.2 h x).choose

theorem extensionLaw_apply (h : List (A × B)) (x : A) (y : B) :
    hp.extensionLaw h x y = p (h ++ [(x, y)]) := (hp.2.2 h x).choose_spec.1 y

theorem extensionLaw_nonneg (h : List (A × B)) (x : A) :
    (hp.extensionLaw h x).NonNeg := by
  intro y
  rw [hp.extensionLaw_apply]
  exact hp.2.1 _

theorem extensionLaw_weight_le (h : List (A × B)) (x : A) :
    (hp.extensionLaw h x).weight ≤ p h := (hp.2.2 h x).choose_spec.2

include hp in
theorem mass_snoc_le (h : List (A × B)) (x : A) (y : B) :
    p (h ++ [(x, y)]) ≤ p h := by
  rw [← hp.extensionLaw_apply]
  exact ((Distribution.apply_le_mass (hp.extensionLaw_nonneg h x) rfl).trans
    (Distribution.mass_le_weight (hp.extensionLaw_nonneg h x) _)).trans
      (hp.extensionLaw_weight_le h x)

include hp in
theorem mass_eq_zero_of_prefix {h k : List (A × B)} (hk : h <+: k) (hz : p h = 0) :
    p k = 0 := by
  obtain ⟨e, rfl⟩ := hk
  induction e using List.reverseRecOn with
  | nil => simpa using hz
  | append_singleton e z ih =>
    rw [← List.append_assoc]
    exact le_antisymm (ih ▸ hp.mass_snoc_le _ z.1 z.2) (hp.2.1 _)

/-- A finite sampling choice is either a reply or no reply. `none` is used
only in this probability space; the resulting system still has output type `B`. -/
noncomputable def replyChoice (h : List (A × B)) (x : A) : Distribution (Option B) :=
  let μ : Distribution B := (hp.extensionLaw h x).mapRange (fun w => w / p h) (zero_div _)
  Distribution.fTransform some μ + Finsupp.single none (1 - μ.weight)

theorem replyChoice_some (h : List (A × B)) (x : A) (y : B) :
    hp.replyChoice h x (some y) = p (h ++ [(x, y)]) / p h := by
  simp only [replyChoice, Finsupp.add_apply,
    Distribution.fTransform_injective_apply _ _ (Option.some_injective B),
    Finsupp.mapRange_apply, hp.extensionLaw_apply, Finsupp.single_apply,
    reduceCtorEq, if_false, add_zero]

theorem replyChoice_isProbDist (h : List (A × B)) (x : A) :
    (hp.replyChoice h x).isProbDist := by
  let μ : Distribution B := (hp.extensionLaw h x).mapRange (fun w => w / p h) (zero_div _)
  have hn : μ.NonNeg := fun y => div_nonneg (hp.extensionLaw_nonneg h x y) (hp.2.1 h)
  have hw : μ.weight ≤ 1 := by
    rw [show μ.weight = (hp.extensionLaw h x).weight / p h from
      Distribution.weight_mapRange_div _ _]
    by_cases hz : p h = 0
    · simp [hz]
    · exact (div_le_one (lt_of_le_of_ne (hp.2.1 h) (Ne.symm hz))).mpr
        (hp.extensionLaw_weight_le h x)
  constructor
  · intro y
    change 0 ≤ Distribution.fTransform some μ y + Finsupp.single none (1 - μ.weight) y
    apply add_nonneg (hn.fTransform some y)
    rw [Finsupp.single_apply]
    split_ifs
    · exact sub_nonneg.mpr hw
    · exact le_rfl
  · change (Distribution.fTransform some μ + Finsupp.single none (1 - μ.weight)).weight = 1
    rw [Distribution.weight_add, Distribution.weight_fTransform]
    rw [Distribution.weight_single]
    ring

end IsSubprobabilistic

end SystemAlgebra

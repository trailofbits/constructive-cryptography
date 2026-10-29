import ConstructiveCryptography.Distinguisher
import ConstructiveCryptography.Substitution.Reduction

set_option autoImplicit false

/-!
# Absorption and admitted reductions

A converter `α : A ⟶ B` acts on distinguishers from the distinguisher end: `dα` on `B` first
attaches `α` to the tested resource, then runs `d`. Both groupings of the same experiment
give the same decision, so the advantage is unchanged:

```text
d ── α ── β ── R        (dα)β = d(α ≫ β)      advantage(dα, R, S) = advantage(d, αR, αS)
```

Absorption alone says nothing about admission. A reduction through `α` needs the explicit
proof `AdmissibleDistinguishers.ClosedUnder α` that `dα` is admitted whenever `d` is; no class
is assumed closed under every converter, and none of these laws asserts computational
efficiency. Given that proof, a substitution between `R` and `S` within `ε` transports to
`αR`, `αS` within the loss evaluated at the actual reduced distinguisher, `d ↦ ε(dα)`.

## Main definitions

* `DistinguisherAction C Phi D`: absorption of converters into distinguishers
* `AdmissibleDistinguishers.ClosedUnder α`: `α` preserves the selected admitted tests
* `DistinguisherAdvantage.DominatedByDistance model`: the advantages of `model` are bounded by
  the selected resource metric

## Main results

* `DistinguisherAction.advantage_absorb`: absorption preserves absolute advantage
* `ClosedUnder.identity`, `ClosedUnder.comp`: closure proofs compose in category order
* `AdmissibleDistinguishers.substitutesWithin_attach`, `substitutesWithin_context`: substitution
  through an admission-preserving converter
* `AdmissibleDistinguishers.all_closedUnder`: under the local `all` choice every converter
  preserves admission

Sources: Banfi, §2.3.3 (printed p. 16), for the transformed loss; MR16, §4.3 (printed
pp. 12–13), for closure under selected converters only.
-/

namespace ConstructiveCryptography

open CategoryTheory CryptographicAlgebra

universe u v w x

/-- The action of the CC converters on decision evaluations, independently of admission.
Banfi §2.3.3 (printed p. 16) writes the composed distinguisher as `Dκρ`. -/
class DistinguisherAction
    -- `C` contains interfaces; `α : A ⟶ B` is a converter with outside `A` and inside `B`.
    (C : Type u) [Category.{v} C]
    -- `Phi A` contains resources on `A`, acted on by the selected resource theory.
    (Phi : C → Type w) [outParam (ResourceTheory C Phi)]
    -- `D A` contains distinguishers on `A`, with the selected decision evaluation.
    (D : C → Type x) [outParam (Distinguishers C Phi D)] where
  /-- Absorption puts the converter between the distinguisher and the resource: `d` on `A`
  and `α : A ⟶ B` give `dα` on `B`. -/
  absorb : ∀ {A B : C}, D A → (A ⟶ B) → D B
  /-- Both groupings of `d ── α ── R` give the same decision: `(dα)(R) = d(αR)`. -/
  probability_absorb : ∀ {A B : C} (d : D A) (α : A ⟶ B) (R : Phi B),
    Distinguishers.probability (absorb d α) R = Distinguishers.probability d (α • R)
  /-- The identity converter leaves the distinguisher unchanged: `d𝟙 = d`. -/
  absorb_id : ∀ {A : C} (d : D A), absorb d (𝟙 A) = d
  /-- Absorption follows category order from the distinguisher end: `d(α ≫ β) = (dα)β`. -/
  absorb_comp : ∀ {A B E : C} (d : D A) (α : A ⟶ B) (β : B ⟶ E),
    absorb d (α ≫ β) = absorb (absorb d α) β

namespace DistinguisherAction

variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {D : C → Type x} [Distinguishers C Phi D] [DistinguisherAction C Phi D]

/-- Regrouping the same experiment preserves absolute advantage:
`advantage(dα, R, S) = advantage(d, αR, αS)`, from `probability_absorb` at `R` and `S`. -/
lemma advantage_absorb {A B : C} (d : D A) (α : A ⟶ B) (R S : Phi B) :
    Distinguishers.advantage (absorb (Phi := Phi) d α) R S =
      Distinguishers.advantage d (α • R) (α • S) := by
  simp only [Distinguishers.advantage, probability_absorb]

end DistinguisherAction

namespace AdmissibleDistinguishers

-- Interfaces `C` with converters, resources `Phi A`, distinguishers `D A` with decision
-- evaluation and absorption, and the selected admitted tests `admissible A`.
variable {C : Type u} [Category.{v} C] {Phi : C → Type w} [ResourceTheory C Phi]
  {D : C → Type x} [Distinguishers C Phi D] [DistinguisherAction C Phi D]
  [AdmissibleDistinguishers C D]

/-- The converter `α : A ⟶ B` preserves the selected admitted tests: every admitted `d` on `A`
gives an admitted `dα` on `B`. A proof obligation for the particular reduction, not a global
closure axiom; MR16, §4.3 (printed pp. 12–13), likewise asks closure only for selected
converters. -/
def ClosedUnder {A B : C} (α : A ⟶ B) : Prop :=
  ∀ d : D A, d ∈ admissible A → DistinguisherAction.absorb (Phi := Phi) d α ∈ admissible B

/-- The identity preserves every admitted class, since `d𝟙 = d`. -/
lemma ClosedUnder.identity (A : C) : ClosedUnder (Phi := Phi) (D := D) (𝟙 A) := by
  intro d hd
  simpa only [DistinguisherAction.absorb_id] using hd

/-- Closure proofs compose in category order: if `α : A ⟶ B` and `β : B ⟶ E` preserve
admission, so does `α ≫ β`, since `d(α ≫ β) = (dα)β` and admission passes `d ↦ dα ↦ (dα)β`. -/
lemma ClosedUnder.comp {A B E : C} {α : A ⟶ B} {β : B ⟶ E}
    (hα : ClosedUnder (Phi := Phi) (D := D) α) (hβ : ClosedUnder (Phi := Phi) (D := D) β) :
    ClosedUnder (Phi := Phi) (D := D) (α ≫ β) := by
  intro d hd
  rw [DistinguisherAction.absorb_comp]
  exact hβ _ (hα d hd)

/-- **Substitution through an admission-preserving converter.** If `R`, `S` substitute within
`ε` for the admitted tests on `B`, then `αR`, `αS` substitute within `d ↦ ε(dα)` on `A`. The
loss is evaluated at the actual reduced distinguisher, not a worst case over `B`. Banfi
§2.3.3 (printed p. 16): `ε′(Dκ) = ε(Dκρ)`. This instantiates
`DistinguisherAdvantage.SubstitutesWithin.attach` with `reduce d = dα`:

```text
advantage(d, αR, αS) = advantage(dα, R, S) ≤ ε(dα)     dα admitted by `closed`
```
-/
lemma substitutesWithin_attach {A B : C} (α : A ⟶ B)
    -- `closed`: `α` maps admitted tests on `A` to admitted tests on `B`; `error = ε` is the
    -- budget on `B`; `R S : Phi B` is the inner pair.
    (closed : ClosedUnder (Phi := Phi) (D := D) α) {error : D B → ENNReal} {R S : Phi B}
    -- `h`: every admitted `d'` on `B` has `advantage(d', R, S) ≤ ε(d')`.
    (h : (Distinguishers.distinguisherAdvantage (Phi := Phi) admissible).SubstitutesWithin
      error R S) :
    (Distinguishers.distinguisherAdvantage (Phi := Phi) admissible).SubstitutesWithin
      (fun d => error (DistinguisherAction.absorb (Phi := Phi) d α)) (α • R) (α • S) :=
  DistinguisherAdvantage.SubstitutesWithin.attach
    (Distinguishers.distinguisherAdvantage (Phi := Phi) admissible) α
    (fun d => DistinguisherAction.absorb (Phi := Phi) d α) closed
    (fun d R S => (DistinguisherAction.advantage_absorb (Phi := Phi) d α R S).symm) h

/-- `substitutesWithin_attach` with the outer endpoints named: given exact equalities
`αR = X` and `αS = Y`, the pair `X`, `Y` substitutes within `d ↦ ε(dα)`. The equalities keep
the systems of a substitution chain visible; by default they are closed by unfolding the
action and serial attachment. -/
lemma substitutesWithin_context {A B : C} (α : A ⟶ B)
    (closed : ClosedUnder (Phi := Phi) (D := D) α) {error : D B → ENNReal} {R S : Phi B}
    (h : (Distinguishers.distinguisherAdvantage (Phi := Phi) admissible).SubstitutesWithin
      error R S) {X Y : Phi A}
    -- `hX`, `hY`: the context applied to the inner pair is the displayed outer pair `X`, `Y`.
    (hX : α • R = X := by
      simp only [CryptographicAlgebra.smul_eq_attach, ResourceTheory.attach_serial] <;> rfl)
    (hY : α • S = Y := by
      simp only [CryptographicAlgebra.smul_eq_attach, ResourceTheory.attach_serial] <;> rfl) :
    (Distinguishers.distinguisherAdvantage (Phi := Phi) admissible).SubstitutesWithin
      (fun d => error (DistinguisherAction.absorb (Phi := Phi) d α)) X Y := by
  subst hX hY
  exact substitutesWithin_attach α closed h

/-- When `AdmissibleDistinguishers.all` is installed locally, every converter preserves
admission, since every `dα` lies in `Set.univ`. The statement installs `all` only inside its
own type; it is not a global instance. -/
lemma all_closedUnder {C : Type u} [Category.{v} C] {Phi : C → Type w}
    [ResourceTheory C Phi] {D : C → Type x} [Distinguishers C Phi D]
    [DistinguisherAction C Phi D] {A B : C} (α : A ⟶ B) :
    letI : AdmissibleDistinguishers C D := all
    ClosedUnder (Phi := Phi) (D := D) α :=
  fun _ _ => Set.mem_univ _

end AdmissibleDistinguishers

namespace CryptographicAlgebra.DistinguisherAdvantage

/-- The admitted advantages of `model` are bounded by the selected resource metric:
`advantage(d, R, S) ≤ Δ(R, S)` for admitted `d`. Both the model and the metric (through its
`CompatiblePseudoMetric` instance) occur in the class index, so an instance neither selects
nor changes either. Only statistical steps of a substitution chain need it. -/
class DominatedByDistance
    -- Interfaces `C` with converters and `⊗`, resources `Phi A` with the selected metric
    -- `distance`, and candidate distinguishers `D A`.
    {C : Type u} [Category.{v} C] [MonoidalCategory C] {Phi : C → Type w}
    [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi] {D : C → Type x}
    -- `model` fixes the admitted tests and their per-test advantage.
    (model : DistinguisherAdvantage C Phi D) : Prop where
  /-- Every admitted `d` has advantage at most the selected distance. -/
  advantage_le_distance : ∀ {A : C} (d : D A), d ∈ model.admissible A →
    ∀ R S : Phi A, model.advantage A d R S ≤ distance R S

end CryptographicAlgebra.DistinguisherAdvantage

end ConstructiveCryptography

import ConstructiveCryptography.Notation.Basic
import ConstructiveCryptography.Tactics.Substitution

/-!
# Admission and abstract calculation checks

A one-interface model: resources are `R : Bool → Bool`, answering a Boolean query `b` with
`R b`; a point test `d : Bool` queries `d` and evaluates to `1` if `R d` and `0` otherwise; a
converter `f : Bool → Bool` rewrites the query, `f • R = R ∘ f`, and absorbs as `f d`. Only the
test `false` is admitted. The identity preserves this class, but negation sends `false` to
`true`, so closure under a converter is a hypothesis to prove, not an ambient axiom.

The generic calculations infer the model from their goal. The mixed calculation accepts a
statistical step only with a `DominatedByDistance` instance for that model, and a premise
stated for a different model does not prove the goal's substitution. No random-system
instance is imported.
-/

namespace DistinguisherActionTests

open CategoryTheory ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra

-- A single interface; an arrow `f : Bool → Bool` rewrites the query, composing in diagram order.
local instance queryCategory : Category Unit where
  Hom _ _ := Bool → Bool
  id _ := id
  comp f g := g ∘ f

-- Resource `R` answers `b` with `R b`, and `f • R` answers `b` with `R (f b)`.
local instance queryResources : ResourceTheory Unit (fun _ => Bool → Bool) where
  attach f R := R ∘ f
  attach_identity _ := rfl
  attach_serial _ _ _ := rfl

-- Point test `d` evaluates to `1` if `R d` holds and to `0` otherwise.
local instance queryEvaluations : Distinguishers Unit (fun _ => Bool → Bool) (fun _ => Bool) where
  probability d R := if R d then 1 else 0

-- Absorbing `f` changes the queried point from `d` to `f d`: `(f d)(R) = R (f d) = d(f • R)`.
local instance queryAction :
    DistinguisherAction Unit (fun _ => Bool → Bool) (fun _ => Bool) where
  absorb d f := f d
  probability_absorb _ _ _ := rfl
  absorb_id _ := rfl
  absorb_comp _ _ _ := rfl

-- Only the query false is admitted, on the unique interface.
local instance falseQuery : AdmissibleDistinguishers Unit (fun _ => Bool) where
  admissible _ := {false}

/-- The identity preserves `{false}`, with no closure under other query transformations. -/
example : AdmissibleDistinguishers.ClosedUnder
    (Phi := fun _ : Unit => Bool → Bool) (D := fun _ => Bool) (𝟙 ()) :=
  AdmissibleDistinguishers.ClosedUnder.identity ()

/-- Negating the query leaves the admitted set: absorbing `Bool.not` sends `false` to `true`. -/
lemma not_closedUnder_not : ¬ AdmissibleDistinguishers.ClosedUnder
    (Phi := fun _ : Unit => Bool → Bool) (D := fun _ => Bool)
    (A := ()) (B := ()) (Bool.not : () ⟶ ()) := by
  intro h
  have bad := h false rfl
  change true = false at bad
  cases bad

section Generic

-- An arbitrary cryptographic setting with a selected metric, and an explicit `model` of admitted
-- tests `D A` and their advantage; `loss` and `ε` are a per-test and a scalar budget.
variable {C : Type} [Category C] [MonoidalCategory C] {Phi D : C → Type}
  [ResourceTheory C Phi] [CompatiblePseudoMetric C Phi] (model : DistinguisherAdvantage C Phi D)
  {A : C} {R S T : Phi A} {loss : D A → ENNReal} {ε : ENNReal}

/-- The inferred form reads this exact model from the substitution goal. -/
example (h : model.SubstitutesWithin loss R S) : model.SubstitutesWithin loss R S := by
  cc_calc quantitative
    R ≃[loss] S := h

/-- A statistical step `≈[ε]` is available once domination holds for this model and metric. -/
example [model.DominatedByDistance] (h : model.SubstitutesWithin loss R S)
    (bound : Δ S T ≤ ε) : model.SubstitutesWithin (fun d => loss d + ε) R T := by
  cc_calc mixed
    R ≃[loss] S := h
    _ ≈[ε] T := bound

/-- Without a `DominatedByDistance model` instance, the same distance bound is not converted. -/
example (_bound : Δ R S ≤ ε) : True := by
  fail_if_success
    have : model.SubstitutesWithin (fun _ => ε) R S := by
      cc_calc mixed
        R ≈[ε] S := _bound
  trivial

end Generic

/-- The inferred `cc_calc quantitative` reads `_model` from the goal, so a premise `_h` for the
distinct model `other` (same interfaces `I`, resources `Phi`, tests `D`) is rejected. -/
example {I : Type} {Phi D : I → Type} (_model other : DistinguisherAdvantage I Phi D)
    {A : I} {R S : Phi A} {loss : D A → ENNReal}
    (_h : other.SubstitutesWithin loss R S) : True := by
  fail_if_success
    have : _model.SubstitutesWithin loss R S := by
      cc_calc quantitative
        R ≃[loss] S := _h
  trivial

#print axioms not_closedUnder_not

end DistinguisherActionTests

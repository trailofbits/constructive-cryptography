import ConstructiveCryptography.Specification.Relaxation.Basic
import Mathlib.Order.Closure

set_option autoImplicit false

/-!
# Idempotent relaxation

A pointwise relaxation with a proved idempotence law is a `ClosureOperator` on
specifications. General monotone extensive maps use `ClosureOperator.mk'`
directly when the required idempotence inclusion is available.
-/

namespace ConstructiveCryptography.Relaxation

universe u
variable {X : Type u}

/-- An idempotent relaxation as a Mathlib closure operator.

MR16, Section 3.4, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”. Jost's general definition
(Definition 2.2.6, printed p. 20) supplies reflexivity; idempotence is an
additional hypothesis of this specialization. -/
def toClosureOperator (relaxation : Relaxation X)
    (idempotent : ∀ source, relaxation (relaxation source) = relaxation source) :
    ClosureOperator (Specification X) where
  toFun := relaxation
  monotone' := relaxation.mono
  le_closure' := relaxation.subset_apply
  idempotent' := idempotent

end ConstructiveCryptography.Relaxation

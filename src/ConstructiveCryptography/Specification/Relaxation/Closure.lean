import ConstructiveCryptography.Specification.Relaxation.Basic
import Mathlib.Order.Closure

set_option autoImplicit false

/-!
# Idempotent relaxation

A pointwise relaxation with a proved idempotence law is a `ClosureOperator` on
specifications. General monotone extensive maps use `ClosureOperator.mk'`
directly when the required idempotence inclusion is available.

A Mathlib `ClosureOperator` on the inclusion order of `Specification X` is a map `c` with

```text
R ⊆ S → c R ⊆ c S       (monotone)
R ⊆ c R                 (extensive: closure only weakens a specification)
c (c R) = c R           (idempotent)
```

Every relaxation is monotone and extensive (`Relaxation.mono`, `Relaxation.subset_apply`);
idempotence need not hold, since two steps of the ε-relaxation are only shown to stay within
`ε + ε` (`Specification.epsilonRelaxation_epsilonRelaxation_subset`). It is therefore a
hypothesis of `toClosureOperator`; `Relaxation.kernel_idem` supplies it for the kernel
relaxation. Converter-class closure (`Specification.starClosure`) is instead built directly
with `ClosureOperator.mk'`.
-/

namespace ConstructiveCryptography.Relaxation

universe u
-- `X` is the type of resources; `Specification X` is ordered by inclusion.
variable {X : Type u}

/-- An idempotent relaxation as a Mathlib closure operator.

MR16, Section 3.4, Equation (1) (printed p. 8): “R ⊆ R* = (R*)*”. Jost's general definition
(Definition 2.2.6, printed p. 20) supplies reflexivity; idempotence is an
additional hypothesis of this specialization.

In the quotation R* (R star) is the closed specification, here `relaxation R`. The resulting
operator has the same action on specifications as `relaxation`. -/
def toClosureOperator
    -- `relaxation : Relaxation X` supplies monotonicity and extensivity.
    (relaxation : Relaxation X)
    -- `idempotent` says relaxing any specification `source` twice is relaxing it once.
    (idempotent : ∀ source, relaxation (relaxation source) = relaxation source) :
    ClosureOperator (Specification X) where
  toFun := relaxation
  monotone' := relaxation.mono
  le_closure' := relaxation.subset_apply
  idempotent' := idempotent

end ConstructiveCryptography.Relaxation

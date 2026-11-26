module

public import Commons.Definitions.GenericGroup.Dense
public import Mathlib.Algebra.Ring.Prod

/-!
# Affine register operations

`affineOperate` interprets the existing operation symbols on coefficient pairs: addition is
componentwise, and `one` inserts `(0,1)`. Initialized with `(1,0)`, these registers represent
expressions in the original secret: “every value computed by S is a linear combination of
x and 1” [1, Appendix F.1, p. 26].

## References

1. U. Maurer, C. Portmann, and J. Zhu. *Unifying Generic Group Models*.
   Cryptology ePrint Archive, Paper 2020/996, 2020.
-/

@[expose] public section

namespace Commons.GenericGroup

-- `F` carries coefficients and secret values; a pair `(a,b)` represents `a * x + b`.
variable {F : Type} [Semiring F]

/-- Interpret addition componentwise and insertion of one by the constant expression `(0,1)`. -/
def affineOperate : (o : Operation) → (Fin (operationArity o) → F × F) → F × F :=
  letI : One (F × F) := ⟨(0, 1)⟩
  operate

end Commons.GenericGroup

import Verbose

open AbstractCryptography
open scoped AbstractCryptography

universe u v w

variable {I : Type u} {Gamma : I → Type v} {Phi : Type w}
variable [∀ i, Monoid (Gamma i)] [MulAction (∀ i, Gamma i) Phi]

/- This file must fail: the controlled grammar is deliberately opt-in. -/
example (protocol : ∀ i, Gamma i) (real ideal : Phi)
    (actionEquation : protocol • real = ideal) :
    ⟪real⟫ —[protocol]→ ⟪ideal⟫ := by
  The construction follows from actionEquation

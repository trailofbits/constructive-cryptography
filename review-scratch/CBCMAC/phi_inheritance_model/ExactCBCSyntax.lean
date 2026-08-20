import Applications.CBCMAC

/-!
Exact use-site smoke test against the real CBC-MAC declarations.
No repository source is modified.
-/

namespace RandomSystems.CBCMAC

open RandomSystems

noncomputable section

universe u

/-- Canonical bridge from a typed PDS fiber to the universal converter action. -/
local instance typedPDSHSMul {M X : Type u} :
    HSMul (↥converterMonoidAt.{u}) (PDS M X) Phi.{u} where
  hSMul sigma resource := sigma • (resource : Phi.{u})

-- This is the exact requested paper-level shape.
example {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] [AddCommGroup X]
    {M : Type u} [Fintype M] [DecidableEq M]
    (bf : M → List X) (r : ℕ) : Phi.{u} :=
  theta bf r • Vn M X

end

end RandomSystems.CBCMAC

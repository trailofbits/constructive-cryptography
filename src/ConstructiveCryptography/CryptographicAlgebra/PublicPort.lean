module

public import ConstructiveCryptography.Notation.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# A public port to a shared resource

`withPublicPort π σ` routes the private calls of `π` and the public calls at `P` through the
same supplied converter `σ`. Its attachment law exposes the one resource behind that converter.

```text
H ── π ──┬── A ────────── auxiliary
         └── B ──┐
P ───────────────┴── σ ── shared
```
-/

@[expose] public section

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory MonoidalCategory
open scoped SystemAlgebra

variable {C : Type*} [Category* C] [MonoidalCategory C] {H A B P R : C}

/-- Give the public port `P` and the protocol's port `B` access through one router `σ`. -/
def withPublicPort
    -- `π` serves `H` using an auxiliary port `A` and an internal caller port `B`.
    (π : H ⟶ A ⊗ B)
    -- `σ` serves both `B` and `P` from the single inside interface `R`.
    (σ : B ⊗ P ⟶ R) : H ⊗ P ⟶ A ⊗ R :=
  (π ⊗ₘ 𝟙 P) ≫ (α_ A B P).hom ≫ (𝟙 A ⊗ₘ σ)

variable {Φ : C → Type*} [ResourceTheory C Φ] [CryptographicAlgebra C Φ]

/-- Attaching the assembly applies `σ` once to `shared`; `aux` remains on its own wire. -/
lemma withPublicPort_attach (π : H ⟶ A ⊗ B) (σ : B ⊗ P ⟶ R) (aux : Φ A) (shared : Φ R) :
    withPublicPort π σ • (aux ∥ shared) =
      (π ⊗ₘ 𝟙 P) • ((α_ A B P).hom • (aux ∥ (σ • shared))) := by
  change attach _ _ = attach _ (attach _ _)
  rw [withPublicPort, attach_serial, attach_serial, attach_parallel, attach_identity]

/-- With a dummy auxiliary and direct internal access, the assembly exposes exactly `σ • shared`. -/
lemma withPublicPort_attach_dummy (σ : B ⊗ P ⟶ R) (shared : Φ R) :
    withPublicPort (λ_ B).inv σ • (dummy (C := C) ∥ shared) = σ • shared := by
  -- Rebracketing the dummy wire moves its unitor through the router.
  change attach _ _ = attach _ _
  rw [withPublicPort, ← Category.assoc, ← leftUnitor_tensor_inv']
  rw [id_tensorHom, ← leftUnitor_inv_naturality, attach_serial, parallel_dummy_left]

end ConstructiveCryptography.CryptographicAlgebra

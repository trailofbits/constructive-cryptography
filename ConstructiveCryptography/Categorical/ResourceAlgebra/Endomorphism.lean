/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ConstructiveCryptography.Categorical.ResourceAlgebra
import Mathlib.CategoryTheory.Endomorphism

set_option autoImplicit false

/-!
# Attachment within one resource fibre

At one interface, converters preserving that interface are endomorphisms.  The
opposite endomorphism monoid acts on the corresponding resource fibre by
attachment.  This is a derived local view of the interface category and
resource functor, not another attachment structure or a global instance.
-/

namespace ConstructiveCryptography.Categorical.ResourceAlgebra

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C]

/-- The opposite endomorphism monoid acts on one resource fibre by converter
attachment.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter `α`, when applied
as an interface `i` of a resource, induces a function `Φ → Φ : R → αⁱR`.”
The same section states “`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” Taking the opposite of
Mathlib's endomorphism monoid aligns its multiplication with this attachment
order.

Jost's interface-indexed converters generally change the exposed interface,
so this endomorphism action is only the specialization obtained after one
interface has been fixed. -/
@[reducible] noncomputable def endoMulAction
    (Phi : Opposite C ⥤ Type w) (A : C) :
    MulAction (MulOpposite (CategoryTheory.End A)) (Resource Phi A) where
  smul converter resource :=
    attach (Phi := Phi) converter.unop resource
  one_smul resource := by
    -- The neutral endomorphism attaches as the identity converter.
    change attach (Phi := Phi) (𝟙 A) resource = resource
    exact attach_identity resource
  mul_smul outer inner resource := by
    -- Opposite multiplication makes the displayed serial arrow act outermost.
    change attach (Phi := Phi)
        (outer.unop ≫ inner.unop) resource =
      attach (Phi := Phi) outer.unop
        (attach (Phi := Phi) inner.unop resource)
    exact attach_serial outer.unop inner.unop resource

end ConstructiveCryptography.Categorical.ResourceAlgebra

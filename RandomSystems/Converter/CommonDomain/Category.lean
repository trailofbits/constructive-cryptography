/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Category
import RandomSystems.Converter.CommonDomain

set_option autoImplicit false

/-!
# Common-domain random-system category

The objects are fixed query/answer interfaces. The arrows are exactly the DDCs
whose ambient action preserves the embedded normalized specialization of
Lanzenberger's common-domain carrier. The resulting attachment functor uses no
total-completion absorption premise.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when applied
as an interface i of a resource, induces a function Φ → Φ : R → αⁱR.”

Jost separates the axiomatic system algebra from his probabilistic discrete
system presentation and does not require Lanzenberger's common-domain
relation.

Liu--Maurer's conditional-probability resource model does not impose this
common-domain restriction. No ordered parallel structure is selected on the
fixed-interface common-domain category here.
-/

namespace RandomSystems.CommonDomain

noncomputable section

open CategoryTheory

universe u v

/-- A fixed query/answer interface for the common-domain carrier. -/
structure Interface where
  query : Type u
  answer : Type v

namespace Interface

/-- Fixed interfaces and common-domain-preserving DDCs form a category.

Maurer--Renner 2016, Section 3.3 (printed p. 7), states
“`(β ◦ α)ⁱR = βⁱ(αⁱR)`” and says that the identity converter induces the
identity. This declaration packages the proved restricted DDC laws. -/
@[reducible] noncomputable def category :
    LargeCategory Interface.{u, v} where
  Hom outer inner :=
    CommonDomain.DDC outer.query outer.answer inner.query inner.answer
  id boundary := CommonDomain.DDC.forwarding boundary.query boundary.answer
  comp outer inner := CommonDomain.DDC.serial outer inner
  id_comp converter := CommonDomain.DDC.forwarding_serial_eq converter
  comp_id converter := CommonDomain.DDC.serial_forwarding_eq converter
  assoc first second third :=
    CommonDomain.DDC.serial_assoc first second third

attribute [local instance] category

/-- Normalized common-domain random systems form the contravariant attachment
functor of common-domain-preserving DDCs.

Maurer--Renner 2016, Section 3.3 (printed p. 7), says that attachment “induces
a function `Φ → Φ`” and satisfies “`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” -/
noncomputable def randomSystems :
    Opposite Interface.{u, v} ⥤ Type (max u v) where
  obj boundary :=
    ProbabilityRandomSystem boundary.unop.query boundary.unop.answer
  map converter := ProbabilityRandomSystem.apply converter.unop
  map_id boundary := by
    -- Restricted forwarding attachment is the identity.
    funext system
    exact ProbabilityRandomSystem.apply_forwarding_eq system
  map_comp outer inner := by
    -- Restricted serial attachment is nested attachment.
    funext system
    exact ProbabilityRandomSystem.apply_serial_eq
      inner.unop outer.unop system

end Interface

end

end RandomSystems.CommonDomain

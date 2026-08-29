/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Category
import RandomSystems.Converter.RandomSystem.Parallel
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Opposite
import Mathlib.CategoryTheory.Monoidal.Types.Basic

set_option autoImplicit false

/-!
# Contravariant random-system functor

Normalized random systems form a contravariant functor under DDC attachment.
Independent ordered parallel supplies a lax monoidal structure. This packages
the proved attachment and parallel equations; it asserts neither symmetry nor
an inverse to parallel composition.
-/

namespace RandomSystems.Ambient

open CategoryTheory

universe u v

namespace Interface

/-- Normalized random systems and DDC attachment form a contravariant functor.

Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when applied
as an interface i of a resource, induces a function Φ → Φ : R → αⁱR.” The
same section states “`(β ◦ α)ⁱR = βⁱ(αⁱR)`.” -/
noncomputable def randomSystems :
    CategoryTheory.Functor
      (Opposite Interface.{u, v}) (Type (max u v)) where
  obj boundary := RandomSystem boundary.unop
  map converter := RandomSystem.apply converter.unop
  map_id boundary := by
    -- Forwarding attachment is the identity on quotient random systems.
    funext system
    exact RandomSystem.apply_forwarding_eq system
  map_comp outer inner := by
    -- Serial DDC attachment is nested attachment on the quotient.
    funext system
    exact RandomSystem.apply_serial_eq inner.unop outer.unop system

/-- Independent ordered parallel gives the random-system functor a lax
monoidal structure.

Jost, Section 2.2.2 (printed p. 17), says: “A finite set of resources with
disjoint interface sets can be viewed as a single one.” Proposition 2.2.3
(printed p. 18) proves attachment locality. The declaration packages the
proved routed equations; Jost does not state a lax-monoidal functor. Neither
symmetry nor invertibility of the lax parallel map is asserted. -/
@[reducible] noncomputable def randomSystemsLaxMonoidal :
    randomSystems.LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (ε := fun _ => RandomSystem.empty)
    (μ := fun _ _ systems => RandomSystem.parallel systems.1 systems.2)
    (μ_natural := by
      -- Attachment acts independently on the two ordered components.
      intro leftOuter leftInner rightOuter rightInner leftConverter
        rightConverter
      funext systems
      exact (RandomSystem.apply_parallel_eq leftConverter.unop
        rightConverter.unop systems.1 systems.2).symm)
    (associativity := by
      -- Canonical reassociation identifies the two bracketings.
      intro first second third
      funext systems
      exact RandomSystem.apply_parallel_assoc_eq
        systems.1.1 systems.1.2 systems.2)
    (left_unitality := by
      -- The empty resource is the left unit after canonical relabeling.
      intro boundary
      funext system
      rcases system with ⟨unitValue, system⟩
      rcases unitValue with ⟨⟩
      exact (RandomSystem.apply_parallel_empty_left_eq system).symm)
    (right_unitality := by
      -- The empty resource is the right unit after canonical relabeling.
      intro boundary
      funext system
      rcases system with ⟨system, unitValue⟩
      rcases unitValue with ⟨⟩
      exact (RandomSystem.apply_parallel_empty_right_eq system).symm)

end Interface

end RandomSystems.Ambient

import ConstructiveCryptography.Specification.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-!
# Converter attachment

Converters form a `Monoid C` and attach to resources by `MulAction C X`.
The product `β * α` attaches `α` first and `β` second. Attachment to
specifications is Mathlib's pointwise set action, in the `Pointwise` scope.
Construction remains `Specification.Constructs (α • ·)`.

MR16, Section 3.3 (printed p. 7): “(β ◦ α)ⁱR = βⁱ(αⁱR)”.
The identity and serial attachment laws are `one_smul` and `mul_smul`.
Commuting selected actions use Mathlib's `SMulCommClass` and `smul_comm`.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable {C : Type u} {X : Type v} [Monoid C] [MulAction C X]

/-- Serial attachment composes exact constructions.

MR16, Lemma 1 (printed p. 11): “This construction notion is composable.”
Jost, Theorem 2.2.5.1 (printed p. 19), derives the rule from image inclusion.
The action law identifies the composite map with the converter product. -/
theorem Constructs.smul_comp {α β : C} {source middle target : Specification X}
    (inner : Constructs (α • ·) source middle)
    (outer : Constructs (β • ·) middle target) :
    Constructs ((β * α) • ·) source target := by
  intro resource admitted
  -- Attach the inner converter, then the outer converter.
  simpa only [mul_smul] using outer (inner admitted)

end ConstructiveCryptography.Specification

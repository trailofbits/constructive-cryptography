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

```text
R ── attach α ──▶ α • R ── attach β ──▶ β • (α • R) = (β * α) • R      (mul_smul)
```

This is a single-sorted action. The interface-typed category of converters, where an arrow
`A ⟶ B` has outside interface `A` and inside `B` and attaches as a map from resources at `B`
to resources at `A`, is a separate layer and is not assumed here.
-/

namespace ConstructiveCryptography.Specification

universe u v

variable
    -- `C` is the type of converters and `X` the type of resources.
    {C : Type u} {X : Type v}
    -- `Monoid C`: `1 : C` is the identity converter and `β * α` the serial composite `β ∘ α`,
    -- attaching `α` first; no inverses, commutativity or efficiency are assumed.
    [Monoid C]
    -- `MulAction C X`: `α • R` attaches `α : C` to `R : X`, the source's αⁱR at the one
    -- interface `i` fixed by this action; different interfaces are different actions.
    [MulAction C X]

/-- Serial attachment composes exact constructions: `β * α`, which attaches `α` first,
constructs `target` from `source`.

MR16, Lemma 1 (printed p. 11): “This construction notion is composable.”
Jost, Theorem 2.2.5.1 (printed p. 19), derives the rule from image inclusion.

```text
source ── α • · ──▶ middle ── β • · ──▶ target
   └────────── (β * α) • · ──────────────▶
``` -/
theorem Constructs.smul_comp
    -- α (alpha) and β (beta) in `C` are attached first and second.
    {α β : C}
    -- `source`, `middle` and `target` are specifications on `X`, the three stages.
    {source middle target : Specification X}
    -- `inner`: attaching `α` to any resource meeting `source` gives one meeting `middle`.
    (inner : Constructs (α • ·) source middle)
    -- `outer`: attaching `β` to any resource meeting `middle` gives one meeting `target`.
    (outer : Constructs (β • ·) middle target) :
    Constructs ((β * α) • ·) source target := by
  intro resource admitted
  -- Attach the inner converter, then the outer converter.
  simpa only [mul_smul] using outer (inner admitted)

end ConstructiveCryptography.Specification

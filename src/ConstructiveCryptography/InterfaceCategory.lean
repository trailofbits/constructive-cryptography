import RandomSystems.Typed.Interface
import Mathlib.CategoryTheory.Types.Basic

/-!
# The category of interfaces

Interfaces are an instance of `Category`: its field `Hom` is `TypedConverter`, `id` is
`TypedConverter.id` and `comp` is `TypedConverter.comp`, the identity and the serial composition
of PDC behaviors; the axioms `id_comp`, `comp_id` and `assoc` are discharged by
`PDCBehavior.id_comp`, `PDCBehavior.comp_id` and `PDCBehavior.comp_assoc`. An arrow acts on
typed systems by `TypedConverter.attach`; attachment is a contravariant functor to types.

## Main definitions

* `Interface.category`: the category of interfaces and typed converters

## Main results

* `Interface.identity_attach`: attaching the identity arrow leaves a typed system unchanged,
  `TypedConverter.identity_attach`
* `Interface.comp_smul`: attaching a serial composition attaches the inner arrow first,
  `TypedConverter.comp_smul`
-/

namespace SystemAlgebra.Interface

open CategoryTheory

/-- Interfaces and typed converters form a category under serial composition. -/
noncomputable instance category : Category Interface where
  Hom := TypedConverter
  id := TypedConverter.id
  comp α β := TypedConverter.comp α β
  id_comp {A _} α := PDCBehavior.id_comp α A.nonempty_prefix
  comp_id {_ B} α := PDCBehavior.comp_id α B.nonempty_prefix
  assoc α β γ := PDCBehavior.comp_assoc α β γ

/-- The action of an arrow on a typed system is attachment. As a default instance, an arrow
whose domains are still to be inferred takes them from the typed system it acts on. -/
@[default_instance high]
noncomputable instance {A B : Interface} : HSMul (A ⟶ B) (TypedSystem B) (TypedSystem A) :=
  ⟨TypedConverter.attach⟩

/-- **Attaching the identity** leaves a typed system unchanged. -/
lemma identity_attach {A : Interface} (R : TypedSystem A) : (𝟙 A • R : TypedSystem A) = R :=
  TypedConverter.identity_attach R

/-- **Serial attachment** (MR16 §3.3, printed p. 7: “(β ∘ α)ⁱR = βⁱ(αⁱR)”): attaching a
serial composition attaches the inner converter first. -/
theorem comp_smul {A B C : Interface} (α : A ⟶ B) (β : B ⟶ C) (R : TypedSystem C) :
    (α ≫ β) • R = α • (β • R) :=
  TypedConverter.comp_smul α β R

lemma comp_eq {A B C : Interface} (α : A ⟶ B) (β : B ⟶ C) :
    α ≫ β = PDCBehavior.comp α β := rfl

end SystemAlgebra.Interface

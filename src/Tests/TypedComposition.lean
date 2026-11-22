module

public import ConstructiveCryptography.Notation
public import Commons.Definitions.Ideal

/-!
# Serial composition from direct converter types

The frontend accepts direct `TypedConverter` signatures, nested compositions and identity
operands with initially unspecified interfaces. Definitional checks identify the result
with the existing serial operation.

The generic-category checks keep its selected composition and identities. `Selected` chooses
reversed composition on lifted interfaces whose morphisms reduce to typed converters; the
frontend must retain that operation, including with a direct converter result type. The
rejected-middle check preserves the intermediate interface constraint. The `Inference` checks
cover missing result types, generic wrappers and categories or endpoint capabilities supplied
by later arguments; these constraints must remain available to ordinary enclosing elaboration.
-/

@[expose] public section

namespace SystemAlgebra.Tests.TypedComposition

open CategoryTheory
open scoped SystemAlgebra

noncomputable section

-- `A`, `B`, `C`, `D` are the consecutive interfaces in the typed composition tests.
variable {A B C D : Interface}

/-- Direct typed signatures infer serial composition without a categorical result annotation. -/
def direct (α : TypedConverter A B) (β : TypedConverter B C) : TypedConverter A C := α ≫ β

/-- Nested compositions share their intermediate interfaces. -/
def nested (α : TypedConverter A B) (β : TypedConverter B C) (γ : TypedConverter C D) :
    TypedConverter A D := α ≫ β ≫ γ

/-- Expected endpoints resolve initially unspecified identity operands. -/
def identities : TypedConverter A A := TypedConverter.id _ ≫ TypedConverter.id _

/-- Both sides may need their interfaces from the surrounding typed composition. -/
def surrounded (α : TypedConverter A B) : TypedConverter A B :=
  TypedConverter.id _ ≫ α ≫ TypedConverter.id _

lemma identities_eq : identities (A := A) =
    TypedConverter.comp (TypedConverter.id A) (TypedConverter.id A) := rfl

lemma surrounded_eq (α : TypedConverter A B) :
    surrounded α = TypedConverter.comp (TypedConverter.id A)
      (TypedConverter.comp α (TypedConverter.id B)) := rfl

lemma direct_eq (α : TypedConverter A B) (β : TypedConverter B C) :
    direct α β = TypedConverter.comp α β := rfl

lemma nested_eq (α : TypedConverter A B) (β : TypedConverter B C) (γ : TypedConverter C D) :
    nested α β γ = TypedConverter.comp α (TypedConverter.comp β γ) := rfl

/-- Ordinary generic composition retains its selected operation. -/
def generic {E : Type*} [Category E] {a b c : E} (f : a ⟶ b) (g : b ⟶ c) : a ⟶ c := f ≫ g

lemma generic_eq {E : Type*} [Category E] {a b c : E} (f : a ⟶ b) (g : b ⟶ c) :
    generic f g = CategoryStruct.comp f g := rfl

/-- Generic identities and nested composition remain in the selected category. -/
def genericNested {E : Type*} [Category E] {a b : E} (f : a ⟶ b) : a ⟶ b :=
  𝟙 a ≫ f ≫ 𝟙 b

lemma genericNested_eq {E : Type*} [Category E] {a b : E} (f : a ⟶ b) :
    genericNested f = CategoryStruct.comp (𝟙 a) (CategoryStruct.comp f (𝟙 b)) := rfl

namespace Selected

/-- On lifted interfaces, an arrow from `A` to `B` is a converter from `B.down` to `A.down`.
Composition reverses the underlying order, detecting hints that reinterpret selected arrows
as direct converters. -/
scoped instance reversedCategory : Category (ULift.{0} Interface) where
  Hom A B := TypedConverter B.down A.down
  id A := TypedConverter.id A.down
  comp α β := TypedConverter.comp β α
  id_comp {A _} α := PDCBehavior.comp_id α A.down.nonempty_prefix
  comp_id {_ B} α := PDCBehavior.id_comp α B.down.nonempty_prefix
  assoc α β γ := (PDCBehavior.comp_assoc γ β α).symm

end Selected

section
open scoped Selected

/-- The scoped category reverses composition even for endomorphisms of one interface. -/
def selected (A : Interface)
    (α β : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A := α ≫ β

lemma selected_eq (A : Interface)
    (α β : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    selected A α β = TypedConverter.comp β α := rfl

/-- Nested notation retains both reversals of the selected category. -/
def selectedNested (A : Interface)
    (α β γ : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A := α ≫ β ≫ γ

lemma selectedNested_eq (A : Interface)
    (α β γ : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    selectedNested A α β γ = TypedConverter.comp (TypedConverter.comp γ β) α := rfl

/-- A direct converter result type does not override the category supplied by the operands. -/
def selectedDirectResult (A : Interface)
    (α β : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    TypedConverter A A := α ≫ β

lemma selectedDirectResult_eq (A : Interface)
    (α β : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) :
    selectedDirectResult A α β = TypedConverter.comp β α := rfl

/-- The expected type can select reversed composition even with direct converter operands. -/
def selectedExpected (A B C : Interface)
    (α : TypedConverter B A) (β : TypedConverter C B) :
    (ULift.up A : ULift.{0} Interface) ⟶ ULift.up C := α ≫ β

lemma selectedExpected_eq (A B C : Interface)
    (α : TypedConverter B A) (β : TypedConverter C B) :
    selectedExpected A B C α β = TypedConverter.comp β α := rfl

/-- These selected arrows have incompatible middle objects; their underlying converter types
would compose in the opposite order, which must not make this notation succeed. -/
lemma selected_incompatible_middle {A B C : Interface}
    (_α : (ULift.up B : ULift.{0} Interface) ⟶ ULift.up A)
    (_β : (ULift.up C : ULift.{0} Interface) ⟶ ULift.up B) : True := by
  fail_if_success
    have rejected : TypedConverter A C := _α ≫ _β
  fail_if_success
    have rejected := _α ≫ _β
  trivial

/-- A type abbreviation retains the selected lifted category. -/
abbrev selectedArrow (A B : Interface) :=
  (ULift.up A : ULift.{0} Interface) ⟶ ULift.up B

/-- Aliased morphism types retain the same incompatible-middle constraint. -/
lemma aliased_incompatible_middle {A B C : Interface}
    (_α : selectedArrow B A) (_β : selectedArrow C B) : True := by
  fail_if_success
    have rejected : TypedConverter A C := _α ≫ _β
  trivial

/-- An aliased expected Hom type also retains its selected category after a mismatch. -/
lemma selected_expected_incompatible {A B C : Interface}
    (_α : TypedConverter A B) (_β : TypedConverter B C) : True := by
  fail_if_success
    have rejected : selectedArrow A C := _α ≫ _β
  trivial

end

/-- A bad innermost operand is rejected through a twelve-link chain within the default
elaboration limits. -/
lemma nested_incompatible_operand (_α : TypedConverter A A) : True := by
  fail_if_success
    have rejected : TypedConverter A A :=
      _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ _α ≫ (0 : ℕ)
  trivial

#print axioms nested_incompatible_operand
#print axioms selected_expected_incompatible
#print axioms selected_incompatible_middle
#print axioms aliased_incompatible_middle
#print axioms selectedExpected_eq
#print axioms selected_eq
#print axioms selectedNested_eq
#print axioms selectedDirectResult_eq
#print axioms identities_eq
#print axioms surrounded_eq
#print axioms genericNested_eq
#print axioms direct_eq
#print axioms nested_eq
#print axioms generic_eq

/-- The typed hint does not identify the distinct middle interfaces `B` and `C`. -/
lemma incompatible_middle (_α : TypedConverter A B) (_β : TypedConverter C D) : True := by
  fail_if_success have rejected : TypedConverter A D := _α ≫ _β
  trivial

#print axioms incompatible_middle

namespace Inference

/-- Keep a value without prescribing its type. -/
def keep {T : Sort*} (x : T) : T := x

/-- Direct converter operands determine a result whose type is initially unspecified. -/
def noExpected (α : TypedConverter A B) (β : TypedConverter B C) := α ≫ β

/-- An identity wrapper leaves the composition's expected type initially unspecified. -/
def underId (α : TypedConverter A B) (β : TypedConverter B C) := id (α ≫ β)

/-- A user-defined wrapper supplies no additional category information. -/
def underKeep (α : TypedConverter A B) (β : TypedConverter B C) := keep (α ≫ β)

/-- A wrapped nested composition retains its intermediate interfaces. -/
def nestedKeep (α : TypedConverter A B) (β : TypedConverter B C)
    (γ : TypedConverter C D) := keep (α ≫ β ≫ γ)

lemma noExpected_eq (α : TypedConverter A B) (β : TypedConverter B C) :
    noExpected α β = TypedConverter.comp α β := rfl

lemma underId_eq (α : TypedConverter A B) (β : TypedConverter B C) :
    underId α β = TypedConverter.comp α β := rfl

lemma underKeep_eq (α : TypedConverter A B) (β : TypedConverter B C) :
    underKeep α β = TypedConverter.comp α β := rfl

lemma nestedKeep_eq (α : TypedConverter A B) (β : TypedConverter B C)
    (γ : TypedConverter C D) :
    nestedKeep α β γ = TypedConverter.comp α (TypedConverter.comp β γ) := rfl

/-- Retain the first value; the second may determine their common type. -/
def firstValue {T : Sort*} (x _y : T) : T := x

/-- Identity on the one-query interface with replies in `X`; writing `_` for `X` leaves
its instances pending. -/
def witnessedIdentity (X : Type) [Fintype X] [Nonempty X] :
    TypedConverter (Interface.queryBudget Unit (fun _ => Unit) (fun _ => X) 1)
      (Interface.queryBudget Unit (fun _ => Unit) (fun _ => X) 1) := TypedConverter.id _

/-- The attached system resolves the reply alphabet after the converter argument. -/
lemma deferred_typed (X : Type) [Fintype X] [Nonempty X]
    (R : TypedSystem (Interface.queryBudget Unit (fun _ => Unit) (fun _ => X) 1)) :
    TypedConverter.attach (witnessedIdentity _ ≫ witnessedIdentity _ ≫ witnessedIdentity _) R =
      TypedConverter.comp (witnessedIdentity X)
        (TypedConverter.comp (witnessedIdentity X) (witnessedIdentity X)) • R := rfl

section
open scoped Selected

/-- A later arrow selects reversed composition even when the first expected type is unknown. -/
lemma later_selected (A : Interface) (α β : TypedConverter A A) :
    firstValue (α ≫ β) (𝟙 (ULift.up A : ULift.{0} Interface)) =
      TypedConverter.comp β α := rfl

/-- Retain a selected reversed arrow; the later system fixes its endpoint interface. -/
def laterSystem {A : Interface}
    (α : (ULift.up A : ULift.{0} Interface) ⟶ ULift.up A) (_R : TypedSystem A) :
    TypedConverter A A := α

/-- A selected category can still have endpoint capabilities resolved by later arguments. -/
lemma selected_pending (X : Type) [Fintype X] [Nonempty X]
    (R : TypedSystem (Interface.queryBudget Unit (fun _ => Unit) (fun _ => X) 1)) :
    laterSystem (witnessedIdentity _ ≫ witnessedIdentity _) R =
      TypedConverter.comp (witnessedIdentity X) (witnessedIdentity X) := rfl

/-- One-query evaluation interface with replies in `X`; `Fintype X` may be resolved later. -/
abbrev evaluationAlphabet (X : Type) [Fintype X] :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => X) 1

/-- Endomorphisms for each witnessed reply alphabet, with no equality assumed between them. -/
abbrev ConverterFamily := ∀ (X : Type), [Fintype X] → [Nonempty X] →
  TypedConverter (evaluationAlphabet X) (evaluationAlphabet X)

/-- Read `f X` in the reversed category before the surrounding term determines `X`. -/
def selectedFamily (f : ConverterFamily) (X : Type) [Fintype X] [Nonempty X] :
    (ULift.up (evaluationAlphabet X) : ULift.{0} Interface) ⟶
      ULift.up (evaluationAlphabet X) := f X

/-- Retain a direct converter; its later system determines the interface. -/
def laterConverter {A : Interface} (α : TypedConverter A A) (_R : TypedSystem A) :
    TypedConverter A A := α

/-- Pending endpoint capabilities do not erase the category selected by each operand. -/
lemma operand_selected_pending (X : Type) [Fintype X] [Nonempty X]
    (f g : ConverterFamily) (R : TypedSystem (evaluationAlphabet X)) :
    laterConverter (selectedFamily f _ ≫ selectedFamily g _) R =
      TypedConverter.comp (g X) (f X) := rfl

/-- Ordinary converter composition at `A` cannot replace the later selected reversed operation. -/
lemma later_selected_incompatible (_α : TypedConverter A B) (_β : TypedConverter B A) : True := by
  fail_if_success
    have rejected := firstValue (_α ≫ _β) (𝟙 (ULift.up A : ULift.{0} Interface))
  trivial

end

#print axioms noExpected_eq
#print axioms underId_eq
#print axioms underKeep_eq
#print axioms nestedKeep_eq
#print axioms deferred_typed
#print axioms later_selected
#print axioms selected_pending
#print axioms operand_selected_pending
#print axioms later_selected_incompatible

end Inference

end
end SystemAlgebra.Tests.TypedComposition

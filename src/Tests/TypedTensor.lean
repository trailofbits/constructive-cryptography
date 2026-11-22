module

public import Tests.TypedComposition

/-!
# Tensor of direct converters

`α ⊗ₘ β` shares the dispatch of serial `≫`, `elabTypedCCArrows`.

* Direct operands give the tensor of `Interface`, syntactically its `tensorHom` (`tensor_term`).
  The same holds for aliases, nested tensors, a missing result type and mixed nesting with `≫`;
  `⊗ₘ` binds more loosely than `≫` (`precedence`).
* Selected operations are kept:
  * a generic monoidal structure;
  * a selected structure `S` on interfaces (`selectedStructure`);
  * the reversed lifted category of `Tests.TypedComposition` with the swapped tensor of
    `Swapped`, whether operands, the expected type or a later argument select it.
  Mixed nesting in that category keeps both its composition and its tensor.
* Endpoint capabilities that later arguments determine stay pending (`deferred_typed`).
* Incompatible endpoints are rejected, and a canonical reading never replaces a selected one.
-/

@[expose] public section

namespace SystemAlgebra.Tests.TypedTensor

open CategoryTheory MonoidalCategory
open scoped SystemAlgebra

noncomputable section

-- `A`, …, `E` are interfaces.
variable {A B C D E : Interface}

/-! ## Direct converters -/

/-- Direct operands and a direct result type. -/
def tensor (α : TypedConverter A B) (β : TypedConverter C D) :
    TypedConverter (A ⊗ C) (B ⊗ D) := α ⊗ₘ β

lemma tensor_eq (α : TypedConverter A B) (β : TypedConverter C D) :
    tensor α β = TypedConverter.parallel α β := rfl

/-- The elaborated term is the `tensorHom` of `Interface`'s monoidal structure. -/
lemma tensor_term (α : TypedConverter A B) (β : TypedConverter C D) : True := by
  let t : TypedConverter (A ⊗ C) (B ⊗ D) := α ⊗ₘ β
  guard_hyp t :=ₛ @MonoidalCategoryStruct.tensorHom Interface Interface.category
    Interface.monoidalStruct A B C D α β
  trivial

/-- The category-arrow spelling. -/
def arrows (α : A ⟶ B) (β : C ⟶ D) : A ⊗ C ⟶ B ⊗ D := α ⊗ₘ β

lemma arrows_eq (α : A ⟶ B) (β : C ⟶ D) : arrows α β = TypedConverter.parallel α β := rfl

/-- The operands determine a result whose type is not given. -/
def noExpected (α : TypedConverter A B) (β : TypedConverter C D) := α ⊗ₘ β

lemma noExpected_eq (α : TypedConverter A B) (β : TypedConverter C D) :
    noExpected α β = TypedConverter.parallel α β := rfl

/-- A right-nested tensor with an identity operand. -/
def nested (α : TypedConverter A B) (β : TypedConverter C D) :
    TypedConverter (A ⊗ C ⊗ E) (B ⊗ D ⊗ E) := α ⊗ₘ β ⊗ₘ 𝟙 E

lemma nested_eq (α : TypedConverter A B) (β : TypedConverter C D) :
    nested (E := E) α β =
      TypedConverter.parallel α (TypedConverter.parallel β (TypedConverter.id E)) := rfl

/-- A direct converter alias. -/
abbrev Link (A B : Interface) := TypedConverter A B

/-- Aliased operands and result. -/
def aliased (α : Link A B) (β : Link C D) : Link (A ⊗ C) (B ⊗ D) := α ⊗ₘ β

lemma aliased_eq (α : Link A B) (β : Link C D) :
    aliased α β = TypedConverter.parallel α β := rfl

/-- The locality law keeps its statement: `(α ⊗ₘ β) • (R ∥ S) = α • R ∥ β • S`. -/
lemma tensor_smul (α : TypedConverter A B) (β : TypedConverter C D)
    (R : TypedSystem B) (S : TypedSystem D) :
    (α ⊗ₘ β) • (R ∥ S) = α • R ∥ β • S :=
  Interface.tensor_smul α β R S

/-! ## Mixed serial and tensor nesting -/

/-- A tensor followed by a direct converter. -/
def serialOfTensor (α : TypedConverter A B) (β : TypedConverter C D)
    (γ : TypedConverter (B ⊗ D) E) : TypedConverter (A ⊗ C) E := (α ⊗ₘ β) ≫ γ

lemma serialOfTensor_eq (α : TypedConverter A B) (β : TypedConverter C D)
    (γ : TypedConverter (B ⊗ D) E) :
    serialOfTensor α β γ = TypedConverter.comp (TypedConverter.parallel α β) γ := rfl

/-- A serial composition beside a direct converter. -/
def tensorOfSerial (α : TypedConverter A B) (β : TypedConverter B C)
    (γ : TypedConverter D E) : TypedConverter (A ⊗ D) (C ⊗ E) := (α ≫ β) ⊗ₘ γ

lemma tensorOfSerial_eq (α : TypedConverter A B) (β : TypedConverter B C)
    (γ : TypedConverter D E) :
    tensorOfSerial α β γ = TypedConverter.parallel (TypedConverter.comp α β) γ := rfl

/-- `⊗ₘ` binds more loosely than `≫`: `α ⊗ₘ β ≫ γ = α ⊗ₘ (β ≫ γ)`. -/
def precedence (α : TypedConverter A B) (β : TypedConverter C D) (γ : TypedConverter D E) :
    TypedConverter (A ⊗ C) (B ⊗ E) := α ⊗ₘ β ≫ γ

lemma precedence_eq (α : TypedConverter A B) (β : TypedConverter C D)
    (γ : TypedConverter D E) :
    precedence α β γ = TypedConverter.parallel α (TypedConverter.comp β γ) := rfl

/-- A tensor with an identity, then a direct converter. -/
def tensorIdentity (α : TypedConverter A B) (γ : TypedConverter (B ⊗ C) D) :
    TypedConverter (A ⊗ C) D := (α ⊗ₘ 𝟙 C) ≫ γ

lemma tensorIdentity_eq (α : TypedConverter A B) (γ : TypedConverter (B ⊗ C) D) :
    tensorIdentity α γ =
      TypedConverter.comp (TypedConverter.parallel α (TypedConverter.id C)) γ := rfl

/-- Incompatible endpoints are rejected, also under serial composition. -/
lemma incompatible (_α : TypedConverter A B) (_β : TypedConverter C D)
    (_γ : TypedConverter (D ⊗ B) E) : True := by
  fail_if_success
    have rejected : TypedConverter (C ⊗ A) (D ⊗ B) := _α ⊗ₘ _β
  fail_if_success
    have rejected : TypedConverter (A ⊗ C) (B ⊗ D) := _β ⊗ₘ _α
  fail_if_success
    have rejected : TypedConverter (A ⊗ C) E := (_α ⊗ₘ _β) ≫ _γ
  trivial

/-- The attached system resolves the reply alphabets of both identities after the tensor. -/
lemma deferred_typed (X : Type) [Fintype X] [Nonempty X]
    (R : TypedSystem (TypedComposition.Inference.evaluationAlphabet X ⊗
      TypedComposition.Inference.evaluationAlphabet X)) :
    TypedConverter.attach (TypedComposition.Inference.witnessedIdentity _ ⊗ₘ
        TypedComposition.Inference.witnessedIdentity _) R =
      TypedConverter.parallel (TypedComposition.Inference.witnessedIdentity X)
        (TypedComposition.Inference.witnessedIdentity X) • R := rfl

/-! ## Selected categories and monoidal structures -/

/-- A generic monoidal structure keeps its tensor, also under composition. -/
def generic {M : Type*} [Category M] [MonoidalCategoryStruct M] {a b c d e : M}
    (f : a ⟶ b) (g : c ⟶ d) (h : b ⊗ d ⟶ e) : a ⊗ c ⟶ e := (f ⊗ₘ g) ≫ h

lemma generic_eq {M : Type*} [Category M] [MonoidalCategoryStruct M] {a b c d e : M}
    (f : a ⟶ b) (g : c ⟶ d) (h : b ⊗ d ⟶ e) :
    generic f g h = CategoryStruct.comp (MonoidalCategoryStruct.tensorHom f g) h := rfl

/-- A selected monoidal structure `S` on interfaces is kept: the term is `S`'s tensor, and the
canonical result type `A.tensor C` is rejected. -/
lemma selectedStructure [S : MonoidalCategoryStruct Interface] (α : TypedConverter A B)
    (β : TypedConverter C D) : True := by
  let t : TypedConverter (A ⊗ C) (B ⊗ D) := α ⊗ₘ β
  guard_hyp t :=ₛ @MonoidalCategoryStruct.tensorHom Interface Interface.category S A B C D α β
  fail_if_success
    have rejected : TypedConverter (A.tensor C) (B.tensor D) := α ⊗ₘ β
  trivial

namespace Swapped

open scoped SystemAlgebra.Tests.TypedComposition.Selected

/-- An isomorphism `e : X ≅ Y` of interfaces, read in the reversed lifted category as an
isomorphism from `up Y` to `up X`. -/
def reversedIso {X Y : Interface} (e : X ≅ Y) :
    (ULift.up Y : ULift.{0} Interface) ≅ ULift.up X where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.inv_hom_id
  inv_hom_id := e.hom_inv_id

/-- A deliberately non-canonical tensor on the reversed lifted category: objects are tensored
in swapped order, `up X ⊗ up Y = up (Y ⊗ X)`, and so are arrows. -/
scoped instance swappedTensor : MonoidalCategoryStruct (ULift.{0} Interface) where
  tensorObj X Y := ULift.up (Y.down ⊗ X.down)
  whiskerLeft X _ _ β := TypedConverter.parallel β (TypedConverter.id X.down)
  whiskerRight α Z := TypedConverter.parallel (TypedConverter.id Z.down) α
  tensorHom α β := TypedConverter.parallel β α
  tensorUnit := ULift.up Interface.unit
  associator X Y Z := reversedIso (Interface.associator Z.down Y.down X.down)
  leftUnitor X := reversedIso (Interface.rightUnitor X.down).symm
  rightUnitor X := reversedIso (Interface.leftUnitor X.down).symm

/-- Arrows `up A ⟶ up B` of the reversed category, converters from `B` to `A`. -/
abbrev SelectedArrow (A B : Interface) := (ULift.up A : ULift.{0} Interface) ⟶ ULift.up B

/-- Selected arrows keep the swapped tensor. -/
def selected (α : SelectedArrow A B) (β : SelectedArrow C D) :
    (ULift.up A ⊗ ULift.up C : ULift.{0} Interface) ⟶ ULift.up B ⊗ ULift.up D := α ⊗ₘ β

lemma selected_eq (α : SelectedArrow A B) (β : SelectedArrow C D) :
    selected α β = TypedConverter.parallel β α := rfl

/-- A direct result type does not override the category of the operands. -/
def selectedDirectResult (α : SelectedArrow A B) (β : SelectedArrow C D) :
    TypedConverter (D ⊗ B) (C ⊗ A) := α ⊗ₘ β

lemma selectedDirectResult_eq (α : SelectedArrow A B) (β : SelectedArrow C D) :
    selectedDirectResult α β = TypedConverter.parallel β α := rfl

/-- The expected type selects the swapped tensor for direct operands. -/
def selectedExpected (α : TypedConverter B A) (β : TypedConverter D C) :
    (ULift.up A ⊗ ULift.up C : ULift.{0} Interface) ⟶ ULift.up B ⊗ ULift.up D := α ⊗ₘ β

lemma selectedExpected_eq (α : TypedConverter B A) (β : TypedConverter D C) :
    selectedExpected α β = TypedConverter.parallel β α := rfl

/-- One selected operand reads the other, direct one in the selected category. -/
def selectedMixed (α : SelectedArrow A B) (β : TypedConverter D C) :
    (ULift.up A ⊗ ULift.up C : ULift.{0} Interface) ⟶ ULift.up B ⊗ ULift.up D := α ⊗ₘ β

lemma selectedMixed_eq (α : SelectedArrow A B) (β : TypedConverter D C) :
    selectedMixed α β = TypedConverter.parallel β α := rfl

/-- Mixed nesting keeps both the reversed composition and the swapped tensor. -/
def selectedSerial (α : SelectedArrow A B) (β : SelectedArrow C D)
    (γ : (ULift.up B ⊗ ULift.up D : ULift.{0} Interface) ⟶ ULift.up E) :
    (ULift.up A ⊗ ULift.up C : ULift.{0} Interface) ⟶ ULift.up E := (α ⊗ₘ β) ≫ γ

lemma selectedSerial_eq (α : SelectedArrow A B) (β : SelectedArrow C D)
    (γ : (ULift.up B ⊗ ULift.up D : ULift.{0} Interface) ⟶ ULift.up E) :
    selectedSerial α β γ = TypedConverter.comp γ (TypedConverter.parallel β α) := rfl

/-- A later arrow selects the swapped tensor while the first expected type is still unknown. -/
lemma later_selected (α : TypedConverter A A) (β : TypedConverter C C) :
    TypedComposition.Inference.firstValue (α ⊗ₘ β)
        (𝟙 (ULift.up A ⊗ ULift.up C : ULift.{0} Interface)) =
      TypedConverter.parallel β α := rfl

/-- Selected operands keep their reading; the canonical `parallel α β`, of exactly the type
below, does not replace it. -/
lemma selected_canonical_rejected (_α : SelectedArrow A B) (_β : SelectedArrow C D) : True := by
  fail_if_success
    have rejected : TypedConverter (B ⊗ D) (A ⊗ C) := _α ⊗ₘ _β
  trivial

/-- With mixed operands, the canonical `parallel α β`, of exactly the type below, does not
replace the selected reading. -/
lemma mixed_canonical_rejected (_α : SelectedArrow A B) (_β : TypedConverter C D) : True := by
  fail_if_success
    have rejected : TypedConverter (B ⊗ C) (A ⊗ D) := _α ⊗ₘ _β
  trivial

/-- A selected expected type forbids the canonical reading, although `parallel α β` has the
underlying type `TypedConverter (A ⊗ C) (B ⊗ D)` of the expected arrow. -/
lemma expected_canonical_rejected (_α : TypedConverter A B) (_β : TypedConverter C D) :
    True := by
  fail_if_success
    have rejected : (ULift.up D ⊗ ULift.up B : ULift.{0} Interface) ⟶
      ULift.up C ⊗ ULift.up A := _α ⊗ₘ _β
  trivial

end Swapped

#print axioms tensor_eq
#print axioms tensor_term
#print axioms arrows_eq
#print axioms noExpected_eq
#print axioms nested_eq
#print axioms aliased_eq
#print axioms tensor_smul
#print axioms serialOfTensor_eq
#print axioms tensorOfSerial_eq
#print axioms precedence_eq
#print axioms tensorIdentity_eq
#print axioms incompatible
#print axioms deferred_typed
#print axioms generic_eq
#print axioms selectedStructure
#print axioms Swapped.selected_eq
#print axioms Swapped.selectedDirectResult_eq
#print axioms Swapped.selectedExpected_eq
#print axioms Swapped.selectedMixed_eq
#print axioms Swapped.selectedSerial_eq
#print axioms Swapped.later_selected
#print axioms Swapped.selected_canonical_rejected
#print axioms Swapped.mixed_canonical_rejected
#print axioms Swapped.expected_canonical_rejected

end

end SystemAlgebra.Tests.TypedTensor

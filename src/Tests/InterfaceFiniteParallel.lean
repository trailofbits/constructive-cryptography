module

public import ConstructiveCryptography.Instances.FiniteParallel
public import Tests.TypedNaryParallel

/-!
# The abstract finite-family calculus on typed systems

The generic context/split attachment calculation specializes to bit resources using the
interface instance. Both finite-family notation scopes coexist with ordered binary parallel;
the abstract operations elaborate to the established typed operations.
-/

public section

namespace Tests.InterfaceFiniteParallel

open CategoryTheory MonoidalCategory
open SystemAlgebra SystemAlgebra.Tests
open ConstructiveCryptography
open scoped SystemAlgebra

-- Match the equality decisions selected by the abstract finite-family instance.
noncomputable local instance : DecidableEq Unit := Classical.decEq Unit
noncomputable local instance : DecidableEq (Option Unit) := Classical.decEq (Option Unit)

/-- The typed-only scope retains its original resource-family notation. -/
example (R : Unit → TypedSystem bitInterface) :
    (∥ k, R k) = TypedSystem.parallelAll R := rfl

open scoped ConstructiveCryptography.FiniteParallel

/-- The generic two-stage calculation applies to a pair of concrete fixed-bit resources. -/
lemma fixedBit_context_split {X : Interface}
    (context : X ⟶ (⨂ _ : Option Unit, bitInterface))
    (α : Option Unit → TypedConverter bitInterface bitInterface) :
    (context ≫ (⨂ₘ k, α k)) • (∥ _ : Option Unit, fixedBit false) =
      (context ≫ (FiniteParallel.optionSplit (fun _ : Option Unit => bitInterface)).hom) •
        ((α none ⊗ₘ (⨂ₘ k : Unit, α (some k))) •
          TypedSystem.parallel (fixedBit false) (∥ _ : Unit, fixedBit false)) :=
  FiniteParallel.context_split_attachment context α (fun _ => fixedBit false)

/-- Finite-family notation from both scopes denotes the chosen typed resource product. -/
example (R : Unit → TypedSystem bitInterface) :
    (∥ k, R k) = TypedSystem.parallelAll R := rfl

/-- Binder and binary notation coexist without changing the ordered typed product. -/
example (R : Unit → TypedSystem bitInterface) (S : TypedSystem bitInterface) :
    (∥ k, R k) ∥ S = TypedSystem.parallel (TypedSystem.parallelAll R) S := rfl

/-- Interface and converter family binders also resolve to the existing typed operations. -/
example (α : Unit → (bitInterface ⟶ bitInterface)) :
    (show (⨂ _ : Unit, bitInterface) ⟶ (⨂ _ : Unit, bitInterface) from
      ⨂ₘ k, α k) = TypedConverter.parallelAll α := rfl

/-- The abstract-to-typed bridge does not fix the caller's equality implementation. -/
example {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface}
    (R : ∀ k, TypedSystem (A k)) :
    FiniteParallel.parallelAll R = TypedSystem.parallelAll R := Interface.cc_parallelAll_eq R

#print axioms SystemAlgebra.Interface.cc_parallelAll_eq
#print axioms SystemAlgebra.Interface.finiteParallel
#print axioms fixedBit_context_split

end Tests.InterfaceFiniteParallel

module

public import ConstructiveCryptography.Notation
public import RandomSystems.Typed.Functional

/-!
# Forward associator and unitor attachment laws

Consumer tests for `CryptographicAlgebra.{associator_hom_attach, leftUnitor_hom_attach,
rightUnitor_hom_attach}` in an arbitrary cryptographic algebra, and for their one-line
interface instances `Interface.{associator_hom_attach, leftUnitor_hom_attach,
rightUnitor_hom_attach}` regrouping three typed systems side by side through the associator.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.ParallelCoherenceHom

open CategoryTheory MonoidalCategory
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

section Abstract

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : C → Type w} [ResourceTheory C Phi] [CryptographicAlgebra C Phi]

/-- Forward associator regroups three resources in any cryptographic algebra. -/
example {A B D : C} (L : Phi A) (M : Phi B) (R : Phi D) :
    (α_ A B D).hom • parallel L (parallel M R) = parallel (parallel L M) R :=
  associator_hom_attach L M R

/-- `cc_normalize` regroups three resources through `(α_ A B D).hom` in any algebra. -/
example {A B D : C} (L : Phi A) (M : Phi B) (R : Phi D) :
    attach (α_ A B D).hom (parallel L (parallel M R)) = parallel (parallel L M) R := by
  cc_normalize

/-- Forward left unitor places `dummy` on the left in any cryptographic algebra. -/
example {A : C} (R : Phi A) :
    (λ_ A).hom • R = parallel (dummy (C := C)) R :=
  leftUnitor_hom_attach R

/-- Forward right unitor places `dummy` on the right in any cryptographic algebra. -/
example {A : C} (R : Phi A) :
    (ρ_ A).hom • R = parallel R (dummy (C := C)) :=
  rightUnitor_hom_attach R

end Abstract

section Interfaces

open SystemAlgebra
open scoped SystemAlgebra

/-- Forward left unitor on interfaces places `TypedSystem.dummy` on the left. -/
example {A : Interface} (R : TypedSystem A) :
    (Interface.leftUnitor A).hom • R = TypedSystem.dummy ∥ R :=
  Interface.leftUnitor_hom_attach R

/-- Forward right unitor on interfaces places `TypedSystem.dummy` on the right. -/
example {A : Interface} (R : TypedSystem A) :
    (Interface.rightUnitor A).hom • R = R ∥ TypedSystem.dummy :=
  Interface.rightUnitor_hom_attach R

/-- Forward associator regroups three typed systems side by side on arbitrary interfaces. -/
example {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B) (T : TypedSystem C) :
    (Interface.associator A B C).hom • (R ∥ (S ∥ T)) = (R ∥ S) ∥ T :=
  Interface.associator_hom_attach R S T

/-- `cc_normalize` regroups three typed systems through `Interface.associator`. -/
example {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B) (T : TypedSystem C) :
    (Interface.associator A B C).hom • (R ∥ (S ∥ T)) = (R ∥ S) ∥ T := by
  cc_normalize

/-- `cc_normalize` regroups three typed systems through `(α_ A B C).hom`. -/
example {A B C : Interface} (R : TypedSystem A) (S : TypedSystem B) (T : TypedSystem C) :
    (α_ A B C).hom • (R ∥ (S ∥ T)) = (R ∥ S) ∥ T := by
  cc_normalize

/-- Three concrete one-query deterministic systems regrouped side by side through `(α_ A B C).hom`
(negation on `Bool`, constant `()` on `Unit`, and identity on `Bool`). -/
example :
    let A := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1
    let B := Interface.queryBudget Unit (fun _ => Unit) (fun _ => Unit) 1
    let C := Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1
    let R : TypedSystem A := TypedSystem.ofFunction fun _ b => !b
    let S : TypedSystem B := TypedSystem.ofFunction fun _ u => u
    let T : TypedSystem C := TypedSystem.ofFunction fun _ b => b
    (α_ A B C).hom • (R ∥ (S ∥ T)) = (R ∥ S) ∥ T := by
  intro A B C R S T
  exact Interface.associator_hom_attach R S T

end Interfaces

#print axioms ConstructiveCryptography.CryptographicAlgebra.associator_hom_attach
#print axioms ConstructiveCryptography.CryptographicAlgebra.leftUnitor_hom_attach
#print axioms ConstructiveCryptography.CryptographicAlgebra.rightUnitor_hom_attach
#print axioms SystemAlgebra.Interface.associator_hom_attach
#print axioms SystemAlgebra.Interface.leftUnitor_hom_attach
#print axioms SystemAlgebra.Interface.rightUnitor_hom_attach

end Tests.ParallelCoherenceHom

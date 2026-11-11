module

public import ConstructiveCryptography.CryptographicAlgebra.FiniteParallel.Specification
public import ConstructiveCryptography.Instances.FiniteParallel
public import Tests.TypedNaryParallel

/-!
# A selected component's specification in a typed family

Equality to a reference resource is transported from the head through a fixed arbitrary tail.
The test uses the existing bit interface and imposes no equality premise on the tail.
-/

public section

open CategoryTheory MonoidalCategory
open ConstructiveCryptography CryptographicAlgebra FiniteParallel
open SystemAlgebra SystemAlgebra.Tests
open scoped ConstructiveCryptography.FiniteParallel

/-- Replacing an equal head preserves its assembled family, with any resources in the tail. -/
example (R : Option Unit → TypedSystem bitInterface) (T : TypedSystem bitInterface)
    (selected : R none = T) :
    (∥ k, R k) = (optionSplit (fun _ : Option Unit => bitInterface)).hom •
      parallel T (∥ j : Unit, R (some j)) := by
  let A : Option Unit → Interface := fun _ => bitInterface
  let splitIso := optionSplit A
  let reindexIso := reindex (Equiv.refl (Option Unit)) A
  have transported := mem_parallelAll_of_mem (Index := TypedSystem)
    (fun A reference => {S : TypedSystem A | S = reference}) (Equiv.refl (Option Unit)) R
    (fun reference => parallel reference (∥ j : Unit, R (some j)))
    (fun reference => splitIso.hom • reference)
    (fun reference => reindexIso.hom • reference)
    (by rintro i S rfl; rfl) (by rintro i S rfl; rfl) (by rintro i S rfl; rfl) selected
  change (∥ k, R k) = reindexIso.hom • (splitIso.hom • parallel T (∥ j, R (some j)))
    at transported
  simpa only [reindexIso, reindex_refl, Interface.identity_attach] using transported

#print axioms mem_parallelAll_of_mem

import ConstructiveCryptography.Distinguisher

/-!
# Decision-layer boundary checks

The decision layer imports no category, resource theory, action or random system: the
`#check_failure` lines confirm that `ResourceTheory`, `DistinguisherAction` and `TypedSystem` are
out of scope. No admitted set is selected by importing it, not even the value
`AdmissibleDistinguishers.all`, so instance search fails. The derived substitution model uses
exactly the supplied admitted set and the decision advantage.
-/

open ConstructiveCryptography

#check_failure ConstructiveCryptography.ResourceTheory
#check_failure ConstructiveCryptography.DistinguisherAction
#check_failure SystemAlgebra.TypedSystem

/-- No `AdmissibleDistinguishers` instance is found for arbitrary interfaces `I` and tests `_D`. -/
example {I : Type} {_D : I → Type} : True := by
  fail_if_success have : AdmissibleDistinguishers I _D := inferInstance
  trivial

/-- The derived model uses exactly the selected tests and the original decision advantage. -/
example {I : Type} {Phi D : I → Type} [Distinguishers I Phi D]
    (admitted : ∀ A, Set (D A)) {A : I} (d : D A) (R S : Phi A) :
    (Distinguishers.distinguisherAdvantage (Phi := Phi) admitted).admissible A = admitted A ∧
      (Distinguishers.distinguisherAdvantage (Phi := Phi) admitted).advantage A d R S =
        Distinguishers.advantage d R S :=
  ⟨rfl, rfl⟩

#print axioms Distinguishers.distinguisherAdvantage

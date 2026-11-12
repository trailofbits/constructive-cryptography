module

public import RandomSystems.Cumulative.ParallelInputs
public import Tests.CumulativeAttachment

/-! Input-domain transport includes impossible prefixes and preserves the typed product formula. -/

@[expose] public section

namespace Tests.ParallelInputDomains

open SystemAlgebra Probability Probability.Distribution
open SystemAlgebra.Tests.CumulativeAttachment

/-- Two independent unlimited fair sources on nonempty trigger histories. -/
lemma fair_parallel_normalized :
    IsRandomSystem
      (fun h x => parallelInputs (fun xs => xs ≠ []) (fun xs => xs ≠ [])
        (h.map Prod.fst ++ [x]))
      (fun h => parallelMass
        (sourceMass (A := Σ _ : Unit, Unit)
          ((𝒰[Bool]).map (Sigma.mk (β := fun _ : Unit => Bool) ())))
        (sourceMass (A := Σ _ : Unit, Unit)
          ((𝒰[Bool]).map (Sigma.mk (β := fun _ : Unit => Bool) ())))
        (h.map ((sumAlphabet (Sum.rec (fun _ : Unit => Unit) (fun _ : Unit => Unit))).symm.prodCongr
          (sumAlphabet (Sum.rec (fun _ : Unit => Bool) (fun _ : Unit => Bool))).symm))) :=
  parallelMass_isRandomSystem_ofInputs fresh_normalized fresh_normalized

/-- A cross-component reply has zero mass even after an already impossible prefix. -/
lemma wrong_port_after_impossible :
    let x : Σ l, Sum.rec (fun _ : Unit => Unit) (fun _ : Unit => Unit) l := ⟨.inl (), ()⟩
    let y : Σ l, Sum.rec (fun _ : Unit => Bool) (fun _ : Unit => Bool) l := ⟨.inr (), false⟩
    parallelMass
      (sourceMass (A := Σ _ : Unit, Unit)
        ((𝒰[Bool]).map (Sigma.mk (β := fun _ : Unit => Bool) ())))
      (sourceMass (A := Σ _ : Unit, Unit)
        ((𝒰[Bool]).map (Sigma.mk (β := fun _ : Unit => Bool) ())))
      (([(x, y)] ++ [(x, y)]).map
        ((sumAlphabet (Sum.rec (fun _ : Unit => Unit) (fun _ : Unit => Unit))).symm.prodCongr
          (sumAlphabet (Sum.rec (fun _ : Unit => Bool) (fun _ : Unit => Bool))).symm)) = 0 := by
  exact parallelMass_repliesAtQueriedInterface fresh_ports fresh_ports _ _ _ (by
    intro he
    cases he)

/-- The bounded typed constructor retains its defining cumulative product at every history. -/
example (A B : Interface) (R : TypedSystem A) (S : TypedSystem B)
    (h : List ((Σ i, (Interface.tensor A B).X i) × (Σ i, (Interface.tensor A B).Y i))) :
    (TypedSystem.parallel R S).1 h = parallelMass R.1 S.1
      (h.map ((sumAlphabet (Sum.rec A.X B.X)).symm.prodCongr
        (sumAlphabet (Sum.rec A.Y B.Y)).symm)) := rfl

#print axioms IsRandomSystem.congr_domain
#print axioms IsRandomSystem.relabel
#print axioms IsRandomSystem.mass_eq_zero_of_not_admitted
#print axioms IsRandomSystem.possible_inputs
#print axioms parallelMass_admits_iff_ofInputs
#print axioms parallelMass_isRandomSystem_ofInputs
#print axioms parallelMass_repliesAtQueriedInterface
#print axioms fair_parallel_normalized
#print axioms wrong_port_after_impossible

end Tests.ParallelInputDomains

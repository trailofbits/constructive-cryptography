module

public import ConstructiveCryptography.CryptographicAlgebra.PublicPort
public import ConstructiveCryptography.Instances.Algebra
public import Tests.QueryRouting

/-!
# A public reader of the writer’s register

The writer calls the register through the internal port; the public port reads it. Each
caller has one query. After a write of `b`, the read returns `b` regardless of the initial bit.
-/

@[expose] public section

namespace SystemAlgebra.Tests.PublicPort

open CategoryTheory MonoidalCategory ConstructiveCryptography CryptographicAlgebra
open Probability.Distribution QueryRouting

/-- The auxiliary resource is empty. Both callers access the register initialized to `b`. -/
noncomputable def publicRegister (b : Bool) : TypedSystem registerPorts :=
  CryptographicAlgebra.attach
    (withPublicPort (C := Interface) (P := bits 1) (λ_ (bits 1)).inv registerRouter)
    (CryptographicAlgebra.parallel (dummy (C := Interface))
      (TypedSystem.ofProbAutomaton registerPorts (ProbStep.ofDeterministic registerStep)
        (ProbDist.single b)))

/-- A completed write and the following public read observe a single register state. -/
lemma publicRegister_write_read_mass (initial written read : Bool) :
    (publicRegister initial).1
      [(⟨.inl (), written⟩, ⟨.inl (), !written⟩), (⟨.inr (), false⟩, ⟨.inr (), read⟩)] =
      if read = written then 1 else 0 := by
  let reg := TypedSystem.ofProbAutomaton registerPorts (ProbStep.ofDeterministic registerStep)
    (ProbDist.single initial)
  have routed : publicRegister initial = registerRouter • reg :=
    withPublicPort_attach_dummy (C := Interface) (Φ := TypedSystem) (B := bits 1) (P := bits 1)
      registerRouter reg
  rw [routed]
  exact register_write_read_mass initial written read

/-- The second call is admitted as soon as the public reader issues it. A third request on
that same port would exceed its allowance, even before it receives a reply. -/
example (b : Bool) :
    let w : Σ i, registerPorts.X i := ⟨.inl (), b⟩
    let r : Σ i, registerPorts.X i := ⟨.inr (), false⟩
    registerPorts.domain [w, r] ∧ ¬ registerPorts.domain [w, r, r] := by
  dsimp only
  simp only [Interface.parallelDomain, parallelInputs, bits, Interface.queryBudget, ne_eq,
    reduceCtorEq, not_false_eq_true, sumAlphabet, Equiv.symm_mk, Equiv.coe_fn_mk, List.map_cons,
    List.map_nil, restrict_cons_self, restrict_cons_ne, restrict_nil, List.cons_ne_self,
    List.length_cons, List.length_nil, zero_add, Std.le_refl, and_self, or_true, Nat.reduceAdd,
    Nat.not_ofNat_le_one, and_false, or_self]

end SystemAlgebra.Tests.PublicPort

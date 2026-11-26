module

public import RandomSystems.System.Interconnection

/-!
# Membership in a component history

The natural-number ports carry dependent values `Fin (n+1)`. Projection membership retains
the selected value and rejects a value recorded only at another port.
-/

@[expose] public section

namespace Tests.RestrictMembership

open SystemAlgebra

example : (1 : Fin 2) ∈ restrict 1
    [(⟨0, (0 : Fin 1)⟩ : Σ n : Nat, Fin (n + 1)), ⟨1, 1⟩] := by
  rw [mem_restrict_iff]
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

example : (0 : Nat) ∉ restrict false [(⟨true, 0⟩ : Sigma (fun _ : Bool => Nat))] := by
  rw [mem_restrict_iff]
  intro member
  have tagged := List.mem_singleton.mp member
  have ports := congrArg Sigma.fst tagged
  cases ports

#print axioms SystemAlgebra.mem_restrict_iff

end Tests.RestrictMembership

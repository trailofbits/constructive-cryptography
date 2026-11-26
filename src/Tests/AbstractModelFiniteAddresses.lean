module

public import Commons.Definitions.AbstractModel.FiniteAddresses
public import Tests.AbstractModelAddressMap

/-!
# Finite-address encoding checks

The existing register model checks unused initial registers, never-read destinations,
and the same command code across every reply history, including a caller that stops immediately.
-/

@[expose] public section

open SystemAlgebra Commons.AbstractModel

namespace Tests.AbstractModelFiniteAddresses

open Tests.AbstractModel

/-- Address coding leaves the existing submitted value unchanged. -/
example : model.mapCommand (fun _ : ℕ => (0 : Fin 1)) submit =
    (⟨.submit, 3⟩ : model.Command (Fin 1)) := rfl

/-- The footprint includes an unused initial address and a stored destination never read later. -/
example : ∃ (n : ℕ) (code : ℕ → Fin n) (decode : Fin n ↪ ℕ),
    decode (code 5) = 5 ∧ decode (code 7) = 7 ∧ code 5 ≠ code 7 ∧
      model.mapCommand decode (model.mapCommand code submit) = submit := by
  obtain ⟨n, code, decode, initial, addresses, commands⟩ :=
    exists_fin_address_encoding (M := model) 5 {store, submit}
      ((Set.finite_singleton submit).insert store)
  have destination : decode (code 7) = 7 :=
    addresses store (Set.mem_insert _ _) 7 (Or.inr rfl)
  refine ⟨n, code, decode, initial, destination, ?_, ?_⟩
  · intro collision
    have impossible := congrArg decode collision
    rw [initial, destination] at impossible
    cases impossible
  · exact commands submit (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- One code handles every branch of the existing fixed-query environment. -/
example : ∃ (n : ℕ) (code : ℕ → Fin n) (decode : Fin n ↪ ℕ),
    decode (code 0) = 0 ∧
      ∀ ys z, z ∈ (DDE.ofQueries (Y := Bool) [store, submit]).1 ys →
        model.mapCommand decode (model.mapCommand code z) = z := by
  obtain ⟨n, code, decode, initial, _, commands⟩ :=
    exists_fin_address_encoding_of_queryBounded (M := model) 0
      (DDE.ofQueries (Y := Bool) [store, submit]) (DDE.ofQueries_queryBounded _)
  exact ⟨n, code, decode, initial, commands⟩

/-- Even a caller that asks nothing retains an exact code for the initial register. -/
example : ∃ (n : ℕ) (code : ℕ → Fin n) (decode : Fin n ↪ ℕ), decode (code 5) = 5 := by
  obtain ⟨n, code, decode, initial, _, _⟩ :=
    exists_fin_address_encoding_of_queryBounded (M := model) 5
      (DDE.ofQueries (Y := Bool) []) (DDE.ofQueries_queryBounded _)
  exact ⟨n, code, decode, initial⟩

#print axioms Commons.AbstractModel.mapCommand_mapCommand_eq_of_inverse_on
#print axioms Commons.AbstractModel.exists_fin_address_encoding
#print axioms Commons.AbstractModel.exists_fin_address_encoding_of_queryBounded

end Tests.AbstractModelFiniteAddresses

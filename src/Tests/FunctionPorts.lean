module

public import RandomSystems.PDS.Function

/-!
# Port certificates for fixed evaluators

Natural-number ports require no finite interface. A second evaluator always replies at port
zero; it satisfies the port contract on its domain of nonempty port-zero histories.
-/

@[expose] public section

namespace Tests.FunctionPorts

open SystemAlgebra

/-- At port `i : ℕ`, a query `x : Fin (i+1)` receives the natural reply `x.val` at port `i`. -/
example : RepliesAtQueriedInterface
    (DDS.ofFunction
      (fun h : List (Σ i : ℕ, Fin (i + 1)) => h ≠ [])
      ⟨fun h => h rfl, fun _ hn _ => hn⟩
      (fun q => (⟨q.1, q.2.val⟩ : Σ _ : ℕ, ℕ))).1 :=
  DDS.ofFunction_repliesAtQueriedInterface _ _ _ (fun _ _ _ => rfl)

/-- `zeroPortDomain h` means `h ≠ []` and every query in `h` has port zero. -/
def zeroPortDomain (h : List (Σ _ : ℕ, ℕ)) : Prop :=
  h ≠ [] ∧ ∀ q ∈ h, q.1 = 0

lemma zeroPortDomain_prefix : ¬ zeroPortDomain [] ∧
    ∀ {p h}, p <+: h → p ≠ [] → zeroPortDomain h → zeroPortDomain p := by
  constructor
  · intro h
    exact h.1 rfl
  · intro p h hp hn hh
    exact ⟨hn, fun q hq => hh.2 q (hp.subset hq)⟩

/-- `zeroPortReply ⟨i,x⟩ = ⟨0,x⟩`: retain the query value and always select reply port zero. -/
def zeroPortReply (q : Σ _ : ℕ, ℕ) : Σ _ : ℕ, ℕ := ⟨0, q.2⟩

/-- The port certificate uses admission, since this function changes every nonzero port. -/
lemma admitted_ports : RepliesAtQueriedInterface
    (DDS.ofFunction zeroPortDomain zeroPortDomain_prefix zeroPortReply).1 := by
  apply DDS.ofFunction_repliesAtQueriedInterface
  intro h x admitted
  exact (admitted.2 x (List.mem_append_right _ (List.mem_singleton_self _))).symm

/-- Port preservation fails for this function outside its admitted domain. -/
example : (zeroPortReply ⟨1, 5⟩).1 ≠ 1 := Nat.zero_ne_one

#print axioms DDS.ofFunction_repliesAtQueriedInterface
#print axioms zeroPortDomain_prefix
#print axioms admitted_ports

end Tests.FunctionPorts

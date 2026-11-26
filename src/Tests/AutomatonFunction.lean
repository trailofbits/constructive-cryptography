module

public import RandomSystems.System.AutomatonFunction
public import Tests.FunctionPorts

/-!
# Retained evaluators on an infinite port family

The natural-number parameter `k` selects replies `k+i+x` at port `i`. The existing port-zero
domain tests both repeated admitted inputs and refusal at an unadmitted port.
-/

@[expose] public section

namespace Tests.AutomatonFunction

open SystemAlgebra Tests.FunctionPorts

/-- The evaluator returns `k+i+x` while retaining `k` at every natural-number port. -/
lemma retained_evaluator (k : ℕ) :
    filterDom zeroPortDomain (automatonSystem (fun k (i : ℕ) (x : ℕ) => (k, k + i + x)) k) =
      (DDS.ofFunction zeroPortDomain zeroPortDomain_prefix
        (fun q : Σ _ : ℕ, ℕ => ⟨q.1, k + q.1 + q.2⟩)).1 :=
  filterDom_automatonSystem_eq_ofFunction zeroPortDomain zeroPortDomain_prefix
    (fun k i x => k + i + x) k

/-- Two queries use the same retained value `10`; the latest query `4` receives `14`. -/
example : filterDom zeroPortDomain
    (automatonSystem (fun k (i : ℕ) (x : ℕ) => (k, k + i + x)) 10)
    [⟨0, 3⟩, ⟨0, 4⟩] = Part.some ⟨0, 14⟩ := by
  rw [retained_evaluator]
  simpa only [List.cons_append, List.nil_append, zeroPortDomain, List.mem_cons,
    ne_eq, List.cons_ne_nil, not_false_eq_true, forall_eq_or_imp, forall_eq, List.not_mem_nil,
    false_implies, forall_const, and_self, ↓reduceIte] using
    DDS.ofFunction_snoc (Y := Σ _ : ℕ, ℕ) zeroPortDomain zeroPortDomain_prefix
      (fun q : Σ _ : ℕ, ℕ => ⟨q.1, 10 + q.1 + q.2⟩) [⟨0, 3⟩] ⟨0, 4⟩

/-- The same two presentations refuse an input at port `1`, outside their declared domain. -/
example : filterDom zeroPortDomain
    (automatonSystem (fun k (i : ℕ) (x : ℕ) => (k, k + i + x)) 10)
    [⟨1, 3⟩] = Part.none := by
  rw [retained_evaluator]
  simpa only [List.nil_append, zeroPortDomain, List.mem_singleton, List.cons_ne_nil,
    not_false_eq_true,
    forall_eq, Nat.one_ne_zero, and_false, ↓reduceIte] using
    DDS.ofFunction_snoc (Y := Σ _ : ℕ, ℕ) zeroPortDomain zeroPortDomain_prefix
      (fun q : Σ _ : ℕ, ℕ => ⟨q.1, 10 + q.1 + q.2⟩) [] ⟨1, 3⟩

#print axioms SystemAlgebra.filterDom_automatonSystem_eq_ofFunction
#print axioms retained_evaluator

end Tests.AutomatonFunction

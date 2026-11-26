module

public import RandomSystems.Typed.DSL.Programs

/-!
# Cost certificates with natural-number queries

A one-call forwarder accepts only the outside query `7`. Both query alphabets are ℕ.
Its pending inside call already counts as one, before any inside reply arrives.
-/

@[expose] public section

namespace Tests.ProgramCostDomain

open SystemAlgebra SystemAlgebra.DSL

/-- Forward `n` once and return the inside reply, keeping unit state. -/
noncomputable def forward : Program Unit Unit Unit (fun _ => ℕ) (fun _ => ℕ)
    (fun _ => ℕ) (fun _ => ℕ) :=
  fun state _ n => callProg () n (fun reply => returnProg (state, reply))

lemma forward_bounded : forward.Bounded 1 :=
  fun _ _ _ => callBound_call _ _ _ (fun _ => callBound_return 0 _)

lemma forward_costs : forward.Costs (fun _ => 1) :=
  fun _ _ _ => callCost_call _ _ _ (fun _ => callCost_return _)

/-- The outside domain allows one query, whose value must be `7`. -/
def outside (xs : List (Σ _ : Unit, ℕ)) : Prop :=
  xs ≠ [] ∧ xs.length ≤ 1 ∧ ∀ x ∈ xs, x.2 = 7

/-- The inside domain allows any one natural-number query. -/
def inside (xs : List (Σ _ : Unit, ℕ)) : Prop := xs ≠ [] ∧ xs.length ≤ 1

/-- The raw certificate retains the restricted domain without a finite query alphabet. -/
lemma forward_domain : IsDDCFrom inside outside 1 (DDC.ofProgramOn () forward outside) := by
  apply DDC.ofProgramOn_isDDCFrom_of_costs (q := 1) forward_bounded
  · intro p h hp hne hh
    exact ⟨hne, hp.length_le.trans hh.2.1, fun x hx => hh.2.2 x (hp.subset hx)⟩
  · exact forward_costs
  · intro xs allowed
    simpa only [List.map_const', List.sum_const_nat, mul_one] using allowed.2.1
  · exact fun _ hne hlen => ⟨hne, hlen⟩

/-- Sending the inside query already incurs its full one-call cost. -/
lemma pending_cost :
    let u : Σ l : Two Unit Unit, twoFam (fun _ => ℕ) (fun _ => ℕ) l :=
      ⟨⟨none, ()⟩, 7⟩
    let v : Σ l : Two Unit Unit, twoFam (fun _ => ℕ) (fun _ => ℕ) l :=
      ⟨⟨some (), ()⟩, 7⟩
    Replies (DDC.ofProgramOn () forward outside) [u] [v] ∧
      (insideQueries [v]).length = 1 ∧
      (insideQueries [v]).length ≤ ((outsideInputs [u]).map (fun _ => 1)).sum := by
  intro u v
  have allowed : outside [⟨(), 7⟩] :=
    ⟨List.cons_ne_nil _ _, le_rfl, fun x hx => by
      obtain rfl := List.mem_singleton.mp hx
      rfl⟩
  have outer : outsideInputs [u] = [⟨(), 7⟩] := outsideInputs_outside _ _
  have replied : Replies (DDC.ofProgramOn () forward outside) [u] [v] := by
    apply (replies_snoc (xs := []) (ys := [])).mpr
    refine ⟨replies_nil _, ?_⟩
    change filterDom (fun xs => outsideInputs xs = [] ∨ outside (outsideInputs xs))
      (DDC.ofProgram () forward) [u] = Part.some v
    rw [filterDom, ite_eq_left (Or.inr (outer ▸ allowed))]
    rw [show [u] = [] ++ [u] from rfl, DDC.ofProgram_snoc]
    simp only [Program.after_nil, Option.bind_some, Program.step, Program.emit,
      forward, callProg]
    rfl
  refine ⟨replied, ?_, ?_⟩
  · rw [insideQueries_inside]
    rfl
  · exact DDC.insideQueries_length_le_of_costs forward_costs
      (DDC.replies_ofProgramOn (h := [(u, v)]) replied).1

#print axioms SystemAlgebra.DDC.ofProgramOn_isDDCFrom_of_costs
#print axioms forward_domain
#print axioms pending_cost

end Tests.ProgramCostDomain

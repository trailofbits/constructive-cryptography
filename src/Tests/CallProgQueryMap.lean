module

public import RandomSystems.Typed.DSL.Programs

/-!
# Query relabeling through two calls

The first call receives `y`, and the second queries `y+4`; both replies determine the final
sum. Reducing query values modulo two retains pending calls, matching and wrong-port replies,
and the final value. The two-call equation applies the same constructor law at each call.
-/

@[expose] public section

namespace Tests.CallProgQueryMap

open SystemAlgebra SystemAlgebra.DSL

/-- The query map retains the Boolean port and reduces each natural input modulo two. -/
def queryMap (_ : Bool) (x : ℕ) : ℕ := x % 2

/-- Call `true(5)`, then `false(y+4)`, returning the sum of their two replies. -/
noncomputable def twoCalls :
    List ((Σ _ : Bool, ℕ) × (Σ _ : Bool, ℕ)) → ℕ ⊕ (Σ _ : Bool, ℕ) :=
  callProg true 5 (fun y => callProg false (y + 4) (fun z => returnProg (y + z)))

/-- The same two calls have their inputs reduced modulo two, retaining both replies. -/
noncomputable def mappedTwoCalls :
    List ((Σ _ : Bool, ℕ) × (Σ _ : Bool, ℕ)) → ℕ ⊕ (Σ _ : Bool, ℕ) :=
  callProg true (queryMap true 5)
    (fun y => callProg false (queryMap false (y + 4)) (fun z => returnProg (y + z)))

/-- Query relabeling transports the two calls and retains their reply sum. -/
lemma twoCalls_map (h : List ((Σ _ : Bool, ℕ) × (Σ _ : Bool, ℕ))) :
    Sum.map id (Sigma.map id queryMap) (twoCalls h) =
      mappedTwoCalls (h.map (Prod.map (Sigma.map id queryMap) id)) := by
  apply callProg_queryMap
  intro y t
  exact callProg_queryMap queryMap false (y + 4) _ _ (fun _ _ => rfl) t

example : queryMap true 3 = queryMap true 5 := rfl

example : mappedTwoCalls [] = .inr ⟨true, 1⟩ := rfl

example : mappedTwoCalls [(⟨true, 1⟩, ⟨true, 3⟩)] = .inr ⟨false, 1⟩ := by
  simp only [mappedTwoCalls, callProg, ↓reduceDIte, queryMap]

example : mappedTwoCalls [(⟨true, 1⟩, ⟨false, 3⟩)] = .inr ⟨true, 1⟩ := by
  simp only [mappedTwoCalls, callProg, queryMap]
  rw [dite_eq_right (by intro h; cases h)]

example : mappedTwoCalls [(⟨true, 1⟩, ⟨true, 3⟩), (⟨false, 1⟩, ⟨false, 8⟩)] =
    .inl 11 := by
  simp only [mappedTwoCalls, callProg, ↓reduceDIte, returnProg]

/-- The same two calls return their reply sum modulo two. -/
noncomputable def parityTwoCalls :
    List ((Σ _ : Bool, ℕ) × (Σ _ : Bool, ℕ)) → ℕ ⊕ (Σ _ : Bool, ℕ) :=
  callProg true (queryMap true 5)
    (fun y => callProg false (queryMap false (y + 4))
      (fun z => returnProg ((y + z) % 2)))

/-- Result mapping and query mapping compose through both existing call blocks. -/
lemma twoCalls_map_result (h : List ((Σ _ : Bool, ℕ) × (Σ _ : Bool, ℕ))) :
    Sum.map (fun n => n % 2) (Sigma.map id queryMap) (twoCalls h) =
      parityTwoCalls (h.map (Prod.map (Sigma.map id queryMap) id)) := by
  apply callProg_map
  intro y t
  exact callProg_map (fun n => n % 2) queryMap false (y + 4) _ _ (fun _ _ => rfl) t

example : parityTwoCalls [] = .inr ⟨true, 1⟩ := rfl

example : parityTwoCalls [(⟨true, 1⟩, ⟨false, 3⟩)] = .inr ⟨true, 1⟩ := by
  simp only [parityTwoCalls, callProg, queryMap]
  rw [dite_eq_right (by intro h; cases h)]

example : parityTwoCalls [(⟨true, 1⟩, ⟨true, 3⟩), (⟨false, 1⟩, ⟨false, 8⟩)] =
    .inl 1 := by
  simp only [parityTwoCalls, callProg, ↓reduceDIte, returnProg]

#print axioms SystemAlgebra.DSL.callProg_map
#print axioms twoCalls_map_result
#print axioms SystemAlgebra.DSL.callProg_queryMap
#print axioms twoCalls_map

end Tests.CallProgQueryMap

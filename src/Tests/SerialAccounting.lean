import Tests.DirectCalls
import RandomSystems.Converter.SerialAccounting

/-!
# Input-dependent serial costs and interrupted calls

Zero inputs return immediately; nonzero inputs make two dependent calls. A transcript
stopped after the first query has spent one unit, although its invocation reserved two.
The serial theorem passes this actual-work inequality through exact component domains.
-/

namespace SystemAlgebra.Tests.SerialAccounting

open DirectCalls

/-- This call's cost depends on its input value, not only its Unit interface. -/
def variableCall (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) :=
  if u.2 = 0 then .inl 0 else chainCall u rs

def variableCost (u : Σ _ : Unit, Nat) : Nat := if u.2 = 0 then 0 else 2

lemma variableCall_phase (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    (variableCall u rs).isRight = true → rs.length < variableCost u := by
  by_cases hz : u.2 = 0
  · simp [variableCall, hz]
  · simpa [variableCall, variableCost, hz] using (chainCall_phase u rs).mp

abbrev natRule := callRule (O := Unit) (J := Unit)
  (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat) variableCall

def interrupted : List
    ((Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
      (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l)) :=
  [(⟨⟨none, ()⟩, 7⟩, ⟨⟨some (), ()⟩, 7⟩)]

/-- Stopping immediately after an inside query is a valid canonical transcript. -/
lemma interrupted_replies : Replies (canon natRule)
    (interrupted.map Prod.fst) (interrupted.map Prod.snd) := by
  apply (replies_canon_iff natRule Part.not_none_dom interrupted).mpr
  constructor
  · change Admitted converterAdmits ([] ++ interrupted)
    exact admitted_snoc.mpr ⟨admitted_nil _, by simp [converterAdmits, admitAfter]⟩
  · change Replies natRule ([] ++ [⟨⟨none, ()⟩, 7⟩]) ([] ++ [⟨⟨some (), ()⟩, 7⟩])
    exact replies_snoc.mpr ⟨replies_nil _, rfl⟩

/-- A pending call is charged already, but an exact completed-call count would be false. -/
example : (insideQueries (interrupted.map Prod.snd)).length = 1 ∧
    ((outsideInputs (interrupted.map Prod.fst)).map variableCost).sum = 2 := by
  simp [interrupted, insideQueries, outsideInputs, splitIn, variableCost]

/-- The arbitrary-reply accounting theorem counts the pending query. -/
example : (insideQueries (interrupted.map Prod.snd)).length ≤
    ((outsideInputs (interrupted.map Prod.fst)).map variableCost).sum := by
  apply callRule_query_count variableCall variableCost variableCall_phase
  exact interrupted_replies.mono fun _ _ hy => canon_mem hy

/-- A certified outer converter retains its actual intermediate input-dependent costs. -/
example {O : Type} {U V : O → Type} {E F : List (Σ _ : Unit, Nat) → Prop}
    {G : List (Σ o, U o) → Prop} {bβ bα : Nat}
    {β : InsideOutsideSystem O Unit U V (fun _ => Nat) (fun _ => Nat)}
    (hβ : IsDDCFrom F G bβ β)
    (hα : IsDDCFrom E F bα (callConverter (O := Unit) (J := Unit)
      (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
      variableCall F))
    {T : List ((Σ l, twoFam U (fun _ : Unit => Nat) l) ×
      (Σ l, twoFam V (fun _ : Unit => Nat) l))}
    (hr : Replies (trim (serialM β (callConverter variableCall F)))
      (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ Tb : List ((Σ l, twoFam U (fun _ : Unit => Nat) l) ×
      (Σ l, twoFam V (fun _ : Unit => Nat) l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      (insideQueries (T.map Prod.snd)).length ≤
        ((insideQueries (Tb.map Prod.snd)).map variableCost).sum :=
  hβ.comp_callConverter_query_count_le variableCall variableCost variableCall_phase hα hr

#print axioms SystemAlgebra.IsDDCFrom.comp_query_charge_le
#print axioms SystemAlgebra.IsDDCFrom.comp_query_charge_le_budget
#print axioms SystemAlgebra.IsDDCFrom.comp_callConverter_query_count_le

end SystemAlgebra.Tests.SerialAccounting

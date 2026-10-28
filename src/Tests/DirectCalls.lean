import RandomSystems.Typed.CallRuleFunctional

/-!
# Direct-call boundary examples

The first query uses the outside input. The second query uses the first oracle reply. These
examples exercise the direct rule without a Program or DSL representation.

```text
u ──► query u ──► reply y₁ ──► query (y₁ + 1) ──► reply y₂ ──► return y₂
```
-/

namespace SystemAlgebra.Tests.DirectCalls

/-- A reply-dependent two-query call. -/
def chainCall (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) :=
  match rs with
  | [] => .inr ⟨(), u.2⟩
  | [r] => .inr ⟨(), r.2 + 1⟩
  | _ :: r :: _ => .inl r.2

/-- The same call with no inside work. -/
def zeroCall (u : Σ _ : Unit, Nat) (_ : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) := .inl u.2

/-- A call that returns immediately has exact cost zero. -/
example : IsResponsiveDDC 0 (canon (callRule (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    zeroCall)) := by
  apply callRule_isResponsiveDDC (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    zeroCall (fun _ => 0) 0
  · intro u rs h
    simp [zeroCall] at h
  · intro u
    rfl

/-- The dependent second query fits the exact two-query phase contract on every reply list. -/
lemma chainCall_phase (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    (chainCall u rs).isRight = true ↔ rs.length < 2 := by
  cases rs with
  | nil => simp [chainCall]
  | cons r rs =>
    cases rs with
    | nil => simp [chainCall]
    | cons s rs => simp [chainCall]

/-- The arbitrary-reply responsiveness proof uses only the phase contract. -/
example : IsResponsiveDDC 2 (canon (callRule (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    chainCall)) := by
  apply callRule_isResponsiveDDC (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    chainCall (fun _ => 2) 2
  · intro u rs h
    exact (chainCall_phase u rs).mp h
  · intro u
    rfl

/-- Against the successor function, the completed schedule is fixed for each outside input. -/
def chainQueries (u : Σ _ : Unit, Nat) : List (Σ _ : Unit, Nat) :=
  [⟨(), u.2⟩, ⟨(), u.2 + 2⟩]

/-- The second query depends on the first reply, not on a preselected query sequence. -/
lemma chainCall_query (u : Σ _ : Unit, Nat) (n : Nat)
    (hn : n < (chainQueries u).length) :
    chainCall u (((chainQueries u).take n).map fun x => ⟨x.1, x.2 + 1⟩) =
      .inr (chainQueries u)[n] := by
  have h : n = 0 ∨ n = 1 := by
    simp only [chainQueries, List.length_cons, List.length_nil] at hn
    omega
  rcases h with rfl | rfl <;> simp [chainCall, chainQueries, Nat.add_assoc]

/-- The second reply determines the outside result. -/
lemma chainCall_return (u : Σ _ : Unit, Nat) :
    chainCall u ((chainQueries u).map fun x => ⟨x.1, x.2 + 1⟩) =
      .inl (u.2 + 3) := by
  simp [chainCall, chainQueries, Nat.add_assoc]

/-- Exact phase data gives equality for a completed call. -/
example (u : Σ _ : Unit, Nat) :
    (insideQueries ((callTranscript (O := Unit) (J := Unit)
      (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
      u ((chainQueries u).map fun x =>
      (x, ⟨x.1, x.2 + 1⟩)) ⟨u.1, u.2 + 3⟩).map Prod.snd)).length = 2 := by
  apply callRule_completed_exact_length chainCall (fun _ => 2) chainCall_phase u _ _
  · intro n hn
    simpa only [List.length_map, List.map_take, List.map_map, List.getElem_map,
      Function.comp_def] using chainCall_query u n (by simpa only [List.length_map] using hn)
  · simpa only [List.map_map, Function.comp_def] using chainCall_return u

/-- One outside invocation reserves both inside queries; a second outside invocation is
excluded by the exact outside domain. -/
example : IsDDCFrom
    (fun qs : List (Σ _ : Unit, Nat) => qs ≠ [] ∧ qs.length ≤ 2)
    (fun us : List (Σ _ : Unit, Nat) => us ≠ [] ∧ us.length ≤ 1) 2
    (callConverter (O := Unit) (J := Unit)
      (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
      chainCall (fun us => us ≠ [] ∧ us.length ≤ 1)) := by
  simpa only [and_true] using
    (callConverter_isDDCFrom (O := Unit) (J := Unit)
      (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
      chainCall (fun _ => 2) 2 2
      (fun us => us ≠ [] ∧ us.length ≤ 1) (fun _ => True)
      (by intro u rs h; exact (chainCall_phase u rs).mp h)
      (by intro u; rfl)
      (by intro p h hp hne hd; exact ⟨hne, hp.length_le.trans hd.2⟩)
      (by
        intro us hu
        cases us with
        | nil => simp
        | cons u us =>
          cases us with
          | nil => simp
          | cons v us => simp at hu)
      (by intro T hr hn; trivial))

/-- A reply at a different inside label is rejected even when its value has the right type. -/
example : ¬ converterAdmits
    ([(⟨⟨none, ()⟩, 0⟩, ⟨⟨some (), false⟩, 0⟩)] :
      List ((Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
        (Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l)))
    (⟨⟨some (), true⟩, 0⟩ :
      Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l) := by
  simp [converterAdmits, admitAfter]

end SystemAlgebra.Tests.DirectCalls

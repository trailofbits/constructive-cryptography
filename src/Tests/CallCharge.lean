module

public import RandomSystems.Converter.CallCharge

/-!
# Payload charges on a single inside port

An outside request carrying zero returns immediately. Requests carrying two and five each
forward their payload once. The last request is pending when the transcript ends; the issued
work is already seven. The bound applies to the domain-restricted canonical converter.
-/

@[expose] public section

namespace SystemAlgebra.Tests.CallCharge

/-- On input `n`, return zero if `n = 0`; otherwise issue `n` once, then return zero. -/
def forward (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) :=
  match u.2, rs with
  | n + 1, [] => .inr ⟨(), n + 1⟩
  | _, _ => .inl 0

/-- The wire values are natural numbers at the sole inside and outside ports. -/
abbrev Wire := Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l

/-- The zero input returns, the second invocation finishes, and the last inside query is pending. -/
def history : List (Wire × Wire) :=
  [] ++ [(⟨⟨none, ()⟩, 0⟩, ⟨⟨none, ()⟩, 0⟩)] ++
    [(⟨⟨none, ()⟩, 2⟩, ⟨⟨some (), ()⟩, 2⟩)] ++
    [(⟨⟨some (), ()⟩, 9⟩, ⟨⟨none, ()⟩, 0⟩)] ++
    [(⟨⟨none, ()⟩, 5⟩, ⟨⟨some (), ()⟩, 5⟩)]

/-- Each issued request spends the single slot reserved at the start of its invocation. -/
lemma forward_charge (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) (x : Σ _ : Unit, Nat)
    (issued : forward u rs = .inr x) :
    x.2 + ([u.2].drop (rs.length + 1)).sum ≤ ([u.2].drop rs.length).sum := by
  rcases u with ⟨o, _ | n⟩ <;> cases rs <;>
    simp only [forward, reduceCtorEq, Sum.inr.injEq] at issued
  subst x
  simp only [List.length_nil, zero_add, List.drop_one, List.tail_cons, List.sum_nil, add_zero,
    List.drop_zero, List.sum_cons, le_refl]

/-- The canonical converter admits each input of `history` at its turn. -/
lemma history_replies : Replies (callConverter (U := fun _ : Unit => Nat) (V := fun _ => Nat)
    (X := fun _ : Unit => Nat) (Y := fun _ => Nat) forward (fun _ => True))
    (history.map Prod.fst) (history.map Prod.snd) := by
  apply (replies_filterDom_iff (fun _ _ _ => Or.inr trivial) _ (fun _ => Or.inr trivial)).mpr
  apply (replies_canon_iff (callRule (U := fun _ : Unit => Nat) (V := fun _ => Nat)
    (X := fun _ : Unit => Nat) (Y := fun _ => Nat) forward) Part.not_none_dom history).mpr
  constructor
  · -- Each inside reply follows an inside query; the other inputs begin outside invocations.
    simp only [history, admitted_snoc, admitted_nil, true_and]
    exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  · -- At the four prefixes the outputs are return 0, request 2, return 0, request 5.
    refine ⟨rfl, fun k hk _ => ?_⟩
    change k < 4 at hk
    rcases k with _ | _ | _ | _ | k <;> first | rfl | omega

/-- Only the two issued requests are charged. Their payloads differ at the same port. -/
lemma history_payloads :
    (insideQueries (history.map Prod.snd)).map (fun x => x.2) = [2, 5] ∧
    (outsideInputs (history.map Prod.fst)).map (fun u => u.2) = [0, 2, 5] := by
  simp only [insideQueries, history, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, splitIn, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne,
    restrict, ↓reduceDIte, outsideInputs, restrict_cons_self, and_self]

/-- The pending five-unit request and the completed two-unit request use their full reservations. -/
example : ((insideQueries (history.map Prod.snd)).map (fun x => x.2)).sum ≤ 7 := by
  have charged := callConverter_query_charge_le forward (fun x => x.2) (fun u => [u.2])
    forward_charge (fun _ => True) history history_replies
  simpa only [List.sum_cons, List.sum_nil, add_zero, history_payloads.2] using charged

end SystemAlgebra.Tests.CallCharge

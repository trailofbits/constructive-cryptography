import RandomSystems.Typed.CallRuleFunctional

/-!
# Direct-call examples

Call rules with one outside port `o` and one inside port `j`, on the outside query `u` and the
inside replies `r₁, r₂, …` of the current invocation:

* `zeroCall u rs = inl u`: return at once;
* `chainCall u [] = inr u`, `chainCall u [r₁] = inr (r₁ + 1)`,
  `chainCall u (r₁ :: r₂ :: _) = inl r₂`, on `Nat`;
* `toggleCall`: the same on `Bool`, with second query `!r₁`.

Against the successor, `chainCall` computes `u + 3`; its second query depends on the first reply:

```text
            o(u)   ┌───────────┐   j(u), j(u + 2)       ┌───────────┐
  ────────────────►│           ├───────────────────────►│           │
                   │ chainCall │                        │ x ↦ x + 1 │
  ◄────────────────┤           │◄───────────────────────┤           │
        o ⇒ u + 3  └───────────┘   j ⇒ u + 1, j ⇒ u + 3 └───────────┘
```

The examples check responsiveness, the exact length under the biconditional phase condition and
its failure under the loose bound `3`, the charge of a pending query, rejection of a reply at
the wrong inside label, the domain certificates, the typed equation
`toggleCall • ofFunction id = ofFunction (! ·)`, and the weighted count of `zeroCall`.
-/

namespace SystemAlgebra.Tests.DirectCalls

/-- A reply-dependent two-query call: query `u`, then `r₁ + 1`, and return `r₂`. -/
def chainCall (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) :=
  match rs with
  | [] => .inr ⟨(), u.2⟩
  | [r] => .inr ⟨(), r.2 + 1⟩
  | _ :: r :: _ => .inl r.2

/-- A call with no inside queries: return `u` at once. -/
def zeroCall (u : Σ _ : Unit, Nat) (_ : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) := .inl u.2

/-- The immediate-return rule is responsive with bound `0`. -/
example : IsResponsiveDDC 0 (canon (callRule (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    zeroCall)) := by
  apply callRule_isResponsiveDDC (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    zeroCall (fun _ => 0) 0
  · intro u rs h
    simp only [zeroCall, Sum.isRight_inl, Bool.false_eq_true] at h
  · intro u
    rfl

/-- The biconditional phase condition with cost `2`, on every reply list. -/
lemma chainCall_phase (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    (chainCall u rs).isRight = true ↔ rs.length < 2 := by
  cases rs with
  | nil => simp only [chainCall, Sum.isRight_inr, List.length_nil, Nat.zero_lt_succ]
  | cons r rs =>
    cases rs with
    | nil => simp only [chainCall, Sum.isRight_inr, List.length_cons, List.length_nil,
        Nat.lt_add_one]
    | cons s rs =>
      simp only [chainCall, Sum.isRight_inl, Bool.false_eq_true, List.length_cons, false_iff]
      omega

/-- Responsiveness with bound `2` follows from the phase condition over arbitrary replies. -/
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

/-- The schedule of `chainCall` against the successor: `x₁ = u`, `x₂ = (u + 1) + 1`. -/
def chainQueries (u : Σ _ : Unit, Nat) : List (Σ _ : Unit, Nat) :=
  [⟨(), u.2⟩, ⟨(), u.2 + 2⟩]

/-- `chainCall` follows its schedule; the second query is computed from the first reply. -/
lemma chainCall_query (u : Σ _ : Unit, Nat) (n : Nat)
    (hn : n < (chainQueries u).length) :
    chainCall u (((chainQueries u).take n).map fun x => ⟨x.1, x.2 + 1⟩) =
      .inr (chainQueries u)[n] := by
  have h : n = 0 ∨ n = 1 := by
    simp only [chainQueries, List.length_cons, List.length_nil] at hn
    omega
  rcases h with rfl | rfl <;>
    simp only [chainCall, chainQueries, List.take_succ_cons, List.take_zero, List.map_cons,
      List.map_nil, Nat.add_assoc, Nat.reduceAdd, List.getElem_cons_succ, List.getElem_cons_zero]

/-- After the replies `u + 1` and `u + 3`, `chainCall` returns the second one. -/
lemma chainCall_return (u : Σ _ : Unit, Nat) :
    chainCall u ((chainQueries u).map fun x => ⟨x.1, x.2 + 1⟩) =
      .inl (u.2 + 3) := by
  simp only [chainCall, chainQueries, List.map_cons, Nat.add_assoc, Nat.reduceAdd, List.map_nil]

/-- Under the biconditional phase condition, the completed call has exactly two inside queries. -/
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
        | nil => simp only [List.map_nil, List.sum_nil, zero_le]
        | cons u us =>
          cases us with
          | nil => simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              add_zero, le_refl]
          | cons v us =>
            have := hu.2
            simp only [List.length_cons] at this
            omega)
      (by intro T hr hn; trivial))

/-- A reply at a different inside label is rejected even when its value has the right type. -/
example : ¬ converterAdmits
    ([(⟨⟨none, ()⟩, 0⟩, ⟨⟨some (), false⟩, 0⟩)] :
      List ((Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
        (Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l)))
    (⟨⟨some (), true⟩, 0⟩ :
      Σ l : Two Unit Bool, twoFam (fun _ => Nat) (fun _ => Nat) l) := by
  simp only [converterAdmits, admitAfter, List.getLast?_singleton, Option.map_some,
    Sigma.mk.injEq, heq_eq_eq, Bool.true_eq_false, and_false, not_false_eq_true]

/-- The two-query rule can stop before its advertised upper bound `3`; an upper phase bound
alone therefore does not give exact cost. -/
example : (∀ u rs, (chainCall u rs).isRight = true → rs.length < 3) ∧
    ¬ (∀ u rs, (chainCall u rs).isRight = true ↔ rs.length < 3) := by
  constructor
  · intro u rs h
    have := (chainCall_phase u rs).mp h
    omega
  · intro h
    have hm := (h ⟨(), 0⟩ [⟨(), 0⟩, ⟨(), 0⟩]).mpr (by
      simp only [List.length_cons, List.length_nil]
      omega)
    simp only [chainCall, Sum.isRight_inl, Bool.false_eq_true] at hm

/-- The responsive constructor accepts the loose upper bound `3` for a two-query call. -/
example : IsResponsiveDDC 3
    (canon (callRule (V := fun _ => Nat) (Y := fun _ => Nat) chainCall)) := by
  apply callRule_isResponsiveDDC (O := Unit) (J := Unit)
    (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat)
    chainCall (fun _ => 3) 3
  · intro u rs h
    have := (chainCall_phase u rs).mp h
    omega
  · intro u
    rfl

/-- A pending query is counted: after `u` alone, the transcript has one inside query and no
inside reply. -/
example (u : Nat) :
    let T : List ((Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
      (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l)) :=
      [(⟨⟨none, ()⟩, u⟩, ⟨⟨some (), ()⟩, u⟩)]
    Replies (callRule chainCall) (T.map Prod.fst) (T.map Prod.snd) ∧
      (insideQueries (T.map Prod.snd)).length = 1 := by
  dsimp only
  constructor
  · simp only [List.map_cons, List.map_nil]
    change Replies _ ([] ++ [_]) ([] ++ [_])
    exact replies_snoc.mpr ⟨replies_nil _, rfl⟩
  · simp only [List.map_cons, List.map_nil, insideQueries_inside, List.length_singleton]

/-- One outside Boolean invocation, or up to two inside Boolean queries, at a single label:
`D_q = {h | h ≠ [] ∧ |h| ≤ q}`. -/
abbrev boolInterface (q : Nat) : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) q

/-- Query `u`, then `!r₁`, and return `r₂`. Against the identity the replies are `u` and `!u`,
so the call computes `!u`. -/
def toggleCall (u : Σ _ : Unit, Bool) (rs : List (Σ _ : Unit, Bool)) :
    Bool ⊕ (Σ _ : Unit, Bool) :=
  match rs with
  | [] => .inr u
  | [r] => .inr ⟨(), !r.2⟩
  | _ :: r :: _ => .inl r.2

/-- The biconditional phase condition with cost `2`, on every reply list. -/
lemma toggleCall_phase (u : Σ _ : Unit, Bool) (rs : List (Σ _ : Unit, Bool)) :
    (toggleCall u rs).isRight = true ↔ rs.length < 2 := by
  cases rs with
  | nil => simp only [toggleCall, Sum.isRight_inr, List.length_nil, Nat.zero_lt_succ]
  | cons r rs =>
    cases rs with
    | nil => simp only [toggleCall, Sum.isRight_inr, List.length_cons, List.length_nil,
        Nat.lt_add_one]
    | cons s rs =>
      simp only [toggleCall, Sum.isRight_inl, Bool.false_eq_true, List.length_cons, false_iff]
      omega

/-- A single outside invocation reserves the two inside queries, including a pending query. -/
lemma toggleCall_isDDCFrom : IsDDCFrom (boolInterface 2).domain (boolInterface 1).domain 2
    (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 1).domain) := by
  simpa only [boolInterface, Interface.queryBudget, and_true] using
    (callConverter_isDDCFrom (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall (fun _ => 2) 2 2
      (boolInterface 1).domain (fun _ => True)
      (by intro u rs h; exact (toggleCall_phase u rs).mp h)
      (by intro u; rfl) (boolInterface 1).nonempty_prefix.2
      (by
        intro us hu
        cases us with
        | nil => simp only [List.map_nil, List.sum_nil, Nat.zero_le]
        | cons u us =>
          cases us with
          | nil => simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
              Nat.add_zero, le_refl]
          | cons v us =>
            have := hu.2
            simp only [List.length_cons] at this
            omega)
      (by intro T hr hn; trivial))

/-- The dependent two-query converter attached to the identity oracle is the negation oracle:
`toggle • ofFunction id = ofFunction (! ·)` on the one-query outside domain. -/
example : TypedConverter.ofDDC (A := boolInterface 1) (B := boolInterface 2)
    (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 1).domain) toggleCall_isDDCFrom •
      TypedSystem.ofFunction (A := boolInterface 2) (fun _ b => b) =
        TypedSystem.ofFunction (A := boolInterface 1) (fun _ b => !b) := by
  apply TypedConverter.ofDDC_callConverter_smul_ofFunction (A := boolInterface 1)
    (B := boolInterface 2) toggleCall toggleCall_isDDCFrom
    (fun _ b => b) (fun _ b => !b) (fun u => [u, ⟨(), !u.2⟩])
  · intro u n hn
    have he : n = 0 ∨ n = 1 := by
      simp only [List.length_cons, List.length_nil] at hn
      omega
    rcases he with rfl | rfl <;> simp only [List.take_zero, List.map_nil, toggleCall,
      List.getElem_cons_zero, List.take_succ_cons, List.map_cons, List.getElem_cons_succ,
      Sigma.eta]
  · intro u
    rfl

/-- An admissible history of the immediate-return rule contains no inside reply in its
current invocation: `currentCall h.reverse [] = some (u, [])`. -/
lemma zeroCall_admissible_replies_empty
    (h : List (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l))
    (ha : Admissible (callRule (V := fun _ => Nat) (Y := fun _ => Nat) zeroCall) h)
    (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat))
    (hc : currentCall h.reverse [] = some (u, rs)) : rs = [] := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · cases hc
  · rw [List.concat_eq_append] at ha hc
    obtain ⟨_, _, hx⟩ := admissible_snoc.mp ha
    -- A last outside input starts an invocation without replies; a last inside reply is not
    -- admitted, since the rule never issues an inside query.
    rcases x with ⟨⟨_ | ⟨⟩, i⟩, x⟩
    · simp only [List.reverse_append, List.reverse_singleton, List.singleton_append,
        currentCall, Option.some.injEq, Prod.mk.injEq] at hc
      exact hc.2.symm
    · cases he : currentCall h.reverse [] with
      | none => simp only [Admits, admitAfter, replyLabel, callRule, he, Part.not_none_dom,
          ↓reduceDIte, reduceCtorEq] at hx
      | some ur => simp only [Admits, admitAfter, replyLabel, callRule, he, zeroCall,
          Part.some_dom, ↓reduceDIte, Part.get_some, reduceCtorEq] at hx

/-- Charge each inside query seven units. The immediate-return rule spends zero on every
admitted transcript; inadmissible inside replies need no budget. -/
example (T : List ((Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
    (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l)))
    (hr : Replies (callRule (V := fun _ => Nat) (Y := fun _ => Nat) zeroCall)
      (T.map Prod.fst) (T.map Prod.snd)) (ha : Admitted converterAdmits T) :
    ((insideQueries (T.map Prod.snd)).map fun _ => 7).sum ≤
      ((outsideInputs (T.map Prod.fst)).map fun _ => 0).sum := by
  apply currentCall_query_charge (callRule (V := fun _ => Nat) (Y := fun _ => Nat) zeroCall)
    (fun _ => 7) (fun _ => 0) ?_ ?_ T hr ha
  · intro h hc
    simp only [callRule, hc]
  -- On an admissible history the invocation has no replies and its output is a return.
  · intro h u rs y hadm hc hy
    have hrs := zeroCall_admissible_replies_empty h hadm u rs hc
    subst rs
    simp only [callRule, hc, zeroCall, Part.mem_some_iff] at hy
    subst y
    simp only [List.map_nil, List.sum_nil, insideQueries_outside, Nat.zero_add, le_refl]

end SystemAlgebra.Tests.DirectCalls

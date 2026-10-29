import Tests.DirectCalls
import RandomSystems.Converter.SerialAccounting

/-!
# Input-dependent serial costs and interrupted calls

One outside port `o` and one inside port `j`, all alphabets `Nat`. The call rule `variableCall`
returns `0` at once on `o(0)`, at cost `0`; on `o(u)` with `u ≠ 0` it runs `chainCall`, two
dependent queries `j(u)`, `j(r₁ + 1)` and the return `o ⇒ r₂`, at cost `2`.

The transcript `interrupted` stops after the first inside query:

```text
        o(7)  ┌──────────────┐  j(7)
  ───────────►│ variableCall ├───────►   work 1, reserved variableCost 7 = 2,
              └──────────────┘           no reply j ⇒ _, no return o ⇒ _
```

The direct-call count charges the pending query, and `comp_callConverter_query_count_le`
carries the same inequality to a composite with an arbitrary certified outer converter. The
immediate return `o(0) ↦ o ⇒ 0` issues no query and reserves `variableCost ⟨(), 0⟩ = 0`.

Two `toggleCall` converters in series, with queries flowing `D₁ → D₂ → D₄`, charge `3` per
exposed query and reserve `6` per intermediate query: `∑_{j(z) ∈ insideQueries T} 3 ≤ 12 · n`
on `n` outside inputs.
-/

namespace SystemAlgebra.Tests.SerialAccounting

open DirectCalls

/-- **An input-dependent call**: `variableCall ⟨(), 0⟩ rs = inl 0`, an immediate return; for
`u ≠ 0`, `variableCall u rs = chainCall u rs`: query `u`, then `r₁ + 1`, and return `r₂`. -/
def variableCall (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    Nat ⊕ (Σ _ : Unit, Nat) :=
  if u.2 = 0 then .inl 0 else chainCall u rs

/-- The reserved cost of `variableCall`, its number of inside queries: `variableCost ⟨(), u⟩`
is `0` if `u = 0` and `2` otherwise. The port is the same; only the value differs. -/
def variableCost (u : Σ _ : Unit, Nat) : Nat := if u.2 = 0 then 0 else 2

/-- The one-way phase condition `(variableCall u rs).isRight → rs.length < variableCost u`, on
every reply list `rs`. -/
lemma variableCall_phase (u : Σ _ : Unit, Nat) (rs : List (Σ _ : Unit, Nat)) :
    (variableCall u rs).isRight = true → rs.length < variableCost u := by
  by_cases hz : u.2 = 0
  -- `o(0)` returns at once, so it never issues an inside query.
  · simp only [variableCall, hz, ↓reduceIte, Sum.isRight_inl, Bool.false_eq_true,
    IsEmpty.forall_iff]
  -- `u ≠ 0`: the phase condition of `chainCall` with cost `2`.
  · simpa only [variableCall, hz, ↓reduceIte, variableCost, Order.lt_two_iff] using
      (chainCall_phase u rs).mp

/-- The raw direct call rule of `variableCall`, outside and inside ports `()`, all alphabets
`Nat`: on a history with current invocation `(u, rs)` it outputs `o ⇒ v` if
`variableCall u rs = inl v` and `j(x)` if `variableCall u rs = inr x`. -/
abbrev natRule := callRule (O := Unit) (J := Unit)
  (U := fun _ => Nat) (V := fun _ => Nat) (X := fun _ => Nat) (Y := fun _ => Nat) variableCall

/-- The one-step transcript `o(7) ↦ j(7)`: the outside input `7` at label `⟨none, ()⟩`, answered
by the inside query `7` at label `⟨some (), ()⟩`. No inside reply and no return follow. -/
def interrupted : List
    ((Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
      (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l)) :=
  [(⟨⟨none, ()⟩, 7⟩, ⟨⟨some (), ()⟩, 7⟩)]

/-- Stopping immediately after an inside query is a valid canonical transcript. -/
lemma interrupted_replies : Replies (canon natRule)
    (interrupted.map Prod.fst) (interrupted.map Prod.snd) := by
  -- A canonical transcript is an admissible transcript of the raw rule.
  apply (replies_canon_iff natRule Part.not_none_dom interrupted).mpr
  constructor
  -- Admissible: an inside query may follow an outside input.
  · change Admitted converterAdmits ([] ++ interrupted)
    exact admitted_snoc.mpr ⟨admitted_nil _, by simp only [converterAdmits, admitAfter,
      List.getLast?_nil, Option.map_none]⟩
  -- `natRule [o(7)] = j(7)`, since `variableCall ⟨(), 7⟩ [] = chainCall ⟨(), 7⟩ [] = inr 7`.
  · change Replies natRule ([] ++ [⟨⟨none, ()⟩, 7⟩]) ([] ++ [⟨⟨some (), ()⟩, 7⟩])
    exact replies_snoc.mpr ⟨replies_nil _, rfl⟩

/-- Work `1` against the reserved `variableCost ⟨(), 7⟩ = 2`: the pending call is charged
already, and an exact count `work = reserved cost` would be false. -/
example : (insideQueries (interrupted.map Prod.snd)).length = 1 ∧
    ((outsideInputs (interrupted.map Prod.fst)).map variableCost).sum = 2 := by
  simp only [insideQueries, interrupted, List.map_cons, List.map_nil, splitIn, restrict_cons_self,
    restrict_nil, List.length_cons, List.length_nil, zero_add, outsideInputs, variableCost,
    OfNat.ofNat_ne_zero, ↓reduceIte, List.sum_cons, List.sum_nil, add_zero, and_self]

/-- The arbitrary-reply accounting lemma counts the pending query: `1 ≤ 2`. -/
example : (insideQueries (interrupted.map Prod.snd)).length ≤
    ((outsideInputs (interrupted.map Prod.fst)).map variableCost).sum := by
  -- `callRule_query_count` on the raw rule; a canonical transcript is one of the raw rule.
  apply callRule_query_count variableCall variableCost variableCall_phase
  exact interrupted_replies.mono fun _ _ hy => canon_mem hy

/-- With `callConverter variableCall F` inside an arbitrary certified outer converter `β`, the
exposed queries of a composite transcript `T` are at most `∑ variableCost` over the actual
intermediate queries of an outer transcript `Tb` with the same outside inputs. -/
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

/-- On outside domain `D_q = (boolInterface q).domain`, `toggleCall` makes at most `2q` inside
queries, with consecutive bound `2`: `IsDDCFrom D_{2q} D_q 2`. Every invocation reserves its two
dependent calls. -/
lemma toggleCall_isDDCFrom_queryBudget (q : ℕ) :
    IsDDCFrom (boolInterface (2 * q)).domain (boolInterface q).domain 2
      (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
        (boolInterface q).domain) := by
  -- `callConverter_isDDCFrom` with cost `2`, bound `2` and work `2q`: at most `q` inputs in
  -- `D_q` cost `2` each; `P` is trivial.
  simpa only [boolInterface, Interface.queryBudget, and_true] using
    (callConverter_isDDCFrom (V := fun _ => Bool) (Y := fun _ => Bool)
      toggleCall (fun _ => 2) 2 (2 * q) (boolInterface q).domain (fun _ => True)
      (fun u rs h => (toggleCall_phase u rs).mp h) (fun _ => le_rfl)
      (boolInterface q).nonempty_prefix.2
      (by
        intro us hu
        simpa only [List.map_const', List.sum_replicate, smul_eq_mul, Nat.mul_comm] using
          Nat.mul_le_mul_left 2 hu.2)
      (by intro T hr hn; trivial))

/-- Two concrete `toggleCall` converters in series: the outer one from `D₂` to `D₁`, the inner
one from `D₄` to `D₂`. Charging `3` per exposed query and reserving `6` per intermediate query,
with `Tb` the outer component transcript,

`∑_{j(z) ∈ insideQueries T} 3 ≤ 6 · |insideQueries Tb| ≤ 12 · |outsideInputs T|`,

including incomplete calls: each outside input yields `≤ 2` intermediate queries, each of
those `≤ 2` exposed ones. -/
example {T : List
    ((Σ l : Two Unit Unit, twoFam (fun _ => Bool) (fun _ => Bool) l) ×
      (Σ l : Two Unit Unit, twoFam (fun _ => Bool) (fun _ => Bool) l))}
    (hr : Replies (trim (serialM
      (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall (boolInterface 1).domain)
      (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
        (boolInterface 2).domain)))
      (T.map Prod.fst) (T.map Prod.snd)) :
    ((insideQueries (T.map Prod.snd)).map (fun _ => 3)).sum ≤
      12 * (outsideInputs (T.map Prod.fst)).length := by
  apply (toggleCall_isDDCFrom_queryBudget 1).comp_query_charge_le_budget
    (toggleCall_isDDCFrom_queryBudget 2) (fun _ => 3) (fun _ => 6)
    (fun us => 12 * us.length) ?_ ?_ hr
  · -- Inner calls: at most two exposed queries per intermediate invocation, each costing 3.
    intro Ta ha
    have hc := callConverter_query_count toggleCall (fun _ => 2)
      (fun u rs h => (toggleCall_phase u rs).mp h) (boolInterface 2).domain Ta ha
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc ⊢
    omega
  · -- Outer calls: at most two intermediate queries per outside invocation, each reserving 6.
    intro Tb hb
    have hc := callConverter_query_count toggleCall (fun _ => 2)
      (fun u rs h => (toggleCall_phase u rs).mp h) (boolInterface 1).domain Tb hb
    simp only [List.map_const', List.sum_replicate, smul_eq_mul] at hc ⊢
    omega

/-- At input `0`, `variableCall` returns `0` immediately: the canonical transcript
`o(0) ↦ o ⇒ 0` has no inside query and reserves `variableCost ⟨(), 0⟩ = 0`, unlike the
interrupted input-`7` call. -/
example :
    let T : List
      ((Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l) ×
        (Σ l : Two Unit Unit, twoFam (fun _ => Nat) (fun _ => Nat) l)) :=
      [(⟨⟨none, ()⟩, 0⟩, ⟨⟨none, ()⟩, 0⟩)]
    Replies (canon natRule) (T.map Prod.fst) (T.map Prod.snd) ∧
      (insideQueries (T.map Prod.snd)).length = 0 ∧
        ((outsideInputs (T.map Prod.fst)).map variableCost).sum = 0 := by
  dsimp only
  constructor
  -- A canonical transcript is an admissible transcript of the raw rule.
  · apply (replies_canon_iff natRule Part.not_none_dom _).mpr
    constructor
    -- Admissible: an outside input opens the empty history.
    · exact admitted_snoc.mpr ⟨admitted_nil _, by simp only [converterAdmits, admitAfter,
      List.getLast?_nil, Option.map_none]⟩
    -- `natRule [o(0)] = o ⇒ 0`, since `variableCall ⟨(), 0⟩ [] = inl 0`.
    · change Replies natRule ([] ++ [⟨⟨none, ()⟩, 0⟩]) ([] ++ [⟨⟨none, ()⟩, 0⟩])
      exact replies_snoc.mpr ⟨replies_nil _, rfl⟩
  -- The return lies on the outside port, so `insideQueries = []`; `variableCost ⟨(), 0⟩ = 0`.
  · simp only [insideQueries, List.map_cons, List.map_nil, splitIn, ne_eq, reduceCtorEq,
    not_false_eq_true, restrict_cons_ne, restrict_nil, List.length_nil, outsideInputs,
    restrict_cons_self, variableCost, ↓reduceIte, List.sum_cons, List.sum_nil, add_zero, and_self]

#print axioms SystemAlgebra.IsDDCFrom.comp_query_charge_le
#print axioms SystemAlgebra.IsDDCFrom.comp_query_charge_le_budget
#print axioms SystemAlgebra.IsDDCFrom.comp_callConverter_query_count_le

end SystemAlgebra.Tests.SerialAccounting

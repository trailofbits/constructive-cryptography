module

public import RandomSystems.Converter.ForwardingProgram
public import RandomSystems.Typed.DSL.Converters

/-!
# Recording and stateful rejection

`recordingGuard record guard hsub` retains a list of recorded keys. On `i(x)`, `guard` either
supplies a reply directly or forwards `i(x)` once. After forwarding, `record i x y` optionally
inserts a key; the inside reply `y` is returned unchanged.

```text
              guard(keys, i(x))
i(x) ───────► some y ──────────────────────► y
              none  ──► inside: i(x) ⇒ y ──► insert record(i,x,y) ──► y
```

`recordingGuardProgram_cost` gives zero calls on rejection and one on forwarding.
The domain certificate is `DDC.ofProgramOn_isDDCFrom_of_forwarding`: `hsub` admits
nonempty subsequences of admitted histories. `recordingGuard_smul_ofAutomaton` and
`recordingGuardProgram_combine` identify the attached system's state/reply rule, preserving
one initial draw of the inside state.
-/

@[expose] public section

open scoped List

namespace SystemAlgebra.TypedConverter

open DSL

variable
  -- `A` fixes the ports, alphabets and domain; `K` carries the keys recorded after replies.
  {A : Interface} {K : Type}
  -- Recording compares keys using the caller's selected equality test.
  [DecidableEq K]
  -- `record i x y = some k` inserts `k`; `none` records nothing for that exchange.
  (record : ∀ i, A.X i → A.Y i → Option K)
  -- `guard keys i x = some y` replies `y` without a call; `none` forwards `i(x)`.
  (guard : List K → ∀ i, A.X i → Option (A.Y i))

/-- The program on retained keys: direct reply on `some y`, or one call followed by optional
recording on `none`. -/
noncomputable def recordingGuardProgram :
    Program (List K) A.I A.I A.X A.Y A.X A.Y :=
  fun keys i x => match guard keys i x with
  | some y => returnProg (keys, y)
  | none => callProg i x fun y =>
      returnProg (Option.elim (record i x y) keys (fun k => keys.insert k), y)

/-- Each issued call is the unchanged current input, before any inside exchange. -/
lemma recordingGuardProgram_calls
    -- `keys` is the current record; `i(x)` is the outside query.
    (keys : List K) (i : A.I) (x : A.X i) (h) (q)
    -- `hc` admits the invocation exchanges `h`; `hq` identifies its pending query.
    (hc : (recordingGuardProgram record guard).Consistent keys i x h)
    (hq : recordingGuardProgram record guard keys i x h = .inr q) :
    h = [] ∧ q = ⟨i, x⟩ := by
  classical
  cases hg : guard keys i x with
  | some y =>
    -- A direct reply cannot be a pending query.
    simp only [recordingGuardProgram, hg, returnProg] at hq
    cases hq
  | none =>
    -- The sole query precedes its reply; after that reply the program returns.
    change Program.ExchangesOf (recordingGuardProgram record guard keys i x) h at hc
    simp only [recordingGuardProgram, hg] at hc hq
    cases h with
    | nil => exact ⟨rfl, (Sum.inr.inj hq).symm⟩
    | cons z h =>
      obtain ⟨y, rfl, he, _⟩ := exchangesOf_callProg hc
      rw [he] at hq
      cases hq

/-- Start with no recorded keys and follow `recordingGuardProgram` on exactly `A.domain`. -/
noncomputable def recordingGuard
    -- `hsub` admits each nonempty subsequence of an admitted outside history.
    (hsub : ∀ {xs ys}, xs <+ ys → xs ≠ [] → A.domain ys → A.domain xs) :
    TypedConverter A A :=
  ofDDC (DDC.ofProgramOn [] (recordingGuardProgram record guard) A.domain)
    (DDC.ofProgramOn_isDDCFrom_of_forwarding (recordingGuardProgram_calls record guard)
      A.nonempty_prefix.2 hsub)

/-- At most one inside call is made per outside input. -/
lemma recordingGuardProgram_bounded :
    (recordingGuardProgram record guard).Bounded 1 :=
  Program.bounded_one_of_history_eq_nil fun s j x h q hc hq =>
    (recordingGuardProgram_calls record guard s j x h q hc hq).1

/-- A supplied rejection reply leaves the record unchanged and issues no query. -/
lemma recordingGuardProgram_reject
    -- `keys` is the current record; `i(x)` is the outside query.
    (keys : List K) (i : A.I) (x : A.X i) (y : A.Y i)
    -- `hg` selects reply `y`; `h` is any current invocation exchange history.
    (hg : guard keys i x = some y) (h) :
    recordingGuardProgram record guard keys i x h = .inl (keys, y) := by
  simp only [recordingGuardProgram, hg, returnProg]

/-- An input with `guard = none` is forwarded once at its original port. -/
lemma recordingGuardProgram_forward
    -- `keys` is the current record; `i(x)` is the outside query.
    (keys : List K) (i : A.I) (x : A.X i)
    -- `hg` selects forwarding for this input.
    (hg : guard keys i x = none) :
    recordingGuardProgram record guard keys i x [] = .inr ⟨i, x⟩ := by
  simp only [recordingGuardProgram, hg, callProg]

/-- A forwarded reply is returned unchanged; its selected key is inserted into the record. -/
lemma recordingGuardProgram_reply
    -- `keys` is the current record; `i(x)` is the outside query.
    (keys : List K) (i : A.I) (x : A.X i) (y : A.Y i)
    -- `y` is the inside reply; `hg` selected the forwarded call.
    (hg : guard keys i x = none) :
    recordingGuardProgram record guard keys i x [(⟨i, x⟩, ⟨i, y⟩)] =
      .inl (Option.elim (record i x y) keys (fun k => keys.insert k), y) := by
  simp only [recordingGuardProgram, hg, callProg, ↓reduceDIte, returnProg]

/-- The exact inside call count is zero for a supplied reply and one for forwarding. -/
lemma recordingGuardProgram_cost
    -- `keys` is the current record; `i(x)` is the outside query.
    (keys : List K) (i : A.I) (x : A.X i) :
    Program.CallCost ((guard keys i x).elim 1 (fun _ => 0))
      (recordingGuardProgram record guard keys i x) := by
  classical
  cases hg : guard keys i x with
  | none =>
    simp only [recordingGuardProgram, hg, Option.elim_none]
    exact callCost_call i x _ (fun _ => callCost_return _)
  | some y =>
    simp only [recordingGuardProgram, hg, Option.elim_some]
    exact callCost_return _

/-- Rejection preserves both states. Forwarding advances the inside state once and records its
reply before returning it. -/
lemma recordingGuardProgram_combine {R : Type}
    -- `R` carries inside states; `step r i x` returns the next state and reply.
    (step : R → (i : A.I) → A.X i → R × A.Y i)
    -- `keys` is the current record; `i(x)` is the outside query.
    -- `r` is the current inside state.
    (keys : List K) (r : R) (i : A.I) (x : A.X i) :
    (recordingGuardProgram record guard).combine step
      (recordingGuardProgram_bounded record guard) (keys, r) i x =
      match guard keys i x with
      | some y => ((keys, r), y)
      | none =>
        let p := step r i x
        ((Option.elim (record i x p.2) keys (fun k => keys.insert k), p.1), p.2) := by
  cases hg : guard keys i x with
  | some y =>
    -- Rejection completes immediately, without advancing the inside automaton.
    apply Program.combine_eq_of_invoke (n := 0)
    simp only [Program.invoke, recordingGuardProgram_reject record guard keys i x y hg,
      Sum.elim_inl]
  | none =>
    -- One inside transition supplies the reply and the optional new record key.
    apply Program.combine_eq_of_invoke (n := 1)
    simp only [Program.invoke, recordingGuardProgram_forward record guard keys i x hg,
      List.nil_append, recordingGuardProgram_reply record guard keys i x _ hg, Sum.elim_inl]

/-- Attachment starts the record at `[]` beside the same sampled inside state; each invocation
follows the combined transition rule. -/
lemma recordingGuard_smul_ofAutomaton {R : Type}
    -- `hsub` admits each nonempty subsequence of an admitted outside history.
    (hsub : ∀ {xs ys}, xs <+ ys → xs ≠ [] → A.domain ys → A.domain xs)
    -- `R` carries inside states; `step r i x` returns the next state and reply.
    (step : R → (i : A.I) → A.X i → R × A.Y i)
    -- `init` samples the inside state once, independently of the initially empty record.
    (init : Probability.Distribution.ProbDist R) :
    recordingGuard record guard hsub • TypedSystem.ofAutomaton A step init =
      TypedSystem.ofAutomaton A
        ((recordingGuardProgram record guard).combine step
          (recordingGuardProgram_bounded record guard))
        (init.map fun r => (([] : List K), r)) :=
  ofDDC_ofProgramOn_smul_ofAutomaton [] (recordingGuardProgram record guard)
    (recordingGuardProgram_bounded record guard) _ step init

end SystemAlgebra.TypedConverter

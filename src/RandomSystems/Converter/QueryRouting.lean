import RandomSystems.Converter.CallRuleTranscript

/-!
# Input-dependent query routing

The router is the converter that answers each outside query `o(v)` with exactly one inside
query `j(x)`, where `(j,x) = request (o,v)`. The request may depend on the whole input
`u = (o,v)`, including its value. On the inside reply `j ⇒ y` the router replies
`o ⇒ answer u (j,y)` at the original outside port. The answer depends on the retained input `u`
and on the returned label and value `(j,y)`. Because the inside port depends on the value `v`, the
router is a converter call and not a renaming of interface labels.

```text
                ┌───────────────────────┐
  o(v)      ──► │ (j,x) = request u     │ ──► j(x)
                │ retain u = (o,v)      │
  o ⇒ v'    ◄── │ v' = answer u (j,y)   │ ◄── j ⇒ y
                └───────────────────────┘
```

## Main definitions

* `routingCall request answer`: the per-invocation rule, one inside query and then the answer
* `routingConverter request answer F`: the router on the outside domain `F`

## Main results

* `routingCall_queries`: the inside queries are the request images of the outside inputs,
  including the query of a pending or interrupted invocation
* `routingConverter_isDDCFrom`: if `F us → E (us.map request)`, the router is a DDC from the
  inside domain `E` to the outside domain `F`, with one inside query per invocation
* `replies_routingConverter_ofFunction`: against fixed functions `f_j`, the router replies
  `answer u (j, f_j(x))` to every input `u` of an admitted history

Sources: Jost, Definition 2.2.2; CR18, Definitions 3.8–3.9.
-/

namespace SystemAlgebra

/-- **The routing rule** of one invocation on the outside input `u`, as a function of the
replies `rs` received so far in that invocation:
`c_u([]) = inr (request u)`, an inside query, and `c_u(r :: rs) = inl (answer u r)`, the
outside reply at port `u.1`. The retained state is `u` together with the replies of the current
invocation. The schedule admits exactly one reply, so `rs` is empty in the second equation.

Jost, Definition 2.2.2, printed pp. 17–18: “Upon an input at an outside interface, the
converter is allowed to make a bounded number of queries to the inside interfaces ... before
returning a value at the queried interface.” -/
def routingCall {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (u : Σ o, U o) (replies : List (Σ j, Y j)) :
    V u.1 ⊕ (Σ j, X j) :=
  match replies with
  | [] => .inr (request u)
  | r :: _ => .inl (answer u r)

/-- **The router** on the outside domain `F`: the direct-call converter of `routingCall`.
On `o(v)` it queries `j(x)` with `(j,x) = request (o,v)`; on `j ⇒ y` it replies
`o ⇒ answer (o,v) (j,y)`. It retains only the current input `(o,v)`.

Canonicalization enforces the reply label `o` and the schedule (one inside query, then one
outside reply). The filter admits exactly the histories whose outside inputs are empty or lie
in `F`. The filter does not make the inside queries legal; that is the hypothesis
`F us → E (us.map request)` of `routingConverter_isDDCFrom`.

CR18, Definition 3.8, printed p. 62: “After an output (in, x) the input alphabet is Y, and
after an output of the form (out, v) the input alphabet is U.” -/
noncomputable def routingConverter {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (F : List (Σ o, U o) → Prop) : InsideOutsideSystem O J U V X Y :=
  callConverter (O := O) (J := J) (U := U) (V := V)
    (X := X) (Y := Y) (routingCall request answer) F

/-- **One inside query per invocation**: the rule queries exactly before the first reply,
whatever the reply. -/
lemma routingCall_phase {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j) (u : Σ o, U o)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (replies : List (Σ j, Y j)) :
    (routingCall request answer u replies).isRight = true ↔ replies.length < 1 := by
  cases replies with
  | nil => simp only [routingCall, Sum.isRight_inr, List.length_nil, Order.lt_one_iff]
  | cons r rs =>
    simp only [routingCall, Sum.isRight_inl, Bool.false_eq_true, List.length_cons,
      Order.lt_one_iff, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false]

/-- The canonical routing rule is a responsive DDC with bound `1`: it answers every admissible
history, runs at most one consecutive inside query, and replies at the current outside port. -/
lemma routingCall_isResponsiveDDC {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1) :
    IsResponsiveDDC 1 (canon (callRule (O := O) (J := J) (U := U)
      (V := V) (X := X) (Y := Y) (routingCall request answer))) := by
  apply callRule_isResponsiveDDC (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) (fun _ => 1) 1
  -- Phase: an invocation queries only before its first reply, so its cost is `1`.
  · intro u replies hr
    exact (routingCall_phase request u answer replies).mp hr
  -- Every cost `1` is within the bound `1`.
  · intro u
    rfl

/-- **The inside queries are the requests**: on every transcript of the raw routing rule,
`insideQueries = map request (outsideInputs)`. Each outside input emits its query immediately,
so the equality also counts the query of a pending or interrupted invocation. -/
lemma routingCall_queries {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
    (hr : Replies (callRule (O := O) (J := J) (U := U)
      (V := V) (X := X) (Y := Y)
      (routingCall request answer)) (T.map Prod.fst) (T.map Prod.snd)) :
    insideQueries (T.map Prod.snd) =
      (outsideInputs (T.map Prod.fst)).map request := by
  -- Induction on the transcript, extended by one exchange `z = (input, output)` at a time;
  -- split on whether the input is an outside query or an inside reply.
  induction T using List.reverseRecOn with
  | nil => rfl
  | append_singleton T z ih =>
    obtain ⟨x, y⟩ := z
    simp only [List.map_append, List.map_singleton, replies_snoc] at hr ⊢
    have hi := ih hr.1
    have hy := Part.eq_some_iff.mp hr.2
    obtain ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩ := x
    · -- An outside input emits its request immediately, including when the call is pending.
      simp only [callRule, routingCall, List.reverse_append, List.reverse_singleton,
        List.singleton_append, currentCall, Part.mem_some_iff] at hy
      subst y
      simp only [insideQueries_append, insideQueries_inside, outsideInputs_append,
        outsideInputs_outside, List.map_append, List.map_singleton, hi]
    · -- An inside reply `j ⇒ y` of the current invocation `(u, rs)` yields the outside reply
      -- `answer u (j,y)`, with no further inside query; without a current invocation the raw
      -- rule is silent.
      simp only [callRule, List.reverse_append, List.reverse_singleton,
        List.singleton_append, currentCall] at hy
      rw [currentCall_acc] at hy
      cases hc : currentCall (T.map Prod.fst).reverse [] with
      | none => simp only [hc, Option.map_none, Part.notMem_none] at hy
      | some c =>
        obtain ⟨u, rs⟩ := c
        simp only [hc, Option.map_some] at hy
        cases rs <;> simp only [routingCall, List.nil_append, List.cons_append,
          Part.mem_some_iff] at hy
        all_goals
          subst y
          simpa only [insideQueries_append, insideQueries_outside, outsideInputs_append,
            outsideInputs_inside, List.append_nil] using hi

/-- **The router's domain guarantee**: if `F` is closed under nonempty prefixes and
`F us → E (us.map request)`, the router is a DDC from the inside domain `E` to the outside
domain `F`, with one inside query per outside input.

```text
  outside inputs   us = [u₁, …, uₙ] ∈ F
  inside queries   [request u₁, …, request uₙ] ∈ E
```

The inside history includes the query of a pending invocation, so the hypothesis is required
for every history in `F`, not only for completed calls. `F` may contain `[]`: the filter
admits the empty outside history in any case, and its inside history is empty. -/
lemma routingConverter_isDDCFrom {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hmap : ∀ us, F us → E (us.map request)) :
    IsDDCFrom E F 1 (routingConverter request answer F) := by
  -- Responsiveness and the outside filter leave the inside-domain condition on transcripts.
  apply (routingCall_isResponsiveDDC request answer).isDDCFrom_filterDom hF
  intro T hr
  -- The empty transcript has no inside queries.
  by_cases hn : T.map Prod.fst = []
  · have he := List.map_eq_nil_iff.mp hn
    subst T
    exact Or.inl rfl
  -- Otherwise the filter gives outside inputs `[]` or in `F`; the transcript is one of the raw
  -- rule, whose inside queries are the requests (`routingCall_queries`), and `hmap` gives `E`.
  have hd := ((filterDom_dom _ _ _).mp (hr.dom hn)).1
  have raw := hr.mono fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2
  rw [routingCall_queries request answer T raw]
  exact hd.elim (fun he => Or.inl (by rw [he]; rfl))
    (fun hd => Or.inr (hmap _ hd))

/-- **The router against fixed functions**: for `us ∈ F` and inside functions `f_j`, the router
has the completed transcript of `us`, in which each call `u = (o,v)` with `(j,x) = request u`
reads

```text
  o(v) ──► j(x),   j ⇒ f_j(x) ──► o ⇒ answer u (j, f_j(x))
```
-/
lemma replies_routingConverter_ofFunction {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {F : List (Σ o, U o) → Prop}
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (f : ∀ j, X j → Y j) (us : List (Σ o, U o)) (hus : F us) :
    Replies (routingConverter request answer F)
      ((us.flatMap fun u => callTranscript u
        [(request u, ⟨(request u).1, f (request u).1 (request u).2⟩)]
        ⟨u.1, answer u ⟨(request u).1, f (request u).1 (request u).2⟩⟩).map Prod.fst)
      ((us.flatMap fun u => callTranscript u
        [(request u, ⟨(request u).1, f (request u).1 (request u).2⟩)]
        ⟨u.1, answer u ⟨(request u).1, f (request u).1 (request u).2⟩⟩).map Prod.snd) := by
  -- The completed-call transcript of the direct-call converter, with the schedule
  -- `queries u = [request u]` and outside reply `g(u) = answer u (j, f_j(x))`.
  change Replies (callConverter (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) F) _ _
  apply replies_callConverter_of_schedule (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) F hF f
    (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => [request u])
  -- Before its only reply, the call queries `request u`.
  · intro u n hn
    have hn0 : n = 0 := by simp only [List.length_singleton] at hn; omega
    subst n
    simp only [routingCall, List.take_zero, List.map_nil, List.getElem_cons_zero]
  -- After the reply `f_j(x)`, the call returns `g(u)`.
  · intro u
    simp only [routingCall, List.map_cons, List.map_nil]
  -- The outside history is admitted.
  · exact hus

end SystemAlgebra

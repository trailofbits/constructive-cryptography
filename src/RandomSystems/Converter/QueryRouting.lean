import RandomSystems.Converter.CallRuleTranscript

/-!
# Input-dependent query routing

One outside input `u` is forwarded as `request u` to the selected inside port. An explicit
`answer` map returns its reply at `u`'s original outside port. The inside port may depend on the
whole outside input, so this is a converter call rather than a label-only interface renaming.

```text
              ┌────────────────────────┐
u = (o,v) ──► │ request u = (j,x)      │ ──► (j,x)
              │ retain u for this call │
(o,z)     ◄── │ z = answer u (j,y)     │ ◄── (j,y)
              └────────────────────────┘
```

The pending inside query is counted as soon as the outside input arrives. The request map must
preserve the chosen inside domain: `F(us) → E(map request us)` for outside domain `F` and inside
domain `E`. Against fixed inside functions `f_j`, the outside reply is
`g(u) = answer u (j, f_j(x))`, where `request u = (j,x)`.
-/

namespace SystemAlgebra

/-- One-query rule: `c_u([]) = query(request u)` and
`c_u(r :: rs) = return(answer u r)`. The outside input `u` is retained until the reply arrives.

Jost, Definition 2.2.2, printed
pp. 17–18: “Upon an input at an outside interface, the converter is allowed to make a bounded
number of queries to the inside interfaces ... before returning a value at the queried
interface.” -/
def routingCall {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (u : Σ o, U o) (replies : List (Σ j, Y j)) :
    V u.1 ⊕ (Σ j, X j) :=
  match replies with
  | [] => .inr (request u)
  | r :: _ => .inl (answer u r)

/-- On outside input `u`, query `request u = (j,x)`; on inside reply `(j,y)`, return
`answer u (j,y)` at the original outside port `u.1`. The current input `u` is retained for
this call. Canonicalization enforces the query/reply order, and restriction to `F` admits
exactly the chosen outside input histories. -/
noncomputable def routingConverter {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (F : List (Σ o, U o) → Prop) : InsideOutsideSystem O J U V X Y :=
  callConverter (O := O) (J := J) (U := U) (V := V)
    (X := X) (Y := Y) (routingCall request answer) F

/-- Every router invocation has exactly one inside-query phase, regardless of the reply. -/
lemma routingCall_phase {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j) (u : Σ o, U o)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (replies : List (Σ j, Y j)) :
    (routingCall request answer u replies).isRight = true ↔ replies.length < 1 := by
  cases replies <;> simp [routingCall]

/-- The direct-call theorem gives responsiveness and correct outside return labels. -/
lemma routingCall_isResponsiveDDC {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1) :
    IsResponsiveDDC 1 (canon (callRule (O := O) (J := J) (U := U)
      (V := V) (X := X) (Y := Y) (routingCall request answer))) := by
  apply callRule_isResponsiveDDC (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) (fun _ => 1) 1
  · intro u replies hr
    exact (routingCall_phase request u answer replies).mp hr
  · intro u
    rfl

/-- The router's inside queries are precisely the request-map images of its outside inputs.
The equality includes the pending query of an interrupted invocation. -/
lemma routingCall_queries {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
    (hr : Replies (callRule (O := O) (J := J) (U := U)
      (V := V) (X := X) (Y := Y)
      (routingCall request answer)) (T.map Prod.fst) (T.map Prod.snd)) :
    insideQueries (T.map Prod.snd) =
      (outsideInputs (T.map Prod.fst)).map request := by
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
    · -- Feeding back the answer ends that invocation without another inside query.
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

/-- If `F(us) → E(map request us)`, the router converts the inside domain `E` to the
outside domain `F`, using one inside query per outside input. The history condition covers
the pending query as well as completed calls. -/
lemma routingConverter_isDDCFrom {O J : Type} {U V : O → Type} {X Y : J → Type}
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hmap : ∀ us, F us → E (us.map request)) :
    IsDDCFrom E F 1 (routingConverter request answer F) := by
  apply (routingCall_isResponsiveDDC request answer).isDDCFrom_filterDom hF.2
  intro T hr
  by_cases hn : T.map Prod.fst = []
  · have he := List.map_eq_nil_iff.mp hn
    subst T
    exact Or.inl rfl
  -- The outside domain and the exact request map discharge the inside-domain condition.
  have hd := ((filterDom_dom _ _ _).mp (hr.dom hn)).1
  have raw := hr.mono fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2
  rw [routingCall_queries request answer T raw]
  exact hd.elim (fun he => Or.inl (by rw [he]; rfl))
    (fun hd => Or.inr (hmap _ hd))

/-- The router's pointwise schedule is one query followed by the returned oracle answer. -/
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
  -- Specialize the generic direct-call realization to a singleton query schedule.
  change Replies (callConverter (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) F) _ _
  apply replies_callConverter_of_schedule (O := O) (J := J) (U := U)
    (V := V) (X := X) (Y := Y) (routingCall request answer) F hF f
    (fun o u => answer ⟨o, u⟩
      ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => [request u])
  · intro u n hn
    have hn0 : n = 0 := by simp at hn; omega
    subst n
    simp [routingCall]
  · intro u
    simp [routingCall]
  · exact hus

end SystemAlgebra

module

public import RandomSystems.Converter.CallRuleTranscript
public import RandomSystems.Converter.SerialAccounting

/-!
# Conditional oracle calls

A conditional oracle-call converter inspects each outside query `u = (o, x)` with a branch
predicate `branch`. On inputs satisfying `branch`, it replies immediately with `pureReply u`
without querying the inside interface. On inputs failing `branch`, it issues one inside query
`request u = (j, a)` and replies `answer u (j, y)` on the inside reply `y`.

```text
                      ┌─────────────────────────────────────────┐
  o(x) [branch]   ──► │ return pureReply (o, x)                 │
  o ⇒ p(x)        ◄── │ (0 inside queries)                      │
                      ├─────────────────────────────────────────┤
  o(x) [¬branch]  ──► │ (j, a) = request u                      │ ──► j(a)
  o ⇒ b(u, j, y)  ◄── │ retain u, return answer u (j, y)        │ ◄── j ⇒ y
                      └─────────────────────────────────────────┘
```

## Main definitions

* `conditionalCost branch u`: per-input inside-query cost (`0` on the pure branch, `1` on the
  oracle branch)
* `conditionalRequests branch request us`: the sequence of inside requests emitted by the
  oracle-branch inputs of `us`
* `conditionalCall branch pureReply request answer`: the per-invocation call rule
* `conditionalCallConverter branch pureReply request answer F`: the converter over
  `callConverter` keeping the outside domain `F`

## Main results

* `conditionalCall_phase`: biconditional phase condition against `conditionalCost`
* `conditionalCall_isResponsiveDDC`: canonical responsiveness with bound `1`
* `conditionalCall_queries`, `conditionalCallConverter_queries`: exact inside queries, including
  a pending oracle-branch call as soon as it is sent
* `conditionalCallConverter_query_count`: exact inside-query count equals the sum of
  `conditionalCost` over outside inputs
* `conditionalCall_completed_exact_length`: completed calls emit `0` or `1` inside requests
* `conditionalCallConverter_isDDCFrom`: domain certificate keeping `F` when nonempty
  oracle-branch request sequences lie in `E`
* `IsDDCFrom.comp_conditionalCallConverter_query_count_le`: serial accounting when composed as an
  inner converter
* `replies_conditionalCallConverter_ofFunction`: completed transcripts against fixed inside
  functions
-/

@[expose] public section

namespace SystemAlgebra

/-- Inside-query cost of a single outside input `u`: `0` on the pure branch (`branch u`), `1` on
the oracle branch (`¬ branch u`). -/
def conditionalCost {O : Type} {U : O → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (u : Σ o, U o) : ℕ :=
  if branch u then 0 else 1

/-- Inside requests emitted by the oracle branch of an outside-input history `us`, in order.
Inputs satisfying `branch` emit no inside request. -/
def conditionalRequests {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j)
    (us : List (Σ o, U o)) : List (Σ j, X j) :=
  us.filterMap fun u => if branch u then none else some (request u)

/-- Empty outside histories produce no inside requests. -/
lemma conditionalRequests_nil {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j) :
    conditionalRequests branch request [] = [] :=
  rfl

/-- Inside requests append across concatenated outside histories. -/
lemma conditionalRequests_append {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j)
    (us vs : List (Σ o, U o)) :
    conditionalRequests branch request (us ++ vs) =
      conditionalRequests branch request us ++ conditionalRequests branch request vs :=
  List.filterMap_append

/-- A single outside input emits `[]` on the pure branch and `[request u]` on the oracle branch. -/
lemma conditionalRequests_singleton {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j)
    (u : Σ o, U o) :
    conditionalRequests branch request [u] = if branch u then [] else [request u] := by
  by_cases hb : branch u
  · simp only [conditionalRequests, List.filterMap_cons, hb, ↓reduceIte, List.filterMap_nil]
  · simp only [conditionalRequests, List.filterMap_cons, hb, ↓reduceIte, List.filterMap_nil]

/-- The number of oracle-branch requests equals the sum of `conditionalCost` over `us`. -/
lemma conditionalRequests_length {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j)
    (us : List (Σ o, U o)) :
    (conditionalRequests branch request us).length =
      (us.map (conditionalCost branch)).sum := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    by_cases hb : branch u
    · simp only [conditionalRequests, List.filterMap_cons, hb, ↓reduceIte, List.map_cons,
        List.sum_cons, conditionalCost, Nat.zero_add] at ih ⊢
      exact ih
    · simp only [conditionalRequests, List.filterMap_cons, hb, ↓reduceIte, List.length_cons,
        List.map_cons, List.sum_cons, conditionalCost] at ih ⊢
      omega

/-- The oracle branch emits at most one inside request per outside input. -/
lemma conditionalRequests_length_le {O J : Type} {U : O → Type} {X : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (request : (Σ o, U o) → Σ j, X j)
    (us : List (Σ o, U o)) :
    (conditionalRequests branch request us).length ≤ us.length := by
  exact List.length_filterMap_le _ us

/-- **The conditional call rule** for one invocation on outside input `u`: return `pureReply u`
immediately when `branch u` holds; otherwise issue `request u` before any inside reply arrives
and return `answer u r` on the inside reply `r`. -/
def conditionalCall {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (u : Σ o, U o) (replies : List (Σ j, Y j)) :
    V u.1 ⊕ (Σ j, X j) :=
  if branch u then
    .inl (pureReply u)
  else
    match replies with
    | [] => .inr (request u)
    | r :: _ => .inl (answer u r)

/-- **The conditional oracle-call converter** on the outside domain `F`: the direct-call converter
of `conditionalCall`, retaining the caller's outside domain `F`. -/
noncomputable def conditionalCallConverter {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (F : List (Σ o, U o) → Prop) : InsideOutsideSystem O J U V X Y :=
  callConverter (O := O) (J := J) (U := U) (V := V)
    (X := X) (Y := Y) (conditionalCall branch pureReply request answer) F

/-- **Biconditional phase condition**: `conditionalCall` emits an inside query if and only if
`replies.length < conditionalCost branch u` (never on the pure branch, before the first reply on
the oracle branch). -/
lemma conditionalCall_phase {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (u : Σ o, U o) (replies : List (Σ j, Y j)) :
    (conditionalCall branch pureReply request answer u replies).isRight = true ↔
      replies.length < conditionalCost branch u := by
  by_cases hb : branch u
  · simp only [conditionalCall, conditionalCost, hb, ↓reduceIte, Sum.isRight_inl,
      Bool.false_eq_true, Nat.not_lt_zero]
  · cases replies with
    | nil =>
      simp only [conditionalCall, conditionalCost, hb, ↓reduceIte, Sum.isRight_inr,
        List.length_nil, Nat.zero_lt_one]
    | cons r rs =>
      simp only [conditionalCall, conditionalCost, hb, ↓reduceIte, Sum.isRight_inl,
        Bool.false_eq_true, List.length_cons, Order.lt_one_iff, Nat.add_eq_zero_iff,
        one_ne_zero, and_false]

/-- The canonical conditional call rule is a responsive DDC with bound `1`. -/
lemma conditionalCall_isResponsiveDDC {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1) :
    IsResponsiveDDC 1 (canon (callRule (O := O) (J := J) (U := U) (V := V) (X := X) (Y := Y)
      (conditionalCall branch pureReply request answer))) := by
  apply callRule_isResponsiveDDC (O := O) (J := J) (U := U) (V := V) (X := X) (Y := Y)
    (conditionalCall branch pureReply request answer) (conditionalCost branch) 1
  · intro u replies hr
    exact (conditionalCall_phase branch pureReply request answer u replies).mp hr
  · intro u
    by_cases hb : branch u
    · simp only [conditionalCost, hb, ↓reduceIte, Nat.zero_le]
    · simp only [conditionalCost, hb, ↓reduceIte, le_refl]

/-- **Exact inside queries**: on every transcript of the raw conditional call rule, the inside
queries are exactly the oracle-branch requests `conditionalRequests branch request` of the
outside inputs, counting a pending oracle-branch request as soon as it is sent. -/
lemma conditionalCall_queries {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
    (hr : Replies (callRule (O := O) (J := J) (U := U) (V := V) (X := X) (Y := Y)
      (conditionalCall branch pureReply request answer)) (T.map Prod.fst) (T.map Prod.snd)) :
    insideQueries (T.map Prod.snd) =
      conditionalRequests branch request (outsideInputs (T.map Prod.fst)) := by
  induction T using List.reverseRecOn with
  | nil => rfl
  | append_singleton T z ih =>
    obtain ⟨x, y⟩ := z
    simp only [List.map_append, List.map_singleton, replies_snoc] at hr ⊢
    have hi := ih hr.1
    have hy := Part.eq_some_iff.mp hr.2
    obtain ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩ := x
    · -- Outside input: pure branch replies immediately (`0` inside queries); oracle branch
      -- emits `request ⟨i, x⟩` immediately, counted as soon as it is sent.
      simp only [callRule, List.reverse_append, List.reverse_singleton,
        List.singleton_append, currentCall] at hy
      by_cases hb : branch ⟨i, x⟩
      · simp only [conditionalCall, hb, ↓reduceIte, Part.mem_some_iff] at hy
        subst y
        rw [insideQueries_append, insideQueries_outside, List.append_nil,
          outsideInputs_append, outsideInputs_outside, conditionalRequests_append,
          conditionalRequests_singleton, ite_eq_left hb, List.append_nil, hi]
      · simp only [conditionalCall, hb, ↓reduceIte, Part.mem_some_iff] at hy
        subst y
        rw [insideQueries_append, insideQueries_inside, outsideInputs_append,
          outsideInputs_outside, conditionalRequests_append,
          conditionalRequests_singleton, ite_eq_right hb, hi]
    · -- Inside reply: `rs ++ [r]` is nonempty, so both branches produce an outside reply and
      -- emit no further inside query.
      simp only [callRule, List.reverse_append, List.reverse_singleton,
        List.singleton_append, currentCall] at hy
      rw [currentCall_acc] at hy
      cases hc : currentCall (T.map Prod.fst).reverse [] with
      | none => simp only [hc, Option.map_none, Part.notMem_none] at hy
      | some c =>
        obtain ⟨u, rs⟩ := c
        simp only [hc, Option.map_some] at hy
        by_cases hb : branch u
        · simp only [conditionalCall, hb, ↓reduceIte, Part.mem_some_iff] at hy
          subst y
          simpa only [insideQueries_append, insideQueries_outside, outsideInputs_append,
            outsideInputs_inside, List.append_nil] using hi
        · cases rs <;> simp only [conditionalCall, hb, ↓reduceIte, List.nil_append,
            List.cons_append, Part.mem_some_iff] at hy
          all_goals
            subst y
            simpa only [insideQueries_append, insideQueries_outside, outsideInputs_append,
              outsideInputs_inside, List.append_nil] using hi

/-- **Domain certificate**: if `F` is closed under nonempty prefixes and every nonempty sequence
of oracle-branch requests from an admitted outside history `us ∈ F` lies in `E`, then
`conditionalCallConverter` is a DDC from `E` to `F` with bound `1`. -/
lemma conditionalCallConverter_isDDCFrom {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hmap : ∀ us, F us → conditionalRequests branch request us ≠ [] →
      E (conditionalRequests branch request us)) :
    IsDDCFrom E F 1 (conditionalCallConverter branch pureReply request answer F) := by
  apply (conditionalCall_isResponsiveDDC branch pureReply request answer).isDDCFrom_filterDom hF
  intro T hr
  by_cases hn : T.map Prod.fst = []
  · have he := List.map_eq_nil_iff.mp hn
    subst T
    exact Or.inl rfl
  have hd := ((filterDom_dom _ _ _).mp (hr.dom hn)).1
  have raw := hr.mono fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2
  rw [conditionalCall_queries branch pureReply request answer T raw]
  rcases hd with he | hf
  · exact Or.inl (by rw [he]; rfl)
  · by_cases hne : conditionalRequests branch request (outsideInputs (T.map Prod.fst)) = []
    · exact Or.inl hne
    · exact Or.inr (hmap _ hf hne)

/-- Every transcript of `conditionalCallConverter` emits exactly the oracle-branch requests of
its outside inputs, including a pending oracle-branch call as soon as it is sent. -/
lemma conditionalCallConverter_queries {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {F : List (Σ o, U o) → Prop}
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (conditionalCallConverter branch pureReply request answer F)
      (T.map Prod.fst) (T.map Prod.snd)) :
    insideQueries (T.map Prod.snd) =
      conditionalRequests branch request (outsideInputs (T.map Prod.fst)) :=
  conditionalCall_queries branch pureReply request answer T
    (hr.mono fun h y hy => canon_mem
      ((filterDom_mem_iff (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs))
        _ h y).mp hy).2)

/-- Every transcript of `conditionalCallConverter` spends `0` inside queries per pure-branch
input and `1` per oracle-branch input, counting pending oracle calls as soon as they are sent. -/
lemma conditionalCallConverter_query_count {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {F : List (Σ o, U o) → Prop}
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (conditionalCallConverter branch pureReply request answer F)
      (T.map Prod.fst) (T.map Prod.snd)) :
    (insideQueries (T.map Prod.snd)).length =
      ((outsideInputs (T.map Prod.fst)).map (conditionalCost branch)).sum := by
  rw [conditionalCallConverter_queries branch pureReply request answer hr,
    conditionalRequests_length]

/-- A completed call of `conditionalCall` on `u` emits `conditionalCost branch u` inside queries
(`0` on the pure branch, `1` on the oracle branch), via `callRule_completed_exact_length`. -/
lemma conditionalCall_completed_exact_length {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    (u : Σ o, U o) (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : V u.1)
    (hquery : ∀ n (hn : n < qs.length),
      conditionalCall branch pureReply request answer u ((qs.take n).map Prod.snd) =
        .inr qs[n].1)
    (hreturn : conditionalCall branch pureReply request answer u (qs.map Prod.snd) = .inl v) :
    (insideQueries ((callTranscript u qs ⟨u.1, v⟩).map Prod.snd)).length =
      conditionalCost branch u :=
  callRule_completed_exact_length (conditionalCall branch pureReply request answer)
    (conditionalCost branch) (conditionalCall_phase branch pureReply request answer)
    u qs v hquery hreturn

/-- Serial composition with an inner `conditionalCallConverter` charges `conditionalCost` per
intermediate query issued by the outer converter `β`. -/
lemma IsDDCFrom.comp_conditionalCallConverter_query_count_le
    {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}
    {E : List (Σ j, X j) → Prop} {F : List (Σ m, Xm m) → Prop}
    {G : List (Σ o, U o) → Prop} {bβ : ℕ}
    {β : InsideOutsideSystem O M U V Xm Ym}
    (hβ : IsDDCFrom F G bβ β)
    (branch : (Σ m, Xm m) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ m, Xm m) → Ym u.1)
    (request : (Σ m, Xm m) → Σ j, X j)
    (answer : (u : Σ m, Xm m) → (Σ j, Y j) → Ym u.1)
    (hα : IsDDCFrom E F 1 (conditionalCallConverter branch pureReply request answer F))
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (trim (serialM β (conditionalCallConverter branch pureReply request answer F)))
      (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ Tb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      (insideQueries (T.map Prod.snd)).length ≤
        ((insideQueries (Tb.map Prod.snd)).map (conditionalCost branch)).sum :=
  hβ.comp_callConverter_query_count_le (conditionalCall branch pureReply request answer)
    (conditionalCost branch)
    (fun u rs h => (conditionalCall_phase branch pureReply request answer u rs).mp h)
    hα hr

/-- **Completed transcripts against fixed functions**: for `us ∈ F` and fixed inside functions
`f_j`, each pure-branch input returns `pureReply u` with no inside query and each oracle-branch
input queries `request u` once and returns `answer u (j, f_j x)`. -/
lemma replies_conditionalCallConverter_ofFunction {O J : Type} {U V : O → Type} {X Y : J → Type}
    (branch : (Σ o, U o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, U o) → V u.1)
    (request : (Σ o, U o) → Σ j, X j)
    (answer : (u : Σ o, U o) → (Σ j, Y j) → V u.1)
    {F : List (Σ o, U o) → Prop}
    (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (f : ∀ j, X j → Y j) (us : List (Σ o, U o)) (hus : F us) :
    let queries : (Σ o, U o) → List (Σ j, X j) := fun u =>
      if branch u then [] else [request u]
    let g : ∀ o, U o → V o := fun o u =>
      if branch ⟨o, u⟩ then pureReply ⟨o, u⟩
      else answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩
    Replies (conditionalCallConverter branch pureReply request answer F)
      ((us.flatMap fun u => callTranscript u
        ((queries u).map fun x => (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.fst)
      ((us.flatMap fun u => callTranscript u
        ((queries u).map fun x => (x, ⟨x.1, f x.1 x.2⟩)) ⟨u.1, g u.1 u.2⟩).map Prod.snd) := by
  dsimp only
  change Replies (callConverter (O := O) (J := J) (U := U) (V := V) (X := X) (Y := Y)
    (conditionalCall branch pureReply request answer) F) _ _
  apply replies_callConverter_of_schedule (O := O) (J := J) (U := U) (V := V) (X := X) (Y := Y)
    (conditionalCall branch pureReply request answer) F hF f
    (fun o u =>
      if branch ⟨o, u⟩ then pureReply ⟨o, u⟩
      else answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => if branch u then [] else [request u])
  · intro u n hn
    by_cases hb : branch u
    · simp only [hb, ↓reduceIte, List.length_nil, Nat.not_lt_zero] at hn
    · have hn0 : n = 0 := by
        simp only [hb, ↓reduceIte, List.length_singleton] at hn
        omega
      subst n
      simp only [hb, ↓reduceIte, List.take_zero, List.map_nil, conditionalCall,
        List.getElem_cons_zero]
  · intro u
    by_cases hb : branch u
    · simp only [hb, ↓reduceIte, conditionalCall]
    · simp only [hb, ↓reduceIte, List.map_singleton, conditionalCall]
  · exact hus

end SystemAlgebra

import RandomSystems.Converter.ConverterDomain

/-!
# Completed converter calls

A completed call of a converter `α` attached to an inside system `R`: the outside query `u` at
port `o`, the inside exchanges `qs = [(x₁, y₁), …, (xₙ, yₙ)]`, and the outside reply `v`.

```text
            o(u)   ┌─────┐   j₁(x₁) … jₙ(xₙ)   ┌─────┐
  ────────────────►│  α  ├────────────────────►│  R  │
  ◄────────────────┤     │◄────────────────────┤     │
            o ⇒ v  └─────┘   j₁ ⇒ y₁ … jₙ ⇒ yₙ └─────┘
```

## Main definitions

* `callTranscript u qs v`: the converter's exchanges (input, output),
  `(u, x₁), (y₁, x₂), …, (yₙ, v)`, and `[(u, v)]` when `n = 0`; `callSteps first qs v` is the
  same from the converter input `first` on
* `callInternal ⟨u⟩ qs`: the internal history of the connection of `α` with `R`, the converter
  inputs and inside queries interleaved, `u, x₁, y₁, …, xₙ, yₙ`, and `[u]` when `n = 0`

## Main results

* `replies_apply_of_calls`: if `α` has the call transcripts and `R` answers their inside queries,
  the attachment `apply α R` answers each call `u` with `v`
* `replies_canon_calls`: a rule answering every prefix of its calls still does so after
  canonicalization
-/

namespace SystemAlgebra

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- The exchanges of a call from the converter input `first` on,
`(first, x₁), (y₁, x₂), …, (yₙ, v)` for `qs = [(x₁, y₁), …, (xₙ, yₙ)]`, and `[(first, v)]` for
`qs = []`: each inside query is answered with its given reply and fed back; the last input is
answered by the outside reply `v`. -/
def callSteps (first : Σ l, twoFam U Y l) :
    List ((Σ j, X j) × (Σ j, Y j)) → (Σ o, V o) → List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))
  | [], v => [(first, ⟨⟨none, v.1⟩, v.2⟩)]
  | xy :: qs, v => (first, ⟨⟨some (), xy.1.1⟩, xy.1.2⟩) ::
      callSteps ⟨⟨some (), xy.2.1⟩, xy.2.2⟩ qs v

/-- **The transcript of one call** of a converter, `(u, x₁), (y₁, x₂), …, (yₙ, v)`, or `[(u, v)]`
without inside exchanges: the outside query `u`, the inside exchanges `qs`, and the outside reply
`v`. -/
def callTranscript (u : Σ o, U o) (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : Σ o, V o) :
    List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)) :=
  callSteps ⟨⟨none, u.1⟩, u.2⟩ qs v

/-- The inside queries of a call are its given queries. -/
lemma insideQueries_callSteps (v : Σ o, V o) :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l),
      insideQueries ((callSteps first qs v).map Prod.snd) = qs.map Prod.fst
  | [], first => by simp only [callSteps, List.map_cons, List.map_nil,
    insideQueries_outside]
  | xy :: qs, first => by
    rw [callSteps, List.map_cons, ← List.singleton_append, insideQueries_append,
      insideQueries_inside, insideQueries_callSteps v qs, List.map_cons]
    rfl

/-- The inside queries along calls are the calls' given queries. -/
lemma insideQueries_flatMap_callTranscript
    (calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o))) :
    insideQueries ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) =
      (calls.flatMap (·.2.1)).map Prod.fst := by
  induction calls with
  | nil => rfl
  | cons c calls ih =>
    rw [List.flatMap_cons, List.map_append, insideQueries_append, ih, callTranscript,
      insideQueries_callSteps, List.flatMap_cons, List.map_append]

/-- The internal history of a call from the converter input `first` on, in the connection of
the converter with the inside system, `first, x₁, y₁, …, xₙ, yₙ`, or `[first]` for `qs = []`:
the converter inputs (tag `none`) and inside queries (tag `some ()`), interleaved. -/
def callInternal (first : Σ l, twoFam U Y l) :
    List ((Σ j, X j) × (Σ j, Y j)) → List (Two (Σ l, twoFam U Y l) (Σ j, X j))
  | [] => [⟨none, first⟩]
  | xy :: qs => ⟨none, first⟩ :: ⟨some (), xy.1⟩ :: callInternal ⟨⟨some (), xy.2.1⟩, xy.2.2⟩ qs

/-- The converter's view of the internal history is the call's converter inputs. -/
lemma restrict_none_callInternal (v : Σ o, V o) :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l),
      restrict none (callInternal first qs) = (callSteps first qs v).map Prod.fst
  | [], first => by simp only [callInternal, restrict_cons_self, restrict_nil, callSteps,
    List.map_cons, List.map_nil]
  | xy :: qs, first => by
    simp only [callInternal, restrict_cons_self, ne_eq, reduceCtorEq, not_false_eq_true,
      restrict_cons_ne, restrict_none_callInternal v qs, callSteps, List.map_cons]

/-- The inside system's view of the internal history is the call's inside queries. -/
lemma restrict_some_callInternal :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l),
      restrict (some ()) (callInternal first qs) = qs.map Prod.fst
  | [], first => by simp only [callInternal, ne_eq, reduceCtorEq, not_false_eq_true,
    restrict_cons_ne, restrict_nil, List.map_nil]
  | xy :: qs, first => by
    simp only [callInternal, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne,
      restrict_cons_self, restrict_some_callInternal qs, List.map_cons]

/-- The connection of a converter answering a call with `callSteps first qs v`, against a
system answering its inside queries with their given replies, exchanges internally until it
exposes `v`. -/
lemma exchange_callSteps {α : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y}
    (v : Σ o, V o) {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hα : Replies α (T.map Prod.fst) (T.map Prod.snd)) {Q : List ((Σ j, X j) × (Σ j, Y j))}
    (hR : Replies R (Q.map Prod.fst) (Q.map Prod.snd)) :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l) (P S) (G) (Qpre Qpost),
      T = P ++ callSteps first qs v ++ S → Q = Qpre ++ qs ++ Qpost →
      restrict none G = P.map Prod.fst → restrict (some ()) G = Qpre.map Prod.fst →
      Exchange (pair α R) resourceRoute (G ++ [⟨none, first⟩]) (some v)
        (G ++ callInternal first qs) := by
  intro qs
  induction qs with
  | nil =>
    -- With no inside queries left, the converter's next reply leaves the connection.
    intro first P S G Qpre Qpost hT _ hG _
    have hy := hα.eq_some_of_eq_append (T₁ := P) (z := (first, ⟨⟨none, v.1⟩, v.2⟩)) (T₂ := S)
      (by simp only [hT, callSteps, List.append_assoc, List.cons_append, List.nil_append])
    refine Exchange.out _ ⟨none, ⟨⟨none, v.1⟩, v.2⟩⟩ v ?_ rfl
    rw [pair_left, hG, hy]
    exact Part.mem_map _ (Part.mem_some _)
  | cons xy qs ih =>
    -- Connect the next query to the inside system and feed its reply back to the converter.
    obtain ⟨x, y⟩ := xy
    intro first P S G Qpre Qpost hT hQ hG hGs
    have hy := hα.eq_some_of_eq_append (T₁ := P) (z := (first, ⟨⟨some (), x.1⟩, x.2⟩))
      (T₂ := callSteps ⟨⟨some (), y.1⟩, y.2⟩ qs v ++ S) (by simp only [hT, callSteps,
        List.append_assoc, List.cons_append])
    have hr := hR.eq_some_of_eq_append (T₁ := Qpre) (z := (x, y)) (T₂ := qs ++ Qpost)
      (by simp only [hQ, List.append_assoc, List.cons_append])
    have hnext := ih ⟨⟨some (), y.1⟩, y.2⟩ (P ++ [(first, ⟨⟨some (), x.1⟩, x.2⟩)]) S
      (G ++ [⟨none, first⟩, ⟨some (), x⟩]) (Qpre ++ [(x, y)]) Qpost (by simp only [hT,
        callSteps, List.append_assoc, List.cons_append, List.nil_append])
      (by simp only [hQ, List.append_assoc, List.cons_append, List.nil_append])
      (by simp only [restrict_append, hG, restrict_cons_self, ne_eq,
        reduceCtorEq, not_false_eq_true, restrict_cons_ne, restrict_nil, List.map_append,
        List.map_cons, List.map_nil])
      (by simp only [restrict_append, hGs, ne_eq, reduceCtorEq, not_false_eq_true,
        restrict_cons_ne, restrict_cons_self, restrict_nil, List.map_append, List.map_cons,
        List.map_nil])
    refine Exchange.feed _ ⟨none, ⟨⟨some (), x.1⟩, x.2⟩⟩ ⟨some (), x⟩ _ _ ?_ rfl ?_
    · rw [pair_left, hG, hy]
      exact Part.mem_map _ (Part.mem_some _)
    · refine Exchange.feed _ ⟨some (), y⟩ ⟨none, ⟨⟨some (), y.1⟩, y.2⟩⟩ _ _ ?_ rfl ?_
      · rw [pair_right, restrict_some_snoc_left, hGs]
        simp only at hr
        rw [hr]
        exact Part.mem_map _ (Part.mem_some _)
      · simpa only [List.append_assoc, List.cons_append, List.nil_append, callInternal] using hnext

/-- **Attachment along calls**: if a converter answers a sequence of calls with the transcripts
`callTranscript`, and the inside system answers their queries with the given replies, the
attachment answers the calls' outside queries with their outside replies.

CR18, Definition 3.9, printed p. 62: “Whenever α outputs (in, x), then x is given as input to
s⊥ … Whenever α outputs (out, v), then v is defined to be the output of αs”. Here every inside
query is answered, so `⊥` does not arise. -/
theorem replies_apply_of_calls {α : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y}
    (calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)))
    (hα : Replies α ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
      ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd))
    (hR : Replies R ((calls.flatMap (·.2.1)).map Prod.fst) ((calls.flatMap (·.2.1)).map Prod.snd)) :
    Replies (apply α R) (calls.map (·.1)) (calls.map (·.2.2)) := by
  -- Concatenate the internal histories, preserving their converter and system projections.
  let H : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)) →
      List (Two (Σ l, twoFam U Y l) (Σ j, X j)) :=
    fun cs => cs.flatMap fun c => callInternal ⟨⟨none, c.1.1⟩, c.1.2⟩ c.2.1
  have key : ∀ cs rest, calls = cs ++ rest →
      Induces (pair α R) resourceRoute resourceInput (cs.map (·.1)) (cs.getLast?.map (·.2.2))
        (H cs) ∧
      restrict none (H cs) = (cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst ∧
      restrict (some ()) (H cs) = (cs.flatMap (·.2.1)).map Prod.fst ∧
      Replies (apply α R) (cs.map (·.1)) (cs.map (·.2.2)) := by
    intro cs
    induction cs using List.reverseRecOn with
    | nil => intro _ _; exact ⟨Induces.nil, by simp only [List.flatMap_nil, restrict_nil,
      List.map_nil, H], by simp only [List.flatMap_nil,
      restrict_nil, List.map_nil, H], replies_nil _⟩
    | append_singleton cs c ih =>
      -- Extend the established outside history by one completed internal call.
      intro rest he
      obtain ⟨hi, hn, hs, hrep⟩ := ih (c :: rest) (by simp only [he, List.append_assoc,
        List.cons_append, List.nil_append])
      have hx := exchange_callSteps c.2.2 hα hR c.2.1 ⟨⟨none, c.1.1⟩, c.1.2⟩
        (cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2)
        (rest.flatMap fun c => callTranscript c.1 c.2.1 c.2.2) (H cs)
        (cs.flatMap (·.2.1)) (rest.flatMap (·.2.1)) (by simp only [callTranscript, he,
          List.append_assoc, List.cons_append, List.nil_append, List.flatMap_append,
          List.flatMap_cons])
        (by simp only [he, List.append_assoc, List.cons_append, List.nil_append,
          List.flatMap_append, List.flatMap_cons]) hn hs
      have hind : Induces (pair α R) resourceRoute resourceInput (cs.map (·.1) ++ [c.1])
          (some c.2.2) (H cs ++ callInternal ⟨⟨none, c.1.1⟩, c.1.2⟩ c.2.1) :=
        Induces.snoc _ _ _ _ _ _ hi hx
      refine ⟨by simpa only [List.map_append, List.map_cons, List.map_nil,
        List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, H]
        using hind, ?_, ?_, ?_⟩
      · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, restrict_append, hn, callTranscript,
        restrict_none_callInternal c.2.2, List.map_append, H]
      · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, restrict_append, hs, restrict_some_callInternal, List.map_append,
        H]
      · rw [List.map_append, List.map_append]
        refine replies_snoc.mpr ⟨hrep, ?_⟩
        rw [apply_eq]
        exact Part.eq_some_iff.mpr (mem_interconnect.mpr ⟨_, hind⟩)
  exact (key calls [] (by simp only [List.append_nil])).2.2.2

/-- The converter inputs of a call: `first`, then the inside replies. -/
lemma callSteps_map_fst (v : Σ o, V o) :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l),
      (callSteps first qs v).map Prod.fst =
        first :: qs.map fun xy => (⟨⟨some (), xy.2.1⟩, xy.2.2⟩ : Σ l, twoFam U Y l)
  | [], first => rfl
  | xy :: qs, first => by
    rw [callSteps, List.map_cons, callSteps_map_fst v qs, List.map_cons]

/-- The converter outputs of a call: the inside queries, then the outside reply. -/
lemma callSteps_map_snd (v : Σ o, V o) :
    ∀ (qs : List ((Σ j, X j) × (Σ j, Y j))) (first : Σ l, twoFam U Y l),
      (callSteps first qs v).map Prod.snd =
        (qs.map fun xy => (⟨⟨some (), xy.1.1⟩, xy.1.2⟩ : Σ l, twoFam V X l)) ++
          [⟨⟨none, v.1⟩, v.2⟩]
  | [], first => rfl
  | xy :: qs, first => by
    rw [callSteps, List.map_cons, callSteps_map_snd v qs, List.map_cons, List.cons_append]

/-- A call has the single outside input `u`. -/
lemma outsideInputs_callSteps (v : Σ o, V o) (u : Σ o, U o) (qs : List ((Σ j, X j) × (Σ j, Y j))) :
    outsideInputs ((callTranscript u qs v).map Prod.fst) = [u] := by
  rw [callTranscript, callSteps_map_fst, ← List.singleton_append, outsideInputs_append,
    outsideInputs_outside]
  suffices h : ∀ l : List ((Σ j, X j) × (Σ j, Y j)), outsideInputs (l.map fun xy =>
      (⟨⟨some (), xy.2.1⟩, xy.2.2⟩ : Σ l, twoFam U Y l)) = [] by rw [h]; rfl
  intro l
  induction l with
  | nil => rfl
  | cons xy l ih =>
    rw [List.map_cons, ← List.singleton_append, outsideInputs_append, outsideInputs_inside, ih]
    rfl

/-- The outside queries along calls are the calls' outside queries. -/
lemma outsideInputs_flatMap_callTranscript
    (calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o))) :
    outsideInputs ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst) =
      calls.map (·.1) := by
  induction calls with
  | nil => rfl
  | cons c calls ih =>
    rw [List.flatMap_cons, List.map_append, outsideInputs_append, ih, outsideInputs_callSteps,
      List.map_cons, List.singleton_append]

/-- **A rule answering a call step by step**: from an idle history, a rule that answers each
prefix of a call with the call's next output answers the call in its restriction to admissible
histories, and is idle again. -/
lemma canon_callTranscript {c : InsideOutsideSystem O J U V X Y}
    {xs : List (Σ l, twoFam U Y l)} {ys : List (Σ l, twoFam V X l)}
    (hr : Replies (canon c) xs ys) (hi : Idle (canon c) xs)
    (u : Σ o, U o) (qs : List ((Σ j, X j) × (Σ j, Y j))) (v : Σ o, V o)
    (hports : ∀ xy ∈ qs, xy.2.1 = xy.1.1)
    (hstep : ∀ k w, ((callTranscript u qs v).map Prod.snd)[k]? = some w →
      c (xs ++ ((callTranscript u qs v).map Prod.fst).take (k + 1)) = Part.some w) :
    Replies (canon c) (xs ++ (callTranscript u qs v).map Prod.fst)
        (ys ++ (callTranscript u qs v).map Prod.snd) ∧
      Idle (canon c) (xs ++ (callTranscript u qs v).map Prod.fst) := by
  set I := (callTranscript u qs v).map Prod.fst with hI
  set O' := (callTranscript u qs v).map Prod.snd with hO
  have hIe : I = ⟨⟨none, u.1⟩, u.2⟩ :: qs.map fun xy =>
      (⟨⟨some (), xy.2.1⟩, xy.2.2⟩ : Σ l, twoFam U Y l) := callSteps_map_fst v qs _
  have hOe : O' = (qs.map fun xy => (⟨⟨some (), xy.1.1⟩, xy.1.2⟩ : Σ l, twoFam V X l)) ++
      [⟨⟨none, v.1⟩, v.2⟩] := callSteps_map_snd v qs _
  have hIl : I.length = qs.length + 1 := by
    rw [hIe]
    simp only [List.length_cons, List.length_map]
  have hOl : O'.length = qs.length + 1 := by
    rw [hOe]
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, zero_add]
  have hax : Admissible c xs := (admissible_canon_iff _).mp hi.1
  -- The outputs are the inside queries followed by the outside reply.
  have hOk : ∀ k (hk : k < qs.length),
      O'[k]? = some ⟨⟨some (), qs[k].1.1⟩, qs[k].1.2⟩ := by
    intro k hk
    rw [hOe, List.getElem?_append_left (by simpa only [List.length_map] using hk),
      List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  have hOlast : O'[qs.length]? = some ⟨⟨none, v.1⟩, v.2⟩ := by
    rw [hOe, List.getElem?_append_right (by simp only [List.length_map, Std.le_refl])]
    simp only [List.length_map, tsub_self, List.length_cons, List.length_nil, zero_add,
      Order.lt_one_iff, getElem?_pos, List.getElem_cons_zero]
  have hIk : ∀ k (hk : k < qs.length), I[k + 1]? = some ⟨⟨some (), qs[k].2.1⟩, qs[k].2.2⟩ := by
    intro k hk
    rw [hIe, List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hk]
    rfl
  -- Every prefix is admissible: start outside, then answer at the inside label just queried.
  have hadm : ∀ k (hk : k < qs.length + 1), Admissible c (xs ++ I.take (k + 1)) := by
    intro k
    induction k with
    | zero =>
      -- An idle converter admits the next outside input.
      intro _
      have h1 : I.take 1 = [⟨⟨none, u.1⟩, u.2⟩] := by rw [hIe]; rfl
      rw [h1]
      refine admissible_snoc.mpr ⟨hax, fun hne => ?_, ?_⟩
      · have := hi.2.1 hne
        rwa [canon_of_admissible hax] at this
      · change admitAfter (replyLabel c xs) _
        rw [← replyLabel_canon hax]
        exact (admitAfter_of_ne hi.2.2).mpr rfl
    | succ k ih =>
      -- The reply to the preceding inside query is at that query's label.
      intro hk
      have hk' : k < qs.length := by omega
      have hprev := ih (by omega)
      have hck := hstep k _ (hOk k hk')
      rw [List.take_add_one, hIk k hk', Option.toList_some, ← List.append_assoc]
      refine admissible_snoc.mpr ⟨hprev, fun _ => by rw [hck]; trivial, ?_⟩
      change admitAfter (replyLabel c (xs ++ I.take (k + 1))) _
      rw [replyLabel_of_mem _ (Part.eq_some_iff.mp hck)]
      change (⟨some (), qs[k].2.1⟩ : Two O J) = ⟨some (), qs[k].1.1⟩
      rw [hports _ (List.getElem_mem hk')]
  have hcanon : ∀ k w, O'[k]? = some w → k < qs.length + 1 →
      canon c (xs ++ I.take (k + 1)) = Part.some w := fun k w hw hk => by
    rw [canon_of_admissible (hadm k hk), hstep k w hw]
  have hfull : I.take (qs.length + 1) = I := List.take_of_length_le (by omega)
  -- Canonicalization preserves these prefixes; the final outside reply leaves the rule idle.
  refine ⟨⟨by simp only [List.length_append, hr.1, hOl, hIl], fun i hi' hj' => ?_⟩, ?_⟩
  · by_cases hix : i < xs.length
    · rw [List.take_append_of_le_length (by omega),
        List.getElem_append_left (by rw [hr.1]; exact hix)]
      exact hr.2 i hix (by rw [hr.1]; exact hix)
    · obtain ⟨k, rfl⟩ : ∃ k, i = xs.length + k := ⟨i - xs.length, by omega⟩
      have hk : k < qs.length + 1 := by simp only [List.length_append, hIl,
        add_lt_add_iff_left, Order.lt_add_one_iff] at hi'; omega
      rw [List.take_append, List.take_of_length_le (by omega),
        show xs.length + k + 1 - xs.length = k + 1 by omega]
      refine hcanon k _ ?_ hk
      rw [← List.getElem?_eq_getElem hj', List.getElem?_append_right (by rw [hr.1]; omega),
        show xs.length + k - ys.length = k by rw [hr.1]; omega]
  · have ha : Admissible c (xs ++ I) := by
      have := hadm qs.length (by omega)
      rwa [hfull] at this
    have hl := hcanon qs.length _ hOlast (by omega)
    rw [hfull] at hl
    refine ⟨(admissible_canon_iff _).mpr ha, fun _ => by rw [hl]; trivial, fun j => ?_⟩
    rw [replyLabel_of_mem _ (Part.eq_some_iff.mp hl)]
    simp only [ne_eq, Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and,
      not_false_eq_true]

/-- **A rule answering its calls step by step**: if a rule, silent on the empty history,
answers each prefix of each call with the call's next output, its restriction to admissible
histories answers the calls. -/
theorem replies_canon_calls {c : InsideOutsideSystem O J U V X Y} (hc0 : c [] = Part.none)
    (calls : List ((Σ o, U o) × List ((Σ j, X j) × (Σ j, Y j)) × (Σ o, V o)))
    (hports : ∀ call ∈ calls, ∀ xy ∈ call.2.1, xy.2.1 = xy.1.1)
    (hstep : ∀ pre call post, calls = pre ++ call :: post → ∀ k w,
      ((callTranscript call.1 call.2.1 call.2.2).map Prod.snd)[k]? = some w →
      c ((pre.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst ++
        ((callTranscript call.1 call.2.1 call.2.2).map Prod.fst).take (k + 1)) = Part.some w) :
    Replies (canon c) ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
      ((calls.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) := by
  -- Each completed call leaves an idle admissible history for the next outside query.
  suffices key : ∀ cs rest, calls = cs ++ rest →
      Replies (canon c) ((cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst)
        ((cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.snd) ∧
      Idle (canon c) ((cs.flatMap fun c => callTranscript c.1 c.2.1 c.2.2).map Prod.fst) from
    (key calls [] (by simp only [List.append_nil])).1
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
    intro _ _
    have h0 : canon c [] = Part.none := by rw [canon_of_admissible admissible_nil, hc0]
    refine ⟨replies_nil _, admissible_nil, fun h => absurd rfl h, fun j => ?_⟩
    change replyLabel _ [] ≠ _
    simp only [replyLabel, h0, Part.not_none_dom, ↓reduceDIte, ne_eq, reduceCtorEq,
      not_false_eq_true]
  | append_singleton cs call ih =>
    intro rest he
    obtain ⟨hr, hi⟩ := ih (call :: rest) (by simp only [he, List.append_assoc,
      List.cons_append, List.nil_append])
    have hmem : call ∈ calls := by rw [he]; simp only [List.append_assoc, List.cons_append,
      List.nil_append, List.mem_append, List.mem_cons, true_or, or_true]
    have hcall := canon_callTranscript hr hi call.1 call.2.1 call.2.2 (hports call hmem)
      (hstep cs call rest (by simp only [he, List.append_assoc, List.cons_append,
        List.nil_append]))
    simpa only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_append] using hcall

end SystemAlgebra

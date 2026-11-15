module

public import RandomSystems.Converter.ConverterTensor
public import RandomSystems.Converter.ForwardingProgram
public import RandomSystems.Converter.PartialConverter

/-!
# Programs side by side

`Program.sum P Q` runs `P` on the left ports and `Q` on the right ports of a parallel
interface, from the paired state `(s, t)`. An invocation at `inl o` runs `P` from `s` on its own
(left) inside exchanges and returns `t` unchanged; an invocation at `inr k` runs `Q` from `t`
and returns `s` unchanged. The inside queries keep their side, so both programs may address one
inside system whose state is shared by `inl` and `inr` ports.

```text
inl o(u) ──► P [s] ── inl j(x) ──┐
                                  ├──► one inside system on J ⊕ L
inr k(w) ──► Q [t] ── inr l(z) ──┘
             state (s, t): an inl invocation changes only s, an inr invocation only t
```

`Program.forward J X Y` forwards each query once and returns its reply.

## Main results

* `Program.exchangesOf_leftBody`, `exchangesOf_rightBody`, `callBound_leftBody`,
  `callBound_rightBody`: a body on one side of a parallel inside interface makes its own side's
  exchanges, so it keeps its call bound.
* `Program.Bounded.sum`, `Bounded.of_sum_left`, `Bounded.of_sum_right`: the paired program makes
  at most `max b c` inside queries per invocation, and each bound of it bounds both sides.
* `Program.step_sum_liftL`, `step_sum_liftR`: a step of the paired run at a left (right) input is
  the step of `P` (`Q`), with the other side's state retained (`Mode.liftL`, `Mode.liftR`).
* `DDC.replies_ofProgram_sum_of_tensorL`: every transcript of the parallel composition
  `tensorL (ofProgramOn s P F₁) (ofProgramOn t Q F₂)` is a transcript of `P.sum Q`. Its
  admissible histories complete each invocation before the next outside query
  (`converterAdmits`), so at most one side is inside an invocation, and the paired mode pends the
  last output (`Mode.Pending`).
* `DDC.tensorL_ofProgramOn_sum`: the parallel composition of two program converters is the
  program converter of `P.sum Q` on the parallel outside domain, by
  `IsDDCFrom.eq_filterDom_of_replies_le` applied to the previous lemma.
* `DDC.filter_eq_ofProgramOn_forward`: the identity filter on `E` is the program converter of
  `Program.forward` on `E`, by the same law.

`RandomSystems.Typed.ProgramTensor` gives the corresponding typed converter equalities.
-/

@[expose] public section

namespace SystemAlgebra

namespace Program

variable
  -- `S`, `T` carry the two programs' states; `O`, `K` their outside and `J`, `L` their inside
  -- ports. `U, V` (`W, Z`) are the left (right) outside queries and replies; `X, Y`
  -- (`X', Y'`) the left (right) inside queries and replies.
  {S T O K J L : Type} {U V : O → Type} {W Z : K → Type} {X Y : J → Type} {X' Y' : L → Type}

/-! ## Exchanges of one side -/

/-- A left inside exchange `(j(x), j(y))` as an exchange at `inl j`. -/
def inlExchange (e : (Σ j, X j) × (Σ j, Y j)) :
    (Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l) :=
  (⟨.inl e.1.1, e.1.2⟩, ⟨.inl e.2.1, e.2.2⟩)

/-- A right inside exchange `(l(z), l(y))` as an exchange at `inr l`. -/
def inrExchange (e : (Σ l, X' l) × (Σ l, Y' l)) :
    (Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l) :=
  (⟨.inr e.1.1, e.1.2⟩, ⟨.inr e.2.1, e.2.2⟩)

/-- The left exchange of a parallel exchange: `some` when its query and its reply are both at
`inl`. -/
def leftExchange :
    (Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l) → Option ((Σ j, X j) × (Σ j, Y j))
  | (⟨.inl j, x⟩, ⟨.inl j', y⟩) => some (⟨j, x⟩, ⟨j', y⟩)
  | _ => none

/-- The right exchange of a parallel exchange: `some` when its query and its reply are both at
`inr`. -/
def rightExchange :
    (Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l) → Option ((Σ l, X' l) × (Σ l, Y' l))
  | (⟨.inr l, x⟩, ⟨.inr l', y⟩) => some (⟨l, x⟩, ⟨l', y⟩)
  | _ => none

/-- Exchanges whose query and reply both belong to the left interface, in order. -/
abbrev leftExchanges (h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))) :
    List ((Σ j, X j) × (Σ j, Y j)) :=
  h.filterMap leftExchange

/-- **The right exchanges** of a parallel history: its exchanges at `inr`, in order, the twin of
`leftExchanges`. -/
abbrev rightExchanges (h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))) :
    List ((Σ l, X' l) × (Σ l, Y' l)) :=
  h.filterMap rightExchange

/-- Left exchanges, embedded and projected again, are unchanged. -/
@[simp] lemma leftExchanges_map_inl (h : List ((Σ j, X j) × (Σ j, Y j))) :
    leftExchanges (X' := X') (Y' := Y') (h.map inlExchange) = h :=
  (List.filterMap_map ..).trans (List.filterMap_some ..)

/-- Right exchanges, embedded and projected again, are unchanged. -/
@[simp] lemma rightExchanges_map_inr (h : List ((Σ l, X' l) × (Σ l, Y' l))) :
    rightExchanges (X := X) (Y := Y) (h.map inrExchange) = h :=
  (List.filterMap_map ..).trans (List.filterMap_some ..)

/-! ## Projecting a single invocation -/

section Bodies

variable {A B : Type}

/-- The exchanges of a left body are left exchanges made by `f` itself. -/
lemma exchangesOf_leftBody {f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)} (g : A → B)
    {h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))}
    (hc : ExchangesOf (fun h => (f (leftExchanges h)).map g fun q => ⟨.inl q.1, q.2⟩) h) :
    h = (leftExchanges h).map inlExchange ∧ ExchangesOf f (leftExchanges h) := by
  -- Each recorded query was asked by the body after the previous exchanges: it is a query
  -- `j(x)` of `f` tagged `inl`, answered at `inl j`.
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | append_singleton h e ih =>
    obtain ⟨hh, hf⟩ := ih (exchangesOf_of_append hc)
    obtain ⟨hq, hl⟩ := exchangesOf_last hc
    obtain ⟨⟨l, x⟩, ⟨l', y⟩⟩ := e
    change Sum.map _ _ (f (leftExchanges h)) = _ at hq
    cases hp : f (leftExchanges h) with
    | inl a => rw [hp] at hq; cases hq
    | inr q =>
      rw [hp] at hq
      obtain ⟨j, x₀⟩ := q
      cases hq
      cases hl
      have hleft : leftExchanges (X' := X') (Y' := Y') (h ++ [(⟨.inl j, x₀⟩, ⟨.inl j, y⟩)]) =
          leftExchanges h ++ [(⟨j, x₀⟩, ⟨j, y⟩)] := List.filterMap_append
      rw [hleft, List.map_append, ← hh]
      -- The new exchange answers the query of `f` after its earlier exchanges.
      refine ⟨rfl, fun i hi => ?_⟩
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [List.take_append_of_le_length hi.le, List.getElem_append_left hi]
        exact hf i hi
      · rw [List.take_left' rfl, List.getElem_append_right (le_refl _)]
        simpa using hp

/-- The exchanges of a right body are right exchanges made by `f` itself. -/
lemma exchangesOf_rightBody {f : List ((Σ l, X' l) × (Σ l, Y' l)) → A ⊕ (Σ l, X' l)}
    (g : A → B) {h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))}
    (hc : ExchangesOf (fun h => (f (rightExchanges h)).map g fun q => ⟨.inr q.1, q.2⟩) h) :
    h = (rightExchanges h).map inrExchange ∧ ExchangesOf f (rightExchanges h) := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | append_singleton h e ih =>
    obtain ⟨hh, hf⟩ := ih (exchangesOf_of_append hc)
    obtain ⟨hq, hl⟩ := exchangesOf_last hc
    obtain ⟨⟨l, x⟩, ⟨l', y⟩⟩ := e
    change Sum.map _ _ (f (rightExchanges h)) = _ at hq
    cases hp : f (rightExchanges h) with
    | inl a => rw [hp] at hq; cases hq
    | inr q =>
      rw [hp] at hq
      obtain ⟨j, x₀⟩ := q
      cases hq
      cases hl
      have hright : rightExchanges (X := X) (Y := Y) (h ++ [(⟨.inr j, x₀⟩, ⟨.inr j, y⟩)]) =
          rightExchanges h ++ [(⟨j, x₀⟩, ⟨j, y⟩)] := List.filterMap_append
      rw [hright, List.map_append, ← hh]
      refine ⟨rfl, fun i hi => ?_⟩
      rw [List.length_append, List.length_singleton] at hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [List.take_append_of_le_length hi.le, List.getElem_append_left hi]
        exact hf i hi
      · rw [List.take_left' rfl, List.getElem_append_right (le_refl _)]
        simpa using hp

/-- A left body makes the queries of `f`, so it keeps the call bound of `f`. -/
lemma callBound_leftBody {b : ℕ} {f : List ((Σ j, X j) × (Σ j, Y j)) → A ⊕ (Σ j, X j)}
    (g : A → B) (hf : CallBound b f) :
    CallBound b (X := Sum.rec X X') (Y := Sum.rec Y Y')
      (fun h => (f (leftExchanges h)).map g fun q => ⟨.inl q.1, q.2⟩) := by
  intro h q hc hq
  obtain ⟨hh, hcf⟩ := exchangesOf_leftBody g hc
  change Sum.map _ _ (f (leftExchanges h)) = _ at hq
  cases hp : f (leftExchanges h) with
  | inl a => rw [hp] at hq; cases hq
  | inr q' =>
    rw [hh, List.length_map]
    exact hf _ q' hcf hp

/-- A right body makes the queries of `f`, so it keeps the call bound of `f`. -/
lemma callBound_rightBody {b : ℕ} {f : List ((Σ l, X' l) × (Σ l, Y' l)) → A ⊕ (Σ l, X' l)}
    (g : A → B) (hf : CallBound b f) :
    CallBound b (X := Sum.rec X X') (Y := Sum.rec Y Y')
      (fun h => (f (rightExchanges h)).map g fun q => ⟨.inr q.1, q.2⟩) := by
  intro h q hc hq
  obtain ⟨hh, hcf⟩ := exchangesOf_rightBody g hc
  change Sum.map _ _ (f (rightExchanges h)) = _ at hq
  cases hp : f (rightExchanges h) with
  | inl a => rw [hp] at hq; cases hq
  | inr q' =>
    rw [hh, List.length_map]
    exact hf _ q' hcf hp

end Bodies

/-! ## The program -/

/-- **Two programs side by side.** From `(s, t)`, an invocation at `inl o` answers as `P` from
`s` on the left exchanges, `(s', v) ↦ ((s', t), v)`, and tags its queries `inl`; an invocation
at `inr k` answers as `Q` from `t`, `(t', z) ↦ ((s, t'), z)`, and tags its queries `inr`. -/
def sum
    -- `P` serves the left ports and `Q` the right ports.
    (P : Program S O J U V X Y) (Q : Program T K L W Z X' Y') :
    Program (S × T) (O ⊕ K) (J ⊕ L) (Sum.rec U W) (Sum.rec V Z) (Sum.rec X X')
      (Sum.rec Y Y')
  | st, .inl o, u, h =>
    (P st.1 o u (leftExchanges h)).map (fun a => ((a.1, st.2), a.2)) fun q => ⟨.inl q.1, q.2⟩
  | st, .inr k, w, h =>
    (Q st.2 k w (rightExchanges h)).map (fun a => ((st.1, a.1), a.2)) fun q => ⟨.inr q.1, q.2⟩

variable {P : Program S O J U V X Y} {Q : Program T K L W Z X' Y'}

/-- The exchanges of a left invocation are left exchanges made by `P` itself: the invocation is
the left body of `P` from `s` (`exchangesOf_leftBody`). -/
lemma exchangesOf_sum_inl {st : S × T} {o : O} {u : U o}
    {h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))}
    (hc : (P.sum Q).Consistent st (.inl o) u h) :
    h = (leftExchanges h).map inlExchange ∧ P.Consistent st.1 o u (leftExchanges h) :=
  exchangesOf_leftBody (f := P st.1 o u) (fun a => ((a.1, st.2), a.2)) hc

/-- The exchanges of a right invocation are right exchanges made by `Q` itself: the invocation
is the right body of `Q` from `t` (`exchangesOf_rightBody`). -/
lemma exchangesOf_sum_inr {st : S × T} {k : K} {w : W k}
    {h : List ((Σ l, Sum.rec X X' l) × (Σ l, Sum.rec Y Y' l))}
    (hc : (P.sum Q).Consistent st (.inr k) w h) :
    h = (rightExchanges h).map inrExchange ∧ Q.Consistent st.2 k w (rightExchanges h) :=
  exchangesOf_rightBody (f := Q st.2 k w) (fun a => ((st.1, a.1), a.2)) hc

/-- Side by side, an invocation makes at most `max b c` inside queries: each invocation is a
body of one side (`callBound_leftBody`, `callBound_rightBody`). -/
lemma Bounded.sum {b c : ℕ} (hP : P.Bounded b) (hQ : Q.Bounded c) :
    (P.sum Q).Bounded (max b c) := by
  rintro st (o | k) u h q hc hq
  · exact (callBound_leftBody (X' := X') (Y' := Y') (f := P st.1 o u)
      (fun a => ((a.1, st.2), a.2)) (hP st.1 o u) h q hc hq).trans_le (le_max_left b c)
  · exact (callBound_rightBody (X := X) (Y := Y) (f := Q st.2 k u)
      (fun a => ((st.1, a.1), a.2)) (hQ st.2 k u) h q hc hq).trans_le (le_max_right b c)

/-- `P`'s own exchanges, embedded on the left, are exchanges of the paired body at `inl o`. -/
lemma exchangesOf_sum_of_inl {st : S × T} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} (hc : P.Consistent st.1 o u h) :
    (P.sum Q).Consistent st (.inl o) u (h.map inlExchange) := by
  intro i hi
  rw [List.length_map] at hi
  obtain ⟨hq, hl⟩ := hc i hi
  refine ⟨?_, by simp only [List.getElem_map, inlExchange, hl]⟩
  change Sum.map _ _ (P st.1 o u (leftExchanges ((h.map inlExchange).take i))) = _
  rw [← List.map_take, leftExchanges_map_inl, hq]
  simp only [Sum.map_inr, List.getElem_map, inlExchange]

/-- `Q`'s own exchanges, embedded on the right, are exchanges of the paired body at `inr k`. -/
lemma exchangesOf_sum_of_inr {st : S × T} {k : K} {w : W k}
    {h : List ((Σ l, X' l) × (Σ l, Y' l))} (hc : Q.Consistent st.2 k w h) :
    (P.sum Q).Consistent st (.inr k) w (h.map inrExchange) := by
  intro i hi
  rw [List.length_map] at hi
  obtain ⟨hq, hl⟩ := hc i hi
  refine ⟨?_, by simp only [List.getElem_map, inrExchange, hl]⟩
  change Sum.map _ _ (Q st.2 k w (rightExchanges ((h.map inrExchange).take i))) = _
  rw [← List.map_take, rightExchanges_map_inr, hq]
  simp only [Sum.map_inr, List.getElem_map, inrExchange]

/-- A bound of the paired program bounds `P`, given any right state `t`. -/
lemma Bounded.of_sum_left {n : ℕ} (t : T) (hn : (P.sum Q).Bounded n) : P.Bounded n := by
  intro s o u h q hc hq
  have := hn (s, t) (.inl o) u _ _ (exchangesOf_sum_of_inl (Q := Q) (st := (s, t)) hc)
    (by change Sum.map _ _ (P s o u (leftExchanges (h.map inlExchange))) = _
        rw [leftExchanges_map_inl, hq]; rfl)
  rwa [List.length_map] at this

/-- A bound of the paired program bounds `Q`, given any left state `s`. -/
lemma Bounded.of_sum_right {n : ℕ} (s : S) (hn : (P.sum Q).Bounded n) : Q.Bounded n := by
  intro t k w h q hc hq
  have := hn (s, t) (.inr k) w _ _ (exchangesOf_sum_of_inr (P := P) (st := (s, t)) hc)
    (by change Sum.map _ _ (Q t k w (rightExchanges (h.map inrExchange))) = _
        rw [rightExchanges_map_inr, hq]; rfl)
  rwa [List.length_map] at this

/-! ## Runs side by side -/

/-- `P`'s mode with the right state `t` retained. -/
def Mode.liftL (t : T) : Mode S O J U X Y →
    Mode (S × T) (O ⊕ K) (J ⊕ L) (Sum.rec U W) (Sum.rec X X') (Sum.rec Y Y')
  | .idle s => .idle (s, t)
  | .busy o s u h q => .busy (.inl o) (s, t) u (h.map inlExchange) ⟨.inl q.1, q.2⟩

/-- `Q`'s mode with the left state `s` retained. -/
def Mode.liftR (s : S) : Mode T K L W X' Y' →
    Mode (S × T) (O ⊕ K) (J ⊕ L) (Sum.rec U W) (Sum.rec X X') (Sum.rec Y Y')
  | .idle t => .idle (s, t)
  | .busy k t w h q => .busy (.inr k) (s, t) w (h.map inrExchange) ⟨.inr q.1, q.2⟩

/-- A left input in `P`'s alphabet as an input at `inl`. -/
def inlInput : (Σ l, twoFam U Y l) → (Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l)
  | ⟨⟨none, o⟩, u⟩ => ⟨⟨none, .inl o⟩, u⟩
  | ⟨⟨some (), j⟩, y⟩ => ⟨⟨some (), .inl j⟩, y⟩

/-- A right input in `Q`'s alphabet as an input at `inr`. -/
def inrInput : (Σ l, twoFam W Y' l) → (Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l)
  | ⟨⟨none, k⟩, w⟩ => ⟨⟨none, .inr k⟩, w⟩
  | ⟨⟨some (), l⟩, y⟩ => ⟨⟨some (), .inr l⟩, y⟩

/-- A left output in `P`'s alphabet as an output at `inl`. -/
def inlOutput : (Σ l, twoFam V X l) → (Σ l, twoFam (Sum.rec V Z) (Sum.rec X X') l)
  | ⟨⟨none, o⟩, v⟩ => ⟨⟨none, .inl o⟩, v⟩
  | ⟨⟨some (), j⟩, x⟩ => ⟨⟨some (), .inl j⟩, x⟩

/-- A right output in `Q`'s alphabet as an output at `inr`. -/
def inrOutput : (Σ l, twoFam Z X' l) → (Σ l, twoFam (Sum.rec V Z) (Sum.rec X X') l)
  | ⟨⟨none, k⟩, z⟩ => ⟨⟨none, .inr k⟩, z⟩
  | ⟨⟨some (), l⟩, x⟩ => ⟨⟨some (), .inr l⟩, x⟩

/-- **A left step** of the paired run is `P`'s step, with `t` retained. -/
lemma step_sum_liftL (t : T) (m : Mode S O J U X Y) (z : Σ l, twoFam U Y l) :
    (P.sum Q).step (m.liftL t) (inlInput z) =
      (P.step m z).map fun p => (p.1.liftL t, inlOutput p.2) := by
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
  · -- idle, outside query: one invocation of `P` on no exchanges.
    simp only [Mode.liftL, inlInput, step, Option.map_some]
    unfold emit
    cases hp : P s i v [] <;>
      simp only [sum, List.filterMap_nil, hp, Sum.map_inl, inlOutput, Sum.map_inr, List.map_nil]
  · rfl
  · rfl
  · -- busy, inside reply: the reply continues the same invocation iff it is at `q.1`.
    simp only [Mode.liftL, inlInput, step, Sum.inl.injEq]
    by_cases hi : i = q.1
    · subst hi
      have hh : h.map inlExchange ++ [(⟨Sum.inl q.1, q.2⟩, ⟨Sum.inl q.1, v⟩)] =
          (h ++ [(q, (⟨q.1, v⟩ : Σ j, Y j))]).map (inlExchange (X' := X') (Y' := Y')) := by
        simp only [List.map_append, List.map_cons, inlExchange, List.map_nil]
      simp only [↓reduceIte, hh, Option.map_some]
      unfold emit
      cases hp : P s o u (h ++ [(q, ⟨q.1, v⟩)]) <;>
        simp only [sum, leftExchanges_map_inl, hp, Sum.map_inl, inlOutput, Sum.map_inr]
    · simp only [Sum.inl.injEq, hi, ↓reduceIte, Option.map_none]

/-- **A right step** of the paired run is `Q`'s step, with `s` retained. -/
lemma step_sum_liftR (s : S) (m : Mode T K L W X' Y') (z : Σ l, twoFam W Y' l) :
    (P.sum Q).step (m.liftR s) (inrInput z) =
      (Q.step m z).map fun p => (p.1.liftR s, inrOutput p.2) := by
  rcases m with t | ⟨k, t, w, h, q⟩ <;> rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
  · simp only [Mode.liftR, inrInput, step, Option.map_some]
    unfold emit
    cases hp : Q t i v [] <;>
      simp only [sum, List.filterMap_nil, hp, Sum.map_inl, inrOutput, Sum.map_inr, List.map_nil]
  · rfl
  · rfl
  · simp only [Mode.liftR, inrInput, step, Sum.inr.injEq]
    by_cases hi : i = q.1
    · subst hi
      have hh : h.map inrExchange ++ [(⟨Sum.inr q.1, q.2⟩, ⟨Sum.inr q.1, v⟩)] =
          (h ++ [(q, (⟨q.1, v⟩ : Σ l, Y' l))]).map (inrExchange (X := X) (Y := Y)) := by
        simp only [List.map_append, List.map_cons, inrExchange, List.map_nil]
      simp only [↓reduceIte, hh, Option.map_some]
      unfold emit
      cases hp : Q t k w (h ++ [(q, ⟨q.1, v⟩)]) <;>
        simp only [sum, rightExchanges_map_inr, hp, Sum.map_inl, inrOutput, Sum.map_inr]
    · simp only [Sum.inr.injEq, hi, ↓reduceIte, Option.map_none]

/-- The mode `m` pends exactly the inside query of the last output `last`: an idle mode follows
no output or an outside reply; a busy mode follows its pending query. -/
def Mode.Pending {S O J : Type} {U V : O → Type} {X Y : J → Type} :
    Mode S O J U X Y → Option (Σ l, twoFam V X l) → Prop
  | .idle _, last => ∀ j x, last ≠ some ⟨⟨some (), j⟩, x⟩
  | .busy _ _ _ _ q, last => last = some ⟨⟨some (), q.1⟩, q.2⟩

/-- A step leaves a mode pending its own output. -/
lemma Mode.pending_of_step {S O J : Type} {U V : O → Type} {X Y : J → Type}
    {P : Program S O J U V X Y} {m m' : Mode S O J U X Y} {z : Σ l, twoFam U Y l}
    {y : Σ l, twoFam V X l} (hs : P.step m z = some (m', y)) : m'.Pending (some y) := by
  -- Every step output is an `emit`: an outside reply with an idle mode, or a pending query.
  rcases m with s | ⟨o, s, u, h, q⟩ <;> rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩ <;>
    simp only [step, Option.some.injEq, reduceCtorEq] at hs
  · revert hs; unfold emit; split <;> rintro ⟨⟩ <;>
      simp only [Mode.Pending, ne_eq, Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and,
        not_false_eq_true, implies_true]
  · split_ifs at hs
    revert hs; unfold emit; split <;> rintro ⟨⟩ <;>
      simp only [Mode.Pending, ne_eq, Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and,
        not_false_eq_true, implies_true]

/-- Pending is preserved by lifting to the left side. -/
lemma Mode.pending_liftL {m : Mode S O J U X Y} {y : Σ l, twoFam V X l} (t : T)
    (hm : m.Pending (some y)) :
    Mode.Pending (m.liftL (K := K) (L := L) (W := W) (X' := X') (Y' := Y') t)
      (some (inlOutput (Z := Z) y)) := by
  rcases m with _ | ⟨o, s, u, h, q⟩ <;> rcases y with ⟨⟨_ | ⟨⟩, i⟩, v⟩ <;>
    simp_all only [Mode.Pending, ne_eq, Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and,
        not_false_eq_true, implies_true, Mode.liftL, inlOutput, heq_eq_eq, true_and, not_and,
        Sum.forall, Sum.inl.injEq, IsEmpty.forall_iff, and_self]

/-- Pending is preserved by lifting to the right side. -/
lemma Mode.pending_liftR {m : Mode T K L W X' Y'} {y : Σ l, twoFam Z X' l} (s : S)
    (hm : m.Pending (some y)) :
    Mode.Pending (m.liftR (O := O) (J := J) (U := U) (X := X) (Y := Y) s)
      (some (inrOutput (V := V) y)) := by
  rcases m with _ | ⟨k, t, w, h, q⟩ <;> rcases y with ⟨⟨_ | ⟨⟩, i⟩, v⟩ <;>
    simp_all only [Mode.Pending, ne_eq, Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and,
        not_false_eq_true, implies_true, Mode.liftR, inrOutput, heq_eq_eq, true_and, not_and,
        Sum.forall, IsEmpty.forall_iff, Sum.inr.injEq, and_self]

end Program

/-! ## Forwarding -/

namespace Program

variable {J : Type} {X Y : J → Type}

open Classical in
/-- Forward the query `j(x)` once and return the reply at `j`; the state is trivial. -/
noncomputable def forward (J : Type) (X Y : J → Type) : Program Unit J J X Y X Y
  | _, j, x, [] => .inr ⟨j, x⟩
  | _, j, x, (_, ⟨j', y⟩) :: _ => if hj : j' = j then .inl ((), hj ▸ y) else .inr ⟨j, x⟩

/-- Forwarding calls only before any exchange of its invocation, hence at most once. -/
lemma forward_bounded : (forward J X Y).Bounded 1 :=
  bounded_one_of_history_eq_nil fun _ j x h q hc hq => by
    rcases h with _ | ⟨e, h⟩
    · rfl
    · -- The first exchange answers the forwarded `j(x)` at `j`, so the body replies.
      exfalso
      obtain ⟨hq₀, hl⟩ := hc 0 (by simp only [List.length_cons, lt_add_iff_pos_left,
          Order.lt_add_one_iff, zero_le])
      obtain ⟨⟨j₁, x₁⟩, ⟨j₂, y⟩⟩ := e
      simp only [List.take_zero, forward, List.getElem_cons_zero] at hq₀ hl
      cases hl
      cases hq₀
      simp only [forward, ↓reduceDIte, reduceCtorEq] at hq

end Program

namespace DDC

open Program

variable {S T O K J L : Type} {U V : O → Type} {W Z : K → Type} {X Y : J → Type}
  {X' Y' : L → Type}
  {P : Program S O J U V X Y} {Q : Program T K L W Z X' Y'} {s : S} {t : T}
  {F₁ : List (Σ o, U o) → Prop} {F₂ : List (Σ k, W k) → Prop}

/-- The joint input relabeling `tIn` sends `inlInput a` to the left. -/
lemma tIn_eq_left {z : Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l} {a}
    (hz : tIn z = ⟨none, a⟩) : z = inlInput a := by
  rcases z with ⟨⟨_ | ⟨⟩, o | k⟩, v⟩ <;> simp only [tIn] at hz <;> cases hz <;> rfl

/-- The joint input relabeling `tIn` sends `inrInput a` to the right. -/
lemma tIn_eq_right {z : Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l} {a}
    (hz : tIn z = ⟨some (), a⟩) : z = inrInput a := by
  rcases z with ⟨⟨_ | ⟨⟩, o | k⟩, v⟩ <;> simp only [tIn] at hz <;> cases hz <;> rfl

/-- `tOut` on the left is the left output embedding. -/
lemma tOut_left (y : Σ l, twoFam V X l) :
    tOut (V := Sum.rec V Z) (Xi := Sum.rec X X') ⟨none, y⟩ = inlOutput y := by
  rcases y with ⟨⟨_ | ⟨⟩, i⟩, v⟩ <;> rfl

/-- `tOut` on the right is the right output embedding. -/
lemma tOut_right (y : Σ l, twoFam Z X' l) :
    tOut (V := Sum.rec V Z) (Xi := Sum.rec X X') ⟨some (), y⟩ = inrOutput y := by
  rcases y with ⟨⟨_ | ⟨⟩, i⟩, v⟩ <;> rfl

/-- The run invariant of `replies_ofProgram_sum_of_tensorL`: the paired transcript so far, and a
paired mode `m` pending the last output, which lifts the busy side's mode with the other side
idle. -/
lemma replies_ofProgram_sum_of_tensorL_run
    {h : List ((Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l) ×
      (Σ l, twoFam (Sum.rec V Z) (Sum.rec X X') l))}
    (hr : Replies (tensorL (U := Sum.rec U W) (V := Sum.rec V Z) (Xi := Sum.rec X X')
      (Yi := Sum.rec Y Y') (ofProgramOn s P F₁) (ofProgramOn t Q F₂))
      (h.map Prod.fst) (h.map Prod.snd)) :
    Replies (DDC.ofProgram (s, t) (P.sum Q)) (h.map Prod.fst) (h.map Prod.snd) ∧
      ∃ m, (P.sum Q).after (s, t) (h.map Prod.fst) = some m ∧
        m.Pending (h.map Prod.snd).getLast? ∧
        ((∃ mP t', P.after s (hA (h.map Prod.fst)) = some mP ∧
            Q.after t (hB (h.map Prod.fst)) = some (.idle t') ∧ m = mP.liftL t') ∨
          (∃ mQ s', P.after s (hA (h.map Prod.fst)) = some (.idle s') ∧
            Q.after t (hB (h.map Prod.fst)) = some mQ ∧ m = mQ.liftR s')) := by
  induction h using List.reverseRecOn with
  | nil =>
    -- Both programs start idle; nothing was output.
    exact ⟨replies_nil _, .idle (s, t), rfl, by simp only [Mode.Pending, List.map_nil,
        List.getLast?_nil, ne_eq, reduceCtorEq, not_false_eq_true, implies_true],
      Or.inl ⟨.idle s, t, rfl, rfl, rfl⟩⟩
  | append_singleton h e ih =>
    obtain ⟨z, y⟩ := e
    -- The prefix is a transcript; the last exchange is admitted after it and answered by the
    -- raw parallel converter.
    have split := replies_tensorL_split hr
    simp only [List.map_append, List.map_singleton] at hr split ⊢
    obtain ⟨hr₀, -⟩ := replies_snoc.mp hr
    obtain ⟨hW, m, hm, hpend, hcase⟩ := ih hr₀
    have hadm : converterAdmits h z := split.1 h (z, y) [] rfl
    have hraw : tensorRaw (U := Sum.rec U W) (V := Sum.rec V Z) (Xi := Sum.rec X X')
        (Yi := Sum.rec Y Y') (ofProgramOn s P F₁) (ofProgramOn t Q F₂)
        (h.map Prod.fst ++ [z]) = Part.some y := (replies_snoc.mp split.2.1).2
    rcases hz : tIn z with ⟨_ | ⟨⟩, a⟩
    · -- A left input `z = inlInput a`, answered by `P` at its own history `hA ++ [a]`.
      rw [tensorRaw_left hz] at hraw
      obtain ⟨y', hy', rfl⟩ : ∃ y', y' ∈ ofProgramOn s P F₁ (hA (h.map Prod.fst) ++ [a]) ∧
          y = tOut ⟨none, y'⟩ := by
        have := Part.mem_map_iff _ |>.mp (hraw ▸ Part.mem_some y)
        obtain ⟨y', hy', he⟩ := this
        exact ⟨y', hy', he.symm⟩
      obtain ⟨mP₀, mP', hmP₀, hstep⟩ :=
        (mem_ofProgram_snoc s P _ a y').mp ((filterDom_mem_iff _ _ _ _).mp hy').2
      -- The right side is idle: otherwise the last output pends a right query, which admits
      -- only a right reply.
      obtain ⟨t', hQidle, rfl⟩ : ∃ t', Q.after t (hB (h.map Prod.fst)) = some (.idle t') ∧
          m = mP₀.liftL t' := by
        rcases hcase with ⟨mP, t', hmP, hQ', rfl⟩ | ⟨mQ, s', hP', hQ', rfl⟩
        · exact ⟨t', hQ', by rw [hmP₀] at hmP; cases hmP; rfl⟩
        · rcases mQ with t' | ⟨k, t', w, e, q⟩
          · rw [hmP₀] at hP'; cases hP'
            exact ⟨t', hQ', rfl⟩
          · -- A pending right query admits only its reply, not the left input `z`.
            exfalso
            simp only [Mode.Pending, Mode.liftR] at hpend
            have hlast : h.getLast?.map (fun e => e.2.1) = some ⟨some (), .inr q.1⟩ := by
              have := congrArg (Option.map Sigma.fst) hpend
              rwa [List.getLast?_map, Option.map_map] at this
            unfold converterAdmits at hadm
            rw [hlast, tIn_eq_left hz] at hadm
            rcases a with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩ <;> simp only [admitAfter, inlInput, Sigma.mk.injEq,
                reduceCtorEq, false_and, heq_eq_eq, and_false] at hadm
      have hstepW := step_sum_liftL (P := P) (Q := Q) t' mP₀ a
      rw [hstep, Option.map_some] at hstepW
      rw [tIn_eq_left hz]
      refine ⟨replies_snoc.mpr ⟨hW, ?_⟩, mP'.liftL t', ?_, ?_, Or.inl ⟨mP', t', ?_, ?_, rfl⟩⟩
      · rw [tOut_left]
        exact Part.eq_some_iff.mpr ((mem_ofProgram_snoc _ _ _ _ _).mpr ⟨_, _, hm, hstepW⟩)
      · rw [Program.after_snoc, hm, Option.bind_some, hstepW, Option.map_some]
      · rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, tOut_left]
        exact Mode.pending_liftL t' (Mode.pending_of_step hstep)
      · rw [← tIn_eq_left hz, hA_left hz, Program.after_snoc, hmP₀, Option.bind_some, hstep,
          Option.map_some]
      · rw [← tIn_eq_left hz, hB_left hz, hQidle]
    · -- A right input `z = inrInput a`: the same argument with the sides exchanged.
      rw [tensorRaw_right hz] at hraw
      obtain ⟨y', hy', rfl⟩ : ∃ y', y' ∈ ofProgramOn t Q F₂ (hB (h.map Prod.fst) ++ [a]) ∧
          y = tOut ⟨some (), y'⟩ := by
        obtain ⟨y', hy', he⟩ := Part.mem_map_iff _ |>.mp (hraw ▸ Part.mem_some y)
        exact ⟨y', hy', he.symm⟩
      obtain ⟨mQ₀, mQ', hmQ₀, hstep⟩ :=
        (mem_ofProgram_snoc t Q _ a y').mp ((filterDom_mem_iff _ _ _ _).mp hy').2
      obtain ⟨s', hPidle, rfl⟩ : ∃ s', P.after s (hA (h.map Prod.fst)) = some (.idle s') ∧
          m = mQ₀.liftR s' := by
        rcases hcase with ⟨mP, t', hmP, hQ', rfl⟩ | ⟨mQ, s', hP', hQ', rfl⟩
        · rcases mP with s' | ⟨o, s', u, e, q⟩
          · rw [hmQ₀] at hQ'; cases hQ'
            exact ⟨s', hmP, rfl⟩
          · exfalso
            simp only [Mode.Pending, Mode.liftL] at hpend
            have hlast : h.getLast?.map (fun e => e.2.1) = some ⟨some (), .inl q.1⟩ := by
              have := congrArg (Option.map Sigma.fst) hpend
              rwa [List.getLast?_map, Option.map_map] at this
            unfold converterAdmits at hadm
            rw [hlast, tIn_eq_right hz] at hadm
            rcases a with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩ <;> simp only [admitAfter, inrInput, Sigma.mk.injEq,
                reduceCtorEq, false_and, heq_eq_eq, and_false] at hadm
        · exact ⟨s', hP', by rw [hmQ₀] at hQ'; cases hQ'; rfl⟩
      have hstepW := step_sum_liftR (P := P) (Q := Q) s' mQ₀ a
      rw [hstep, Option.map_some] at hstepW
      rw [tIn_eq_right hz]
      refine ⟨replies_snoc.mpr ⟨hW, ?_⟩, mQ'.liftR s', ?_, ?_, Or.inr ⟨mQ', s', ?_, ?_, rfl⟩⟩
      · rw [tOut_right]
        exact Part.eq_some_iff.mpr ((mem_ofProgram_snoc _ _ _ _ _).mpr ⟨_, _, hm, hstepW⟩)
      · rw [Program.after_snoc, hm, Option.bind_some, hstepW, Option.map_some]
      · rw [List.getLast?_append, List.getLast?_singleton, Option.some_or, tOut_right]
        exact Mode.pending_liftR s' (Mode.pending_of_step hstep)
      · rw [← tIn_eq_right hz, hA_right hz, hPidle]
      · rw [← tIn_eq_right hz, hB_right hz, Program.after_snoc, hmQ₀, Option.bind_some, hstep,
          Option.map_some]

/-- **Parallel transcripts are transcripts of the paired program.** -/
lemma replies_ofProgram_sum_of_tensorL
    {h : List ((Σ l, twoFam (Sum.rec U W) (Sum.rec Y Y') l) ×
      (Σ l, twoFam (Sum.rec V Z) (Sum.rec X X') l))}
    (hr : Replies (tensorL (U := Sum.rec U W) (V := Sum.rec V Z) (Xi := Sum.rec X X')
      (Yi := Sum.rec Y Y') (ofProgramOn s P F₁) (ofProgramOn t Q F₂))
      (h.map Prod.fst) (h.map Prod.snd)) :
    Replies (DDC.ofProgram (s, t) (P.sum Q)) (h.map Prod.fst) (h.map Prod.snd) :=
  (replies_ofProgram_sum_of_tensorL_run hr).1

/-- **Program converters side by side form a program converter.** On outside domains `F₁`,
`F₂` with nonempty-prefix closure, the parallel composition of the converters of `P` and `Q` is
the converter of `P.sum Q` on the parallel domain. -/
theorem tensorL_ofProgramOn_sum {b c : ℕ} (hP : P.Bounded b) (hQ : Q.Bounded c)
    {E₁ : List (Σ j, X j) → Prop} {E₂ : List (Σ l, X' l) → Prop}
    -- `ha`, `hc` certify the two converters; their bounds are the programs' bounds.
    (ha : IsDDCFrom E₁ F₁ b (ofProgramOn s P F₁)) (hc : IsDDCFrom E₂ F₂ c (ofProgramOn t Q F₂))
    -- `hF₁`, `hF₂`: the outside domains are closed under nonempty prefixes.
    (hF₁ : ∀ {p h}, p <+: h → p ≠ [] → F₁ h → F₁ p)
    (hF₂ : ∀ {p h}, p <+: h → p ≠ [] → F₂ h → F₂ p) :
    tensorL (U := Sum.rec U W) (V := Sum.rec V Z) (Xi := Sum.rec X X') (Yi := Sum.rec Y Y')
        (ofProgramOn s P F₁) (ofProgramOn t Q F₂) =
      ofProgramOn (s, t) (P.sum Q) (parallelInputs (F := Sum.rec U W) F₁ F₂) :=
  -- The parallel composition is a certified DDC below the responsive paired program, hence its
  -- outside-domain restriction, which is `ofProgramOn` by definition.
  (IsDDCFrom.tensorL ha hc).eq_filterDom_of_replies_le
    (ofProgram_isResponsiveDDC (s := (s, t)) (hP.sum hQ)).isDDC
    (parallelInputs_nonempty_prefix hF₁ hF₂).2
    fun xs ys hr => by
      -- A transcript `(xs, ys)` is the history `xs.zip ys` of input/output pairs.
      have hfst : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [hr.1])
      have hsnd : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [hr.1])
      have := replies_ofProgram_sum_of_tensorL (h := xs.zip ys) (by rwa [hfst, hsnd])
      rwa [hfst, hsnd] at this

/-- Identity transcripts are transcripts of the forwarding program, whose mode pends the last
output and is busy only with the single forwarded query. -/
lemma replies_ofProgram_forward_of_idConverter
    {h : List ((Σ l, twoFam X Y l) × (Σ l, twoFam Y X l))}
    (hr : Replies (idConverter J X Y) (h.map Prod.fst) (h.map Prod.snd)) :
    Replies (DDC.ofProgram () (forward J X Y)) (h.map Prod.fst) (h.map Prod.snd) ∧
      ∃ m, (forward J X Y).after () (h.map Prod.fst) = some m ∧
        m.Pending (h.map Prod.snd).getLast? ∧
        (m = .idle () ∨ ∃ j x, m = .busy j () x [] ⟨j, x⟩) := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨replies_nil _, .idle (), rfl, by simp only [Mode.Pending, List.map_nil,
      List.getLast?_nil, ne_eq, reduceCtorEq, not_false_eq_true, implies_true], Or.inl rfl⟩
  | append_singleton h e ih =>
    obtain ⟨z, y⟩ := e
    -- `idConverter = canon (forwardAll J X Y)`: admitted inputs, answered by `forwardAll`.
    obtain ⟨hadm, hraw⟩ :=
      (replies_canon_iff _ (by simp only [SilentAtEmpty, forwardAll, List.getLast?_nil,
          Part.not_none_dom, not_false_eq_true]) (h ++ [(z, y)])).mp hr
    simp only [List.map_append, List.map_singleton] at hr hraw ⊢
    obtain ⟨hW, m, hm, hpend, hmode⟩ := ih (replies_snoc.mp hr).1
    have hz : converterAdmits h z := hadm h (z, y) [] rfl
    have hy := (replies_snoc.mp hraw).2
    -- Admission reads the label of the last output, which the mode pends.
    have hlast : h.getLast?.map (fun e => e.2.1) = (h.map Prod.snd).getLast?.map Sigma.fst := by
      rw [List.getLast?_map, Option.map_map]
      rfl
    unfold converterAdmits at hz
    rw [hlast] at hz
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
    · -- An outside query `j(v)` is forwarded as the inside query `j(v)`; the mode was idle.
      rw [forwardAll_snoc_outer] at hy
      cases Part.some_injective hy
      obtain rfl : m = .idle () := by
        rcases hmode with rfl | ⟨j', x', rfl⟩
        · rfl
        · simp only [Mode.Pending] at hpend
          rw [hpend] at hz
          simp only [admitAfter, Option.map_some, Sigma.mk.injEq, reduceCtorEq, heq_eq_eq,
              false_and] at hz
      refine ⟨replies_snoc.mpr ⟨hW, Part.eq_some_iff.mpr
          ((mem_ofProgram_snoc _ _ _ _ _).mpr ⟨_, _, hm, rfl⟩)⟩,
        .busy j () v [] ⟨j, v⟩, ?_, by simp only [Mode.Pending, List.getLast?_append,
            List.getLast?_singleton, List.getLast?_map, Option.some_or], Or.inr ⟨j, v, rfl⟩⟩
      rw [Program.after_snoc, hm]
      rfl
    · -- An inside reply `j(v)` returns as the outside reply `j(v)`; the mode pended `j`.
      rw [forwardAll_snoc_inner] at hy
      cases Part.some_injective hy
      obtain ⟨j', x', rfl⟩ : ∃ j' x', m = .busy j' () x' [] ⟨j', x'⟩ := by
        rcases hmode with rfl | h'
        · exfalso
          simp only [Mode.Pending] at hpend
          rcases hl : (h.map Prod.snd).getLast? with _ | ⟨⟨_ | ⟨⟨⟩⟩, i⟩, w⟩
          · rw [hl] at hz; simp only [admitAfter, Option.map_none, reduceCtorEq] at hz
          · rw [hl] at hz; simp only [admitAfter, Option.map_some, reduceCtorEq] at hz
          · exact hpend i w hl
        · exact h'
      obtain rfl : j = j' := by
        simp only [Mode.Pending] at hpend
        rw [hpend] at hz
        simpa only [admitAfter, Option.map_some, Sigma.mk.injEq, heq_eq_eq, true_and] using hz
      have hstep : (forward J X Y).step (.busy j () x' [] ⟨j, x'⟩) ⟨⟨some (), j⟩, v⟩ =
          some (.idle (), ⟨⟨none, j⟩, v⟩) := by
        simp only [step, ↓reduceIte, emit, forward, List.nil_append, ↓reduceDIte]
      refine ⟨replies_snoc.mpr ⟨hW, Part.eq_some_iff.mpr
          ((mem_ofProgram_snoc _ _ _ _ _).mpr ⟨_, _, hm, hstep⟩)⟩, .idle (), ?_,
        by simp only [Mode.Pending, List.getLast?_append, List.getLast?_singleton,
            List.getLast?_map, Option.some_or, ne_eq, Option.some.injEq, Sigma.mk.injEq,
            reduceCtorEq, heq_eq_eq, false_and, not_false_eq_true, implies_true], Or.inl rfl⟩
      rw [Program.after_snoc, hm, Option.bind_some, hstep, Option.map_some]

/-- **The identity filter is the forwarding program** on the same domain. -/
lemma filter_eq_ofProgramOn_forward {E : List (Σ j, X j) → Prop}
    -- `hE`: `E` excludes `[]` and is closed under nonempty prefixes.
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    (DDC.filter (Y := Y) (fun h => h = [] ∨ E h) (prefix_or_nil hE.2)).1 =
      ofProgramOn () (forward J X Y) E :=
  (isDDCFrom_filter hE).eq_filterDom_of_replies_le
    (ofProgram_isResponsiveDDC (s := ()) forward_bounded).isDDC hE.2
    fun xs ys hr => by
      -- The filter's transcripts are identity transcripts, indexed by `xs.zip ys`.
      change Replies (filterDom (fun h => outsideInputs h = [] ∨ E (outsideInputs h))
        (idConverter J X Y)) xs ys at hr
      have hid := hr.mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
      have hfst : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [hr.1])
      have hsnd : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [hr.1])
      have := (replies_ofProgram_forward_of_idConverter (h := xs.zip ys)
        (by rwa [hfst, hsnd])).1
      rwa [hfst, hsnd] at this

/-- The forwarding program certifies the identity domain map `E → E`. -/
lemma isDDCFrom_ofProgramOn_forward {E : List (Σ j, X j) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    IsDDCFrom E E 1 (ofProgramOn () (forward J X Y) E) :=
  filter_eq_ofProgramOn_forward hE ▸ isDDCFrom_filter hE

end DDC

end SystemAlgebra

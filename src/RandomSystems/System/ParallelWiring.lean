import RandomSystems.System.Basic

/-!
# Componentwise wiring of parallel systems

A family `s k : System (X k) (Y k)`, `k : K`, each wired by a route `route k : Y k → B k ⊕ X k`
and an injection `inj k : A k → X k`. The tagged route sends a reply `⟨k, y⟩` out as `⟨k, b⟩`
or back in as `⟨k, x⟩`, so every internal exchange stays in its component:

```text
  ⟨k,a⟩ ──▶ ┌───────┐ ──▶ ⟨k,b⟩      route k y = inl b: reply at the outside
            │  s k  │ ◀─┐
            └───────┘ ──┘ ⟨k,x⟩      route k y = inr x: fed back, tag k kept
```

Wiring the components separately is wiring their parallel composition:

  `parAll (k ↦ interconnect (s k) (route k) (inj k))`
  `  = interconnect (parAll s) (parallelRoute route) (parallelInj inj)`.

The hypothesis is convergence of every component on every outside history. `K` need not be
finite, and no off-tree representatives are identified.

## Main definitions

* `parallelRoute route`, `parallelInj inj`: the tagged route and injection
* `pairParallel`: `Two (Σ k, A k) (Σ k, C k) ≃ Σ k, Two (A k) (C k)`

## Main results

* `parAll_interconnect_all`: componentwise wiring is wiring of the parallel family
* `trim_parAll_trim`: `trim (parAll (k ↦ trim (s k))) = trim (parAll s)`
* `pair_parAll`: `pair (parAll s) (parAll t)` is `parAll (k ↦ pair (s k) (t k))` regrouped

Source: Jost, Thesis, printed p. 17, views finite disjoint-interface resources as one; the
wiring law is derived here from `Induces`.
-/

namespace SystemAlgebra


variable {K : Type} {A B X Y : K → Type}

open Classical in
/-- The tagged route: `parallelRoute route ⟨k, y⟩ = (route k y).map ⟨k, ·⟩ ⟨k, ·⟩`, an outside
reply `inl b` as `inl ⟨k, b⟩`, a feedback `inr x` as `inr ⟨k, x⟩`. -/
def parallelRoute (route : ∀ k, Y k → B k ⊕ X k) :
    (Σ k, Y k) → (Σ k, B k) ⊕ (Σ k, X k)
  | ⟨k, y⟩ => (route k y).map (Sigma.mk k) (Sigma.mk k)

open Classical in
/-- The tagged injection: `parallelInj inj ⟨k, a⟩ = ⟨k, inj k a⟩`. -/
def parallelInj (inj : ∀ k, A k → X k) : (Σ k, A k) → Σ k, X k
  | ⟨k, a⟩ => ⟨k, inj k a⟩

variable {s : ∀ k, System (X k) (Y k)} {route : ∀ k, Y k → B k ⊕ X k}
  {inj : ∀ k, A k → X k}

open Classical in
/-- An exchange of component `k` lifts to the parallel family: if `s k` runs from
`T = (H ++ [⟨k, x⟩])|k` to `T'` with result `o`, then `parAll s` runs from `H ++ [⟨k, x⟩]` to
some `H'` with result `o.map ⟨k, ·⟩`, `H'|k = T'` and `H'|j = H|j` for `j ≠ k`. -/
lemma Exchange.parallel_at {k : K} {T o T'} (l : Exchange (s k) (route k) T o T') :
    ∀ (H : List (Σ k, X k)) (x : X k), restrict k (H ++ [⟨k, x⟩]) = T →
      ∃ H', Exchange (parAll s) (parallelRoute route) (H ++ [⟨k, x⟩])
          (o.map (Sigma.mk k)) H' ∧
        restrict k H' = T' ∧
        ∀ j, j ≠ k → restrict j H' = restrict j H := by
  -- Induction on the component exchange; `parAll s` answers the last input `⟨k, x⟩` by
  -- `s k` on `H|k ++ [x] = T`, so each constructor lifts with the same reply.
  induction l with
  | silent T hd =>
    -- `s k` is silent at `T`, hence `parAll s` at `H ++ [⟨k, x⟩]`; `H' = H ++ [⟨k, x⟩]`.
    rintro H x rfl
    refine ⟨_, Exchange.silent _ ?_, rfl, ?_⟩
    · rw [parAll_snoc]
      change ¬ (s k (restrict k H ++ [x])).Dom
      simpa only [restrict_append, restrict_cons_self, restrict_nil] using hd
    -- The appended input is tagged `k`, so `(H ++ [⟨k, x⟩])|j = H|j`.
    · intro j hj
      simp only [restrict_append, restrict_cons_ne (Ne.symm hj), restrict_nil,
        List.append_nil]
  | out T y b hy hr =>
    -- `s k` replies `y` routed out as `b`; `parAll s` replies `⟨k, y⟩`, routed out as `⟨k, b⟩`.
    rintro H x rfl
    refine ⟨_, Exchange.out _ ⟨k, y⟩ _ ?_ ?_, rfl, ?_⟩
    · rw [parAll_snoc]
      exact Part.mem_map _ (by simpa only [restrict_append, restrict_cons_self,
        restrict_nil] using hy)
    · simp only [parallelRoute, hr, Sum.map_inl]
    · intro j hj
      simp only [restrict_append, restrict_cons_ne (Ne.symm hj), restrict_nil,
        List.append_nil]
  | feed T y x' o T' hy hr _ ih =>
    -- `s k` replies `y` fed back as `x'`; the tagged feed `⟨k, x'⟩` keeps the tag, so the
    -- induction hypothesis continues from `H ++ [⟨k, x⟩]` with the next input `x'`.
    rintro H x rfl
    obtain ⟨H', l, hk, hj⟩ := ih (H ++ [⟨k, x⟩]) x' (by simp only [List.append_assoc,
      List.cons_append, List.nil_append, restrict_append, restrict_cons_self, restrict_nil])
    refine ⟨H', Exchange.feed _ ⟨k, y⟩ ⟨k, x'⟩ _ _ ?_ ?_ l, hk, ?_⟩
    · rw [parAll_snoc]
      exact Part.mem_map _ (by simpa only [restrict_append, restrict_cons_self,
        restrict_nil] using hy)
    · simp only [parallelRoute, hr, Sum.map_inr]
    -- `H'|j = (H ++ [⟨k, x⟩])|j = H|j`.
    · intro j hne
      rw [hj j hne]
      simp only [restrict_append, restrict_cons_ne (Ne.symm hne), restrict_nil,
        List.append_nil]

open Classical in
/-- **Componentwise wiring is wiring of the parallel family.** If every component wiring
converges on every outside history, then

  `parAll (k ↦ interconnect (s k) (route k) (inj k))`
  `  = interconnect (parAll s) (parallelRoute route) (parallelInj inj)`.

`K` need not be finite. Proof invariant: at each outside prefix `u`, the joint wiring induces
some `(o, H)` and component `k` induces `H|k` from `u|k`. Jost, Thesis, printed p. 17, views
finite disjoint-interface resources as one; this equation is derived from `Induces`. -/
theorem parAll_interconnect_all (hc : ∀ k, Converges (s k) (route k) (inj k)) :
    parAll (fun k => interconnect (s k) (route k) (inj k)) =
      interconnect (parAll s) (parallelRoute route) (parallelInj inj) := by
  -- Invariant at `u`: `Induces (parAll s) … u o H`, `∀ k, Induces (s k) … (u|k) _ (H|k)`,
  -- and the left side replies `c` at `u` iff `o = some c`.
  have key : ∀ u : List (Σ k, A k), ∃ o H,
      Induces (parAll s) (parallelRoute route) (parallelInj inj) u o H ∧
      (∀ k, ∃ ok, Induces (s k) (route k) (inj k) (restrict k u) ok (restrict k H)) ∧
      ∀ c, c ∈ parAll (fun k => interconnect (s k) (route k) (inj k)) u ↔
        o = some c := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      -- Nothing asked: no reply, empty internal history in every view.
      exact ⟨none, [], Induces.nil, fun _ => ⟨none, Induces.nil⟩, by simp only [parAll_nil,
        Part.notMem_none, reduceCtorEq, implies_true]⟩
    | append_singleton u a ih =>
      -- New outside input `⟨k, a⟩`. Convergence of `s k` on `u|k ++ [a]` gives a run that
      -- splits as the run on `u|k`, which by determinism ends at the stored `H|k`, and one
      -- exchange from `H|k ++ [inj k a]`:
      --
      --   u|k ++ [a] ⊢ s k :  Induces (u|k) _ (H|k)  ;  Exchange (H|k ++ [inj k a]) ok T
      --   u ++ [⟨k,a⟩] ⊢ parAll s :  Induces u o H  ;  Exchange (H ++ [⟨k, inj k a⟩]) _ H'
      obtain ⟨o, H, r, hrs, -⟩ := ih
      obtain ⟨k, a⟩ := a
      obtain ⟨ok, T, rk⟩ := hc k (restrict k u ++ [a])
      obtain ⟨_, _, rk0, lk⟩ := induces_snoc_iff.mp rk
      obtain ⟨_, rkH⟩ := hrs k
      obtain ⟨-, rfl⟩ := rk0.det rkH
      -- Lift the exchange: `H'|k = T`, `H'|j = H|j` for `j ≠ k`.
      obtain ⟨H', l, hk, hj⟩ := lk.parallel_at H (inj k a) (by simp only [restrict_append,
        restrict_cons_self, restrict_nil])
      refine ⟨_, H', Induces.snoc _ _ _ _ _ _ r l, ?_, ?_⟩
      -- Component `k` induces `H'|k = T` from `(u ++ [⟨k, a⟩])|k`; any other component
      -- sees neither the new input nor a new internal message.
      · intro j
        by_cases he : j = k
        · subst j
          refine ⟨ok, ?_⟩
          simpa only [restrict_append, restrict_cons_self, restrict_nil, hk] using rk
        · obtain ⟨oj, rj⟩ := hrs j
          refine ⟨oj, ?_⟩
          simpa only [restrict_append, restrict_cons_ne (Ne.symm he), restrict_nil,
            List.append_nil, hj j he] using rj
      · -- The left side at `u ++ [⟨k, a⟩]` is `⟨k, ·⟩` of the wired `s k` at `u|k ++ [a]`,
        -- whose reply is `ok`, determined by `rk`; the joint result is `ok.map ⟨k, ·⟩`.
        intro c
        rw [parAll_snoc, Part.mem_map_iff]
        constructor
        · rintro ⟨b, hb, rfl⟩
          obtain ⟨H'', rb⟩ := mem_interconnect.mp hb
          rw [(rk.det rb).1]
          rfl
        · intro he
          cases ok with
          | none => cases he
          | some b => cases he; exact ⟨b, mem_of_induces_some rk, rfl⟩
  -- Right side replies `c` at `u` iff some run induces `some c`; by determinism every run is
  -- the constructed one, so this is `o = some c`, the left side's reply.
  apply system_ext
  intro u c
  obtain ⟨o, H, r, -, ho⟩ := key u
  rw [ho, mem_interconnect]
  constructor
  · rintro rfl
    exact ⟨H, r⟩
  · rintro ⟨H', r'⟩
    exact (r.det r').1

open Classical in
/-- Trimming each component does not change the trimmed parallel family:
`trim (parAll (k ↦ trim (s k))) = trim (parAll s)`. -/
lemma trim_parAll_trim {A B : K → Type} (s : ∀ k, System (A k) (B k)) :
    trim (parAll fun k => trim (s k)) = trim (parAll s) := by
  -- `trim (s k) ≈ₛ s k` for each `k`, so `parAll` of either family has the same reachable
  -- histories and replies there; both are silent at `[]`, so their trims are equal.
  exact (EqOnReachable.parAll fun k => trim_behEq (s k)).trim_eq
    Part.not_none_dom Part.not_none_dom


section Pair

variable {C D : K → Type}

open Classical in
/-- A pair of tagged families as a tagged family of pairs:
`⟨none, ⟨k, a⟩⟩ ↦ ⟨k, ⟨none, a⟩⟩` and `⟨some (), ⟨k, c⟩⟩ ↦ ⟨k, ⟨some (), c⟩⟩`. -/
def pairParallel : Two (Σ k, A k) (Σ k, C k) ≃ Σ k, Two (A k) (C k) where
  toFun
    | ⟨none, ⟨k, a⟩⟩ => ⟨k, ⟨none, a⟩⟩
    | ⟨some (), ⟨k, c⟩⟩ => ⟨k, ⟨some (), c⟩⟩
  invFun
    | ⟨k, ⟨none, a⟩⟩ => ⟨none, ⟨k, a⟩⟩
    | ⟨k, ⟨some (), c⟩⟩ => ⟨some (), ⟨k, c⟩⟩
  left_inv := by rintro ⟨(_ | ⟨⟩), ⟨k, a⟩⟩ <;> rfl
  right_inv := by rintro ⟨k, ⟨(_ | ⟨⟩), a⟩⟩ <;> rfl

open Classical in
/-- Regrouping commutes with the left projection: `(h.map pairParallel)|k|none = h|none|k`. -/
lemma restrict_pairParallel_none (k : K) (h : List (Two (Σ k, A k) (Σ k, C k))) :
    restrict none (restrict k (h.map pairParallel)) = restrict k (restrict none h) := by
  -- Induction on `h`; each message is kept by both sides iff it is left and tagged `k`.
  -- Four cases on the head: left or right, tag `k` or not.
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [pairParallel, Equiv.coe_fn_mk] at ih
    rcases a with ⟨(_ | ⟨⟩), ⟨j, a⟩⟩ <;> by_cases he : j = k
    all_goals first | subst j | skip
    all_goals simp only [pairParallel, List.map_cons, Equiv.coe_fn_mk]
    · simpa only [restrict_cons_self] using congrArg (List.cons a) ih
    · simpa only [restrict_cons_ne he, restrict_cons_self] using ih
    · simpa only [restrict_cons_self, restrict_cons_ne (Option.some_ne_none _)] using ih
    · simpa only [restrict_cons_ne he, restrict_cons_ne (Option.some_ne_none _)] using ih

open Classical in
/-- Regrouping commutes with the right projection:
`(h.map pairParallel)|k|some () = h|some ()|k`. -/
lemma restrict_pairParallel_some (k : K) (h : List (Two (Σ k, A k) (Σ k, C k))) :
    restrict (some ()) (restrict k (h.map pairParallel)) =
      restrict k (restrict (some ()) h) := by
  -- Induction on `h`; each message is kept by both sides iff it is right and tagged `k`.
  -- Four cases on the head: left or right, tag `k` or not.
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [pairParallel, Equiv.coe_fn_mk] at ih
    rcases a with ⟨(_ | ⟨⟩), ⟨j, a⟩⟩ <;> by_cases he : j = k
    all_goals first | subst j | skip
    all_goals simp only [pairParallel, List.map_cons, Equiv.coe_fn_mk]
    · simpa only [restrict_cons_self, restrict_cons_ne (Ne.symm (Option.some_ne_none _))] using ih
    · simpa only [restrict_cons_ne he, restrict_cons_ne (Ne.symm (Option.some_ne_none _))] using ih
    · simpa only [restrict_cons_self] using congrArg (List.cons a) ih
    · simpa only [restrict_cons_ne he, restrict_cons_self] using ih

open Classical in
/-- **A pair of parallel families is a parallel family of pairs**, after the explicit
regrouping `pairParallel`:

  `pair (parAll s) (parAll t) = relabel (parAll (k ↦ pair (s k) (t k))) pairParallel
    pairParallel.symm`. -/
lemma pair_parAll (s : ∀ k, System (A k) (B k)) (t : ∀ k, System (C k) (D k)) :
    pair (parAll s) (parAll t) =
      relabel (parAll fun k => pair (s k) (t k)) pairParallel pairParallel.symm := by
  -- Compare at `[]` (both silent) and after each last input.
  apply parAll_ext
  · simp only [pair, parAll_nil, relabel, List.map_nil, Part.map_none]
  · intro h o a
    cases o with
    | none =>
      -- Last input `⟨none, ⟨k, a⟩⟩`: both sides answer by `s k` at `h|none|k ++ [a]`,
      -- the right side via `(h.map pairParallel)|k|none`, equal by regrouping.
      obtain ⟨k, a⟩ := a
      simp only [pair_left, parAll_snoc, relabel, List.map_append, List.map_singleton]
      change _ = ((parAll fun k => pair (s k) (t k))
        (h.map pairParallel ++ [⟨k, ⟨none, a⟩⟩])).map pairParallel.symm
      rw [parAll_snoc, pair_left, restrict_pairParallel_none,
        Part.map_map, Part.map_map, Part.map_map]
      rfl
    | some o =>
      -- Last input `⟨some (), ⟨k, a⟩⟩`: both sides answer by `t k` at `h|some ()|k ++ [a]`.
      cases o
      obtain ⟨k, a⟩ := a
      simp only [pair_right, parAll_snoc, relabel, List.map_append, List.map_singleton]
      change _ = ((parAll fun k => pair (s k) (t k))
        (h.map pairParallel ++ [⟨k, ⟨some (), a⟩⟩])).map pairParallel.symm
      rw [parAll_snoc, pair_right, restrict_pairParallel_some,
        Part.map_map, Part.map_map, Part.map_map]
      rfl

end Pair

end SystemAlgebra

module

public import RandomSystems.Converter.ProgramTensor
public import RandomSystems.Converter.ProbProgramAttachment

/-!
# Paired programs against one probabilistic automaton

`Program.sum P Q` runs `P` on the left and `Q` on the right ports of one inside automaton
`step` on `J ⊕ L`, whose state `r` both sides share. One combined step of `Program.probCombine`
moves only the queried side's program state:

```text
((s, t), r) ── inl o(u) ──► P from (s, r) against step at inl ──► (((s', t), r'), v)
((s, t), r) ── inr k(w) ──► Q from (t, r) against step at inr ──► (((s, t'), r'), z)
```

* `probInvoke_sum_inl`, `probInvoke_sum_inr`: an invocation of the paired program is the
  invocation of the queried side against the same inside step, at every number of queries left.
* `probCombine_sum_inl`, `probCombine_sum_inr`: the same for one combined step, for any bounds
  of the paired program and of the queried side (`Program.probCombine_congr`).
* `probCombine_forward`: forwarding answers `j(x)` by one inside step and keeps its trivial state.

`leftStep` and `rightStep` keep only the active program state beside the resource state.
The inside step is arbitrary: a query at either side may change `r`, which the next query at
the other side reads.
-/

@[expose] public section

namespace SystemAlgebra.Program

open Probability.Distribution

variable
  -- The two programs and their port alphabets, as in `Program.sum`.
  {S T O K J L R : Type} {U V : O → Type} {W Z : K → Type} {X Y : J → Type} {X' Y' : L → Type}
  {P : Program S O J U V X Y} {Q : Program T K L W Z X' Y'}
  -- `step` is the joint inside transition on `J ⊕ L`.
  (step : ProbStep R (J ⊕ L) (Sum.rec X X') (Sum.rec Y Y'))

/-- A left invocation of the paired program is `P`'s invocation against the left ports of the
same inside state; `t` is returned unchanged. -/
lemma probInvoke_sum_inl (s : S) (t : T) (o : O) (u : U o) (n : ℕ) (r : R)
    (h : List ((Σ j, X j) × (Σ j, Y j))) :
    (P.sum Q).probInvoke step (s, t) (.inl o) u n r (h.map inlExchange) =
      fTransform (fun p => (((p.1.1, t), p.1.2), p.2))
        (P.probInvoke (fun r j x => step r (.inl j) x) s o u n r h) := by
  induction n generalizing r h with
  | zero =>
    simp only [probInvoke, sum, leftExchanges_map_inl]
    cases P s o u h <;> simp only [Sum.map_inl, fTransform_single, Sum.map_inr, fTransform_zero]
  | succ n ih =>
    simp only [probInvoke, sum, leftExchanges_map_inl]
    cases hq : P s o u h with
    | inl a => simp only [Sum.map_inl, fTransform_single]
    | inr q =>
      -- The inside step at `inl q.1` is the left step, its reply tagged `inl`.
      simp only [Sum.map_inr, ProbStep.outcome, bindK_fTransform, fTransform_bindK,
        Function.comp_def, ProbStep.tagged]
      congr 1
      funext p
      have hh : h.map inlExchange ++ [(⟨Sum.inl q.1, q.2⟩, ⟨Sum.inl q.1, p.2⟩)] =
          (h ++ [(q, (⟨q.1, p.2⟩ : Σ j, Y j))]).map (inlExchange (X' := X') (Y' := Y')) := by
        simp only [List.map_append, List.map_cons, inlExchange, List.map_nil]
      rw [hh, ih]

/-- A right invocation of the paired program is `Q`'s invocation against the right ports of the
same inside state; `s` is returned unchanged. -/
lemma probInvoke_sum_inr (s : S) (t : T) (k : K) (w : W k) (n : ℕ) (r : R)
    (h : List ((Σ l, X' l) × (Σ l, Y' l))) :
    (P.sum Q).probInvoke step (s, t) (.inr k) w n r (h.map inrExchange) =
      fTransform (fun p => (((s, p.1.1), p.1.2), p.2))
        (Q.probInvoke (fun r l x => step r (.inr l) x) t k w n r h) := by
  induction n generalizing r h with
  | zero =>
    simp only [probInvoke, sum, rightExchanges_map_inr]
    cases Q t k w h <;> simp only [Sum.map_inl, fTransform_single, Sum.map_inr, fTransform_zero]
  | succ n ih =>
    simp only [probInvoke, sum, rightExchanges_map_inr]
    cases hq : Q t k w h with
    | inl a => simp only [Sum.map_inl, fTransform_single]
    | inr q =>
      simp only [Sum.map_inr, ProbStep.outcome, bindK_fTransform, fTransform_bindK,
        Function.comp_def, ProbStep.tagged]
      congr 1
      funext p
      have hh : h.map inrExchange ++ [(⟨Sum.inr q.1, q.2⟩, ⟨Sum.inr q.1, p.2⟩)] =
          (h ++ [(q, (⟨q.1, p.2⟩ : Σ l, Y' l))]).map (inrExchange (X := X) (Y := Y)) := by
        simp only [List.map_append, List.map_cons, inrExchange, List.map_nil]
      rw [hh, ih]

/-- **Left step, right state retained**: `((s, t), r)` at `inl o` moves as `P` from `(s, r)`
against the left ports, with `t` unchanged. Any bound `n` of the paired program and any bound `b`
of `P` give the same combined step. -/
lemma probCombine_sum_inl {b n : ℕ} (hb : P.Bounded b) (hn : (P.sum Q).Bounded n)
    (s : S) (t : T) (r : R) (o : O) (u : U o) :
    (P.sum Q).probCombine step hn ((s, t), r) (.inl o) u =
      (P.probCombine (fun r j x => step r (.inl j) x) hb (s, r) o u).map
        fun p => (((p.1.1, t), p.1.2), p.2) := by
  rw [probCombine_congr (fun r j x => step r (.inl j) x) hb (hn.of_sum_left t)]
  exact Subtype.ext (by
    simpa only [probCombine_val, ProbDist.map_val, List.map_nil] using
      probInvoke_sum_inl (Q := Q) step s t o u n r [])

/-- **Right step, left state retained**: `((s, t), r)` at `inr k` moves as `Q` from `(t, r)`
against the right ports, with `s` unchanged. -/
lemma probCombine_sum_inr {c n : ℕ} (hc : Q.Bounded c) (hn : (P.sum Q).Bounded n)
    (s : S) (t : T) (r : R) (k : K) (w : W k) :
    (P.sum Q).probCombine step hn ((s, t), r) (.inr k) w =
      (Q.probCombine (fun r l x => step r (.inr l) x) hc (t, r) k w).map
        fun p => (((s, p.1.1), p.1.2), p.2) := by
  rw [probCombine_congr (fun r l x => step r (.inr l) x) hc (hn.of_sum_right s)]
  exact Subtype.ext (by
    simpa only [probCombine_val, ProbDist.map_val, List.map_nil] using
      probInvoke_sum_inr (P := P) step s t k w n r [])

/-- **Forwarding** answers `j(x)` by one inside step `step r j x`, keeping the trivial state:
`((), r) ↦ ((), r')` with the inside reply. -/
lemma probCombine_forward {J : Type} {X Y : J → Type}
    -- `step` is the inside transition; `hb` bounds forwarding by `b ≥ 1` inside queries.
    (step : ProbStep R J X Y) {b : ℕ} (hb : (forward J X Y).Bounded b) (hpos : 0 < b)
    (r : R) (j : J) (x : X j) :
    (forward J X Y).probCombine step hb ((), r) j x =
      (step r j x).map fun p => (((), p.1), p.2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_lt hpos
  apply Subtype.ext
  -- One forwarded query; its reply at `j` completes the invocation.
  have hfwd : ∀ (y : Y j), forward J X Y () j x [(⟨j, x⟩, ⟨j, y⟩)] = .inl ((), y) := by
    intro y
    simp only [forward, ↓reduceDIte]
  simp only [probCombine_val, ProbDist.map_val, Nat.zero_add, probInvoke, forward,
    ProbStep.outcome, ProbStep.tagged, bindK_fTransform, Function.comp_def]
  rw [← bindK_single_comp]
  congr 1
  funext p
  rw [List.nil_append, probInvoke_inl (hfwd p.2)]

/-- Run `P` at the left ports. A right query updates the same resource state `r` and returns
its reply, carrying the program state `s` unchanged. -/
noncomputable def leftStep (P : Program S O J U V X Y) {b : ℕ} (hb : P.Bounded b)
    (step : ProbStep R (J ⊕ L) (Sum.rec X X') (Sum.rec Y Y')) :
    ProbStep (S × R) (O ⊕ L) (Sum.rec U X') (Sum.rec V Y')
  | sr, .inl o, u => P.probCombine (fun r j x => step r (.inl j) x) hb sr o u
  | (s, r), .inr l, x => (step r (.inr l) x).map fun p => ((s, p.1), p.2)

/-- Run `Q` at the right ports. A left query updates the shared resource state and preserves
the program state. The state order is again (program, resource). -/
noncomputable def rightStep (Q : Program T K L W Z X' Y') {c : ℕ} (hc : Q.Bounded c)
    (step : ProbStep R (J ⊕ L) (Sum.rec X X') (Sum.rec Y Y')) :
    ProbStep (T × R) (J ⊕ K) (Sum.rec X W) (Sum.rec Y Z)
  | (t, r), .inl j, x => (step r (.inl j) x).map fun p => ((t, p.1), p.2)
  | tr, .inr k, w => Q.probCombine (fun r l x => step r (.inr l) x) hc tr k w

end SystemAlgebra.Program

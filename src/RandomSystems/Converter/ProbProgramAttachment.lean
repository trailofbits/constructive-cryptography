module

public import RandomSystems.Converter.ProgramAttachment
public import RandomSystems.Converter.ConverterAttachment
public import RandomSystems.System.ProbAutomaton

/-!
# Attaching a program to a probabilistic automaton

`Program.probCombine` runs a program `P` against an inside transition law `step`. Each
invocation returns a law of the two new states and the outside reply:

```text
     u              x
  ──────► [P, s] ──────► [step, r]      (r', y) ← step r x, fresh per inside query
  ◄──────        ◄──────
     v              y
  Program.probCombine: (s, r), u ↦ law of ((s', r'), v)
  Proof table: independent t(c) ← drawLaw rec c; t retained in (r, k, t)
```

This is the combined system `C(F)` of [1, §3.3, p. 9: "then the combined random system is C(F)"].
`PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton` identifies it with converter attachment.

The proof represents fresh transitions by one retained table of independent draws, indexed
by the step number, reachable state and query: a random automaton in the sense of
[1, Definition 2, p. 6: "specifying the internal randomness and the initial state"].
`ProbStep.recording` runs `step` and appends each draw to a record. Given that record,
`ProbStep.drawKernel` fixes recorded cells and independently samples the others.
`ProbStep.simulatesAt_drawStep` shows that reading the table simulates recording;
`ProbStep.simulatesAt_forget` shows that forgetting the record simulates it too.
Together they give `RandomSystem.ofProbAutomaton_eq_drawStep` on inputs of at most `m ≤ L` queries.

For attachment, take `L = m + b * n`, covering both the inside domain bound `m` and the
`b * n` calls made by `n` program invocations. `attach_ofDDC_ofProgramOn_ofDeterministic`
and `Program.ofDeterministic_combine` identify the program against the table's point steps.
`RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation` transports both simulations
through the program, returning from the table through the record to `step` from `init`.
`ProbStep.drawKernel_val` exposes the raw cell law for the simulation calculation.

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology —
   EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002. Page numbers refer to the preprint.
-/

@[expose] public section

namespace SystemAlgebra

open Probability Probability.Distribution

-- `S`, `R` carry program and inside states; `O`, `J` carry outside and inside port labels.
-- `U o`, `V o` are outside query/reply types; `X j`, `Y j` are inside query/reply types.
variable {S O J R : Type} {U V : O → Type} {X Y : J → Type}

/-! ### Programs against probabilistic steps -/

namespace Program

-- `P` chooses the next inside query or final outside reply; `stepR` draws an inside transition.
variable (P : Program S O J U V X Y) (stepR : ProbStep R J X Y)

/-- **An invocation against a probabilistic step**: the body runs from the exchanges `h`, the
automaton in the state `r` answering its inside queries, with at most `n` more of them; the law
of the next states and of the reply.

```text
  body(h) = reply (s', v)   ⟶   point law at ((s', r), v)
  body(h) = query q         ⟶   (r', y) ← step r q;  continue from r' with h · (q, y)
```
-/
noncomputable def probInvoke (s : S) (o : O) (u : U o) :
    ℕ → R → List ((Σ j, X j) × (Σ j, Y j)) → Distribution ((S × R) × V o)
  -- One invocation: the outside query `u` enters the body, whose inside queries the automaton
  -- answers with fresh steps from `r`, until the body replies `v`:
  --
  --     u ──►┌──────┐── q₁, q₂, … ──►┌──────────┐
  --          │ P(s) │                │ stepR, r │   r ─► r₁ ─► r₂ ─► …   (fresh draws)
  --     v ◄──└──────┘◄── y₁, y₂, … ──└──────────┘
  --
  -- No query left: a reply is its point law, a further query gets no mass.
  | 0, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr _ => 0
  -- Queries left: a further query `q` is answered by a draw `(r', y)` of the step from `r`.
  | n + 1, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr q => bindK (stepR.outcome r q) fun p => probInvoke s o u n p.1 (h ++ [(q, p.2)])

variable {P stepR}

/-- When the body replies, the invocation is the point law of its reply. -/
lemma probInvoke_inl {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {a : S × V o} (ha : P s o u h = .inl a) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u n r h = Finsupp.single ((a.1, r), a.2) 1 := by
  -- Whatever the number of queries left, the first case of the definition.
  cases n <;> simp [probInvoke, ha]

/-- When the body asks with no query left, the invocation has no mass. -/
lemma probInvoke_zero_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (r : R) :
    P.probInvoke stepR s o u 0 r h = 0 := by
  -- The second case of the definition with no query left.
  simp [probInvoke, hq]

/-- When the body asks `q`, the invocation draws a step and continues. -/
lemma probInvoke_succ_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u (n + 1) r h =
      bindK (stepR.outcome r q) fun p => P.probInvoke stepR s o u n p.1 (h ++ [(q, p.2)]) := by
  -- The second case of the definition with a query left.
  simp [probInvoke, hq]

/-- An invocation is a nonnegative law. -/
lemma probInvoke_nonNeg (s : S) (o : O) (u : U o) :
    ∀ n r h, (P.probInvoke stepR s o u n r h).NonNeg := by
  -- Induction on the number of queries left: point laws, zero, or mixtures of nonnegative laws.
  intro n
  induction n with
  | zero =>
    intro r h
    cases hq : P s o u h with
    -- the body replies: a point law
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    -- the body asks with no query left: the zero law
    | inr q => rw [probInvoke_zero_inr hq]; exact fun _ => le_rfl
  | succ n ih =>
    intro r h
    cases hq : P s o u h with
    -- the body replies: a point law
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    | inr q =>
      -- the body asks `q`: the step's draws, a nonnegative law, mixing nonnegative
      -- continuations (induction)
      rw [probInvoke_succ_inr hq]
      exact bindK_nonNeg (stepR.outcome_nonNeg r q) fun _ => ih _ _

/-- **A bounded program completes each invocation** against a probabilistic step. -/
lemma probInvoke_weight {b : ℕ} (hP : P.Bounded b) (s : S) (o : O) (u : U o) :
    ∀ n r h, P.Consistent s o u h → b ≤ n + h.length →
      (P.probInvoke stepR s o u n r h).weight = 1 := by
  -- Induct on the remaining queries, preserving `b ≤ n + h.length`.
  intro n
  induction n with
  | zero =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: a point law
      rw [probInvoke_inl hq]; exact (isProbDist_single _).2
    | inr q =>
      -- a query with no query left: impossible, the body has made its `b` queries already
      exact absurd (hP s o u h q hc hq) (by omega)
  | succ n ih =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: a point law
      rw [probInvoke_inl hq]; exact (isProbDist_single _).2
    | inr q =>
      -- the body asks `q`: a draw of the step, then the rest of the invocation
      rw [probInvoke_succ_inr hq]
      -- every continuation completes (induction), so the mixture keeps the weight ...
      rw [weight_bindK_of_weight fun p hp => ?_]
      -- ... of the step, a probability law
      · exact stepR.weight_outcome r q
      -- a possible draw replies at `q`'s port, and the body's exchanges grow by one
      obtain ⟨y, hy⟩ := stepR.mem_support_outcome hp
      rw [hy]
      exact ih _ _ (hc.snoc hq y) (by simp; omega)

variable (P stepR) in
/-- The combined transition from `(s, r)` on outside query `⟨o, u⟩` is
`probInvoke stepR s o u b r []`: the law of the next paired state and the reply. -/
noncomputable def probCombine {b : ℕ} (hP : P.Bounded b) : ProbStep (S × R) O U V :=
  -- From `(s, r)` at `⟨o, u⟩`: the invocation from no exchanges with the whole budget `b`, a
  -- nonnegative law of weight one since the program is bounded.
  fun sr o u => ⟨P.probInvoke stepR sr.1 o u b sr.2 [],
    probInvoke_nonNeg sr.1 o u b sr.2 [],
    probInvoke_weight hP sr.1 o u b sr.2 [] (consistent_nil P _ _ _) (by simp)⟩

/-- The law of a combined step is the invocation from the empty exchanges. -/
lemma probCombine_val {b : ℕ} (hP : P.Bounded b) (sr : S × R) (o : O) (u : U o) :
    (P.probCombine stepR hP sr o u).1 = P.probInvoke stepR sr.1 o u b sr.2 [] := rfl

/-- Against a deterministic automaton, an invocation is the point law of its completion. -/
lemma probInvoke_ofDeterministic (stepD : R → (j : J) → X j → R × Y j) (s : S) (o : O)
    (u : U o) : ∀ n r h v, P.invoke stepD s o u n r h = some v →
      P.probInvoke (ProbStep.ofDeterministic stepD) s o u n r h = Finsupp.single v 1 := by
  -- Follow the completed deterministic invocation by induction on the remaining queries.
  intro n
  induction n with
  | zero =>
    intro r h v hv
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: both are its reply
      simp only [invoke, hq, Sum.elim_inl, Option.some.injEq] at hv
      rw [probInvoke_inl hq, hv]
    | inr q =>
      -- the body asks with no query left: the invocation does not complete
      simp [invoke, hq] at hv
  | succ n ih =>
    intro r h v hv
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: both are its reply
      simp only [invoke, hq, Option.some.injEq] at hv
      rw [probInvoke_inl hq, ← hv]
    | inr q =>
      -- the body asks `q`: the invocation draws a step ...
      simp only [invoke, hq] at hv
      rw [probInvoke_succ_inr hq]
      -- ... a point step, whose single outcome is the automaton's answer ...
      rw [ProbStep.outcome_ofDeterministic, bindK_single, one_smul]
      -- ... and continues as the deterministic invocation (induction)
      exact ih _ _ v hv

/-- **A program against a deterministic automaton**: the program run against its point steps is
the point step of the combined automaton. -/
lemma ofDeterministic_combine (stepD : R → (j : J) → X j → R × Y j) {b : ℕ}
    (hP : P.Bounded b) :
    ProbStep.ofDeterministic (P.combine stepD hP) =
      P.probCombine (ProbStep.ofDeterministic stepD) hP := by
  -- Compare the laws of each step, from each pair of states, at each query.
  funext sr o u
  apply Subtype.ext
  -- The invocation against the automaton completes with the combined step ...
  have hinvoke := invoke_eq_combine stepD hP sr o u
  -- ... so the invocation against its point steps is the point law of the combined step.
  exact (probInvoke_ofDeterministic stepD sr.1 o u b sr.2 [] _ hinvoke).symm

/-! ### Programs along simulations -/

section Simulation

-- `R₁`, `R₂` carry the two inside states; `stepR₁`, `stepR₂` answer the same inside interface.
variable {R₁ R₂ : Type} {stepR₁ : ProbStep R₁ J X Y} {stepR₂ : ProbStep R₂ J X Y}
    -- `K r₁` represents state `r₁` by a law of states in `R₂`; `E` admits inside query histories.
    {K : R₁ → Distribution.ProbDist R₂} {E : List (Σ j, X j) → Prop}
    -- `invR τ r₁` is the state invariant after inside queries `τ`.
    {invR : List (Σ j, X j) → R₁ → Prop}

variable (P) in
/-- After the inside queries `τ`, every inside query of an invocation at `⟨o, u⟩` in the state `s`
is admitted by `E`. -/
def AdmitsInvocation (E : List (Σ j, X j) → Prop) (s : S) (o : O) (u : U o)
    (τ : List (Σ j, X j)) : Prop :=
  ∀ h q, P.Consistent s o u h → P s o u h = .inr q → E (τ ++ h.map Prod.fst ++ [q])

/-- **An invocation along simulation steps** of the inside automata: from the kernel image of `r`,
the invocation against `stepR₂` is the invocation against `stepR₁` followed by the kernel. -/
lemma probInvoke_simulation
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      (bindK (K r).1 fun r₂ => P.probInvoke stepR₂ s o u n r₂ h) =
        bindK (P.probInvoke stepR₁ s o u n r h) fun p =>
          fTransform (fun r₂ => ((p.1.1, r₂), p.2)) (K p.1.2).1 := by
  -- The square to prove, for an invocation from the exchanges `h` with `n` queries left:
  --
  --     r ──── P against stepR₁ ────► ((s', r'), v)
  --     │                                   │
  --     K                                   K on r'
  --     ▼                                   ▼
  --     r₂ ─── P against stepR₂ ────► ((s', r₂'), v)
  --
  -- An admitted query gives one simulation square; `hpres` enables the continuation square:
  --
  --     r  ── stepR₁, q ──► (r', y)  ── rest against stepR₁ ──► ((s', r''), v)
  --     │                    │                                        │
  --     K  (simulation at r) K        (induction hypothesis)          K
  --     ▼                    ▼                                        ▼
  --     r₂ ── stepR₂, q ──► (r₂', y) ── rest against stepR₂ ──► ((s', r₂''), v)
  --
  intro n
  induction n with
  | zero =>
    intro r h _ _
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: the inside state is only moved by the kernel
      simp only [probInvoke_inl hq, bindK_single, one_smul]
      -- a point kernel along `r₂ ↦ ((s', r₂), v)` is the pushforward of `K r` along it
      exact bindK_single_comp _ _
    | inr q =>
      -- the body asks with no query left: no mass on both sides
      simp only [probInvoke_zero_inr hq, bindK_zero, bindK_zero_right]
  | succ n ih =>
    intro r h hc hr
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: the inside state is only moved by the kernel
      simp only [probInvoke_inl hq, bindK_single, one_smul]
      exact bindK_single_comp _ _
    | inr q =>
      -- the body asks `q`, which is admitted, so the simulation step applies at `r`
      have hE := hgood h q hc hq
      have hs := hsim _ r q hr hE
      unfold ProbStep.SimulatesAt at hs
      -- on both sides the invocation draws an inside step on `q`, then continues
      simp only [probInvoke_succ_inr hq]
      -- Left square, then right square, along the chain:
      --   K, then (stepR₂, then rest₂)
      --     = (K, then stepR₂), then rest₂        (associativity)
      --     = stepR₁, then (K, then rest₂)        (simulation at `r`)
      --     = stepR₁, then (rest₁, then K)        (induction hypothesis)
      --     = (stepR₁, then rest₁), then K        (associativity)
      calc (bindK (K r).1 fun r₂ => bindK (stepR₂.outcome r₂ q) fun p =>
            P.probInvoke stepR₂ s o u n p.1 (h ++ [(q, p.2)]))
          -- regroup: first the step of `stepR₂` from the kernel image of `r`
          = bindK (bindK (K r).1 fun r₂ => stepR₂.outcome r₂ q) fun p =>
              P.probInvoke stepR₂ s o u n p.1 (h ++ [(q, p.2)]) := (bindK_bindK _ _ _).symm
          -- simulation step: a step of `stepR₁` from `r`, then the kernel
        _ = bindK (stepR₁.outcome r q) fun p => bindK (K p.1).1 fun r₂ =>
              P.probInvoke stepR₂ s o u n r₂ (h ++ [(q, p.2)]) := by
            -- the simulation step at `r`
            rw [hs]
            -- regroup: for each outcome `p` of `stepR₁`, the kernel image of its next state
            rw [bindK_bindK]
            refine bindK_congr fun p _ => ?_
            -- pairing the kernel image with the reply `p.2`, then continuing, is continuing
            -- from the kernel image with `(q, p.2)` appended
            rw [bindK_fTransform]
            rfl
          -- the rest of the invocation along the simulation (induction hypothesis)
        _ = bindK (stepR₁.outcome r q) fun p =>
              bindK (P.probInvoke stepR₁ s o u n p.1 (h ++ [(q, p.2)])) fun p' =>
                fTransform (fun r₂ => ((p'.1.1, r₂), p'.2)) (K p'.1.2).1 :=
            bindK_congr fun p hp => by
              -- a possible draw replies at `q`'s port: the body's exchanges grow by one ...
              obtain ⟨y, hy⟩ := stepR₁.mem_support_outcome hp
              refine ih _ _ (hy ▸ hc.snoc hq y) ?_
              -- ... and the next state keeps the invariant
              have := hpres _ r q hr hE p hp
              -- the inside queries of `h · (q, y)` are those of `h`, then `q`
              simpa using this
          -- regroup the two mixtures
        _ = _ := (bindK_bindK _ _ _).symm

/-- **The end of an invocation**: each outcome of an invocation is the reply of the body on its
own exchanges extending `h`, with the invariant on the inside queries made. -/
lemma probInvoke_support
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      ∀ p ∈ (P.probInvoke stepR₁ s o u n r h).support, ∃ hf, P.Consistent s o u hf ∧
        h <+: hf ∧ P s o u hf = .inl (p.1.1, p.2) ∧ invR (τ ++ hf.map Prod.fst) p.1.2 := by
  -- Induction constructs final exchanges `hf` while preserving `invR` along each fresh draw.
  intro n
  induction n with
  | zero =>
    intro r h hc hr p hp
    cases hq : P s o u h with
    | inl a =>
      -- the body replies on `h` itself: the outcome is its reply
      rw [probInvoke_inl hq, Finsupp.mem_support_single] at hp
      rw [hp.1]
      -- `hf = h`: the body's own exchanges, a prefix of themselves, with the invariant
      exact ⟨h, hc, List.prefix_refl _, hq, hr⟩
    | inr q =>
      -- no query left: no outcome
      rw [probInvoke_zero_inr hq] at hp; simp at hp
  | succ n ih =>
    intro r h hc hr p hp
    cases hq : P s o u h with
    | inl a =>
      -- the body replies on `h` itself: the outcome is its reply
      rw [probInvoke_inl hq, Finsupp.mem_support_single] at hp
      rw [hp.1]
      exact ⟨h, hc, List.prefix_refl _, hq, hr⟩
    | inr q =>
      -- the outcome comes from a possible draw `p'` and the rest of the invocation
      rw [probInvoke_succ_inr hq] at hp
      obtain ⟨p', hp', hp⟩ := mem_support_bindK hp
      -- the draw replies at `q`'s port: `p' = (r', ⟨q.1, y⟩)`
      obtain ⟨y, hy⟩ := stepR₁.mem_support_outcome hp'
      -- the draw keeps the invariant on the inside queries made
      have hr' : invR (τ ++ (h ++ [(q, p'.2)]).map Prod.fst) p'.1 := by
        simpa using hpres _ r q hr (hgood h q hc hq) p' hp'
      -- the rest of the invocation ends on exchanges extending `h · (q, y)` (induction)
      obtain ⟨hf, hcf, hpf, hf₁, hf₂⟩ := ih _ _ (hy ▸ hc.snoc hq y) hr' p hp
      -- `h` is a prefix of `h · (q, y)`, hence of `hf`
      exact ⟨hf, hcf, (List.prefix_append h _).trans hpf, hf₁, hf₂⟩

/-- Map `(s, r₁)` to `(s, r₂)` with `r₂ ← K r₁`, leaving the program state fixed. -/
noncomputable def insideKernel
    -- `K` changes the inside-state representation; `sr` supplies the program and inside states.
    (K : R₁ → Distribution.ProbDist R₂) (sr : S × R₁) :
    Distribution.ProbDist (S × R₂) :=
  (K sr.2).map fun r₂ => (sr.1, r₂)

variable (P) in
/-- **A program respects simulations**: when the inside queries of an invocation are admitted
and simulated, the program run against `stepR₂` simulates the program run against `stepR₁` along
the kernel on the inside state. -/
lemma simulatesAt_probCombine {b : ℕ} (hP : P.Bounded b)
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    {s : S} {r : R₁} {τ : List (Σ j, X j)} (hr : invR τ r) {x : Σ o, U o}
    (hgood : P.AdmitsInvocation E s x.1 x.2 τ) :
    ProbStep.SimulatesAt (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP) (insideKernel K)
      (s, r) x := by
  -- One step of the two combined automata at the outside query `⟨o, u⟩`, the kernel `K`
  -- acting on the inside state only:
  --
  --   (s, r)  ── P against stepR₁, ⟨o, u⟩ ──► ((s', r'), v)
  --       │                                         │
  --       K                                         K
  --       ▼                                         ▼
  --   (s, r₂) ── P against stepR₂, ⟨o, u⟩ ──► ((s', r₂'), v)
  --
  -- It is the square of one invocation (`probInvoke_simulation`), the reply tagged by `o`.
  obtain ⟨o, u⟩ := x
  -- The invocations from the empty exchanges, along the simulation.
  have hinv := probInvoke_simulation (P := P) hsim hpres s o u τ hgood b r []
    (consistent_nil P _ _ _) (by simpa using hr)
  -- Unfold the outcomes of the combined steps into the invocations, tagged by the port.
  unfold ProbStep.SimulatesAt
  simp only [insideKernel, ProbDist.map_val, ProbStep.outcome, probCombine_val, bindK_fTransform,
    Function.comp_def]
  -- Tag after mixing: the left side is the tagged invocation from the kernel image of `r` ...
  rw [← fTransform_bindK]
  -- ... which is the invocation from `r` followed by the kernel (`hinv`) ...
  rw [hinv]
  -- ... tagged; compare outcome by outcome.
  rw [fTransform_bindK]
  refine bindK_congr fun p _ => ?_
  -- both sides push `K` of the final inside state along the same map
  simp only [fTransform_fTransform, Function.comp_def]
  rfl

variable (P) in
/-- The outcomes of the program run against `stepR₁` come from the body's own exchanges, with the
invariant on the inside queries made. -/
lemma probCombine_support {b : ℕ} (hP : P.Bounded b)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    {s : S} {r : R₁} {τ : List (Σ j, X j)} (hr : invR τ r) {x : Σ o, U o}
    (hgood : P.AdmitsInvocation E s x.1 x.2 τ) :
    ∀ p ∈ ((P.probCombine stepR₁ hP).outcome (s, r) x).support, ∃ hf,
      P.Consistent s x.1 x.2 hf ∧ invR (τ ++ hf.map Prod.fst) p.1.2 := by
  intro p hp
  -- An outcome is a tagged outcome `p'` of the invocation from the empty exchanges ...
  obtain ⟨p', hp', rfl⟩ := mem_support_fTransform _ _ hp
  -- ... which ends on the body's own exchanges `hf`, with the invariant.
  obtain ⟨hf, hcf, -, -, hinv⟩ := probInvoke_support (P := P) hpres s x.1 x.2 τ hgood b r []
    (consistent_nil P _ _ _) (by simpa using hr) p' hp'
  exact ⟨hf, hcf, hinv⟩

end Simulation

end Program

section

variable [Fintype (Σ o, U o)] [Fintype (Σ o, V o)]

/-- **A program respects simulations, as random systems**: if `stepR₂` simulates `stepR₁` along
`K` at the states satisfying an invariant of the inside queries so far, at every inside query
before the program's total budget `b * n`, then the program run against the two automata gives
the same random system on the outside domain `F`, of at most `n` queries.

```text
  P run against stepR₁ from (s, r)   =   P run against stepR₂ from (s, K r)
```
-/
lemma RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation
    -- `F` admits outside histories of length at most `n`, as certified by `hF`.
    {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
    -- `P` makes at most `b` inside queries per invocation, as certified by `hP`.
    (P : Program S O J U V X Y) {b : ℕ} (hP : P.Bounded b)
    -- `stepR₁`, `stepR₂` answer the same inside interface using states `R₁`, `R₂`.
    {R₁ R₂ : Type} (stepR₁ : ProbStep R₁ J X Y) (stepR₂ : ProbStep R₂ J X Y)
    -- `K r` represents an `R₁` state by a law on `R₂`; `invR τ r` tracks it after queries `τ`.
    (K : R₁ → Distribution.ProbDist R₂) (invR : List (Σ j, X j) → R₁ → Prop)
    -- `hpres` preserves `invR` at every supported next state before the total bound `b * n`.
    (hpres : ∀ τ r q, invR τ r → τ.length < b * n →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    -- `hsim` equates the next joint state/reply laws through `K` at those states and queries.
    (hsim : ∀ τ r q, invR τ r → τ.length < b * n → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    -- `s` starts the program; `init` starts the inside automaton with `invR []`, by `hinit`.
    (s : S) (init : Distribution.ProbDist R₁) (hinit : ∀ r ∈ init.1.support, invR [] r) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine stepR₁ hP)
        (init.map fun r => (s, r)) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine stepR₂ hP)
        ((init.bind K).map fun r => (s, r)) := by
  -- Admit exactly the inside histories within the total bound `b * n`.
  let E : List (Σ j, X j) → Prop := fun τ => τ.length ≤ b * n
  -- Admission of `τ ++ [q]` is exactly `τ.length < b * n`, where the hypotheses apply.
  have hsim' : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q :=
    fun τ r q hr hq => hsim τ r q hr (by simp [E] at hq; omega)
  have hpres' : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1 :=
    fun τ r q hr hq => hpres τ r q hr (by simp [E] at hq; omega)
  -- An invocation after `xs` outside queries, with at most `b` inside queries per earlier one,
  -- keeps its inside queries within the budget when the outside domain admits one more.
  have good : ∀ xs (sr : S × R₁) x τ, τ.length ≤ b * xs.length → F (xs ++ [x]) →
      P.AdmitsInvocation E sr.1 x.1 x.2 τ := fun xs sr x τ hl hx h q hc hq => by
    -- this invocation has made fewer than `b` queries, and there are at most `n` outside ones
    have h1 := hP sr.1 x.1 x.2 h q hc hq
    have h2 := hF _ hx
    simp only [List.length_append, List.length_singleton] at h2
    simp only [E, List.length_append, List.length_map, List.length_singleton]
    -- `|τ| + |h| + 1 ≤ b·|xs| + b = b·(|xs| + 1) ≤ b·n`
    nlinarith
  -- After `xs`, retain an inside history `τ` with `invR τ` and `τ.length ≤ b * xs.length`.
  let inv : List (Σ o, U o) → S × R₁ → Prop :=
    fun xs sr => ∃ τ, invR τ sr.2 ∧ τ.length ≤ b * xs.length
  -- Each outside step keeps it: an invocation adds its own exchanges `hf`, at most `b`.
  have hpres_out : ∀ xs sr x, inv xs sr → F (xs ++ [x]) →
      ∀ p ∈ ((P.probCombine stepR₁ hP).outcome sr x).support, inv (xs ++ [x]) p.1 := by
    rintro xs sr x ⟨τ, hτ, hl⟩ hx p hp
    obtain ⟨hf, hcf, hinv⟩ := Program.probCombine_support P hP hpres' hτ
      (good xs sr x τ hl hx) p hp
    -- the new inside history: `τ`, then the inside queries of `hf`
    refine ⟨τ ++ hf.map Prod.fst, hinv, ?_⟩
    -- `|hf| ≤ b`, the program being bounded
    have := Program.Consistent.length_le hP hcf
    simp only [List.length_append, List.length_map, List.length_singleton]
    -- `|τ| + |hf| ≤ b·|xs| + b = b·(|xs| + 1)`
    nlinarith
  -- Each outside step is a simulation step: the program respects the inside simulation.
  have hsim_out : ∀ xs sr x, inv xs sr → F (xs ++ [x]) →
      ProbStep.SimulatesAt (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP)
        (Program.insideKernel K) sr x := by
    rintro xs sr x ⟨τ, hτ, hl⟩ hx
    -- `good` admits this invocation, and `invR τ` holds at its starting inside state.
    exact Program.simulatesAt_probCombine P hP hsim' hpres' hτ (good xs sr x τ hl hx)
  -- Initially the inside history is empty.
  have hinit_out : ∀ sr ∈ (init.map fun r => (s, r)).1.support, inv [] sr := by
    intro sr hsr
    -- an initial state is `(s, r)` for a possible `r` of `init`; take `τ = []`
    obtain ⟨r, hr, rfl⟩ := mem_support_fTransform _ _ hsr
    exact ⟨[], hinit r hr, le_refl _⟩
  -- The outside simulation equates the cumulative laws on `F`.
  rw [RandomSystem.ofProbAutomaton_eq_of_simulation (E := F) (bound := n) (hE := hF)
    (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP) (Program.insideKernel K) inv hpres_out
    hsim_out _ hinit_out]
  -- Its initial kernel image is `(s, r₂)` with `r₂ ← init.bind K`, as on the right.
  congr 1
  apply Subtype.ext
  simp only [ProbDist.bind_val, ProbDist.map_val, Program.insideKernel, bindK_fTransform,
    fTransform_bindK, Function.comp_def]

end

/-! ### Pre-sampled draws -/

namespace ProbStep

variable (step : ProbStep R J X Y)

/-- A record of one step: the state and the query, and the drawn next state and reply. -/
abbrev Draw (R J : Type) (X Y : J → Type) := (R × Σ j, X j) × (R × Σ j, Y j)

/-- Draw `(r', y) ← step r j x`, reply `y`, and change `(r, rec)` to
`(r', rec ++ [((r, ⟨j, x⟩), (r', ⟨j, y⟩))])`. -/
noncomputable def recording : ProbStep (R × List (Draw R J X Y)) J X Y :=
  fun rd j x => (step rd.1 j x).map fun o =>
    ((o.1, rd.2 ++ [((rd.1, ⟨j, x⟩), tagged ⟨j, x⟩ o)]), o.2)

/-- The outcome of the recording step: a draw of `step`, appended to the record. -/
lemma outcome_recording (rd : R × List (Draw R J X Y)) (x : Σ j, X j) :
    step.recording.outcome rd x =
      fTransform (fun o => ((o.1, rd.2 ++ [((rd.1, x), o)]), o.2)) (step.outcome rd.1 x) := by
  -- Both are the step's law, pushed forward along the same map.
  simp only [outcome, recording, ProbDist.map_val, fTransform_fTransform]
  -- Recording the tagged draw then tagging the reply, or tagging first: the same map.
  rfl

/-- **Forgetting the record** is a simulation. -/
lemma simulatesAt_forget (rd : R × List (Draw R J X Y)) (x : Σ j, X j) :
    SimulatesAt step.recording step (fun rd => Distribution.ProbDist.single rd.1) rd x := by
  -- The kernel maps each recorded state `(r, rec)` to the point mass at `r`:
  --
  --   (r, rec) ── recording, x ──► ((r', rec · ((r, x), (r', y))), y)
  --      │                                  │
  --    forget                             forget
  --      ▼                                  ▼
  --      r ─────── step, x ───────► (r', y)
  unfold SimulatesAt
  -- From the recorded state, `step` steps as the recording step, forgetting the record.
  simp only [Distribution.ProbDist.single, bindK_single, one_smul, outcome_recording,
    bindK_fTransform, Function.comp_def, fTransform_single]
  -- What is left: the step's law against its image under the point kernel, which is itself.
  exact (bindK_single_one _).symm

open scoped Classical in
/-- The reply at the queried port from a tagged draw, or the default `d`. -/
noncomputable def untag (x : Σ j, X j) (o : R × Σ j, Y j) (d : R × Y x.1) : R × Y x.1 :=
  if h : o.2.1 = x.1 then (o.1, h ▸ o.2.2) else d

@[simp] lemma untag_tagged (x : Σ j, X j) (o : R × Y x.1) (d : R × Y x.1) :
    untag x (tagged x o) d = o := by
  -- The tagged draw is at the queried port: `untag` takes its first case and gives back `o`.
  simp [untag, tagged]

/-- The initial law with an empty record, forgetting the record, is the initial law. -/
lemma bind_forget (init : Distribution.ProbDist R) :
    ((init.map fun r => (r, ([] : List (Draw R J X Y)))).bind
      fun rd => Distribution.ProbDist.single rd.1) = init := by
  -- Compare the underlying laws.
  apply Subtype.ext
  -- Pairing with the empty record and keeping the state is the point kernel.
  simp only [ProbDist.bind_val, ProbDist.map_val, Distribution.ProbDist.single,
    bindK_fTransform, Function.comp_def]
  -- ... which leaves `init` unchanged.
  exact bindK_single_one _

variable [Fintype (Σ j, X j)] (init : Distribution R)

open scoped Classical in
/-- States reachable from `init` in at most `k` transitions:
`reachable 0 = init.support` and
`reachable (k+1) = reachable k ∪ ⋃ r ∈ reachable k, ⋃ x, fst '' support(step.outcome r x)`. -/
noncomputable def reachable : ℕ → Finset R
  | 0 => init.support
  | k + 1 => reachable k ∪ (reachable k).biUnion fun r =>
      Finset.univ.biUnion fun x => (step.outcome r x).support.image Prod.fst

/-- More steps reach more states. -/
lemma reachable_mono {k k' : ℕ} (h : k ≤ k') :
    step.reachable init k ⊆ step.reachable init k' := by
  classical
  -- Each step adds states to the reachable ones.
  induction h with
  -- `k' = k`: the same set
  | refl => exact subset_refl _
  -- one step more: the states reachable before are the left part of the union
  | step _ ih => exact ih.trans Finset.subset_union_left

open scoped Classical in
/-- A possible next state from a state reachable in `k` steps is reachable in `k + 1`. -/
lemma mem_reachable_succ {k : ℕ} {r : R} (hr : r ∈ step.reachable init k) {x : Σ j, X j}
    {p : R × Σ j, Y j} (hp : p ∈ (step.outcome r x).support) :
    p.1 ∈ step.reachable init (k + 1) :=
  -- `p.1` is a next state of a possible draw from `r` at `x`: one of the new states of step
  -- `k + 1`, the right part of the union.
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_biUnion.mpr
    ⟨x, Finset.mem_univ _, Finset.mem_image_of_mem _ hp⟩⟩)

/-- **The record after `k` draws**: `k` draws, from a state reachable in `k` steps; one more draw
keeps this. -/
lemma recording_reachable {k : ℕ} {rd : R × List (Draw R J X Y)} (hl : rd.2.length = k)
    (hr : rd.1 ∈ step.reachable init k) (x : Σ j, X j)
    {p : (R × List (Draw R J X Y)) × Σ j, Y j} (hp : p ∈ (step.recording.outcome rd x).support) :
    p.1.2.length = k + 1 ∧ p.1.1 ∈ step.reachable init (k + 1) := by
  -- The recording step draws `o` from `step` and appends it to the record.
  rw [outcome_recording] at hp
  obtain ⟨o, ho, rfl⟩ := mem_support_fTransform _ _ hp
  -- One more draw in the record, and the next state of a possible draw.
  exact ⟨by simp [hl], step.mem_reachable_succ init hr ho⟩

/-- **The record initially**: a possible initial recorded state `(r, [])`, `r ∈ supp init`, has
no draws, and `r` is reachable in zero steps. -/
lemma recording_init_reachable (init : Distribution.ProbDist R)
    {rd : R × List (Draw R J X Y)}
    (hrd : rd ∈ (init.map fun r => (r, ([] : List (Draw R J X Y)))).1.support) :
    rd.2.length = 0 ∧ rd.1 ∈ step.reachable init.1 0 := by
  -- The support of the pushforward `r ↦ (r, [])`: `rd = (r, [])` with `r ∈ supp init`.
  obtain ⟨r, hr, rfl⟩ := mem_support_fTransform _ _ hrd
  exact ⟨rfl, hr⟩

variable (L : ℕ)

/-- A cell of the table of draws: a step number below `L`, a reachable state and a query. -/
abbrev Cell := Fin L × {r // r ∈ step.reachable init L} × (Σ j, X j)

open scoped Classical in
/-- **The deterministic step reading pre-sampled draws**: in the state `r` with `k` steps done
and the table `t`, the query `x` is answered by the draw in the cell `(k, r, x)`.

```text
  state (r, k, t)  ──x──►  (t(k, r, x) = (r', y))  ──►  state (r', k + 1, t), reply y
```
-/
noncomputable def drawStep :
    R × ℕ × (step.Cell init L → R × Σ j, Y j) → (j : J) → X j →
      (R × ℕ × (step.Cell init L → R × Σ j, Y j)) × Y j :=
  fun rkt j x =>
    -- `d`: some next state and reply (the step's law has a sample), used as a default
    let d := Classical.choice (step rkt.1 j x).nonempty
    -- inside the table (fewer than `L` steps done, `r` reachable in `L` steps): read the cell
    -- `(k, r, x)`, move to its next state and give its reply (`d` if it is at another port)
    if h : rkt.2.1 < L ∧ rkt.1 ∈ step.reachable init L then
      let o := untag ⟨j, x⟩ (rkt.2.2 (⟨rkt.2.1, h.1⟩, ⟨rkt.1, h.2⟩, ⟨j, x⟩)) d
      ((o.1, rkt.2.1 + 1, rkt.2.2), o.2)
    -- outside the table: stay in `r` and give the default reply
    else ((rkt.1, rkt.2.1 + 1, rkt.2.2), d.2)

open scoped Classical in
/-- For cell `c = (k, r, x)`, use `δ_o` when record entry `rec[k] = ((r, x), o)`;
otherwise use the fresh transition law `step.outcome r x`. -/
noncomputable def drawLaw
    -- `rec` lists the draws already made; `c` selects a time, reachable state and query.
    (rec : List (Draw R J X Y)) (c : step.Cell init L) :
    Distribution (R × Σ j, Y j) :=
  -- a step already done: its recorded draw if it read this cell, a fresh step otherwise
  if h : c.1.val < rec.length then
    if rec[c.1.val].1 = (c.2.1.val, c.2.2) then Finsupp.single rec[c.1.val].2 1
    else step.outcome c.2.1.val c.2.2
  -- a step not yet done: a fresh step
  else step.outcome c.2.1.val c.2.2

/-- Each cell law is normalized: it is a point mass or a tagged transition law. -/
lemma drawLaw_isProbDist (rec : List (Draw R J X Y)) (c : step.Cell init L) :
    (step.drawLaw init L rec c).isProbDist := by
  unfold drawLaw
  split_ifs
  -- the recorded draw: a point mass
  · exact isProbDist_single _
  -- a fresh step: the tagged step's law, a probability law
  · exact fTransform_isProbDist _ (step _ _ _).2
  · exact fTransform_isProbDist _ (step _ _ _).2

open scoped Classical in
/-- Given `rd = (r, rec)`, sample independent cells `t(c) ∼ drawLaw rec c` and return
`(r, rec.length, t)`. Recorded cells are fixed; the remaining cells are fresh transitions. -/
noncomputable def drawKernel
    -- `rd` carries the current state `r` and the record `rec` of previous draws.
    (rd : R × List (Draw R J X Y)) :
    Distribution.ProbDist (R × ℕ × (step.Cell init L → R × Σ j, Y j)) :=
  ProbDist.map (fun t => (rd.1, rd.2.length, t))
    (ProbDist.pi fun c =>
      ⟨step.drawLaw init L rd.2 c, step.drawLaw_isProbDist init L rd.2 c⟩)

open scoped Classical in
/-- The underlying table law is the product of its cell laws, paired with state and row. -/
@[simp] lemma drawKernel_val (rd : R × List (Draw R J X Y)) :
    (step.drawKernel init L rd).1 =
      fTransform (fun t => (rd.1, rd.2.length, t)) (pi (step.drawLaw init L rd.2)) := rfl

open scoped Classical in
/-- Appending `((r, x), o)` fixes cell `(rec.length, r, x)` to `δ_o`; every other cell law
is unchanged. -/
lemma update_drawLaw (rec : List (Draw R J X Y)) (r : R) (x : Σ j, X j) (o : R × Σ j, Y j)
    (hk : rec.length < L) (hr : r ∈ step.reachable init L) :
    Function.update (step.drawLaw init L rec) (⟨rec.length, hk⟩, ⟨r, hr⟩, x) (Finsupp.single o 1) =
      step.drawLaw init L (rec ++ [((r, x), o)]) := by
  -- The updated row is `rec.length`; earlier rows retain their entries and later rows stay fresh.
  funext c
  by_cases hc : c = (⟨rec.length, hk⟩, ⟨r, hr⟩, x)
  -- At the updated cell, both laws are the point mass at `o`.
  · subst hc
    simp [drawLaw]
  -- At every other cell, compare the existing row with the appended record.
  · rw [Function.update_of_ne hc]
    unfold drawLaw
    by_cases hlt : c.1.val < rec.length
    -- Earlier rows read the same entry of `rec`.
    · rw [dite_eq_left hlt, dite_eq_left (by simp; omega), List.getElem_append_left hlt]
    · by_cases heq : c.1.val = rec.length
      · -- At this row, a different state/query still has its fresh transition law.
        rw [dite_eq_right hlt, dite_eq_left (by simp; omega)]
        -- entry `rec.length` of the new record is the new draw
        have hget : (rec ++ [((r, x), o)])[c.1.val]'(by simp; omega) = ((r, x), o) := by
          simp [heq]
        rw [hget, ite_eq_right]
        -- the new record is at another state or query than `c`
        intro h
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        apply hc
        -- with that state and query, `c` (row `rec.length`) is the updated cell, against `hc`
        -- (the bounds in the two triples are proofs, equal by proof irrelevance)
        obtain ⟨⟨k, hk'⟩, ⟨r', hr'⟩, x'⟩ := c
        simp only at heq h₁ h₂
        subst heq h₁ h₂
        rfl
      -- Later rows have no recorded draw and retain their fresh transition laws.
      · rw [dite_eq_right hlt, dite_eq_right (by simp; omega)]

/-- From a reachable state before row `L`, reading the next table cell has the fresh
transition law. Drawing the table then reading it has the same joint law as recording a
fresh draw then sampling the updated conditional table.

```text
  (r, rec) ──── recording, x ────► ((r', rec · ((r, x), (r', y))), y)
     │                                        │
  drawKernel                               drawKernel
     ▼                                        ▼
  (r, k, t) ──── drawStep, x ────► ((r', k + 1, t), y)      t(k, r, x) = (r', y)
```
-/
lemma simulatesAt_drawStep
    -- `rd = (r, rec)` gives the current state and record; `hk` leaves a row in the table.
    (rd : R × List (Draw R J X Y)) (hk : rd.2.length < L)
    -- `hr` includes the state among the table's indices; `x` is the next tagged query.
    (hr : rd.1 ∈ step.reachable init L) (x : Σ j, X j) :
    SimulatesAt step.recording (ofDeterministic (step.drawStep init L)) (step.drawKernel init L)
      rd x := by
  classical
  obtain ⟨r, rec⟩ := rd
  obtain ⟨j, x⟩ := x
  simp only at hk hr
  -- The cell read now: step `rec.length`, state `r`, query `x`.
  set c : step.Cell init L := (⟨rec.length, hk⟩, ⟨r, hr⟩, ⟨j, x⟩)
  -- Its law given the record is a fresh step of `step` from `r`.
  have hentry : step.drawLaw init L rec c = step.outcome r ⟨j, x⟩ := by
    -- Row `rec.length` has no recorded draw yet.
    simp [drawLaw, c]
  -- The deterministic step reads the cell `c` (fewer than `L` steps, reachable state).
  have hread : ∀ t : step.Cell init L → R × Σ j, Y j,
      step.drawStep init L (r, rec.length, t) j x =
        (((untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).1, rec.length + 1, t),
          (untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).2) := by
    intro t
    -- The guard holds: `rec.length < L` and `r` is reachable in `L` transitions.
    simp only [drawStep, dite_eq_left (And.intro hk hr), c]
  -- The simulation equation: the kernel then `drawStep`, against `recording` then the kernel.
  unfold SimulatesAt
  calc bindK (step.drawKernel init L (r, rec)).1
        (fun st => (ofDeterministic (step.drawStep init L)).outcome st ⟨j, x⟩)
      -- Sample the conditional table and read its next cell `c`.
      = fTransform (fun t => (((untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).1,
            rec.length + 1, t), (⟨j, (untag ⟨j, x⟩ (t c)
              (Classical.choice (step r j x).nonempty)).2⟩ : Σ j, Y j)))
          (pi (step.drawLaw init L rec)) := by
        -- The point transition at each table is its pushforward under the cell-reading map.
        simp only [drawKernel_val, bindK_fTransform, Function.comp_def,
          outcome_ofDeterministic, hread]
        exact bindK_single_comp _ _
      -- Sample `o = t(c)` first, then the independent table with that cell fixed.
    _ = bindK (step.outcome r ⟨j, x⟩) fun o =>
          fTransform (fun t => (((untag ⟨j, x⟩ o (Classical.choice (step r j x).nonempty)).1,
            rec.length + 1, t), (⟨j, (untag ⟨j, x⟩ o
              (Classical.choice (step r j x).nonempty)).2⟩ : Σ j, Y j)))
          (pi (step.drawLaw init L (rec ++ [((r, ⟨j, x⟩), o)]))) := by
        -- `pi_eq_bindK_update` isolates cell `c`; `hentry` identifies its fresh law.
        rw [pi_eq_bindK_update _ c, fTransform_bindK, hentry]
        refine bindK_congr fun o _ => ?_
        -- Fixing `c` to `o` is precisely appending this draw to the record.
        rw [update_drawLaw step init L rec r ⟨j, x⟩ o hk hr]
        -- Every table in the updated support reads back `o` at `c`.
        refine fTransform_congr_support fun t ht => ?_
        rw [← update_drawLaw step init L rec r ⟨j, x⟩ o hk hr] at ht
        rw [eq_of_mem_support_pi_update _ _ o ht]
      -- This is the recording step followed by its updated conditional table law.
    _ = _ := by
        -- Both sides append the same draw and retain the same table at row `rec.length + 1`.
        simp only [outcome_recording, drawKernel_val, bindK_fTransform,
          Function.comp_def, fTransform_fTransform, List.length_append, List.length_singleton]
        -- Untagging the tagged fresh draw recovers its state and reply.
        rw [outcome, bindK_fTransform, bindK_fTransform]
        refine bindK_congr fun o _ => ?_
        simp only [Function.comp_def, untag_tagged]
        rfl

end ProbStep

/-- Draw `r₀ ← init`; for each cell `c = (k, r, x)`, independently draw
`t(c) ← step.outcome r x`, then return `(r₀, 0, t)`. -/
noncomputable def ProbStep.drawInit
    -- The finite query alphabet and finite supports give finitely many reachable table cells.
    [Fintype (Σ j, X j)] (step : ProbStep R J X Y)
    -- `init` samples the initial state; `L` gives the number of table rows.
    (init : Distribution.ProbDist R) (L : ℕ) :
    Distribution.ProbDist (R × ℕ × (step.Cell init.1 L → R × Σ j, Y j)) :=
  (init.map fun r => (r, [])).bind (step.drawKernel init.1 L)

section

variable [Fintype (Σ j, X j)] [Fintype (Σ j, Y j)]

/-- A probabilistic automaton on a domain of at most `m ≤ L` queries equals the deterministic
automaton reading a table sampled once with the initial state. This realizes
[1, Definition 2, p. 6: "specifying the internal randomness and the initial state"].

```text
  (step, init)  =  (recording, (init, []))  =  (drawStep, drawInit)
```
-/
theorem RandomSystem.ofProbAutomaton_eq_drawStep
    -- `E` admits inside query histories; `hE` bounds their length by `m`.
    {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    -- `step` supplies fresh transitions; `init` samples the initial inside state.
    (step : ProbStep R J X Y) (init : Distribution.ProbDist R)
    -- `L` is the number of retained table rows; `hL` covers every query admitted by `E`.
    {L : ℕ} (hL : m ≤ L) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step init =
      RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE)
        (ProbStep.ofDeterministic (step.drawStep init.1 L)) (step.drawInit init L) := by
  -- One draw is recorded per query, and its state is reachable after that many transitions.
  let inv : List (Σ j, X j) → R × List (ProbStep.Draw R J X Y) → Prop :=
    fun xs rd => rd.2.length = xs.length ∧ rd.1 ∈ step.reachable init.1 xs.length
  -- Each query appends one draw, from a reachable state (`recording_reachable`).
  have hpres : ∀ xs rd x, inv xs rd → E (xs ++ [x]) →
      ∀ p ∈ (step.recording.outcome rd x).support, inv (xs ++ [x]) p.1 := by
    rintro xs rd x ⟨hl, hr⟩ - p hp
    simpa only [inv, List.length_append, List.length_singleton] using
      step.recording_reachable init.1 hl hr x hp
  -- Initially: no draws, from a state in the support of `init`.
  have hinit : ∀ rd ∈ (init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))).1.support,
      inv [] rd := fun _ hrd => step.recording_init_reachable init hrd
  -- Along the domain, fewer than `L` steps are done, from states reachable in `L` steps: the
  -- deterministic step on the table of draws simulates the recording step.
  have hsim : ∀ xs rd x, inv xs rd → E (xs ++ [x]) →
      ProbStep.SimulatesAt step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L))
        (step.drawKernel init.1 L) rd x := by
    rintro xs rd x ⟨hl, hr⟩ hx
    -- the domain admits `xs · x`, so `|xs| + 1 ≤ m ≤ L`: fewer than `L` draws recorded ...
    have hlen := hE _ hx
    simp only [List.length_append, List.length_singleton] at hlen
    -- ... and the state, reachable in `|xs|` steps, is reachable in `L`
    exact step.simulatesAt_drawStep init.1 L rd (by omega)
      (step.reachable_mono init.1 (by omega) hr) x
  calc RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step init
      -- the initial law is the recorded initial law, the record forgotten ...
      _ = RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step
          ((init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))).bind
            fun rd => Distribution.ProbDist.single rd.1) := by rw [ProbStep.bind_forget]
      -- ... and forgetting the record is a simulation of the recording step
      _ = RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step.recording
          (init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))) :=
        (RandomSystem.ofProbAutomaton_eq_of_simulation step.recording step
          (fun rd => Distribution.ProbDist.single rd.1) inv hpres
          (fun xs rd x _ _ => step.simulatesAt_forget rd x) _ hinit).symm
      -- the deterministic step on the table of draws simulates the recording step
      -- (`drawInit` is by definition the kernel image of `(init, [])`)
      _ = _ := RandomSystem.ofProbAutomaton_eq_of_simulation step.recording _ _ inv hpres hsim _
        hinit

end

/-! ### Attaching a program -/

namespace PDCBehavior

-- Finite port and query/reply types give finite presentations on the bounded domains.
variable [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
    [∀ j, Fintype (Y j)]
    -- `E`, `F` admit inside and outside histories; `hE`, `hF` bound their lengths by `m`, `n`.
    {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
    {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
    -- `hE'`, `hF'` exclude empty histories and admit every nonempty prefix.
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)

/-- **Attaching a program to a deterministic automaton** with a random initial state: the
combined automaton, its initial state paired with the program's. -/
lemma attach_ofDDC_ofProgramOn_ofDeterministic
    -- `s` starts program `P`; `hb` bounds each invocation by `b` inside queries.
    (s : S) (P : Program S O J U V X Y) {b : ℕ} (hb : P.Bounded b)
    -- `hα` gives exactly the converter domain over `F`, using only inside histories in `E`.
    (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F))
    -- `stepR` updates the inside state deterministically; `init` samples its starting value.
    (stepR : R → (j : J) → X j → R × Y j) (init : Distribution.ProbDist R) :
    attach hE' hF' (ofDDC (DDC.ofProgramOn s P F) hα)
        (RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE)
          (ProbStep.ofDeterministic stepR) init)
        (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF)
        (ProbStep.ofDeterministic (P.combine stepR hb)) (init.map fun r => (s, r)) := by
  --          ┌──────┐ ──q─▶ ┌──────────┐
  --   ──u──▶ │ P(s) │       │ stepR, r │   =   combined automaton `P.combine stepR`,
  --   ◀──v── └──────┘ ◀─y── └──────────┘       from `(s, r)`
  --
  -- The automaton started in `r`, on the domain `E`, as a deterministic system with domain `E`.
  let aut : R → {t : InterfaceSystem J X Y //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ E h} := fun r =>
    ⟨filterDom E (automatonSystem stepR r),
      -- a DDS: the automaton system restricted to the prefix-closed domain `E`
      (automatonSystem_isDDS stepR r).filterDom _ hE'.2,
      -- it replies at the queried port, as the automaton does
      fun h x y hy => automatonSystem_replies stepR r h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
      -- its domain is `E`: the automaton answers every nonempty input list, and `E []` fails
      fun h => by
        rw [filterDom_dom, automatonSystem_dom]
        exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE'.1 (he ▸ hd)⟩⟩⟩
  -- Its random initial state presents the probabilistic automaton of its point steps.
  have hQ : ∀ h, behaviorMass (init.map aut).1 (h.map Prod.fst) (h.map Prod.snd) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) (ProbStep.ofDeterministic stepR)
        init h := by
    intro h
    -- right side: the mass of the initial states whose automaton replies `h` ...
    rw [RandomSystem.ofProbAutomaton_ofDeterministic_apply]
    -- ... and the left side is the same mass, under the image law of `init` by `aut`
    exact mass_fTransform _ _ _
  -- Compare the probabilities of each outside transcript `t`.
  apply RandomSystem.ext
  intro t
  -- Present the converter by its DDC and the automaton by its deterministic systems.
  -- (The point law at the DDC presents `ofDDC` by definition: `fun _ => rfl`.)
  rw [attach_presents hE' hF' _ _ _ ⟨Finsupp.single ⟨_, hα⟩ 1, isProbDist_single _⟩
    (init.map aut) (fun _ => rfl) hQ]
  -- The attachment of presentations: the program attached to the automaton from each initial
  -- state `r`, with probability `init r`.
  rw [behaviorMass_attachPDS, prod_single_left, mass_fTransform, ProbDist.map_val,
    mass_fTransform]
  -- The other side: the combined automaton from each initial pair `(s, r)`.
  rw [RandomSystem.ofProbAutomaton_ofDeterministic_apply, ProbDist.map_val, mass_fTransform]
  -- Attached to each automaton, the program is the combined automaton.
  refine mass_congr _ fun r => ?_
  -- the trimmed attachment of the DDC to `aut r` is the combined automaton from `(s, r)`,
  -- restricted to the outside domain `F`
  exact iff_of_eq (congrArg (fun z => Replies z (t.map Prod.fst) (t.map Prod.snd))
    (Program.trim_apply_ofProgramOn_automaton stepR hb s r hE' hF' hα))

/-- Attaching `P` to the probabilistic automaton `(step, init)` gives `P.probCombine step hb`
with initial law `(r ↦ (s, r))_* init` on `F`. This is the composition of
[1, §3.3, p. 9: "then the combined random system is C(F)"].

```text
P • (step, init)
  = P • (drawStep, drawInit)                    ofProbAutomaton_eq_drawStep
  = (P.combine drawStep, (s, drawInit))          attach_ofDDC_ofProgramOn_ofDeterministic
  = (P.probCombine drawStep, (s, drawInit))      Program.ofDeterministic_combine
  = (P.probCombine recording, (s, (init, [])))   simulation of the recording step
  = (P.probCombine step, (s, init))              simulation that forgets the record
```

The last two equalities use `ofProbAutomaton_probCombine_eq_of_simulation`, respectively with
`ProbStep.simulatesAt_drawStep` and `ProbStep.simulatesAt_forget`. `drawStep` denotes its point
transition law when passed to `probCombine`.
-/
theorem attach_ofDDC_ofProgramOn_ofProbAutomaton
    -- `s` starts program `P`; `hb` bounds each invocation by `b` inside queries.
    (s : S) (P : Program S O J U V X Y) {b : ℕ} (hb : P.Bounded b)
    -- `hα` gives exactly the converter domain over `F`, using only inside histories in `E`.
    (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F))
    -- `step` samples a fresh transition per inside query; `init` samples the starting state.
    (step : ProbStep R J X Y) (init : Distribution.ProbDist R) :
    attach hE' hF' (ofDDC (DDC.ofProgramOn s P F) hα)
        (RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step init)
        (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine step hb)
        (init.map fun r => (s, r)) := by
  -- `L = m + b * n` covers both the inside domain and all calls by `n` invocations.
  let L := m + b * n
  -- Attachment depends on the random system only.
  have congr_attach : ∀ (α : PDCBehavior O J U V X Y E m hE F n hF)
      (R₁ R₂ : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
      (h₁ : R₁.RepliesAtQueriedInterface) (h₂ : R₂.RepliesAtQueriedInterface), R₁ = R₂ →
      attach hE' hF' α R₁ h₁ = attach hE' hF' α R₂ h₂ := by
    -- equal systems: the two proofs that it replies at the queried port are equal
    rintro α R₁ _ _ _ rfl
    rfl
  -- `m ≤ L` permits replacement by the deterministic automaton reading its retained table.
  rw [congr_attach _ _ _ _ (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _)
    (RandomSystem.ofProbAutomaton_eq_drawStep step init (L := L) (by omega))]
  -- Deterministic attachment gives the combined transition rule.
  rw [attach_ofDDC_ofProgramOn_ofDeterministic hE' hF' s P hb hα]
  -- Its point transitions are `probCombine` against the point transitions of `drawStep`.
  rw [Program.ofDeterministic_combine]
  -- Both simulations use one recorded draw per inside query and a reachable inside state.
  let inv : List (Σ j, X j) → R × List (ProbStep.Draw R J X Y) → Prop :=
    fun τ rd => rd.2.length = τ.length ∧ rd.1 ∈ step.reachable init.1 τ.length
  -- Each inside query appends one draw, from a reachable state (`recording_reachable`).
  have hpres : ∀ τ rd q, inv τ rd → τ.length < b * n →
      ∀ p ∈ (step.recording.outcome rd q).support, inv (τ ++ [q]) p.1 := by
    rintro τ rd q ⟨hl, hr⟩ - p hp
    simpa only [inv, List.length_append, List.length_singleton] using
      step.recording_reachable init.1 hl hr q hp
  -- Initially: no draws, from a state in the support of `init`.
  have hinit : ∀ rd ∈ (init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))).1.support,
      inv [] rd := fun _ hrd => step.recording_init_reachable init hrd
  -- Before the program's budget `b * n ≤ L`, the deterministic step on the table of draws
  -- simulates the recording step.
  have hsim : ∀ τ rd q, inv τ rd → τ.length < b * n →
      ProbStep.SimulatesAt step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L))
        (step.drawKernel init.1 L) rd q := by
    rintro τ rd q ⟨hl, hr⟩ hτ
    -- The invariant gives `rd.2.length = τ.length < b * n ≤ L` and reachability within `L`.
    exact step.simulatesAt_drawStep init.1 L rd (by omega)
      (step.reachable_mono init.1 (by omega) hr) q
  -- Transport the table simulation through `P`, starting from its kernel image `drawInit`.
  have draw := RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation (hF := hF) P hb
    step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L)) (step.drawKernel init.1 L)
    inv hpres hsim s _ hinit
  -- Transport the forgetting simulation through `P` to recover the original inside automaton.
  have forget := RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation (hF := hF) P hb
    step.recording step (fun rd => Distribution.ProbDist.single rd.1) inv hpres
    (fun τ rd q _ _ => step.simulatesAt_forget rd q) s _ hinit
  -- Forgetting the empty record returns the initial law `init`.
  rw [ProbStep.bind_forget] at forget
  -- `draw.symm` returns from the table to the recording automaton; `forget` removes the record.
  exact draw.symm.trans forget

end PDCBehavior

end SystemAlgebra

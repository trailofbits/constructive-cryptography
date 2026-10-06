import RandomSystems.Converter.ProgramAttachment
import RandomSystems.Converter.ConverterAttachment
import RandomSystems.System.ProbAutomaton

/-!
# Attaching a program to a probabilistic automaton

Run against a probabilistic automaton, a program answers each outside query by an invocation in
which the automaton answers the inside queries, from its state, with fresh steps. This is again a
probabilistic automaton, on pairs of states (`Program.probCombine`). The main theorem says that it
is the attachment of the program's converter to the automaton, as random systems:

```
        u            ┌─────┐   q        ┌───────────┐
  ─────────────────►│  P  ├───────────►│ automaton │        =    ┌─────────────────────┐
  ◄─────────────────┤ (s) │◄───────────┤ (step, r) │             │ P run against step  │
        v            └─────┘   y        └───────────┘             │ from (s, r)         │
                                                                  └─────────────────────┘
```

A system `C(·)` invoking an internal system `F` is the combined system `C(F)` [1, §3.3]; for a
deterministic automaton this is the inlining of `Program.inline_automatonSystem`. The
probabilistic case is reduced to it: a probabilistic automaton is a random automaton in the sense
of [1, Definition 2], a deterministic automaton whose internal randomness, a table of the draws of
every step from every reachable state, is sampled once with the initial state. Reading this table
in order is drawing afresh (a simulation, `simulatesAt_drawStep`), the program attached to each
deterministic automaton is the combined automaton, and the program respects simulations.

## Main definitions

* `Program.probInvoke`, `Program.probCombine`: an invocation against a probabilistic step, and
  the program run against a probabilistic automaton, a probabilistic automaton on pairs of states
* `ProbStep.reachable`, `ProbStep.recording`, `ProbStep.drawStep`, `ProbStep.drawKernel`: the
  states reachable from the initial law, the step recording its draws, the deterministic step
  reading pre-sampled draws, and the law of the draws given the recorded ones

## Main results

* `Program.ofDeterministic_combine`: against a deterministic automaton, the program run against its
  point steps is the combined automaton
* `Program.simulatesAt_probCombine`, `RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation`:
  a program respects simulations of the automaton it is run against
* `RandomSystem.ofProbAutomaton_eq_drawStep`: a probabilistic automaton is a deterministic
  automaton reading pre-sampled draws
* `PDCBehavior.attach_ofDDC_ofProgramOn_ofDeterministic`: attaching a program to a deterministic
  automaton with a random initial state
* `PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton`: attaching a program to a probabilistic
  automaton is the program run against it

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology – EUROCRYPT
   2002*, LNCS 2332, Springer, 2002.
-/

namespace SystemAlgebra

open Probability Probability.Distribution Classical

variable {S O J R : Type} {U V : O → Type} {X Y : J → Type}

/-! ### Programs against probabilistic steps -/

namespace Program

variable (P : Program S O J U V X Y) (stepR : ProbStep R J X Y)

/-- **An invocation against a probabilistic step**: the body runs from the exchanges `h`, the
automaton in the state `r` answering its inside queries, with at most `n` more of them; the law
of the next states and of the reply.

```
  body(h) = reply (s', v)   ⟶   point law at ((s', r), v)
  body(h) = query q         ⟶   (r', y) ← step r q;  continue from r' with h · (q, y)
```
-/
noncomputable def probInvoke (s : S) (o : O) (u : U o) :
    ℕ → R → List ((Σ j, X j) × (Σ j, Y j)) → Distribution ((S × R) × V o)
  | 0, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr _ => 0
  | n + 1, r, h => match P s o u h with
    | .inl a => Finsupp.single ((a.1, r), a.2) 1
    | .inr q => bindK (stepR.outcome r q) fun p => probInvoke s o u n p.1 (h ++ [(q, p.2)])

variable {P stepR}

/-- When the body replies, the invocation is the point law of its reply. -/
theorem probInvoke_inl {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {a : S × V o} (ha : P s o u h = .inl a) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u n r h = Finsupp.single ((a.1, r), a.2) 1 := by
  -- Whatever the number of queries left, the first case of the definition.
  cases n <;> simp [probInvoke, ha]

/-- When the body asks with no query left, the invocation has no mass. -/
theorem probInvoke_zero_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (r : R) :
    P.probInvoke stepR s o u 0 r h = 0 := by
  -- The second case of the definition with no query left.
  simp [probInvoke, hq]

/-- When the body asks `q`, the invocation draws a step and continues. -/
theorem probInvoke_succ_inr {s : S} {o : O} {u : U o} {h : List ((Σ j, X j) × (Σ j, Y j))}
    {q : Σ j, X j} (hq : P s o u h = .inr q) (n : ℕ) (r : R) :
    P.probInvoke stepR s o u (n + 1) r h =
      bindK (stepR.outcome r q) fun p => P.probInvoke stepR s o u n p.1 (h ++ [(q, p.2)]) := by
  -- The second case of the definition with a query left.
  simp [probInvoke, hq]

/-- An invocation is a nonnegative law. -/
theorem probInvoke_nonNeg (s : S) (o : O) (u : U o) :
    ∀ n r h, (P.probInvoke stepR s o u n r h).NonNeg := by
  -- Induction on the number of queries left: point laws, zero, or mixtures of nonnegative laws.
  intro n
  induction n with
  | zero =>
    intro r h
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    | inr q => rw [probInvoke_zero_inr hq]; exact fun _ => le_rfl
  | succ n ih =>
    intro r h
    cases hq : P s o u h with
    | inl a => rw [probInvoke_inl hq]; exact (isProbDist_single _).1
    | inr q =>
      rw [probInvoke_succ_inr hq]
      exact bindK_nonNeg (stepR.outcome_nonNeg r q) fun _ => ih _ _

/-- **A bounded program completes each invocation** against a probabilistic step. -/
theorem probInvoke_weight {b : ℕ} (hP : P.Bounded b) (s : S) (o : O) (u : U o) :
    ∀ n r h, P.Consistent s o u h → b ≤ n + h.length →
      (P.probInvoke stepR s o u n r h).weight = 1 := by
  intro n
  induction n with
  | zero =>
    intro r h hc hb
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: a point law
      rw [probInvoke_inl hq]; exact (isProbDist_single _).2
    | inr q =>
      -- a query with no query left: impossible, the body has made `b` queries already
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
/-- **The program run against a probabilistic automaton**, a probabilistic automaton on pairs of
states: each outside query runs an invocation, the automaton answering its inside queries. -/
noncomputable def probCombine {b : ℕ} (hP : P.Bounded b) : ProbStep (S × R) O U V :=
  fun sr o u => ⟨P.probInvoke stepR sr.1 o u b sr.2 [],
    probInvoke_nonNeg sr.1 o u b sr.2 [],
    probInvoke_weight hP sr.1 o u b sr.2 [] (consistent_nil P _ _ _) (by simp)⟩

/-- The law of a combined step is the invocation from the empty exchanges. -/
theorem probCombine_val {b : ℕ} (hP : P.Bounded b) (sr : S × R) (o : O) (u : U o) :
    (P.probCombine stepR hP sr o u).1 = P.probInvoke stepR sr.1 o u b sr.2 [] := rfl

/-- Against a deterministic automaton, an invocation is the point law of its completion. -/
theorem probInvoke_ofDeterministic (stepD : R → (j : J) → X j → R × Y j) (s : S) (o : O)
    (u : U o) : ∀ n r h v, P.invoke stepD s o u n r h = some v →
      P.probInvoke (ProbStep.ofDeterministic stepD) s o u n r h = Finsupp.single v 1 := by
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
theorem ofDeterministic_combine (stepD : R → (j : J) → X j → R × Y j) {b : ℕ}
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

variable {R₁ R₂ : Type} {stepR₁ : ProbStep R₁ J X Y} {stepR₂ : ProbStep R₂ J X Y}
  {K : R₁ → Distribution.ProbDist R₂} {E : List (Σ j, X j) → Prop}
  {invR : List (Σ j, X j) → R₁ → Prop}

variable (P) in
/-- After the inside queries `τ`, every inside query of an invocation at `⟨o, u⟩` in the state `s`
is admitted by `E`. -/
def AdmitsInvocation (E : List (Σ j, X j) → Prop) (s : S) (o : O) (u : U o)
    (τ : List (Σ j, X j)) : Prop :=
  ∀ h q, P.Consistent s o u h → P s o u h = .inr q → E (τ ++ h.map Prod.fst ++ [q])

/-- **An invocation along simulation steps** of the inside automata: from the kernel image of `r`,
the invocation against `stepR₂` is the invocation against `stepR₁` followed by the kernel. -/
theorem probInvoke_simulation
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      (bindK (K r).1 fun r₂ => P.probInvoke stepR₂ s o u n r₂ h) =
        bindK (P.probInvoke stepR₁ s o u n r h) fun p =>
          fTransform (fun r₂ => ((p.1.1, r₂), p.2)) (K p.1.2).1 := by
  -- Induction on the number of inside queries left.
  intro n
  induction n with
  | zero =>
    intro r h _ _
    cases hq : P s o u h with
    | inl a =>
      -- the body replies: the inside state is only moved by the kernel
      simp only [probInvoke_inl hq, bindK_single, one_smul]
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
      simp only [probInvoke_succ_inr hq]
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
              simpa using this
          -- regroup the two mixtures
        _ = _ := (bindK_bindK _ _ _).symm

/-- **The end of an invocation**: each outcome of an invocation is the reply of the body on its
own exchanges extending `h`, with the invariant on the inside queries made. -/
theorem probInvoke_support
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (s : S) (o : O) (u : U o) (τ : List (Σ j, X j)) (hgood : P.AdmitsInvocation E s o u τ) :
    ∀ n r h, P.Consistent s o u h → invR (τ ++ h.map Prod.fst) r →
      ∀ p ∈ (P.probInvoke stepR₁ s o u n r h).support, ∃ hf, P.Consistent s o u hf ∧
        h <+: hf ∧ P s o u hf = .inl (p.1.1, p.2) ∧ invR (τ ++ hf.map Prod.fst) p.1.2 := by
  -- Induction on the number of inside queries left.
  intro n
  induction n with
  | zero =>
    intro r h hc hr p hp
    cases hq : P s o u h with
    | inl a =>
      -- the body replies on `h` itself: the outcome is its reply
      rw [probInvoke_inl hq, Finsupp.mem_support_single] at hp
      rw [hp.1]
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
      obtain ⟨y, hy⟩ := stepR₁.mem_support_outcome hp'
      -- the draw keeps the invariant on the inside queries made
      have hr' : invR (τ ++ (h ++ [(q, p'.2)]).map Prod.fst) p'.1 := by
        simpa using hpres _ r q hr (hgood h q hc hq) p' hp'
      -- the rest of the invocation ends on exchanges extending `h · (q, y)` (induction)
      obtain ⟨hf, hcf, hpf, hf₁, hf₂⟩ := ih _ _ (hy ▸ hc.snoc hq y) hr' p hp
      exact ⟨hf, hcf, (List.prefix_append h _).trans hpf, hf₁, hf₂⟩

/-- The kernel on the inside state, the program state unchanged. -/
noncomputable def insideKernel (K : R₁ → Distribution.ProbDist R₂) (sr : S × R₁) :
    Distribution.ProbDist (S × R₂) :=
  (K sr.2).map fun r₂ => (sr.1, r₂)

variable (P) in
/-- **A program respects simulations**: when the inside queries of an invocation are admitted
and simulated, the program run against `stepR₂` simulates the program run against `stepR₁` along
the kernel on the inside state. -/
theorem simulatesAt_probCombine {b : ℕ} (hP : P.Bounded b)
    (hsim : ∀ τ r q, invR τ r → E (τ ++ [q]) → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (hpres : ∀ τ r q, invR τ r → E (τ ++ [q]) →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    {s : S} {r : R₁} {τ : List (Σ j, X j)} (hr : invR τ r) {x : Σ o, U o}
    (hgood : P.AdmitsInvocation E s x.1 x.2 τ) :
    ProbStep.SimulatesAt (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP) (insideKernel K)
      (s, r) x := by
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
  simp only [fTransform_fTransform, Function.comp_def]
  rfl

variable (P) in
/-- The outcomes of the program run against `stepR₁` come from the body's own exchanges, with the
invariant on the inside queries made. -/
theorem probCombine_support {b : ℕ} (hP : P.Bounded b)
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

```
  P run against stepR₁ from (s, r)   =   P run against stepR₂ from (s, K r)
```
-/
theorem RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation {F : List (Σ o, U o) → Prop}
    {n : ℕ} {hF : ∀ h, F h → h.length ≤ n} (P : Program S O J U V X Y) {b : ℕ}
    (hP : P.Bounded b) {R₁ R₂ : Type} (stepR₁ : ProbStep R₁ J X Y) (stepR₂ : ProbStep R₂ J X Y)
    (K : R₁ → Distribution.ProbDist R₂) (invR : List (Σ j, X j) → R₁ → Prop)
    (hpres : ∀ τ r q, invR τ r → τ.length < b * n →
      ∀ p ∈ (stepR₁.outcome r q).support, invR (τ ++ [q]) p.1)
    (hsim : ∀ τ r q, invR τ r → τ.length < b * n → ProbStep.SimulatesAt stepR₁ stepR₂ K r q)
    (s : S) (init : Distribution.ProbDist R₁) (hinit : ∀ r ∈ init.1.support, invR [] r) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine stepR₁ hP)
        (init.map fun r => (s, r)) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine stepR₂ hP)
        ((init.bind K).map fun r => (s, r)) := by
  -- The inside queries admitted: those before the total budget, `τ ++ [q]` of length `≤ b * n`.
  let E : List (Σ j, X j) → Prop := fun τ => τ.length ≤ b * n
  -- The hypotheses, at the admitted inside queries.
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
    nlinarith
  -- The outside invariant: some inside history `τ`, at most `b` queries per outside query,
  -- satisfies `invR` at the inside state.
  let inv : List (Σ o, U o) → S × R₁ → Prop :=
    fun xs sr => ∃ τ, invR τ sr.2 ∧ τ.length ≤ b * xs.length
  -- Each outside step keeps it: an invocation adds its own exchanges `hf`, at most `b`.
  have hpres_out : ∀ xs sr x, inv xs sr → F (xs ++ [x]) →
      ∀ p ∈ ((P.probCombine stepR₁ hP).outcome sr x).support, inv (xs ++ [x]) p.1 := by
    rintro xs sr x ⟨τ, hτ, hl⟩ hx p hp
    obtain ⟨hf, hcf, hinv⟩ := Program.probCombine_support P hP hpres' hτ
      (good xs sr x τ hl hx) p hp
    refine ⟨τ ++ hf.map Prod.fst, hinv, ?_⟩
    have := Program.Consistent.length_le hP hcf
    simp only [List.length_append, List.length_map, List.length_singleton]
    nlinarith
  -- Each outside step is a simulation step: the program respects the inside simulation.
  have hsim_out : ∀ xs sr x, inv xs sr → F (xs ++ [x]) →
      ProbStep.SimulatesAt (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP)
        (Program.insideKernel K) sr x := by
    rintro xs sr x ⟨τ, hτ, hl⟩ hx
    exact Program.simulatesAt_probCombine P hP hsim' hpres' hτ (good xs sr x τ hl hx)
  -- Initially the inside history is empty.
  have hinit_out : ∀ sr ∈ (init.map fun r => (s, r)).1.support, inv [] sr := by
    intro sr hsr
    obtain ⟨r, hr, rfl⟩ := mem_support_fTransform _ _ hsr
    exact ⟨[], hinit r hr, le_refl _⟩
  -- Equal random systems along the outside simulation ...
  rw [RandomSystem.ofProbAutomaton_eq_of_simulation (E := F) (bound := n) (hE := hF)
    (P.probCombine stepR₁ hP) (P.probCombine stepR₂ hP) (Program.insideKernel K) inv hpres_out
    hsim_out _ hinit_out]
  -- ... from the kernel image of `(s, r)` for `r ← init`: `(s, r₂)` for `r₂ ← init.bind K`.
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

/-- **The step recording its draws**: it steps as `step` and appends the draw to its record. -/
noncomputable def recording : ProbStep (R × List (Draw R J X Y)) J X Y :=
  fun rd j x => (step rd.1 j x).map fun o =>
    ((o.1, rd.2 ++ [((rd.1, ⟨j, x⟩), tagged ⟨j, x⟩ o)]), o.2)

/-- The outcome of the recording step: a draw of `step`, appended to the record. -/
theorem outcome_recording (rd : R × List (Draw R J X Y)) (x : Σ j, X j) :
    step.recording.outcome rd x =
      fTransform (fun o => ((o.1, rd.2 ++ [((rd.1, x), o)]), o.2)) (step.outcome rd.1 x) := by
  -- Both are the step's law, pushed forward along the same map.
  simp only [outcome, recording, ProbDist.map_val, fTransform_fTransform]
  rfl

/-- **Forgetting the record** is a simulation. -/
theorem simulatesAt_forget (rd : R × List (Draw R J X Y)) (x : Σ j, X j) :
    SimulatesAt step.recording step (fun rd => Distribution.ProbDist.single rd.1) rd x := by
  unfold SimulatesAt
  -- From the recorded state, `step` steps as the recording step, forgetting the record.
  simp only [Distribution.ProbDist.single, bindK_single, one_smul, outcome_recording,
    bindK_fTransform, Function.comp_def, fTransform_single]
  exact (bindK_single_one _).symm

/-- The reply at the queried port from a tagged draw, or the default `d`. -/
noncomputable def untag (x : Σ j, X j) (o : R × Σ j, Y j) (d : R × Y x.1) : R × Y x.1 :=
  if h : o.2.1 = x.1 then (o.1, h ▸ o.2.2) else d

@[simp] theorem untag_tagged (x : Σ j, X j) (o : R × Y x.1) (d : R × Y x.1) :
    untag x (tagged x o) d = o := by
  simp [untag, tagged]

/-- The initial law with an empty record, forgetting the record, is the initial law. -/
theorem bind_forget (init : Distribution.ProbDist R) :
    ((init.map fun r => (r, ([] : List (Draw R J X Y)))).bind
      fun rd => Distribution.ProbDist.single rd.1) = init := by
  apply Subtype.ext
  -- Pairing with the empty record and keeping the state is the point kernel.
  simp only [ProbDist.bind_val, ProbDist.map_val, Distribution.ProbDist.single,
    bindK_fTransform, Function.comp_def]
  exact bindK_single_one _

variable [Fintype (Σ j, X j)] (init : Distribution R)

/-- **The states reachable** from the initial law in at most `k` steps. -/
noncomputable def reachable : ℕ → Finset R
  | 0 => init.support
  | k + 1 => reachable k ∪ (reachable k).biUnion fun r =>
      Finset.univ.biUnion fun x => (step.outcome r x).support.image Prod.fst

/-- More steps reach more states. -/
theorem reachable_mono {k k' : ℕ} (h : k ≤ k') :
    step.reachable init k ⊆ step.reachable init k' := by
  -- Each step adds states to the reachable ones.
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- A possible next state from a state reachable in `k` steps is reachable in `k + 1`. -/
theorem mem_reachable_succ {k : ℕ} {r : R} (hr : r ∈ step.reachable init k) {x : Σ j, X j}
    {p : R × Σ j, Y j} (hp : p ∈ (step.outcome r x).support) :
    p.1 ∈ step.reachable init (k + 1) :=
  Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_biUnion.mpr
    ⟨x, Finset.mem_univ _, Finset.mem_image_of_mem _ hp⟩⟩)

/-- **The record after `k` draws**: `k` draws, from a state reachable in `k` steps; one more draw
keeps this. -/
theorem recording_reachable {k : ℕ} {rd : R × List (Draw R J X Y)} (hl : rd.2.length = k)
    (hr : rd.1 ∈ step.reachable init k) (x : Σ j, X j)
    {p : (R × List (Draw R J X Y)) × Σ j, Y j} (hp : p ∈ (step.recording.outcome rd x).support) :
    p.1.2.length = k + 1 ∧ p.1.1 ∈ step.reachable init (k + 1) := by
  -- The recording step draws `o` from `step` and appends it to the record.
  rw [outcome_recording] at hp
  obtain ⟨o, ho, rfl⟩ := mem_support_fTransform _ _ hp
  -- One more draw in the record, and the next state of a possible draw.
  exact ⟨by simp [hl], step.mem_reachable_succ init hr ho⟩

variable (L : ℕ)

/-- A cell of the table of draws: a step number below `L`, a reachable state and a query. -/
abbrev Cell := Fin L × {r // r ∈ step.reachable init L} × (Σ j, X j)

/-- **The deterministic step reading pre-sampled draws**: in the state `r` with `k` steps done
and the table `t`, the query `x` is answered by the draw in the cell `(k, r, x)`.

```
  state (r, k, t)  ──x──►  (t(k, r, x) = (r', y))  ──►  state (r', k + 1, t), reply y
```
-/
noncomputable def drawStep :
    R × ℕ × (step.Cell init L → R × Σ j, Y j) → (j : J) → X j →
      (R × ℕ × (step.Cell init L → R × Σ j, Y j)) × Y j :=
  fun rkt j x =>
    let d := Classical.choice (step rkt.1 j x).nonempty
    if h : rkt.2.1 < L ∧ rkt.1 ∈ step.reachable init L then
      let o := untag ⟨j, x⟩ (rkt.2.2 (⟨rkt.2.1, h.1⟩, ⟨rkt.1, h.2⟩, ⟨j, x⟩)) d
      ((o.1, rkt.2.1 + 1, rkt.2.2), o.2)
    else ((rkt.1, rkt.2.1 + 1, rkt.2.2), d.2)

/-- The law of the draw in a cell, given the recorded draws: the recorded one if the cell was
read, a fresh step otherwise. -/
noncomputable def drawLaw (rec : List (Draw R J X Y)) (c : step.Cell init L) :
    Distribution (R × Σ j, Y j) :=
  if h : c.1.val < rec.length then
    if rec[c.1.val].1 = (c.2.1.val, c.2.2) then Finsupp.single rec[c.1.val].2 1
    else step.outcome c.2.1.val c.2.2
  else step.outcome c.2.1.val c.2.2

/-- The law of a cell is a probability law: a point mass or a step. -/
theorem drawLaw_isProbDist (rec : List (Draw R J X Y)) (c : step.Cell init L) :
    (step.drawLaw init L rec c).isProbDist := by
  unfold drawLaw
  split_ifs
  · exact isProbDist_single _
  · exact fTransform_isProbDist _ (step _ _ _).2
  · exact fTransform_isProbDist _ (step _ _ _).2

/-- **The law of the table given the recorded draws**: the recorded cells fixed, the others
independent fresh steps; with the state and the number of steps done. -/
noncomputable def drawKernel (rd : R × List (Draw R J X Y)) :
    Distribution.ProbDist (R × ℕ × (step.Cell init L → R × Σ j, Y j)) :=
  ProbDist.map (fun t => (rd.1, rd.2.length, t))
    ⟨pi (step.drawLaw init L rd.2), pi_isProbDist fun c => step.drawLaw_isProbDist init L rd.2 c⟩

/-- Recording a draw in a cell fixes that cell. -/
theorem update_drawLaw (rec : List (Draw R J X Y)) (r : R) (x : Σ j, X j) (o : R × Σ j, Y j)
    (hk : rec.length < L) (hr : r ∈ step.reachable init L) :
    Function.update (step.drawLaw init L rec) (⟨rec.length, hk⟩, ⟨r, hr⟩, x) (Finsupp.single o 1) =
      step.drawLaw init L (rec ++ [((r, x), o)]) := by
  -- Compare cell by cell.
  funext c
  by_cases hc : c = (⟨rec.length, hk⟩, ⟨r, hr⟩, x)
  · -- the new cell: the recorded draw `o`
    subst hc
    simp [drawLaw]
  · rw [Function.update_of_ne hc]
    unfold drawLaw
    by_cases hlt : c.1.val < rec.length
    · -- an earlier cell: the same record
      rw [dif_pos hlt, dif_pos (by simp; omega), List.getElem_append_left hlt]
    · by_cases heq : c.1.val = rec.length
      · -- a cell of the current step at another state or query: still a fresh step
        rw [dif_neg hlt, dif_pos (by simp; omega)]
        have hget : (rec ++ [((r, x), o)])[c.1.val]'(by simp; omega) = ((r, x), o) := by
          simp [heq]
        rw [hget, if_neg]
        -- the new record is at another state or query than `c`
        intro h
        obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
        apply hc
        obtain ⟨⟨k, hk'⟩, ⟨r', hr'⟩, x'⟩ := c
        simp only at heq h₁ h₂
        subst heq h₁ h₂
        rfl
      · -- a later cell: a fresh step
        rw [dif_neg hlt, dif_neg (by simp; omega)]

/-- **Reading the next cell is drawing afresh**: while fewer than `L` steps are done from a
reachable state, the deterministic step on the table of draws simulates the recording step,
along the law of the table given the record.

```
  (r, rec) ──── recording, x ────► ((r', rec · ((r, x), (r', y))), y)
     │                                        │
  drawKernel                               drawKernel
     ▼                                        ▼
  (r, k, t) ──── drawStep, x ────► ((r', k + 1, t), y)      t(k, r, x) = (r', y)
```
-/
theorem simulatesAt_drawStep (rd : R × List (Draw R J X Y)) (hk : rd.2.length < L)
    (hr : rd.1 ∈ step.reachable init L) (x : Σ j, X j) :
    SimulatesAt step.recording (ofDeterministic (step.drawStep init L)) (step.drawKernel init L)
      rd x := by
  obtain ⟨r, rec⟩ := rd
  obtain ⟨j, x⟩ := x
  simp only at hk hr
  -- The cell read now: step `rec.length`, state `r`, query `x`.
  set c : step.Cell init L := (⟨rec.length, hk⟩, ⟨r, hr⟩, ⟨j, x⟩)
  -- Its law given the record is a fresh step of `step` from `r`.
  have hentry : step.drawLaw init L rec c = step.outcome r ⟨j, x⟩ := by
    simp [drawLaw, c]
  -- The deterministic step reads the cell `c` (fewer than `L` steps, reachable state).
  have hread : ∀ t : step.Cell init L → R × Σ j, Y j,
      step.drawStep init L (r, rec.length, t) j x =
        (((untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).1, rec.length + 1, t),
          (untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).2) := by
    intro t
    simp only [drawStep, dif_pos (And.intro hk hr), c]
  unfold SimulatesAt
  calc bindK (step.drawKernel init L (r, rec)).1
        (fun st => (ofDeterministic (step.drawStep init L)).outcome st ⟨j, x⟩)
      -- the table `t` is sampled, and the deterministic step reads `t c`
      = fTransform (fun t => (((untag ⟨j, x⟩ (t c) (Classical.choice (step r j x).nonempty)).1,
            rec.length + 1, t), (⟨j, (untag ⟨j, x⟩ (t c)
              (Classical.choice (step r j x).nonempty)).2⟩ : Σ j, Y j)))
          (pi (step.drawLaw init L rec)) := by
        simp only [drawKernel, ProbDist.map_val, bindK_fTransform, Function.comp_def,
          outcome_ofDeterministic, hread]
        exact bindK_single_comp _ _
      -- sample the cell `c` first: a fresh step `o`, then the table with `c` fixed to `o`
    _ = bindK (step.outcome r ⟨j, x⟩) fun o =>
          fTransform (fun t => (((untag ⟨j, x⟩ o (Classical.choice (step r j x).nonempty)).1,
            rec.length + 1, t), (⟨j, (untag ⟨j, x⟩ o
              (Classical.choice (step r j x).nonempty)).2⟩ : Σ j, Y j)))
          (pi (step.drawLaw init L (rec ++ [((r, ⟨j, x⟩), o)]))) := by
        -- the independent table, disintegrated at the cell `c`, whose law is a fresh step
        rw [pi_eq_bindK_update _ c, fTransform_bindK, hentry]
        refine bindK_congr fun o _ => ?_
        -- with `c` fixed to `o`, the table is the table given the record with `o` appended ...
        rw [update_drawLaw step init L rec r ⟨j, x⟩ o hk hr]
        -- ... and every possible such table has `o` in the cell `c`
        refine fTransform_congr_support fun t ht => ?_
        rw [← update_drawLaw step init L rec r ⟨j, x⟩ o hk hr] at ht
        rw [eq_of_mem_support_pi_update _ _ o ht]
      -- the fresh step is the recording step's draw, and the table with the record is the
      -- kernel image of the recorded state
    _ = _ := by
        simp only [outcome_recording, drawKernel, ProbDist.map_val, bindK_fTransform,
          Function.comp_def, fTransform_fTransform, List.length_append, List.length_singleton]
        -- draw from the untagged step on both sides
        rw [outcome, bindK_fTransform, bindK_fTransform]
        refine bindK_congr fun o _ => ?_
        -- untagging a tagged draw gives it back
        simp only [Function.comp_def, untag_tagged]
        rfl

end ProbStep

/-- The draws of the initial law: no step done, all cells fresh. -/
noncomputable def ProbStep.drawInit [Fintype (Σ j, X j)] (step : ProbStep R J X Y)
    (init : Distribution.ProbDist R) (L : ℕ) :
    Distribution.ProbDist (R × ℕ × (step.Cell init.1 L → R × Σ j, Y j)) :=
  (init.map fun r => (r, [])).bind (step.drawKernel init.1 L)

section

variable [Fintype (Σ j, X j)] [Fintype (Σ j, Y j)]

/-- **A probabilistic automaton is a random automaton** [1, Definition 2]: on any input domain
of at most `L` queries, it is the deterministic automaton reading a table of pre-sampled draws,
the table sampled once with the initial state.

```
  (step, init)  =  (recording, (init, []))  =  (drawStep, (r, 0, t) for r ← init, t ← draws)
```
-/
theorem RandomSystem.ofProbAutomaton_eq_drawStep {E : List (Σ j, X j) → Prop} {m : ℕ}
    {hE : ∀ h, E h → h.length ≤ m} (step : ProbStep R J X Y) (init : Distribution.ProbDist R)
    {L : ℕ} (hL : m ≤ L) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step init =
      RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE)
        (ProbStep.ofDeterministic (step.drawStep init.1 L)) (step.drawInit init L) := by
  -- The invariant of the recording step: one draw per query, from a reachable state.
  let inv : List (Σ j, X j) → R × List (ProbStep.Draw R J X Y) → Prop :=
    fun xs rd => rd.2.length = xs.length ∧ rd.1 ∈ step.reachable init.1 xs.length
  have hpres : ∀ xs rd x, inv xs rd → E (xs ++ [x]) →
      ∀ p ∈ (step.recording.outcome rd x).support, inv (xs ++ [x]) p.1 := by
    rintro xs rd x ⟨hl, hr⟩ - p hp
    obtain ⟨h₁, h₂⟩ := step.recording_reachable init.1 hl hr x hp
    exact ⟨by simpa using h₁, by simpa using h₂⟩
  have hinit : ∀ rd ∈ (init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))).1.support,
      inv [] rd := by
    intro rd hrd
    obtain ⟨r, hr, rfl⟩ := mem_support_fTransform _ _ hrd
    exact ⟨rfl, hr⟩
  -- Along the domain, fewer than `L` steps are done, from states reachable in `L` steps: the
  -- deterministic step on the table of draws simulates the recording step.
  have hsim : ∀ xs rd x, inv xs rd → E (xs ++ [x]) →
      ProbStep.SimulatesAt step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L))
        (step.drawKernel init.1 L) rd x := by
    rintro xs rd x ⟨hl, hr⟩ hx
    have hlen := hE _ hx
    simp only [List.length_append, List.length_singleton] at hlen
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
      _ = _ := RandomSystem.ofProbAutomaton_eq_of_simulation step.recording _ _ inv hpres hsim _
        hinit

end

/-! ### Attaching a program -/

namespace PDCBehavior

variable [Fintype O] [Fintype J] [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)]
  [∀ j, Fintype (Y j)] {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}
  (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
  (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)

/-- **Attaching a program to a deterministic automaton** with a random initial state: the
combined automaton, its initial state paired with the program's. -/
theorem attach_ofDDC_ofProgramOn_ofDeterministic (s : S) (P : Program S O J U V X Y) {b : ℕ}
    (hb : P.Bounded b) (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F))
    (stepR : R → (j : J) → X j → R × Y j) (init : Distribution.ProbDist R) :
    attach hE' hF' (ofDDC (DDC.ofProgramOn s P F) hα)
        (RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE)
          (ProbStep.ofDeterministic stepR) init)
        (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF)
        (ProbStep.ofDeterministic (P.combine stepR hb)) (init.map fun r => (s, r)) := by
  -- The automaton started in `r`, on the domain `E`, as a deterministic system with domain `E`.
  let aut : R → {t : InterfaceSystem J X Y //
      IsDDS t ∧ RepliesAtQueriedInterface t ∧ ∀ h, (t h).Dom ↔ E h} := fun r =>
    ⟨filterDom E (automatonSystem stepR r),
      (automatonSystem_isDDS stepR r).filterDom _ hE'.2,
      fun h x y hy => automatonSystem_replies stepR r h x y ((filterDom_mem_iff _ _ _ _).mp hy).2,
      fun h => by
        rw [filterDom_dom, automatonSystem_dom]
        exact ⟨fun hd => hd.1, fun hd => ⟨hd, fun he => hE'.1 (he ▸ hd)⟩⟩⟩
  -- Its random initial state presents the probabilistic automaton of its point steps.
  have hQ : ∀ h, behaviorMass (init.map aut).1 (h.map Prod.fst) (h.map Prod.snd) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) (ProbStep.ofDeterministic stepR)
        init h := by
    intro h
    rw [RandomSystem.ofProbAutomaton_ofDeterministic_apply]
    exact mass_fTransform _ _ _
  apply RandomSystem.ext
  intro t
  -- Present the converter by its DDC and the automaton by its deterministic systems.
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
  exact iff_of_eq (congrArg (fun z => Replies z (t.map Prod.fst) (t.map Prod.snd))
    (Program.trim_apply_ofProgramOn_automaton stepR hb s r hE' hF' hα))

/-- **Attaching a program to a probabilistic automaton is the program run against it**: on the
inside domain `E`, the converter of a bounded program on the outside domain `F`, attached to the
probabilistic automaton of `step` started from `init`, is the probabilistic automaton of the
program run against `step`, started from `s` and `init` [1, §3.3].

```
  P(s) attached to (step, init)   =   P run against step, from (s, r) for r ← init
```

The proof presents the automaton by pre-sampled draws and uses the deterministic case:

```
  P • (step, init)
    = P • (drawStep, draws)                       a random automaton   ofProbAutomaton_eq_drawStep
    = (P.combine drawStep, (s, draws))            deterministic case   …_ofDeterministic
    = (P run against drawStep, (s, draws))        point steps          ofDeterministic_combine
    = (P run against recording, (s, (init, [])))  P respects the simulation
    = (P run against step, (s, init))             P respects forgetting the record
```
-/
theorem attach_ofDDC_ofProgramOn_ofProbAutomaton (s : S) (P : Program S O J U V X Y) {b : ℕ}
    (hb : P.Bounded b) (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F))
    (step : ProbStep R J X Y) (init : Distribution.ProbDist R) :
    attach hE' hF' (ofDDC (DDC.ofProgramOn s P F) hα)
        (RandomSystem.ofProbAutomaton (Domain.ofInputs E m hE) step init)
        (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _) =
      RandomSystem.ofProbAutomaton (Domain.ofInputs F n hF) (P.probCombine step hb)
        (init.map fun r => (s, r)) := by
  -- Pre-sampled draws for at most `L = m + b * n` steps: enough for the inside domain and for
  -- the inside queries of `n` invocations.
  let L := m + b * n
  -- Attachment depends on the random system only.
  have congr_attach : ∀ (α : PDCBehavior O J U V X Y E m hE F n hF)
      (R₁ R₂ : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE))
      (h₁ : R₁.RepliesAtQueriedInterface) (h₂ : R₂.RepliesAtQueriedInterface), R₁ = R₂ →
      attach hE' hF' α R₁ h₁ = attach hE' hF' α R₂ h₂ := by
    rintro α R₁ _ _ _ rfl
    rfl
  -- Step 1: the automaton is the deterministic automaton reading pre-sampled draws.
  rw [congr_attach _ _ _ _ (RandomSystem.ofProbAutomaton_repliesAtQueriedInterface _ _ _)
    (RandomSystem.ofProbAutomaton_eq_drawStep step init (L := L) (by omega))]
  -- Step 2: attached to a deterministic automaton, the program is the combined automaton ...
  rw [attach_ofDDC_ofProgramOn_ofDeterministic hE' hF' s P hb hα]
  -- Step 3: ... which is the program run against the point steps of the deterministic automaton.
  rw [Program.ofDeterministic_combine]
  -- Steps 4 and 5: the program respects the simulations of Step 1, from the recorded initial
  -- law. The invariant: one draw per inside query, from a reachable state.
  let inv : List (Σ j, X j) → R × List (ProbStep.Draw R J X Y) → Prop :=
    fun τ rd => rd.2.length = τ.length ∧ rd.1 ∈ step.reachable init.1 τ.length
  have hpres : ∀ τ rd q, inv τ rd → τ.length < b * n →
      ∀ p ∈ (step.recording.outcome rd q).support, inv (τ ++ [q]) p.1 := by
    rintro τ rd q ⟨hl, hr⟩ - p hp
    obtain ⟨h₁, h₂⟩ := step.recording_reachable init.1 hl hr q hp
    exact ⟨by simpa using h₁, by simpa using h₂⟩
  have hinit : ∀ rd ∈ (init.map fun r => (r, ([] : List (ProbStep.Draw R J X Y)))).1.support,
      inv [] rd := by
    intro rd hrd
    obtain ⟨r, hr, rfl⟩ := mem_support_fTransform _ _ hrd
    exact ⟨rfl, hr⟩
  -- Before the program's budget `b * n ≤ L`, the deterministic step on the table of draws
  -- simulates the recording step.
  have hsim : ∀ τ rd q, inv τ rd → τ.length < b * n →
      ProbStep.SimulatesAt step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L))
        (step.drawKernel init.1 L) rd q := by
    rintro τ rd q ⟨hl, hr⟩ hτ
    exact step.simulatesAt_drawStep init.1 L rd (by omega)
      (step.reachable_mono init.1 (by omega) hr) q
  -- Step 4: the program run against the recording step is the one against the table of draws.
  have draw := RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation (hF := hF) P hb
    step.recording (ProbStep.ofDeterministic (step.drawStep init.1 L)) (step.drawKernel init.1 L)
    inv hpres hsim s _ hinit
  -- Step 5: it is also the one against `step`, forgetting the record ...
  have forget := RandomSystem.ofProbAutomaton_probCombine_eq_of_simulation (hF := hF) P hb
    step.recording step (fun rd => Distribution.ProbDist.single rd.1) inv hpres
    (fun τ rd q _ _ => step.simulatesAt_forget rd q) s _ hinit
  -- ... from the initial law `init` itself.
  rw [ProbStep.bind_forget] at forget
  exact draw.symm.trans forget

end PDCBehavior

end SystemAlgebra

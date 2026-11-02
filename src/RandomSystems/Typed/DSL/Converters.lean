module

public import RandomSystems.Typed.DSL.Programs
public import RandomSystems.Typed.Filter
public import RandomSystems.Typed.Source
public import RandomSystems.Typed.Parallel

/-!
# Programs as converters

A program `P` from outside interface `A` to inside interface `B` becomes a typed converter
when its inside queries stay in `B.domain`. `ofProgram`, `ofCostedProgram`, and
`ofPreservingProgram` establish this from total, exact-cost, or selected-port bounds.

Attaching it to an automaton runs `P` and the automaton together, the combined system `C(F)`
of [1, §3.3, p. 9: "then the combined random system is C(F)"]:

```text
     u                 x
A ──────► [P, state s] ───B──► [stepR, state r ← initial]
  ◄──────              ◄──────
     v                 y
```

`ofDDC_ofProgramOn_smul_ofPDS` reduces each transcript probability to deterministic inlining.
`ofDDC_ofProgramOn_smul_ofAutomaton` then identifies the combined rule `P.combine stepR hb`
and initial law `(r ↦ (s, r))_* initial`. Its three typed corollaries preserve the same draw,
while their domain hypotheses select the applicable converter constructor.

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology —
   EUROCRYPT 2002*, LNCS 2332, pp. 110–132, Springer, 2002. Page numbers refer to the preprint.
-/

@[expose] public section

namespace SystemAlgebra

-- `S` carries the program state, retained between outside queries.
variable {S : Type}

open Classical in
/-- Run `P` from `s` on `A.domain`; each outside query makes at most `b` inside queries.
The total inside length is at most `b * A.bound`. -/
noncomputable def TypedConverter.ofProgram
    -- `A` is the outside interface, `B` the inside interface, and `s` the initial program state.
    {A B : Interface} (s : S)
    -- `P` supplies the query/reply rule; `hb` bounds inside queries per invocation by `b`.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hB` admits every nonempty inside history within that total bound.
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs) : TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      -- An empty inside history needs no admission; otherwise the length bound gives it.
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      · exact Or.inr (hB _ hne
          (DDC.insideQueries_length_le_of_budget hb A.length_le hr hF)))

open Classical in
/-- Run `P` from `s` on `A.domain`, making `cost u` inside queries on outside query `u`.
An outside history of total cost at most `q` gives at most `q` inside queries. -/
noncomputable def TypedConverter.ofCostedProgram
    -- `A` is the outside interface, `B` the inside interface; `s` starts the retained state.
    {A B : Interface} (s : S)
    -- `P` gives the interaction rule; `hb` bounds each invocation by `b` inside queries.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hc` gives exact per-query counts `cost`; `hA` bounds their sum by `q` on `A.domain`.
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    -- `hB` admits every nonempty inside history of length at most `q`.
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs) : TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      -- Exact invocation costs sum to a bound on the inside history.
      · refine Or.inr (hB _ hne ((DDC.insideQueries_length_le_of_costs hc hr).trans ?_))
        rcases hF with he | hF
        · rw [he]; exact Nat.zero_le _
        · exact hA _ hF)

open Classical in
/-- Run `P` from `s` on `A.domain`, with at most `q o` inside queries at each selected
port `j` where `ι o = some j`. All inside queries together number at most `b * A.bound`. -/
noncomputable def TypedConverter.ofPreservingProgram
    -- `A`, `B` are the outside and inside interfaces; `s` starts the retained program state.
    {A B : Interface} (s : S)
    -- `P` gives the interaction rule; `hb` bounds all inside queries per invocation by `b`.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `ι` selects protected inside ports. `hι` permits a call at `ι o'` only from `o = o'`,
    -- at most once per invocation; calls to other ports still count toward `b`.
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    -- `hA` bounds outside calls at `o` by `q o`; `hB` admits the resulting inside histories.
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys) :
    TypedConverter A B :=
  TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain)
    (DDC.ofProgramOn_isDDCFrom hb A.nonempty_prefix.2 fun h hr hF => by
      by_cases hne : insideQueries (h.map Prod.snd) = []
      · exact Or.inl hne
      -- Port preservation transfers each outside count; `hb` bounds the total count.
      · refine Or.inr (hB _ hne (DDC.insideQueries_length_le_of_budget hb A.length_le hr hF)
          fun o j hj => (DDC.insideQueries_restrict_length_le hι hr hj).trans ?_)
        rcases hF with he | hF
        · rw [he]; exact Nat.zero_le _
        · exact hA _ hF o)

/-- A tensor admits a history with left-port counts `≤ q o` and total length `≤ k`
when `A` admits those port counts and `B` admits length `≤ k`. -/
lemma Interface.perPort_tensor_admits
    -- `A`, `B` are the left and right interfaces; `q o` bounds calls at each left port `o`.
    {A B : Interface} (q : A.I → ℕ)
    -- `hA` admits left histories whose port counts obey `q`.
    (hA : ∀ xs, xs ≠ [] → (∀ o, (SystemAlgebra.restrict o xs).length ≤ q o) → A.domain xs)
    -- `k` bounds the total history; `hB` admits each nonempty right projection of length `≤ k`.
    {k : ℕ} (hB : ∀ xs, xs ≠ [] → xs.length ≤ k → B.domain xs) :
    ∀ ys, ys ≠ [] → ys.length ≤ k → (∀ o, (SystemAlgebra.restrict (Sum.inl o) ys).length ≤ q o) →
      (Interface.tensor A B).domain ys := by
  classical
  intro ys hne hl hc
  -- Project the history to each component and check its own domain.
  refine ⟨hne, ?_, ?_⟩
  · by_cases he : SystemAlgebra.restrict none (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hA _ he fun o => by
        rw [SystemAlgebra.restrict_restrict_sumAlphabet]
        exact hc o)
  · by_cases he :
        SystemAlgebra.restrict (some ()) (ys.map (sumAlphabet (Sum.rec A.X B.X)).symm) = []
    · exact Or.inl he
    · exact Or.inr (hB _ he ((SystemAlgebra.length_restrict_le _ _).trans (by simpa using hl)))

/-- The probability of transcript `t` after attachment is the `Q`-mass of deterministic
systems whose inlined program answers `t` on `A.domain`. -/
lemma TypedConverter.ofDDC_ofProgramOn_smul_ofPDS
    -- `A`, `B` are outside and inside interfaces; `s : S` starts the retained program state.
    {A B : Interface} (s : S)
    -- `P` is the program; `hb` bounds each invocation by `b` inside queries.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hα` gives exactly the converter domain over `A.domain`, using only `B.domain` queries.
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    -- `Q` samples a deterministic system with exactly `B.domain` and port-correct replies.
    (Q : Probability.Distribution.ProbDist {r : InterfaceSystem B.I B.X B.Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ B.domain h})
    -- `t` records the outside query/reply pairs whose cumulative probability is compared.
    (t : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hα • TypedSystem.ofPDS Q).1 t =
      Q.1.mass fun r =>
        Replies (filterDom A.domain (P.inline r.1 b s)) (t.map Prod.fst) (t.map Prod.snd) := by
  -- Attachment samples the same inside system from `Q` and applies the deterministic program.
  rw [TypedConverter.smul_val, PDCBehavior.attach_presents B.nonempty_prefix A.nonempty_prefix _ _ _
    ⟨Finsupp.single ⟨_, hα⟩ 1, Probability.Distribution.isProbDist_single _⟩ Q (fun _ => rfl)
    (fun _ => rfl) t, behaviorMass_attachPDS, Probability.Distribution.prod_single_left,
    Probability.Distribution.mass_fTransform]
  -- For each sampled system, attachment and inlining give the same outside replies.
  refine Probability.Distribution.mass_congr _ fun r => ?_
  rw [Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2]

/-- Attachment gives `P.combine stepR hb` with initial law `(r ↦ (s, r))_* initial`.
The automaton's sampled state remains one retained draw. -/
lemma TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton
    -- `A`, `B` are outside and inside interfaces; `R` carries the inside state and `s : S`
    -- starts the program state.
    {A B : Interface} {R : Type} (s : S)
    -- `P` gives the interaction rule; `hb` bounds each invocation by `b` inside queries.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hα` gives exactly the converter domain over `A.domain`, using only `B.domain` queries.
    (hα : IsDDCFrom B.domain A.domain b (DDC.ofProgramOn s P A.domain))
    -- `stepR` answers inside queries; `initial` samples its retained starting state `r : R`.
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofDDC (DDC.ofProgramOn s P A.domain) hα •
        TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        (Probability.Distribution.ProbDist.map (fun r => (s, r)) initial) := by
  -- Both transcript probabilities are masses over the same starting draw `r ← initial`.
  apply Subtype.ext
  apply RandomSystem.ext
  intro t
  rw [TypedSystem.ofAutomaton_mass]
  conv_lhs => rw [TypedSystem.ofAutomaton]
  rw [TypedConverter.ofDDC_ofProgramOn_smul_ofPDS s P hb hα,
    Probability.Distribution.ProbDist.map_val,
    Probability.Distribution.mass_fTransform, Probability.Distribution.mass_fTransform]
  -- Deterministic program attachment is `P.combine stepR hb` at each fixed `r`.
  refine Probability.Distribution.mass_congr _ fun r => ?_
  change Replies (filterDom A.domain (P.inline (filterDom B.domain (automatonSystem stepR r)) b s))
    _ _ ↔ _
  rw [← Program.trim_apply_ofProgramOn s hb A.domain A.nonempty_prefix.2,
    Program.trim_apply_ofProgramOn_automaton stepR hb s r B.nonempty_prefix A.nonempty_prefix hα]

/-- The total-length constructor has combined initial law `(r ↦ (s, r))_* initial`. -/
lemma TypedConverter.ofProgram_smul_ofAutomaton
    -- `A`, `B` are outside and inside interfaces; `R` carries inside states, `s : S` the start.
    {A B : Interface} {R : Type} (s : S)
    -- `P` makes at most `b` inside calls per invocation; `hB` admits their total length.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → B.domain xs)
    -- `stepR` updates the inside state; `initial` samples its retained starting value.
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofProgram s P hb hB • TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        (Probability.Distribution.ProbDist.map (fun r => (s, r)) initial) :=
  TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ stepR initial

/-- The selected-port constructor has combined initial law `(r ↦ (s, r))_* initial`. -/
lemma TypedConverter.ofPreservingProgram_smul_ofAutomaton
    -- `A`, `B` are outside and inside interfaces; `R` carries inside states, `s : S` the start.
    {A B : Interface} {R : Type} (s : S)
    -- `P` makes at most `b` inside calls per invocation, as certified by `hb`.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hι` transfers outside counts to the selected ports `ι o`; `q o` bounds those counts.
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    -- `hA` bounds outside counts; `hB` admits the total length and selected inside counts.
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    -- `stepR` updates the inside state; `initial` samples its retained starting value.
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofPreservingProgram s P hb ι hι q hA hB •
        TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        (Probability.Distribution.ProbDist.map (fun r => (s, r)) initial) :=
  TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ stepR initial

/-- The exact-cost constructor has combined initial law `(r ↦ (s, r))_* initial`.
The cost hypotheses type the converter; its DDC remains `DDC.ofProgramOn s P A.domain`. -/
lemma TypedConverter.ofCostedProgram_smul_ofAutomaton
    -- `A`, `B` are outside and inside interfaces; `R` carries inside states, `s : S` the start.
    {A B : Interface} {R : Type} (s : S)
    -- `P` gives the interaction rule; `hb` bounds each invocation by `b` inside queries.
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    -- `hc` fixes each invocation's query count to `cost`; `q` bounds their sum via `hA`.
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    -- `hB` admits the resulting inside histories.
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs)
    -- `stepR` updates the inside state; `initial` samples its retained starting value.
    (stepR : R → (j : B.I) → B.X j → R × B.Y j) (initial : Probability.Distribution.ProbDist R) :
    TypedConverter.ofCostedProgram s P hb cost hc hA hB •
        TypedSystem.ofAutomaton B stepR initial =
      TypedSystem.ofAutomaton A (P.combine stepR hb)
        (Probability.Distribution.ProbDist.map (fun r => (s, r)) initial) :=
  TypedConverter.ofDDC_ofProgramOn_smul_ofAutomaton s P hb _ stepR initial

end SystemAlgebra

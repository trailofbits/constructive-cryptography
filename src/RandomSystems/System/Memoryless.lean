import RandomSystems.Converter.ProbProgramAttachment

/-!
# Memoryless systems

A system is memoryless when the law of its reply depends only on the current query, never on the
history: a source "can be memoryless or have memory" [1, Definition 3.1, p. 55], and a single-input
system given by a conditional distribution `p_{Y|X}` is a "discrete memoryless channel"
[1, §3.6.1, p. 65]. As a random system, a memoryless system is given by its conditional reply
laws, which are those of the current query alone, as for the beacon, whose conditional law is
`1/|Y|` "for all choices of the arguments" [1, Example 3.8, p. 68].

A probabilistic automaton whose reply law does not depend on its state is memoryless, and a
program run against memoryless replies replies memorylessly, with the law of one invocation fed
with fresh samples of the inside laws. So attaching a program to a memoryless system gives a
memoryless system, whatever the number of the program's inside queries:

```
        o(u)          ┌───┐   j(q)      ┌──────────┐
  ──────────────────►│ P ├────────────►│ mem(ν)   │      =      mem(κ)
  ◄──────────────────┤   │◄────────────┤          │
        o ⇒ v         └───┘   j ⇒ y     └──────────┘      κ = the reply law of P against ν
```

## Main definitions

* `RandomSystem.memoryless D ν`: the memoryless system with the reply law `ν` on the domain `D`
* `RandomSystem.portLaw ν`: the reply law `ν i x` at the queried port `i`
* `RandomSystem.parallelLaw ν₁ ν₂`: the reply laws of two systems side by side
* `ProbStep.Memoryless step ν`: a probabilistic step replying with the law `ν` from every state
* `ProbStep.fresh ν`: fresh samples of `ν`, a step with no state
* `Program.replyLaw P ν`: the reply law of an invocation against inside replies of the laws `ν`

## Main results

* `RandomSystem.memoryless_snoc`, `RandomSystem.eq_memoryless_of_snoc`: the chain rule, and a
  random system obeying it is the memoryless system
* `RandomSystem.ofProbAutomaton_eq_memoryless`: an automaton with a memoryless step is the
  memoryless system of its reply law
* `Program.memoryless_probCombine`: a program run against a memoryless step is memoryless
* `PDCBehavior.attach_ofDDC_ofProgramOn_memoryless`: the composition law: attaching a program to
  the memoryless system of `ν` gives the memoryless system of its reply law against `ν`

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

namespace SystemAlgebra

open Probability Probability.Distribution Classical

/-! ### Memoryless systems -/

namespace RandomSystem

variable {A B : Type} [Fintype A] [Fintype B]

/-- **The memoryless system** with the reply law `ν` [1, Definition 3.1, §3.6.1]: on the domain
`D`, the reply to the query `x` is a fresh sample of `ν x`, independent of the history. -/
noncomputable def memoryless (D : Domain A B) (ν : A → ProbDist B) : RandomSystem A B D :=
  -- A random system is given by its conditional reply laws (`ofConditional`). Here the law at
  -- the history `h` and the query `x` ignores `h`: it is `ν x`.
  ofConditional fun _ x _ => ν x

/-- **The chain rule**: one more exchange multiplies the probability of a transcript by the
reply law, when the domain admits the query. -/
lemma memoryless_snoc (D : Domain A B) (ν : A → ProbDist B) (h : List (A × B)) (x : A)
    (y : B) :
    memoryless D ν (h ++ [(x, y)]) = if D h x then memoryless D ν h * (ν x).1 y else 0 := by
  -- `ofConditional_snoc` is the chain rule of any system given by conditional laws ...
  have chain := ofConditional_snoc (D := D) (fun _ x _ => ν x) h x y
  -- ... stated with a dependent `if`; ours does not use the proof that `D h x`.
  rw [dite_eq_ite] at chain
  exact chain

/-- **A random system obeying the chain rule of `ν` is the memoryless system** of `ν`: when each
admitted exchange multiplies the probability by the reply law `ν`. -/
lemma eq_memoryless_of_snoc {D : Domain A B} {ν : A → ProbDist B} {R : RandomSystem A B D}
    (hR : ∀ h x y, D h x → R (h ++ [(x, y)]) = R h * (ν x).1 y) : R = memoryless D ν := by
  -- Compare the probabilities of every transcript, by induction, one exchange at a time.
  ext t
  induction t using List.reverseRecOn with
  | nil =>
    -- the empty transcript has probability one on both sides
    rw [mass_nil, mass_nil]
  | append_singleton t e ih =>
    obtain ⟨x, y⟩ := e
    -- the chain rule of the memoryless system
    rw [memoryless_snoc]
    split_ifs with hd
    · -- an admitted query: both multiply the probability of `t` by `ν x y`
      rw [hR t x y hd, ih]
    · -- a query outside the domain has no reply
      exact R.mass_eq_zero_of_not_admitted hd y

variable {I : Type} {X Y : I → Type}

/-- **The reply law at the queried port**: for a query `x` at the port `i`, the law `ν i x` of
the reply, as a law on replies tagged with their port. -/
noncomputable def portLaw (ν : ∀ i, X i → ProbDist (Y i)) (x : Σ i, X i) :
    ProbDist (Σ i, Y i) :=
  ProbDist.map (Sigma.mk x.1) (ν x.1 x.2)

/-- The reply law at the queried port, at a reply at that port. -/
lemma portLaw_apply_mk (ν : ∀ i, X i → ProbDist (Y i)) (i : I) (x : X i) (y : Y i) :
    (portLaw ν ⟨i, x⟩).1 ⟨i, y⟩ = (ν i x).1 y :=
  -- Tagging by the port is injective.
  fTransform_injective_apply _ _ sigma_mk_injective y

/-- The reply law at the queried port gives no mass to replies at another port. -/
lemma portLaw_apply_of_ne (ν : ∀ i, X i → ProbDist (Y i)) {x : Σ i, X i} {y : Σ i, Y i}
    (h : y.1 ≠ x.1) : (portLaw ν x).1 y = 0 :=
  -- Every tagged reply is at the port `x.1`.
  fTransform_apply_of_forall_ne _ _ _ fun _ ha => h (ha ▸ rfl)

variable {J : Type} {X₁ Y₁ : I → Type} {X₂ Y₂ : J → Type}

/-- **The reply laws of two systems side by side**: a query at a left port has the left law, one
at a right port the right law. -/
def parallelLaw (ν₁ : ∀ i, X₁ i → ProbDist (Y₁ i)) (ν₂ : ∀ j, X₂ j → ProbDist (Y₂ j)) :
    ∀ l : I ⊕ J, Sum.rec (motive := fun _ => Type) X₁ X₂ l →
      ProbDist (Sum.rec (motive := fun _ => Type) Y₁ Y₂ l)
  | .inl i, x => ν₁ i x
  | .inr j, x => ν₂ j x

end RandomSystem

/-! ### Memoryless steps -/

namespace ProbStep

variable {S I : Type} {X Y : I → Type}

/-- **A memoryless step** with the reply law `ν`: from every state, the reply to `x` at `i` has
the law `ν i x`. -/
def Memoryless (step : ProbStep S I X Y) (ν : ∀ i, X i → ProbDist (Y i)) : Prop :=
  -- `step s i x` is a law on pairs (next state, reply); forgetting the next state leaves `ν i x`
  ∀ s i x, fTransform Prod.snd (step s i x).1 = (ν i x).1

/-- From any state, a memoryless step replies `y` with the probability its reply law gives `y`. -/
lemma Memoryless.mass_outcome {step : ProbStep S I X Y} {ν : ∀ i, X i → ProbDist (Y i)}
    (hν : step.Memoryless ν) (s : S) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.outcome s x).mass (·.2 = y) = (RandomSystem.portLaw ν x).1 y := by
  -- The probability that the reply is `y` is the pushforward to the reply, evaluated at `y`.
  rw [← fTransform_apply_eq_mass]
  -- `outcome` is the step at the port `x.1`, the reply tagged by the port.
  rw [outcome, fTransform_fTransform]
  -- Tagging and then keeping the reply is keeping the reply and then tagging it.
  rw [show (Prod.snd ∘ tagged x) = Sigma.mk x.1 ∘ Prod.snd from rfl, ← fTransform_fTransform]
  -- The step is memoryless: its reply law is `ν x.1 x.2`, whatever the state `s`.
  rw [hν s x.1 x.2]
  -- What remains is the definition of `portLaw`.
  rfl

/-- **Fresh samples** of `ν`: a step with no state, answering the query `x` at `i` with a new
sample of `ν i x`. -/
noncomputable def fresh (ν : ∀ i, X i → ProbDist (Y i)) : ProbStep Unit I X Y :=
  fun _ i x => (ν i x).map fun y => ((), y)

/-- **Fresh samples are memoryless.** -/
lemma memoryless_fresh (ν : ∀ i, X i → ProbDist (Y i)) : (fresh ν).Memoryless ν := by
  intro _ i x
  -- The step pairs a sample of `ν i x` with the trivial state; keeping the reply undoes this.
  simp only [fresh, ProbDist.map_val, fTransform_fTransform]
  exact fTransform_id _

end ProbStep

/-- **A probabilistic automaton with a memoryless step is the memoryless system** of its reply
law. -/
lemma RandomSystem.ofProbAutomaton_eq_memoryless {S I : Type} {X Y : I → Type}
    [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] (D : Domain (Σ i, X i) (Σ i, Y i))
    {step : ProbStep S I X Y} {ν : ∀ i, X i → ProbDist (Y i)} (hν : step.Memoryless ν)
    (init : ProbDist S) :
    RandomSystem.ofProbAutomaton D step init = RandomSystem.memoryless D (portLaw ν) := by
  -- It suffices to check the chain rule of `portLaw ν` at every admitted exchange `(x, y)`:
  --
  --   P(t · (x, y)) = ∑ₛ belief_t(s) · Pr[step s x replies y]      (state laws)
  --                 = (∑ₛ belief_t(s)) · ν x y                       (memoryless step)
  --                 = P(t) · ν x y
  refine eq_memoryless_of_snoc fun t x y hd => ?_
  -- the probability of `t · (x, y)` is the weight of the state law after it
  rw [ofProbAutomaton_apply, ProbStep.belief_snoc, if_pos hd]
  -- the weight of the transition: the old state law, weighted by the reply probabilities
  rw [ProbStep.weight_transition]
  -- every state replies `y` with the same probability (the step is memoryless) ...
  simp only [hν.mass_outcome]
  -- ... which factors out of the sum, leaving the weight of the old state law
  rw [ofProbAutomaton_apply, weight, Finsupp.sum_mul]

/-! ### Programs against memoryless steps -/

namespace Program

variable {S O J R : Type} {U V : O → Type} {X Y : J → Type} (P : Program S O J U V X Y)

/-- **The reply law of an invocation** against inside replies of the laws `ν`: the body runs
from the exchanges `h`, with at most `n` more inside queries, and each inside query `q` is
answered by a fresh sample of `ν q`. -/
noncomputable def replyLaw (ν : ∀ j, X j → ProbDist (Y j)) (s : S) (o : O) (u : U o) :
    ℕ → List ((Σ j, X j) × (Σ j, Y j)) → Distribution (V o)
  -- No inside query is left: the body must reply now (otherwise no mass).
  | 0, h => match P s o u h with
    | .inl a => Finsupp.single a.2 1
    | .inr _ => 0
  -- The body replies (a point law on its reply), or asks `q` and continues with `y ← ν q`.
  | n + 1, h => match P s o u h with
    | .inl a => Finsupp.single a.2 1
    | .inr q => bindK (ν q.1 q.2).1 fun y => replyLaw ν s o u n (h ++ [(q, ⟨q.1, y⟩)])

variable {P}

/-- When the body replies, the reply law is the point law on its reply. -/
lemma replyLaw_inl {ν : ∀ j, X j → ProbDist (Y j)} {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} {a : S × V o} (ha : P s o u h = .inl a) (n : ℕ) :
    P.replyLaw ν s o u n h = Finsupp.single a.2 1 := by
  -- Whatever the number of queries left, the first case of the definition.
  cases n <;> simp [replyLaw, ha]

/-- When the body asks `q`, the reply law samples the answer `y ← ν q` and continues. -/
lemma replyLaw_succ_inr {ν : ∀ j, X j → ProbDist (Y j)} {s : S} {o : O} {u : U o}
    {h : List ((Σ j, X j) × (Σ j, Y j))} {q : Σ j, X j} (hq : P s o u h = .inr q) (n : ℕ) :
    P.replyLaw ν s o u (n + 1) h =
      bindK (ν q.1 q.2).1 fun y => P.replyLaw ν s o u n (h ++ [(q, ⟨q.1, y⟩)]) := by
  -- The second case of the definition with a query left.
  simp [replyLaw, hq]

/-- **An invocation against a memoryless step** replies with the reply law of the program,
whatever the state of the step. -/
lemma fTransform_snd_probInvoke {stepR : ProbStep R J X Y} {ν : ∀ j, X j → ProbDist (Y j)}
    (hν : stepR.Memoryless ν) (s : S) (o : O) (u : U o) :
    ∀ n r h, fTransform Prod.snd (P.probInvoke stepR s o u n r h) = P.replyLaw ν s o u n h := by
  -- `probInvoke` runs the body against the step, tracking (next states, reply). Looking only at
  -- the reply, the state of the step drops out: each inside answer has the law `ν q`.
  -- Induction on the number `n` of inside queries still allowed.
  intro n
  induction n with
  | zero =>
    intro r h
    cases hq : P s o u h with
    | inl a =>
      -- the body replies `a.2`: a point law on both sides
      simp [probInvoke_inl hq, replyLaw_inl hq, fTransform]
    | inr q =>
      -- the body asks, but no query is left: no mass on both sides
      simp [probInvoke_zero_inr hq, replyLaw, hq, fTransform]
  | succ n ih =>
    intro r h
    cases hq : P s o u h with
    | inl a =>
      -- the body replies `a.2`: a point law on both sides
      simp [probInvoke_inl hq, replyLaw_inl hq, fTransform]
    | inr q =>
      -- the body asks `q`: the invocation draws the step's (next state, answer) and continues
      rw [probInvoke_succ_inr hq, replyLaw_succ_inr hq]
      -- move the projection to the reply inside the draw
      rw [fTransform_bindK]
      -- the step's answer law, with the state forgotten, is `ν q` (memoryless)
      rw [← hν r q.1 q.2, bindK_fTransform]
      -- the continuation's reply law does not depend on the next state (induction hypothesis)
      simp only [ih, ProbStep.outcome, bindK_fTransform]
      rfl

/-- **A program run against a memoryless step is memoryless**, when its reply law against `ν` is
the same `κ` in every state of the program. -/
lemma memoryless_probCombine {stepR : ProbStep R J X Y} {ν : ∀ j, X j → ProbDist (Y j)}
    (hν : stepR.Memoryless ν) {b : ℕ} (hb : P.Bounded b) {κ : ∀ o, U o → ProbDist (V o)}
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1) :
    (P.probCombine stepR hb).Memoryless κ := by
  -- The combined step runs one invocation from the pair of states `(s, r)`.
  intro sr o u
  -- Its reply law is the program's reply law against `ν` from `s` (previous theorem) ...
  have reply := fTransform_snd_probInvoke (P := P) hν sr.1 o u b sr.2 []
  -- ... which is `κ o u` by hypothesis.
  exact reply.trans (hκ sr.1 o u)

end Program

/-! ### The composition law -/

namespace PDCBehavior

variable {S O J : Type} {U V : O → Type} {X Y : J → Type} [Fintype O] [Fintype J]
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)] [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- **The composition law for memoryless systems**: attaching the converter of a bounded program,
whose reply law against `ν` is `κ` in every state, to the memoryless system of `ν` gives the
memoryless system of `κ`.

```
  P • mem(ν) = mem(κ)        κ o u = the law of P's reply to o(u) when every inside query
                                     j(q) is answered by a fresh sample of ν j q
```
-/
theorem attach_ofDDC_ofProgramOn_memoryless
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) (s : S) (P : Program S O J U V X Y)
    {b : ℕ} (hb : P.Bounded b) (hα : IsDDCFrom E F b (DDC.ofProgramOn s P F))
    {ν : ∀ j, X j → ProbDist (Y j)} {κ : ∀ o, U o → ProbDist (V o)}
    (hκ : ∀ s o u, P.replyLaw ν s o u b [] = (κ o u).1)
    {R : RandomSystem (Σ j, X j) (Σ j, Y j) (Domain.ofInputs E m hE)}
    (hR : R = RandomSystem.memoryless _ (RandomSystem.portLaw ν))
    (hRq : R.RepliesAtQueriedInterface) :
    attach hE' hF' (ofDDC (DDC.ofProgramOn s P F) hα) R hRq =
      RandomSystem.memoryless (Domain.ofInputs F n hF) (RandomSystem.portLaw κ) := by
  -- Step 1: the memoryless system of `ν` is the automaton of fresh samples of `ν`.
  have hfresh : R = RandomSystem.ofProbAutomaton _ (ProbStep.fresh ν)
      (Distribution.ProbDist.single ()) :=
    hR.trans (RandomSystem.ofProbAutomaton_eq_memoryless _ (ProbStep.memoryless_fresh ν) _).symm
  subst hfresh
  -- Step 2: attached to an automaton, the program is the program run against its step ...
  rw [attach_ofDDC_ofProgramOn_ofProbAutomaton hE' hF' s P hb hα]
  -- Step 3: ... a memoryless step of law `κ`, so the memoryless system of `κ`.
  exact RandomSystem.ofProbAutomaton_eq_memoryless _
    (Program.memoryless_probCombine (ProbStep.memoryless_fresh ν) hb hκ) _

end PDCBehavior

end SystemAlgebra

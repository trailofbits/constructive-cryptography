import RandomSystems.System.Automaton
import RandomSystems.Cumulative.Cumulative
import RandomSystems.PDS.Filter
import Probability.Kernel

/-!
# Probabilistic automata

A probabilistic automaton answers a query at a port from its state with a law on the next state
and the reply at that port (a probabilistic step). Its random system is given by its state laws
along a transcript: after a transcript `h`, the sub-law `belief h` of the states reached with the
replies of `h`, whose weight is the probability of `h`. One more exchange `port(x)`, `port ⇒ y`
moves this sub-law by one step and keeps the states that replied `y`:

```
  belief (h · (x, y)) (s') = ∑ₛ belief h (s) · Pr[step s x = (s', y)]      (if the domain admits x)
  P(h)                     = ∑ₛ belief h (s)
```

Two probabilistic automata have the same random system along a **simulation**: a kernel from the
states of the first to those of the second such that, from the kernel image of a state, a step of
the second is a step of the first followed by the kernel. A deterministic automaton is the
probabilistic automaton of its point steps, and its random system is the one of the distribution
over deterministic systems its initial law induces [1, Definition 2].

## Main definitions

* `ProbStep S I X Y`: a probabilistic step
* `ProbStep.outcome`, `ProbStep.transition`: the law of the next state and the reply, and the
  states reached with a given reply
* `ProbStep.belief D step init h`: the sub-law of the states after the transcript `h`
* `RandomSystem.ofProbAutomaton D step init`: the random system of a probabilistic automaton
* `ProbStep.SimulatesAt step₁ step₂ K s x`: a simulation step along the kernel `K`
* `ProbStep.ofDeterministic step`: the probabilistic step of a deterministic automaton

## Main results

* `RandomSystem.ofProbAutomaton_repliesAtQueriedInterface`: a probabilistic automaton replies at
  the queried port
* `ProbStep.belief_simulation`, `RandomSystem.ofProbAutomaton_eq_of_simulation`: along a
  simulation the state laws correspond, and the random systems are equal
* `RandomSystem.ofProbAutomaton_ofDeterministic_apply`: a deterministic automaton with a random
  initial state is the probabilistic automaton of its point steps

## References

1. U. Maurer. Indistinguishability of Random Systems. In *Advances in Cryptology – EUROCRYPT
   2002*, LNCS 2332, Springer, 2002.
-/

namespace SystemAlgebra

open Probability Probability.Distribution Classical

/-- **A probabilistic step**: from a state and a query at the port `i`, a law on the next state
and the reply at `i`. -/
abbrev ProbStep (S I : Type) (X Y : I → Type) :=
  S → (i : I) → X i → Distribution.ProbDist (S × Y i)

namespace ProbStep

variable {S I : Type} {X Y : I → Type} (step : ProbStep S I X Y)

/-- The next state with the reply tagged by the queried port. -/
def tagged (x : Σ i, X i) (sy : S × Y x.1) : S × Σ i, Y i := (sy.1, ⟨x.1, sy.2⟩)

/-- **The outcome** of the query `x` in the state `s`: the law of the next state and the reply,
tagged by the queried port. -/
noncomputable def outcome (s : S) (x : Σ i, X i) : Distribution (S × Σ i, Y i) :=
  fTransform (tagged x) (step s x.1 x.2).1

/-- An outcome is a nonnegative law: the tagged step. -/
theorem outcome_nonNeg (s : S) (x : Σ i, X i) : (step.outcome s x).NonNeg :=
  (step s x.1 x.2).2.1.fTransform _

/-- An outcome has weight one: the step is a probability law. -/
theorem weight_outcome (s : S) (x : Σ i, X i) : (step.outcome s x).weight = 1 := by
  -- Tagging the reply moves mass without changing it, and the step is a probability law.
  rw [outcome, weight_fTransform]
  exact (step s x.1 x.2).2.2

/-- The replies of an outcome are at the queried port. -/
theorem mem_support_outcome {s : S} {x : Σ i, X i} {p : S × Σ i, Y i}
    (hp : p ∈ (step.outcome s x).support) : ∃ y : Y x.1, p.2 = ⟨x.1, y⟩ := by
  -- A possible outcome is the tag of a possible step `(s', y)`, whose reply is at `x.1`.
  obtain ⟨a, -, rfl⟩ := mem_support_fTransform _ _ hp
  exact ⟨a.2, rfl⟩

/-- **The transition** of a state law on a query and its reply: the states reached with that
reply. -/
noncomputable def transition (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    Distribution S :=
  bindK β fun s => fTransform Prod.fst ((step.outcome s x).restrict fun sy => sy.2 = y)

/-- The law of the reply to the query `x` from the state law `β`. -/
noncomputable def replyLaw (β : Distribution S) (x : Σ i, X i) : Distribution (Σ i, Y i) :=
  bindK β fun s => fTransform Prod.snd (step.outcome s x)

/-- The weight of a transition: the probability, under the state law, of replying `y`. -/
theorem weight_transition (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.transition β x y).weight = β.sum fun s w => w * (step.outcome s x).mass (·.2 = y) := by
  -- The weight of a mixture weighs each law of the kernel; forgetting the reply keeps the
  -- weight, and the weight of a restriction is the mass of its event.
  rw [transition, weight_bindK]
  simp only [weight_fTransform, weight_restrict]

/-- The reply law at `y` is the weight of the transition with the reply `y`. -/
theorem replyLaw_apply (β : Distribution S) (x : Σ i, X i) (y : Σ i, Y i) :
    step.replyLaw β x y = (step.transition β x y).weight := by
  -- Both sides are `∑ₛ β s · Pr[step s x replies y]`.
  rw [weight_transition, replyLaw, bindK_apply]
  simp only [fTransform_apply_eq_mass]

/-- The reply law has the weight of the state law. -/
theorem weight_replyLaw (β : Distribution S) (x : Σ i, X i) :
    (step.replyLaw β x).weight = β.weight := by
  -- Each outcome is a probability law, so its reply law has weight one.
  rw [replyLaw, weight_bindK_of_weight fun s _ => by rw [weight_fTransform, weight_outcome]]

/-- A transition of a nonnegative state law is nonnegative. -/
theorem transition_nonNeg {β : Distribution S} (hβ : β.NonNeg) (x : Σ i, X i) (y : Σ i, Y i) :
    (step.transition β x y).NonNeg :=
  bindK_nonNeg hβ fun s => ((step.outcome_nonNeg s x).restrict _).fTransform _

/-- A reply at another port than the queried one is impossible. -/
theorem transition_eq_zero {β : Distribution S} {x : Σ i, X i} {y : Σ i, Y i} (hy : y.1 ≠ x.1) :
    step.transition β x y = 0 := by
  -- No outcome of `x` has its reply at `y.1`, so every restriction to the reply `y` is empty.
  have hr : ∀ s, (step.outcome s x).restrict (fun sy => sy.2 = y) = 0 := by
    intro s
    ext sy
    rw [restrict_apply]
    split_ifs with h
    · -- an outcome with reply `y` would be the tag of a step replying at `x.1`
      rw [outcome, fTransform_apply_eq_mass]
      exact mass_eq_zero_of_forall_not _ fun a ha => hy (by rw [← h, ← ha]; rfl)
    · rfl
  -- The kernel vanishes, so the mixture does.
  rw [transition]
  simp only [hr]
  exact (bindK_congr fun _ _ => fTransform_zero _).trans (bindK_zero_right β)

variable (D : Domain (Σ i, X i) (Σ i, Y i)) (init : Distribution S)

/-- The state laws along a reversed transcript. -/
noncomputable def beliefRev : List ((Σ i, X i) × (Σ i, Y i)) → Distribution S
  | [] => init
  | e :: rh => if D rh.reverse e.1 then step.transition (beliefRev rh) e.1 e.2 else 0

/-- **The state law after the transcript `h`**: the sub-law of the states reached with the
replies of `h`, started from `init`; zero once a query is outside the domain. -/
noncomputable def belief (h : List ((Σ i, X i) × (Σ i, Y i))) : Distribution S :=
  step.beliefRev D init h.reverse

@[simp] theorem belief_nil : step.belief D init [] = init := rfl

/-- One more exchange: the transition of the state law, if the domain admits the query. -/
theorem belief_snoc (h : List ((Σ i, X i) × (Σ i, Y i))) (x : Σ i, X i) (y : Σ i, Y i) :
    step.belief D init (h ++ [(x, y)]) =
      if D h x then step.transition (step.belief D init h) x y else 0 := by
  -- Reversed, the exchange `(x, y)` comes first: one step of `beliefRev`.
  simp [belief, beliefRev, List.reverse_append]

/-- The state laws of a nonnegative initial law are nonnegative. -/
theorem belief_nonNeg (hinit : init.NonNeg) (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (step.belief D init h).NonNeg := by
  -- Induction on the transcript: each exchange is a transition of a nonnegative law, or zero.
  induction h using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton h e ih =>
    rw [belief_snoc]
    split_ifs
    · exact step.transition_nonNeg ih _ _
    · exact fun _ => le_rfl

end ProbStep

variable {S I : Type} {X Y : I → Type} [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)]

/-- **The random system of a probabilistic automaton** with its initial state sampled from
`init`: the probability of a transcript is the weight of the state law after it. -/
noncomputable def RandomSystem.ofProbAutomaton (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S) :
    RandomSystem (Σ i, X i) (Σ i, Y i) D :=
  ⟨fun h => (step.belief D init.1 h).weight, init.2.2,
    fun h => (step.belief_nonNeg D init.1 init.2.1 h).weight_nonneg, fun h x =>
    -- At an admitted query, the replies have the law of the reply from the current state law;
    -- elsewhere no reply has mass.
    ⟨if D h x then step.replyLaw (step.belief D init.1 h) x else 0, fun y => by
      -- the reply `y` has the weight of the state law after `h · (x, y)` ...
      show _ = (step.belief D init.1 (h ++ [(x, y)])).weight
      rw [step.belief_snoc]
      split_ifs
      · -- ... which is the transition with the reply `y`
        exact step.replyLaw_apply _ _ _
      · -- ... or zero, outside the domain
        simp [weight], by
      -- the reply law has the weight of the state law after `h`, or zero outside the domain
      split_ifs
      · exact step.weight_replyLaw _ _
      · simp [weight]⟩⟩

/-- The probability of a transcript is the weight of the state law after it. -/
theorem RandomSystem.ofProbAutomaton_apply (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    RandomSystem.ofProbAutomaton D step init h = (step.belief D init.1 h).weight := rfl

/-- **A probabilistic automaton replies at the queried port.** -/
theorem RandomSystem.ofProbAutomaton_repliesAtQueriedInterface (D : Domain (Σ i, X i) (Σ i, Y i))
    (step : ProbStep S I X Y) (init : Distribution.ProbDist S) :
    (RandomSystem.ofProbAutomaton D step init).RepliesAtQueriedInterface := by
  intro h x y hy
  -- The probability of `h · (x, y)` is the weight of the state law after it ...
  rw [ofProbAutomaton_apply, step.belief_snoc]
  split_ifs
  · -- ... which is the transition with a reply at another port: no state is reached.
    rw [step.transition_eq_zero hy]
    simp [weight]
  · -- ... or zero, when the domain does not admit `x`.
    simp [weight]

/-! ### Simulations -/

namespace ProbStep

variable {S₁ S₂ : Type} (step₁ : ProbStep S₁ I X Y) (step₂ : ProbStep S₂ I X Y)

/-- **A simulation step** of `step₁` by `step₂` along the kernel `K`, at the state `s` and the
query `x`: from the kernel image of `s`, a step of `step₂` is a step of `step₁` from `s` followed
by the kernel, with the same reply.

```
        s ──── step₁, x ────► (s₁', y)
        │                        │
        K                        K
        ▼                        ▼
      K(s) ─── step₂, x ────► (s₂', y)
```
-/
def SimulatesAt (K : S₁ → Distribution.ProbDist S₂) (s : S₁) (x : Σ i, X i) : Prop :=
  bindK (K s).1 (fun s₂ => step₂.outcome s₂ x) =
    bindK (step₁.outcome s x) fun p => fTransform (fun s₂ => (s₂, p.2)) (K p.1).1

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- The states of a pushforward into pairs `(a, c)` with second component `y`. -/
theorem fTransform_fst_restrict_pair {A C : Type} (ν : Distribution A) (c y : C) :
    fTransform Prod.fst ((fTransform (fun a => (a, c)) ν).restrict fun p => p.2 = y) =
      if c = y then ν else 0 := by
  -- Restricting the pairs to the second component `y` keeps everything if `c = y` and nothing
  -- otherwise; then forgetting `c` gives back `ν`.
  rw [restrict_fTransform, fTransform_fTransform]
  split_ifs with h
  · rw [restrict_congr ν (Q := fun _ => True) fun _ => by simp [h]]
    rw [show (ν.restrict fun _ => True) = ν by ext; simp]
    exact fTransform_id ν
  · rw [restrict_congr ν (Q := fun _ => False) fun _ => by simp [h], restrict_false]
    exact fTransform_zero _

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **Transitions along simulation steps**: the transition of the kernel image is the kernel
image of the transition. -/
theorem transition_bindK {K : S₁ → Distribution.ProbDist S₂} {β : Distribution S₁}
    {x : Σ i, X i} (hsim : ∀ s ∈ β.support, SimulatesAt step₁ step₂ K s x) (y : Σ i, Y i) :
    step₂.transition (bindK β fun s => (K s).1) x y =
      bindK (step₁.transition β x y) fun s => (K s).1 := by
  -- Both sides are mixtures over `β`; compare them state by state.
  rw [transition, transition, bindK_bindK, bindK_bindK]
  refine bindK_congr fun s hs => ?_
  -- Left: from `K s`, the step of `step₂` restricted to the reply `y`, next states only.
  -- Move the restriction and the projection outside the mixture over `K s`.
  have hpush : (bindK (K s).1 fun s₂ =>
      fTransform Prod.fst ((step₂.outcome s₂ x).restrict fun sy => sy.2 = y)) =
      fTransform Prod.fst ((bindK (K s).1 fun s₂ => step₂.outcome s₂ x).restrict
        fun sy => sy.2 = y) := by
    rw [restrict_bindK, fTransform_bindK]
  rw [hpush]
  -- The simulation step replaces the mixture by the step of `step₁` followed by `K`.
  rw [hsim s hs]
  -- Move the restriction and projection back inside, over the outcomes `p` of `step₁`.
  rw [restrict_bindK, fTransform_bindK]
  -- For each outcome `p = (s₁', y')`: `K s₁'` if `y' = y`, nothing otherwise.
  simp only [fTransform_fst_restrict_pair]
  -- Keeping the outcomes with reply `y` and their next states is the right-hand side.
  rw [bindK_ite, bindK_fTransform]
  rfl

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **The state laws along a simulation**: if `step₂` simulates `step₁` along `K` at the states
satisfying an invariant of the inputs so far, at every query the domain admits, then after each
transcript the invariant holds on the states of `step₁`, and the state law of `step₂` is the
kernel image of that of `step₁`. -/
theorem belief_simulation (E : List (Σ i, X i) → Prop) (bound : ℕ)
    (hE : ∀ h, E h → h.length ≤ bound) (K : S₁ → Distribution.ProbDist S₂)
    (inv : List (Σ i, X i) → S₁ → Prop)
    (hpres : ∀ xs s x, inv xs s → E (xs ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1)
    (hsim : ∀ xs s x, inv xs s → E (xs ++ [x]) → SimulatesAt step₁ step₂ K s x)
    (init : Distribution S₁) (hinit : ∀ s ∈ init.support, inv [] s)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (∀ s ∈ (step₁.belief (Domain.ofInputs E bound hE) init h).support, inv (h.map Prod.fst) s) ∧
      step₂.belief (Domain.ofInputs E bound hE) (bindK init fun s => (K s).1) h =
        bindK (step₁.belief (Domain.ofInputs E bound hE) init h) fun s => (K s).1 := by
  -- Induction on the transcript, one exchange `(x, y)` at a time.
  induction h using List.reverseRecOn with
  | nil => exact ⟨hinit, rfl⟩
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    rw [belief_snoc, belief_snoc]
    split_ifs with hd
    · have hd' : E (h.map Prod.fst ++ [x]) := hd
      refine ⟨fun s hs => ?_, ?_⟩
      · -- A state after `h · (x, y)` is reached by a step from a state after `h`, which
        -- satisfies the invariant; the step preserves it.
        obtain ⟨s₀, hs₀, hs⟩ := mem_support_bindK hs
        obtain ⟨p, hp, rfl⟩ := mem_support_fTransform _ _ hs
        have hp' : p ∈ (step₁.outcome s₀ x).support := support_restrict_subset _ _ hp
        simpa using hpres _ _ x (ih.1 s₀ hs₀) hd' p hp'
      · -- The state law of `step₂` after `h` is the kernel image (induction hypothesis), and
        -- transitions commute with the kernel along simulation steps.
        rw [ih.2]
        exact transition_bindK step₁ step₂ (fun s hs => hsim _ s x (ih.1 s hs) hd') y
    · -- The query is not admitted: both state laws are zero.
      exact ⟨fun s hs => absurd hs (by simp), by simp⟩

end ProbStep

/-- **Equal random systems along a simulation**: if `step₂` simulates `step₁` along `K` at the
states satisfying an invariant of the inputs so far, at every query the domain admits, the
probabilistic automata are the same random system, `step₂` started from the kernel image of the
initial law of `step₁`. -/
theorem RandomSystem.ofProbAutomaton_eq_of_simulation {E : List (Σ i, X i) → Prop} {bound : ℕ}
    {hE : ∀ h, E h → h.length ≤ bound} {S₁ S₂ : Type} (step₁ : ProbStep S₁ I X Y)
    (step₂ : ProbStep S₂ I X Y) (K : S₁ → Distribution.ProbDist S₂)
    (inv : List (Σ i, X i) → S₁ → Prop)
    (hpres : ∀ xs s x, inv xs s → E (xs ++ [x]) →
      ∀ p ∈ (step₁.outcome s x).support, inv (xs ++ [x]) p.1)
    (hsim : ∀ xs s x, inv xs s → E (xs ++ [x]) → ProbStep.SimulatesAt step₁ step₂ K s x)
    (init : Distribution.ProbDist S₁) (hinit : ∀ s ∈ init.1.support, inv [] s) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs E bound hE) step₁ init =
      RandomSystem.ofProbAutomaton (Domain.ofInputs E bound hE) step₂ (init.bind K) := by
  -- Compare the probabilities of every transcript `h`.
  apply RandomSystem.ext
  intro h
  rw [ofProbAutomaton_apply, ofProbAutomaton_apply]
  -- The state law of `step₂` after `h` is the kernel image of that of `step₁` ...
  rw [ProbDist.bind_val, (ProbStep.belief_simulation step₁ step₂ E bound hE K inv hpres hsim
    init.1 hinit h).2]
  -- ... and a kernel of probability laws preserves the weight.
  rw [weight_bindK_of_weight fun s _ => (K s).2.2]

/-! ### Deterministic automata -/

namespace ProbStep

/-- **The probabilistic step of a deterministic automaton**: the point law of its step. -/
noncomputable def ofDeterministic (step : S → (i : I) → X i → S × Y i) : ProbStep S I X Y :=
  fun s i x => Distribution.ProbDist.single (step s i x)

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- The outcome of a point step: the point mass at the step's next state and tagged reply. -/
theorem outcome_ofDeterministic (step : S → (i : I) → X i → S × Y i) (s : S) (x : Σ i, X i) :
    (ofDeterministic step).outcome s x =
      Finsupp.single ((step s x.1 x.2).1, (⟨x.1, (step s x.1 x.2).2⟩ : Σ i, Y i)) 1 := by
  -- The point law of the step, with its reply tagged by the port.
  simp [outcome, ofDeterministic, Distribution.ProbDist.single, fTransform, tagged]

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- The transition of a deterministic step moves the states that reply `y` to their next state. -/
theorem transition_ofDeterministic (step : S → (i : I) → X i → S × Y i) (β : Distribution S)
    (x : Σ i, X i) (y : Σ i, Y i) :
    (ofDeterministic step).transition β x y = fTransform (fun s => (step s x.1 x.2).1)
      (β.restrict fun s => (⟨x.1, (step s x.1 x.2).2⟩ : Σ i, Y i) = y) := by
  -- Each state has one outcome; restricted to the reply `y` it is that outcome or nothing.
  rw [transition]
  simp only [outcome_ofDeterministic, single_restrict]
  -- A kernel vanishing off an event is the kernel on the restriction, here a point kernel.
  rw [← bindK_single_comp, ← bindK_ite]
  refine bindK_congr fun s _ => ?_
  split_ifs <;> simp [fTransform]

omit [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)] in
/-- **The state law of a deterministic automaton** on an input domain: the initial states from
which the automaton gives the transcript, moved to the state they reach. -/
theorem belief_ofDeterministic (step : S → (i : I) → X i → S × Y i) (E : List (Σ i, X i) → Prop)
    (bound : ℕ) (hE : ∀ h, E h → h.length ≤ bound) (init : Distribution S)
    (h : List ((Σ i, X i) × (Σ i, Y i))) :
    (ofDeterministic step).belief (Domain.ofInputs E bound hE) init h =
      fTransform (fun s => stateAfter step s (h.map Prod.fst)) (init.restrict fun s =>
        Replies (filterDom E (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd)) := by
  induction h using List.reverseRecOn with
  | nil =>
    -- No exchange: every initial state gives the empty transcript, and stays where it is.
    simp only [belief_nil, List.map_nil, stateAfter_nil, replies_nil]
    rw [show (init.restrict fun _ => True) = init by ext; simp]
    exact (fTransform_id init).symm
  | append_singleton h e ih =>
    obtain ⟨x, y⟩ := e
    -- The automaton from `s` gives `h · (x, y)` when it gives `h`, the domain admits `x`, and
    -- its reply from the state after `h` is `y`.
    have hrep : ∀ s, Replies (filterDom E (automatonSystem step s)) ((h ++ [(x, y)]).map Prod.fst)
        ((h ++ [(x, y)]).map Prod.snd) ↔
          Replies (filterDom E (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd) ∧
            E (h.map Prod.fst ++ [x]) ∧
              (⟨x.1, (step (stateAfter step s (h.map Prod.fst)) x.1 x.2).2⟩ : Σ i, Y i) = y := by
      intro s
      simp only [List.map_append, List.map_cons, List.map_nil, replies_snoc,
        SystemAlgebra.filterDom, automatonSystem_snoc]
      by_cases hx : E (h.map Prod.fst ++ [x])
      · simp [hx, Part.some_inj, eq_comm]
      · simp [hx, Part.none_ne_some]
    rw [belief_snoc, restrict_congr init hrep]
    split_ifs with hd
    · have hd' : E (h.map Prod.fst ++ [x]) := hd
      -- The transition moves the states replying `y` (induction hypothesis for `h`) ...
      rw [ih, transition_ofDeterministic, restrict_fTransform, fTransform_fTransform,
        restrict_restrict]
      -- ... to the state after `h · x`.
      simp only [List.map_append, List.map_cons, List.map_nil, stateAfter_snoc]
      congr 1
      exact restrict_congr init fun s => by simp [hd']
    · -- The query is not admitted: no initial state gives the transcript.
      have hd' : ¬ E (h.map Prod.fst ++ [x]) := hd
      rw [restrict_congr init (Q := fun _ => False) fun s => by simp [hd'], restrict_false]
      exact (fTransform_zero _).symm

end ProbStep

/-- **A deterministic automaton is a probabilistic automaton** with point steps: with its initial
state sampled from `init`, a transcript has the probability of the initial states from which the
automaton gives it [1, Definition 2]. -/
theorem RandomSystem.ofProbAutomaton_ofDeterministic_apply {E : List (Σ i, X i) → Prop}
    {bound : ℕ} {hE : ∀ h, E h → h.length ≤ bound} (step : S → (i : I) → X i → S × Y i)
    (init : Distribution.ProbDist S) (h : List ((Σ i, X i) × (Σ i, Y i))) :
    RandomSystem.ofProbAutomaton (Domain.ofInputs E bound hE) (ProbStep.ofDeterministic step)
        init h =
      init.1.mass fun s =>
        Replies (filterDom E (automatonSystem step s)) (h.map Prod.fst) (h.map Prod.snd) := by
  -- The probability is the weight of the state law: the initial states giving `h`, moved.
  rw [ofProbAutomaton_apply, ProbStep.belief_ofDeterministic]
  -- Moving keeps the weight, and the weight of a restriction is the mass of its event.
  rw [weight_fTransform, weight_restrict]

end SystemAlgebra

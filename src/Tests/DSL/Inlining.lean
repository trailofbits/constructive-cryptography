import ConstructiveCryptography.DSL

/-! # Checked component equations and inlining

These checks keep arbitrary inside transitions visible, distinguish retained and fresh draws,
and exercise initialization, resumed calls, literal and symbolic loops and parallel outside
labels. `inline` expands the registered wrappers itself: attachments to automata, exact-cost
converters and own sources need no arguments, memoryless attachments take their certificate
with `using`, and an unsupported goal fails.
-/

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open CategoryTheory MonoidalCategory

noncomputable section
namespace DSLTests.Inlining

-- One input bit and one reply bit per query.
interface Bits
  get(x : Bool) → Bool

-- `get(x) ⇒ x`, with no private state.
system Echo : Bits
  on get(x : Bool) → Bool
    return x

-- Call the inside system on `x` and negate its reply.
converter Negate : Bits
  inside bit : Bits
  on get(x : Bool) → Bool
    y ← bit.get(x)
    return !y

-- The step equation of a system that samples nothing.
example (st : Unit) (x : Bool) : Echo.step st .get x = ((), x) := by
  simp only [component_equations]

-- The arbitrary inside transition remains explicit; no inside state is discarded.
example {R : Type} (step : R → Bits.Port → Bool → R × Bool) (r : R) (x : Bool) :
    Negate.body.combine step Negate.bound_spec (none, r) .get x =
      ((some (), (step r .get x).1), !(step r .get x).2) := by
  simp only [component_equations]

-- Against fresh replies `y ∼ ν get x`, the reply `!y` has law `ν get x` mapped by `not`.
example (ν : Bits.Port → Bool → ProbDist Bool) (st : Unit) (x : Bool) :
    Negate.body.memorylessReplyLaw ν (some st) .get x Negate.bound [] =
      fTransform Bool.not (ν .get x).1 := by
  simp only [component_equations]

-- The attachment is the combined automaton; the command does not choose a state relation.
example (q : ℕ) :
    Negate (budget := q) • Echo =
      TypedSystem.ofAutomaton (Bits q)
        (Negate.body.combine Echo.step Negate.bound_spec)
        (ProbDist.map (fun r => (none, r)) (ProbDist.single ())) := by
  inline
  rfl

-- An assembled DSL declaration reuses the equations of its constituent components.
system Wired ≔ Negate • Echo

example (q : ℕ) :
    Wired (budget := q) =
      TypedSystem.ofAutomaton (Bits q)
        (Negate.body.combine Echo.step Negate.bound_spec)
        (ProbDist.map (fun r => (none, r)) (ProbDist.single ())) := by
  inline
  rfl

-- Exact-cost domains use the same invocation, with the admitted histories restricted by cost.
example (q work : ℕ) :
    Negate.exact (queries := q) (budget := work) • Echo (budget := work) =
      TypedSystem.ofAutomaton
        (Interface.restrict (Bits q)
          (fun h => (h.map fun x => Negate.cost x.1 x.2).sum ≤ work)
          (cost_prefix_closed _ _))
        (Negate.body.combine Echo.step Negate.bound_spec)
        (ProbDist.map (fun r => (none, r)) (ProbDist.single ())) := by
  inline
  rfl

-- The memoryless rule, with the certificate `hR : R = mem(ν)`, keeps that same cost restriction
-- on the outside histories: `Negate.exact • mem(ν) = mem(fun i x => map not (ν i x))`.
example (q work : ℕ) (R : TypedSystem (Bits work))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R.1 = RandomSystem.memoryless (Bits work).inputDomain (RandomSystem.portLaw ν)) :
    (Negate.exact (queries := q) (budget := work) • R).1 =
      RandomSystem.memoryless
        (Interface.restrict (Bits q)
          (fun h => (h.map fun x => Negate.cost x.1 x.2).sum ≤ work)
          (cost_prefix_closed _ _)).inputDomain
        (RandomSystem.portLaw fun i x => ProbDist.map Bool.not (ν i x)) := by
  inline using hR
  all_goals rfl

-- An own source stays beside the inside system, with independent initial states. The serial and
-- right-context laws place the `g`-automaton beside the `f`-automaton, and the parallel-automaton
-- law makes them one automaton with step `parallelStep f g`, started from `μ × ν`.
example {A B C : Interface} {S R T : Type} (s : S)
    (P : Program S A.I (B ⊗ C).I A.X A.Y (B ⊗ C).X (B ⊗ C).Y) {b : ℕ}
    (hb : P.Bounded b)
    (hBC : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → (B ⊗ C).domain xs)
    (f : R → (i : B.I) → B.X i → R × B.Y i)
    (g : T → (j : C.I) → C.X j → T × C.Y j) (μ : ProbDist R) (ν : ProbDist T) :
    (TypedConverter.ofProgram s P hb hBC ≫
        TypedConverter.rightContext B (TypedSystem.ofAutomaton C g ν)) •
        TypedSystem.ofAutomaton B f μ =
      TypedSystem.ofAutomaton A (P.combine (parallelStep f g) hb)
        (ProbDist.map (fun rt => (s, rt)) (prodProbDist μ ν)) := by
  inline
  rfl

-- One initial draw `bit ← 𝒰[Bool]` is retained by every later invocation: `get(_) ⇒ bit`.
system Retained : Bits
  initialize
    bit ←$ 𝒰[Bool]
  on get(_x : Bool) → Bool
    return bit

-- The first call draws `bit` from its source, so its reply has the source's law.
example (ν : Unit → Unit → ProbDist Bool) (x : Bool) :
    Retained.body.memorylessReplyLaw ν none .get x Retained.bound [] =
      fTransform id (ν () ()).1 := by
  exact Retained.memorylessReplyLaw_get_initial ν x

-- A resumed call replies with the stored `b`, not a fresh draw.
example (ν : Unit → Unit → ProbDist Bool) (b x : Bool) :
    Retained.body.memorylessReplyLaw ν (some b) .get x Retained.bound [] =
      Finsupp.single b 1 := by
  simp only [component_equations]

-- The two literal iterations use the first reply as the second query.
converter Twice : Bits
  inside bit : Bits
  on get(x : Bool) → Bool
    result ← x
    for _i ∈ [(), ()]
      result ← bit.get(result)
    return result

-- The displayed literal list gives the constant bound `2 · 1`.
example : Twice.bound = 2 := rfl

-- `get(x) ⇒ y₂`, where `y₁ = bit.get(x)` and `y₂ = bit.get(y₁)`.
example {R : Type} (step : R → Bits.Port → Bool → R × Bool) (r : R) (x : Bool) :
    Twice.body.combine step Twice.bound_spec (none, r) .get x =
      ((some (), (step (step r .get x).1 .get (step r .get x).2).1),
        (step (step r .get x).1 .get (step r .get x).2).2) := by
  simp only [component_equations]

-- Qualified names retain their outside namespaces.
system Multi
  outside left : Bits
  outside right : Bits
  on left.get(x : Bool) → Bool
    return x
  on right.get(x : Bool) → Bool
    return !x

example (st : Unit) (x : Bool) : Multi.step st (.inr .get) x = ((), !x) := by
  exact Multi.right.step_get st x

-- A symbolic loop remains a fold in its body equation; the compiler does not enumerate inputs.
converter Counted : Bits
  inside bit : Bits
  on get(x : Bool) → Bool
    result ← x
    for _i ∈ (if x then [(), ()] else [()])
      result ← bit.get(result)
    return result

example (x : Bool) (h : List (Sigma Bits.Input × Sigma Bits.Output)) :
    Counted.body none .get x h =
      forEach (if x then [(), ()] else [()])
        (fun (_i : Unit) next (bindings : Bool × Bool) =>
          callProg Bits.Port.get bindings.2 fun value => next (bindings.1, value))
        (fun (bindings : Bool × Bool) => returnProg (some (), bindings.2)) (x, x) h := by
  exact Counted.body_get_initial x h

-- Unrelated section variables must not become uninferrable arguments of generated equations.
-- The unused universe `u` is also dropped, so `simp` can still apply both equations below.
section
universe u
variable (Unused : Type u) [Fintype Unused]

system Local : Bits
  on get(x : Bool) → Bool
    return x

example (st : Unit) (x : Bool) : Local.step st .get x = ((), x) := by
  simp only [component_equations]

-- `get(_)` draws a fresh uniform `bit ← 𝒰[Bool]` on every call and returns it.
system LocalSample : Bits
  on get(_x : Bool) → Bool
    bit ←$ 𝒰[Bool]
    return bit

-- Against fresh source draws, the reply has the source's law `ν () ()`.
example (ν : Unit → Unit → ProbDist Bool) (x : Bool) :
    LocalSample.body.memorylessReplyLaw ν none .get x LocalSample.bound [] =
      fTransform id (ν () ()).1 := by
  simp only [component_equations]
  rfl
end

-- Unsupported shapes fail rather than searching for another proof route.
example (n : ℕ) : n = n := by
  fail_if_success inline
  rfl

#print axioms Negate.combine_get_initial
#print axioms Retained.memorylessReplyLaw_get_resumed
#print axioms Twice.combine_get_initial

end DSLTests.Inlining

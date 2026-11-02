module

public import ConstructiveCryptography.DSL

/-! # Checked component equations and inlining

These checks keep arbitrary inside transitions visible, distinguish retained and fresh draws,
and exercise initialization, resumed calls, literal and symbolic loops and parallel outside
labels. `inline` expands the registered wrappers itself: attachments to automata, exact-cost
converters and own sources need no arguments, memoryless attachments take their certificate
with `using`, and an unsupported goal fails. Typed and cumulative targets retain the selected
domains; supplied certificates may use either carrier.
-/

@[expose] public section

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

-- An assembled DSL declaration reuses the equations of its constituent components.
system Wired ≔ Negate • Echo

example (q : ℕ) :
    Wired (budget := q) =
      TypedSystem.ofAutomaton (Bits q)
        (Negate.body.combine Echo.step Negate.bound_spec)
        (ProbDist.map (fun r => (none, r)) (ProbDist.single ())) := by
  inline

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

-- The cumulative certificate `hR : R.1 = memoryless …` keeps the outside cost restriction:
-- `Negate.exact • mem(ν) = mem(fun i x => map not (ν i x))`.
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

/-! ### Typed memoryless attachment -/

-- An ordinary program preserves the explicitly supplied fresh-law contract.
example (q : ℕ) (R : TypedSystem (Bits (Negate.bound * q)))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R = TypedSystem.ofMemoryless (Bits (Negate.bound * q)) ν) :
    Negate (budget := q) • R =
      TypedSystem.ofMemoryless (Bits q) (fun i x => ProbDist.map Bool.not (ν i x)) := by
  -- The tactic neither invents the certificate nor accepts a nonexistent own source.
  fail_if_success inline
  fail_if_success inline using hR, hR
  inline using hR
  all_goals rfl

-- A raw certificate can also prove a typed goal for the per-port constructor.
example (q : Bits.Port → ℕ) (R : TypedSystem (Bits.perPort q))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R.1 = RandomSystem.memoryless (Bits.perPort q).inputDomain (RandomSystem.portLaw ν)) :
    Negate.perPort (budget := q) • R =
      TypedSystem.ofMemoryless (Bits.perPort q) (fun i x => ProbDist.map Bool.not (ν i x)) := by
  inline using hR
  all_goals rfl

-- The typed exact-cost contract retains the restriction on accumulated inside calls.
example (q work : ℕ) (R : TypedSystem (Bits work))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R = TypedSystem.ofMemoryless (Bits work) ν) :
    Negate.exact (queries := q) (budget := work) • R =
      TypedSystem.ofMemoryless
        (Interface.restrict (Bits q)
          (fun h => (h.map fun x => Negate.cost x.1 x.2).sum ≤ work)
          (cost_prefix_closed _ _))
        (fun i x => ProbDist.map Bool.not (ν i x)) := by
  inline using hR
  all_goals rfl

-- Typed certificates also retain the existing raw-goal route.
example (q : Bits.Port → ℕ) (R : TypedSystem (Bits.perPort q))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R = TypedSystem.ofMemoryless (Bits.perPort q) ν) :
    (Negate.perPort (budget := q) • R).1 =
      RandomSystem.memoryless (Bits.perPort q).inputDomain
        (RandomSystem.portLaw fun i x => ProbDist.map Bool.not (ν i x)) := by
  inline using hR
  all_goals rfl

-- An equality without an attachment is outside this tactic's contract.
example {A : Interface} (R : TypedSystem A) (ν : ∀ i, A.X i → ProbDist (A.Y i))
    (hR : R = TypedSystem.ofMemoryless A ν) : R = TypedSystem.ofMemoryless A ν := by
  fail_if_success inline using hR
  exact hR

-- `get(x)`: query the inside bit, draw a fresh independent mask, and return their xor.
converter Masked : Bits
  inside bit : Bits
  on get(x : Bool) → Bool
    y ← bit.get(x)
    mask ←$ 𝒰[Bool]
    return mask != y

-- Both supplied contracts are used: inside replies and the converter's fresh masks.
example (q : Bits.Port → ℕ) (R : TypedSystem (Bits.perPort q))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R = TypedSystem.ofMemoryless (Bits.perPort q) ν) :
    Masked.perPort (budget := q) • R =
      TypedSystem.ofMemoryless (Bits.perPort q)
        (fun i x => ProbDist.bind (ν i x) (fun y => ProbDist.map (fun b => b != y) 𝒰[Bool])) := by
  fail_if_success inline using hR
  inline using hR, (TypedSystem.source_eq_ofMemoryless _ _)
  all_goals rfl

-- Typed source certificates with inferred law/budget also serve cumulative targets.
example (q : Bits.Port → ℕ) (R : TypedSystem (Bits.perPort q))
    (ν : Bits.Port → Bool → ProbDist Bool)
    (hR : R = TypedSystem.ofMemoryless (Bits.perPort q) ν) :
    (Masked.perPort (budget := q) • R).1 =
      RandomSystem.memoryless (Bits.perPort q).inputDomain
        (RandomSystem.portLaw fun i x =>
          ProbDist.bind (ν i x) (fun y => ProbDist.map (fun b => b != y) 𝒰[Bool])) := by
  inline using hR, (TypedSystem.source_eq_ofMemoryless _ _)
  all_goals rfl

#print axioms TypedSystem.eq_memoryless_of_eq_ofMemoryless
#print axioms TypedSystem.parallel_eq_ofMemoryless
#print axioms TypedConverter.ofProgram_smul_ofMemoryless
#print axioms TypedConverter.ofPreservingProgram_smul_ofMemoryless
#print axioms TypedConverter.ofCostedProgram_smul_ofMemoryless

-- Direct parallel inputs normalize before applying the program's automaton contract.
example {A B C : Interface} {S R T : Type} (s : S)
    (P : Program S A.I (B ⊗ C).I A.X A.Y (B ⊗ C).X (B ⊗ C).Y) {b : ℕ}
    (hb : P.Bounded b)
    (hBC : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → (B ⊗ C).domain xs)
    (f : R → (i : B.I) → B.X i → R × B.Y i)
    (g : T → (j : C.I) → C.X j → T × C.Y j) (μ : ProbDist R) (ν : ProbDist T) :
    TypedConverter.ofProgram s P hb hBC •
        TypedSystem.parallel (TypedSystem.ofAutomaton B f μ) (TypedSystem.ofAutomaton C g ν) =
      TypedSystem.ofAutomaton A (P.combine (parallelStep f g) hb)
        (ProbDist.map (fun rt => (s, rt)) (prodProbDist μ ν)) := by
  inline

-- Independent initialized states assemble under the same attached converter `α`.
example {A B C : Interface}
    -- `Ω`, `Ξ` carry independent draws; `init`, `init'` turn them into retained states `S`, `T`.
    {Ω Ξ S T : Type} (init : Ω → S) (init' : Ξ → T) (P : ProbDist Ω) (Q : ProbDist Ξ)
    -- `f`, `g` update the state and answer queries at `A`, `B`; `α` is their common context.
    (f : S → (i : A.I) → A.X i → S × A.Y i)
    (g : T → (j : B.I) → B.X j → T × B.Y j) (α : TypedConverter C (A ⊗ B)) :
    α • TypedSystem.parallel
        (TypedSystem.ofAutomaton A f (ProbDist.map init P))
        (TypedSystem.ofAutomaton B g (ProbDist.map init' Q)) =
      α • TypedSystem.ofAutomaton (A ⊗ B) (parallelStep f g)
        (ProbDist.map (Prod.map init init') (prodProbDist P Q)) := by
  -- Parallel states start independently; initializing each draw commutes with their product.
  rw [TypedSystem.parallel_ofAutomaton, prodProbDist_map]
  rfl

-- Explicit typed `comp` places the independent `g`-automaton beside the inside `f`-automaton.
-- The parallel law gives step `parallelStep f g` and initial law `μ × ν`.
example {A B C : Interface} {S R T : Type} (s : S)
    (P : Program S A.I (B ⊗ C).I A.X A.Y (B ⊗ C).X (B ⊗ C).Y) {b : ℕ}
    (hb : P.Bounded b)
    (hBC : ∀ xs, xs ≠ [] → xs.length ≤ b * A.bound → (B ⊗ C).domain xs)
    (f : R → (i : B.I) → B.X i → R × B.Y i)
    (g : T → (j : C.I) → C.X j → T × C.Y j) (μ : ProbDist R) (ν : ProbDist T) :
    TypedConverter.comp (TypedConverter.ofProgram s P hb hBC)
        (TypedConverter.rightContext B (TypedSystem.ofAutomaton C g ν)) •
        TypedSystem.ofAutomaton B f μ =
      TypedSystem.ofAutomaton A (P.combine (parallelStep f g) hb)
        (ProbDist.map (fun rt => (s, rt)) (prodProbDist μ ν)) := by
  inline

-- An arbitrary inner converter `α` is not the displayed own-source context required by `inline`.
example (q : Bits.Port → ℕ) (α : TypedConverter (Bits.perPort q) (Bits.perPort q))
    (R : TypedSystem (Bits.perPort q))
    (h : (Negate.perPort (budget := q) ≫ α) • Echo.perPort (budget := q) = R) :
    (Negate.perPort (budget := q) ≫ α) • Echo.perPort (budget := q) = R := by
  fail_if_success inline
  exact h

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
-- The closure step keeps only the variables and universes the equation uses, so `Unused` and
-- `u` are dropped and `simp` can still apply both equations below.
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

-- `Guesses Value`: one port `check(guess : Value) → Bool`, over a finite guess space.
interface Guesses(Value : Type) [Fintype Value]
  check(guess : Value) → Bool

section
variable {Value : Type} [Fintype Value]

-- Stateless; rejects every guess: `check(guess) ↦ false`.
system Reject : Guesses Value
  on check(_guess : Value) → Bool
    return false

-- The proof mentions `Value` via the `guess` binder, but `simp` may erase the `Fintype` instance
-- that `Reject.step` needs; the equation keeps it in type and proof, so `simp` applies it.
example (st : Unit) (guess : Value) : Reject.step st .check guess = ((), false) := by
  simp only [component_equations]
end

-- Unsupported shapes fail rather than searching for another proof route.
example (n : ℕ) : n = n := by
  fail_if_success inline
  rfl

/-- error: Cannot generate a component equation with unresolved metavariables. -/
#guard_msgs in
component_equation unfinished : (_ : Nat) using Nat.add_zero

#print axioms Negate.combine_get_initial
#print axioms Retained.memorylessReplyLaw_get_resumed
#print axioms Twice.combine_get_initial

end DSLTests.Inlining

import ConstructiveCryptography.DSL
import ConstructiveCryptography.Functional
import ConstructiveCryptography.Memoryless
import Mathlib.Data.Fintype.Perm

/-!
# Ideal systems

An `(X, Y)`-random function is a random variable over the functions `X → Y`, as the system that
answers each input with the function's value; an `X`-random permutation is one over the
bijections of `X`. The uniform ones are the uniform random function (URF) and the uniform random
permutation (URP) (CR18, Definition 3.15 and Example 3.5, printed p. 64). The strong URP also
answers inverse queries, and a tweakable URP is an independent URP for each tweak. Each system
samples once and keeps its sample for the whole interaction. A memoryless source samples afresh
at each query (CR18, Definition 3.1, printed p. 55: "A source can be memoryless or have memory").

## Main definitions

* `Evaluation X Y`, `Bidirectional X`, `TweakedEvaluation T X`, `TweakedBidirectional T X`: the
  interfaces of a function, of a permutation with its inverse, and of their tweaked versions
* `URF A`, `URP A`: an independent URF, and an independent URP, at each label of `A`
* `StrongURP X`, `TweakableURP T X`, `TweakableStrongURP T X`
* `MemorylessSource Y ν`: the memoryless source of `ν`, answering each query with a fresh sample

## Main results

* `MemorylessSource.memoryless_eq`: the memoryless source of `ν` is the memoryless system of `ν`
-/

namespace Commons

open SystemAlgebra Probability

interface Evaluation(X Y : Type) [Fintype X] [Fintype Y]
  eval(x : X) → Y

interface Bidirectional(X : Type) [Fintype X]
  forward(x : X) → X
  inverse(y : X) → X

interface TweakedEvaluation(T X : Type) [Fintype T] [Fintype X]
  eval(tweak : T, x : X) → X

interface TweakedBidirectional(T X : Type) [Fintype T] [Fintype X]
  forward(tweak : T, x : X) → X
  inverse(tweak : T, y : X) → X

noncomputable section

open Classical

/-- **The uniform random function** on `A`: at each label, a uniformly random function from its
inputs to its outputs. On `Evaluation X Y q` it is the `(X, Y)`-URF. -/
def URF (A : Interface) [∀ i, Nonempty (A.Y i)] : Interface.Resource A :=
  Interface.Resource.sample (Distribution.uniform (∀ i, A.X i → A.Y i)) Interface.Resource.ofFunction

/-- **The uniform random permutation** on `A`: at each label, a uniformly random bijection from its
inputs to its outputs. On `Evaluation X X q` it is the `X`-URP. -/
def URP (A : Interface) [∀ i, Nonempty (A.X i ≃ A.Y i)] : Interface.Resource A :=
  Interface.Resource.sample (Distribution.uniform (∀ i, A.X i ≃ A.Y i))
    fun π => Interface.Resource.ofFunction fun i x => π i x

variable (T X : Type) [Fintype T] [Fintype X] {q : ℕ}

/-- **The strong uniform random permutation**: a uniformly random permutation of `X`, answering
forward queries with it and inverse queries with its inverse. -/
def StrongURP : Interface.Resource (Bidirectional X q) :=
  Interface.Resource.sample (Distribution.uniform (Equiv.Perm X)) fun π =>
    Interface.Resource.ofFunction fun
      | .forward => fun x => π x
      | .inverse => fun y => π.symm y

/-- **The tweakable uniform random permutation**: an independent uniformly random permutation of
`X` for each tweak. -/
def TweakableURP : Interface.Resource (TweakedEvaluation T X q) :=
  Interface.Resource.sample (Distribution.uniform (T → Equiv.Perm X)) fun π =>
    Interface.Resource.ofFunction fun _ tx => π tx.1 tx.2

/-- **The strong tweakable uniform random permutation**: the tweakable URP, answering inverse
queries with the inverse permutation of their tweak. -/
def TweakableStrongURP : Interface.Resource (TweakedBidirectional T X q) :=
  Interface.Resource.sample (Distribution.uniform (T → Equiv.Perm X)) fun π =>
    Interface.Resource.ofFunction fun
      | .forward => fun tx => π tx.1 tx.2
      | .inverse => fun ty => (π ty.1).symm ty.2

end

/-! ### Memoryless sources -/

open SystemAlgebra.DSL

-- **The memoryless source** of `ν` (CR18, Definition 3.1, printed p. 55): on `eval(())`, a fresh
-- sample `y ← ν`, returned.
system MemorylessSource(Y : Type) [Fintype Y] (ν : Distribution.ProbDist Y) : Evaluation Unit Y
  on eval(_input : Unit) → Y
    y ←$ ν
    return y

open Distribution in
/-- **The memoryless source of `ν` is the memoryless system of `ν`**: each `eval(())` is answered
by a fresh sample of `ν`, independent of the history. -/
theorem MemorylessSource.memoryless_eq {Y : Type} [Fintype Y] (ν : ProbDist Y)
    (q : Evaluation.Port → ℕ) :
    (MemorylessSource.perPort Y ν (budget := q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => ν) := by
  -- The source is its program attached to its source of samples of `ν`:
  --
  --   eval(()) ──► program ── randomness(()) ──► source, fresh samples y ← ν
  --            ◄── eval ⇒ y
  --
  -- The source of samples is memoryless, so by the composition law the system is memoryless with
  -- the reply law of one invocation of the program.
  refine Interface.Converter.ofProgram_smul_memoryless none _ _ _
    (Interface.source_eq_memoryless _ _) ?_
  -- One invocation: draw `y ← ν` and reply `y`. Its law is `ν`, in both initialization states
  -- (`none` before the first call, `some ()` after).
  rintro (_ | ⟨⟩) ⟨⟩ ⟨⟩
  · simp [Program.replyLaw, MemorylessSource.body, MemorylessSource.law1, callProg, returnProg,
      bindK_single_one]
  · simp [Program.replyLaw, MemorylessSource.body, MemorylessSource.law1, callProg, returnProg,
      bindK_single_one]

end Commons

import ConstructiveCryptography.DSL
import ConstructiveCryptography.Functional
import Mathlib.Data.Fintype.Perm

/-!
# Ideal systems

An `(X, Y)`-random function is a random variable over the functions `X → Y`, as the system that
answers each input with the function's value; an `X`-random permutation is one over the
bijections of `X`. The uniform ones are the uniform random function (URF) and the uniform random
permutation (URP) (CR18, Definition 3.15 and Example 3.5, printed p. 64). The strong URP also
answers inverse queries, and a tweakable URP is an independent URP for each tweak. Each system
samples once and keeps its sample for the whole interaction.

## Main definitions

* `Evaluation X Y`, `Bidirectional X`, `TweakedEvaluation T X`, `TweakedBidirectional T X`: the
  interfaces of a function, of a permutation with its inverse, and of their tweaked versions
* `URF A`, `URP A`: an independent URF, and an independent URP, at each label of `A`
* `StrongURP X`, `TweakableURP T X`, `TweakableStrongURP T X`
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

end Commons

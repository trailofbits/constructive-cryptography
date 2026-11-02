module

public import ConstructiveCryptography.DSL
public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Memoryless
public import Mathlib.Data.Fintype.Perm

/-!
# Ideal systems

An `(X, Y)`-random function is a random variable over the functions `X → Y`, as the system that
answers each input with the function's value; an `X`-random permutation is one over the
bijections of `X`. The uniform ones are the uniform random function (URF) and the uniform random
permutation (URP) [1, Definition 3.15, Example 3.5, p. 64]. The strong URP also
answers inverse queries, and a tweakable URP is an independent URP for each tweak. Each system
samples once and keeps its sample for the whole interaction. A memoryless source samples afresh
at each query [1, Definition 3.1, p. 55]: "A source can be memoryless or have memory".

## Main definitions

* `Evaluation X Y`, `Bidirectional X`, `TweakedEvaluation T X`, `TweakedBidirectional T X`: the
  interfaces of a function, of a permutation with its inverse, and of their tweaked versions
* `URF A`, `URP A`: an independent URF, and an independent URP, at each label of `A`
* `StrongURP X`, `TweakableURP T X`, `TweakableStrongURP T X`
* `MemorylessSource Y ν`: the memoryless source of `ν`, answering each query with a fresh sample

## Main results

* `MemorylessSource.memoryless_eq`, `MemorylessSource.eq_ofMemoryless`: the source of `ν`
  equals the memoryless system of `ν`, at the cumulative and typed levels

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Commons

open SystemAlgebra Probability

-- Query `eval(x)` with `x : X` and receive a reply in `Y`.
interface Evaluation(X Y : Type) [Fintype X] [Fintype Y]
  eval(x : X) → Y

-- Query a function or its inverse on `X`.
interface Bidirectional(X : Type) [Fintype X]
  forward(x : X) → X
  inverse(y : X) → X

-- The tweak `t : T` selects a function on `X`.
interface TweakedEvaluation(T X : Type) [Fintype T] [Fintype X]
  eval(tweak : T, x : X) → X

-- The tweak selects one permutation on `X` for both forward and inverse queries.
interface TweakedBidirectional(T X : Type) [Fintype T] [Fintype X]
  forward(tweak : T, x : X) → X
  inverse(tweak : T, y : X) → X

noncomputable section


open Classical in
/-- Sample `f ∼ 𝒰[∀ i, A.X i → A.Y i]` once; answer each admitted `i(x)` with `f i x`.
The functions at distinct ports are independent. On `Evaluation X Y q` this is the `(X, Y)`-URF. -/
def URF
    -- `A` selects ports, alphabets and domain; inhabited replies make the function law nonempty.
    (A : Interface) [∀ i, Nonempty (A.Y i)] : TypedSystem A :=
  TypedSystem.sample (Distribution.uniform (∀ i, A.X i → A.Y i)) TypedSystem.ofFunction

open Classical in
/-- Sample `π ∼ 𝒰[∀ i, A.X i ≃ A.Y i]` once; answer each admitted `i(x)` with `π i x`.
The bijections at distinct ports are independent. On `Evaluation X X q` this is the `X`-URP. -/
def URP
    -- `A` selects ports, alphabets and domain; each port must admit an input/output bijection.
    (A : Interface) [∀ i, Nonempty (A.X i ≃ A.Y i)] : TypedSystem A :=
  TypedSystem.sample (Distribution.uniform (∀ i, A.X i ≃ A.Y i))
    fun π => TypedSystem.ofFunction fun i x => π i x

-- `T` carries tweaks, `X` carries permutation inputs and outputs; `q` bounds total queries.
variable (T X : Type) [Fintype T] [Fintype X] {q : ℕ}

open Classical in
/-- Retain `π ∼ 𝒰[Equiv.Perm X]`; answer `forward(x)` with `π x` and `inverse(y)` with
`π⁻¹ y`, for at most `q` queries across both ports. -/
def StrongURP : TypedSystem (Bidirectional X q) :=
  TypedSystem.sample (Distribution.uniform (Equiv.Perm X)) fun π =>
    TypedSystem.ofFunction fun
      | .forward => fun x => π x
      | .inverse => fun y => π.symm y

open Classical in
/-- Retain independent `π t ∼ 𝒰[Equiv.Perm X]` for each tweak `t : T`.
Each `eval(t, x)` returns `π t x`, for at most `q` queries across all tweaks. -/
def TweakableURP : TypedSystem (TweakedEvaluation T X q) :=
  TypedSystem.sample (Distribution.uniform (T → Equiv.Perm X)) fun π =>
    TypedSystem.ofFunction fun _ tx => π tx.1 tx.2

open Classical in
/-- Retain independent `π t ∼ 𝒰[Equiv.Perm X]`; answer `forward(t, x)` with `π t x`
and `inverse(t, y)` with `(π t)⁻¹ y`, for at most `q` queries across both ports and all tweaks. -/
def TweakableStrongURP : TypedSystem (TweakedBidirectional T X q) :=
  TypedSystem.sample (Distribution.uniform (T → Equiv.Perm X)) fun π =>
    TypedSystem.ofFunction fun
      | .forward => fun tx => π tx.1 tx.2
      | .inverse => fun ty => (π ty.1).symm ty.2

end

/-! ### Memoryless sources -/

open SystemAlgebra.DSL

-- On `Evaluation Unit Y`, each admitted `eval(())` returns a fresh `y ∼ ν`
-- [1, Definition 3.1, p. 55]. The selected total or per-port budget bounds the number of triggers.
system MemorylessSource(Y : Type) [Fintype Y] (ν : Distribution.ProbDist Y) : Evaluation Unit Y
  on eval(_input : Unit) → Y
    y ←$ ν
    return y

open Distribution in
/-- Each admitted `eval(())` has reply law `ν`, so the cumulative behavior is `memoryless ν`. -/
lemma MemorylessSource.memoryless_eq
    -- `Y` carries replies; `ν` is the fresh reply law.
    {Y : Type} [Fintype Y] (ν : ProbDist Y)
    -- `q` fixes the query allowance at the evaluation port.
    (q : Evaluation.Port → ℕ) :
    (MemorylessSource.perPort Y ν (budget := q)).1 =
      RandomSystem.memoryless _ (RandomSystem.portLaw fun _ _ => ν) := by
  -- Each invocation forwards one fresh sample:
  --   eval(()) ──► program ── () ──► source(ν)
  --        y ◄────────────── y ◄───
  -- The program contract gives reply law `id_* ν` in both initial and resumed states.
  inline using (TypedSystem.source_eq_memoryless _ _)
  -- Returning the sampled value preserves its law: `id_* ν = ν`.
  all_goals exact Distribution.fTransform_id _

open Distribution in
/-- The source of fresh `ν` replies equals `ofMemoryless` on the same per-port domain. -/
lemma MemorylessSource.eq_ofMemoryless
    -- `Y` carries replies; `ν` is sampled afresh at each admitted trigger.
    {Y : Type} [Fintype Y] (ν : ProbDist Y)
    -- `q` fixes the query allowance at the source's evaluation port.
    (q : Evaluation.Port → ℕ) :
    MemorylessSource.perPort Y ν (budget := q) =
      TypedSystem.ofMemoryless (Evaluation.perPort Unit Y q) (fun _ _ => ν) :=
  Subtype.ext (MemorylessSource.memoryless_eq ν q)

end Commons

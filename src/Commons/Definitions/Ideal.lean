module

public import ConstructiveCryptography.DSL
public import Commons.Definitions.RandomFunction.Laws
public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.Memoryless
public import Mathlib.Data.Fintype.Perm

/-!
# Ideal systems

An `(X, Y)`-random function is a random variable over the functions `X → Y`, as the system that
answers each input with the function's value; an `X`-random permutation is one over the
bijections of `X`. The uniform ones are the uniform random function (URF) and the uniform random
permutation (URP) [1, Definition 3.15, Example 3.5, p. 64]. The strong URP also
answers inverse queries, and a tweakable URP is an independent URP for each tweak. The sampled
presentations retain their draws for the whole interaction. A memoryless source samples afresh
at each query [1, Definition 3.1, p. 55]: "A source can be memoryless or have memory".

`URF.lazy` specializes the generic lazy random function to uniform coordinate laws.
`Commons.randomFunction.lazy_eq`, in `Commons.Definitions.RandomFunction.Laws`, proves
its retained-table correspondence; `URF.eq_randomFunction` identifies the uniform table.
Together they give `URF.lazy_eq` on every admitted history, including repeated queries.

## Main definitions

* `Evaluation X Y`, `Bidirectional X`, `TweakedEvaluation T X`, `TweakedBidirectional T X`: the
  interfaces of a function, of a permutation with its inverse, and of their tweaked versions
* `URF A`, `URP A`: an independent URF, and an independent URP, at each label of `A`
* `URF.lazy A`: the same random function, recording replies and sampling only on a miss
* `URP.lazy A` in `Commons.Definitions.LazyPermutation`: uniform unused replies at fresh inputs
* `StrongURP X`, `TweakableURP T X`, `TweakableStrongURP T X`
* `MemorylessSource Y ν`: the memoryless source of `ν`, answering each query with a fresh sample

## Main results

* `URF.eq_randomFunction`: uniform coordinate laws give the existing retained uniform table
* `URF.eq_sample`, `URF.smul_eq_sample`: `URF A` and its converter attachments draw one retained
  uniform function table for any `Fintype` enumeration of `∀ i, A.X i → A.Y i`
* `URF.single_mass`: on a single-port admitted transcript, URF mass is the uniform-table
  probability of supplying every recorded reply
* `URF.lazy_eq`: the lazy table equals `URF` on every history admitted by `A.domain`
* `MemorylessSource.memoryless_eq`, `MemorylessSource.eq_ofMemoryless`: the source of `ν`
  equals the memoryless system of `ν`, at the cumulative and typed levels

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
2. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
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

namespace URF

open Distribution

/-- `URF A` draws one uniform function table `f` once and answers each admitted `i(x)` with
`f i x`, for any `Fintype` enumeration `inst` of `∀ i, A.X i → A.Y i`. -/
lemma eq_sample
    -- `A` selects ports, finite alphabets and domain; inhabited replies make the table space
    -- nonempty.
    (A : Interface) [∀ i, Nonempty (A.Y i)]
    -- `inst` is any finite enumeration of the function tables on `A`.
    [inst : Fintype (∀ i, A.X i → A.Y i)] :
    Commons.URF A =
      TypedSystem.sample (Distribution.uniform (∀ i, A.X i → A.Y i)) TypedSystem.ofFunction := by
  -- Unfold `Commons.URF` and identify its classical `Fintype` witness with `inst`.
  unfold Commons.URF
  congr 1
  exact uniform_congr_fintype _ inst

/-- Uniform coordinate laws give `URF A`, retaining one table throughout the interaction. -/
lemma eq_randomFunction
    -- `A` supplies ports and finite alphabets; each reply alphabet admits a uniform law.
    (A : Interface) [∀ i, Nonempty (A.Y i)] :
    Commons.URF A = randomFunction A (fun i _ => 𝒰[A.Y i]) := by
  classical
  rw [eq_sample, randomFunction]
  congr 1
  simp only [ProbDist.piDep_val, ProbDist.uniform, piDep_uniform]

/-- Attaching a converter `α` to `URF A` draws one uniform function table `f` once and runs `α`
against `ofFunction f`, for any `Fintype` enumeration `inst` of `∀ i, A.X i → A.Y i`. -/
lemma smul_eq_sample
    -- `A` is the inside URF interface with nonempty reply alphabets; `B` is the outside interface.
    {A B : Interface} [∀ i, Nonempty (A.Y i)]
    -- `α` translates outside queries on `B` into admitted queries on `A`.
    (α : TypedConverter B A)
    -- `inst` is any finite enumeration of the function tables on `A`.
    [inst : Fintype (∀ i, A.X i → A.Y i)] :
    α • Commons.URF A =
      TypedSystem.sample (Distribution.uniform (∀ i, A.X i → A.Y i))
        (fun f => α • TypedSystem.ofFunction f) := by
  -- Expose the retained uniform table at `inst`, then pull sampling across `α`.
  rw [eq_sample A, TypedConverter.smul_sample]

section SinglePort

-- `I` is the sole port; `X`, `Y` are its finite query/reply alphabets.
variable {I X Y : Type} [Unique I] [Fintype X] [Fintype Y] [Nonempty Y]
    -- `D` is the selected nonempty, prefix-closed query domain, bounded by `q`.
    (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    (q : ℕ) (hq : ∀ xs, D xs → xs.length ≤ q)

local notation "A" => (Interface.mk I (fun _ => X) (fun _ => Y) D hD q hq)

open Classical in
/-- On an admitted single-port transcript, the URF mass is the probability that a uniform
function supplies every recorded reply. Repeated inputs share that function value. -/
lemma single_mass
    -- `h` records tagged query/reply pairs; `admitted` permits the initial empty transcript.
    (h : List ((Σ _ : I, X) × Σ _ : I, Y))
    (admitted : h = [] ∨ D (h.map Prod.fst)) :
    (Commons.URF A).1 h = (uniform (X → Y)).mass (fun f => ∀ z ∈ h, f z.1.2 = z.2.2) := by
  -- Expose the sampled family, then remove its unique port by a uniform-preserving equivalence.
  rw [Commons.URF, TypedSystem.sample_ofFunction_mass, behaviorMass, mass_fTransform]
  simp only [DDS.replies_ofFunction_iff, List.map_eq_nil_iff]
  change (uniform (I → X → Y)).mass (fun f =>
    (h = [] ∨ D (h.map Prod.fst)) ∧
      h.map Prod.snd = (h.map Prod.fst).map (fun x => (⟨x.1, f x.1 x.2⟩ : Σ _ : I, Y))) = _
  simp only [admitted, true_and]
  rw [← fTransform_equiv_uniform (Equiv.funUnique I (X → Y)).symm, mass_fTransform]
  -- At the sole port, equality of tagged replies is equality of their values.
  apply mass_congr
  intro f
  change h.map Prod.snd = (h.map Prod.fst).map (fun x => (⟨x.1, f x.2⟩ : Σ _ : I, Y)) ↔ _
  rw [List.map_map, List.map_eq_map_iff]
  constructor
  · intro hr z hz
    exact (congrArg Sigma.snd (hr z hz)).symm
  · intro hr z hz
    exact Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (hr z hz).symm)

end SinglePort

-- `A` fixes ports, finite alphabets and admitted histories; every reply type is nonempty.
variable (A : Interface) [∀ i, Nonempty (A.Y i)]

/-- A stored reply has point law; an unrecorded input is uniform at its port. -/
def replyLaw
    -- `table i` retains input/reply pairs; `i(x)` is the current query.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) :
    ProbDist (A.Y i) :=
  randomFunction.replyLaw A (fun i _ => 𝒰[A.Y i]) table i x

/-- Draw from the uniform reply law and record the reply exactly on a lookup miss. -/
def tableLaw : ProbStep (∀ i, List (A.X i × A.Y i)) A.I A.X A.Y :=
  randomFunction.tableLaw A (fun i _ => 𝒰[A.Y i])

/-- Empty initial records, with uniform independent draws at each fresh input. -/
def lazy : TypedSystem A := randomFunction.lazy A (fun i _ => 𝒰[A.Y i])

/-- Lazy sampling realizes the retained URF on every admitted history.
[2, §4.4.2, p. 133]: "we can implement the random function". -/
theorem lazy_eq : lazy A = Commons.URF A :=
  (randomFunction.lazy_eq A (fun i _ => 𝒰[A.Y i])).trans (eq_randomFunction A).symm

end URF

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

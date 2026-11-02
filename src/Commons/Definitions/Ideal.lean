module

public import ConstructiveCryptography.DSL
public import RandomSystems.Typed.Functional
public import RandomSystems.Typed.KeyedAutomaton
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

`URF.lazy` presents the same function by retaining per-port records and drawing only on a miss
[2, §4.4.2, pp. 133–134]. `URF.completionLaw_eq_bind` reveals one fresh coordinate of a
uniform completion; `URF.tableLaw_simulates` uses this identity for misses and the pinned
coordinate for hits. The kernel simulation law in `RandomSystems.Typed.ProbAutomaton` then
identifies all cumulative probabilities. The retained-key law in
`RandomSystems.Typed.KeyedAutomaton` and a function reindexing give `URF.lazy_eq`.

## Main definitions

* `Evaluation X Y`, `Bidirectional X`, `TweakedEvaluation T X`, `TweakedBidirectional T X`: the
  interfaces of a function, of a permutation with its inverse, and of their tweaked versions
* `URF A`, `URP A`: an independent URF, and an independent URP, at each label of `A`
* `URF.lazy A`: the same random function, recording replies and sampling only on a miss
* `StrongURP X`, `TweakableURP T X`, `TweakableStrongURP T X`
* `MemorylessSource Y ν`: the memoryless source of `ν`, answering each query with a fresh sample

## Main results

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

-- `A` fixes ports, finite alphabets and admitted histories; every reply type is nonempty.
variable (A : Interface) [∀ i, Nonempty (A.Y i)]

open Classical in
/-- A stored reply has point law; an unrecorded input has uniform law on its port's replies.
This is [1, Example 3.6, equation (3.1), p. 67]; [1, Definition 3.15, p. 64] requires
“equal inputs are always answered by identical outputs”. -/
def replyLaw
    -- `table i` retains input/reply pairs at port `i`; `x` is the current input there.
    (table : ∀ i, List (A.X i × A.Y i)) (i : A.I) (x : A.X i) :
    ProbDist (A.Y i) :=
  ((table i).lookup x).elim 𝒰[A.Y i] ProbDist.single

open Classical in
/-- Draw from `replyLaw`; on a miss append `(x, y)` at the queried port, and retain the other
records. [2, §4.4.2, p. 134]: “otherwise, he chooses yᵢ at random from the set Y”. -/
def tableLaw : ProbStep (∀ i, List (A.X i × A.Y i)) A.I A.X A.Y :=
  ProbStep.recordReplies (replyLaw A)

open Classical in
/-- The lazy presentation on `A.domain`: start with an empty list at every port and use
`tableLaw` for each query. Stored replies are reused; misses draw independently at that port. -/
def lazy : TypedSystem A :=
  TypedSystem.ofProbAutomaton A (tableLaw A) (ProbDist.single (fun _ => []))

open Classical in
/-- Complete the retained records to a function: at tagged input `q = (i, x)`, use its stored
reply if present and an independent uniform reply otherwise. Tagged inputs at different ports
are separate coordinates of this normalized product. -/
def completionLaw
    -- `table i` contains the input/reply records already retained at port `i`.
    (table : ∀ i, List (A.X i × A.Y i)) :
    ProbDist (∀ q : Σ i, A.X i, A.Y q.1) :=
  ProbDist.piDep fun q => replyLaw A table q.1 q.2

open Classical in
/-- Recording a fresh reply fixes exactly its coordinate in the independent completion law. -/
lemma completionLaw_update_eq
    -- `table` contains prior records; `i(x)` is the query and `y` its newly recorded reply.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (y : A.Y i)
    -- `miss` ensures no earlier record fixes a different value at `i(x)`.
    (miss : (table i).lookup x = none) :
    (completionLaw A (Function.update table i (table i ++ [(x, y)]))).1 =
      piDep (Function.update (fun q : Σ j, A.X j => (replyLaw A table q.1 q.2).1)
        ⟨i, x⟩ (Finsupp.single y 1)) := by
  unfold completionLaw
  rw [ProbDist.piDep_val]
  -- Compare the factor at each tagged input `(j, z)`.
  congr 1
  funext ⟨j, z⟩
  by_cases hj : j = i
  · subst j
    by_cases hx : z = x
    · subst z
      -- The newly recorded coordinate changes from uniform to the point mass at `y`.
      simp only [Function.update_self, replyLaw, List.lookup_append, miss, Option.none_or,
        List.lookup_cons_self, Option.elim_some, ProbDist.single]
    · -- Another input at the same port keeps its earlier lookup.
      have hq : (⟨i, z⟩ : Σ j, A.X j) ≠ ⟨i, x⟩ := by
        intro he
        exact hx (eq_of_heq (Sigma.mk.inj_iff.mp he).2)
      have absent : ([(x, y)] : List (A.X i × A.Y i)).lookup z = none := by
        simp only [List.lookup_cons, List.lookup_nil, beq_eq_false_iff_ne.mpr hx]
      simp only [replyLaw, Function.update_self, Function.update_of_ne hq,
        List.lookup_append, absent, Option.or_none]
  · -- Another port keeps its whole list of records.
    have hq : (⟨j, z⟩ : Σ j, A.X j) ≠ ⟨i, x⟩ := fun he => hj (congrArg Sigma.fst he)
    simp only [replyLaw, Function.update_of_ne hj, Function.update_of_ne hq]

open Classical in
/-- Every supported completion agrees with a stored lookup. -/
lemma completionLaw_apply_eq_of_lookup
    -- `hit` records reply `y` at input `x` of port `i` in `table`.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (y : A.Y i) (hit : (table i).lookup x = some y)
    -- `hf` says `f` is a possible completion of those records.
    (f : ∀ q : Σ j, A.X j, A.Y q.1) (hf : f ∈ (completionLaw A table).1.support) :
    f ⟨i, x⟩ = y := by
  let factors := fun q : Σ j, A.X j => (replyLaw A table q.1 q.2).1
  -- Fixing the already pinned coordinate leaves the product factors unchanged.
  have fixed : Function.update factors ⟨i, x⟩ (Finsupp.single y 1) = factors := by
    have value : factors ⟨i, x⟩ = Finsupp.single y 1 := by
      simp only [factors, replyLaw, hit, Option.elim_some, ProbDist.single]
    rw [← value, Function.update_eq_self]
  -- A supported function takes the point-mass value at that coordinate.
  apply eq_of_mem_support_piDep_update factors ⟨i, x⟩ y
  simpa only [fixed, factors, completionLaw, ProbDist.piDep_val] using hf

open Classical in
/-- On a fresh input, complete the table by first drawing its reply uniformly and then
completing the updated records. -/
lemma completionLaw_eq_bind
    -- `table` contains the past records; `miss` makes `i(x)` a fresh coordinate.
    (table : ∀ i, List (A.X i × A.Y i))
    (i : A.I) (x : A.X i) (miss : (table i).lookup x = none) :
    completionLaw A table =
      𝒰[A.Y i].bind (fun y => completionLaw A (Function.update table i (table i ++ [(x, y)]))) := by
  apply Subtype.ext
  change piDep (fun q : Σ j, A.X j => (replyLaw A table q.1 q.2).1) = _
  -- Disintegrate the independent product at the queried coordinate.
  rw [piDep_eq_bindK_update _ ⟨i, x⟩]
  have freshLaw : (replyLaw A table i x).1 = uniform (A.Y i) := by
    simp only [replyLaw, miss, Option.elim_none, ProbDist.uniform]
  rw [freshLaw]
  -- The remaining factors are exactly the completions after recording the sampled reply.
  apply bindK_congr
  intro y _
  exact (completionLaw_update_eq A table i x y miss).symm

open Classical in
/-- Completing the records before answering has the same joint law as answering from the
lazy table and completing the resulting records, with the same tagged reply. -/
lemma tableLaw_simulates
    -- `table` contains per-port records; `query` selects a port and an input at that port.
    (table : ∀ i, List (A.X i × A.Y i)) (query : Σ i, A.X i) :
    ProbStep.SimulatesAt (tableLaw A)
      (fun f i x => (ProbDist.single (f ⟨i, x⟩)).map (fun y => (f, y)))
      (completionLaw A) table query := by
  obtain ⟨i, x⟩ := query
  simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbDist.map_val, ProbDist.single,
    fTransform_single]
  rw [bindK_single_comp]
  cases lookup : (table i).lookup x with
  | none =>
    -- Reveal a fresh coordinate, then retain it in the conditional completion.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_none,
      Option.isNone_none,
      ite_true, ProbDist.map_val, fTransform_fTransform, Function.comp_def,
      bindK_fTransform, ProbStep.tagged]
    have disintegration := congrArg Subtype.val (completionLaw_eq_bind A table i x lookup)
    rw [disintegration, ProbDist.bind_val, fTransform_bindK]
    apply bindK_congr
    intro y _
    apply fTransform_congr_support
    intro f hf
    rw [completionLaw_update_eq A table i x y lookup] at hf
    -- Every resulting completion returns the freshly drawn reply at this input.
    have pin := eq_of_mem_support_piDep_update
      (fun q : Σ j, A.X j => (replyLaw A table q.1 q.2).1) ⟨i, x⟩ y hf
    rw [pin]
  | some y =>
    -- A hit leaves the records unchanged; every completion already returns `y`.
    simp only [tableLaw, ProbStep.recordReplies, replyLaw, lookup, Option.elim_some,
      Option.isNone_some,
      ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul, ProbStep.tagged]
    apply fTransform_congr_support
    intro f hf
    rw [completionLaw_apply_eq_of_lookup A table i x y lookup f hf]

open Classical in
/-- Lazy sampling is the existing URF on every admitted history, including adaptive repeated
queries across ports. [2, §4.4.2, p. 133]: “we can implement the random function”. -/
theorem lazy_eq : lazy A = Commons.URF A := by
  -- The one-query completion identity lifts to all histories on the declared domain.
  have simulation := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A) (tableLaw A)
    (fun f i x => (ProbDist.single (f ⟨i, x⟩)).map (fun y => (f, y))) (completionLaw A)
    (fun _ _ => True) (by intros; trivial) (by intros; apply tableLaw_simulates)
    (ProbDist.single (fun _ => [])) (by intros; trivial)
  -- Completing empty records gives independent uniform coordinates.
  have initial : (ProbDist.single (fun _ => [])).bind (completionLaw A) =
      𝒰[∀ q : Σ i, A.X i, A.Y q.1] := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.single, bindK_single, one_smul,
      completionLaw, ProbDist.piDep_val, replyLaw, List.lookup_nil, Option.elim_none,
      ProbDist.uniform]
    exact piDep_uniform (A := fun q : Σ i, A.X i => A.Y q.1)
  -- The completed table is a retained key with point-mass replies.
  rw [initial, TypedSystem.ofProbAutomaton_eq_keyed, TypedSystem.keyed_single] at simulation
  change lazy A = _ at simulation
  rw [simulation]
  unfold Commons.URF
  -- Curry tagged-coordinate functions into the existing URF carrier, preserving uniformity.
  have eqUniform := fTransform_equiv_uniform (Equiv.piCurry fun i (_ : A.X i) => A.Y i)
  have transport :=
    (TypedSystem.sample_fTransform (A := A) (Equiv.piCurry fun i (_ : A.X i) => A.Y i)
      (uniform (∀ q : Σ i, A.X i, A.Y q.1)) TypedSystem.ofFunction).symm
  -- Reindexing preserves the evaluator answers.
  simp only [eqUniform, Equiv.piCurry_apply] at transport
  -- Match the normalized key law to its underlying raw distribution.
  convert transport using 1
  simp only [ProbDist.uniform]
  congr 1

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

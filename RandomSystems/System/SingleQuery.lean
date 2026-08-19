/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Attainment

/-!
# The single-query slice: thesis §2.4.2's tuple reading (obligation U1)

Lanzenberger opens the proof of Theorem 2.31 (printed p. 20, §2.4.2, "The
Single-Query Case") with an unnumbered but load-bearing reading:

> Observe that a single-query `(𝒳,𝒴)`-DDS `s` is a function from `𝒳` to `𝒴`,
> and can thus be represented by a tuple
> `(y_{x₁}, y_{x₂}, …, y_{xₙ}) ∈ 𝒴ⁿ`, where `𝒳 = {x₁,…,xₙ}` and `s(xᵢ) = y_{xᵢ}`.

This file states that reading on the current carrier and proves it.

## What "single-query" is on this carrier

Definition 2.9's DDS is a partial function on *histories*, so "single-query"
is a condition on the domain, and there are two honest readings of it:

* `System.singleQueryDomain X = {[x] | x : X}` — the domain is **exactly** the
  length-one histories.  This is the thesis's reading: every query is
  answered, so the tuple lands in `Yⁿ`, and `singleQueryEquiv` is the
  bijection the quotation asserts.
* `QBounded (· ∈ dom s) 1` — the domain is **contained** in the length-one
  histories (`dom_subset_singleQueryDomain_of_qBounded_one`; the empty history
  is outside every domain by `Valid`).  This is the tree's `QBounded`-at-`D`
  vocabulary, it is what the L2a hypothesis bundle
  `PDS.HaveCommonDomainAndBounded` carries, and it is strictly weaker: a
  `1`-bounded system may *refuse* some queries.

  Under CR18 Definition 3.3 a refusal is the observable answer `none`, so on
  this reading the answer tuple lands in `(Option Y)ⁿ` rather than `Yⁿ`, and
  the determination statement is
  `eq_of_qBounded_one_of_answer_eq`.  **This is a documented deviation from the
  thesis**, which totalizes over a finite alphabet and therefore never sees the
  refusing case; it is the same `⊥`-visibility that
  `AttainmentCounterexample`-style arguments turn on, so it is not cosmetic.

## Scope

The quotation's second half — `Adv(S,T) = maxᵢ δ(Sᵢ,Tᵢ)` for single-query
systems — is the depth-`1` case of L3's query induction and is **not** restated
here; the tree reaches it through `PDS.exists_boundedAttainmentWitness`
(`Attainment.lean`), whose statement already covers every `q`.  What U1 asks
for and what is delivered here is the representation itself.

## Provenance

The `singleQuery` constructor and its domain lemma follow the read-only quarry
`RandomSystems/Example216.lean:129,140` (`singleQuery`, `mem_dom_singleQuery`),
which likewise assembles it from `glue`/`prepend`/`empty` rather than reusing
the total `functionEvaluator` — a total evaluator answers *every* history, and
the single-query restriction is load-bearing (see
`RandomSystems/System/Example216.lean`).  The `Equiv` and the determination
lemma are new: the quarry carries the representation only informally.
-/

namespace RandomSystems

noncomputable section

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-! ## The domain of a single-query system -/

/-- The single-query domain `X¹`: exactly the length-one histories.  This is
Definition 2.9's `dom(s) ⊆ ∪_{i≤1} Xⁱ` read at equality, the domain the
thesis's §2.4.2 tuple reading assumes.  COINAGE (the thesis writes `𝒳`). -/
def singleQueryDomain (X : Type u) : Set (List X) :=
  {l : List X | ∃ x : X, l = [x]}

@[simp] theorem mem_singleQueryDomain {l : List X} :
    l ∈ singleQueryDomain X ↔ ∃ x : X, l = [x] := Iff.rfl

theorem singleton_mem_singleQueryDomain (x : X) :
    [x] ∈ singleQueryDomain X := ⟨x, rfl⟩

/-- A `1`-bounded DDS has its domain inside the single-query domain: `Valid`
already keeps the empty history out, and `QBounded … 1` keeps everything of
length two or more out. -/
theorem dom_subset_singleQueryDomain_of_qBounded_one (s : DDS X Y)
    (hq : QBounded (fun l => l ∈ dom s) 1) :
    dom s ⊆ singleQueryDomain X := by
  intro l hl
  have hlen : l.length ≤ 1 := hq l hl
  rcases l with _ | ⟨x, m⟩
  · exact absurd hl (empty_not_mem s)
  · have : m = [] := by
      have : m.length = 0 := by simpa using hlen
      exact List.eq_nil_of_length_eq_zero this
    exact ⟨x, by rw [this]⟩

/-! ## The single-query system of an answer function -/

/-- Thesis Figure 2.1's genus and §2.4.2's object: the **single-query** DDS
realizing `f : X → Y` — domain exactly `X¹` (`dom_singleQuery`), answering
`f x` to the first query `x` and refusing everything afterwards.

Assembled from the existing constructors: `glue` dispatches on the first
query, `prepend x (some (f x))` answers it, and the `emptySystem`
continuation makes the system self-destruct.  This is deliberately *not*
`functionEvaluator f`, which accepts every nonempty history: a total
evaluator lets an environment read two coordinates of one sample, and the
single-query restriction is exactly what Example 2.16 turns on. -/
def DDS.singleQuery (f : X → Y) : DDS X Y :=
  DDS.glue fun x => DDS.prepend x (some (f x)) emptySystem

/-- The single-query system's domain is exactly `X¹`. -/
@[simp] theorem dom_singleQuery (f : X → Y) :
    dom (DDS.singleQuery f) = singleQueryDomain X := by
  ext l
  rcases l with _ | ⟨x, m⟩
  · refine iff_of_false (empty_not_mem _) ?_
    rintro ⟨x, hx⟩
    exact absurd hx (by simp)
  · rw [DDS.singleQuery, cons_mem_dom_glue, dom_prepend_some]
    constructor
    · rintro (h | ⟨m', hm', -⟩)
      · exact ⟨x, h⟩
      · exact absurd hm' (by rw [dom_emptySystem]; exact fun h => h)
    · rintro ⟨x', hx'⟩
      obtain ⟨rfl, rfl⟩ := List.cons_eq_cons.mp hx'
      exact Or.inl rfl

theorem singleton_mem_dom_singleQuery (f : X → Y) (x : X) :
    [x] ∈ dom (DDS.singleQuery f) := by
  rw [dom_singleQuery]; exact singleton_mem_singleQueryDomain x

open Classical in
/-- CR18 Definition 3.3 at a first query, with the deletion pass discharged:
before any history there is nothing to delete, so `s⊥`'s answer to `x` is the
value of `s` at `[x]` when it has one and `none` otherwise. -/
theorem answer_nil_eq (u : DDS X Y) (x : X) :
    answer u [] x = if h : [x] ∈ dom u then some (output u [x] h) else none :=
  answer_eq u [] x

/-- The single-query system answers its one query by `f`. -/
@[simp] theorem output_fullyDefined_singleQuery (f : X → Y) (x : X) :
    output (fullyDefined (DDS.singleQuery f)) [x]
        (by rw [dom_fullyDefined]; simp) = some (f x) :=
  output_fullyDefined_glue_prepend (fun x' => some (f x')) (fun _ => emptySystem) x

/-- The raw (uncompleted) value of the single-query system at its one query. -/
@[simp] theorem output_singleQuery (f : X → Y) (x : X)
    (h : [x] ∈ dom (DDS.singleQuery f)) :
    output (DDS.singleQuery f) [x] h = f x := by
  have hval : answer (DDS.singleQuery f) [] x = some (f x) :=
    output_fullyDefined_singleQuery f x
  rw [answer_nil_eq, dif_pos h] at hval
  exact Option.some.inj hval

/-- After its one query the single-query system is spent. -/
theorem successor_singleQuery (f : X → Y) (x : X) :
    DDS.successor (DDS.singleQuery f) x = emptySystem :=
  successor_glue_prepend (fun x' => some (f x')) (fun _ => emptySystem) x rfl

/-- The `answer` spelling of `output_fullyDefined_singleQuery`. -/
@[simp] theorem answer_nil_singleQuery (f : X → Y) (x : X) :
    answer (DDS.singleQuery f) [] x = some (f x) :=
  output_fullyDefined_singleQuery f x

/-! ## U1: the tuple representation -/

/-- **U1, determination** (the `QBounded`-at-`D` reading): two `1`-bounded
deterministic systems that give the same `s⊥`-answer to every query are equal.

The answers range over `Option Y`, not `Y`: a `1`-bounded system may refuse,
and CR18 Definition 3.3 makes the refusal the observable answer `none`.  The
thesis's `Yⁿ` reading is the total case, `singleQueryEquiv` below. -/
theorem eq_of_qBounded_one_of_answer_eq {s t : DDS X Y}
    (hs : QBounded (fun l => l ∈ dom s) 1) (ht : QBounded (fun l => l ∈ dom t) 1)
    (h : ∀ x : X, answer s [] x = answer t [] x) :
    s = t := by
  refine Subtype.ext (funext fun l => ?_)
  have hkey : ∀ (u : DDS X Y), ∀ x : X, ∀ hx : [x] ∈ dom u,
      answer u [] x = some (output u [x] hx) := fun u x hx => by
    rw [answer_nil_eq, dif_pos hx]
  have hnone : ∀ (u : DDS X Y), ∀ x : X, [x] ∉ dom u → answer u [] x = none :=
    fun u x hx => by rw [answer_nil_eq, dif_neg hx]
  rcases hl : l with _ | ⟨x, m⟩
  · exact Part.ext' (iff_of_false (empty_not_mem s) (empty_not_mem t))
      fun h₁ _ => absurd h₁ (empty_not_mem s)
  · rcases hm : m with _ | ⟨c, m'⟩
    · -- the singleton case: the answers decide both membership and value
      have hiff : [x] ∈ dom s ↔ [x] ∈ dom t := by
        constructor
        · intro hx
          by_contra hx'
          have hx2 := h x
          rw [hkey s x hx, hnone t x hx'] at hx2
          exact absurd hx2 (by simp)
        · intro hx
          by_contra hx'
          have hx2 := h x
          rw [hkey t x hx, hnone s x hx'] at hx2
          exact absurd hx2 (by simp)
      refine Part.ext' hiff fun h₁ h₂ => ?_
      have := (hkey s x h₁).symm.trans ((h x).trans (hkey t x h₂))
      exact Option.some.inj this
    · -- everything longer is outside both domains
      have hs' : x :: c :: m' ∉ dom s := fun hd => by
        have := hs _ hd; simp at this
      have ht' : x :: c :: m' ∉ dom t := fun hd => by
        have := ht _ hd; simp at this
      exact Part.ext' (iff_of_false hs' ht') fun h₁ _ => absurd h₁ hs'

/-- `singleQuery` is injective: the answer function is recovered from the one
answer the system gives. -/
theorem singleQuery_injective :
    Function.Injective (DDS.singleQuery : (X → Y) → DDS X Y) := by
  intro f g h
  funext x
  have hf := output_fullyDefined_singleQuery f x
  rw [h, output_fullyDefined_singleQuery g x] at hf
  exact (Option.some.inj hf).symm

/-- **U1, the thesis's tuple reading**: single-query `(X,Y)`-systems *are* the
functions `X → Y`, hence at finite `X` the tuples `Y^{|X|}`
(`Nat.card_singleQuerySubtype`).

The subtype pins the domain to be *exactly* `X¹`, which is what makes the
tuple total; the weaker `QBounded … 1` reading is
`eq_of_qBounded_one_of_answer_eq`. -/
def singleQueryEquiv :
    (X → Y) ≃ {s : DDS X Y // dom s = singleQueryDomain X} where
  toFun f := ⟨DDS.singleQuery f, dom_singleQuery f⟩
  invFun s := fun x => output s.1 [x] (by rw [s.2]; exact singleton_mem_singleQueryDomain x)
  left_inv f := by
    funext x
    exact output_singleQuery f x (singleton_mem_dom_singleQuery f x)
  right_inv s := by
    refine Subtype.ext (eq_of_qBounded_one_of_answer_eq ?_ ?_ fun x => ?_)
    · intro l hl
      rw [dom_singleQuery] at hl
      obtain ⟨x, rfl⟩ := hl
      simp
    · intro l hl
      rw [s.2] at hl
      obtain ⟨x, rfl⟩ := hl
      simp
    · have hx : [x] ∈ dom s.1 := by
        rw [s.2]; exact singleton_mem_singleQueryDomain x
      rw [answer_nil_eq, answer_nil_eq, dif_pos hx,
        dif_pos (singleton_mem_dom_singleQuery _ x), output_singleQuery]

/-- **U1's cardinality receipt**: at a finite alphabet the single-query
systems are `Y^{|X|}`, the thesis's `𝒴ⁿ` with `n = |𝒳|`. -/
theorem card_singleQuerySubtype [Fintype X] [DecidableEq X] [Fintype Y] :
    Nat.card {s : DDS X Y // dom s = singleQueryDomain X}
      = Fintype.card Y ^ Fintype.card X := by
  rw [Nat.card_congr (singleQueryEquiv (X := X) (Y := Y)).symm,
    Nat.card_eq_fintype_card, Fintype.card_fun]

end System

end

end RandomSystems

import Probability.DependentProduct
import RandomSystems.Cumulative.ParallelAll
import RandomSystems.Converter.ConverterTensor
import RandomSystems.Converter.ConverterAttachment

/-!
# Finite parallel canonical converters

The parallel composition `⨂ₖ α k` of a finite family of converters
`α k : InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)`, `k ∈ K`, whose outside labels
`O k` and inside labels `J k` depend on `k`. Joint labels are tagged, `⟨k, o⟩ : Σ k, O k` and
`⟨k, j⟩ : Σ k, J k`. Writing `h|k` for the inputs of `h` tagged `k`, tags removed (`hAt k h`),
an input `z` regrouped to `⟨k, a⟩` is answered by component `k` alone:

  `tensorAllRaw α (h ++ [z]) = (α k (h|k ++ [a])).map (y ↦ tensorAllOutputs ⟨k, y⟩)`,
  `tensorAllL α h = tensorAllRaw α h` if `h` is admissible, undefined otherwise.

```text
  outside                                  inside
  ⟨k₁,o⟩(u)   ──▶ ┌──────┐ ──▶ ⟨k₁,j⟩(x)
  ⟨k₁,o⟩ ⇒ v  ◀── │ α k₁ │ ◀── ⟨k₁,j⟩ ⇒ y       sees h|k₁
                  └──────┘
     ⋮               ⋮                          one box per tag k ∈ K
  ⟨k₂,o'⟩(u') ──▶ ┌──────┐ ──▶ ⟨k₂,j'⟩(x')
  ⟨k₂,o'⟩ ⇒ v'◀── │ α k₂ │ ◀── ⟨k₂,j'⟩ ⇒ y'     sees h|k₂
                  └──────┘
```

An outside query finds every component idle, so at most one component has an open inside
call. A run of joint inside queries is a run of one component, and the consecutive bound is
`Finset.univ.sup b` (`0` for empty `K`), not `∑ k, b k`. Components may be partial: none is
required to answer every legal input.

Sources: Jost, Thesis, printed p. 17 (finite disjoint resources as one) for the wiring;
Def. 2.2.2, printed pp. 17–18 (alternating interfaces, consecutive bound) for the converters.

## Main definitions

* `tensorAllInputs`, `tensorAllOutputs`: regrouping of joint inputs and outputs by component
* `tensorAllRaw α`: the relabelled `parAll α`; `tensorAllL α`: its canonicalization
* `tensorAllPDC P`: `⨂ₖ f k` for independent samples `f k ∼ P k`
* `PDCBehavior.tensorAll`: the behavior of `tensorAllPDC` on chosen presentations

## Main results

* `IsDDC.tensorAllL`: `⨂ₖ α k` is a partial converter with bound `Finset.univ.sup b`
* `IsDDCFrom.tensorAllL`: DDCs from `E k` to `F k` give one from `parallelAllInputs E` to
  `parallelAllInputs F`
* `behaviorMass_tensorAllPDC`: for any presentations `P k` and admitted, consistent `t`,
  `Pr_{tensorAllPDC P}[Replies · t] = ∏ k, Pr_{P k}[Replies · t'|k]`
* `PDCBehavior.tensorAll_apply`: with `t'` the regrouped transcript,
  `(tensorAll α)(t) = ∏ k, α_k(t'|k)` if `t` is admitted and `t'` tag-consistent, else `0`
* `PDCBehavior.tensorAll_ofDDC`: on DDC behaviors, `tensorAll` is the behavior of `tensorAllL`
-/

namespace SystemAlgebra

open Probability
open scoped NNReal ENNReal

variable {K : Type} [Fintype K] [DecidableEq K]

/-! ### The tagged converter and its invariant -/

section Tensor

variable {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}

open Classical in
/-- Regrouping of joint converter inputs by component, with `out = none`, `in = some ()`:
`(out ⟨k, o⟩, u) ↦ ⟨k, (out o, u)⟩` for `u : U k o`, `(in ⟨k, j⟩, y) ↦ ⟨k, (in j, y)⟩` for
`y : Y k j`. -/
def tensorAllInputs :
    (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l) ≃
      Σ k, Σ l : Two (O k) (J k), twoFam (U k) (Y k) l where
  toFun
    | ⟨⟨none, ⟨k, o⟩⟩, u⟩ => ⟨k, ⟨⟨none, o⟩, u⟩⟩
    | ⟨⟨some (), ⟨k, j⟩⟩, y⟩ => ⟨k, ⟨⟨some (), j⟩, y⟩⟩
  invFun
    | ⟨k, ⟨⟨none, o⟩, u⟩⟩ => ⟨⟨none, ⟨k, o⟩⟩, u⟩
    | ⟨k, ⟨⟨some (), j⟩, y⟩⟩ => ⟨⟨some (), ⟨k, j⟩⟩, y⟩
  left_inv := by rintro ⟨⟨(_ | ⟨⟩), ⟨k, i⟩⟩, x⟩ <;> rfl
  right_inv := by rintro ⟨k, ⟨⟨(_ | ⟨⟩), i⟩, x⟩⟩ <;> rfl

open Classical in
/-- Joint converter outputs from component outputs, the inverse regrouping on `V`, `X`:
`⟨k, (out o, v)⟩ ↦ (out ⟨k, o⟩, v)`, `⟨k, (in j, x)⟩ ↦ (in ⟨k, j⟩, x)`. -/
abbrev tensorAllOutputs := (tensorAllInputs (U := V) (Y := X)).symm

open Classical in
/-- The raw n-ary parallel converter `[α_k]_k`: `parAll α` relabelled by the regroupings.
`[α_k]_k [] = none` and, for `tensorAllInputs z = ⟨k, a⟩` (`tensorAllRaw_snoc`),
`[α_k]_k (h ++ [z]) = (α k (h|k ++ [a])).map (y ↦ tensorAllOutputs ⟨k, y⟩)`, on and off the
admissible tree. -/
noncomputable def tensorAllRaw (α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)) :
    InsideOutsideSystem (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2) :=
  relabel (parAll α) tensorAllInputs tensorAllOutputs

open Classical in
/-- **The n-ary parallel converter** `⨂ₖ α k = canon [α_k]_k`: `⨂ₖ α k h = [α_k]_k h` if
`h` is admissible for `[α_k]_k`, undefined otherwise; equalities of `⨂ₖ α k` thus never
depend on raw off-tree values of `[α_k]_k`. Jost, Thesis, printed
p. 17: “A finite set of resources with disjoint interface sets can be viewed as a single one”;
this is the converter wiring that statement motivates, not a construction stated there. -/
noncomputable def tensorAllL (α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)) :
    InsideOutsideSystem (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2) :=
  canon (tensorAllRaw α)

open Classical in
/-- Tagging a component label: `labAt k (out o) = out ⟨k, o⟩`, `labAt k (in j) = in ⟨k, j⟩`. -/
def labAt (k : K) : Two (O k) (J k) → Two (Σ k, O k) (Σ k, J k)
  | ⟨none, o⟩ => ⟨none, ⟨k, o⟩⟩
  | ⟨some (), j⟩ => ⟨some (), ⟨k, j⟩⟩

open Classical in
/-- The input history of component `k`, `h|k = restrict k (h.map tensorAllInputs)`: the
inputs of `h` tagged `k`, in order, tags removed. -/
noncomputable abbrev hAt (k : K)
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    List (Σ l : Two (O k) (J k), twoFam (U k) (Y k) l) :=
  restrict k (h.map tensorAllInputs)

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- `(tensorAllOutputs ⟨k, y⟩).1 = labAt k y.1`. -/
lemma tensorAllOutputs_fst (k : K) (y : Σ l : Two (O k) (J k), twoFam (V k) (X k) l) :
    (tensorAllOutputs (V := V) (X := X) ⟨k, y⟩).1 = labAt k y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma isInside_tensorAllOutputs (k : K) (y : Σ l : Two (O k) (J k), twoFam (V k) (X k) l) :
    IsInside (tensorAllOutputs (V := V) (X := X) ⟨k, y⟩) ↔ IsInside y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

variable {α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)}
  {h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l)}
  {z : Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l}

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- Only the addressed component answers: for `z ↦ ⟨k, a⟩`,
`[α_k]_k (h ++ [z]) = (α k (h|k ++ [a])).map (y ↦ tensorAllOutputs ⟨k, y⟩)`. -/
lemma tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    tensorAllRaw α (h ++ [z]) =
      (α k (hAt k h ++ [a])).map (fun y => tensorAllOutputs (V := V) (X := X) ⟨k, y⟩) := by
  simp only [tensorAllRaw, relabel, List.map_append, List.map_singleton, hz, parAll_snoc,
    Part.map_map]
  rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- For `z ↦ ⟨k, a⟩`, `(h ++ [z])|k = h|k ++ [a]`. -/
lemma hAt_snoc_self {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    hAt k (h ++ [z]) = hAt k h ++ [a] := by
  simp only [hAt, List.map_append, List.map_singleton, hz, restrict_append, restrict_cons_self,
    restrict_nil]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- For `z ↦ ⟨k, a⟩` and `k' ≠ k`, `(h ++ [z])|k' = h|k'`. -/
lemma hAt_snoc_ne {k k' : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) (hk : k' ≠ k) :
    hAt k' (h ++ [z]) = hAt k' h := by
  simp only [hAt, List.map_append, List.map_singleton, hz, restrict_append,
    restrict_cons_ne (Ne.symm hk), restrict_nil, List.append_nil]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The joint reply label is component `k`'s reply label, tagged by `labAt k`. -/
lemma replyLabel_tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    replyLabel (tensorAllRaw α) (h ++ [z]) = (replyLabel (α k) (hAt k h ++ [a])).map (labAt k) := by
  unfold replyLabel
  rw [tensorAllRaw_snoc hz]
  -- Both sides are defined exactly when `α k` answers `h|k ++ [a]`.
  by_cases hd : (α k (hAt k h ++ [a])).Dom
  · rw [dif_pos hd, dif_pos (by simpa only [Part.map_Dom] using hd)]
    exact congrArg some (tensorAllOutputs_fst _ _)
  · rw [dif_neg hd, dif_neg (by simpa only [Part.map_Dom] using hd)]
    rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The joint run of consecutive inside queries grows by one if component `k` replies inside
to `h|k ++ [a]`, and is `0` otherwise. -/
lemma insideRun_tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    insideRun (tensorAllRaw α) (h ++ [z]) =
      if ∃ y ∈ α k (hAt k h ++ [a]), IsInside y then insideRun (tensorAllRaw α) h + 1 else 0 := by
  rw [insideRun, run_snoc, tensorAllRaw_snoc hz]
  congr 1
  -- Tagging by `tensorAllOutputs ⟨k, ·⟩` preserves being an inside query.
  simp only [Part.mem_map_iff]
  exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_tensorAllOutputs k y).mp hi⟩,
    fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_tensorAllOutputs k y).mpr hi⟩⟩

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- `[α_k]_k []` is undefined. -/
lemma tensorAllRaw_silentAtEmpty : SilentAtEmpty (tensorAllRaw α) := by
  simp only [SilentAtEmpty, tensorAllRaw, relabel, parAll, List.map_nil, List.getLast?_nil,
    Part.map_none, Part.not_none_dom, not_false_eq_true]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- `[α_k]_k` has no reply at `[]`. -/
lemma replyLabel_tensorAllRaw_nil : replyLabel (tensorAllRaw α) [] = none := by
  simp only [replyLabel, dif_neg tensorAllRaw_silentAtEmpty]

variable (α) in
open Classical in
/-- Component `k` is idle after `h`: its last reply is no inside query,
`∀ j, replyLabel (α k) (h|k) ≠ some (in j)`. -/
def IdleAt (k : K)
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    Prop :=
  ∀ j, replyLabel (α k) (hAt k h) ≠ some ⟨some (), j⟩

variable (α) in
open Classical in
/-- The state of `[α_k]_k` after a nonempty `h` it answers, one of:

* all idle: the last reply is `out o`, `lastOuter h = some o`, every component idle;
* one active: the last reply is `in ⟨k, j⟩`, `replyLabel (α k) (h|k) = some (in j)`, every
  `k' ≠ k` idle, `lastOuter h = (lastOuter (h|k)).map (Sigma.mk k)`, and
  `insideRun [α_k]_k h ≤ insideRun (α k) (h|k)`.

The empty history, with no reply and all components idle, is handled separately. -/
def TCaseAll
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    Prop :=
  (∃ o, replyLabel (tensorAllRaw α) h = some ⟨none, o⟩ ∧ lastOuter h = some o ∧
    ∀ k, IdleAt α k h) ∨
  (∃ k j, replyLabel (tensorAllRaw α) h = some ⟨some (), ⟨k, j⟩⟩ ∧
    replyLabel (α k) (hAt k h) = some ⟨some (), j⟩ ∧ (∀ k', k' ≠ k → IdleAt α k' h) ∧
    lastOuter h = (lastOuter (hAt k h)).map (Sigma.mk k) ∧
    insideRun (tensorAllRaw α) h ≤ insideRun (α k) (hAt k h))

variable (α) in
open Classical in
/-- The invariant of `[α_k]_k` along admissible histories `h`:

* `h ≠ [] → [α_k]_k h` is defined;
* for every `k`, `h|k` is admissible for `α k`, and `h|k ≠ [] → α k (h|k)` is defined;
* `h ≠ [] → TCaseAll α h`.

It states definedness only on the admitted projections, not responsiveness of `α k`. -/
def TInvAll
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    Prop :=
  (h ≠ [] → (tensorAllRaw α h).Dom) ∧
    (∀ k, Admissible (α k) (hAt k h) ∧ (hAt k h ≠ [] → (α k (hAt k h)).Dom)) ∧
    (h ≠ [] → TCaseAll α h)

variable {b : K → ℕ}

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- One invariant step to `h ++ [z]`, `z ↦ ⟨k, a⟩`: if the projections satisfy the invariant,
`α k` admits `a` after `h|k`, every `k' ≠ k` is idle, `lastOuter` and the joint run transfer
to `k`, and `α k` answers the admissible `h|k ++ [a]`, then `TInvAll α (h ++ [z])`. -/
lemma tpostAll (hα : ∀ k, IsDDC (b k) (α k)) {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩)
    (hcomp : ∀ k, Admissible (α k) (hAt k h) ∧ (hAt k h ≠ [] → (α k (hAt k h)).Dom))
    (hadm : Admits (α k) (hAt k h) a) (hid : ∀ k', k' ≠ k → IdleAt α k' h)
    (hlo : lastOuter (h ++ [z]) = (lastOuter (hAt k h ++ [a])).map (Sigma.mk k))
    (hrun : insideRun (tensorAllRaw α) h ≤ insideRun (α k) (hAt k h))
    (hnext : Admissible (α k) (hAt k h ++ [a]) → (α k (hAt k h ++ [a])).Dom) :
    TInvAll α (h ++ [z]) := by
  -- `h|k ++ [a]` is admissible for `α k`, so `α k` answers it with some `y`.
  have ha' : Admissible (α k) (hAt k h ++ [a]) :=
    admissible_snoc.mpr ⟨(hcomp k).1, (hcomp k).2, hadm⟩
  have hd' : (α k (hAt k h ++ [a])).Dom := hnext ha'
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd'
  -- The joint rule answers `h ++ [z]` with `y` tagged `k`.
  have hdRaw : (tensorAllRaw α (h ++ [z])).Dom := by rw [tensorAllRaw_snoc hz]; exact hd'
  have hl' : replyLabel (tensorAllRaw α) (h ++ [z]) = some (labAt k y.1) := by
    rw [replyLabel_tensorAllRaw_snoc hz, replyLabel_of_mem (α k) hy]; rfl
  -- Components `k' ≠ k` receive no input and stay idle.
  have hid' : ∀ k', k' ≠ k → IdleAt α k' (h ++ [z]) := fun k' hk' => by
    unfold IdleAt
    rw [hAt_snoc_ne hz hk']
    exact hid k' hk'
  refine ⟨fun _ => hdRaw, fun k' => ?_, fun _ => ?_⟩
  -- Projections: `k` gains `a`; every other projection is unchanged.
  · by_cases hk' : k' = k
    · subst hk'
      rw [hAt_snoc_self hz]
      exact ⟨ha', fun _ => hd'⟩
    · rw [hAt_snoc_ne hz hk']
      exact hcomp k'
  -- The new case is decided by `y`: outside reply ⇒ all idle, inside query ⇒ `k` active.
  · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    -- `α k` replies `out l` at its last outside query (`IsDDC.replies`), so `k` is idle too.
    · refine Or.inl ⟨⟨k, l⟩, hl', ?_, fun k' => ?_⟩
      · rw [hlo, (hα k).replies _ _ l hy rfl]; rfl
      · by_cases hk' : k' = k
        · subst hk'
          intro j hj
          rw [hAt_snoc_self hz, replyLabel_of_mem _ hy] at hj
          simp only [Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and] at hj
        · exact hid' k' hk'
    -- `α k` queries `in l`; the joint run and `k`'s run both grow by one.
    · refine Or.inr ⟨k, l, hl', by rw [hAt_snoc_self hz]; exact replyLabel_of_mem (α k) hy, hid',
        by rw [hAt_snoc_self hz]; exact hlo, ?_⟩
      rw [insideRun_tensorAllRaw_snoc hz, if_pos ⟨_, hy, rfl⟩, hAt_snoc_self hz,
        insideRun_snoc_eq, if_pos ⟨_, hy, rfl⟩]
      omega

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- If the last joint reply after `h` is no inside query, every component is idle and
`insideRun [α_k]_k h = 0`; this is the state in which an outside query is admitted. -/
lemma tensorAll_idle (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hn : ∀ j, replyLabel (tensorAllRaw α) h ≠ some ⟨some (), j⟩) :
    (∀ k, IdleAt α k h) ∧ insideRun (tensorAllRaw α) h = 0 := by
  -- `h = []`: each `α k` is silent at `[]`. Otherwise `TCaseAll` must be the all-idle case.
  rcases eq_or_ne h [] with rfl | hne
  · refine ⟨fun k j hj => ?_, rfl⟩
    simp only [hAt, List.map_nil, restrict_nil, replyLabel_nil_conv (hα k)] at hj
    cases hj
  · rcases inv.2.2 hne with ⟨o, hl, -, hid⟩ | ⟨k, j, hl, -⟩
    · exact ⟨hid, insideRun_eq_zero_of_outer hl⟩
    · exact absurd hl (hn _)

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The invariant extends along an input `z ↦ ⟨k, a⟩` admitted by `[α_k]_k`, provided `α k`
answers `h|k ++ [a]` whenever it is admissible. -/
lemma tensorAll_step (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hadm : Admits (tensorAllRaw α) h z)
    (hn : ∀ k a, tensorAllInputs z = ⟨k, a⟩ → Admissible (α k) (hAt k h ++ [a]) →
      (α k (hAt k h ++ [a])).Dom) :
    TInvAll α (h ++ [z]) := by
  obtain ⟨hd, hcomp, hcase⟩ := inv
  have inv : TInvAll α h := ⟨hd, hcomp, hcase⟩
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k, o⟩⟩, v⟩
  · -- an outside input to component `k`: all components are idle and the joint run is `0`
    obtain ⟨hid, hr0⟩ := tensorAll_idle hα inv (admitAfter_outer hadm)
    refine tpostAll hα rfl hcomp ?_ (fun k' _ => hid k') ?_
      (by rw [hr0]; exact Nat.zero_le _) (hn _ _ rfl)
    · exact (admitAfter_of_ne (hid k)).mpr rfl
    · rw [lastOuter_snoc, lastOuter_snoc]; rfl
  · -- an inside reply to component `k`: the last joint reply was the query `in ⟨k, o⟩`
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl; cases hl
    -- so `TCaseAll` is the one-active case, with `k` the active component and `o` its call
    rcases hcase hne with ⟨o', hl', -⟩ | ⟨k', j, hl', hj, hid, hlo, hrun⟩
    · rw [hl] at hl'; simp only [Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and] at hl'
    · rw [hl] at hl'
      simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl'
      obtain ⟨rfl, hoj⟩ := hl'
      obtain rfl := eq_of_heq hoj
      refine tpostAll hα rfl hcomp ?_ hid ?_ hrun (hn _ _ rfl)
      · unfold Admits
        rw [hj]
        rfl
      · rw [lastOuter_snoc, lastOuter_snoc]
        simpa only [outerOf, Option.none_or] using hlo

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The invariant holds at `[]`, where every projection is empty. -/
lemma tInvAll_nil : TInvAll α [] :=
  ⟨fun h => absurd rfl h,
    fun _ => ⟨by simp only [hAt, List.map_nil, restrict_nil, admissible_nil],
      fun h => absurd (by simp only [hAt, List.map_nil, restrict_nil]) h⟩,
    fun h => absurd rfl h⟩

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- `TInvAll α h` for every admissible `h` with `h ≠ [] → [α_k]_k h` defined; admissibility
gives definedness on the shorter nonempty prefixes. The components need not be responsive. -/
lemma tensorAll_inv_partial (hα : ∀ k, IsDDC (b k) (α k)) :
    ∀ h, Admissible (tensorAllRaw α) h → (h ≠ [] → (tensorAllRaw α h).Dom) → TInvAll α h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; exact tInvAll_nil
  | append_singleton h z ih =>
    intro ha hd
    obtain ⟨ha₀, hd₀, hz⟩ := admissible_snoc.mp ha
    have hd' := hd (by simp only [ne_eq, List.append_eq_nil_iff, List.cons_ne_self, and_false,
      not_false_eq_true])
    -- The joint rule answers `h ++ [z]`, hence `α k` answers `h|k ++ [a]` (`tensorAllRaw_snoc`).
    refine tensorAll_step hα (ih ha₀ hd₀) hz fun k a e _ => ?_
    rw [tensorAllRaw_snoc e] at hd'
    exact hd'

omit [DecidableEq K] in
open Classical in
/-- **`⨂ₖ α k` is a partial converter with bound `max_k b k`** (`Finset.univ.sup b`, `0` for
empty `K`). Jost Def. 2.2.2, printed p. 18: “There is a finite upper bound on the number of
consecutive outputs of the form (y, I′) ∈ X × I_in.” At most one component has an open inside
call, so a joint run is a run of one component: the bound is the maximum, not `∑ k, b k`. -/
theorem IsDDC.tensorAllL (hα : ∀ k, IsDDC (b k) (α k)) :
    IsDDC (Finset.univ.sup b) (tensorAllL α) := by
  -- Canonicalization supplies the off-tree behavior; check the raw rule on admitted histories.
  refine canon_isDDC ?_ ?_ ?_
  -- Silent at `[]`.
  · exact tensorAllRaw_silentAtEmpty
  · intro h ha hd
    -- At most one component is active, so its run is bounded by the largest component bound.
    rcases eq_or_ne h [] with rfl | hne
    · exact Nat.zero_le _
    rcases (tensorAll_inv_partial hα h ha (fun _ => hd)).2.2 hne with ⟨o, hl, -⟩ |
        ⟨k, j, -, hj, -, -, hrun⟩
    -- All idle: the last reply is outside, so the run is `0`.
    · rw [insideRun_eq_zero_of_outer hl]; exact Nat.zero_le _
    -- `k` active: joint run ≤ `insideRun (α k) (h|k)` ≤ `b k` ≤ `max_k b k`.
    · have hdk : (α k (hAt k h)).Dom := by
        by_contra hn; simp only [replyLabel, hn, ↓reduceDIte, reduceCtorEq] at hj
      exact hrun.trans (((hα k).bound _ hdk).trans (Finset.le_sup (Finset.mem_univ k)))
  · intro h y o ha hy hl
    -- An outside reply carries the joint label of the last outside query, not another
    -- component's: an outside reply `out o` forces the all-idle case, where `lastOuter h = o`.
    have hl' := replyLabel_of_mem _ hy
    rw [hl] at hl'
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl'; cases hl'
    rcases (tensorAll_inv_partial hα h ha (fun _ => Part.dom_iff_mem.mpr ⟨y, hy⟩)).2.2 hne
      with ⟨o', hl'', hlo, -⟩ | ⟨k, j, hl'', -⟩
    · rw [hl'] at hl''
      obtain rfl : o = o' := by
        simpa only [Option.some.injEq, Sigma.mk.injEq, heq_eq_eq, true_and] using hl''
      exact hlo
    · rw [hl'] at hl''
      simp only [Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and] at hl''

omit [Fintype K] in
open Classical in
/-- The transcripts of `[α_k]_k` are the interleavings of the components' transcripts: with
`t' = t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)` the regrouped exchanges, `t` is
a transcript iff every exchange of `t'` has equal input and output tags and, for every `k`,
`t'|k` is a transcript of `α k`. -/
lemma replies_tensorAllRaw_iff
    (h : List ((Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l) ×
      (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => V o.1 o.2) (fun j => X j.1 j.2) l))) :
    Replies (tensorAllRaw α) (h.map Prod.fst) (h.map Prod.snd) ↔
      RandomSystem.parallelAllConsistent (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)) ∧
      ∀ k, Replies (α k)
        ((RandomSystem.restrictExchanges k (h.map (tensorAllInputs.prodCongr
          tensorAllOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.restrictExchanges k (h.map (tensorAllInputs.prodCongr
          tensorAllOutputs.symm))).map
          Prod.snd) :=
  (replies_relabel_iff (parAll α) tensorAllInputs tensorAllOutputs h).trans
    (RandomSystem.replies_parAll_iff α _)

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- Projection commutes with taking outside inputs: `(outsideInputs xs)|k` (regrouped by
`Equiv.sigmaAssoc U`) `= outsideInputs (xs|k)`. -/
lemma outsideInputs_at (k : K)
    (xs : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    restrict k ((outsideInputs xs).map (Equiv.sigmaAssoc U)) = outsideInputs (hAt k xs) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [outsideInputs_append, List.map_append, restrict_append, ih, hAt]
    congr 1
    -- The last input: outside or inside, at `k` or at another tag.
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, u⟩
    · by_cases hk : k' = k
      · subst hk
        simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, outsideInputs, List.map_cons, splitIn,
          List.map_nil, restrict_cons_self, restrict_nil, tensorAllInputs]
      · simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, outsideInputs, List.map_cons, splitIn,
        List.map_nil, restrict_cons_self, restrict_nil, restrict_cons_ne hk, tensorAllInputs]
    · by_cases hk : k' = k
      · subst hk
        simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, outsideInputs, List.map_cons, splitIn,
          List.map_nil, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne, restrict_nil,
          tensorAllInputs, restrict_cons_self]
      · simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, outsideInputs, List.map_cons, splitIn,
        List.map_nil, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne, restrict_nil,
        tensorAllInputs, restrict_cons_ne hk]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- Projection commutes with taking inside queries: `(insideQueries ys)|k` (regrouped by
`Equiv.sigmaAssoc X`) `= insideQueries (ys'|k)`, where `ys'` is `ys` regrouped by component. -/
lemma insideQueries_at (k : K)
    (ys : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => V o.1 o.2) (fun j => X j.1 j.2)
      l)) :
    restrict k ((insideQueries ys).map (Equiv.sigmaAssoc X)) =
      insideQueries (restrict k (ys.map (tensorAllOutputs (V := V) (X := X)).symm)) := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    simp only [insideQueries_append, List.map_append, restrict_append, ih]
    congr 1
    -- The last output: outside or inside, at `k` or at another tag.
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, v⟩
    · by_cases hk : k' = k
      · subst hk
        simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, insideQueries, List.map_cons, splitIn,
          List.map_nil, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne, restrict_nil,
          Equiv.symm_symm, tensorAllInputs, restrict_cons_self]
      · simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, insideQueries, List.map_cons, splitIn,
        List.map_nil, ne_eq, reduceCtorEq, not_false_eq_true, restrict_cons_ne, restrict_nil,
        Equiv.symm_symm, tensorAllInputs, restrict_cons_ne hk]
    · by_cases hk : k' = k
      · subst hk
        simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, insideQueries, List.map_cons, splitIn,
          List.map_nil, restrict_cons_self, restrict_nil, Equiv.symm_symm, tensorAllInputs]
      · simp only [Equiv.sigmaAssoc, Equiv.coe_fn_mk, insideQueries, List.map_cons, splitIn,
        List.map_nil, restrict_cons_self, restrict_nil, restrict_cons_ne hk, Equiv.symm_symm,
        tensorAllInputs]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- If `[α_k]_k` admits `z ↦ ⟨k, a⟩` after `h` satisfying the invariant, then `α k` admits
`a` after `h|k`. -/
lemma tensorAll_admits_at (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hadm : Admits (tensorAllRaw α) h z) {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    Admits (α k) (hAt k h) a := by
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, v⟩
  -- Outside query: every component is idle, so `α k` admits any outside label.
  · simp only [tensorAllInputs, Equiv.coe_fn_mk, Sigma.mk.inj_iff] at hz
    obtain ⟨rfl, ha⟩ := hz
    obtain rfl := eq_of_heq ha
    exact (admitAfter_of_ne ((tensorAll_idle hα inv (admitAfter_outer hadm)).1 k')).mpr rfl
  -- Inside reply: `k` is the active component, and `a` answers its open call.
  · simp only [tensorAllInputs, Equiv.coe_fn_mk, Sigma.mk.inj_iff] at hz
    obtain ⟨rfl, ha⟩ := hz
    obtain rfl := eq_of_heq ha
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl; cases hl
    rcases inv.2.2 hne with ⟨o', hl', -⟩ | ⟨k'', j, hl', hj, -⟩
    · rw [hl] at hl'; simp only [Option.some.injEq, Sigma.mk.injEq, reduceCtorEq, false_and] at hl'
    · rw [hl] at hl'
      simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl'
      obtain ⟨rfl, hoj⟩ := hl'
      obtain rfl := eq_of_heq hoj
      unfold Admits
      rw [hj]
      rfl

omit [Fintype K] in
open Classical in
/-- Splitting a transcript `t` of `⨂ₖ α k`, with `t'` the regrouped exchanges: `t` is
admitted and a transcript of `[α_k]_k`; each `t'|k` is a transcript of `α k`; its inputs are
`hAt k` of the joint inputs and its outputs the regrouped joint outputs tagged `k`. -/
lemma replies_tensorAllL_split
    {h : List ((Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l) ×
      (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => V o.1 o.2) (fun j => X j.1 j.2) l))}
    (hr : Replies (tensorAllL α) (h.map Prod.fst) (h.map Prod.snd)) :
    Admitted converterAdmits h ∧ Replies (tensorAllRaw α) (h.map Prod.fst) (h.map Prod.snd) ∧
      (∀ k, Replies (α k)
        ((RandomSystem.restrictExchanges k (h.map (tensorAllInputs.prodCongr
          tensorAllOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.restrictExchanges k (h.map (tensorAllInputs.prodCongr
          tensorAllOutputs.symm))).map
          Prod.snd)) ∧
      (∀ k, (RandomSystem.restrictExchanges k
          (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst =
        hAt k (h.map Prod.fst)) ∧
      (∀ k, (RandomSystem.restrictExchanges k
          (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd =
        restrict k ((h.map Prod.snd).map (tensorAllOutputs (V := V) (X := X)).symm)) := by
  -- `canon` keeps exactly the admitted transcripts of the raw rule, which split by component.
  obtain ⟨hadm, hrr⟩ := (replies_canon_iff _ tensorAllRaw_silentAtEmpty h).mp hr
  obtain ⟨hc, hk⟩ := (replies_tensorAllRaw_iff h).mp hrr
  -- With consistent tags, projecting exchanges and then inputs (outputs) projects them directly.
  have hfst : (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)).map Prod.fst =
      (h.map Prod.fst).map tensorAllInputs := by
    simp only [List.map_map]; rfl
  have hsnd : (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)).map Prod.snd =
      (h.map Prod.snd).map (tensorAllOutputs (V := V) (X := X)).symm := by
    simp only [List.map_map]; rfl
  refine ⟨hadm, hrr, hk, fun k => ?_, fun k => ?_⟩
  · rw [RandomSystem.restrictExchanges_queries hc, hfst]
  · rw [RandomSystem.restrictExchanges_snd hc, hsnd]

end Tensor

/-! ### Domain certificates and PDCs -/

section Converters

variable {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}
  {E : ∀ k, List (Σ j, X k j) → Prop} {F : ∀ k, List (Σ o, U k o) → Prop} {b : K → ℕ}

omit [DecidableEq K] in
open Classical in
/-- **Domain certificate**: if each `α k` is a DDC from `E k` to `F k` with bound `b k`, then
`⨂ₖ α k` is a DDC from `parallelAllInputs E` to `parallelAllInputs F` with bound `max_k b k`.
`parallelAllInputs F h` means `h ≠ []` and every projection `h|k` is `[]` or in `F k`, so each
component keeps its own nonempty input domain, and `⨂ₖ α k` answers `x ↦ ⟨k, a⟩` iff `α k`
answers `a` on its projection. -/
theorem IsDDCFrom.tensorAllL
    {α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)}
    (hα : ∀ k, IsDDCFrom (E k) (F k) (b k) (α k)) :
    IsDDCFrom (parallelAllInputs E) (parallelAllInputs F)
      (Finset.univ.sup b) (SystemAlgebra.tensorAllL α) := by
  -- Project the joint transcript: every component's inside queries remain in its own domain.
  have hraw : SilentAtEmpty (tensorAllRaw α) := tensorAllRaw_silentAtEmpty
  have queries : ∀ h : List ((Σ l : Two (Σ k, O k) (Σ k, J k),
        twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l) ×
      (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => V o.1 o.2) (fun j => X j.1 j.2) l)),
      Replies (SystemAlgebra.tensorAllL α) (h.map Prod.fst) (h.map Prod.snd) →
        insideQueries (h.map Prod.snd) = [] ∨
          parallelAllInputs E (insideQueries (h.map Prod.snd)) := by
    intro h hr
    obtain ⟨-, -, hrk, -, hsk⟩ := replies_tensorAllL_split hr
    by_cases hq : insideQueries (h.map Prod.snd) = []
    · exact Or.inl hq
    · refine Or.inr ⟨hq, fun k => ?_⟩
      rw [insideQueries_at, ← hsk k]
      exact (hα k).queries _ (hrk k)
  -- Answers: after a transcript `h`, `⨂ₖ α k` answers `x` iff `x` is in the joint domain.
  refine ⟨IsDDC.tensorAllL fun k => (hα k).isDDC, fun h x hr => ?_, queries⟩
  obtain ⟨hadm, hrr, hrk, hfk, -⟩ := replies_tensorAllL_split hr
  -- The joint transcript is admissible and answered, so the invariant holds along it.
  have inv := tensorAll_inv_partial (fun k => (hα k).isDDC) (h.map Prod.fst)
    ((hrr.admissible_iff_admitted hraw).mpr hadm) (fun hne => hrr.dom hne)
  -- Converter admission of `x` is admission by the raw rule: both read the last reply label.
  have hjoint : converterAdmits h x → Admits (tensorAllRaw α) (h.map Prod.fst) x := by
    intro hx
    simpa only [Admits, hrr.replyLabel hraw, converterAdmits] using hx
  -- On the transcript tree, `canon` answers `x` iff `x` is admitted and the raw rule answers.
  change (canon (tensorAllRaw α) (h.map Prod.fst ++ [x])).Dom ↔ _
  rw [canon_snoc_dom_iff hraw hadm hrr x]
  have hE := queries h hr
  have hne := fun hx => outsideInputs_ne_nil (x := x) hadm hx
  -- `x ↦ ⟨k, a⟩`: the raw rule answers iff `α k` answers `h|k ++ [a]`; only `h|k` grows.
  rcases e : tensorAllInputs x with ⟨k, a⟩
  rw [tensorAllRaw_snoc e, Part.map_Dom]
  have hself : hAt k (h.map Prod.fst ++ [x]) =
      (RandomSystem.restrictExchanges k
        (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst ++ [a] := by
    rw [hAt_snoc_self e, hfk k]
  have hother : ∀ k', k' ≠ k → hAt k' (h.map Prod.fst ++ [x]) =
      (RandomSystem.restrictExchanges k'
        (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst := fun k' hk' => by
    rw [hAt_snoc_ne e hk', hfk k']
  rw [← hfk k]
  constructor
  -- (→) `α k`'s domain puts `k`'s new projection in `F k`; other projections are unchanged.
  · rintro ⟨hx, hd⟩
    have hz := ((hα k).answers _ a (hrk k)).mp hd
    refine ⟨hadm, hx, ⟨hne hx, fun k' => ?_⟩, hE⟩
    rw [outsideInputs_at]
    by_cases hk' : k' = k
    · subst hk'
      rw [hself]
      exact Or.inr hz.2.2.1
    · rw [hother k' hk']
      exact (hα k').outsideInputs_mem (hrk k')
  -- (←) `a` is admitted by `α k` and `k`'s new projection is in `F k`, so `α k` answers.
  · rintro ⟨-, hx, ⟨-, hFk⟩, -⟩
    refine ⟨hx, ((hα k).answers _ a (hrk k)).mpr ?_⟩
    have hax : converterAdmits (RandomSystem.restrictExchanges k
        (h.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))) a := by
      have hk := tensorAll_admits_at (fun k => (hα k).isDDC) inv (hjoint hx) e
      rwa [Admits, ← hfk k, (hrk k).replyLabel (hα k).isDDC.dds.1] at hk
    have hadmk := (hα k).isDDC.admitted_of_replies (hrk k)
    refine ⟨hadmk, hax, ?_, (hα k).queries _ (hrk k)⟩
    have hFk' := hFk k
    rw [outsideInputs_at, hself] at hFk'
    exact hFk'.resolve_left (outsideInputs_ne_nil hadmk hax)

variable [∀ k, Fintype (O k)] [∀ k, Fintype (J k)] [∀ k o, Fintype (U k o)]
  [∀ k o, Fintype (V k o)] [∀ k j, Fintype (X k j)] [∀ k j, Fintype (Y k j)]

open Classical in
/-- The n-ary parallel composition of PDCs: sample `f` from `piDep (fun k => P k)`, so the
`f k ∼ P k` are independent and each sampled once, and return `⨂ₖ f k` with certificate
`IsDDCFrom.tensorAllL`. As a law, `tensorAllPDC P = (f ↦ ⨂ₖ f k)_* (∏ₖ P k)`. Independence is
the chosen product law. -/
noncomputable def tensorAllPDC
    (P : ∀ k, Distribution.ProbDist {a : InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k) //
      IsDDCFrom (E k) (F k) (b k) a}) :
    Distribution.ProbDist {c : InsideOutsideSystem (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2)
      (fun o => V o.1 o.2) (fun j => X j.1 j.2) (fun j => Y j.1 j.2) //
      IsDDCFrom (parallelAllInputs E) (parallelAllInputs F)
        (Finset.univ.sup b) c} :=
  ⟨Distribution.fTransform
      (fun f => ⟨tensorAllL fun k => (f k).1, IsDDCFrom.tensorAllL fun k => (f k).2⟩)
      (Distribution.piDep fun k => (P k).1),
    Distribution.fTransform_isProbDist _
      (Distribution.piDep_isProbDist fun k => (P k).2)⟩

omit [∀ k, Fintype (O k)] [∀ k, Fintype (J k)] [∀ k o, Fintype (U k o)]
  [∀ k o, Fintype (V k o)] [∀ k j, Fintype (X k j)] [∀ k j, Fintype (Y k j)] in
open Classical in
/-- **The rectangular mass of `tensorAllPDC`.** With `t' = t.map (tensorAllInputs ×
tensorAllOutputs⁻¹)` the regrouped transcript and `t'|k` its exchanges tagged `k`,

  `Pr_{tensorAllPDC P}[Replies · t] = ∏ k, Pr_{P k}[Replies · t'|k]`

if `t` is admitted and `t'` tag-consistent, and `0` otherwise: the event
`{f | Replies (⨂ₖ f k) t}` is then the rectangle `{f | ∀ k, Replies (f k) t'|k}`
(`piDep_mass_forall`). Stated for arbitrary presentations `P k`; `tensorAll_apply` and
`tensorAll_presents` both instantiate it. -/
lemma behaviorMass_tensorAllPDC
    (P : ∀ k, Distribution.ProbDist {a : InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k) //
      IsDDCFrom (E k) (F k) (b k) a})
    (t : List ((Σ l, twoFam (fun o : Σ k, O k => U o.1 o.2)
      (fun j : Σ k, J k => Y j.1 j.2) l) ×
      (Σ l, twoFam (fun o : Σ k, O k => V o.1 o.2)
        (fun j : Σ k, J k => X j.1 j.2) l))) :
    behaviorMass (tensorAllPDC P).1 (t.map Prod.fst) (t.map Prod.snd) =
      if Admitted converterAdmits t ∧
          RandomSystem.parallelAllConsistent
            (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)) then
        ∏ k, behaviorMass (P k).1
          ((RandomSystem.restrictExchanges k
            (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst)
          ((RandomSystem.restrictExchanges k
            (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd)
      else 0 := by
  -- `Replies (⨂ₖ f k) t` iff `t` is admitted, `t'` tag-consistent and every `f k` replies
  -- `t'|k`; the left side is the `piDep P` mass of that event.
  unfold behaviorMass tensorAllPDC
  rw [Distribution.mass_fTransform]
  simp only [tensorAllL, replies_canon_iff _ tensorAllRaw_silentAtEmpty,
    replies_tensorAllRaw_iff]
  split_ifs with hc
  · -- Admitted and consistent: the event is the rectangle `{f | ∀ k, Replies (f k) t'|k}`,
    -- whose `piDep` mass is the product of the component masses.
    rw [Distribution.mass_congr _ fun f => ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩]
    exact Distribution.piDep_mass_forall (fun k => (P k).1) (fun k s => Replies s.1
      ((RandomSystem.restrictExchanges k
        (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst)
      ((RandomSystem.restrictExchanges k
        (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd))
  -- Otherwise no sample replies `t`: the mass is `0`.
  · exact Distribution.mass_eq_zero_of_forall_not _ fun _ hf => hc ⟨hf.1, hf.2.1⟩

variable {m n : K → ℕ} {hE : ∀ k h, E k h → h.length ≤ m k} {hF : ∀ k h, F k h → h.length ≤ n k}

open Classical in
/-- **n-ary parallel composition of PDC behaviors**: choose a presentation `P k` of each
`α k` and return the behavior of `tensorAllPDC P`. The domains are `parallelAllInputs E` and
`parallelAllInputs F`, with length bounds `∑ k, m k` and `∑ k, n k`, since the lengths of the
projections of an interleaved history add up. -/
noncomputable def PDCBehavior.tensorAll
    (α : ∀ k, PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k) (m k) (hE k) (F k) (n k) (hF
      k)) :
    PDCBehavior (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2)
      (parallelAllInputs E) (∑ k, m k) (parallelAllInputs_length_le hE)
      (parallelAllInputs F) (∑ k, n k) (parallelAllInputs_length_le hF) :=
  PDCBehavior.ofPDC (tensorAllPDC fun k => (α k).2.choose_spec.choose)

open Classical in
/-- **The product formula for `tensorAll`.** With `t' = t.map (tensorAllInputs.prodCongr
tensorAllOutputs.symm)` the regrouped transcript and `t'|k` its exchanges tagged `k`,

  `(tensorAll α)(t) = ∏ k, α_k(t'|k)` if `Admitted converterAdmits t` and every exchange of
  `t'` has equal input and output tags, and `(tensorAll α)(t) = 0` otherwise.

The right side involves only the behaviors `α_k`, so `tensorAll` does not depend on the chosen
presentations. -/
theorem PDCBehavior.tensorAll_apply
    (α : ∀ k, PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k)
      (E k) (m k) (hE k) (F k) (n k) (hF k))
    (t : List ((Σ l : Two (Σ k, O k) (Σ k, J k),
      twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l) ×
      (Σ l : Two (Σ k, O k) (Σ k, J k),
        twoFam (fun o => V o.1 o.2) (fun j => X j.1 j.2) l))) :
    (PDCBehavior.tensorAll α).1 t =
      if Admitted converterAdmits t ∧
          RandomSystem.parallelAllConsistent
            (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)) then
        ∏ k, (α k).1 (RandomSystem.restrictExchanges k
          (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm)))
      else 0 := by
  -- `behaviorMass_tensorAllPDC` at the chosen presentations, each factor of mass `α_k(t'|k)`.
  change behaviorMass (tensorAllPDC fun k => (α k).2.choose_spec.choose).1
    (t.map Prod.fst) (t.map Prod.snd) = _
  simp only [behaviorMass_tensorAllPDC, fun k => (α k).2.choose_spec.choose_spec]

omit [DecidableEq K] in
open Classical in
/-- Any presentations `P k` of the `α k` present `tensorAll α`:
`(tensorAll α)(t) = Pr_{tensorAllPDC P}[Replies · t]`. Both sides factor by
`behaviorMass_tensorAllPDC` into `∏ k, α_k(t'|k)` on admitted, tag-consistent `t`. -/
lemma PDCBehavior.tensorAll_presents
    (α : ∀ k, PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k)
      (E k) (m k) (hE k) (F k) (n k) (hF k))
    (P : ∀ k, Distribution.ProbDist {a : InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k) //
      IsDDCFrom (E k) (F k) (b k) a})
    (hP : ∀ k h, behaviorMass (P k).1 (h.map Prod.fst) (h.map Prod.snd) = (α k).1 h)
    (t : List ((Σ l, twoFam (fun o : Σ k, O k => U o.1 o.2)
      (fun j : Σ k, J k => Y j.1 j.2) l) ×
      (Σ l, twoFam (fun o : Σ k, O k => V o.1 o.2)
        (fun j : Σ k, J k => X j.1 j.2) l))) :
    (PDCBehavior.tensorAll α).1 t =
      behaviorMass (tensorAllPDC P).1 (t.map Prod.fst) (t.map Prod.snd) := by
  -- Both sides factor into the same component behaviors on every admitted, consistent trace.
  rw [PDCBehavior.tensorAll_apply, behaviorMass_tensorAllPDC]
  simp only [hP]

omit [DecidableEq K] in
open Classical in
/-- **The n-ary parallel composition of DDC behaviors is the behavior of `⨂ₖ a k`**: for every
transcript `t`, `(tensorAll (ofDDC a))(t) = 1[t is a transcript of ⨂ₖ a k]`. This is behavior
equality: by `tensorAll_apply` only the behaviors `1[· is a transcript of a k]` enter, whether
or not the chosen presentations of `ofDDC (a k)` are point masses. -/
lemma PDCBehavior.tensorAll_ofDDC
    {a : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)}
    (ha : ∀ k, IsDDCFrom (E k) (F k) (b k) (a k)) :
    PDCBehavior.tensorAll (fun k => (PDCBehavior.ofDDC (a k) (ha k) :
      PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k) (m k) (hE k) (F k) (n k) (hF k))) =
      PDCBehavior.ofDDC (tensorAllL a) (IsDDCFrom.tensorAllL ha) := by
  -- Compare masses at each transcript `t`.
  apply PDCBehavior.ext
  intro t
  -- Left: `tensorAll_apply` with `(ofDDC (a k))(t'|k) = 1[Replies (a k) t'|k]`; the product
  -- of indicators is `1[∀ k, Replies (a k) t'|k]`. Right: `1[Replies (⨂ₖ a k) t]`.
  rw [PDCBehavior.tensorAll_apply, PDCBehavior.ofDDC_apply]
  simp only [PDCBehavior.ofDDC_apply, Finset.prod_boole, Finset.mem_univ, true_implies]
  -- `Replies (⨂ₖ a k) t` is the same event: admitted, tag-consistent, components reply.
  rw [tensorAllL, replies_canon_iff _ tensorAllRaw_silentAtEmpty t, replies_tensorAllRaw_iff]
  -- Merge the nested indicators; both sides then test one proposition.
  simp only [← ite_and, and_assoc]
  split_ifs <;> rfl

end Converters

end SystemAlgebra

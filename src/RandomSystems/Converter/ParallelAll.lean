import Probability.DependentProduct
import RandomSystems.Cumulative.ParallelAll
import RandomSystems.Converter.ConverterTensor
import RandomSystems.Converter.ConverterAttachment

/-!
# Finite parallel canonical converters

Each component converter receives only its projected tagged history. The joint raw history
rule is canonicalized before it becomes a DDC. The direct domain certificate preserves
component input domains; the consecutive inside-query bound is the maximum of the component
bounds, including zero for the empty family. Independent converter laws are sampled with
`Distribution.piDep`.

Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be
viewed as a single one.” This tagged converter construction gives the corresponding finite
parallel wiring; it does not equate raw off-tree converter functions.

## Main definitions

* `tensorAllL`: the canonical n-ary direct converter
* `tensorAllPDC`, `PDCBehavior.tensorAll`: independently sampled n-ary converter laws

## Main results

* `IsDDC.tensorAllL`: a family of direct converters has the maximum consecutive bound
* `IsDDCFrom.tensorAllL`: component domain certificates give a joint certificate
* `PDCBehavior.tensorAll_ofDDC`: direct converters embed in stochastic composition
-/

namespace SystemAlgebra

open Probability
open scoped NNReal ENNReal

variable {K : Type} [Fintype K] [DecidableEq K]

section Tensor

variable {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}

open Classical in
/-- Joint converter inputs, split by component: an outside input at `⟨k, o⟩` and an inside
reply at `⟨k, j⟩` both go to component `k`. -/
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
/-- Joint converter outputs, from the components. -/
abbrev tensorAllOutputs := (tensorAllInputs (U := V) (Y := X)).symm

open Classical in
/-- `[α_k]_k` on the joint labels: the raw n-ary parallel converter. -/
noncomputable def tensorAllRaw (α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)) :
    InsideOutsideSystem (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2) :=
  relabel (parAll α) tensorAllInputs tensorAllOutputs

open Classical in
/-- **The n-ary parallel converter** `⨂ₖ α k`: `[α_k]_k` restricted to its admissible
histories. Jost, Thesis, printed p. 17: “A finite set of resources with disjoint interface
sets can be viewed as a single one.” Canonicalization supplies the needed off-tree values. -/
noncomputable def tensorAllL (α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)) :
    InsideOutsideSystem (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2) :=
  canon (tensorAllRaw α)

open Classical in
/-- The joint label of a component's label. -/
def labAt (k : K) : Two (O k) (J k) → Two (Σ k, O k) (Σ k, J k)
  | ⟨none, o⟩ => ⟨none, ⟨k, o⟩⟩
  | ⟨some (), j⟩ => ⟨some (), ⟨k, j⟩⟩

open Classical in
/-- The input history of component `k`. -/
noncomputable abbrev hAt (k : K)
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    List (Σ l : Two (O k) (J k), twoFam (U k) (Y k) l) :=
  restrict k (h.map tensorAllInputs)

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma tensorAllOutputs_fst (k : K) (y : Σ l : Two (O k) (J k), twoFam (V k) (X k) l) :
    (tensorAllOutputs (V := V) (X := X) ⟨k, y⟩).1 = labAt k y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma isInside_tensorAllOutputs (k : K) (y : Σ l : Two (O k) (J k), twoFam (V k) (X k) l) :
    IsInside (tensorAllOutputs (V := V) (X := X) ⟨k, y⟩) ↔ IsInside y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> simp [IsInside, tensorAllOutputs, tensorAllInputs]

variable {α : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)}
  {h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l)}
  {z : Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2) l}

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    tensorAllRaw α (h ++ [z]) =
      (α k (hAt k h ++ [a])).map (fun y => tensorAllOutputs (V := V) (X := X) ⟨k, y⟩) := by
  simp only [tensorAllRaw, relabel, List.map_append, List.map_singleton, hz, parAll_snoc,
    Part.map_map]
  rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma hAt_snoc_self {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    hAt k (h ++ [z]) = hAt k h ++ [a] := by
  simp only [hAt, List.map_append, List.map_singleton, hz, restrict_append, restrict_cons_self,
    restrict_nil]

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma hAt_snoc_ne {k k' : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) (hk : k' ≠ k) :
    hAt k' (h ++ [z]) = hAt k' h := by
  simp only [hAt, List.map_append, List.map_singleton, hz, restrict_append,
    restrict_cons_ne (Ne.symm hk), restrict_nil, List.append_nil]

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma replyLabel_tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    replyLabel (tensorAllRaw α) (h ++ [z]) = (replyLabel (α k) (hAt k h ++ [a])).map (labAt k) := by
  unfold replyLabel
  rw [tensorAllRaw_snoc hz]
  by_cases hd : (α k (hAt k h ++ [a])).Dom
  · rw [dif_pos hd, dif_pos (by simpa using hd)]
    exact congrArg some (tensorAllOutputs_fst _ _)
  · rw [dif_neg hd, dif_neg (by simpa using hd)]
    rfl

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma insideRun_tensorAllRaw_snoc {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    insideRun (tensorAllRaw α) (h ++ [z]) =
      if ∃ y ∈ α k (hAt k h ++ [a]), IsInside y then insideRun (tensorAllRaw α) h + 1 else 0 := by
  rw [insideRun, run_snoc, tensorAllRaw_snoc hz]
  congr 1
  simp only [Part.mem_map_iff]
  exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_tensorAllOutputs k y).mp hi⟩,
    fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_tensorAllOutputs k y).mpr hi⟩⟩

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma replyLabel_tensorAllRaw_nil : replyLabel (tensorAllRaw α) [] = none := by
  simp [replyLabel, tensorAllRaw, relabel, parAll]

variable (α) in
open Classical in
/-- Component `k` has no open inside call after `h`. -/
def IdleAt (k : K)
    (h : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    Prop :=
  ∀ j, replyLabel (α k) (hAt k h) ≠ some ⟨some (), j⟩

variable (α) in
open Classical in
/-- The state of `[α_k]_k` after `h`: every component idle, or exactly one with an open
inside call, which is the last reply. -/
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
/-- The invariant of `[α_k]_k` on admissible histories. -/
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
lemma tpostAll (hα : ∀ k, IsDDC (b k) (α k)) {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩)
    (hcomp : ∀ k, Admissible (α k) (hAt k h) ∧ (hAt k h ≠ [] → (α k (hAt k h)).Dom))
    (hadm : Admits (α k) (hAt k h) a) (hid : ∀ k', k' ≠ k → IdleAt α k' h)
    (hlo : lastOuter (h ++ [z]) = (lastOuter (hAt k h ++ [a])).map (Sigma.mk k))
    (hrun : insideRun (tensorAllRaw α) h ≤ insideRun (α k) (hAt k h))
    (hnext : Admissible (α k) (hAt k h ++ [a]) → (α k (hAt k h ++ [a])).Dom) :
    TInvAll α (h ++ [z]) := by
  have ha' : Admissible (α k) (hAt k h ++ [a]) :=
    admissible_snoc.mpr ⟨(hcomp k).1, (hcomp k).2, hadm⟩
  have hd' : (α k (hAt k h ++ [a])).Dom := hnext ha'
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd'
  have hdRaw : (tensorAllRaw α (h ++ [z])).Dom := by rw [tensorAllRaw_snoc hz]; exact hd'
  have hl' : replyLabel (tensorAllRaw α) (h ++ [z]) = some (labAt k y.1) := by
    rw [replyLabel_tensorAllRaw_snoc hz, replyLabel_of_mem (α k) hy]; rfl
  have hid' : ∀ k', k' ≠ k → IdleAt α k' (h ++ [z]) := fun k' hk' => by
    unfold IdleAt
    rw [hAt_snoc_ne hz hk']
    exact hid k' hk'
  refine ⟨fun _ => hdRaw, fun k' => ?_, fun _ => ?_⟩
  · by_cases hk' : k' = k
    · subst hk'
      rw [hAt_snoc_self hz]
      exact ⟨ha', fun _ => hd'⟩
    · rw [hAt_snoc_ne hz hk']
      exact hcomp k'
  · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    · refine Or.inl ⟨⟨k, l⟩, hl', ?_, fun k' => ?_⟩
      · rw [hlo, (hα k).replies _ _ l hy rfl]; rfl
      · by_cases hk' : k' = k
        · subst hk'
          intro j hj
          rw [hAt_snoc_self hz, replyLabel_of_mem _ hy] at hj
          simp at hj
        · exact hid' k' hk'
    · refine Or.inr ⟨k, l, hl', by rw [hAt_snoc_self hz]; exact replyLabel_of_mem (α k) hy, hid',
        by rw [hAt_snoc_self hz]; exact hlo, ?_⟩
      rw [insideRun_tensorAllRaw_snoc hz, if_pos ⟨_, hy, rfl⟩, hAt_snoc_self hz,
        insideRun_snoc_eq, if_pos ⟨_, hy, rfl⟩]
      omega

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- Before an outside input, every component is idle and no inside call is open. -/
lemma tensorAll_idle (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hn : ∀ j, replyLabel (tensorAllRaw α) h ≠ some ⟨some (), j⟩) :
    (∀ k, IdleAt α k h) ∧ insideRun (tensorAllRaw α) h = 0 := by
  rcases eq_or_ne h [] with rfl | hne
  · refine ⟨fun k j hj => ?_, rfl⟩
    simp only [hAt, List.map_nil, restrict_nil, replyLabel_nil_conv (hα k)] at hj
    cases hj
  · rcases inv.2.2 hne with ⟨o, hl, -, hid⟩ | ⟨k, j, hl, -⟩
    · exact ⟨hid, insideRun_eq_zero_of_outer hl⟩
    · exact absurd hl (hn _)

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma tensorAll_step (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hadm : Admits (tensorAllRaw α) h z)
    (hn : ∀ k a, tensorAllInputs z = ⟨k, a⟩ → Admissible (α k) (hAt k h ++ [a]) →
      (α k (hAt k h ++ [a])).Dom) :
    TInvAll α (h ++ [z]) := by
  obtain ⟨hd, hcomp, hcase⟩ := inv
  have inv : TInvAll α h := ⟨hd, hcomp, hcase⟩
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k, o⟩⟩, v⟩
  · -- an outside input to component `k`
    obtain ⟨hid, hr0⟩ := tensorAll_idle hα inv (admitAfter_outer hadm)
    refine tpostAll hα rfl hcomp ?_ (fun k' _ => hid k') ?_
      (by rw [hr0]; exact Nat.zero_le _) (hn _ _ rfl)
    · exact (admitAfter_of_ne (hid k)).mpr rfl
    · rw [lastOuter_snoc, lastOuter_snoc]; rfl
  · -- an inside reply to component `k`
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl; cases hl
    rcases hcase hne with ⟨o', hl', -⟩ | ⟨k', j, hl', hj, hid, hlo, hrun⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl'
      obtain ⟨rfl, hoj⟩ := hl'
      obtain rfl := eq_of_heq hoj
      refine tpostAll hα rfl hcomp ?_ hid ?_ hrun (hn _ _ rfl)
      · unfold Admits
        rw [hj]
        rfl
      · rw [lastOuter_snoc, lastOuter_snoc]
        simpa [outerOf] using hlo

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma tInvAll_nil : TInvAll α [] :=
  ⟨fun h => absurd rfl h, fun _ => ⟨by simp [hAt], fun h => absurd (by simp [hAt]) h⟩,
    fun h => absurd rfl h⟩

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The invariant holds on every admissible history at which `[α_k]_k` is defined on all
nonempty prefixes. No component need answer every legal input. -/
lemma tensorAll_inv_partial (hα : ∀ k, IsDDC (b k) (α k)) :
    ∀ h, Admissible (tensorAllRaw α) h → (h ≠ [] → (tensorAllRaw α h).Dom) → TInvAll α h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; exact tInvAll_nil
  | append_singleton h z ih =>
    intro ha hd
    obtain ⟨ha₀, hd₀, hz⟩ := admissible_snoc.mp ha
    have hd' := hd (by simp)
    refine tensorAll_step hα (ih ha₀ hd₀) hz fun k a e _ => ?_
    rw [tensorAllRaw_snoc e] at hd'
    exact hd'

omit [DecidableEq K] in
open Classical in
/-- **`⨂ₖ α k` is a partial converter**, with the largest of the bounds. -/
lemma IsDDC.tensorAllL (hα : ∀ k, IsDDC (b k) (α k)) :
    IsDDC (Finset.univ.sup b) (tensorAllL α) := by
  -- Canonicalization supplies the off-tree behavior; check the raw rule on admitted histories.
  refine canon_isDDC ?_ ?_ ?_
  · simp [tensorAllRaw, relabel, parAll]
  · intro h ha hd
    -- At most one component is active, so its run is bounded by the largest component bound.
    rcases eq_or_ne h [] with rfl | hne
    · exact Nat.zero_le _
    rcases (tensorAll_inv_partial hα h ha (fun _ => hd)).2.2 hne with ⟨o, hl, -⟩ |
        ⟨k, j, -, hj, -, -, hrun⟩
    · rw [insideRun_eq_zero_of_outer hl]; exact Nat.zero_le _
    · have hdk : (α k (hAt k h)).Dom := by
        by_contra hn; simp [replyLabel, hn] at hj
      exact hrun.trans (((hα k).bound _ hdk).trans (Finset.le_sup (Finset.mem_univ k)))
  · intro h y o ha hy hl
    -- An outside reply carries the label of the last outside query, not another component's.
    have hl' := replyLabel_of_mem _ hy
    rw [hl] at hl'
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl'; cases hl'
    rcases (tensorAll_inv_partial hα h ha (fun _ => Part.dom_iff_mem.mpr ⟨y, hy⟩)).2.2 hne
      with ⟨o', hl'', hlo, -⟩ | ⟨k, j, hl'', -⟩
    · rw [hl'] at hl''
      obtain rfl : o = o' := by simpa using hl''
      exact hlo
    · rw [hl'] at hl''; simp at hl''

omit [Fintype K] [DecidableEq K] in
open Classical in
lemma tensorAllRaw_silentAtEmpty : SilentAtEmpty (tensorAllRaw α) := by
  simp [SilentAtEmpty, tensorAllRaw, relabel, parAll]

omit [Fintype K] in
open Classical in
/-- The transcripts of `[α_k]_k` are the interleavings of the components' transcripts. -/
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
/-- The outside inputs of component `k` are the joint outside inputs restricted to `k`. -/
lemma outsideInputs_at (k : K)
    (xs : List (Σ l : Two (Σ k, O k) (Σ k, J k), twoFam (fun o => U o.1 o.2) (fun j => Y j.1 j.2)
      l)) :
    restrict k ((outsideInputs xs).map (Equiv.sigmaAssoc U)) = outsideInputs (hAt k xs) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [outsideInputs_append, List.map_append, restrict_append, ih, hAt]
    congr 1
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, u⟩
    · by_cases hk : k' = k
      · subst hk
        simp [outsideInputs, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_self]
      · simp [outsideInputs, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_ne hk]
    · by_cases hk : k' = k
      · subst hk
        simp [outsideInputs, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_self]
      · simp [outsideInputs, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_ne hk]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The inside queries of component `k` are the joint inside queries restricted to `k`. -/
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
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, v⟩
    · by_cases hk : k' = k
      · subst hk
        simp [insideQueries, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_self]
      · simp [insideQueries, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_ne hk]
    · by_cases hk : k' = k
      · subst hk
        simp [insideQueries, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_self]
      · simp [insideQueries, splitIn, tensorAllInputs, Equiv.sigmaAssoc, restrict_cons_ne hk]

omit [Fintype K] [DecidableEq K] in
open Classical in
/-- The component answering the next input is admitting it. -/
lemma tensorAll_admits_at (hα : ∀ k, IsDDC (b k) (α k)) (inv : TInvAll α h)
    (hadm : Admits (tensorAllRaw α) h z) {k : K} {a} (hz : tensorAllInputs z = ⟨k, a⟩) :
    Admits (α k) (hAt k h) a := by
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨k', o⟩⟩, v⟩
  · simp only [tensorAllInputs, Equiv.coe_fn_mk, Sigma.mk.inj_iff] at hz
    obtain ⟨rfl, ha⟩ := hz
    obtain rfl := eq_of_heq ha
    exact (admitAfter_of_ne ((tensorAll_idle hα inv (admitAfter_outer hadm)).1 k')).mpr rfl
  · simp only [tensorAllInputs, Equiv.coe_fn_mk, Sigma.mk.inj_iff] at hz
    obtain ⟨rfl, ha⟩ := hz
    obtain rfl := eq_of_heq ha
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorAllRaw_nil] at hl; cases hl
    rcases inv.2.2 hne with ⟨o', hl', -⟩ | ⟨k'', j, hl', hj, -⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      simp only [Option.some.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl'
      obtain ⟨rfl, hoj⟩ := hl'
      obtain rfl := eq_of_heq hoj
      unfold Admits
      rw [hj]
      rfl

omit [Fintype K] in
open Classical in
/-- The components of a joint transcript of `⨂ₖ α k`. -/
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
  obtain ⟨hadm, hrr⟩ := (replies_canon_iff _ tensorAllRaw_silentAtEmpty h).mp hr
  obtain ⟨hc, hk⟩ := (replies_tensorAllRaw_iff h).mp hrr
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

/-! ## Converters from domains to domains, PDCs and arrows -/

section Converters

variable {O J : K → Type} {U V : ∀ k, O k → Type} {X Y : ∀ k, J k → Type}
  {E : ∀ k, List (Σ j, X k j) → Prop} {F : ∀ k, List (Σ o, U k o) → Prop} {b : K → ℕ}

omit [DecidableEq K] in
open Classical in
/-- `⨂ₖ α k` is a DDC from the n-ary inside domain to the n-ary outside domain, with the
largest of the components' bounds. -/
lemma IsDDCFrom.tensorAllL
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
  refine ⟨IsDDC.tensorAllL fun k => (hα k).isDDC, fun h x hr => ?_, queries⟩
  obtain ⟨hadm, hrr, hrk, hfk, -⟩ := replies_tensorAllL_split hr
  have inv := tensorAll_inv_partial (fun k => (hα k).isDDC) (h.map Prod.fst)
    ((hrr.admissible_iff_admitted hraw).mpr hadm) (fun hne => hrr.dom hne)
  have hjoint : converterAdmits h x → Admits (tensorAllRaw α) (h.map Prod.fst) x := by
    intro hx
    simpa only [Admits, hrr.replyLabel hraw, converterAdmits] using hx
  change (canon (tensorAllRaw α) (h.map Prod.fst ++ [x])).Dom ↔ _
  rw [canon_snoc_dom_iff hraw hadm hrr x]
  have hE := queries h hr
  have hne := fun hx => outsideInputs_ne_nil (x := x) hadm hx
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
/-- The n-ary parallel composition of PDCs: independent samples, side by side. Jost,
Thesis, printed p. 17: “A finite set of resources with disjoint interface sets can be viewed
as a single one.” Independent sampling is the chosen stochastic product law. -/
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

variable {m n : K → ℕ} {hE : ∀ k h, E k h → h.length ≤ m k} {hF : ∀ k h, F k h → h.length ≤ n k}

open Classical in
/-- **n-ary parallel composition of PDC behaviors**: the PDCs are sampled independently
and run side by side on disjoint interfaces. Jost, Thesis, printed p. 17, regards a finite
set of disjoint-interface resources as one; this defines its converter-side product. -/
noncomputable def PDCBehavior.tensorAll
    (α : ∀ k, PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k) (m k) (hE k) (F k) (n k) (hF
      k)) :
    PDCBehavior (Σ k, O k) (Σ k, J k) (fun o => U o.1 o.2) (fun o => V o.1 o.2)
      (fun j => X j.1 j.2) (fun j => Y j.1 j.2)
      (parallelAllInputs E) (∑ k, m k) (parallelAllInputs_length_le hE)
      (parallelAllInputs F) (∑ k, n k) (parallelAllInputs_length_le hF) :=
  PDCBehavior.ofPDC (tensorAllPDC fun k => (α k).2.choose_spec.choose)

open Classical in
/-- **The n-ary parallel composition of DDCs** as behaviors is the behavior of their n-ary
parallel composition. -/
lemma PDCBehavior.tensorAll_ofDDC
    {a : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k)}
    (ha : ∀ k, IsDDCFrom (E k) (F k) (b k) (a k)) :
    PDCBehavior.tensorAll (fun k => (PDCBehavior.ofDDC (a k) (ha k) :
      PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k) (m k) (hE k) (F k) (n k) (hF k))) =
      PDCBehavior.ofDDC (tensorAllL a) (IsDDCFrom.tensorAllL ha) := by
  apply PDCBehavior.ext
  intro t
  rw [PDCBehavior.ofDDC_apply]
  set P := fun k => (PDCBehavior.ofDDC (a k) (ha k) :
    PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k) (m k) (hE k) (F k) (n k) (hF
      k)).2.choose_spec.choose
  have hP : ∀ k (T : List ((Σ l, twoFam (U k) (Y k) l) × (Σ l, twoFam (V k) (X k) l))),
      behaviorMass (P k).1 (T.map Prod.fst) (T.map Prod.snd) =
      if Replies (a k) (T.map Prod.fst) (T.map Prod.snd) then 1 else 0 := fun k T => by
    rw [(PDCBehavior.ofDDC (a k) (ha k) : PDCBehavior (O k) (J k) (U k) (V k) (X k) (Y k) (E k)
      (m k) (hE k) (F k) (n k) (hF k)).2.choose_spec.choose_spec T, PDCBehavior.ofDDC_apply]
  have key : ∀ c : ∀ k, InsideOutsideSystem (O k) (J k) (U k) (V k) (X k) (Y k),
      Replies (tensorAllL c) (t.map Prod.fst) (t.map Prod.snd) ↔
        Admitted converterAdmits t ∧
          (RandomSystem.parallelAllConsistent (t.map (tensorAllInputs.prodCongr
            tensorAllOutputs.symm)) ∧
          ∀ k, Replies (c k)
            ((RandomSystem.restrictExchanges k
              (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst)
            ((RandomSystem.restrictExchanges k
              (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd)) :=
    fun c => by rw [tensorAllL, replies_canon_iff _ tensorAllRaw_silentAtEmpty t,
      replies_tensorAllRaw_iff]
  change behaviorMass (tensorAllPDC P).1 (t.map Prod.fst) (t.map Prod.snd) = _
  unfold behaviorMass tensorAllPDC
  rw [Distribution.mass_fTransform]
  simp only [key]
  by_cases hc : Admitted converterAdmits t ∧
      RandomSystem.parallelAllConsistent (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))
  · rw [Distribution.mass_congr _ fun f => ⟨fun h => h.2.2, fun h => ⟨hc.1, hc.2, h⟩⟩,
      Distribution.piDep_mass_forall (fun k => (P k).1) (fun k s => Replies s.1
        ((RandomSystem.restrictExchanges k
          (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst)
        ((RandomSystem.restrictExchanges k
          (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd))]
    have hP' : ∀ k (T : List ((Σ l, twoFam (U k) (Y k) l) × (Σ l, twoFam (V k) (X k) l))),
        (P k).1.mass (fun s => Replies s.1 (T.map Prod.fst) (T.map Prod.snd)) =
          if Replies (a k) (T.map Prod.fst) (T.map Prod.snd) then 1 else 0 := hP
    simp only [hP', Finset.prod_boole, Finset.mem_univ, true_implies]
    by_cases hr : ∀ k, Replies (a k)
        ((RandomSystem.restrictExchanges k
          (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.fst)
        ((RandomSystem.restrictExchanges k
          (t.map (tensorAllInputs.prodCongr tensorAllOutputs.symm))).map Prod.snd)
    · rw [if_pos hr, if_pos ⟨hc.1, hc.2, hr⟩]
    · rw [if_neg hr, if_neg fun h => hr h.2.2]
  · rw [Distribution.mass_eq_zero_of_forall_not _ fun f hf => hc ⟨hf.1, hf.2.1⟩,
      if_neg fun h => hc ⟨h.1, h.2.1⟩]

end Converters



end SystemAlgebra

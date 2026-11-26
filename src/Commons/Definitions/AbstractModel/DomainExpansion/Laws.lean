module

public import Commons.Definitions.AbstractModel.DomainExpansion
public import Commons.Definitions.AbstractModel.Registers.Laws
public import Probability.List

/-!
# Admission under command expansion

`admitted_iff_forallScan` presents existing admission as a scan and an ordinary-command bound.
`Admitted.flatMap` transports that scan through locally legal command blocks and adds their
ordinary costs. A terminal submission remains outside the ordinary-command allowance.
-/

@[expose] public section

namespace Commons.AbstractModel

variable
    -- `S`, `T` carry submitted values; `P`, `Q` carry model parameters; `ι` names registers.
    {S P T Q ι : Type} [DecidableEq ι]
    -- `M`, `N` are source and target models; only their register names are shared.
    (M : AbstractModel S P) (N : AbstractModel T Q)

/-- The fold accumulates all written addresses and whether every command was ordinary. -/
lemma admissionUpdate_fold (state : Finset ι × Bool) (h : List (M.Command ι)) :
    h.foldl M.admissionUpdate state =
      (state.1 ∪ (h.filterMap M.target).toFinset, state.2 && h.all M.ordinary) := by
  induction h using List.reverseRecOn with
  | nil => simp only [List.foldl_nil, List.filterMap_nil, List.toFinset_nil,
      Finset.union_empty, List.all_nil, Bool.and_true, Prod.eta]
  | append_singleton h z ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    cases target : M.target z <;>
      simp only [admissionUpdate, target, Option.elim_none, Option.elim_some,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
        List.toFinset_append, List.toFinset_nil, List.toFinset_cons, Finset.union_empty,
        Finset.union_insert, List.all_append, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_assoc]

/-- Starting at the input address gives the existing initialized-address set and stop flag. -/
lemma admissionUpdate_fold_initial (input : ι) (h : List (M.Command ι)) :
    h.foldl M.admissionUpdate ({input}, true) = (M.initialized input h, h.all M.ordinary) := by
  simpa only [initialized, Finset.singleton_union, Bool.true_and] using
    M.admissionUpdate_fold ({input}, true) h

/-- Admission is nonemptiness, the ordinary allowance, and the initialized-read/terminal scan. -/
lemma admitted_iff_forallScan (input : ι) (k : ℕ) (h : List (M.Command ι)) :
    M.Admitted input k h ↔ h ≠ [] ∧ h.countP M.ordinary ≤ k ∧
      List.ForallScan M.admissionUpdate M.admissionAllowed ({input}, true) h := by
  induction h using List.reverseRecOn with
  | nil => simp only [Admitted, ne_eq, not_true_eq_false, false_and]
  | append_singleton h z ih =>
    rw [admitted_snoc_iff, List.forallScan_append_iff, M.admissionUpdate_fold_initial]
    simp only [List.ForallScan, admissionAllowed, and_true]
    have priorCount : h.countP M.ordinary ≤ (h ++ [z]).countP M.ordinary := by
      rw [List.countP_append]
      exact Nat.le_add_right _ _
    constructor
    · rintro ⟨prior, count, ordinary, reads⟩
      refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), count,
        ?_, List.all_eq_true.mpr ordinary, reads⟩
      rcases prior with rfl | prior
      · trivial
      · exact (ih.mp prior).2.2
    · rintro ⟨_, count, scan, ordinary, reads⟩
      refine ⟨?_, count, List.all_eq_true.mp ordinary, reads⟩
      by_cases empty : h = []
      · exact Or.inl empty
      · exact Or.inr (ih.mpr ⟨empty, priorCount.trans count, scan⟩)

/-- Each expanded block preserves the source command's destination and terminal update. -/
lemma admissionUpdate_expansion
    (expand : M.Command ι → List (N.Command ι))
    (targets : ∀ z, (expand z).filterMap N.target = (M.target z).toList)
    (ordinary : ∀ z, (expand z).all N.ordinary = M.ordinary z)
    (state : Finset ι × Bool) (z : M.Command ι) :
    (expand z).foldl N.admissionUpdate state = M.admissionUpdate state z := by
  rw [N.admissionUpdate_fold, targets, ordinary]
  cases target : M.target z <;>
    simp only [admissionUpdate, target, Option.toList_none, Option.toList_some,
      Option.elim_none, Option.elim_some, List.toFinset_nil, List.toFinset_cons,
      Finset.union_empty, Finset.union_insert]

/-- A block reads only admitted source operands and stops, if at all, at its final command. -/
lemma admissionAllowed_expansion
    (expand : M.Command ι → List (N.Command ι))
    (reads : ∀ z u, u ∈ expand z → N.reads u ⊆ M.reads z)
    (terminal : ∀ z u, u ∈ (expand z).dropLast → N.ordinary u = true)
    (state : Finset ι × Bool) (z : M.Command ι) (allowed : M.admissionAllowed state z) :
    List.ForallScan N.admissionUpdate N.admissionAllowed state (expand z) := by
  apply List.forallScan_iff_forall_prefix.mpr
  intro t u ⟨rest, whole⟩
  have member : u ∈ expand z := by
    rw [← whole]
    exact List.mem_append_left _ (List.mem_append_right _ (by simp only [List.mem_singleton]))
  have active : t.all N.ordinary = true := by
    apply List.all_eq_true.mpr
    intro v hv
    apply terminal z v
    rw [← whole, List.append_assoc, List.singleton_append, List.dropLast_append_cons]
    exact List.mem_append_left _ hv
  rw [N.admissionUpdate_fold]
  refine ⟨?_, ?_⟩
  · exact Bool.and_eq_true_iff.mpr ⟨allowed.1, active⟩
  · exact (reads z u member).trans (allowed.2.trans Finset.subset_union_left)

/-- Local expansion contracts preserve command admission, charging only ordinary commands. -/
theorem Admitted.flatMap
    -- `expand z` is the complete block replacing one source command `z`.
    (expand : M.Command ι → List (N.Command ι))
    -- `targets` preserves the computation destination of each source command.
    (targets : ∀ z, (expand z).filterMap N.target = (M.target z).toList)
    -- `reads` restricts each target command to operands already checked by the source.
    (reads : ∀ z u, u ∈ expand z → N.reads u ⊆ M.reads z)
    -- `terminal` permits a stopping command only at the end of its block.
    (terminal : ∀ z u, u ∈ (expand z).dropLast → N.ordinary u = true)
    -- `ordinary` preserves whether execution may continue after the complete block.
    (ordinary : ∀ z, (expand z).all N.ordinary = M.ordinary z)
    -- `c` bounds ordinary target work per ordinary source command; submission costs zero.
    (c : ℕ) (cost : ∀ z, (expand z).countP N.ordinary ≤
      c * (if M.ordinary z then 1 else 0))
    {input : ι} {k : ℕ} {h : List (M.Command ι)} (admitted : M.Admitted input k h) :
    h.flatMap expand = [] ∨ N.Admitted input (c * k) (h.flatMap expand) := by
  by_cases empty : h.flatMap expand = []
  · exact Or.inl empty
  apply Or.inr
  apply (N.admitted_iff_forallScan input (c * k) _).mpr
  have scan := (M.admitted_iff_forallScan input k h).mp admitted |>.2.2
  have expanded := scan.flatMap expand
    (M.admissionUpdate_expansion N expand targets ordinary)
    (M.admissionAllowed_expansion N expand reads terminal)
  have charged := List.countP_flatMap_le_mul_countP M.ordinary N.ordinary expand c
    (l := h) (fun z _ => cost z)
  exact ⟨empty, charged.trans (Nat.mul_le_mul_left c admitted.2.1), expanded⟩

end Commons.AbstractModel

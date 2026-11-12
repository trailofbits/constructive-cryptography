module

public import RandomSystems.Converter.InsideCuts
public import Tests.DirectCalls

/-! Inside and outside cuts preserve forwarding and two-query calls through finite horizons. -/

@[expose] public section

namespace SystemAlgebra.Tests.AttachmentInsideCuts

open DirectCalls

/-- The existing function evaluator echoes Boolean queries through horizon `n`. -/
noncomputable abbrev echo (n : ℕ) :=
  DDS.ofFunction (boolInterface n).domain (boolInterface n).nonempty_prefix id

/-- A single Unit port makes every reply stay at the queried interface. -/
lemma echo_ports (n : ℕ) : RepliesAtQueriedInterface (echo n).1 := by
  intro h x y hr
  exact Subsingleton.elim _ _

/-- Forwarding through one query agrees after cutting a three-query resource at one. -/
lemma forwarding_one :
    let E := (boolInterface 3).domain
    let α := (DDC.filter (Y := fun _ : Unit => Bool) (fun h => h = [] ∨ E h)
      (prefix_or_nil (boolInterface 3).nonempty_prefix.2)).1
    cutSystem (trim (apply α (cutSystem (echo 3).1 1))) 1 =
      cutSystem (trim (apply α (echo 3).1)) 1 := by
  have ha := isDDCFrom_filter (Y := fun _ : Unit => Bool) (boolInterface 3).nonempty_prefix
  exact ha.cutSystem_trim_apply_cutSystem
    (insideQueriesBounded_id.of_le
      (fun xs y hy => (filterDom_mem_iff _ _ xs y).mp hy |>.2)) monotone_id
    (echo_ports 3) (DDS.ofFunction_dom _ _ _) 1

/-- The interior cut genuinely removes the evaluator's second reply. -/
lemma cut_removes_second :
    cutSystem (echo 3).1 1 [⟨(), false⟩, ⟨(), true⟩] = Part.none ∧
      (echo 3).1 [⟨(), false⟩, ⟨(), true⟩] = Part.some ⟨(), true⟩ := by
  constructor
  · exact cutSystem_apply_of_bound_lt _ _ _ (Nat.lt_succ_self 1)
  · change (echo 3).1 ([⟨(), false⟩] ++ [⟨(), true⟩]) = Part.some ⟨(), true⟩
    rw [DDS.ofFunction_snoc, ite_eq_left ⟨List.cons_ne_nil _ _, Nat.le_succ 2⟩]
    rfl

/-- The existing toggle call has the same canonical outside cut at every horizon, including zero. -/
lemma toggle_cut (q : ℕ) :
    let α := callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 1).domain
    cutSystem (trim (apply α (cutSystem (echo 2).1 2))) q =
      cutSystem (trim (apply α (echo 2).1)) q :=
  toggleCall_isDDCFrom.cutSystem_trim_apply_cutSystem
    (toggleCall_isDDCFrom.insideQueriesBounded_of_domain (fun _ hx => hx.2))
    monotone_const (echo_ports 2) (DDS.ofFunction_dom _ _ _) q

example := toggle_cut 0

/-- Forwarding still returns the first echo reply through a one-query outside filter. -/
lemma outside_one :
    Replies (apply (filterDom (fun xs => (outsideInputs xs).length ≤ 1)
      (idConverter Unit (fun _ => Bool) (fun _ => Bool))) (echo 3).1)
      [⟨(), false⟩] [⟨(), false⟩] := by
  rw [apply_filterDom_outside_length,
    replies_cutSystem_iff _ _ (show ([⟨(), false⟩] : List (Σ _ : Unit, Bool)).length ≤ 1
      from Nat.le_refl 1)]
  apply replies_apply_id (echo_ports 3)
  rw [echo, DDS.replies_ofFunction_iff]
  exact ⟨Or.inr ⟨List.cons_ne_nil _ _, (Nat.le_succ 1).trans (Nat.le_succ 2)⟩, rfl⟩

/-- The existing toggle call has no first reply through a zero-query outside filter. -/
lemma outside_zero :
    apply (filterDom (fun xs => (outsideInputs xs).length ≤ 0)
      (callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
        (boolInterface 1).domain)) (echo 2).1 [⟨(), false⟩] = Part.none := by
  rw [apply_filterDom_outside_length]
  exact cutSystem_apply_of_bound_lt _ _ _ (Nat.zero_lt_succ 0)

#print axioms SystemAlgebra.apply_filterDom_outside_length
#print axioms outside_one
#print axioms outside_zero

#print axioms SystemAlgebra.pair_eq_on_prefixes_right
#print axioms SystemAlgebra.IsDDCFrom.replies_apply_cutSystem_iff
#print axioms SystemAlgebra.IsDDCFrom.cutSystem_trim_apply_cutSystem
#print axioms forwarding_one
#print axioms toggle_cut

end SystemAlgebra.Tests.AttachmentInsideCuts

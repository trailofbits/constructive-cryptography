module

public import RandomSystems.Cumulative.Attachment
public import Tests.UnlimitedSource
public import Tests.DirectCalls

/-!
Unlimited fair-source forwarding and the bounded two-query call use cumulative attachment.
-/

@[expose] public section

namespace SystemAlgebra.Tests.CumulativeAttachment

open Probability Probability.Distribution DirectCalls

/-- Nonempty Unit-port trigger histories retain every nonempty prefix. -/
lemma triggers : ¬ (([] : List (Σ _ : Unit, Unit)) ≠ []) ∧
    ∀ {s t : List (Σ _ : Unit, Unit)}, s <+: t → s ≠ [] → t ≠ [] → s ≠ [] :=
  ⟨fun h => h rfl, fun _ hn _ => hn⟩

/-- The existing forwarding filter admits every nonempty outside trigger history. -/
noncomputable abbrev forwarding :=
  (DDC.filter (Y := fun _ : Unit => Bool)
    (fun h : List (Σ _ : Unit, Unit) => h = [] ∨ h ≠ []) (prefix_or_nil triggers.2)).1

/-- Forwarding admits matching nonempty histories and uses one inside call per outside call. -/
lemma forwarding_cert : IsDDCFrom (fun xs => xs ≠ []) (fun xs => xs ≠ []) 1 forwarding :=
  isDDCFrom_filter triggers

/-- Every outside query pays for its single forwarded inside query, including a pending reply. -/
lemma forwarding_bound : InsideQueriesBounded forwarding id :=
  insideQueriesBounded_id.of_le (fun xs y hy => (filterDom_mem_iff _ _ xs y).mp hy |>.2)

/-- The existing unlimited fair source admits every next trigger. -/
lemma fresh_normalized :
    IsRandomSystem (fun h x => h.map Prod.fst ++ [x] ≠ [])
      (sourceMass (A := Σ _ : Unit, Unit)
        ((𝒰[Bool]).map (Sigma.mk (β := fun _ : Unit => Bool) ()))) := by
  have domain : (fun (h : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Bool))) x =>
      h.map Prod.fst ++ [x] ≠ []) = fun _ _ => True := by
    funext h x
    exact propext ⟨fun _ => trivial, fun _ =>
      List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)⟩
  rw [domain]
  exact sourceMass_isRandomSystem _

/-- Unit has one port, so a fresh reply always carries the queried port. -/
lemma fresh_ports (h : List ((Σ _ : Unit, Unit) × (Σ _ : Unit, Bool)))
    (x : Σ _ : Unit, Unit) (y : Σ _ : Unit, Bool) (hne : y.1 ≠ x.1) :
    sourceMass ((𝒰[Bool]).map (Sigma.mk ())) (h ++ [(x, y)]) = 0 :=
  False.elim (hne (Subsingleton.elim _ _))

/-- Forwarding attaches to the unlimited fresh law. -/
noncomputable abbrev fairForwarded :=
  IsRandomSystem.attachMass triggers triggers forwarding_cert forwarding_bound monotone_id
    fresh_normalized fresh_ports

/-- The forwarded fair source is normalized on every nonempty trigger history. -/
lemma fairForwarded_normalized :
    IsRandomSystem (fun h x => h.map Prod.fst ++ [x] ≠ []) fairForwarded :=
  IsRandomSystem.attachMass_isRandomSystem triggers triggers forwarding_cert forwarding_bound
    monotone_id fresh_normalized fresh_ports

/-- Both zero and positive observation horizons recover the concrete finite assembly. -/
lemma fairForwarded_cut (q : ℕ) :
    IsRandomSystem.cut _ fairForwarded fairForwarded_normalized q =
      IsRandomSystem.attachCut triggers triggers forwarding_cert forwarding_bound monotone_id
        fresh_normalized fresh_ports q q le_rfl :=
  IsRandomSystem.cut_attachMass triggers triggers forwarding_cert forwarding_bound monotone_id
    fresh_normalized fresh_ports q q le_rfl

example := fairForwarded_cut 0
example := fairForwarded_cut 2

/-- A looser total-query allowance gives the same actual forwarded fair behavior. -/
lemma fairForwarded_looser :
    fairForwarded = IsRandomSystem.attachMass triggers triggers forwarding_cert
      (show InsideQueriesBounded forwarding (fun q => q + 1) from
        fun T hr => (forwarding_bound T hr).trans (Nat.le_succ _))
      (fun _ _ h => Nat.add_le_add_right h 1) fresh_normalized fresh_ports :=
  IsRandomSystem.attachMass_eq_of_queryBound triggers triggers forwarding_cert forwarding_bound
    monotone_id fresh_normalized fresh_ports _ _

/-- The existing toggle call on the bounded echo is exactly its established bounded attachment. -/
lemma toggle_bounded :
    let R := TypedSystem.ofFunction (A := boolInterface 2) (fun _ b => b)
    let α := callConverter (V := fun _ => Bool) (Y := fun _ => Bool) toggleCall
      (boolInterface 1).domain
    IsRandomSystem.attachMass (boolInterface 2).nonempty_prefix (boolInterface 1).nonempty_prefix
      toggleCall_isDDCFrom
      (toggleCall_isDDCFrom.insideQueriesBounded_of_domain (fun _ hx => hx.2))
      monotone_const R.1.2 R.2 =
      (PDCBehavior.attach (boolInterface 2).nonempty_prefix (boolInterface 1).nonempty_prefix
        (PDCBehavior.ofDDC α toggleCall_isDDCFrom :
          PDCBehavior Unit Unit (fun _ => Bool) (fun _ => Bool) (fun _ => Bool) (fun _ => Bool)
            (boolInterface 2).domain 2 (fun _ hx => hx.2)
            (boolInterface 1).domain 1 (fun _ hx => hx.2)) R.1 R.2 :
        List ((Σ _ : Unit, Bool) × (Σ _ : Unit, Bool)) → ℝ) :=
  IsRandomSystem.attachMass_eq_attach _ _ toggleCall_isDDCFrom
    (toggleCall_isDDCFrom.insideQueriesBounded_of_domain (fun _ hx => hx.2)) monotone_const
    (fun _ hx => hx.2) (fun _ hx => hx.2) _ _

#print axioms SystemAlgebra.IsRandomSystem.attachMass_isRandomSystem
#print axioms SystemAlgebra.IsRandomSystem.cut_attachMass
#print axioms SystemAlgebra.IsRandomSystem.attachMass_eq_of_queryBound
#print axioms SystemAlgebra.IsRandomSystem.attachMass_eq_attach
#print axioms SystemAlgebra.IsRandomSystem.attachMass_repliesAtQueriedInterface
#print axioms fairForwarded_cut
#print axioms fairForwarded_looser
#print axioms toggle_bounded

end SystemAlgebra.Tests.CumulativeAttachment

import ConstructiveCryptography.Interface
import RandomSystems.Distance.Restriction

/-!
# Domain filters

A filter forwards the queries of an admitted history and stops on the others. The filter
admitting `D` on `A` is a converter from `A` restricted to `D` to `A`: the forwarding DDC of
the restricted domain, a DDC from `A`'s domain. Attached to a resource, it is the restriction of
the resource's random system to the restricted domain, so two filters in series act as the
filter of both conditions.
Source: CR18, §3.4.3 (printed p. 62).

## Main definitions

* `Interface.restrict A D`: the histories of `A`'s domain admitted by `D`
* `Interface.filter A D`: the filter admitting `D` on `A`

## Main results

* `Interface.filter_smul`: a filter attached to a resource is the restriction of its random
  system
* `Interface.filter_comp_filter_smul`: two filters in series act as the filter of both
  conditions
-/

namespace SystemAlgebra.Interface

/-- The histories of `A`'s domain admitted by `D`. -/
abbrev restrict (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) : Interface where
  I := A.I
  X := A.X
  Y := A.Y
  domain h := A.domain h ∧ D h
  nonempty_prefix := ⟨fun hd => A.nonempty_prefix.1 hd.1,
    fun hp hne hd => ⟨A.nonempty_prefix.2 hp hne hd.1, hD _ _ hp hd.2⟩⟩
  bound := A.bound
  length_le h hd := A.length_le h hd.1

/-- **The filter** admitting `D` on `A`: it forwards the queries of an admitted history and
stops on the others. -/
noncomputable def filter (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) : A.restrict D hD ⟶ A :=
  ofDDC
    (DDC.filter (Y := A.Y) (fun h => h = [] ∨ (A.restrict D hD).domain h)
      (prefix_or_nil (A.restrict D hD).nonempty_prefix.2)).1
    ((isDDCFrom_filter (A.restrict D hD).nonempty_prefix).inside_mono fun _ hd => hd.1)

open Classical Probability CategoryTheory

/-- **A filter attached to a resource** is the restriction of the resource's random system to
the restricted domain. -/
theorem filter_smul (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) (R : Resource A) :
    (filter A D hD • R).1 = R.1.restrict (A.restrict D hD).inputDomain fun _ _ hx => hx.1 := by
  obtain ⟨Q, hQ⟩ := Resource.exists_ofPDS R
  subst hQ
  ext h
  change _ = if Admitted _ h then _ else _
  rw [admitted_ofInputs_iff (A.restrict D hD).nonempty_prefix, filter, smul_val,
    PDCBehavior.attach_presents A.nonempty_prefix (A.restrict D hD).nonempty_prefix _ _ _
      ⟨Finsupp.single ⟨_, _⟩ 1, Distribution.isProbDist_single _⟩ Q (fun _ => rfl)
      (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_left, Distribution.mass_fTransform]
  have admits : ∀ {p h : List (Σ i, A.X i)}, p <+: h → (h = [] ∨ (A.restrict D hD).domain h) →
      (p = [] ∨ (A.restrict D hD).domain p) := prefix_or_nil (A.restrict D hD).nonempty_prefix.2
  have filtered : ∀ r : {r : InterfaceSystem A.I A.X A.Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ A.domain h},
      trim (apply (DDC.filter (Y := A.Y) (fun h => h = [] ∨ (A.restrict D hD).domain h)
        admits).1 r.1) = filterDom (fun h => h = [] ∨ (A.restrict D hD).domain h) r.1 :=
    fun r => trim_apply_filter _ admits r.2.1 r.2.2.1
  dsimp only
  simp only [filtered]
  split_ifs with hd
  · refine (Distribution.mass_congr _ fun r => ?_).trans rfl
    refine replies_filterDom_iff (fun hp _ hh => admits hp hh) _ fun hne => ?_
    rcases hd with rfl | hd
    · exact (hne rfl).elim
    · exact Or.inr hd
  · refine Distribution.mass_eq_zero_of_forall_not _ fun r hr => hd ?_
    have hne : h.map Prod.fst ≠ [] := fun he => hd (Or.inl (List.map_eq_nil_iff.mp he))
    have hf := ((filterDom_dom _ _ _).mp (hr.dom hne)).1
    exact Or.inr (hf.resolve_left hne)

/-- **Two filters in series** act as the filter of both conditions: the resources have the
same transcript masses. -/
theorem filter_comp_filter_smul (A : Interface) (D : List (Σ i, A.X i) → Prop)
    (hD : ∀ p h, p <+: h → D h → D p) (D' : List (Σ i, A.X i) → Prop)
    (hD' : ∀ p h, p <+: h → D' h → D' p) (R : Resource A) :
    ((filter (A.restrict D hD) D' hD' ≫ filter A D hD) • R).1.1 =
      (filter A (fun h => D h ∧ D' h)
        (fun p h hp hh => ⟨hD p h hp hh.1, hD' p h hp hh.2⟩) • R).1.1 := by
  rw [comp_smul, filter_smul, filter_smul, filter_smul]
  refine (congrArg Subtype.val (RandomSystem.restrict_restrict _ _ _)).trans (funext fun h => ?_)
  change (if Admitted _ h then _ else _) = if Admitted _ h then _ else _
  have both : ∀ p h, p <+: h → D h ∧ D' h → D p ∧ D' p :=
    fun p h hp hh => ⟨hD p h hp hh.1, hD' p h hp hh.2⟩
  refine if_congr ?_ rfl rfl
  rw [admitted_ofInputs_iff ((A.restrict D hD).restrict D' hD').nonempty_prefix,
    admitted_ofInputs_iff (A.restrict _ both).nonempty_prefix]
  exact or_congr_right and_assoc

end SystemAlgebra.Interface

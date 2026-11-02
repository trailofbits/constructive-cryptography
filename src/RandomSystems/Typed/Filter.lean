module

public import RandomSystems.Typed.Interface
public import RandomSystems.Distance.Restriction

/-!
# Domain filters

`filter A D hD : TypedConverter (A.restrict D hD) A` forwards admitted inputs.
Attached to `R`, it preserves the cumulative probability of an admitted transcript and gives
zero to other transcripts. Two successive filters intersect their input conditions.

## Main definitions

* `Interface.restrict A D`: the histories of `A`'s domain admitted by `D`
* `TypedConverter.filter A D`: the filter admitting `D` on `A`

## Main results

* `TypedConverter.filter_smul`: a filter attached to a typed system is the restriction of its
  random system
* `TypedConverter.filter_mass_of_admitted`: admitted transcripts retain their probability
* `TypedConverter.filter_comp_filter_smul`: two filters in series act as the filter of both
  conditions

## References

1. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace SystemAlgebra

namespace Interface

/-- Keep the ports, alphabets and bound of `A`, with domain `A.domain h ∧ D h`. -/
abbrev restrict
    -- `A` supplies the original interface; `D` selects its input histories.
    (A : Interface) (D : List (Σ i, A.X i) → Prop)
    -- `hD` makes the selection prefix-closed.
    (hD : ∀ p h, p <+: h → D h → D p) : Interface where
  I := A.I
  X := A.X
  Y := A.Y
  domain h := A.domain h ∧ D h
  nonempty_prefix := ⟨fun hd => A.nonempty_prefix.1 hd.1,
    fun hp hne hd => ⟨A.nonempty_prefix.2 hp hne hd.1, hD _ _ hp hd.2⟩⟩
  bound := A.bound
  length_le h hd := A.length_le h hd.1

end Interface

namespace TypedConverter

variable
  -- `A` supplies ports, alphabets, the query bound and the original input domain.
  (A : Interface)
  -- `D` selects input histories; `hD` makes the selection prefix-closed.
  (D : List (Σ i, A.X i) → Prop) (hD : ∀ p h, p <+: h → D h → D p)

/-- Forward inputs while their history satisfies `A.domain ∧ D`; stop otherwise.
A “deterministic discrete converter” in the sense of [1, §3.4.3, p. 62]. -/
noncomputable def filter : TypedConverter (A.restrict D hD) A :=
  ofDDC
    (DDC.filter (Y := A.Y) (fun h => h = [] ∨ (A.restrict D hD).domain h)
      (prefix_or_nil (A.restrict D hD).nonempty_prefix.2)).1
    ((isDDCFrom_filter (A.restrict D hD).nonempty_prefix).inside_mono fun _ hd => hd.1)

open Probability

/-- **A filter attached to a typed system** is the restriction of the system's random system to
the restricted domain. -/
lemma filter_smul
    -- `R` is the original system; restriction keeps its probabilities on admitted histories.
    (R : TypedSystem A) :
    (filter A D hD • R).1 = R.1.restrict (A.restrict D hD).inputDomain fun _ _ hx => hx.1 := by
  classical
  -- Choose a PDS representative to apply the deterministic forwarding law.
  obtain ⟨Q, hQ⟩ := TypedSystem.exists_ofPDS R
  subst hQ
  ext h
  change _ = if Admitted _ h then _ else _
  -- Attachment averages forwarding over the representative's deterministic systems.
  rw [admitted_ofInputs_iff (A.restrict D hD).nonempty_prefix, filter, smul_val,
    PDCBehavior.attach_presents A.nonempty_prefix (A.restrict D hD).nonempty_prefix _ _ _
      ⟨Finsupp.single ⟨_, _⟩ 1, Distribution.isProbDist_single _⟩ Q (fun _ => rfl)
      (fun _ => rfl) h,
    behaviorMass_attachPDS, Distribution.prod_single_left, Distribution.mass_fTransform]
  have admits : ∀ {p h : List (Σ i, A.X i)}, p <+: h → (h = [] ∨ (A.restrict D hD).domain h) →
      (p = [] ∨ (A.restrict D hD).domain p) := prefix_or_nil (A.restrict D hD).nonempty_prefix.2
  -- On each deterministic system, forwarding is exactly domain restriction.
  have filtered : ∀ r : {r : InterfaceSystem A.I A.X A.Y //
      IsDDS r ∧ RepliesAtQueriedInterface r ∧ ∀ h, (r h).Dom ↔ A.domain h},
      trim (apply (DDC.filter (Y := A.Y) (fun h => h = [] ∨ (A.restrict D hD).domain h)
        admits).1 r.1) = filterDom (fun h => h = [] ∨ (A.restrict D hD).domain h) r.1 :=
    fun r => trim_apply_filter _ admits r.2.1 r.2.2.1
  dsimp only
  simp only [filtered]
  split_ifs with hd
  · -- Admission makes the filtered and original reply events identical.
    refine (Distribution.mass_congr _ fun r => ?_).trans rfl
    refine replies_filterDom_iff (fun hp _ hh => admits hp hh) _ fun hne => ?_
    rcases hd with rfl | hd
    · exact (hne rfl).elim
    · exact Or.inr hd
  · -- A reply on an excluded history would contradict the forwarding domain.
    refine Distribution.mass_eq_zero_of_forall_not _ fun r hr => hd ?_
    have hne : h.map Prod.fst ≠ [] := fun he => hd (Or.inl (List.map_eq_nil_iff.mp he))
    have hf := ((filterDom_dom _ _ _).mp (hr.dom hne)).1
    exact Or.inr (hf.resolve_left hne)

/-- An admitted transcript has the same probability before and after filtering. -/
lemma filter_mass_of_admitted
    -- `R` is filtered; `h` is a transcript over `A`'s query and reply alphabets.
    (R : TypedSystem A) (h : List ((Σ i, A.X i) × (Σ i, A.Y i)))
    -- `hh` admits the empty transcript or the complete input history in the restricted domain.
    (hh : h = [] ∨ (A.restrict D hD).domain (h.map Prod.fst)) :
    (filter A D hD • R).1 h = R.1 h := by
  classical
  rw [filter_smul]
  -- Restriction keeps the original mass on precisely these admitted input histories.
  change (if Admitted (A.restrict D hD).inputDomain h then R.1 h else 0) = R.1 h
  exact ite_eq_left ((admitted_ofInputs_iff (A.restrict D hD).nonempty_prefix h).mpr hh)

/-- **Two filters in series** act as the filter of both conditions: the typed systems have the
same transcript masses. -/
lemma filter_comp_filter_smul
    -- `D'` is a second prefix-closed condition on the same query alphabet.
    (D' : List (Σ i, A.X i) → Prop) (hD' : ∀ p h, p <+: h → D' h → D' p)
    -- `R` is filtered by both conditions, in either serial or intersected form.
    (R : TypedSystem A) :
    (comp (filter (A.restrict D hD) D' hD') (filter A D hD) • R).1.1 =
      (filter A (fun h => D h ∧ D' h)
        (fun p h hp hh => ⟨hD p h hp hh.1, hD' p h hp hh.2⟩) • R).1.1 := by
  classical
  -- Serial restriction intersects the two conditions on the same input history.
  rw [comp_smul, filter_smul, filter_smul, filter_smul]
  refine (congrArg Subtype.val (RandomSystem.restrict_restrict _ _ _)).trans (funext fun h => ?_)
  change (if Admitted _ h then _ else _) = if Admitted _ h then _ else _
  have both : ∀ p h, p <+: h → D h ∧ D' h → D p ∧ D' p :=
    fun p h hp hh => ⟨hD p h hp hh.1, hD' p h hp hh.2⟩
  refine if_congr ?_ rfl rfl
  rw [admitted_ofInputs_iff ((A.restrict D hD).restrict D' hD').nonempty_prefix,
    admitted_ofInputs_iff (A.restrict _ both).nonempty_prefix]
  exact or_congr_right and_assoc

end TypedConverter

end SystemAlgebra

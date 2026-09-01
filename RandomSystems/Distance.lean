/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.ObservationRestriction
import Probability.StatisticalDistance

/-!
# Fixed-interface random-system distance

Lanzenberger, Definition 2.26 (printed p. 18), defines distinguishing
advantage for random systems with one common domain.  `CommonDomain.Presentation.Adv`
makes that common domain part of the type.  The broader `PDS.advantage` is an
auxiliary supremum whose observation family is determined separately by each
pair of laws.
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-- The pair-specific distinguishing advantage over DDEs compatible with, and
stopping on, both laws.  This broader auxiliary is useful before a common
domain has been fixed; it is not Lanzenberger's literal Definition 2.26. -/
def advantage (S T : PDS X Y) : ℝ :=
  sSup ((fun e : {e : System.DDE Y X //
      (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)} =>
    statDist (trLaw e.1 S) (trLaw e.1 T)) '' Set.univ)

/-- Notation for pair-specific fixed-interface advantage. For laws with one
common domain, this is Lanzenberger's `Adv(S,T)`. -/
scoped notation:max "Adv(" S ", " T ")" => advantage S T

/-- Transcript observation cannot make two fixed laws farther apart, so the
set defining pair-specific advantage is bounded above. -/
lemma bddAbove_advantage (S T : PDS X Y) :
    BddAbove ((fun e : {e : System.DDE Y X //
        (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)} =>
      statDist (trLaw e.1 S) (trLaw e.1 T)) '' Set.univ) := by
  refine ⟨statDist S T, ?_⟩
  rintro value ⟨environment, _, rfl⟩
  exact Probability.statDist_fTransform_le S T _

/-- Pair-specific distinguishing advantage is nonnegative. -/
lemma advantage_nonneg (S T : PDS X Y) : 0 ≤ advantage S T := by
  unfold advantage
  exact Probability.sSup_image_univ_nonneg_of_forall _
    (bddAbove_advantage S T) fun environment =>
      Probability.statDist_nonneg
        (trLaw environment.1 S) (trLaw environment.1 T)

@[simp]
theorem advantage_self (S : PDS X Y) : advantage S S = 0 :=
  le_antisymm
    (Probability.sSup_image_univ_le_of_forall _ le_rfl fun _ =>
      (Probability.statDist_self _).le)
    (advantage_nonneg S S)

/-- Lanzenberger, Definition 2.4 (printed p. 12): “for distributions of the
same weight, i.e., `|X| = |Y|`, we have
`δ(X,Y) = 1/2 ∑_{a∈A} |X(a) - Y(a)|`.”
Transcript pushforward preserves weight, so swapping the two pair-admissible
observation families preserves their advantage. -/
theorem advantage_comm_of_weight_eq {S T : PDS X Y}
    (weight_eq : S.weight = T.weight) : advantage S T = advantage T S := by
  apply le_antisymm
  · unfold advantage
    refine Probability.sSup_image_univ_le_sSup_image_univ_of_forall_exists
      _ _ (bddAbove_advantage T S) (fun environment =>
        Probability.statDist_nonneg
          (trLaw environment.1 T) (trLaw environment.1 S)) ?_
    intro environment
    let swapped : {e : System.DDE Y X //
        (Compatible e T ∧ Stops e T) ∧ (Compatible e S ∧ Stops e S)} :=
      ⟨environment.1, environment.2.2, environment.2.1⟩
    have transcript_weight_eq :
        (trLaw environment.1 S).weight = (trLaw environment.1 T).weight := by
      simpa only [trLaw, Distribution.weight_fTransform] using weight_eq
    rw [Probability.statDist_symm_of_eq_weight _ _ transcript_weight_eq]
    exact ⟨swapped, rfl⟩
  · unfold advantage
    refine Probability.sSup_image_univ_le_sSup_image_univ_of_forall_exists
      _ _ (bddAbove_advantage S T) (fun environment =>
        Probability.statDist_nonneg
          (trLaw environment.1 S) (trLaw environment.1 T)) ?_
    intro environment
    let swapped : {e : System.DDE Y X //
        (Compatible e S ∧ Stops e S) ∧ (Compatible e T ∧ Stops e T)} :=
      ⟨environment.1, environment.2.2, environment.2.1⟩
    have transcript_weight_eq :
        (trLaw environment.1 T).weight = (trLaw environment.1 S).weight := by
      simpa only [trLaw, Distribution.weight_fTransform] using weight_eq.symm
    rw [Probability.statDist_symm_of_eq_weight _ _ transcript_weight_eq]
    exact ⟨swapped, rfl⟩

/-- The advantage over DDEs compatible with one named domain and halting on
every answer history. This global halting condition is stronger than the
pair-specific `Stops` condition used by `PDS.advantage`; both are Lean
extensions beyond the thesis's standing finite-system setting. This is an
auxiliary observation family rather than Definition 2.26. -/
def advantageOnDomain (D : Set (List X)) (S T : PDS X Y) : ℝ :=
  sSup ((fun e : {e : System.DDE Y X //
      System.CompatibleD e D ∧ System.DDE.Halts e} =>
    statDist (trLaw e.1 S) (trLaw e.1 T)) '' Set.univ)

/-- Transcript observation cannot make two fixed laws farther apart, so the
set defining fixed-domain advantage is bounded above. -/
lemma bddAbove_advantageOnDomain (D : Set (List X)) (S T : PDS X Y) :
    BddAbove ((fun e : {e : System.DDE Y X //
        System.CompatibleD e D ∧ System.DDE.Halts e} =>
      statDist (trLaw e.1 S) (trLaw e.1 T)) '' Set.univ) := by
  refine ⟨statDist S T, ?_⟩
  rintro value ⟨environment, _, rfl⟩
  exact Probability.statDist_fTransform_le S T _

/-- Fixed-domain distinguishing advantage is nonnegative. -/
lemma advantageOnDomain_nonneg (D : Set (List X)) (S T : PDS X Y) :
    0 ≤ advantageOnDomain D S T := by
  unfold advantageOnDomain
  exact Probability.sSup_image_univ_nonneg_of_forall _
    (bddAbove_advantageOnDomain D S T) fun environment =>
      Probability.statDist_nonneg
        (trLaw environment.1 S) (trLaw environment.1 T)

@[simp]
theorem advantageOnDomain_self (D : Set (List X)) (S : PDS X Y) : advantageOnDomain D S S = 0 :=
  le_antisymm
    (Probability.sSup_image_univ_le_of_forall _ le_rfl fun _ =>
      (Probability.statDist_self _).le)
    (advantageOnDomain_nonneg D S S)

/-- Triangle inequality for advantage over one fixed-domain observation
family.  The three terms use the same compatible, halting environments, so
the distribution-level statistical-distance triangle inequality applies at
each environment before taking the supremum. -/
theorem advantageOnDomain_triangle (D : Set (List X)) (S T U : PDS X Y) :
    advantageOnDomain D S U ≤ advantageOnDomain D S T + advantageOnDomain D T U := by
  unfold advantageOnDomain
  refine Real.sSup_le ?_ (add_nonneg
    (advantageOnDomain_nonneg D S T)
    (advantageOnDomain_nonneg D T U))
  rintro value ⟨environment, _, rfl⟩
  calc
    statDist (trLaw environment.1 S) (trLaw environment.1 U) ≤
        statDist (trLaw environment.1 S) (trLaw environment.1 T) +
          statDist (trLaw environment.1 T) (trLaw environment.1 U) :=
      Probability.statDist_triangle _ _ _
    _ ≤ sSup ((fun e : {e : System.DDE Y X //
              System.CompatibleD e D ∧ System.DDE.Halts e} =>
            statDist (trLaw e.1 S) (trLaw e.1 T)) '' Set.univ) +
          sSup ((fun e : {e : System.DDE Y X //
              System.CompatibleD e D ∧ System.DDE.Halts e} =>
            statDist (trLaw e.1 T) (trLaw e.1 U)) '' Set.univ) :=
      add_le_add
        (le_csSup (bddAbove_advantageOnDomain D S T)
          ⟨environment, Set.mem_univ _, rfl⟩)
        (le_csSup (bddAbove_advantageOnDomain D T U)
          ⟨environment, Set.mem_univ _, rfl⟩)

/-- The globally halting fixed-domain observation family is included in the
pair-specific auxiliary family when both laws present `D`. -/
theorem advantageOnDomain_le_advantage {S T : PDS X Y} {D : Set (List X)}
    (hS : HasDomain S D) (hT : HasDomain T D) :
    advantageOnDomain D S T ≤ advantage S T := by
  unfold advantageOnDomain advantage
  refine Probability.sSup_image_univ_le_sSup_image_univ_of_forall_exists
    _ _ (bddAbove_advantage S T) (fun environment =>
      Probability.statDist_nonneg
        (trLaw environment.1 S) (trLaw environment.1 T)) ?_
  intro environment
  exact ⟨⟨environment.1,
      ⟨compatible_of_compatibleD environment.2.1 hS,
        stops_of_halts environment.2.2 S⟩,
      ⟨compatible_of_compatibleD environment.2.1 hT,
        stops_of_halts environment.2.2 T⟩⟩, rfl⟩

/-- Lean support for Definition 2.14's standing finite-system scope (printed
p. 15): “We always assume that `S` is finite.” A DDS presenting the shared
domain lets every pair-compatible, pair-stopping DDE be restricted to a
globally halting, domain-compatible DDE with the same two transcript laws. -/
theorem advantage_le_advantageOnDomain_of_reference
    {left right : PDS X Y} {domain : Set (List X)}
    (leftDomain : HasDomain left domain) (rightDomain : HasDomain right domain)
    (reference : System.DDS X Y) (referenceDomain : System.dom reference = domain) :
    advantage left right ≤ advantageOnDomain domain left right := by
  unfold advantage advantageOnDomain
  refine Probability.sSup_image_univ_le_sSup_image_univ_of_forall_exists
    _ _ (bddAbove_advantageOnDomain domain left right) (fun environment =>
      Probability.statDist_nonneg
        (trLaw environment.1 left) (trLaw environment.1 right)) ?_
  intro environment
  -- Finite law support turns the two pointwise stopping predicates into one cutoff.
  let rounds := max
    (stoppingBound environment.1 left environment.2.1.2)
    (stoppingBound environment.1 right environment.2.2.2)
  let restricted :=
    System.DDE.boundedDomainRestriction reference environment.1 rounds
  -- The restriction is one member of the fixed common-domain observation family.
  have restrictedCompatible : System.CompatibleD restricted domain := by
    intro system systemDomain
    exact System.DDE.boundedDomainRestriction_compatible reference environment.1
      rounds system (systemDomain.trans referenceDomain.symm)
  have restrictedHalts : System.DDE.Halts restricted :=
    System.DDE.boundedDomainRestriction_halts reference environment.1 rounds
  let candidate : {e : System.DDE Y X //
      System.CompatibleD e domain ∧ System.DDE.Halts e} :=
    ⟨restricted, restrictedCompatible, restrictedHalts⟩
  -- Each endpoint law is unchanged because its interactions stabilize by `rounds`.
  have leftLaw : trLaw restricted left = trLaw environment.1 left :=
    trLaw_boundedDomainRestriction_eq reference environment.1 rounds left
      (fun system supported =>
        (leftDomain system supported).trans referenceDomain.symm)
      environment.2.1.1 environment.2.1.2 (Nat.le_max_left _ _)
  have rightLaw : trLaw restricted right = trLaw environment.1 right :=
    trLaw_boundedDomainRestriction_eq reference environment.1 rounds right
      (fun system supported =>
        (rightDomain system supported).trans referenceDomain.symm)
      environment.2.2.1 environment.2.2.2 (Nat.le_max_right _ _)
  -- The same statistical-distance term therefore occurs in the fixed-family supremum.
  refine ⟨candidate, ?_⟩
  rw [leftLaw, rightLaw]

/-- Every pair-specific common-domain observation has an equivalent globally
halting, domain-compatible restriction. If both laws have empty support, both
are the zero law; otherwise a supported DDS supplies the reference domain. -/
theorem advantage_le_advantageOnDomain
    {left right : PDS X Y} {domain : Set (List X)}
    (leftDomain : HasDomain left domain) (rightDomain : HasDomain right domain) :
    advantage left right ≤ advantageOnDomain domain left right := by
  by_cases leftNonempty : left.support.Nonempty
  · obtain ⟨reference, supported⟩ := leftNonempty
    exact advantage_le_advantageOnDomain_of_reference leftDomain rightDomain
      reference (leftDomain reference supported)
  · by_cases rightNonempty : right.support.Nonempty
    · obtain ⟨reference, supported⟩ := rightNonempty
      exact advantage_le_advantageOnDomain_of_reference leftDomain rightDomain
        reference (rightDomain reference supported)
    · have leftZero : left = 0 := by
        apply Finsupp.support_eq_empty.mp
        exact Finset.not_nonempty_iff_eq_empty.mp leftNonempty
      have rightZero : right = 0 := by
        apply Finsupp.support_eq_empty.mp
        exact Finset.not_nonempty_iff_eq_empty.mp rightNonempty
      subst left
      subst right
      rw [advantage_self, advantageOnDomain_self]

/-- On two laws presenting one domain, pair-specific stopping observations and
globally halting domain-compatible observations give the same advantage. -/
theorem advantage_eq_advantageOnDomain
    {left right : PDS X Y} {domain : Set (List X)}
    (leftDomain : HasDomain left domain) (rightDomain : HasDomain right domain) :
    advantage left right = advantageOnDomain domain left right :=
  le_antisymm
    (advantage_le_advantageOnDomain leftDomain rightDomain)
    (advantageOnDomain_le_advantage leftDomain rightDomain)

end PDS

namespace CommonDomain.Presentation

/-- Lanzenberger, Definition 2.26 (printed p. 18): “For two random
`(X,Y)`-systems `S` and `T` with the same domain,” the distinguishing
advantage is the supremum over DDEs compatible with both systems.  The common
domain is enforced by placing both presentations in the same fibre. Lean does
not bundle the thesis's standing finite-system assumption, so the underlying
formula records stopping explicitly on the broader carrier. -/
def Adv {D : Set (List X)}
    (S T : {P : CommonDomain.Presentation X Y // P.domain = D}) : ℝ :=
  PDS.advantage S.1.law T.1.law

/-- Lanzenberger's notation `Adv(S,T)` for two presentations in one
common-domain fibre. -/
scoped notation "Adv(" S ", " T ")" => Adv S T

@[simp]
theorem Adv_self {D : Set (List X)}
    (S : {P : CommonDomain.Presentation X Y // P.domain = D}) : Adv S S = 0 :=
  PDS.advantage_self S.1.law

/-- Lanzenberger, Definition 2.4 (printed p. 12): “for distributions of the
same weight, i.e., `|X| = |Y|`, we have
`δ(X,Y) = 1/2 ∑_{a∈A} |X(a) - Y(a)|`.”
Thus literal common-domain advantage is symmetric for equal-weight
presentations; arbitrary-mass presentations do not satisfy this law. -/
theorem Adv_comm_of_weight_eq {D : Set (List X)}
    (S T : {P : CommonDomain.Presentation X Y // P.domain = D})
    (weight_eq : S.1.law.weight = T.1.law.weight) : Adv S T = Adv T S :=
  PDS.advantage_comm_of_weight_eq weight_eq

/-- Lanzenberger, Definition 2.26 (printed p. 18): “For two random
`(X,Y)`-systems `S` and `T` with the same domain,” `Adv(S,T)` is the supremum
“over all compatible `(Y,X)`-DDE.” On Lean's unbounded carrier, the bounded
common-domain restriction identifies each pair-specific observation family
with the fixed family, whose pointwise statistical distances satisfy the
triangle inequality. -/
theorem Adv_triangle {D : Set (List X)}
    (left middle right :
      {P : CommonDomain.Presentation X Y // P.domain = D}) :
    Adv left right ≤ Adv left middle + Adv middle right := by
  have leftDomain : PDS.HasDomain left.1.law D := by
    simpa only [left.2] using left.1.hasDomain
  have middleDomain : PDS.HasDomain middle.1.law D := by
    simpa only [middle.2] using middle.1.hasDomain
  have rightDomain : PDS.HasDomain right.1.law D := by
    simpa only [right.2] using right.1.hasDomain
  change PDS.advantage left.1.law right.1.law ≤
    PDS.advantage left.1.law middle.1.law +
      PDS.advantage middle.1.law right.1.law
  rw [PDS.advantage_eq_advantageOnDomain leftDomain rightDomain,
    PDS.advantage_eq_advantageOnDomain leftDomain middleDomain,
    PDS.advantage_eq_advantageOnDomain middleDomain rightDomain]
  exact PDS.advantageOnDomain_triangle D
    left.1.law middle.1.law right.1.law

end CommonDomain.Presentation

end


end RandomSystems

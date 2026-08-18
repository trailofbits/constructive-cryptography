/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ClassDistance

/-!
# Notation 2.19: the random system as an equivalence class

Lanzenberger **Notation 2.19** (printed p. 16): "We use bold-face font `𝐒` to
denote a *random system*, an equivalence class of PDS.  Since the transcript
distribution `tr(S,e)` does (by definition) only depend on the random system
`𝐒` and not on the concrete element `S ∈ 𝐒` of the equivalence class, we write
`tr(𝐒,e)`."  §2.1.2 makes the same point in words — a random system *is* the
class, and a PDS is a presentation of one.

Until now the tree worked with representatives and transported along
`PDS.advFullyDefined_congr` / `PDS.classDistance_congr`; this file forms the
quotient those congruences describe and descends the three invariants onto it.

## What is here

* `PDS.equivalentSetoid` — Definition 2.17's relation as a `Setoid`
  (`ClassDistance.lean` already proves it reflexive, symmetric, transitive).
* `PDS.Behaviour X Y` — Notation 2.19's `𝐒`: `PDS X Y` taken up to `≡`, at a
  fixed alphabet pair (the L2 pin), with the eliminators `toBehaviour`,
  `Behaviour.ind`, `Behaviour.ind₂`.
* The descended invariants `Behaviour.weight` (`weight_eq_of_equivalent`),
  `Behaviour.advFullyDefined` (`advFullyDefined_congr`),
  `Behaviour.classDistance` (`classDistance_congr`) and `Behaviour.AdvD`
  (`AdvD_congr`) — each an equality on the quotient where it was a transport
  lemma below.  The last of them is Definition 2.26 itself, in the domain-indexed
  reading the thesis uses; `PDS.Adv`, whose index set is cut out by the two
  supports, has no counterpart here and is not expected to.
* The metric.  `Adv⊥` is one-sided on the signed carrier and symmetric exactly
  at equal weight, so the distance installed is its `⊔`-symmetrization, exactly
  as the `Phi` instance in `MetricFullyDefined.lean` does it (read for the
  shape; not modified, and not imported — that instance is at the *universal*
  carrier `Phi = PDS Uni Uni` and is a `PseudoEMetricSpace`, this one is at an
  arbitrary `(X, Y)`).

  On the quotient the metric **separates points**
  (`equivalent_iff_advFullyDefined_eq_zero`), so what is installed is a genuine
  `EMetricSpace`, not merely a pseudo one — the whole point of Notation 2.19.
  That strengthening is a *gain* over the `Phi` instance and over the quarry's
  `RandomSystemMetric.lean:59`, whose `MetricSpace` is built on `maxAdvantage`,
  which pin 2 forbids.

## MR16 discipline

No `DistinguisherClass` appears here.  `AbstractCryptography/Metric/Behaviour.lean`
is a *different* object behind the MR11 provenance fence — MauRen11 Definition
14's carrier taken up to the zero set of `edistD`, indexed by an admitted test
family — and this file neither imports nor mentions it.  The relation quotiented
here is Lanzenberger Definition 2.17, which quantifies over *all* total
environments and is fixed before any class of distinguishers is chosen.

## Provenance

Statement shapes from the read-only quarry
`RandomSystems/RandomSystemQuotient.lean:99,150,154,171` (the quotient
construction and a descended distance) and `RandomSystems/RandomSystemMetric.lean:49,59`
(separation and the metric-space upgrade), with the documented **delta
`metric`**: the quarry descends `maxAdvantage`, which Ruling R4 forbids as a
statement target, so the descended distance here is `PDS.advFullyDefined` and
the separation lemma is re-proved against it.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-! ## Separation: `Adv⊥` vanishes in both directions exactly on `≡` -/

/-- **`Adv⊥` separates the equivalence classes.**  Two systems are equivalent
(Definition 2.17) exactly when the fully defined advantage vanishes in *both*
argument orders.

Both directions are one-line consequences of the definitions, and the
two-sidedness is the signed carrier's honest cost: `statDist` is one-sided, so
`statDist X Y = 0` says only `X ≤ Y` pointwise, and the two orders together are
what force the transcript laws equal.  For equal-weight systems — in particular
for any two probability laws — one direction already implies the other through
`advFullyDefined_comm_of_weight_eq`.

This is the quarry's `maximal_advantage_eq_zero_iff_equivalent`
(`RandomSystemMetric.lean:49`) re-targeted from `maxAdvantage` to the pin-2
object. -/
theorem equivalent_iff_advFullyDefined_eq_zero {S T : PDS X Y} :
    equivalent S T ↔ advFullyDefined S T = 0 ∧ advFullyDefined T S = 0 := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [advFullyDefined_congr h (equivalent_refl T), advFullyDefined_self]
    · rw [advFullyDefined_congr (equivalent_refl T) h, advFullyDefined_self]
  · rintro ⟨hST, hTS⟩ e n
    have hzero : ∀ {U V : PDS X Y}, advFullyDefined U V = 0 →
        statDist (trLawFullyDefined e n U) (trLawFullyDefined e n V) = 0 := by
      intro U V h
      have hle : ENNReal.ofReal
          (statDist (trLawFullyDefined e n U) (trLawFullyDefined e n V)) ≤ 0 :=
        h ▸ le_iSup_of_le e (le_iSup_of_le n le_rfl)
      have := ENNReal.ofReal_eq_zero.mp (le_antisymm hle (zero_le _))
      exact le_antisymm this (Probability.statDist_nonneg _ _)
    refine Finsupp.ext fun t => ?_
    have h₁ := Probability.Distribution.max_sub_eq_zero_of_statDist_eq_zero (hzero hST) t
    have h₂ := Probability.Distribution.max_sub_eq_zero_of_statDist_eq_zero (hzero hTS) t
    have hle₁ : trLawFullyDefined e n S t ≤ trLawFullyDefined e n T t := by
      by_contra hcon
      exact absurd h₁ (by
        rw [max_eq_left (by linarith [not_le.mp hcon] : (0:ℝ) ≤
          trLawFullyDefined e n S t - trLawFullyDefined e n T t)]
        exact sub_ne_zero.mpr (ne_of_gt (not_le.mp hcon)))
    have hle₂ : trLawFullyDefined e n T t ≤ trLawFullyDefined e n S t := by
      by_contra hcon
      exact absurd h₂ (by
        rw [max_eq_left (by linarith [not_le.mp hcon] : (0:ℝ) ≤
          trLawFullyDefined e n T t - trLawFullyDefined e n S t)]
        exact sub_ne_zero.mpr (ne_of_gt (not_le.mp hcon)))
    exact le_antisymm hle₁ hle₂

/-! ## The quotient -/

/-- Lanzenberger **Definition 2.17**'s relation as a `Setoid`: the three laws
are `equivalent_refl`, `equivalent_symm`, `equivalent_trans`.

Deliberately a `def` and not an `instance`: `PDS X Y` is an `abbrev` for a
`Finsupp`, and registering a global `Setoid` on it would be found by every
`Quotient` elaboration in the tree. -/
def equivalentSetoid (X : Type u) (Y : Type v) : Setoid (PDS X Y) where
  r := equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

/-- Lanzenberger **Notation 2.19**: a *random system* `𝐒` is an equivalence
class of PDS.  `Behaviour X Y` is the carrier of those classes at a fixed
alphabet pair.

The name is the repository's ("behaviour" for the observable content of a
presentation), not the thesis's — the thesis writes only the bold `𝐒`.
COINAGE, flagged. -/
def Behaviour (X : Type u) (Y : Type v) : Type (max u v) :=
  Quotient (equivalentSetoid X Y)

/-- The random system a PDS presents: Notation 2.19's `S ↦ 𝐒`. -/
def toBehaviour (S : PDS X Y) : Behaviour X Y :=
  Quotient.mk (equivalentSetoid X Y) S

theorem toBehaviour_surjective :
    Function.Surjective (toBehaviour (X := X) (Y := Y)) :=
  Quotient.exists_rep

@[simp] theorem toBehaviour_eq_iff {S T : PDS X Y} :
    toBehaviour S = toBehaviour T ↔ equivalent S T := by
  show Quotient.mk (equivalentSetoid X Y) S = Quotient.mk (equivalentSetoid X Y) T ↔ _
  exact ⟨Quotient.exact, Quotient.sound (s := equivalentSetoid X Y)⟩

@[elab_as_elim] theorem Behaviour.ind {motive : Behaviour X Y → Prop}
    (h : ∀ S, motive (toBehaviour S)) : ∀ B, motive B := Quotient.ind h

@[elab_as_elim] theorem Behaviour.ind₂
    {motive : Behaviour X Y → Behaviour X Y → Prop}
    (h : ∀ S T, motive (toBehaviour S) (toBehaviour T)) : ∀ B C, motive B C :=
  Quotient.ind₂ h

/-! ## The descended invariants

Each of the three is a transport lemma below the quotient and an *equality*
above it. -/

/-- The weight of a random system: equivalent presentations have equal weight
(`weight_eq_of_equivalent`), so Definition 2.1's `|S|` is an invariant of the
class. -/
def Behaviour.weight : Behaviour X Y → ℝ :=
  Quotient.lift Distribution.weight fun _ _ h => weight_eq_of_equivalent h

@[simp] theorem Behaviour.weight_toBehaviour (S : PDS X Y) :
    Behaviour.weight (toBehaviour S) = S.weight := rfl

/-- Ruling R4's `Adv⊥` on random systems: Notation 2.19's own observation
(`tr(𝐒,e)` depends only on the class) at the metric, which is
`advFullyDefined_congr`. -/
def Behaviour.advFullyDefined : Behaviour X Y → Behaviour X Y → ℝ≥0∞ :=
  Quotient.lift₂ PDS.advFullyDefined fun _ _ _ _ h₁ h₂ =>
    PDS.advFullyDefined_congr h₁ h₂

@[simp] theorem Behaviour.advFullyDefined_toBehaviour (S T : PDS X Y) :
    Behaviour.advFullyDefined (toBehaviour S) (toBehaviour T) =
      PDS.advFullyDefined S T := rfl

/-- **Lanzenberger Definition 2.26 on random systems**, at the domain-indexed
reading `PDS.AdvD`.

Definition 2.26's advantage is a supremum over the environments the *domain*
admits, and the thesis reads it on classes without further comment — Notation
2.19's own observation, `tr(𝐒, e)` depending only on the class.  That reading
descends here for the same reason, and unconditionally: the index set names no
system (`System.CompatibleD`, `System.DDE.Halts`), and at each of its
environments the transcript law is pinned by Definition 2.17
(`PDS.trLaw_congr_of_halts`), so `PDS.AdvD_congr` is a congruence with no
hypothesis at all.

`PDS.Adv` itself has no counterpart here and is not expected to: its index set
is cut out by the two *supports*, which is presentation data.  On the systems
Definition 2.14 admits the two agree (`PDS.AdvD_eq_Adv`), which is where a
statement about `Adv` becomes a statement about this. -/
def Behaviour.AdvD (D : Set (List X)) :
    Behaviour X Y → Behaviour X Y → ℝ≥0∞ :=
  Quotient.lift₂ (PDS.AdvD D) fun _ _ _ _ h₁ h₂ => PDS.AdvD_congr h₁ h₂

@[simp] theorem Behaviour.AdvD_toBehaviour (D : Set (List X)) (S T : PDS X Y) :
    Behaviour.AdvD D (toBehaviour S) (toBehaviour T) = PDS.AdvD D S T := rfl

/-- On the systems Definition 2.14 admits, the class-level Definition-2.26
advantage is Ruling R4's metric — the coding map read at the quotient.  The
domain clause stays at the presentations, being invisible to the transcript
laws; the conclusion is an equation of class invariants. -/
theorem Behaviour.AdvD_toBehaviour_eq_advFullyDefined {D : Set (List X)}
    {S T : PDS X Y} (hS : PDS.HasDomain S D) (hT : PDS.HasDomain T D) :
    Behaviour.AdvD D (toBehaviour S) (toBehaviour T) =
      Behaviour.advFullyDefined (toBehaviour S) (toBehaviour T) :=
  (PDS.advFullyDefined_eq_AdvD hS hT).symm

/-- Lanzenberger **Definition 2.28**'s `Δ` on random systems.  Definition 2.28
already quantifies over the classes, so on the quotient it is a function of the
two points rather than a congruence (`classDistance_congr`). -/
def Behaviour.classDistance : Behaviour X Y → Behaviour X Y → ℝ≥0∞ :=
  Quotient.lift₂ PDS.classDistance fun _ _ _ _ h₁ h₂ =>
    PDS.classDistance_congr h₁ h₂

@[simp] theorem Behaviour.classDistance_toBehaviour (S T : PDS X Y) :
    Behaviour.classDistance (toBehaviour S) (toBehaviour T) =
      PDS.classDistance S T := rfl

/-- `Adv⊥ ≤ Δ` on random systems — `advFullyDefined_le_classDistance` read on
the quotient. -/
theorem Behaviour.advFullyDefined_le_classDistance (B C : Behaviour X Y) :
    Behaviour.advFullyDefined B C ≤ Behaviour.classDistance B C := by
  induction B using Behaviour.ind with | _ S =>
  induction C using Behaviour.ind with | _ T =>
  exact PDS.advFullyDefined_le_classDistance S T

/-! ## The metric on random systems -/

/-- Ruling R4's distance, symmetrized and descended.  Same construction as the
`PseudoEMetricSpace Phi` instance in `MetricFullyDefined.lean` — `Adv⊥` is
symmetric exactly at equal weight (Ruling B2), so the distance is
`Adv⊥(B, C) ⊔ Adv⊥(C, B)` — but here at an arbitrary alphabet pair and on the
quotient. -/
instance : EDist (Behaviour X Y) where
  edist B C := Behaviour.advFullyDefined B C ⊔ Behaviour.advFullyDefined C B

@[simp] theorem Behaviour.edist_toBehaviour (S T : PDS X Y) :
    edist (toBehaviour S) (toBehaviour T) =
      PDS.advFullyDefined S T ⊔ PDS.advFullyDefined T S := rfl

/-- **Notation 2.19's carrier is a metric space.**  Reflexivity is
`advFullyDefined_self`, symmetry is commutativity of `⊔`, the triangle
inequality is `advFullyDefined_triangle` once in each orientation — the three
laws of the `Phi` instance — and *separation* is
`equivalent_iff_advFullyDefined_eq_zero`, which is available only here: below
the quotient two distinct presentations of one random system are at distance
zero, which is exactly why the thesis works with the class. -/
instance : EMetricSpace (Behaviour X Y) where
  edist_self := Behaviour.ind fun S => by
    show PDS.advFullyDefined S S ⊔ PDS.advFullyDefined S S = 0
    simp
  edist_comm := Behaviour.ind₂ fun S T => by
    show PDS.advFullyDefined S T ⊔ PDS.advFullyDefined T S =
      PDS.advFullyDefined T S ⊔ PDS.advFullyDefined S T
    exact sup_comm _ _
  edist_triangle B C D := by
    induction B using Behaviour.ind with | _ S =>
    induction C using Behaviour.ind with | _ T =>
    induction D using Behaviour.ind with | _ U =>
    show PDS.advFullyDefined S U ⊔ PDS.advFullyDefined U S ≤
      (PDS.advFullyDefined S T ⊔ PDS.advFullyDefined T S) +
        (PDS.advFullyDefined T U ⊔ PDS.advFullyDefined U T)
    refine sup_le ((PDS.advFullyDefined_triangle S T U).trans
      (add_le_add le_sup_left le_sup_left)) ?_
    refine (PDS.advFullyDefined_triangle U T S).trans ?_
    rw [add_comm]
    exact add_le_add le_sup_right le_sup_right
  eq_of_edist_eq_zero {B C} h := by
    induction B using Behaviour.ind with | _ S =>
    induction C using Behaviour.ind with | _ T =>
    have h' : PDS.advFullyDefined S T ⊔ PDS.advFullyDefined T S = 0 := h
    exact toBehaviour_eq_iff.mpr
      (equivalent_iff_advFullyDefined_eq_zero.mpr
        ⟨le_antisymm (h' ▸ le_sup_left) (zero_le _),
          le_antisymm (h' ▸ le_sup_right) (zero_le _)⟩)

/-- On equal-weight random systems — in particular on any two probability laws
— the symmetrization is invisible: the metric *is* Ruling R4's `Adv⊥`. -/
theorem Behaviour.edist_eq_advFullyDefined_of_weight_eq {B C : Behaviour X Y}
    (h : Behaviour.weight B = Behaviour.weight C) :
    edist B C = Behaviour.advFullyDefined B C := by
  induction B using Behaviour.ind with | _ S =>
  induction C using Behaviour.ind with | _ T =>
  show PDS.advFullyDefined S T ⊔ PDS.advFullyDefined T S = PDS.advFullyDefined S T
  rw [PDS.advFullyDefined_comm_of_weight_eq T S h.symm, sup_idem]

/-- The metric is below the class distance, symmetrically: `Δ` is symmetric at
equal weight, so its `⊔`-symmetrization is itself. -/
theorem Behaviour.edist_le_classDistance_of_weight_eq {B C : Behaviour X Y}
    (h : Behaviour.weight B = Behaviour.weight C) :
    edist B C ≤ Behaviour.classDistance B C :=
  (Behaviour.edist_eq_advFullyDefined_of_weight_eq h).trans_le
    (Behaviour.advFullyDefined_le_classDistance B C)

end PDS

end

end RandomSystems

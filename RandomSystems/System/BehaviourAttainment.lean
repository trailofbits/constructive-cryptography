/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Attainment
import RandomSystems.System.Behaviour

/-!
# Theorems 2.31 and 2.32 read on Notation 2.19's quotient

`Attainment.lean` proves Lanzenberger's **Theorem 2.31** (`Δ(S,T) = Adv⊥(S,T)`)
and **Theorem 2.32** (the coupling theorem) at *presentations* — two PDS and a
hypothesis bundle about their supports.  `Behaviour.lean` forms Notation 2.19's
quotient `𝐒`, on which both `Δ` and `Adv⊥` are already functions of the two
points.  This file states the two theorems there, which is where the thesis
states them: Theorem 2.31 is about two *random systems*, and the objects it
equates are class invariants.

## The hypothesis bundle at the quotient

`PDS.HaveCommonDomainAndBounded S T D q` and `Distribution.NonNeg` are
properties of a *presentation*, not of the behaviour it presents: they speak
about the deterministic systems in the support and about the sign of the mass,
neither of which the transcript laws see.  So they do not descend, and the
class-level bundle is the honest existential —

  `Behaviour.HaveCommonDomainAndBounded B C D q` :=
    *some* presentation of `B` and *some* presentation of `C` are honest and
    jointly lie on Definition 2.14's common-domain, Definition 2.9's
    `q`-bounded slice.

The conclusions are unaffected by the choice, because every quantity in them
(`Behaviour.classDistance`, `Behaviour.advFullyDefined`, `edist`,
`Behaviour.weight`) is a function of the two classes.  Contrast
`Behaviour.weight`, which *is* a class invariant
(`PDS.weight_eq_of_equivalent`): that is why the normalization hypothesis of
the probability form below is stated on the class while honesty is not.

## Why nothing is re-proved here

Every endpoint is the corresponding `Attainment.lean` endpoint applied to the
representatives the bundle hands over, followed by the three `simp` equations
of `Behaviour.lean` (`Behaviour.classDistance_toBehaviour`,
`Behaviour.advFullyDefined_toBehaviour`, `Behaviour.weight_toBehaviour`).  No
induction over the quotient is used at all: `Behaviour.ind` is needed only for
statements that quantify over classes with no hypothesis producing
representatives, such as `Behaviour.advFullyDefined_le_classDistance`, and the
bundle *is* such a hypothesis.  The query induction of Theorem 2.31 is
untouched.

Two clauses of the presentation-level statements disappear on the way up, and
their disappearance is the content of Notation 2.19:

* the attainment half's `PDS.equivalent S S'` becomes `toBehaviour S' = B` —
  an attained representative is a *point of the fibre*, so the infimum
  defining `Δ` is a minimum over `toBehaviour ⁻¹' {B} × toBehaviour ⁻¹' {C}`;
* its `S'.weight = S.weight` clause becomes redundant, weight being an
  invariant of the class.

## Naming

`rep` in a theorem name abbreviates *representative*, i.e. a point of a
`toBehaviour` fibre; house vocabulary, flagged, continuing the `exists_…`
shape of the presentation-level statements.

## Honesty and the infimum

The attained pair produced below is honest (`NonNeg`, and normalized in the
probability form), and since **Ruling R9** so is every competitor:
`PDS.classDistance` infimizes over honest equivalent representatives, which is
Definition 2.28's own carrier.  The attained pair is therefore a witness *of*
that infimum rather than a witness in a smaller class than it, which is why
Theorem 2.31 transfers to the ruling verbatim.  Honesty stays a property of the
presentation and so stays inside the slice bundle — it is not visible to the
transcript laws and does not descend — while weight, which is a class
invariant, is stated on the class.
-/

namespace RandomSystems

noncomputable section

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

namespace PDS

/-! ## The finite shared-domain slice, at the quotient -/

/-- **The finite shared-domain slice for random systems.**  A pair of classes
lies on the slice when it *has* a pair of honest presentations on it:
`PDS.HaveCommonDomainAndBounded` constrains the supports and `NonNeg`
constrains the sign of the mass, and neither is visible to the transcript
laws, so neither descends to the quotient.

COINAGE (the class-level continuation of `PDS.HaveCommonDomainAndBounded`,
itself a coinage; the thesis names neither, it assumes finiteness globally).
-/
def Behaviour.HaveCommonDomainAndBounded
    (B C : Behaviour X Y) (D : Set (List X)) (q : Nat) : Prop :=
  ∃ S T : PDS X Y,
    PDS.toBehaviour S = B ∧ PDS.toBehaviour T = C ∧ S.NonNeg ∧ T.NonNeg ∧
      PDS.HaveCommonDomainAndBounded S T D q

/-- An honest pair on the slice presents a pair of classes on the slice.  This
is the only introduction rule; the slice is never established at the quotient
directly. -/
theorem HaveCommonDomainAndBounded.toBehaviour {S T : PDS X Y} {D : Set (List X)}
    {q : Nat} (h : PDS.HaveCommonDomainAndBounded S T D q)
    (hSnn : S.NonNeg) (hTnn : T.NonNeg) :
    Behaviour.HaveCommonDomainAndBounded (PDS.toBehaviour S) (PDS.toBehaviour T) D q :=
  ⟨S, T, rfl, rfl, hSnn, hTnn, h⟩

/-- The class-level slice is symmetric, its presentation-level counterpart
being so (`PDS.HaveCommonDomainAndBounded.symm`). -/
theorem Behaviour.HaveCommonDomainAndBounded.symm {B C : Behaviour X Y}
    {D : Set (List X)} {q : Nat}
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    Behaviour.HaveCommonDomainAndBounded C B D q := by
  obtain ⟨S, T, hS, hT, hSnn, hTnn, hb⟩ := h
  exact ⟨T, S, hT, hS, hTnn, hSnn, hb.symm⟩

/-- The class-level slice is inherited by a longer budget
(`PDS.HaveCommonDomainAndBounded.mono`). -/
theorem Behaviour.HaveCommonDomainAndBounded.mono {B C : Behaviour X Y}
    {D : Set (List X)} {q q' : Nat}
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) (hq : q ≤ q') :
    Behaviour.HaveCommonDomainAndBounded B C D q' := by
  obtain ⟨S, T, hS, hT, hSnn, hTnn, hb⟩ := h
  exact ⟨S, T, hS, hT, hSnn, hTnn, hb.mono hq⟩

/-! ## Lanzenberger Theorem 2.31 on random systems -/

/-- **Theorem 2.31 at the quotient.**  For two random systems presented on the
finite shared-domain slice, Definition 2.28's class distance and Ruling R4's
advantage are the same number:

  `Δ(𝐒, 𝐓) = Adv⊥(𝐒, 𝐓)`.

This is the shape the thesis states — both sides are functions of the classes,
and no representative appears.  The proof is
`PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded` at the
presentations the bundle supplies, read through the two descent equations. -/
theorem Behaviour.classDistance_eq_advFullyDefined_of_commonDomain_bounded [Fintype X]
    {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    Behaviour.classDistance B C = Behaviour.advFullyDefined B C := by
  obtain ⟨S, T, rfl, rfl, hSnn, hTnn, hb⟩ := h
  rw [Behaviour.classDistance_toBehaviour, Behaviour.advFullyDefined_toBehaviour]
  exact PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded hSnn hTnn hb

/-- **Theorem 2.31, attainment half, at the quotient.**  The infimum defining
`Δ(𝐒, 𝐓)` is attained: there are points `S'` of the fibre over `𝐒` and `T'` of
the fibre over `𝐓` whose own laws are exactly `Δ(𝐒, 𝐓)` apart.

Below the quotient this is stated with two `PDS.equivalent` clauses and two
weight clauses (`PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded`);
here the equivalences *are* fibre membership and the weight clauses are
automatic, `Behaviour.weight` being a class invariant. -/
theorem Behaviour.exists_rep_statDist_eq_classDistance_of_commonDomain_bounded [Fintype X]
    {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    ∃ S' T' : PDS X Y,
      PDS.toBehaviour S' = B ∧ PDS.toBehaviour T' = C ∧
        S'.NonNeg ∧ T'.NonNeg ∧
        ENNReal.ofReal (statDist S' T') = Behaviour.classDistance B C := by
  obtain ⟨S, T, rfl, rfl, hSnn, hTnn, hb⟩ := h
  obtain ⟨S', T', hS'nn, hT'nn, hS', hT', -, -, hattained⟩ :=
    PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded
      hSnn hTnn hb
  refine ⟨S', T', PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hS'),
    PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hT'), hS'nn, hT'nn, ?_⟩
  rw [hattained, Behaviour.classDistance_toBehaviour,
    PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded hSnn hTnn hb]

/-- **Theorem 2.31 against Definition 2.26, at the quotient.**  Lanzenberger's
own advantage `Adv` is indexed by the environments *compatible* with the two
systems, so — unlike `Adv⊥` — it is not a function of the classes and does not
descend.  The honest quotient reading is therefore at representatives: on the
slice there are presentations of `𝐒` and `𝐓` whose Definition-2.26 advantage
is the class distance.  The coding map
`PDS.advFullyDefined_eq_Adv_of_dom_eq` is what makes the two readings agree
there. -/
theorem Behaviour.exists_rep_classDistance_eq_Adv_of_commonDomain_bounded [Fintype X]
    {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    ∃ S T : PDS X Y,
      PDS.toBehaviour S = B ∧ PDS.toBehaviour T = C ∧
        Behaviour.classDistance B C = PDS.Adv S T := by
  obtain ⟨S, T, rfl, rfl, hSnn, hTnn, hb⟩ := h
  refine ⟨S, T, rfl, rfl, ?_⟩
  rw [Behaviour.classDistance_toBehaviour,
    PDS.classDistance_eq_Adv_of_commonDomain_bounded hSnn hTnn hb]

/-! ## Theorem 2.31 at the metric

`Behaviour.lean` installs `edist` as the `⊔`-symmetrization of `Adv⊥`, the
signed carrier's honest distance.  At equal weight the symmetrization is
invisible, so on the slice the `EMetricSpace` distance *is* Definition 2.28's
class distance. -/

/-- **Theorem 2.31 as a statement about the metric.**  For equal-weight random
systems on the finite shared-domain slice, the `EMetricSpace` distance of
`Behaviour X Y` is Definition 2.28's `Δ`.

This is the reading that makes Theorem 2.31 a *metric* theorem rather than a
statement about two separately defined numbers: the space whose points are
random systems carries exactly one distance, and it is the class distance. -/
theorem Behaviour.edist_eq_classDistance_of_commonDomain_bounded [Fintype X]
    {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (hweight : Behaviour.weight B = Behaviour.weight C)
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    edist B C = Behaviour.classDistance B C := by
  rw [Behaviour.edist_eq_advFullyDefined_of_weight_eq hweight,
    Behaviour.classDistance_eq_advFullyDefined_of_commonDomain_bounded h]

/-! ## Lanzenberger Theorem 2.32 on random systems -/

/-- **Theorem 2.32 (Coupling Theorem for Random Systems) at the quotient.**  On
the finite shared-domain slice, `Δ(𝐒, 𝐓)` is the disagreement probability of an
optimal coupling of two presentations: there are points `S'` of the fibre over
`𝐒` and `T'` of the fibre over `𝐓` and an honest joint law of them whose
off-diagonal mass is exactly `Δ(𝐒, 𝐓)`.

The interactive distance of two random systems is thus the probability of a
*static* event decided before any interaction — the two sampled deterministic
systems are simply unequal. -/
theorem Behaviour.exists_rep_coupling_offDiagonalMass_eq_classDistance_of_commonDomain_bounded
    [Fintype X] {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (hweight : Behaviour.weight B = Behaviour.weight C)
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    ∃ (S' T' : PDS X Y) (J : Distribution (System.DDS X Y × System.DDS X Y)),
      PDS.toBehaviour S' = B ∧ PDS.toBehaviour T' = C ∧
        S'.NonNeg ∧ T'.NonNeg ∧
        Distribution.IsCoupling J S' T' ∧ (∀ p, 0 ≤ J p) ∧
        ENNReal.ofReal (Distribution.offDiagonalMass J) =
          Behaviour.classDistance B C := by
  obtain ⟨S, T, rfl, rfl, hSnn, hTnn, hb⟩ := h
  obtain ⟨S', T', J, hS'nn, hT'nn, hS', hT', hJ, hJnn, hJmass⟩ :=
    PDS.exists_equivalent_coupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded
      hSnn hTnn hweight hb
  refine ⟨S', T', J, PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hS'),
    PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hT'), hS'nn, hT'nn, hJ, hJnn, ?_⟩
  rw [hJmass, Behaviour.classDistance_toBehaviour,
    PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded hSnn hTnn hb]

/-- **Theorem 2.32 in the thesis's own shape**: for random systems of weight
one the coupling is a genuine probability distribution.

Normalization is stated *on the classes*, unlike honesty: weight is a class
invariant, so `|𝐒| = 1` is a property of the random system, while `NonNeg` is
a property of a presentation and stays inside the slice bundle. -/
theorem Behaviour.exists_rep_probCoupling_offDiagonalMass_eq_classDistance_of_commonDomain_bounded
    [Fintype X] {B C : Behaviour X Y} {D : Set (List X)} {q : Nat}
    (hB : Behaviour.weight B = 1) (hC : Behaviour.weight C = 1)
    (h : Behaviour.HaveCommonDomainAndBounded B C D q) :
    ∃ (S' T' : PDS X Y) (J : Distribution (System.DDS X Y × System.DDS X Y)),
      J.isProbDist ∧
        PDS.toBehaviour S' = B ∧ PDS.toBehaviour T' = C ∧
        Distribution.IsCoupling J S' T' ∧
        ENNReal.ofReal (Distribution.offDiagonalMass J) =
          Behaviour.classDistance B C := by
  obtain ⟨S, T, rfl, rfl, hSnn, hTnn, hb⟩ := h
  obtain ⟨S', T', J, hJprob, hS', hT', hJ, hJmass⟩ :=
    PDS.exists_equivalent_probCoupling_offDiagonalMass_eq_advFullyDefined_of_commonDomain_bounded
      ⟨hSnn, hB⟩ ⟨hTnn, hC⟩ hb
  refine ⟨S', T', J, hJprob, PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hS'),
    PDS.toBehaviour_eq_iff.mpr (PDS.equivalent_symm hT'), hJ, ?_⟩
  rw [hJmass, Behaviour.classDistance_toBehaviour,
    PDS.classDistance_eq_advFullyDefined_of_commonDomain_bounded hSnn hTnn hb]

end PDS

end

end RandomSystems

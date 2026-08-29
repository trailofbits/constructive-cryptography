/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.Observation
import RandomSystems.Converter.Serial
import Probability.Lift
import Mathlib.Topology.EMetricSpace.Basic

set_option autoImplicit false

/-!
# Normalized random systems at query-indexed interfaces

Lanzenberger, Definition 2.14 (printed p. 15), says that a PDS “is a
distribution over `(X,Y)`-DDS” and that all DDSs in its support have the same
domain. The ambient carrier below is a different construction: DDSs return
optional answers on every attempted history, and PDSs are normalized
finite-support laws. The literal normalized common-domain specialization is
embedded separately.

The quotient identifies two ambient PDSs when every finite observation by a
DDE has the same transcript law. Converter application is deterministic
distribution transformation, and finite observation factorization proves that
it is well-defined and non-expanding. Liu--Maurer, Definition 6 (printed p. 10),
states: “An `(X,Y)`-converter `π` is a pair of sequences of conditional
probability distributions.” The deterministic converter and normalized
pushforward here are a specialization; Jost's probabilistic converters and a
general measure-theoretic carrier remain beyond this finite-support layer.
-/

namespace RandomSystems.Ambient

noncomputable section

open Probability (Distribution)
open scoped ENNReal

universe u v w z p q

/-- A normalized finite-support probability law over query-indexed DDSs. -/
abbrev PDS (A : Interface.{u, v}) :=
  Distribution.ProbDist (DDS A)

namespace PDS

variable {A : Interface.{u, v}} {B : Interface.{w, z}}

/-- The normalized point law concentrated on one DDS. -/
def ofDDS (system : DDS A) : PDS A :=
  ⟨Finsupp.single system 1, Distribution.isProbDist_single system⟩

/-- The normalized law obtained by sampling a total answer function uniformly
and viewing it as a DDS. -/
def uniformFunction (A : Interface.{u, v})
    [Fintype ((query : A.query) → A.answer query)]
    [Nonempty ((query : A.query) → A.answer query)] : PDS A :=
  ⟨Distribution.fTransform DDS.ofFunction
      (Distribution.uniform ((query : A.query) → A.answer query)),
    Distribution.fTransform_isProbDist DDS.ofFunction
      Distribution.uniform_isProbDist⟩

@[simp]
theorem coe_uniformFunction (A : Interface.{u, v})
    [Fintype ((query : A.query) → A.answer query)]
    [Nonempty ((query : A.query) → A.answer query)] :
    (uniformFunction A : Distribution (DDS A)) =
      Distribution.fTransform DDS.ofFunction
        (Distribution.uniform ((query : A.query) → A.answer query)) :=
  rfl

/-- Deterministic transformation of a normalized PDS. -/
private def fTransform (transform : DDS A → DDS B) (system : PDS A) : PDS B :=
  ⟨Distribution.fTransform transform system.1,
    Distribution.fTransform_isProbDist transform system.2⟩

@[simp]
private theorem fTransform_ofDDS_eq
    (transform : DDS A → DDS B) (system : DDS A) :
    fTransform transform (ofDDS system) = ofDDS (transform system) := by
  apply Subtype.ext
  simp [fTransform, ofDDS, Distribution.fTransform]

@[simp]
private theorem fTransform_id_eq (system : PDS A) :
    fTransform id system = system := by
  apply Subtype.ext
  exact Distribution.fTransform_id system.1

private theorem fTransform_comp_eq {C : Interface.{p, q}}
    (outer : DDS B → DDS C) (inner : DDS A → DDS B) (system : PDS A) :
    fTransform outer (fTransform inner system) =
      fTransform (outer ∘ inner) system := by
  apply Subtype.ext
  exact Distribution.fTransform_fTransform outer inner system.1

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7): “A converter α, when
applied as an interface i of a resource, induces a function Φ → Φ.” Here the
function on normalized PDSs is the pushforward of deterministic attachment. -/
def apply (converter : DDC A B) (system : PDS B) : PDS A :=
  fTransform (applySystem converter) system

@[simp]
theorem apply_ofDDS_eq (converter : DDC A B) (system : DDS B) :
    apply converter (ofDDS system) = ofDDS (applySystem converter system) :=
  fTransform_ofDDS_eq _ _

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), says that the identity
converter “induces the identity function Φ → Φ”. -/
@[simp]
theorem apply_forwarding_eq (system : PDS A) :
    apply (DDC.forwarding A) system = system := by
  -- Replace deterministic forwarding attachment by the identity function.
  unfold apply
  rw [show applySystem (DDC.forwarding A) = id by
    funext deterministicSystem
    exact applySystem_forwarding_eq A deterministicSystem]
  -- Pushforward by the identity leaves the normalized law unchanged.
  exact fTransform_id_eq system

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), requires
“(β ◦ α)ⁱ R = βⁱ (αⁱ R)”. -/
theorem apply_serial_eq {A B C : Interface.{u, v}}
    (outer : DDC A B) (inner : DDC B C) (system : PDS C) :
    apply (DDC.serial outer inner) system =
      apply outer (apply inner system) := by
  -- Combine the two deterministic distribution transformations.
  unfold apply
  rw [fTransform_comp_eq]
  -- The underlying deterministic functions agree by serial attachment.
  congr 1
  funext deterministicSystem
  exact DDC.applySystem_serial_eq outer inner deterministicSystem

/-- The finite transcript law observed from a normalized PDS. -/
def trLaw (environment : DDE A) (rounds : Nat)
    (system : PDS A) : Distribution (Transcript A) :=
  RandomSystems.Ambient.trLaw environment rounds system.1

theorem trLaw_weight_eq_one (environment : DDE A)
    (rounds : Nat) (system : PDS A) :
    (trLaw environment rounds system).weight = 1 := by
  rw [trLaw, RandomSystems.Ambient.trLaw,
    Distribution.weight_fTransform]
  exact system.2.weight_eq

private def commonInnerRounds (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) : Nat := by
  classical
  exact (left.1.support ∪ right.1.support).sup
    (DDC.Internal.innerRoundsFor converter environment outerRounds)

private theorem innerRoundsFor_le_commonInnerRounds_left
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) {system : DDS B}
    (supported : system ∈ left.1.support) :
    DDC.Internal.innerRoundsFor converter environment outerRounds system ≤
      commonInnerRounds converter environment outerRounds left right := by
  classical
  rw [commonInnerRounds]
  exact Finset.le_sup
    (f := DDC.Internal.innerRoundsFor converter environment outerRounds)
    (Finset.mem_union_left right.1.support supported)

private theorem innerRoundsFor_le_commonInnerRounds_right
    (converter : DDC A B) (environment : DDE A) (outerRounds : Nat)
    (left right : PDS B) {system : DDS B}
    (supported : system ∈ right.1.support) :
    DDC.Internal.innerRoundsFor converter environment outerRounds system ≤
      commonInnerRounds converter environment outerRounds left right := by
  classical
  rw [commonInnerRounds]
  exact Finset.le_sup
    (f := DDC.Internal.innerRoundsFor converter environment outerRounds)
    (Finset.mem_union_right left.1.support supported)

private theorem trLaw_apply_of_support (converter : DDC A B)
    (environment : DDE A) (outerRounds : Nat)
    (left right system : PDS B)
    (side : ∀ deterministicSystem ∈ system.1.support,
      DDC.Internal.innerRoundsFor converter environment outerRounds
          deterministicSystem ≤
        commonInnerRounds converter environment outerRounds left right) :
    trLaw environment outerRounds (apply converter system) =
      Distribution.fTransform
        (DDC.Internal.composedTranscriptAt converter environment outerRounds)
        (trLaw
          (DDC.Internal.composeDDEAt converter environment outerRounds)
          (commonInnerRounds converter environment outerRounds left right)
          system) := by
  unfold PDS.trLaw RandomSystems.Ambient.trLaw apply fTransform
  rw [Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  apply Distribution.fTransform_congr
  intro deterministicSystem supported
  exact DDC.Internal.transcript_applySystem_of_innerRounds_le converter environment
    outerRounds _ deterministicSystem (side deterministicSystem supported)

/-- The ambient distinguishing advantage obtained by taking the supremum over
total DDEs and finite observation lengths.

Lanzenberger, Definition 2.26 (printed p. 18), says that “the supremum is over
all compatible `(Y,X)`-DDE.”  His definition applies to two systems with the
same domain; the ambient definition below instead observes optional answers
on every attempted history. -/
def advantage (left right : PDS A) : ENNReal :=
  ⨆ environment : DDE A, ⨆ rounds : Nat,
    ENNReal.ofReal
      (Probability.statDist (trLaw environment rounds left)
        (trLaw environment rounds right))

@[simp]
theorem advantage_self (system : PDS A) : advantage system system = 0 :=
  le_antisymm
    (iSup_le fun _ => iSup_le fun _ => by simp [Probability.statDist_self])
    (zero_le _)

theorem advantage_comm (left right : PDS A) :
    advantage left right = advantage right left := by
  refine iSup_congr fun environment => iSup_congr fun rounds => ?_
  rw [Probability.statDist_symm_of_eq_weight _ _ (by
    rw [trLaw_weight_eq_one, trLaw_weight_eq_one])]

theorem advantage_triangle (left middle right : PDS A) :
    advantage left right ≤ advantage left middle + advantage middle right := by
  refine iSup_le fun environment => iSup_le fun rounds => ?_
  calc
    ENNReal.ofReal
          (Probability.statDist (trLaw environment rounds left)
            (trLaw environment rounds right))
        ≤ ENNReal.ofReal
              (Probability.statDist (trLaw environment rounds left)
                (trLaw environment rounds middle)) +
            ENNReal.ofReal
              (Probability.statDist (trLaw environment rounds middle)
                (trLaw environment rounds right)) := by
          rw [← ENNReal.ofReal_add (Probability.statDist_nonneg _ _)
            (Probability.statDist_nonneg _ _)]
          exact ENNReal.ofReal_le_ofReal (Probability.statDist_triangle _ _ _)
    _ ≤ advantage left middle + advantage middle right :=
      add_le_add
        (le_iSup_of_le environment (le_iSup_of_le rounds le_rfl))
        (le_iSup_of_le environment (le_iSup_of_le rounds le_rfl))

/-- Maurer--Renner 2016, Definition 2 (printed p. 11): “A metric d on Φ is
called non-expanding if d(αR, αS) ≤ d(R, S)”. -/
theorem advantage_apply_le (converter : DDC A B) (left right : PDS B) :
    advantage (apply converter left) (apply converter right) ≤
      advantage left right := by
  -- Fix an arbitrary outer environment and finite observation length.
  refine iSup_le fun environment => iSup_le fun rounds => ?_
  -- Factor both attached transcript laws through one common inner observation.
  rw [trLaw_apply_of_support converter environment rounds left right left
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_left converter environment rounds
          left right supported),
    trLaw_apply_of_support converter environment rounds left right right
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_right converter environment rounds
          left right supported)]
  calc
    ENNReal.ofReal
        (Probability.statDist
          (Distribution.fTransform
            (DDC.Internal.composedTranscriptAt converter environment rounds)
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right) left))
          (Distribution.fTransform
            (DDC.Internal.composedTranscriptAt converter environment rounds)
            (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
              (commonInnerRounds converter environment rounds left right)
              right)))
        ≤ ENNReal.ofReal
            (Probability.statDist
              (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
                (commonInnerRounds converter environment rounds left right)
                left)
              (trLaw (DDC.Internal.composeDDEAt converter environment rounds)
                (commonInnerRounds converter environment rounds left right)
                right)) :=
          -- Deterministic transcript transformation cannot increase distance.
          ENNReal.ofReal_le_ofReal
            (Probability.statDist_fTransform_le _ _
              (DDC.Internal.composedTranscriptAt converter environment rounds))
    _ ≤ advantage left right :=
      -- The chosen inner environment and length occur in the defining supremum.
      le_iSup_of_le (DDC.Internal.composeDDEAt converter environment rounds)
        (le_iSup_of_le
          (commonInnerRounds converter environment rounds left right) le_rfl)

/-- Lanzenberger, Definition 2.17 (printed p. 16), requires agreement “for all
compatible `(Y,X)`-DDE.” This ambient relation retains the transcript-law
clause; the literal carrier separately retains the common-domain clause. -/
def equivalent (left right : PDS A) : Prop :=
  ∀ environment : DDE A, ∀ rounds : Nat,
    trLaw environment rounds left = trLaw environment rounds right

@[refl]
theorem equivalent_refl (system : PDS A) : equivalent system system :=
  fun _ _ => rfl

@[symm]
theorem equivalent_symm {left right : PDS A}
    (hypothesis : equivalent left right) : equivalent right left :=
  fun environment rounds => (hypothesis environment rounds).symm

@[trans]
theorem equivalent_trans {left middle right : PDS A}
    (first : equivalent left middle) (second : equivalent middle right) :
    equivalent left right :=
  fun environment rounds =>
    (first environment rounds).trans (second environment rounds)

/-- Finite-observation equivalence under total DDEs is preserved by DDC
attachment. -/
theorem equivalent_apply (converter : DDC A B)
    {left right : PDS B} (hypothesis : equivalent left right) :
    equivalent (apply converter left) (apply converter right) := by
  -- Fix an outer DDE and a finite observation length.
  intro environment rounds
  -- Factor both attached observations through one common inner DDE horizon.
  rw [trLaw_apply_of_support converter environment rounds left right left
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_left converter environment rounds
          left right supported),
    trLaw_apply_of_support converter environment rounds left right right
      (fun system supported =>
        innerRoundsFor_le_commonInnerRounds_right converter environment rounds
          left right supported),
    hypothesis (DDC.Internal.composeDDEAt converter environment rounds)
      (commonInnerRounds converter environment rounds left right)]

theorem advantage_congr {left left' right right' : PDS A}
    (leftEquivalent : equivalent left left')
    (rightEquivalent : equivalent right right') :
    advantage left right = advantage left' right' := by
  refine iSup_congr fun environment => iSup_congr fun rounds => ?_
  rw [leftEquivalent environment rounds, rightEquivalent environment rounds]

theorem equivalent_iff_advantage_eq_zero {left right : PDS A} :
    equivalent left right ↔ advantage left right = 0 := by
  constructor
  · intro hypothesis
    apply le_antisymm
    · refine iSup_le fun environment => iSup_le fun rounds => ?_
      rw [hypothesis environment rounds]
      simp [Probability.statDist_self]
    · exact zero_le _
  · intro advantageZero environment rounds
    have distanceLe : ENNReal.ofReal
        (Probability.statDist (trLaw environment rounds left)
          (trLaw environment rounds right)) ≤ 0 :=
      advantageZero ▸
        le_iSup_of_le environment (le_iSup_of_le rounds le_rfl)
    have distanceZero : Probability.statDist
        (trLaw environment rounds left)
        (trLaw environment rounds right) = 0 := by
      have nonpositive := ENNReal.ofReal_eq_zero.mp
        (le_antisymm distanceLe (zero_le _))
      exact le_antisymm nonpositive (Probability.statDist_nonneg _ _)
    have reverseZero : Probability.statDist
        (trLaw environment rounds right)
        (trLaw environment rounds left) = 0 := by
      rw [Probability.statDist_symm_of_eq_weight _ _ (by
        rw [trLaw_weight_eq_one, trLaw_weight_eq_one])]
      exact distanceZero
    apply Finsupp.ext
    intro value
    have forward := Distribution.max_sub_eq_zero_of_statDist_eq_zero
      distanceZero value
    have reverse := Distribution.max_sub_eq_zero_of_statDist_eq_zero
      reverseZero value
    have forwardLe : trLaw environment rounds left value -
        trLaw environment rounds right value ≤ 0 :=
      (le_max_left _ _).trans_eq forward
    have reverseLe : trLaw environment rounds right value -
        trLaw environment rounds left value ≤ 0 :=
      (le_max_left _ _).trans_eq reverse
    linarith

/-- The setoid induced by equality at every finite observation length under
every total DDE. -/
def equivalentSetoid (A : Interface.{u, v}) : Setoid (PDS A) where
  r := equivalent
  iseqv := ⟨equivalent_refl, equivalent_symm, equivalent_trans⟩

end PDS

/-- Normalized query-indexed PDSs modulo total-DDE finite-observation
equivalence. -/
abbrev RandomSystem (A : Interface.{u, v}) :=
  Quotient (PDS.equivalentSetoid A)

namespace RandomSystem

variable {A : Interface.{u, v}} {B : Interface.{w, z}}

/-- Regard a normalized PDS presentation as a random system. -/
def ofPDS (system : PDS A) : RandomSystem A :=
  Quotient.mk (PDS.equivalentSetoid A) system

theorem ofPDS_eq_iff {left right : PDS A} :
    ofPDS left = ofPDS right ↔ PDS.equivalent left right :=
  ⟨Quotient.exact, Quotient.sound (s := PDS.equivalentSetoid A)⟩

/-- The quotient lift of Maurer--Renner 2016's converter action: “A converter
α ... induces a function Φ → Φ” (Section 3.3, printed p. 7). -/
def apply (converter : DDC A B) : RandomSystem B → RandomSystem A :=
  Quotient.map (PDS.apply converter) fun _ _ hypothesis =>
    PDS.equivalent_apply converter hypothesis

@[simp]
theorem apply_ofPDS_eq (converter : DDC A B) (system : PDS B) :
    apply converter (ofPDS system) = ofPDS (PDS.apply converter system) :=
  rfl

/-- The identity converter induces the identity on the observational quotient;
Maurer--Renner 2016, Section 3.3 (printed p. 7), calls it the converter that
“simply stands for using the resource ‘as is’.” -/
@[simp]
theorem apply_forwarding_eq (system : RandomSystem A) :
    apply (DDC.forwarding A) system = system := by
  -- Choose a normalized PDS representative.
  induction system using Quotient.ind with
  | _ presentation =>
      -- Apply the proved identity law before returning to the quotient.
      change ofPDS (PDS.apply (DDC.forwarding A) presentation) =
        ofPDS presentation
      rw [PDS.apply_forwarding_eq]

/-- Maurer--Renner 2016, Section 3.3 (printed p. 7), requires
“(β ◦ α)ⁱ R = βⁱ (αⁱ R)”; this is its quotient lift. -/
theorem apply_serial_eq {A B C : Interface.{u, v}}
    (outer : DDC A B) (inner : DDC B C)
    (system : RandomSystem C) :
    apply (DDC.serial outer inner) system =
      apply outer (apply inner system) := by
  -- Choose a normalized PDS representative.
  induction system using Quotient.ind with
  | _ presentation =>
      -- Apply the proved serial law before returning to the quotient.
      change ofPDS (PDS.apply (DDC.serial outer inner) presentation) =
        ofPDS (PDS.apply outer (PDS.apply inner presentation))
      rw [PDS.apply_serial_eq]

noncomputable instance : EDist (RandomSystem A) where
  edist := Quotient.lift₂ PDS.advantage
    fun _ _ _ _ leftEquivalent rightEquivalent =>
      PDS.advantage_congr leftEquivalent rightEquivalent

@[simp]
theorem edist_ofPDS_eq (left right : PDS A) :
    edist (ofPDS left) (ofPDS right) = PDS.advantage left right :=
  rfl

noncomputable instance : EMetricSpace (RandomSystem A) where
  edist_self := by
    -- Select a PDS representative and use reflexivity of ambient advantage.
    intro system
    induction system using Quotient.ind with
    | _ presentation => exact PDS.advantage_self presentation
  edist_comm := by
    -- Select representatives and use symmetry of ambient advantage.
    intro left right
    induction left using Quotient.ind with
    | _ leftPresentation =>
        induction right using Quotient.ind with
        | _ rightPresentation =>
            exact PDS.advantage_comm leftPresentation rightPresentation
  edist_triangle := by
    -- Select three representatives and use the ambient triangle inequality.
    intro left middle right
    induction left using Quotient.ind with
    | _ leftPresentation =>
        induction middle using Quotient.ind with
        | _ middlePresentation =>
            induction right using Quotient.ind with
            | _ rightPresentation =>
                exact PDS.advantage_triangle leftPresentation
                  middlePresentation rightPresentation
  eq_of_edist_eq_zero {left right} equal := by
    -- Select representatives and turn zero advantage into observational equivalence.
    induction left using Quotient.ind with
    | _ leftPresentation =>
        induction right using Quotient.ind with
        | _ rightPresentation =>
            apply ofPDS_eq_iff.mpr
            exact PDS.equivalent_iff_advantage_eq_zero.mpr equal

/-- The quotient distance satisfies Maurer--Renner 2016, Definition 2
(printed p. 11): “d(αR, αS) ≤ d(R, S)”. -/
theorem edist_apply_le (converter : DDC A B)
    (left right : RandomSystem B) :
    edist (apply converter left) (apply converter right) ≤ edist left right := by
  -- Choose normalized PDS representatives of both random systems.
  induction left using Quotient.ind with
  | _ leftPresentation =>
    induction right using Quotient.ind with
    | _ rightPresentation =>
        -- Apply non-expansion of the ambient PDS advantage.
        exact PDS.advantage_apply_le converter leftPresentation
            rightPresentation

end RandomSystem

end

end RandomSystems.Ambient

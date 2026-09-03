import Probability.SignedCoupling
import RandomSystems.Uniform
import RandomSystems.Converter.RandomSystem
import RandomSystems.Distance

noncomputable section

/-!
# Coupling and difference bounds for random systems

Coupling remains the primary joint-law technique in this module.  Signed
intermediate distributions add a complementary difference route: transcript
observation is a positive, weight-preserving linear pushforward, so signed
`L¹` contraction bounds every finite observation directly.

The system model is the ambient normalized PDS carrier.  This is weaker than
choosing the optimal same-domain representatives in Lanzenberger--Maurer,
Theorem 1 (printed p. 14): the theorem below applies to every pair of defining
PDS distributions, hence provides the hard inequality before minimizing over
representatives.  Jost's abstract resource development does not require a
particular lower-layer representation of distance and neither requires nor
rules out signed intermediate proof objects; signedness is confined here to
the already real-valued distribution carrier, while endpoint PDSs remain
normalized and nonnegative.
-/

namespace RandomSystems.Ambient
namespace PDS

universe u v

/-- Every ambient random-system observation is bounded by the statistical
 distance of the PDSs' defining distributions.

This is the hard direction underlying Lanzenberger--Maurer, Theorem 1
(printed p. 14), specialized to fixed defining representatives.  The proof
follows *Signed Couplings: Distribution Differences as Proof Objects*,
Advantage Corollary, §3, printed p. 3: transcript pushforward contracts signed
`L¹`, after which the weight-zero estimate bounds the final test. -/
theorem advantage_le_statDist {A : Interface.{u, v}} (left right : PDS A) :
    advantage left right ≤ Probability.statDist left.1 right.1 := by
  unfold advantage
  refine csSup_le ?_ ?_
  · exact ⟨_, ⟨((fun _ => none), 0), rfl⟩⟩
  · rintro value ⟨⟨environment, rounds⟩, rfl⟩
    let observe : DDS A → Transcript A := fun system =>
      RandomSystems.Ambient.transcript system environment rounds
    have hweight : left.1.weight = right.1.weight :=
      left.2.weight_eq.trans right.2.weight_eq.symm
    have hobserveWeight :
        (Probability.Distribution.fTransform observe left.1).weight =
          (Probability.Distribution.fTransform observe right.1).weight := by
      rw [Probability.Distribution.weight_fTransform,
        Probability.Distribution.weight_fTransform, hweight]
    have hmapSub :
        Probability.Distribution.fTransform observe (left.1 - right.1) =
          Probability.Distribution.fTransform observe left.1 -
            Probability.Distribution.fTransform observe right.1 :=
      (Probability.Distribution.fTransformLinear observe).map_sub left.1 right.1
    change Probability.statDist
        (Probability.Distribution.fTransform observe left.1)
        (Probability.Distribution.fTransform observe right.1) ≤
      Probability.statDist left.1 right.1
    calc
      Probability.statDist
          (Probability.Distribution.fTransform observe left.1)
          (Probability.Distribution.fTransform observe right.1) =
          (1 / 2 : ℝ) * Probability.Distribution.l1Norm
            (Probability.Distribution.fTransform observe left.1 -
              Probability.Distribution.fTransform observe right.1) :=
        Probability.Distribution.statDist_eq_half_l1Norm_of_weight_eq _ _
          hobserveWeight
      _ = (1 / 2 : ℝ) * Probability.Distribution.l1Norm
          (Probability.Distribution.fTransform observe (left.1 - right.1)) := by
        rw [hmapSub]
      _ ≤ (1 / 2 : ℝ) * Probability.Distribution.l1Norm (left.1 - right.1) :=
        mul_le_mul_of_nonneg_left
          (Probability.Distribution.l1Norm_fTransform_le observe (left.1 - right.1))
          (by norm_num)
      _ = Probability.statDist left.1 right.1 :=
        (Probability.Distribution.statDist_eq_half_l1Norm_of_weight_eq _ _
          hweight).symm
/-- The representative-attainment clause of Lanzenberger--Maurer Theorem 1,
separated as data because the ambient library also studies PDS presentations
without a common source domain.

Lanzenberger--Maurer, Theorem 1 (printed p. 14), states that representatives
`S ∈ 𝒮` and `T ∈ 𝒯` exist with `δ(S,T) = Adv(𝒮,𝒯)`.  Here membership in a
random-system equivalence class is the existing finite-observation relation
`PDS.equivalent`. -/
structure OptimalRepresentatives {A : Interface.{u, v}} (left right : PDS A) where
  leftRep : PDS A
  rightRep : PDS A
  leftEquivalent : equivalent left leftRep
  rightEquivalent : equivalent right rightRep
  statDist_eq_advantage :
    Probability.statDist leftRep.1 rightRep.1 = advantage left right

/-- A first-class system-level coupling: the marginals are defining PDS
representatives of the two observational equivalence classes.

This is the repository form of Lanzenberger--Maurer, Theorem 2 (Coupling
Theorem for Random Systems, printed p. 14): “there exist PDS `S ∈ 𝒮` and
`T ∈ 𝒯` with a joint distribution ... such that
`Adv(𝒮,𝒯) = Pr(S ≠ T)`.” -/
structure RepresentativeCoupling {A : Interface.{u, v}} (left right : PDS A) where
  leftRep : PDS A
  rightRep : PDS A
  leftEquivalent : equivalent left leftRep
  rightEquivalent : equivalent right rightRep
  joint : Probability.Distribution (DDS A × DDS A)
  nonNeg : joint.NonNeg
  isCoupling : Probability.Distribution.IsCoupling joint leftRep.1 rightRep.1

/-- Disagreement mass of a system-level representative coupling.  This uses
the support-finite `offDiagonalMass`, rather than the older bundled
`Probability.Coupling.prDisagree`, because the deterministic-system carrier is
not a finite type. -/
def RepresentativeCoupling.prDisagree {A : Interface.{u, v}}
    {left right : PDS A} (C : RepresentativeCoupling left right) : ℝ :=
  Probability.Distribution.offDiagonalMass C.joint

/-- The construction step of the Coupling Theorem: an optimal representative
pair and the classical optimal-coupling lemma produce a representative
coupling whose failure probability is exactly distinguishing advantage.

The source explicitly calls Theorem 2 an immediate consequence of Theorem 1
and the classical Coupling Lemma (Lanzenberger--Maurer, printed p. 14). -/
theorem exists_representativeCoupling_of_optimalRepresentatives
    {A : Interface.{u, v}} {left right : PDS A}
    (optimal : OptimalRepresentatives left right) :
    ∃ C : RepresentativeCoupling left right,
      C.prDisagree = advantage left right := by
  have hweight : optimal.leftRep.1.weight = optimal.rightRep.1.weight :=
    optimal.leftRep.2.weight_eq.trans optimal.rightRep.2.weight_eq.symm
  obtain ⟨joint, hcoupling, hnonneg, hoff⟩ :=
    Probability.exists_coupling_offDiagonalMass_eq
      optimal.leftRep.2.nonNeg optimal.rightRep.2.nonNeg hweight
  let C : RepresentativeCoupling left right :=
    { leftRep := optimal.leftRep
      rightRep := optimal.rightRep
      leftEquivalent := optimal.leftEquivalent
      rightEquivalent := optimal.rightEquivalent
      joint := joint
      nonNeg := hnonneg
      isCoupling := hcoupling }
  refine ⟨C, ?_⟩
  calc
    C.prDisagree = Probability.statDist optimal.leftRep.1 optimal.rightRep.1 := hoff
    _ = advantage left right := optimal.statDist_eq_advantage

/-- Exact representative couplings characterize optimal representatives.
The reverse implication uses the Signed-Difference Advantage bound for the
hard direction and the ordinary coupling bound for the easy direction. -/
theorem exists_representativeCoupling_iff_optimalRepresentatives
    {A : Interface.{u, v}} {left right : PDS A} :
    (∃ C : RepresentativeCoupling left right,
        C.prDisagree = advantage left right) ↔
      Nonempty (OptimalRepresentatives left right) := by
  constructor
  · rintro ⟨C, hC⟩
    have hadvantage :
        advantage left right = advantage C.leftRep C.rightRep :=
      advantage_congr C.leftEquivalent C.rightEquivalent
    have hlower :
        Probability.statDist C.leftRep.1 C.rightRep.1 ≤ advantage left right := by
      calc
        Probability.statDist C.leftRep.1 C.rightRep.1 ≤
            Probability.Distribution.offDiagonalMass C.joint :=
          Probability.statDist_le_offDiagonalMass C.isCoupling C.nonNeg
        _ = C.prDisagree := rfl
        _ = advantage left right := hC
    have hupper :
        advantage left right ≤
          Probability.statDist C.leftRep.1 C.rightRep.1 := by
      calc
        advantage left right = advantage C.leftRep C.rightRep := hadvantage
        _ ≤ Probability.statDist C.leftRep.1 C.rightRep.1 :=
          advantage_le_statDist C.leftRep C.rightRep
    exact ⟨
      { leftRep := C.leftRep
        rightRep := C.rightRep
        leftEquivalent := C.leftEquivalent
        rightEquivalent := C.rightEquivalent
        statDist_eq_advantage := le_antisymm hlower hupper }⟩
  · rintro ⟨optimal⟩
    exact exists_representativeCoupling_of_optimalRepresentatives optimal

/-- Coupling remains available without representative attainment: coupling the
current defining distributions gives an ordinary failure event that upper
bounds distinguishing advantage. -/
theorem exists_representativeCoupling_advantage_le
    {A : Interface.{u, v}} (left right : PDS A) :
    ∃ C : RepresentativeCoupling left right,
      advantage left right ≤ C.prDisagree := by
  have hweight : left.1.weight = right.1.weight :=
    left.2.weight_eq.trans right.2.weight_eq.symm
  obtain ⟨joint, hcoupling, hnonneg, hoff⟩ :=
    Probability.exists_coupling_offDiagonalMass_eq
      left.2.nonNeg right.2.nonNeg hweight
  let C : RepresentativeCoupling left right :=
    { leftRep := left
      rightRep := right
      leftEquivalent := equivalent_refl left
      rightEquivalent := equivalent_refl right
      joint := joint
      nonNeg := hnonneg
      isCoupling := hcoupling }
  refine ⟨C, ?_⟩
  calc
    advantage left right ≤ Probability.statDist left.1 right.1 :=
      advantage_le_statDist left right
    _ = C.prDisagree := hoff.symm


end PDS
end RandomSystems.Ambient

namespace RandomSystems
namespace PDS

universe u v

/-- On the fixed-interface PDS carrier, normalized endpoints satisfy the same
coupling-free Advantage Corollary: observation pushforward contracts the signed
difference, so no transcript test exceeds the defining statistical distance.

This is *Signed Couplings: Distribution Differences as Proof Objects*,
Advantage Corollary (printed p. 3), in the repository's literal
Lanzenberger-style PDS/DDE model. -/
theorem advantage_le_statDist_of_isProbDist {X : Type u} {Y : Type v}
    (left right : PDS X Y) (hleft : left.isProbDist)
    (hright : right.isProbDist) :
    advantage left right ≤ Probability.statDist left right := by
  classical
  unfold advantage
  refine Probability.sSup_image_univ_le_of_forall _
    (Probability.statDist_nonneg left right) ?_
  intro environment
  let observe : System.DDS X Y → Option (System.Transcript X Y) :=
    fun system => (System.tr environment.1 system).toOption
  have hweight : left.weight = right.weight :=
    hleft.weight_eq.trans hright.weight_eq.symm
  have hobserveWeight :
      (Probability.Distribution.fTransform observe left).weight =
        (Probability.Distribution.fTransform observe right).weight := by
    rw [Probability.Distribution.weight_fTransform,
      Probability.Distribution.weight_fTransform, hweight]
  have hmapSub :
      Probability.Distribution.fTransform observe (left - right) =
        Probability.Distribution.fTransform observe left -
          Probability.Distribution.fTransform observe right :=
    (Probability.Distribution.fTransformLinear observe).map_sub left right
  unfold trLaw
  change Probability.statDist
      (Probability.Distribution.fTransform observe left)
      (Probability.Distribution.fTransform observe right) ≤
    Probability.statDist left right
  calc
    Probability.statDist
        (Probability.Distribution.fTransform observe left)
        (Probability.Distribution.fTransform observe right) =
        (1 / 2 : ℝ) * Probability.Distribution.l1Norm
          (Probability.Distribution.fTransform observe left -
            Probability.Distribution.fTransform observe right) :=
      Probability.Distribution.statDist_eq_half_l1Norm_of_weight_eq _ _
        hobserveWeight
    _ = (1 / 2 : ℝ) * Probability.Distribution.l1Norm
        (Probability.Distribution.fTransform observe (left - right)) := by
      rw [hmapSub]
    _ ≤ (1 / 2 : ℝ) * Probability.Distribution.l1Norm (left - right) :=
      mul_le_mul_of_nonneg_left
        (Probability.Distribution.l1Norm_fTransform_le observe (left - right))
        (by norm_num)
    _ = Probability.statDist left right :=
      (Probability.Distribution.statDist_eq_half_l1Norm_of_weight_eq _ _
        hweight).symm

open Probability

/-- Adding two independent uniform functions pointwise has zero distinguishing advantage
from one uniform random function.  This is the unfolded `xorUniformFunctions` distribution. -/
theorem advantage_addUniformFunctions_urf_le_zero
    (X : Type u) (Y : Type v)
    [Fintype X] [DecidableEq X] [Fintype Y] [AddCommGroup Y] :
    PDS.advantage
      (Distribution.fTransform
        (fun pair : (X → Y) × (X → Y) =>
          System.functionEvaluator (fun x => pair.1 x + pair.2 x))
        (Distribution.prod (Distribution.uniform (X → Y))
          (Distribution.uniform (X → Y))))
      (PDS.urf X Y) ≤ 0 := by
  classical
  let source : Distribution ((X → Y) × (X → Y)) :=
    Distribution.prod (Distribution.uniform (X → Y)) (Distribution.uniform (X → Y))
  let output : ((X → Y) × (X → Y)) → X → Y := fun pair => pair.1 + pair.2
  let left : PDS X Y := Distribution.fTransform (System.functionEvaluator ∘ output) source
  change PDS.advantage left (PDS.urf X Y) ≤ 0
  let shear : ((X → Y) × (X → Y)) ≃ ((X → Y) × (X → Y)) :=
    { toFun := fun pair => (pair.1, pair.1 + pair.2)
      invFun := fun pair => (pair.1, -pair.1 + pair.2)
      left_inv := by rintro ⟨f, g⟩; simp
      right_inv := by rintro ⟨f, g⟩; simp }
  have outputUniform : Distribution.fTransform output source =
      Distribution.uniform (X → Y) := by
    rw [show source = Distribution.uniform ((X → Y) × (X → Y)) by
      simp [source, Distribution.prod_uniform]]
    change Distribution.fTransform (Prod.snd ∘ shear) _ = _
    rw [← Distribution.fTransform_fTransform, Distribution.fTransform_equiv_uniform,
      Distribution.fTransform_snd_uniform]
  have systemsEqual : left = PDS.urf X Y := by
    change Distribution.fTransform (System.functionEvaluator ∘ output) source =
      Distribution.fTransform System.functionEvaluator (Distribution.uniform (X → Y))
    rw [← Distribution.fTransform_fTransform, outputUniform]
  calc
    _ ≤ statDist left (PDS.urf X Y) := advantage_le_statDist_of_isProbDist _ _
      (by rw [systemsEqual]; exact PDS.isProbDist_urf X Y) (PDS.isProbDist_urf X Y)
    _ = 0 := by rw [systemsEqual, statDist_self]

end PDS
end RandomSystems

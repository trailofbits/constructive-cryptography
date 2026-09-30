import Mathlib.Algebra.BigOperators.Ring.Finset
import Commons.Schemes.Lattice.VectorBackend
import Mathlib.RingTheory.AdjoinRoot

/-!
# Certified NTTs

Adapted from VCVio (`Verified-zkEVM/VCVio`, `LatticeCrypto/Ring/NTTCert.lean` at `f5119c6`), by Quang Dao.

The structure shared by the concrete NTTs of ML-KEM and ML-DSA. A `ButterflyLayout` partitions the
coefficient coordinates into pairs, and a `ScaledStage` is one layer of butterflies on such a
partition together with its inverse, which cancels it up to a scalar. Composing stages gives the
forward and inverse transforms, their additivity and the inverse law after the final
normalization; the stages also run on coefficient vectors, which is how the schemes compute them.

A transform built from butterflies evaluates: after its stages, a segment of coefficients read as a
polynomial agrees with the input polynomial at the roots of the segment's modulus, in every
commutative algebra over the coefficients. Negacyclic products evaluate multiplicatively at the
roots of `X^n + 1`, and in `R[X]/(X² − γ)` the coordinates of `a₀ + a₁ω` are unique, which turns
evaluations back into coefficients.

## Main definitions

* `applyCoeffTransform`: a transform of coefficient functions on a polynomial backend
* `ButterflyLayout`, `ScaledStage`, `forwardStages`, `inverseStages`: butterfly layers and their
  composites
* `forwardStagesVec`, `inverseStagesVec`: the composites on coefficient vectors
* `segmentEval`: the evaluation of a segment of coefficients

## Main statements

* `scale_inverseStages_forwardStages`: the normalized inverse cancels the forward stages
* `segmentEval_butterfly`: a butterfly preserves evaluations
* `segmentEval_negacyclicConv`: negacyclic products evaluate multiplicatively
* `adjoinRoot_pair_injective`: coordinates in `R[X]/(X² − γ)` are unique
-/




namespace LatticeCrypto.NTTCert

universe u

variable {Coeff : Type u} {backend : LatticeCrypto.PolyBackend Coeff}

/-! ## Coefficient-function transforms -/

/-- Lift a transformation on `Fin`-indexed coefficient functions to an
arbitrary polynomial backend.  Unlike unfolding a nested stage list through
`Vector.ofFn`, this boundary keeps wrapper proofs at constant elaboration
depth. -/
def applyCoeffTransform (backend : LatticeCrypto.PolyBackend Coeff)
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    (input : backend.Poly) : backend.Poly :=
  backend.build (transform (backend.coeff input))

/-- Lift a coefficient-level roundtrip through a polynomial backend. -/
theorem applyCoeffTransform_comp
    (forward inverse : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    (hroundtrip : ∀ input, inverse (forward input) = input)
    (input : backend.Poly) :
    applyCoeffTransform backend inverse (applyCoeffTransform backend forward input) = input := by
  unfold applyCoeffTransform
  have hcoeff : backend.coeff (backend.build (forward (backend.coeff input))) =
      forward (backend.coeff input) := by
    funext coord
    exact backend.coeff_build _ coord
  rw [hcoeff, hroundtrip, backend.build_coeff]

/-- Lift additivity of a coefficient transformation through a backend whose
addition is pointwise on coefficients. -/
theorem applyCoeffTransform_add
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Add Coeff]
    [Add backend.Poly]
    (hcoeffAdd : ∀ left right : backend.Poly,
      backend.coeff (left + right) = backend.coeff left + backend.coeff right)
    (htransformAdd : ∀ left right, transform (left + right) =
      transform left + transform right)
    (left right : backend.Poly) :
    applyCoeffTransform backend transform (left + right) =
      applyCoeffTransform backend transform left + applyCoeffTransform backend transform right := by
  unfold applyCoeffTransform
  rw [hcoeffAdd left right, htransformAdd]
  rw [← backend.build_coeff
    (backend.build (transform (backend.coeff left)) +
      backend.build (transform (backend.coeff right)))]
  congr 1
  rw [hcoeffAdd]
  funext coord
  simp only [backend.coeff_build, Pi.add_apply]

/-- Lift subtraction preservation through a pointwise backend. -/
theorem applyCoeffTransform_sub
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Sub Coeff]
    [Sub backend.Poly]
    (hcoeffSub : ∀ left right : backend.Poly,
      backend.coeff (left - right) = backend.coeff left - backend.coeff right)
    (htransformSub : ∀ left right, transform (left - right) =
      transform left - transform right)
    (left right : backend.Poly) :
    applyCoeffTransform backend transform (left - right) =
      applyCoeffTransform backend transform left - applyCoeffTransform backend transform right := by
  unfold applyCoeffTransform
  rw [hcoeffSub left right, htransformSub]
  rw [← backend.build_coeff
    (backend.build (transform (backend.coeff left)) -
      backend.build (transform (backend.coeff right)))]
  congr 1
  rw [hcoeffSub]
  funext coord
  simp only [backend.coeff_build, Pi.sub_apply]

/-- Lift zero preservation through a pointwise backend. -/
theorem applyCoeffTransform_zero
    (transform : (Fin backend.degree → Coeff) → (Fin backend.degree → Coeff))
    [Zero Coeff]
    [Zero backend.Poly]
    (hcoeffZero : backend.coeff (0 : backend.Poly) = 0)
    (htransformZero : transform 0 = 0) :
    applyCoeffTransform backend transform 0 = 0 := by
  unfold applyCoeffTransform
  rw [hcoeffZero, htransformZero]
  calc
    backend.build 0 = backend.build (backend.coeff 0) := congrArg backend.build hcoeffZero.symm
    _ = 0 := backend.build_coeff 0

/-! ## Structural butterfly certificates -/

universe v w

variable {R : Type*} [CommRing R]

/-- A partition of the coefficient coordinates `Coord` into pairs indexed by
`Pair`.  `false` names the left coordinate and `true` the right coordinate.

Using an equivalence rather than separate index functions packages coverage,
disjointness, and uniqueness in the form needed by a butterfly-stage proof. -/
structure ButterflyLayout (Pair : Type v) (Coord : Type w) where
  equiv : Pair × Bool ≃ Coord

/-- The standard blocked NTT layout.  A pair is a block number and an offset
inside that block; its coordinates are
`group * (2 * len) + offset` and that index plus `len`.

This layout is directly usable by the nested `start`/`j` loops in the FIPS 203
and FIPS 204 kernels and packages their coverage/disjointness arithmetic. -/
def blockLayout (groups len : Nat) :
    ButterflyLayout (Fin groups × Fin len) (Fin (groups * (2 * len))) where
  equiv := (Equiv.prodAssoc (Fin groups) (Fin len) Bool).trans
    ((Equiv.refl (Fin groups)).prodCongr (Equiv.prodComm (Fin len) Bool) |>.trans
      ((Equiv.refl (Fin groups)).prodCongr
        ((finTwoEquiv.symm.prodCongr (Equiv.refl (Fin len))).trans finProdFinEquiv) |>.trans
          finProdFinEquiv))

@[simp] theorem blockLayout_left_val (groups len : Nat)
    (group : Fin groups) (offset : Fin len) :
    ((blockLayout groups len).equiv ((group, offset), false)).val =
      group.val * (2 * len) + offset.val := by
  have h : offset.val + 2 * len * group.val = group.val * (2 * len) + offset.val := by
    ac_rfl
  simpa [blockLayout, finProdFinEquiv, finTwoEquiv] using h

@[simp] theorem blockLayout_right_val (groups len : Nat)
    (group : Fin groups) (offset : Fin len) :
    ((blockLayout groups len).equiv ((group, offset), true)).val =
      group.val * (2 * len) + len + offset.val := by
  have h : offset.val + len + 2 * len * group.val =
      group.val * (2 * len) + len + offset.val := by
    ac_rfl
  simpa [blockLayout, finProdFinEquiv, finTwoEquiv] using h

/-- The forward two-coordinate butterfly `(u, v) ↦ (u + z*v, u - z*v)`. -/
def forwardButterfly (z u v : R) : Bool → R
  | false => u + z * v
  | true => u - z * v

/-- The inverse-oriented two-coordinate butterfly
`(x, y) ↦ (x + y, z⁻¹*(x - y))`.

Some concrete NTT specifications write the second coordinate as
`(-z⁻¹) * (y - x)`; that expression is propositionally equal to this one. -/
def inverseButterfly (zInv x y : R) : Bool → R
  | false => x + y
  | true => zInv * (x - y)

/-- The same inverse butterfly with the right-minus-left convention used by
the ML-KEM loop.  Its coefficient is the *negation* of the `zInv` expected by
`inverseButterfly`; keeping this spelling explicit prevents a sign convention
from being hidden in a concrete refinement proof. -/
def inverseButterflyRev (zRev x y : R) : Bool → R
  | false => x + y
  | true => zRev * (y - x)

theorem inverseButterflyRev_eq (zRev x y : R) :
    inverseButterflyRev zRev x y = inverseButterfly (-zRev) x y := by
  funext side
  cases side <;> simp only [inverseButterflyRev, inverseButterfly]
  ring

/-- Apply one forward butterfly to every pair in a layout. -/
def forwardStage {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (z : Pair → R)
    (input : Coord → R) : Coord → R := fun coord =>
  let pairSide := layout.equiv.symm coord
  forwardButterfly (z pairSide.1)
    (input (layout.equiv (pairSide.1, false)))
    (input (layout.equiv (pairSide.1, true))) pairSide.2

/-- Apply one inverse butterfly to every pair in a layout. -/
def inverseStage {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (zInv : Pair → R)
    (input : Coord → R) : Coord → R := fun coord =>
  let pairSide := layout.equiv.symm coord
  inverseButterfly (zInv pairSide.1)
    (input (layout.equiv (pairSide.1, false)))
    (input (layout.equiv (pairSide.1, true))) pairSide.2

/-- Inverse stage using ML-KEM's right-minus-left spelling. -/
def inverseStageRev {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (zRev : Pair → R)
    (input : Coord → R) : Coord → R := fun coord =>
  let pairSide := layout.equiv.symm coord
  inverseButterflyRev (zRev pairSide.1)
    (input (layout.equiv (pairSide.1, false)))
    (input (layout.equiv (pairSide.1, true))) pairSide.2

theorem inverseStageRev_eq {Pair : Type v} {Coord : Type w}
    (layout : ButterflyLayout Pair Coord) (zRev : Pair → R) :
    inverseStageRev layout zRev = inverseStage layout (fun pair => -zRev pair) := by
  funext input coord
  simp only [inverseStageRev, inverseStage]
  exact congrFun (inverseButterflyRev_eq _ _ _) _

/-- Pointwise scalar multiplication for coefficient functions. -/
def scaleCoeffs {Coord : Type w} (c : R) (input : Coord → R) : Coord → R :=
  fun coord => c * input coord

/-- A matching inverse butterfly cancels a forward butterfly up to the factor
`2` introduced by the unnormalised sum/difference convention. -/
theorem inverseButterfly_forwardButterfly
    (z zInv u v : R) (hz : zInv * z = 1) :
    inverseButterfly zInv (forwardButterfly z u v false)
        (forwardButterfly z u v true) =
      fun side => scaleCoeffs (2 : R) (fun b => if b then v else u) side := by
  funext side
  cases side <;>
    simp only [inverseButterfly, forwardButterfly, scaleCoeffs]
  · simp only [Bool.false_eq_true, ↓reduceIte]
    ring
  · calc
      zInv * (u + z * v - (u - z * v)) = zInv * (z * v + z * v) := by ring
      _ = (zInv * z) * v + (zInv * z) * v := by ring
      _ = 2 * v := by rw [hz]; ring

/-- Matching inverse and forward stages cancel pointwise up to multiplication
by `2`.  The only concrete algebraic obligation is the per-pair twiddle inverse
law; all schedule coverage and non-overlap follows from `layout.equiv`. -/
theorem inverseStage_forwardStage
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z zInv : Pair → R) (hz : ∀ pair, zInv pair * z pair = 1)
    (input : Coord → R) :
    inverseStage layout zInv (forwardStage layout z input) =
      scaleCoeffs (2 : R) input := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [inverseStage, forwardStage, inverseButterfly, forwardButterfly, scaleCoeffs,
      Equiv.symm_apply_apply]
  · ring
  · calc
      zInv pair *
          (input (layout.equiv (pair, false)) +
              z pair * input (layout.equiv (pair, true)) -
            (input (layout.equiv (pair, false)) -
              z pair * input (layout.equiv (pair, true)))) =
        zInv pair *
          (z pair * input (layout.equiv (pair, true)) +
            z pair * input (layout.equiv (pair, true))) := by ring
      _ =
          (zInv pair * z pair) * input (layout.equiv (pair, true)) +
            (zInv pair * z pair) * input (layout.equiv (pair, true)) := by ring
      _ = 2 * input (layout.equiv (pair, true)) := by rw [hz]; ring

/-- A stage commutes with pointwise scalar multiplication. -/
theorem inverseStage_scaleCoeffs
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (zInv : Pair → R) (c : R) (input : Coord → R) :
    inverseStage layout zInv (scaleCoeffs c input) =
      scaleCoeffs c (inverseStage layout zInv input) := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [inverseStage, inverseButterfly, scaleCoeffs, Equiv.symm_apply_apply]
  <;> ring

/-- A forward butterfly stage is additive. -/
theorem forwardStage_add
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) (left right : Coord → R) :
    forwardStage layout z (left + right) =
      forwardStage layout z left + forwardStage layout z right := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.add_apply]
  <;> ring

/-- A forward butterfly stage preserves subtraction. -/
theorem forwardStage_sub
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) (left right : Coord → R) :
    forwardStage layout z (left - right) =
      forwardStage layout z left - forwardStage layout z right := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.sub_apply]
  <;> ring

/-- A forward butterfly stage preserves zero. -/
theorem forwardStage_zero
    {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z : Pair → R) :
    forwardStage layout z 0 = 0 := by
  funext coord
  rw [← layout.equiv.apply_symm_apply coord]
  obtain ⟨pair, side⟩ := layout.equiv.symm coord
  cases side <;>
    simp only [forwardStage, forwardButterfly, Equiv.symm_apply_apply, Pi.zero_apply, mul_zero,
      add_zero, sub_zero]

/-- Package the two laws needed to compose an unnormalised transform stage:
the inverse/forward roundtrip and compatibility of the inverse with a scalar
accumulated by inner stages. -/
structure ScaledStage (R : Type*) [CommRing R] (Coord : Type w) where
  forward : (Coord → R) → (Coord → R)
  inverse : (Coord → R) → (Coord → R)
  scalar : R
  inverse_forward : ∀ input, inverse (forward input) = scaleCoeffs scalar input
  inverse_scale : ∀ c input,
    inverse (scaleCoeffs c input) = scaleCoeffs c (inverse input)
  forward_add : ∀ left right, forward (left + right) = forward left + forward right
  forward_sub : ∀ left right, forward (left - right) = forward left - forward right
  forward_zero : forward 0 = 0

/-- Build a composable stage certificate from a butterfly layout and matching
twiddle tables.  For ML-KEM's syntactic `zRev * (y - x)`, the `zInv` supplied
here must be `-zRev`; for ML-DSA it is the coefficient already multiplying
`(x - y)`.  In both cases the obligation is explicitly `zInv * z = 1`. -/
def butterflyStage {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z zInv : Pair → R) (hz : ∀ pair, zInv pair * z pair = 1) :
    ScaledStage R Coord where
  forward := forwardStage layout z
  inverse := inverseStage layout zInv
  scalar := 2
  inverse_forward := inverseStage_forwardStage layout z zInv hz
  inverse_scale := inverseStage_scaleCoeffs layout zInv
  forward_add := forwardStage_add layout z
  forward_sub := forwardStage_sub layout z
  forward_zero := forwardStage_zero layout z

/-- Build a stage certificate using the right-minus-left inverse spelling of
the ML-KEM loop.  The sign is visible in the required twiddle law:
`(-zRev pair) * z pair = 1`. -/
def butterflyStageRev {Pair : Type v} {Coord : Type w} (layout : ButterflyLayout Pair Coord)
    (z zRev : Pair → R) (hz : ∀ pair, (-zRev pair) * z pair = 1) :
    ScaledStage R Coord where
  forward := forwardStage layout z
  inverse := inverseStageRev layout zRev
  scalar := 2
  inverse_forward := by
    rw [inverseStageRev_eq]
    exact inverseStage_forwardStage layout z (fun pair => -zRev pair) hz
  inverse_scale := by
    rw [inverseStageRev_eq]
    exact inverseStage_scaleCoeffs layout (fun pair => -zRev pair)
  forward_add := forwardStage_add layout z
  forward_sub := forwardStage_sub layout z
  forward_zero := forwardStage_zero layout z

/-- Apply a list of stages from left to right. -/
def forwardStages {Coord : Type w} : List (ScaledStage R Coord) →
    (Coord → R) → (Coord → R)
  | [], input => input
  | stage :: stages, input => forwardStages stages (stage.forward input)

/-- Apply the inverse stages in reverse order. -/
def inverseStages {Coord : Type w} : List (ScaledStage R Coord) →
    (Coord → R) → (Coord → R)
  | [], input => input
  | stage :: stages, input => stage.inverse (inverseStages stages input)

/-- Product of the scale factors introduced by a list of stages, in the order
in which the corresponding inverse stages expose them. -/
def stageScalar {Coord : Type w} : List (ScaledStage R Coord) → R
  | [] => 1
  | stage :: stages => stageScalar stages * stage.scalar

/-- A reverse sequence of certified inverse stages cancels its forward stage
sequence, accumulating only the product of the per-stage scale factors. -/
theorem inverseStages_forwardStages {Coord : Type w}
    (stages : List (ScaledStage R Coord)) (input : Coord → R) :
    inverseStages stages (forwardStages stages input) =
      scaleCoeffs (stageScalar stages) input := by
  induction stages generalizing input with
  | nil =>
      funext coord
      simp [inverseStages, forwardStages, stageScalar, scaleCoeffs]
  | cons stage stages ih =>
      simp only [forwardStages, inverseStages, stageScalar]
      rw [ih (stage.forward input), stage.inverse_scale, stage.inverse_forward]
      funext coord
      simp [scaleCoeffs]
      ring

/-- Normalize the accumulated stage factor.  Concrete NTT developments use
this with their final `nInv` constant, leaving only the small closed identity
`nInv * stageScalar stages = 1`. -/
theorem scale_inverseStages_forwardStages {Coord : Type w}
    (stages : List (ScaledStage R Coord)) (nInv : R)
    (hnorm : nInv * stageScalar stages = 1) (input : Coord → R) :
    scaleCoeffs nInv (inverseStages stages (forwardStages stages input)) = input := by
  rw [inverseStages_forwardStages]
  funext coord
  simp only [scaleCoeffs]
  rw [← mul_assoc, hnorm, one_mul]

/-- A sequence of certified forward stages is additive. -/
theorem forwardStages_add {Coord : Type w} (stages : List (ScaledStage R Coord))
    (left right : Coord → R) :
    forwardStages stages (left + right) =
      forwardStages stages left + forwardStages stages right := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_add, ih]

/-- A sequence of certified forward stages preserves subtraction. -/
theorem forwardStages_sub {Coord : Type w} (stages : List (ScaledStage R Coord))
    (left right : Coord → R) :
    forwardStages stages (left - right) =
      forwardStages stages left - forwardStages stages right := by
  induction stages generalizing left right with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_sub, ih]

/-- A sequence of certified forward stages preserves zero. -/
theorem forwardStages_zero {Coord : Type w} (stages : List (ScaledStage R Coord)) :
    forwardStages stages 0 = 0 := by
  induction stages with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStages]
      rw [stage.forward_zero, ih]

/-! ## Stages on coefficient vectors

The stages of a transform on `Fin n` as maps of coefficient vectors: each stage reads the
vector of the previous one and produces its own, so a list of butterfly stages runs in linear
time per stage. The vector composites are the stage composites. -/

/-- `forwardStages` on coefficient vectors. -/
def forwardStagesVec {n : Nat} : List (ScaledStage R (Fin n)) → Vector R n → Vector R n
  | [], v => v
  | stage :: stages, v => forwardStagesVec stages (Vector.ofFn (stage.forward v.get))

/-- `inverseStages` on coefficient vectors. -/
def inverseStagesVec {n : Nat} : List (ScaledStage R (Fin n)) → Vector R n → Vector R n
  | [], v => v
  | stage :: stages, v =>
    let w := inverseStagesVec stages v
    Vector.ofFn (stage.inverse w.get)

omit [CommRing R] in
/-- A vector built from a function reads back as the function. -/
theorem get_ofFn {n : Nat} (f : Fin n → R) : (Vector.ofFn f).get = f :=
  funext fun i => by simp [Vector.get, Vector.ofFn]; rfl

theorem forwardStagesVec_get {n : Nat} (stages : List (ScaledStage R (Fin n))) (v : Vector R n) :
    (forwardStagesVec stages v).get = forwardStages stages v.get := by
  induction stages generalizing v with
  | nil => rfl
  | cons stage stages ih =>
      simp only [forwardStagesVec, forwardStages]
      rw [ih, get_ofFn]

theorem inverseStagesVec_get {n : Nat} (stages : List (ScaledStage R (Fin n))) (v : Vector R n) :
    (inverseStagesVec stages v).get = inverseStages stages v.get := by
  induction stages with
  | nil => rfl
  | cons stage stages ih =>
      simp only [inverseStagesVec, inverseStages]
      rw [get_ofFn, ih]

/-! ## Evaluation

A transform correct as a ring map evaluates: after its stages, a segment of coefficients read as
a polynomial agrees with the input polynomial at the roots of the segment's modulus. These
statements hold in every commutative algebra `S` over the coefficients, so a modulus without
roots in the coefficient ring still has them in its quotient. -/

section Evaluation

open Finset

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]

/-- The coefficient at index `i` of a coefficient function on `Fin N`, `0` past the end. -/
def coeffAt {N : ℕ} (a : Fin N → R) (i : ℕ) : R := if h : i < N then a ⟨i, h⟩ else 0

/-- The evaluation at `ω` of the `L` coefficients from `start`. -/
def segmentEval {N : ℕ} (a : Fin N → R) (start L : ℕ) (ω : S) : S :=
  ∑ j ∈ range L, algebraMap R S (coeffAt a (start + j)) * ω ^ j

theorem segmentEval_double {N : ℕ} (a : Fin N → R) (start len : ℕ) (ω : S) :
    segmentEval a start (2 * len) ω =
      segmentEval a start len ω + ω ^ len * segmentEval a (start + len) len ω := by
  unfold segmentEval
  rw [two_mul, sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  rw [pow_add, add_assoc]
  ring

/-- **A butterfly preserves evaluations**: if the halves of a segment of length `2 len` become
`u + z v` and `u - z v`, the left half evaluates like the segment at every `ω` with
`ω ^ len = z`, and the right half at every `ω` with `ω ^ len = -z`. -/
theorem segmentEval_butterfly {N M : ℕ} (a : Fin N → R) (b : Fin M → R) (start len : ℕ) (z : R)
    (hleft : ∀ j < len, coeffAt b (start + j) =
      coeffAt a (start + j) + z * coeffAt a (start + len + j))
    (hright : ∀ j < len, coeffAt b (start + len + j) =
      coeffAt a (start + j) - z * coeffAt a (start + len + j)) (ω : S) :
    (ω ^ len = algebraMap R S z → segmentEval b start len ω = segmentEval a start (2 * len) ω) ∧
    (ω ^ len = -algebraMap R S z →
      segmentEval b (start + len) len ω = segmentEval a start (2 * len) ω) := by
  rw [segmentEval_double]
  constructor
  · intro hω
    rw [hω]
    unfold segmentEval
    rw [mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [hleft j (mem_range.mp hj), map_add, map_mul]
    ring
  · intro hω
    rw [hω]
    unfold segmentEval
    rw [neg_mul, mul_sum, ← sum_neg_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun j hj => ?_
    rw [hright j (mem_range.mp hj), map_sub, map_mul]
    ring

/-- The left and right outputs of a forward stage on a layout whose pairs sit at
`g · 2 len + j` and `g · 2 len + len + j`. -/
theorem forwardStage_coeffAt {G len N : ℕ} (layout : ButterflyLayout (Fin G × Fin len) (Fin N))
    (hl : ∀ g j, (layout.equiv ((g, j), false)).val = g.val * (2 * len) + j.val)
    (hr : ∀ g j, (layout.equiv ((g, j), true)).val = g.val * (2 * len) + len + j.val)
    (z : Fin G × Fin len → R) (a : Fin N → R) (g : Fin G) (j : Fin len) :
    coeffAt (forwardStage layout z a) (g.val * (2 * len) + j.val) =
        coeffAt a (g.val * (2 * len) + j.val) + z (g, j) * coeffAt a (g.val * (2 * len) + len + j.val) ∧
      coeffAt (forwardStage layout z a) (g.val * (2 * len) + len + j.val) =
        coeffAt a (g.val * (2 * len) + j.val) - z (g, j) * coeffAt a (g.val * (2 * len) + len + j.val) := by
  have key : ∀ side (i : ℕ) (hi : (layout.equiv ((g, j), side)).val = i),
      coeffAt (forwardStage layout z a) i = forwardButterfly (z (g, j))
        (a (layout.equiv ((g, j), false))) (a (layout.equiv ((g, j), true))) side := by
    intro side i hi
    subst hi
    simp [coeffAt, forwardStage, Equiv.symm_apply_apply]
  have hA : ∀ side (i : ℕ) (hi : (layout.equiv ((g, j), side)).val = i),
      coeffAt a i = a (layout.equiv ((g, j), side)) := by
    intro side i hi; subst hi; simp [coeffAt]
  refine ⟨?_, ?_⟩
  · rw [key false _ (hl g j), hA false _ (hl g j), hA true _ (hr g j)]; rfl
  · rw [key true _ (hr g j), hA false _ (hl g j), hA true _ (hr g j)]; rfl

theorem segmentEval_zero_eq {n : ℕ} (a : Fin n → R) (ω : S) :
    segmentEval a 0 n ω = ∑ i : Fin n, algebraMap R S (a i) * ω ^ (i : ℕ) := by
  unfold segmentEval
  rw [← Fin.sum_univ_eq_sum_range (fun j => algebraMap R S (coeffAt a (0 + j)) * ω ^ j)]
  refine sum_congr rfl fun i _ => ?_
  simp [coeffAt, i.isLt]

omit [CommRing R] [Algebra R S] in
theorem sum_ite_val_eq {n : ℕ} (m : ℕ) (hm : m < n) (F : Fin n → S) :
    (∑ k : Fin n, if m = k.val then F k else 0) = F ⟨m, hm⟩ := by
  rw [Finset.sum_eq_single ⟨m, hm⟩]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Negacyclic products evaluate multiplicatively** at every `ω` with `ω ^ n = -1`. -/
theorem segmentEval_negacyclicConv {n : ℕ} (f g : Fin n → R) (ω : S) (hω : ω ^ n = -1) :
    segmentEval (fun k => LatticeCrypto.negacyclicConvCoeff f g k) 0 n ω =
      segmentEval f 0 n ω * segmentEval g 0 n ω := by
  rw [segmentEval_zero_eq, segmentEval_zero_eq, segmentEval_zero_eq, sum_mul_sum,
    ← Finset.sum_product']
  simp only [LatticeCrypto.negacyclicConvCoeff, map_sum, sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun ij _ => ?_
  have hn : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact ij.1.elim0)
  have hi := ij.1.isLt
  have hj := ij.2.isLt
  have hm : (ij.1.val + ij.2.val) % n < n := Nat.mod_lt _ hn
  by_cases hlt : ij.1.val + ij.2.val < n
  · simp only [hlt, if_true, apply_ite (algebraMap R S), map_zero, ite_mul, zero_mul]
    rw [sum_ite_val_eq _ hm (fun k => algebraMap R S (f ij.1 * g ij.2) * ω ^ (k : ℕ))]
    simp only [Nat.mod_eq_of_lt hlt, map_mul, pow_add]
    ring
  · simp only [hlt, if_false, apply_ite (algebraMap R S), map_zero, ite_mul, zero_mul]
    rw [sum_ite_val_eq _ hm (fun k => algebraMap R S (-(f ij.1 * g ij.2)) * ω ^ (k : ℕ))]
    have hmod : (ij.1.val + ij.2.val) % n = ij.1.val + ij.2.val - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    have hsplit : ω ^ ij.1.val * ω ^ ij.2.val = -(ω ^ ((ij.1.val + ij.2.val) % n)) := by
      rw [← pow_add, hmod, show ij.1.val + ij.2.val = ij.1.val + ij.2.val - n + n by omega,
        pow_add, hω, Nat.add_sub_cancel]
      ring
    simp only [map_neg, map_mul]
    linear_combination (algebraMap R S (f ij.1) * algebraMap R S (g ij.2)) * hsplit.symm

section Quadratic

open Polynomial

/-- In `R[X] / (X² − γ)`, the root `ω` satisfies `ω² = γ`. -/
theorem adjoinRoot_root_sq (γ : R) :
    AdjoinRoot.root (X ^ 2 - C γ) ^ 2 = algebraMap R (AdjoinRoot (X ^ 2 - C γ)) γ := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C γ)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [AdjoinRoot.algebraMap_eq]
  exact sub_eq_zero.mp h

/-- **Coordinates in `R[X] / (X² − γ)` are unique**: `a + b ω = c + d ω` at the root `ω` only if
`a = c` and `b = d`. -/
theorem adjoinRoot_pair_injective [Nontrivial R] {γ a b c d : R}
    (h : algebraMap R (AdjoinRoot (X ^ 2 - C γ)) a +
        algebraMap R _ b * AdjoinRoot.root (X ^ 2 - C γ) =
      algebraMap R _ c + algebraMap R _ d * AdjoinRoot.root (X ^ 2 - C γ)) :
    a = c ∧ b = d := by
  have hmk : AdjoinRoot.mk (X ^ 2 - C γ) (C (a - c) + C (b - d) * X) = 0 := by
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
    rw [← AdjoinRoot.algebraMap_eq] at *
    linear_combination h
  rw [AdjoinRoot.mk_eq_zero] at hmk
  have hdeg : (C (a - c) + C (b - d) * X).degree < (X ^ 2 - C γ : R[X]).degree := by
    rw [degree_X_pow_sub_C (by norm_num)]
    exact lt_of_le_of_lt (by compute_degree) (by norm_num)
  have hmonic : (X ^ 2 - C γ : R[X]).Monic := monic_X_pow_sub_C γ (by norm_num)
  have h0 : C (a - c) + C (b - d) * X = 0 := by
    rw [← (modByMonic_eq_self_iff hmonic).mpr hdeg, (modByMonic_eq_zero_iff_dvd hmonic).mpr hmk]
  have hc0 := congrArg (coeff · 0) h0
  have hc1 := congrArg (coeff · 1) h0
  simp at hc0 hc1
  exact ⟨sub_eq_zero.mp hc0, sub_eq_zero.mp hc1⟩

end Quadratic

end Evaluation

end LatticeCrypto.NTTCert

module

public import Commons.Definitions.BidirectionalSwitching
public import Commons.Schemes.Sponge.Uniform
public import Mathlib.Data.BitVec
public import RandomSystems.Typed.DSL.Converters
public import RandomSystems.Typed.Memoryless
public import RandomSystems.Typed.ProbProgramAttachment
public import RandomSystems.Typed.SamplingAlgebra

/-!
# Sponge construction converter, lazy simulator, and automaton semantics

Defines the byte-state decomposition, partial-table completion queries, honest work-budget and
fixed-budget interfaces (`HonestWorkSpec`, `workHonestInterface`, `HonestInterface`), shared random
oracle target (`sharedIdealRO`), real sponge converter (`spongePublic`), and lazy sponge simulator
(`spongeSimulator`), together with their exact probabilistic-automaton presentations [1, §§3–4].

## References

1. G. Bertoni, J. Daemen, M. Peeters, and G. Van Assche. *On the Indifferentiability of the Sponge
   Construction*. In *Advances in Cryptology — EUROCRYPT 2008*, LNCS 4965, pp. 181–197, 2008.
2. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
-/

@[expose] public section

namespace Commons.Sponge

open CategoryTheory ConstructiveCryptography SystemAlgebra
open SystemAlgebra.DSL (returnProg callProg forEach callBound_return callBound_call
  callBound_uniform callCost_return callCost_call callCost_foldr Avoids avoids_call avoids_return
  preservesAt_return preservesAt_call_self preservesAt_call_other)
open Probability Probability.Distribution Commons.BidirectionalSwitching
open scoped BigOperators NNReal SystemAlgebra ConstructiveCryptography MonoidalCategory

/-! ### Byte-state splitting, reassembly, and capacity counting -/

section ByteStateSplit

/-- Number of bytes in a sponge state after the `outputBytes` digest prefix. -/
def tailBytes (p : Parameters) : ℕ :=
  p.stateBytes - p.outputBytes

/-- The suffix of a sponge state after its `outputBytes` digest prefix. -/
def tailPart (p : Parameters) (state : ByteState p.stateBytes) : ByteState (tailBytes p) :=
  fun i => if h : p.outputBytes + i.val < p.stateBytes then state ⟨p.outputBytes + i.val, h⟩ else 0

/-- Reassemble a sponge state from its digest prefix and remaining tail bytes. -/
def assembleState (p : Parameters) (digest : ByteState p.outputBytes)
    (tail : ByteState (tailBytes p)) : ByteState p.stateBytes :=
  fun i =>
    if h : i.val < p.outputBytes then digest ⟨i.val, h⟩
    else if h' : i.val - p.outputBytes < tailBytes p then tail ⟨i.val - p.outputBytes, h'⟩
    else 0

lemma digestPart_assembleState (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes)
    (digest : ByteState p.outputBytes) (tail : ByteState (tailBytes p)) :
    digestPart p (assembleState p digest tail) = digest := by
  funext i
  have hi : i.val < p.stateBytes := Nat.lt_of_lt_of_le i.isLt ho
  simp only [digestPart, assembleState, hi, i.isLt, ↓reduceDIte]

lemma tailPart_assembleState (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes)
    (digest : ByteState p.outputBytes) (tail : ByteState (tailBytes p)) :
    tailPart p (assembleState p digest tail) = tail := by
  funext i
  have h1 : p.outputBytes + i.val < p.stateBytes := by
    have := i.isLt; unfold tailBytes at this; omega
  have h2 : ¬ p.outputBytes + i.val < p.outputBytes := by omega
  have h3 : p.outputBytes + i.val - p.outputBytes < tailBytes p := by
    have := i.isLt; omega
  have h4 : p.outputBytes + i.val - p.outputBytes = i.val := Nat.add_sub_cancel_left _ _
  simp only [tailPart, assembleState, h1, h2, h3, ↓reduceDIte]
  congr 1
  exact Fin.ext h4

lemma assembleState_digestPart_tailPart (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes)
    (state : ByteState p.stateBytes) :
    assembleState p (digestPart p state) (tailPart p state) = state := by
  funext i
  by_cases h : i.val < p.outputBytes
  · simp only [assembleState, digestPart, h, i.isLt, ↓reduceDIte]
  · have h1 : i.val - p.outputBytes < tailBytes p := by
      unfold tailBytes; have := i.isLt; omega
    have h2 : p.outputBytes + (i.val - p.outputBytes) < p.stateBytes := by
      have := i.isLt; omega
    have h3 : p.outputBytes + (i.val - p.outputBytes) = i.val := by omega
    simp only [assembleState, tailPart, h, h1, h2, ↓reduceDIte]
    congr 1
    exact Fin.ext h3

/-- Bijection splitting a sponge state into its digest prefix and remaining tail bytes. -/
def stateEquiv (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    ByteState p.stateBytes ≃ ByteState p.outputBytes × ByteState (tailBytes p) where
  toFun s := (digestPart p s, tailPart p s)
  invFun dt := assembleState p dt.1 dt.2
  left_inv := assembleState_digestPart_tailPart p ho
  right_inv dt := Prod.ext (digestPart_assembleState p ho dt.1 dt.2)
    (tailPart_assembleState p ho dt.1 dt.2)

/-- Number of rate bytes lying strictly between the digest prefix and the capacity suffix. -/
def middleBytes (p : Parameters) : ℕ :=
  p.rateBytes - p.outputBytes

/-- The rate bytes after `outputBytes` and before `rateBytes`. -/
def middlePart (p : Parameters) (state : ByteState p.stateBytes) : ByteState (middleBytes p) :=
  fun i => if h : p.outputBytes + i.val < p.stateBytes then state ⟨p.outputBytes + i.val, h⟩ else 0

/-- Reassemble a sponge state from its digest, remaining rate bytes, and capacity. -/
def assembleThree (p : Parameters) (digest : ByteState p.outputBytes)
    (mid : ByteState (middleBytes p)) (cap : ByteState p.capacityBytes) : ByteState p.stateBytes :=
  fun i =>
    if h1 : i.val < p.outputBytes then digest ⟨i.val, h1⟩
    else if _h2 : i.val < p.rateBytes then
      if h2' : i.val - p.outputBytes < middleBytes p then mid ⟨i.val - p.outputBytes, h2'⟩ else 0
    else if h3 : i.val - p.rateBytes < p.capacityBytes then cap ⟨i.val - p.rateBytes, h3⟩
    else 0

/-- Three-way bijection splitting a valid sponge state into `(digest, middleRate, capacity)`. -/
def stateThreeEquiv (p : Parameters) (hp : p.Valid) :
    ByteState p.stateBytes ≃
      ByteState p.outputBytes × ByteState (middleBytes p) × ByteState p.capacityBytes where
  toFun s := (digestPart p s, middlePart p s, capacityPart p s)
  invFun dmc := assembleThree p dmc.1 dmc.2.1 dmc.2.2
  left_inv s := by
    obtain ⟨_, hrs, _, hor, _, _⟩ := hp
    funext i
    by_cases h1 : i.val < p.outputBytes
    · simp only [assembleThree, digestPart, h1, i.isLt, ↓reduceDIte]
    · by_cases h2 : i.val < p.rateBytes
      · have h2' : i.val - p.outputBytes < middleBytes p := by unfold middleBytes; omega
        have h3 : p.outputBytes + (i.val - p.outputBytes) < p.stateBytes := by omega
        have h4 : p.outputBytes + (i.val - p.outputBytes) = i.val := by omega
        simp only [assembleThree, middlePart, h1, h2, h2', h3, ↓reduceDIte]
        congr 1; exact Fin.ext h4
      · have h3 : i.val - p.rateBytes < p.capacityBytes := by
          unfold Parameters.capacityBytes; have := i.isLt; omega
        have h4 : p.rateBytes + (i.val - p.rateBytes) < p.stateBytes := by
          have := i.isLt; omega
        have h5 : p.rateBytes + (i.val - p.rateBytes) = i.val := by omega
        simp only [assembleThree, capacityPart, h1, h2, h3, h4, ↓reduceDIte]
        congr 1; exact Fin.ext h5
  right_inv dmc := by
    obtain ⟨_, hrs, _, hor, _, _⟩ := hp
    rcases dmc with ⟨d, m, c⟩
    refine Prod.ext ?_ (Prod.ext ?_ ?_)
    · funext i
      have hi : i.val < p.stateBytes := by have := i.isLt; omega
      simp only [digestPart, assembleThree, hi, i.isLt, ↓reduceDIte]
    · funext i
      have h0 : p.outputBytes + i.val < p.rateBytes := by
        have := i.isLt; unfold middleBytes at this; omega
      have h1 : p.outputBytes + i.val < p.stateBytes := by omega
      have h2 : ¬ p.outputBytes + i.val < p.outputBytes := by omega
      have h3 : p.outputBytes + i.val - p.outputBytes < middleBytes p := by
        have := i.isLt; omega
      simp only [middlePart, assembleThree, h1, h2, h0, h3, ↓reduceDIte]
      congr 1; exact Fin.ext (Nat.add_sub_cancel_left _ _)
    · funext i
      have h1 : p.rateBytes + i.val < p.stateBytes := by
        have := i.isLt; unfold Parameters.capacityBytes at this; omega
      have h2 : ¬ p.rateBytes + i.val < p.outputBytes := by omega
      have h3 : ¬ p.rateBytes + i.val < p.rateBytes := by omega
      have h4 : p.rateBytes + i.val - p.rateBytes < p.capacityBytes := by
        have := i.isLt; omega
      simp only [capacityPart, assembleThree, h1, h2, h3, h4, ↓reduceDIte]
      congr 1; exact Fin.ext (Nat.add_sub_cancel_left _ _)

/-- Reassemble a sponge state from its rate prefix and capacity suffix. -/
def assembleRateCap (p : Parameters) (rate : ByteState p.rateBytes)
    (cap : ByteState p.capacityBytes) : ByteState p.stateBytes :=
  fun i =>
    if h1 : i.val < p.rateBytes then rate ⟨i.val, h1⟩
    else if h2 : i.val - p.rateBytes < p.capacityBytes then cap ⟨i.val - p.rateBytes, h2⟩
    else 0

/-- Bijection splitting a valid sponge state into `(rate, capacity)`. -/
def stateRateCapEquiv (p : Parameters) (hp : p.Valid) :
    ByteState p.stateBytes ≃ ByteState p.rateBytes × ByteState p.capacityBytes where
  toFun s := (ratePart p s, capacityPart p s)
  invFun rc := assembleRateCap p rc.1 rc.2
  left_inv s := by
    obtain ⟨_, hrs, _, _, _, _⟩ := hp
    funext i
    by_cases h1 : i.val < p.rateBytes
    · simp only [assembleRateCap, ratePart, h1, i.isLt, ↓reduceDIte]
    · have h2 : i.val - p.rateBytes < p.capacityBytes := by
        unfold Parameters.capacityBytes; have := i.isLt; omega
      have h3 : p.rateBytes + (i.val - p.rateBytes) < p.stateBytes := by
        have := i.isLt; omega
      have h4 : p.rateBytes + (i.val - p.rateBytes) = i.val := by omega
      simp only [assembleRateCap, capacityPart, h1, h2, h3, ↓reduceDIte]
      congr 1; exact Fin.ext h4
  right_inv rc := by
    obtain ⟨_, hrs, _, _, _, _⟩ := hp
    rcases rc with ⟨r, c⟩
    refine Prod.ext ?_ ?_
    · funext i
      have hi : i.val < p.stateBytes := by have := i.isLt; omega
      simp only [ratePart, assembleRateCap, hi, i.isLt, ↓reduceDIte]
    · funext i
      have h1 : p.rateBytes + i.val < p.stateBytes := by
        have := i.isLt; unfold Parameters.capacityBytes at this; omega
      have h2 : ¬ p.rateBytes + i.val < p.rateBytes := by omega
      have h3 : p.rateBytes + i.val - p.rateBytes < p.capacityBytes := by
        have := i.isLt; omega
      simp only [capacityPart, assembleRateCap, h1, h2, h3, ↓reduceDIte]
      congr 1; exact Fin.ext (Nat.add_sub_cancel_left _ _)

lemma card_state_eq_digest_mul_tail (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    Fintype.card (ByteState p.stateBytes) =
      Fintype.card (ByteState p.outputBytes) * Fintype.card (ByteState (tailBytes p)) := by
  simpa only [Fintype.card_prod] using Fintype.card_congr (stateEquiv p ho)

lemma card_state_eq_rate_mul_cap (p : Parameters) (hp : p.Valid) :
    Fintype.card (ByteState p.stateBytes) =
      Fintype.card (ByteState p.rateBytes) * Fintype.card (ByteState p.capacityBytes) := by
  simpa only [Fintype.card_prod] using Fintype.card_congr (stateRateCapEquiv p hp)

lemma card_state_eq_three (p : Parameters) (hp : p.Valid) :
    Fintype.card (ByteState p.stateBytes) =
      Fintype.card (ByteState p.outputBytes) *
        (Fintype.card (ByteState (middleBytes p)) * Fintype.card (ByteState p.capacityBytes)) := by
  simpa only [Fintype.card_prod] using Fintype.card_congr (stateThreeEquiv p hp)

lemma card_tail_eq_mid_mul_cap (p : Parameters) (hp : p.Valid) :
    Fintype.card (ByteState (tailBytes p)) =
      Fintype.card (ByteState (middleBytes p)) * Fintype.card (ByteState p.capacityBytes) := by
  have h1 := card_state_eq_digest_mul_tail p (hp.2.2.2.1.trans hp.2.1.le)
  have h2 := card_state_eq_three p hp
  have hpos : 0 < Fintype.card (ByteState p.outputBytes) := Fintype.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h1.symm.trans h2)

/-- Reassembling independent uniform digest and tail yields the uniform state distribution. -/
lemma uniform_state_eq_assemble (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    fTransform (fun dt : ByteState p.outputBytes × ByteState (tailBytes p) =>
        assembleState p dt.1 dt.2)
      ((uniform (ByteState p.outputBytes)).prod (uniform (ByteState (tailBytes p)))) =
      uniform (ByteState p.stateBytes) := by
  rw [prod_uniform]
  exact fTransform_equiv_uniform (stateEquiv p ho).symm

/-- Projecting a uniform state to its tail yields the uniform tail distribution. -/
lemma fTransform_tailPart_uniform (p : Parameters) (ho : p.outputBytes ≤ p.stateBytes) :
    fTransform (tailPart p) (uniform (ByteState p.stateBytes)) =
      uniform (ByteState (tailBytes p)) := by
  have hcomp : tailPart p = Prod.snd ∘ (stateEquiv p ho) := rfl
  have hw : (uniform (ByteState p.outputBytes)).weight = 1 := (𝒰[ByteState p.outputBytes]).2.2
  rw [hcomp, ← fTransform_fTransform, fTransform_equiv_uniform, ← prod_uniform,
    fTransform_snd_prod, hw, one_smul]

/-- Under a fixed digest `d`, uniform tail reassembly has uniform capacity projection. -/
lemma fTransform_capacityPart_assembleState (p : Parameters) (hp : p.Valid)
    (d : ByteState p.outputBytes) :
    fTransform (fun t : ByteState (tailBytes p) => capacityPart p (assembleState p d t))
      (uniform (ByteState (tailBytes p))) = uniform (ByteState p.capacityBytes) := by
  have hho : p.outputBytes ≤ p.stateBytes := hp.2.2.2.1.trans hp.2.1.le
  let eTail : ByteState (tailBytes p) ≃ ByteState (middleBytes p) × ByteState p.capacityBytes :=
    { toFun := fun t => (middlePart p (assembleState p d t), capacityPart p (assembleState p d t))
      invFun := fun mc => tailPart p (assembleThree p d mc.1 mc.2)
      left_inv := fun t => by
        have h3 : assembleThree p d (middlePart p (assembleState p d t))
            (capacityPart p (assembleState p d t)) = assembleState p d t := by
          have hd : digestPart p (assembleState p d t) = d := digestPart_assembleState p hho d t
          have hli := (stateThreeEquiv p hp).left_inv (assembleState p d t)
          change assembleThree p (digestPart p (assembleState p d t))
            (middlePart p (assembleState p d t)) (capacityPart p (assembleState p d t)) = _ at hli
          rwa [hd] at hli
        dsimp only
        rw [h3, tailPart_assembleState p hho]
      right_inv := fun mc => by
        have h1 : digestPart p (assembleThree p d mc.1 mc.2) = d :=
          congrArg Prod.fst ((stateThreeEquiv p hp).right_inv (d, mc.1, mc.2))
        have h2 : assembleState p d (tailPart p (assembleThree p d mc.1 mc.2)) =
            assembleThree p d mc.1 mc.2 := by
          have ha := assembleState_digestPart_tailPart p hho (assembleThree p d mc.1 mc.2)
          rwa [h1] at ha
        dsimp only
        rw [h2]
        exact congrArg Prod.snd ((stateThreeEquiv p hp).right_inv (d, mc.1, mc.2)) }
  have hcomp : (fun t => capacityPart p (assembleState p d t)) = Prod.snd ∘ eTail := rfl
  have hw : (uniform (ByteState (middleBytes p))).weight = 1 := (𝒰[ByteState (middleBytes p)]).2.2
  rw [hcomp, ← fTransform_fTransform, fTransform_equiv_uniform, ← prod_uniform,
    fTransform_snd_prod, hw, one_smul]

/-- Number of states whose capacity lies outside a forbidden set `S_cap`. -/
lemma card_filter_avoid_cap (p : Parameters) (hp : p.Valid)
    (caps : Finset (ByteState p.capacityBytes)) :
    (Finset.univ.filter fun s : ByteState p.stateBytes => capacityPart p s ∉ caps).card =
      (Fintype.card (ByteState p.capacityBytes) - caps.card) *
        Fintype.card (ByteState p.rateBytes) := by
  have hbij :
      (Finset.univ.filter fun s : ByteState p.stateBytes => capacityPart p s ∉ caps).card =
        ((Finset.univ : Finset (ByteState p.rateBytes)) ×ˢ (Finset.univ \ caps)).card := by
    apply Finset.card_bij (fun s _ => stateRateCapEquiv p hp s)
    · intro s hs
      rw [Finset.mem_filter] at hs
      exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
        hs.2⟩⟩
    · intro a _ b _ h
      exact (stateRateCapEquiv p hp).injective h
    · intro rc hrc
      refine ⟨(stateRateCapEquiv p hp).symm rc, ?_, (stateRateCapEquiv p hp).apply_symm_apply rc⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hcap : capacityPart p ((stateRateCapEquiv p hp).symm rc) = rc.2 :=
        congrArg Prod.snd ((stateRateCapEquiv p hp).apply_symm_apply rc)
      rw [hcap]
      exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hrc).2).2
  rw [hbij, Finset.card_product, Finset.card_univ,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Nat.mul_comm]

/-- Number of states having a prescribed digest `d` and capacity outside `caps`. -/
lemma card_filter_digest_and_avoid_cap (p : Parameters) (hp : p.Valid)
    (d : ByteState p.outputBytes) (caps : Finset (ByteState p.capacityBytes)) :
    (Finset.univ.filter fun s : ByteState p.stateBytes =>
        digestPart p s = d ∧ capacityPart p s ∉ caps).card =
      (Fintype.card (ByteState p.capacityBytes) - caps.card) *
        Fintype.card (ByteState (middleBytes p)) := by
  have hbij :
      (Finset.univ.filter fun s : ByteState p.stateBytes =>
          digestPart p s = d ∧ capacityPart p s ∉ caps).card =
        ((Finset.univ : Finset (ByteState (middleBytes p))) ×ˢ (Finset.univ \ caps)).card := by
    apply Finset.card_bij (fun s _ => (middlePart p s, capacityPart p s))
    · intro s hs
      rw [Finset.mem_filter] at hs
      exact Finset.mem_product.mpr
        ⟨Finset.mem_univ _, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hs.2.2⟩⟩
    · intro a ha b hb h
      rw [Finset.mem_filter] at ha hb
      apply (stateThreeEquiv p hp).injective
      exact Prod.ext (ha.2.1.trans hb.2.1.symm) h
    · intro mc hmc
      refine ⟨(stateThreeEquiv p hp).symm (d, mc.1, mc.2), ?_, ?_⟩
      · rw [Finset.mem_filter]
        have hinv := (stateThreeEquiv p hp).apply_symm_apply (d, mc.1, mc.2)
        refine ⟨Finset.mem_univ _, congrArg Prod.fst hinv, ?_⟩
        have hcap : capacityPart p ((stateThreeEquiv p hp).symm (d, mc.1, mc.2)) = mc.2 :=
          congrArg (fun x => x.2.2) hinv
        rw [hcap]
        exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hmc).2).2
      · have hinv := (stateThreeEquiv p hp).apply_symm_apply (d, mc.1, mc.2)
        exact congrArg Prod.snd hinv
  rw [hbij, Finset.card_product, Finset.card_univ,
    Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Nat.mul_comm]

/-- Uniform probability of hitting a forbidden capacity set `caps`. -/
lemma uniform_mass_cap_mem (p : Parameters) (hp : p.Valid)
    (caps : Finset (ByteState p.capacityBytes)) :
    (uniform (ByteState p.stateBytes)).mass (fun s => capacityPart p s ∈ caps) =
      (caps.card : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  have h1 : (uniform (ByteState p.stateBytes)).mass (fun s => capacityPart p s ∈ caps) =
      (fTransform (capacityPart p) (uniform (ByteState p.stateBytes))).mass (fun c => c ∈ caps) :=
    (mass_fTransform (capacityPart p) (uniform (ByteState p.stateBytes)) (fun c => c ∈ caps)).symm
  rw [h1, fTransform_capacityPart_uniform p hp.2.1.le]
  classical
  have hsupp : (uniform (ByteState p.capacityBytes)).support = Finset.univ := by
    ext c
    simp only [Finsupp.mem_support_iff, uniform_apply, Finset.mem_univ, iff_true, one_div]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState p.capacityBytes)))
  rw [mass, Finsupp.sum, hsupp]
  simp only [uniform_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  ring

/-- Uniform tail probability (under a fixed digest) of hitting a forbidden capacity set `caps`. -/
lemma uniform_tail_mass_cap_mem (p : Parameters) (hp : p.Valid)
    (d : ByteState p.outputBytes) (caps : Finset (ByteState p.capacityBytes)) :
    (uniform (ByteState (tailBytes p))).mass (fun t => capacityPart p (assembleState p d t) ∈ caps)
      =
      (caps.card : ℝ) / (Fintype.card (ByteState p.capacityBytes) : ℝ) := by
  have h1 :
      (uniform (ByteState (tailBytes p))).mass
          (fun t => capacityPart p (assembleState p d t) ∈ caps) =
        (fTransform (fun t => capacityPart p (assembleState p d t))
          (uniform (ByteState (tailBytes p)))).mass (fun c => c ∈ caps) :=
    (mass_fTransform _ _ (fun c => c ∈ caps)).symm
  rw [h1, fTransform_capacityPart_assembleState p hp d]
  classical
  have hsupp : (uniform (ByteState p.capacityBytes)).support = Finset.univ := by
    ext c
    simp only [Finsupp.mem_support_iff, uniform_apply, Finset.mem_univ, iff_true, one_div]
    exact inv_ne_zero (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ByteState p.capacityBytes)))
  rw [mass, Finsupp.sum, hsupp]
  simp only [uniform_apply, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul, Finset.filter_mem_eq_inter, Finset.univ_inter]
  ring

end ByteStateSplit

/-! ### Partial-table lookups, rooted absorption, and unique completion -/

section PartialTable

variable {State : Type} [DecidableEq State]

/-- First recorded output for `x` in a directed permutation table. -/
def lookupForwardEdge : List (PermutationEdge State) → State → Option State
  | [], _ => none
  | e :: rest, x => if e.input = x then some e.output else lookupForwardEdge rest x

/-- First recorded input for `y` in a directed permutation table. -/
def lookupInverseEdge : List (PermutationEdge State) → State → Option State
  | [], _ => none
  | e :: rest, y => if e.output = y then some e.input else lookupInverseEdge rest y

/-- Strip directions from a directed table to obtain its underlying `(input, output)` pair list. -/
def toPairs (table : List (PermutationEdge State)) : List (State × State) :=
  table.map fun e => (e.input, e.output)

lemma lookupForwardEdge_eq_lookupForward (table : List (PermutationEdge State)) (x : State) :
    lookupForwardEdge table x = lookupForward (toPairs table) x := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    simp only [lookupForwardEdge, toPairs, List.map_cons, lookupForward, List.lookup_cons, ih]
    by_cases h : e.input = x
    · subst h
      simp only [↓reduceIte, beq_self_eq_true]
    · have hne : x ≠ e.input := Ne.symm h
      rw [ite_eq_right h]
      have hbf : @BEq.beq State (@instBEqOfDecidableEq State (Classical.decEq State)) x e.input =
          false := by
        let _ : DecidableEq State := Classical.decEq State
        exact beq_eq_false_iff_ne.mpr hne
      rw [hbf]

lemma lookupInverseEdge_eq_lookupInverse (table : List (PermutationEdge State)) (y : State) :
    lookupInverseEdge table y = lookupInverse (toPairs table) y := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    simp only [lookupInverseEdge, toPairs, List.map_cons, lookupInverse, Prod.swap_prod_mk,
      List.lookup_cons, ih]
    by_cases h : e.output = y
    · subst h
      simp only [↓reduceIte, beq_self_eq_true]
    · have hne : y ≠ e.output := Ne.symm h
      rw [ite_eq_right h]
      have hbf : @BEq.beq State (@instBEqOfDecidableEq State (Classical.decEq State)) y e.output =
          false := by
        let _ : DecidableEq State := Classical.decEq State
        exact beq_eq_false_iff_ne.mpr hne
      rw [hbf]

lemma lookupForwardEdge_eq_none_iff (table : List (PermutationEdge State)) (x : State) :
    lookupForwardEdge table x = none ↔ ∀ e ∈ table, e.input ≠ x := by
  induction table with
  | nil => simp only [lookupForwardEdge, List.not_mem_nil, false_implies, implies_true]
  | cons e rest ih =>
    simp only [lookupForwardEdge, List.mem_cons, forall_eq_or_imp]
    split_ifs with h
    · simp only [ne_eq, h, not_true_eq_false, false_and]
    · simp only [ih, ne_eq, h, not_false_eq_true, true_and]

lemma lookupInverseEdge_eq_none_iff (table : List (PermutationEdge State)) (y : State) :
    lookupInverseEdge table y = none ↔ ∀ e ∈ table, e.output ≠ y := by
  induction table with
  | nil => simp only [lookupInverseEdge, List.not_mem_nil, false_implies, implies_true]
  | cons e rest ih =>
    simp only [lookupInverseEdge, List.mem_cons, forall_eq_or_imp]
    split_ifs with h
    · simp only [ne_eq, h, not_true_eq_false, false_and]
    · simp only [ih, ne_eq, h, not_false_eq_true, true_and]

lemma lookupForwardEdge_eq_some_mem {table : List (PermutationEdge State)} {x y : State}
    (h : lookupForwardEdge table x = some y) :
    ∃ e ∈ table, e.input = x ∧ e.output = y := by
  induction table with
  | nil => simp only [lookupForwardEdge, reduceCtorEq] at h
  | cons e rest ih =>
    simp only [lookupForwardEdge] at h
    split_ifs at h with hx
    · exact ⟨e, List.mem_cons_self, hx, Option.some.inj h⟩
    · obtain ⟨e', hm, hi, ho⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ hm, hi, ho⟩

lemma lookupInverseEdge_eq_some_mem {table : List (PermutationEdge State)} {y x : State}
    (h : lookupInverseEdge table y = some x) :
    ∃ e ∈ table, e.input = x ∧ e.output = y := by
  induction table with
  | nil => simp only [lookupInverseEdge, reduceCtorEq] at h
  | cons e rest ih =>
    simp only [lookupInverseEdge] at h
    split_ifs at h with hy
    · exact ⟨e, List.mem_cons_self, Option.some.inj h, hy⟩
    · obtain ⟨e', hm, hi, ho⟩ := ih h
      exact ⟨e', List.mem_cons_of_mem _ hm, hi, ho⟩

lemma lookupForwardEdge_append_of_some {table ext : List (PermutationEdge State)} {x y : State}
    (h : lookupForwardEdge table x = some y) :
    lookupForwardEdge (table ++ ext) x = some y := by
  induction table with
  | nil => simp only [lookupForwardEdge, reduceCtorEq] at h
  | cons e rest ih =>
    simp only [List.cons_append, lookupForwardEdge] at h ⊢
    split_ifs at h ⊢
    · exact h
    · exact ih h

lemma lookupForwardEdge_append_of_none {table ext : List (PermutationEdge State)} {x : State}
    (h : lookupForwardEdge table x = none) :
    lookupForwardEdge (table ++ ext) x = lookupForwardEdge ext x := by
  induction table with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.cons_append, lookupForwardEdge] at h ⊢
    split_ifs at h ⊢
    · exact ih h

/-- Record a fresh forward edge `(x, y)` unless `y` already appears as a recorded output. -/
def recordForwardEdge (table : List (PermutationEdge State)) (x y : State) :
    List (PermutationEdge State) :=
  if y ∉ table.map PermutationEdge.output then table ++ [⟨x, y, false⟩] else table

/-- Record a fresh inverse edge `(x, y)` unless `x` already appears as a recorded input. -/
def recordInverseEdge (table : List (PermutationEdge State)) (x y : State) :
    List (PermutationEdge State) :=
  if x ∉ table.map PermutationEdge.input then table ++ [⟨x, y, true⟩] else table

lemma toPairs_recordForwardEdge (table : List (PermutationEdge State)) (x y : State) :
    toPairs (recordForwardEdge table x y) =
      if y ∉ (toPairs table).map Prod.snd then toPairs table ++ [(x, y)] else toPairs table := by
  have hmap : (toPairs table).map Prod.snd = table.map PermutationEdge.output := by
    simp only [toPairs, List.map_map, Function.comp_def]
  rw [hmap]
  unfold recordForwardEdge
  by_cases hy : y ∉ table.map PermutationEdge.output
  · rw [ite_eq_left hy, ite_eq_left hy]
    simp only [toPairs, List.map_append, List.map_singleton]
  · rw [ite_eq_right hy, ite_eq_right hy]

lemma toPairs_recordInverseEdge (table : List (PermutationEdge State)) (x y : State) :
    toPairs (recordInverseEdge table x y) =
      if x ∉ (toPairs table).map Prod.fst then toPairs table ++ [(x, y)] else toPairs table := by
  have hmap : (toPairs table).map Prod.fst = table.map PermutationEdge.input := by
    simp only [toPairs, List.map_map, Function.comp_def]
  rw [hmap]
  unfold recordInverseEdge
  by_cases hx : x ∉ table.map PermutationEdge.input
  · rw [ite_eq_left hx, ite_eq_left hx]
    simp only [toPairs, List.map_append, List.map_singleton]
  · rw [ite_eq_right hx, ite_eq_right hx]

omit [DecidableEq State] in
/-- Avoiding occupied capacities guarantees no output collision on a forward edge. -/
lemma output_not_mem_of_avoidsOccupied {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) {x y : State}
    (hf : AvoidsOccupiedCapacity capacity zeroCap table ⟨x, y, false⟩) :
    y ∉ table.map PermutationEdge.output := by
  intro hy
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
  have hcap : capacity e.output ∉ occupiedCapacities capacity zeroCap table := by
    simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, Bool.false_eq_true,
      ↓reduceIte] using hf
  exact hcap (occupiedCapacities_output capacity zeroCap table he)

omit [DecidableEq State] in
/-- Avoiding occupied capacities guarantees no input collision on an inverse edge. -/
lemma input_not_mem_of_avoidsOccupied {Cap : Type*} [DecidableEq Cap]
    (capacity : State → Cap) (zeroCap : Cap)
    (table : List (PermutationEdge State)) {x y : State}
    (hf : AvoidsOccupiedCapacity capacity zeroCap table ⟨x, y, true⟩) :
    x ∉ table.map PermutationEdge.input := by
  intro hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  have hcap : capacity e.input ∉ occupiedCapacities capacity zeroCap table := by
    simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, ↓reduceIte] using hf
  exact hcap (occupiedCapacities_input capacity zeroCap table he)

/-- Partial-table sponge absorption: returns `some finalState` when every block is covered. -/
def evalAbsorption (p : Parameters) (table : List (PermutationEdge (ByteState p.stateBytes))) :
    ByteState p.stateBytes → List (ByteState p.rateBytes) → Option (ByteState p.stateBytes)
  | state, [] => some state
  | state, block :: rest =>
    match lookupForwardEdge table (absorbBlock p state block) with
    | none => none
    | some next => evalAbsorption p table next rest

lemma evalAbsorption_append (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (state : ByteState p.stateBytes) (first second : List (ByteState p.rateBytes)) :
    evalAbsorption p table state (first ++ second) =
      (evalAbsorption p table state first).bind fun mid => evalAbsorption p table mid second := by
  induction first generalizing state with
  | nil => rfl
  | cons block rest ih =>
    simp only [List.cons_append, evalAbsorption]
    cases lookupForwardEdge table (absorbBlock p state block) with
    | none => rfl
    | some next => exact ih next

lemma evalAbsorption_mono (p : Parameters)
    {table ext : List (PermutationEdge (ByteState p.stateBytes))}
    {state out : ByteState p.stateBytes} {blocks : List (ByteState p.rateBytes)}
    (h : evalAbsorption p table state blocks = some out) :
    evalAbsorption p (table ++ ext) state blocks = some out := by
  induction blocks generalizing state with
  | nil => exact h
  | cons block rest ih =>
    simp only [evalAbsorption] at h ⊢
    cases hl : lookupForwardEdge table (absorbBlock p state block) with
    | none => rw [hl] at h; cases h
    | some next =>
      rw [hl] at h
      rw [lookupForwardEdge_append_of_some hl]
      exact ih h

/-- If `π` agrees with `table` and `evalAbsorption` succeeds, it equals `absorbBlocks`. -/
lemma evalAbsorption_eq_absorbBlocks (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (π : Equiv.Perm (ByteState p.stateBytes)) (ha : AgreesWith table π)
    (state out : ByteState p.stateBytes) (blocks : List (ByteState p.rateBytes))
    (h : evalAbsorption p table state blocks = some out) :
    absorbBlocks (absorbBlock p) π state blocks = out := by
  induction blocks generalizing state with
  | nil =>
    simp only [evalAbsorption, Option.some.injEq] at h
    exact h
  | cons block rest ih =>
    simp only [evalAbsorption] at h
    cases hl : lookupForwardEdge table (absorbBlock p state block) with
    | none => rw [hl] at h; cases h
    | some next =>
      rw [hl] at h
      obtain ⟨e, hm, hi, ho⟩ := lookupForwardEdge_eq_some_mem hl
      have hπ : π (absorbBlock p state block) = next := by
        rw [← hi, ha e hm, ho]
      rw [absorbBlocks_cons, hπ]
      exact ih next h

/-- Every nonempty rooted path evaluated in a `CapacityCollisionFree` table ends in
`forwardOutputs table`. -/
lemma evalAbsorption_mem_forwardOutputs (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (state : ByteState p.stateBytes)
    (hs : capacityPart p state = zeroState p.capacityBytes ∨ state ∈ forwardOutputs table)
    (blocks : List (ByteState p.rateBytes)) (hne : blocks ≠ [])
    {out : ByteState p.stateBytes} (h : evalAbsorption p table state blocks = some out) :
    out ∈ forwardOutputs table := by
  induction blocks generalizing state with
  | nil => exact False.elim (hne rfl)
  | cons block rest ih =>
    simp only [evalAbsorption] at h
    cases hl : lookupForwardEdge table (absorbBlock p state block) with
    | none => rw [hl] at h; cases h
    | some next =>
      rw [hl] at h
      obtain ⟨e, hm, hi, ho⟩ := lookupForwardEdge_eq_some_mem hl
      have hf : e.inverse = false :=
        rooted_edge_forward (capacityPart p) (zeroState p.capacityBytes) table hg hm state hs
          (by rw [hi, capacityPart_absorbBlock])
      have hnext : next ∈ forwardOutputs table := ⟨e, hm, hf, ho⟩
      cases rest with
      | nil =>
        simp only [evalAbsorption, Option.some.injEq] at h
        exact h ▸ hnext
      | cons b rest' =>
        exact ih next (Or.inr hnext) (List.cons_ne_nil _ _) h

lemma evalAbsorption_reached (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (blocks : List (ByteState p.rateBytes)) {out : ByteState p.stateBytes}
    (h : evalAbsorption p table (zeroState p.stateBytes) blocks = some out) :
    out ∈ insert (zeroState p.stateBytes) (forwardOutputs table) := by
  cases blocks with
  | nil =>
    simp only [evalAbsorption, Option.some.injEq] at h
    exact h ▸ Set.mem_insert _ _
  | cons b rest =>
    exact Set.mem_insert_of_mem _
      (evalAbsorption_mem_forwardOutputs p table hg (zeroState p.stateBytes)
        (Or.inl (capacityPart_zeroState p)) (b :: rest) (List.cons_ne_nil _ _) h)

/-- Rooted path uniqueness directly on a partial bijection table without needing a global `π`. -/
theorem blocks_eq_of_evalAbsorption_eq (p : Parameters) (hp : p.Valid)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {first second : List (ByteState p.rateBytes)} {out : ByteState p.stateBytes}
    (hf : evalAbsorption p table (zeroState p.stateBytes) first = some out)
    (hs : evalAbsorption p table (zeroState p.stateBytes) second = some out) :
    first = second := by
  induction first using List.reverseRecOn generalizing second out with
  | nil =>
    simp only [evalAbsorption, Option.some.injEq] at hf
    subst hf
    cases second with
    | nil => rfl
    | cons b rest =>
      have hmem := evalAbsorption_mem_forwardOutputs p table hg (zeroState p.stateBytes)
        (Or.inl (capacityPart_zeroState p)) (b :: rest) (List.cons_ne_nil _ _) hs
      exact False.elim (hg.2.1 _ hmem (capacityPart_zeroState p))
  | append_singleton first block ih =>
    cases second using List.reverseRecOn with
    | nil =>
      simp only [evalAbsorption, Option.some.injEq] at hs
      subst hs
      have hne : first ++ [block] ≠ [] :=
        List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
      have hmem := evalAbsorption_mem_forwardOutputs p table hg (zeroState p.stateBytes)
        (Or.inl (capacityPart_zeroState p)) (first ++ [block]) hne hf
      exact False.elim (hg.2.1 _ hmem (capacityPart_zeroState p))
    | append_singleton second last =>
      rw [evalAbsorption_append] at hf hs
      cases hfp : evalAbsorption p table (zeroState p.stateBytes) first with
      | none => rw [hfp] at hf; cases hf
      | some p1 =>
        rw [hfp, Option.bind_some, evalAbsorption] at hf
        cases hsp : evalAbsorption p table (zeroState p.stateBytes) second with
        | none => rw [hsp] at hs; cases hs
        | some p2 =>
          rw [hsp, Option.bind_some, evalAbsorption] at hs
          cases hl1 : lookupForwardEdge table (absorbBlock p p1 block) with
          | none => rw [hl1] at hf; cases hf
          | some o1 =>
            rw [hl1] at hf
            simp only [evalAbsorption, Option.some.injEq] at hf
            cases hl2 : lookupForwardEdge table (absorbBlock p p2 last) with
            | none => rw [hl2] at hs; cases hs
            | some o2 =>
              rw [hl2] at hs
              simp only [evalAbsorption, Option.some.injEq] at hs
              subst hf
              obtain ⟨e1, hm1, hi1, ho1⟩ := lookupForwardEdge_eq_some_mem hl1
              obtain ⟨e2, hm2, hi2, ho2⟩ := lookupForwardEdge_eq_some_mem hl2
              have hp1m : (e1.input, e1.output) ∈ toPairs table :=
                List.mem_map.mpr ⟨e1, hm1, rfl⟩
              have hp2m : (e2.input, e2.output) ∈ toPairs table :=
                List.mem_map.mpr ⟨e2, hm2, rfl⟩
              have hxe : e1.input = e2.input := by
                have hno := hpb.2
                have hmem1 : (e1.input, e1.output) ∈ toPairs table := hp1m
                have hmem2 : (e2.input, e2.output) ∈ toPairs table := hp2m
                have hoeq : e1.output = e2.output := by rw [ho1, ← hs, ho2]
                by_contra hne
                obtain ⟨i, hi, hget1⟩ := List.mem_iff_getElem.mp hmem1
                obtain ⟨j, hj, hget2⟩ := List.mem_iff_getElem.mp hmem2
                have hij : i ≠ j := by
                  intro hEq; subst hEq
                  rw [hget1] at hget2
                  exact hne (congrArg Prod.fst hget2)
                have hnd := List.nodup_iff_injective_getElem.mp hno
                have hgetm : ((toPairs table).map Prod.snd)[i]'(by simpa using hi) =
                    ((toPairs table).map Prod.snd)[j]'(by simpa using hj) := by
                  simp only [List.getElem_map, hget1, hget2, hoeq]
                have hfin : (⟨i, by simpa using hi⟩ : Fin ((toPairs table).map Prod.snd).length) =
                    ⟨j, by simpa using hj⟩ := hnd hgetm
                exact hij (congrArg Fin.val hfin)
              have hx : absorbBlock p p1 block = absorbBlock p p2 last := by
                rw [← hi1, hxe, hi2]
              have hcapEq : capacityPart p p1 = capacityPart p p2 := by
                have hc := congrArg (capacityPart p) hx
                simpa only [capacityPart_absorbBlock] using hc
              have hpar : p1 = p2 :=
                reached_capacity_injective (capacityPart p) (zeroState p.capacityBytes)
                  (zeroState p.stateBytes) (capacityPart_zeroState p) table hg
                  (evalAbsorption_reached p table hg first hfp)
                  (evalAbsorption_reached p table hg second hsp) hcapEq
              subst hpar
              have hb : block = last := absorbBlock_injective p hp.2.1.le p1 hx
              rw [ih hfp hsp, hb]

/-- `MatchesCompletion p encode table x m` holds when `x` is the final permutation input of
`encode m` along a prefix already covered by `table`. -/
def MatchesCompletion {M : Type} (p : Parameters) (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (x : ByteState p.stateBytes) (m : M) : Prop :=
  ∃ (parent : ByteState p.stateBytes) (last : ByteState p.rateBytes),
    paddedBlocks p (encode m) = (paddedBlocks p (encode m)).dropLast ++ [last] ∧
      evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m)).dropLast =
        some parent ∧
      absorbBlock p parent last = x

/-- In a `CapacityCollisionFree` partial bijection table, at most one message is completed by `x`.
-/
theorem matchesCompletion_unique {M : Type} (p : Parameters) (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {x : ByteState p.stateBytes} {m₁ m₂ : M}
    (h₁ : MatchesCompletion p encode table x m₁)
    (h₂ : MatchesCompletion p encode table x m₂) :
    m₁ = m₂ := by
  obtain ⟨p1, b1, hsplit1, heval1, habs1⟩ := h₁
  obtain ⟨p2, b2, hsplit2, heval2, habs2⟩ := h₂
  have hcapEq : capacityPart p p1 = capacityPart p p2 := by
    have hc := congrArg (capacityPart p) (habs1.trans habs2.symm)
    simpa only [capacityPart_absorbBlock] using hc
  have hpar : p1 = p2 :=
    reached_capacity_injective (capacityPart p) (zeroState p.capacityBytes)
      (zeroState p.stateBytes) (capacityPart_zeroState p) table hg
      (evalAbsorption_reached p table hg _ heval1)
      (evalAbsorption_reached p table hg _ heval2) hcapEq
  subst hpar
  have hb : b1 = b2 := absorbBlock_injective p hp.2.1.le p1 (habs1.trans habs2.symm)
  have hpre : (paddedBlocks p (encode m₁)).dropLast = (paddedBlocks p (encode m₂)).dropLast :=
    blocks_eq_of_evalAbsorption_eq p hp table hpb hg heval1 heval2
  have hblocks : paddedBlocks p (encode m₁) = paddedBlocks p (encode m₂) := by
    rw [hsplit1, hsplit2, hpre, hb]
  exact henc (paddedBlocks_injective p hp.1 hp.2.2.2.2.1 hp.2.2.2.2.2 hblocks)

open Classical in
/-- Select the completing message `m` for `x` in `table`, if any exists. -/
noncomputable def completingMessage {M : Type} (p : Parameters) (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (x : ByteState p.stateBytes) : Option M :=
  if h : ∃ m : M, MatchesCompletion p encode table x m then some (Classical.choose h) else none

open Classical in
lemma completingMessage_eq_some_iff {M : Type} (p : Parameters) (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (x : ByteState p.stateBytes) (m : M) :
    completingMessage p encode table x = some m ↔ MatchesCompletion p encode table x m := by
  unfold completingMessage
  split_ifs with h
  · constructor
    · intro he
      exact (Option.some.inj he) ▸ Classical.choose_spec h
    · intro hm
      exact congrArg some (matchesCompletion_unique p hp encode henc table hpb hg
        (Classical.choose_spec h) hm)
  · constructor
    · intro he; cases he
    · intro hm; exact False.elim (h ⟨m, hm⟩)

/-- Appending an edge satisfying `AvoidsOccupiedCapacity` cannot cover a previously uncovered
nonempty block sequence unless `edge` is a fresh forward edge finishing its last block. -/
theorem no_preexisting_extension (p : Parameters)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (edge : PermutationEdge (ByteState p.stateBytes))
    (hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) table edge)
    (blocks : List (ByteState p.rateBytes)) (hne : blocks ≠ [])
    {out : ByteState p.stateBytes}
    (hnew : evalAbsorption p (table ++ [edge]) (zeroState p.stateBytes) blocks = some out)
    (hold : evalAbsorption p table (zeroState p.stateBytes) blocks = none) :
    edge.inverse = false ∧
      ∃ (parent : ByteState p.stateBytes) (last : ByteState p.rateBytes),
        blocks = blocks.dropLast ++ [last] ∧
        evalAbsorption p table (zeroState p.stateBytes) blocks.dropLast = some parent ∧
        absorbBlock p parent last = edge.input ∧
        out = edge.output := by
  have helper : ∀ (state : ByteState p.stateBytes) (bs : List (ByteState p.rateBytes)),
      bs ≠ [] →
      capacityPart p state ∈ occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table →
      evalAbsorption p (table ++ [edge]) state bs = some out →
      evalAbsorption p table state bs = none →
      edge.inverse = false ∧
        ∃ (parent : ByteState p.stateBytes) (last : ByteState p.rateBytes),
          bs = bs.dropLast ++ [last] ∧
          evalAbsorption p table state bs.dropLast = some parent ∧
          absorbBlock p parent last = edge.input ∧
          out = edge.output := by
    intro state bs
    induction bs generalizing state with
    | nil => intro hn; exact False.elim (hn rfl)
    | cons b rest ih =>
      intro _ hcap hnew' hold'
      simp only [evalAbsorption] at hnew' hold'
      cases hl : lookupForwardEdge table (absorbBlock p state b) with
      | some next =>
        rw [hl] at hold'
        rw [lookupForwardEdge_append_of_some hl] at hnew'
        cases rest with
        | nil =>
          simp only [evalAbsorption, reduceCtorEq] at hold'
        | cons b2 rest2 =>
          obtain ⟨e, hm, _, ho⟩ := lookupForwardEdge_eq_some_mem hl
          have hcap' : capacityPart p next ∈
              occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
            rw [← ho]; exact occupiedCapacities_output _ _ table hm
          obtain ⟨hinv, par, last, hsplit, heval, habs, hout⟩ :=
            ih next (List.cons_ne_nil _ _) hcap' hnew' hold'
          refine ⟨hinv, par, last, ?_, ?_, habs, hout⟩
          · simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), List.cons_append]
            exact congrArg (b :: ·) hsplit
          · simp only [List.dropLast_cons_of_ne_nil (List.cons_ne_nil _ _), evalAbsorption, hl]
            exact heval
      | none =>
        rw [lookupForwardEdge_append_of_none hl] at hnew'
        simp only [lookupForwardEdge] at hnew'
        split_ifs at hnew' with hx
        · have hinv : edge.inverse = false := by
            cases hi : edge.inverse with
            | false => rfl
            | true =>
              have hc : capacityPart p edge.input ∈
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
                rw [hx, capacityPart_absorbBlock]; exact hcap
              have hnot : capacityPart p edge.input ∉
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
                simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, hi,
                  ↓reduceIte] using hf
              exact False.elim (hnot hc)
          cases rest with
          | nil =>
            simp only [evalAbsorption, Option.some.injEq] at hnew'
            exact ⟨hinv, state, b, rfl, rfl, hx.symm, hnew'.symm⟩
          | cons b2 rest2 =>
            simp only [evalAbsorption] at hnew'
            have hcapOut : capacityPart p edge.output ∉
                occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
              simpa only [AvoidsOccupiedCapacity, PermutationEdge.freshEndpoint, hinv,
                Bool.false_eq_true, ↓reduceIte] using hf
            have hnone2 : lookupForwardEdge table (absorbBlock p edge.output b2) = none := by
              rw [lookupForwardEdge_eq_none_iff]
              intro e hm he
              have hc := occupiedCapacities_input (capacityPart p) (zeroState p.capacityBytes)
                table hm
              rw [he, capacityPart_absorbBlock] at hc
              exact hcapOut hc
            have hne2 : edge.input ≠ absorbBlock p edge.output b2 := by
              intro he
              have hc : capacityPart p edge.output = capacityPart p edge.input := by
                rw [he, capacityPart_absorbBlock]
              have hci : capacityPart p edge.input ∈
                  occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
                rw [hx, capacityPart_absorbBlock]; exact hcap
              exact hcapOut (hc ▸ hci)
            rw [lookupForwardEdge_append_of_none hnone2, lookupForwardEdge,
              ite_eq_right hne2] at hnew'
            simp only [lookupForwardEdge, reduceCtorEq] at hnew'
  exact helper (zeroState p.stateBytes) blocks hne
    (by rw [capacityPart_zeroState]; exact occupiedCapacities_zero _ _ table) hnew hold

end PartialTable

/-! ### Interfaces, shared ideal RO, real sponge converter, and lazy simulator -/

section InterfacesAndConverters

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-- Fixed-budget honest hash interface (`Evaluation M (ByteState p.outputBytes) q_honest`). -/
abbrev HonestInterface (q_honest : ℕ) : Interface :=
  Evaluation M (ByteState p.outputBytes) q_honest

/-- Simulator's inside random-oracle interface (`Evaluation M (ByteState p.outputBytes) q_pub`). -/
abbrev SimROInterface (q_pub : ℕ) : Interface :=
  Evaluation M (ByteState p.outputBytes) q_pub

/-- Public bidirectional primitive interface (`Bidirectional (ByteState p.stateBytes) q`). -/
abbrev PrimitiveInterface (q : ℕ) : Interface :=
  Bidirectional (ByteState p.stateBytes) q

/-- Work-budgeted honest hash interface admitting nonempty query lists whose total absorbed
padded blocks are at most `w`. -/
def workHonestInterface (hp : p.Valid) (encode : M → List (BitVec 8)) (w : ℕ) : Interface :=
  Interface.mk Evaluation.Port (fun _ => M) (fun _ => ByteState p.outputBytes)
    (fun xs => xs ≠ [] ∧ (xs.map fun q => paddedBlockCount p (encode q.2).length).sum ≤ w)
    (by
      refine ⟨fun h => h.1 rfl, ?_⟩
      intro pre xs hpre hne hxs
      refine ⟨hne, ?_⟩
      obtain ⟨suf, rfl⟩ := hpre
      have hsum := hxs.2
      simp only [List.map_append, List.sum_append] at hsum
      omega)
    w
    (by
      intro xs hxs
      have hge : ∀ ys : List (Σ _ : Evaluation.Port, M),
          ys.length ≤ (ys.map fun q => paddedBlockCount p (encode q.2).length).sum := by
        intro ys
        induction ys with
        | nil => exact le_rfl
        | cons x rest ih =>
          simp only [List.length_cons, List.map_cons, List.sum_cons]
          have hpos : 1 ≤ paddedBlockCount p (encode x.2).length :=
            paddedBlockCount_pos p (encode x.2).length hp.1
          omega
      exact (hge xs).trans hxs.2)

/-- Total block-work bound on an honest interface over `Evaluation.Port`, `M`, and
`ByteState p.outputBytes`. -/
structure HonestWorkSpec (encode : M → List (BitVec 8)) (w : ℕ) where
  /-- Admitted nonempty prefix-closed honest query sequences. -/
  admits : List (Σ _ : Evaluation.Port, M) → Prop
  /-- The empty history is rejected and nonempty prefixes remain admitted. -/
  nonempty_prefix : ¬ admits [] ∧ ∀ {pre h}, pre <+: h → pre ≠ [] → admits h → admits pre
  /-- Upper bound on the number of honest queries. -/
  bound : ℕ
  /-- Every admitted honest history has length at most `bound`. -/
  length_le : ∀ xs, admits xs → xs.length ≤ bound
  /-- Total padded blocks absorbed across any admitted honest history is at most `w`. -/
  work_le : ∀ xs, admits xs → (xs.map fun q => paddedBlockCount p (encode q.2).length).sum ≤ w

/-- The `Interface` associated with an `HonestWorkSpec`. -/
abbrev HonestWorkSpec.toInterface {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) : Interface :=
  Interface.mk Evaluation.Port (fun _ => M) (fun _ => ByteState p.outputBytes)
    spec.admits spec.nonempty_prefix spec.bound spec.length_le

/-- Work-budgeted honest specification for `workHonestInterface`. -/
def HonestWorkSpec.ofWorkBudget (hp : p.Valid) (encode : M → List (BitVec 8)) (w : ℕ) :
    HonestWorkSpec p M encode w where
  admits := (workHonestInterface p M hp encode w).domain
  nonempty_prefix := (workHonestInterface p M hp encode w).nonempty_prefix
  bound := (workHonestInterface p M hp encode w).bound
  length_le := (workHonestInterface p M hp encode w).length_le
  work_le _ h := h.2

/-- Fixed-budget honest specification whose interface is definitionally `HonestInterface p M q`. -/
def HonestWorkSpec.ofFixedBudget (encode : M → List (BitVec 8)) (maxBlocks : ℕ)
    (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks) (q_honest : ℕ) :
    HonestWorkSpec p M encode (q_honest * maxBlocks) where
  admits := (HonestInterface p M q_honest).domain
  nonempty_prefix := (HonestInterface p M q_honest).nonempty_prefix
  bound := (HonestInterface p M q_honest).bound
  length_le := (HonestInterface p M q_honest).length_le
  work_le xs hxs := by
    have hsum : ∀ ys : List (Σ _ : Evaluation.Port, M),
        (ys.map fun q => paddedBlockCount p (encode q.2).length).sum ≤
          ys.length * maxBlocks := by
      intro ys
      induction ys with
      | nil => simp only [List.map_nil, List.sum_nil, List.length_nil, zero_mul, le_rfl]
      | cons x rest ih =>
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, one_mul]
        have hx := hmax x.2
        omega
    exact (hsum xs).trans (Nat.mul_le_mul_right maxBlocks hxs.2)

omit [DecidableEq M] in
lemma HonestWorkSpec.ofFixedBudget_toInterface (encode : M → List (BitVec 8)) (maxBlocks : ℕ)
    (hmax : ∀ m : M, paddedBlockCount p (encode m).length ≤ maxBlocks) (q_honest : ℕ) :
    (HonestWorkSpec.ofFixedBudget p M encode maxBlocks hmax q_honest).toInterface =
      HonestInterface p M q_honest := rfl

omit [DecidableEq M] in
lemma HonestWorkSpec.ofWorkBudget_toInterface (hp : p.Valid) (encode : M → List (BitVec 8))
    (w : ℕ) :
    (HonestWorkSpec.ofWorkBudget p M hp encode w).toInterface =
      workHonestInterface p M hp encode w := rfl

open Classical in
/-- Shared ideal random oracle exposing one retained uniform function `f : M → ByteState
outputBytes`
across both the honest port `spec.toInterface` and the simulator port `SimROInterface p M q_pub`. -/
noncomputable def sharedIdealRO {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    TypedSystem (spec.toInterface ⊗ SimROInterface p M q_pub) :=
  TypedSystem.sample (uniform (M → ByteState p.outputBytes)) fun f =>
    TypedSystem.parallel
      (TypedSystem.ofFunction (A := spec.toInterface) fun _ => f)
      (TypedSystem.ofFunction (A := SimROInterface p M q_pub) fun _ => f)

/-! #### Real sponge construction converter `spongePublic` -/

/-- Program body of `spongePublic`: honest queries absorb padded blocks via `forward`; public
queries pass directly to `Bidirectional`. -/
noncomputable def spongePublicProgram {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub Q : ℕ) :
    Program Unit (spec.toInterface ⊗ PrimitiveInterface p q_pub).I (PrimitiveInterface p Q).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y
      (PrimitiveInterface p Q).X (PrimitiveInterface p Q).Y
  | (), Sum.inl Evaluation.Port.eval, m =>
    forEach (paddedBlocks p (encode m))
      (fun block k state =>
        callProg Bidirectional.Port.forward (absorbBlock p state block) k)
      (fun state => returnProg ((), digestPart p state))
      (zeroState p.stateBytes)
  | (), Sum.inr Bidirectional.Port.forward, x =>
    callProg Bidirectional.Port.forward x (fun y => returnProg ((), y))
  | (), Sum.inr Bidirectional.Port.inverse, y =>
    callProg Bidirectional.Port.inverse y (fun x => returnProg ((), x))

/-- Exact primitive query cost of each query on `spec.toInterface ⊗ PrimitiveInterface p q_pub`. -/
def spongePublicCost {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) → ℕ
  | ⟨Sum.inl Evaluation.Port.eval, m⟩ => paddedBlockCount p (encode m).length
  | ⟨Sum.inr Bidirectional.Port.forward, _⟩ => 1
  | ⟨Sum.inr Bidirectional.Port.inverse, _⟩ => 1

omit [DecidableEq M] in
lemma spongePublicProgram_costs {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub Q : ℕ) :
    (spongePublicProgram p M spec q_pub Q).Costs (spongePublicCost p M spec q_pub) := by
  intro s o u
  let B := PrimitiveInterface p Q
  cases s
  rcases o with o | o
  · cases o
    dsimp only [spongePublicProgram, spongePublicCost]
    have hlen : 0 + (paddedBlocks p (encode u)).length * 1 =
        paddedBlockCount p (encode u).length := by
      rw [zero_add, mul_one, length_paddedBlocks]
    exact (callCost_foldr (X := B.X) (Y := B.Y) (paddedBlocks p (encode u))
      (fun block k state =>
        callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p state block) k)
      (fun state => returnProg ((), digestPart p state)) 0 1
      (fun s => callCost_return ((), digestPart p s))
      (fun b n k hk s =>
        callCost_call (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p s b) k hk)
      (zeroState p.stateBytes)).of_eq hlen
  · cases o with
    | forward =>
      exact callCost_call (X := B.X) (Y := B.Y) Bidirectional.Port.forward u _
        (fun y => callCost_return ((), y))
    | inverse =>
      exact callCost_call (X := B.X) (Y := B.Y) Bidirectional.Port.inverse u _
        (fun x => callCost_return ((), x))

/-- Explicit uniform per-invocation call bound for `spongePublicProgram`. -/
def spongePublicMaxStep (encode : M → List (BitVec 8)) : ℕ :=
  max 1 (Finset.univ.sup fun m : M => paddedBlockCount p (encode m).length)

omit [DecidableEq M] in
lemma one_le_spongePublicMaxStep (encode : M → List (BitVec 8)) :
    1 ≤ spongePublicMaxStep p M encode :=
  le_max_left _ _

omit [DecidableEq M] in
lemma paddedBlockCount_le_spongePublicMaxStep (encode : M → List (BitVec 8)) (m : M) :
    paddedBlockCount p (encode m).length ≤ spongePublicMaxStep p M encode :=
  (Finset.le_sup (f := fun m : M => paddedBlockCount p (encode m).length)
    (Finset.mem_univ m)).trans (le_max_right _ _)

omit [DecidableEq M] in
lemma spongePublicProgram_bounded {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub Q : ℕ) :
    (spongePublicProgram p M spec q_pub Q).Bounded (spongePublicMaxStep p M encode) := by
  intro s o u h q hc hq
  have hlt := (spongePublicProgram_costs p M spec q_pub Q s o u h hc).1 q hq
  rcases o with o | o
  · cases o
    exact lt_of_lt_of_le hlt (paddedBlockCount_le_spongePublicMaxStep p M encode u)
  · cases o <;> exact lt_of_lt_of_le hlt (one_le_spongePublicMaxStep p M encode)

omit [DecidableEq M] in
lemma spongePublicCost_sum_le {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (us : List (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o))
    (hus : (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain us) :
    (us.map (spongePublicCost p M spec q_pub)).sum ≤ w + q_pub := by
  classical
  have hsplit : ∀ xs : List (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o),
      (xs.map (spongePublicCost p M spec q_pub)).sum =
        ((SystemAlgebra.restrict none
            (xs.map (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p
              q_pub).X)).symm)).map
          fun q => paddedBlockCount p (encode q.2).length).sum +
        (SystemAlgebra.restrict (some ())
            (xs.map (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p
              q_pub).X)).symm)).length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x rest ih =>
      rcases x with ⟨o, u⟩
      rcases o with o | o
      · cases o
        have h1 : (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p q_pub).X)).symm
            ⟨Sum.inl Evaluation.Port.eval, u⟩ = ⟨none, ⟨Evaluation.Port.eval, u⟩⟩ := rfl
        rw [List.map_cons, List.map_cons, List.sum_cons, h1]
        simp only [spongePublicCost, SystemAlgebra.restrict, ↓reduceDIte, reduceCtorEq,
          List.map_cons, List.sum_cons, ih]
        omega
      · cases o with
        | forward =>
          have h1 : (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p q_pub).X)).symm
              ⟨Sum.inr Bidirectional.Port.forward, u⟩ =
              ⟨some (), ⟨Bidirectional.Port.forward, u⟩⟩ := rfl
          rw [List.map_cons, List.map_cons, List.sum_cons, h1]
          simp only [spongePublicCost, SystemAlgebra.restrict, ↓reduceDIte, reduceCtorEq,
            List.length_cons, ih]
          omega
        | inverse =>
          have h1 : (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p q_pub).X)).symm
              ⟨Sum.inr Bidirectional.Port.inverse, u⟩ =
              ⟨some (), ⟨Bidirectional.Port.inverse, u⟩⟩ := rfl
          rw [List.map_cons, List.map_cons, List.sum_cons, h1]
          simp only [spongePublicCost, SystemAlgebra.restrict, ↓reduceDIte, reduceCtorEq,
            List.length_cons, ih]
          omega
  rw [hsplit us]
  have hL :
      ((SystemAlgebra.restrict none
          (us.map (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p
            q_pub).X)).symm)).map
        fun q => paddedBlockCount p (encode q.2).length).sum ≤ w := by
    rcases hus.2.1 with he | hd
    · rw [he]; exact Nat.zero_le _
    · exact spec.work_le _ hd
  have hR :
      (SystemAlgebra.restrict (some ())
          (us.map (sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p
            q_pub).X)).symm)).length ≤
        q_pub := by
    rcases hus.2.2 with he | hd
    · rw [he]; exact Nat.zero_le _
    · exact hd.2
  exact Nat.add_le_add hL hR

/-- Real sponge converter `H ⊗ P ⟶ Bidirectional (ByteState p.stateBytes) (w + q_pub)`. -/
noncomputable def spongePublic {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    TypedConverter (spec.toInterface ⊗ PrimitiveInterface p q_pub)
      (PrimitiveInterface p (w + q_pub)) :=
  TypedConverter.ofCostedProgram ()
    (spongePublicProgram p M spec q_pub (w + q_pub))
    (spongePublicProgram_bounded p M spec q_pub (w + q_pub))
    (spongePublicCost p M spec q_pub)
    (spongePublicProgram_costs p M spec q_pub (w + q_pub))
    (spongePublicCost_sum_le p M spec q_pub)
    (fun _xs hne hlen => ⟨hne, hlen⟩)

/-! #### Lazy sponge simulator `spongeSimulator` [1, §4] -/

/-- Internal randomness source interface for `spongeSimulator`: at most `2 * q_pub` fresh draws. -/
abbrev SimCoinInterface (q_pub : ℕ) : Interface :=
  Evaluation Unit (ByteState p.stateBytes) (2 * q_pub)

/-- Memoryless source of fresh uniform sponge states for `spongeSimulator`. -/
noncomputable def simCoinSource (q_pub : ℕ) : TypedSystem (SimCoinInterface p q_pub) :=
  TypedSystem.ofMemoryless (SimCoinInterface p q_pub) (fun _ _ => 𝒰[ByteState p.stateBytes])

open Classical in
/-- Deterministic program body of `spongeSimulator` calling `SimROInterface ⊗ SimCoinInterface`. -/
noncomputable def spongeSimProgram (encode : M → List (BitVec 8)) (q_pub : ℕ) :
    Program (List (PermutationEdge (ByteState p.stateBytes)))
      (PrimitiveInterface p q_pub).I (SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub).I
      (PrimitiveInterface p q_pub).X (PrimitiveInterface p q_pub).Y
      (SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub).X
      (SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub).Y
  | table, Bidirectional.Port.forward, x =>
    match lookupForwardEdge table x with
    | some y => returnProg (table, y)
    | none =>
      match completingMessage p encode table x with
      | some m =>
        callProg (Sum.inl Evaluation.Port.eval) m fun d =>
          callProg (Sum.inr Evaluation.Port.eval) () fun r =>
            let y := assembleState p d (tailPart p r)
            returnProg (recordForwardEdge table x y, y)
      | none =>
        callProg (Sum.inr Evaluation.Port.eval) () fun y =>
          returnProg (recordForwardEdge table x y, y)
  | table, Bidirectional.Port.inverse, y =>
    match lookupInverseEdge table y with
    | some x => returnProg (table, x)
    | none =>
      callProg (Sum.inr Evaluation.Port.eval) () fun x =>
        returnProg (recordInverseEdge table x y, x)

omit [DecidableEq M] in
open Classical in
lemma spongeSimProgram_bounded (encode : M → List (BitVec 8)) (q_pub : ℕ) :
    (spongeSimProgram p M encode q_pub).Bounded 2 := by
  intro table o u
  let B := SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub
  cases o with
  | forward =>
    dsimp only [spongeSimProgram]
    cases lookupForwardEdge table u with
    | some y => exact callBound_return 2 (table, y)
    | none =>
      cases completingMessage p encode table u with
      | some m =>
        exact callBound_call (X := B.X) (Y := B.Y) (b := 1) (Sum.inl Evaluation.Port.eval) m _
          fun d => callBound_call (X := B.X) (Y := B.Y) (b := 0) (Sum.inr Evaluation.Port.eval) () _
            fun r => callBound_return 0 _
      | none =>
        exact (callBound_call (X := B.X) (Y := B.Y) (b := 0) (Sum.inr Evaluation.Port.eval) () _
          fun y => callBound_return 0 _).mono (by omega)
  | inverse =>
    dsimp only [spongeSimProgram]
    cases lookupInverseEdge table u with
    | some x => exact callBound_return 2 (table, x)
    | none =>
      exact (callBound_call (X := B.X) (Y := B.Y) (b := 0) (Sum.inr Evaluation.Port.eval) () _
        fun x => callBound_return 0 _).mono (by omega)

/-- Port preservation map sending outside `forward` queries to the inside ideal-RO port. -/
def spongeSimPortMap (q_pub : ℕ) :
    (PrimitiveInterface p q_pub).I →
      Option (SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub).I
  | Bidirectional.Port.forward => some (Sum.inl Evaluation.Port.eval)
  | Bidirectional.Port.inverse => none

omit [DecidableEq M] in
open Classical in
lemma spongeSimProgram_portPreserving (encode : M → List (BitVec 8)) (q_pub : ℕ) :
    (spongeSimProgram p M encode q_pub).PortPreserving (spongeSimPortMap p M q_pub) := by
  intro table o u
  let B := SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub
  have hCoinNe : ∀ o', spongeSimPortMap p M q_pub o' ≠ some (Sum.inr Evaluation.Port.eval) := by
    intro o' h
    cases o' <;> simp only [spongeSimPortMap, Option.some.injEq, reduceCtorEq] at h
  have hFwdOnly : ∀ o', spongeSimPortMap p M q_pub o' = some (Sum.inl Evaluation.Port.eval) →
      o' = Bidirectional.Port.forward := by
    intro o' h
    cases o' with
    | forward => rfl
    | inverse => simp only [spongeSimPortMap, reduceCtorEq] at h
  have hAvoidCoin : ∀ (f : ByteState p.stateBytes →
        List (PermutationEdge (ByteState p.stateBytes)) × ByteState p.stateBytes),
      Avoids (X := B.X) (Y := B.Y) (spongeSimPortMap p M q_pub)
        (callProg (X := B.X) (Y := B.Y) (Sum.inr Evaluation.Port.eval) () fun r =>
          returnProg (f r)) := fun f =>
    avoids_call (X := B.X) (Y := B.Y) (spongeSimPortMap p M q_pub)
      (j := Sum.inr Evaluation.Port.eval) () _ (fun r => avoids_return _ _) hCoinNe
  cases o with
  | forward =>
    dsimp only [spongeSimProgram]
    cases lookupForwardEdge table u with
    | some y => exact preservesAt_return _ _ _
    | none =>
      cases completingMessage p encode table u with
      | some m =>
        exact preservesAt_call_self (X := B.X) (Y := B.Y) (spongeSimPortMap p M q_pub)
          (o := Bidirectional.Port.forward) (j := Sum.inl Evaluation.Port.eval) m _
          (fun d => hAvoidCoin _) hFwdOnly
      | none =>
        exact preservesAt_call_other (X := B.X) (Y := B.Y) (spongeSimPortMap p M q_pub)
          (o := Bidirectional.Port.forward) (j := Sum.inr Evaluation.Port.eval) () _
          (fun y => preservesAt_return _ _ _) hCoinNe
  | inverse =>
    dsimp only [spongeSimProgram]
    cases lookupInverseEdge table u with
    | some x => exact preservesAt_return _ _ _
    | none =>
      exact preservesAt_call_other (X := B.X) (Y := B.Y) (spongeSimPortMap p M q_pub)
        (o := Bidirectional.Port.inverse) (j := Sum.inr Evaluation.Port.eval) () _
        (fun x => preservesAt_return _ _ _) hCoinNe

open Classical in
/-- Deterministic core converter of `spongeSimulator` before attaching `simCoinSource`. -/
noncomputable def spongeSimCore (encode : M → List (BitVec 8)) (q_pub : ℕ) :
    TypedConverter (PrimitiveInterface p q_pub)
      (SimROInterface p M q_pub ⊗ SimCoinInterface p q_pub) :=
  TypedConverter.ofPreservingProgram [] (spongeSimProgram p M encode q_pub)
    (spongeSimProgram_bounded p M encode q_pub)
    (spongeSimPortMap p M q_pub) (spongeSimProgram_portPreserving p M encode q_pub)
    (fun _ => q_pub)
    (fun xs hxs o => (SystemAlgebra.length_restrict_le o xs).trans hxs.2)
    (fun ys hne hlen hprot => by
      refine ⟨hne, ?_, ?_⟩
      · by_cases he :
            SystemAlgebra.restrict none
              (ys.map (sumAlphabet (Sum.rec (SimROInterface p M q_pub).X
                (SimCoinInterface p q_pub).X)).symm) = []
        · exact Or.inl he
        · refine Or.inr ⟨he, ?_⟩
          have hsub :
              (SystemAlgebra.restrict none
                (ys.map (sumAlphabet (Sum.rec (SimROInterface p M q_pub).X
                  (SimCoinInterface p q_pub).X)).symm)).length =
                (SystemAlgebra.restrict (Sum.inl Evaluation.Port.eval) ys).length := by
            rw [← SystemAlgebra.restrict_restrict_sumAlphabet]
            have huniq : ∀ xs : List (Σ _ : Evaluation.Port, M),
                (SystemAlgebra.restrict Evaluation.Port.eval xs).length = xs.length := by
              intro xs
              induction xs with
              | nil => rfl
              | cons z rest ih =>
                rcases z with ⟨⟨⟩, m⟩
                simp only [SystemAlgebra.restrict, ↓reduceDIte, List.length_cons, ih]
            exact (huniq _).symm
          rw [hsub]
          exact hprot Bidirectional.Port.forward (Sum.inl Evaluation.Port.eval) rfl
      · by_cases he :
            SystemAlgebra.restrict (some ())
              (ys.map (sumAlphabet (Sum.rec (SimROInterface p M q_pub).X
                (SimCoinInterface p q_pub).X)).symm) = []
        · exact Or.inl he
        · refine Or.inr ⟨he, ?_⟩
          exact (SystemAlgebra.length_restrict_le _ _).trans (by simpa only [List.length_map] using
            hlen))

open Classical in
/-- Lazy sponge simulator [1, §4] `Bidirectional (ByteState p.stateBytes) q_pub ⟶
Evaluation M (ByteState p.outputBytes) q_pub`. -/
noncomputable def spongeSimulator (encode : M → List (BitVec 8)) (q_pub : ℕ) :
    TypedConverter (PrimitiveInterface p q_pub) (SimROInterface p M q_pub) :=
  TypedConverter.comp (spongeSimCore p M encode q_pub)
    (TypedConverter.rightContext (SimROInterface p M q_pub) (simCoinSource p q_pub))

end InterfacesAndConverters

/-! ### Exact semantics of the real and ideal sponge systems -/

section RealAndIdealSemantics

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-- Deterministic reply of the real sponge construction under a fixed permutation `π`. -/
def spongeRealAnswer {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (π : Equiv.Perm (ByteState p.stateBytes)) :
    (q : Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) →
      Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o
  | ⟨Sum.inl Evaluation.Port.eval, m⟩ =>
    ⟨Sum.inl Evaluation.Port.eval, spongeHash p π (encode m)⟩
  | ⟨Sum.inr Bidirectional.Port.forward, x⟩ =>
    ⟨Sum.inr Bidirectional.Port.forward, π x⟩
  | ⟨Sum.inr Bidirectional.Port.inverse, y⟩ =>
    ⟨Sum.inr Bidirectional.Port.inverse, π.symm y⟩

omit [Fintype M] [DecidableEq M] in
lemma ofCostedProgram_smul_ofProbAutomaton
    {A B : Interface} {S R : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (cost : (Σ o, A.X o) → ℕ) (hc : P.Costs cost) {q : ℕ}
    (hA : ∀ us, A.domain us → (us.map cost).sum ≤ q)
    (hB : ∀ xs, xs ≠ [] → xs.length ≤ q → B.domain xs)
    (step : ProbStep R B.I B.X B.Y) (init : ProbDist R) :
    TypedConverter.ofCostedProgram s P hb cost hc hA hB •
        TypedSystem.ofProbAutomaton B step init =
      TypedSystem.ofProbAutomaton A (P.probCombine step hb) (init.map fun r => (s, r)) :=
  Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton
    B.nonempty_prefix A.nonempty_prefix s P hb _ step init)

omit [Fintype M] [DecidableEq M] in
lemma ofPreservingProgram_smul_ofProbAutomaton
    {A B : Interface} {S R : Type} (s : S)
    (P : Program S A.I B.I A.X A.Y B.X B.Y) {b : ℕ} (hb : P.Bounded b)
    (ι : A.I → Option B.I) (hι : P.PortPreserving ι) (q : A.I → ℕ)
    (hA : ∀ xs, A.domain xs → ∀ o, (SystemAlgebra.restrict o xs).length ≤ q o)
    (hB : ∀ ys, ys ≠ [] → ys.length ≤ b * A.bound →
      (∀ o j, ι o = some j → (SystemAlgebra.restrict j ys).length ≤ q o) → B.domain ys)
    (step : ProbStep R B.I B.X B.Y) (init : ProbDist R) :
    TypedConverter.ofPreservingProgram s P hb ι hι q hA hB •
        TypedSystem.ofProbAutomaton B step init =
      TypedSystem.ofProbAutomaton A (P.probCombine step hb) (init.map fun r => (s, r)) :=
  Subtype.ext (PDCBehavior.attach_ofDDC_ofProgramOn_ofProbAutomaton
    B.nonempty_prefix A.nonempty_prefix s P hb _ step init)

omit [Fintype M] [DecidableEq M] in
/-- Shifting the accumulated inside history of `Program.invoke` when two bodies on possibly
different outside port types (sharing the reply type `V₁ o₁`) agree on all extensions. -/
lemma invoke_eq_of_shift {S O₁ O₂ J R : Type} {U₁ : O₁ → Type} {U₂ : O₂ → Type}
    {V₁ : O₁ → Type} {X Y : J → Type}
    {s₁ s₂ : S} {o₁ : O₁} {o₂ : O₂} {u₁ : U₁ o₁} {u₂ : U₂ o₂}
    (P₁ : Program S O₁ J U₁ V₁ X Y)
    (P₂ : Program S O₂ J U₂ (fun _ => V₁ o₁) X Y)
    (stepR : R → (j : J) → X j → R × Y j)
    (pref : List ((Σ j, X j) × (Σ j, Y j)))
    (hshift : ∀ t, P₁ s₁ o₁ u₁ (pref ++ t) = P₂ s₂ o₂ u₂ t) :
    ∀ n r t, P₁.invoke stepR s₁ o₁ u₁ n r (pref ++ t) = P₂.invoke stepR s₂ o₂ u₂ n r t := by
  intro n
  induction n with
  | zero =>
    intro r t
    simp only [Program.invoke, hshift t]
  | succ n ih =>
    intro r t
    simp only [Program.invoke, hshift t]
    cases P₂ s₂ o₂ u₂ t with
    | inl a => rfl
    | inr q =>
      simp only [List.append_assoc]
      exact ih (stepR r q.1 q.2).1 (t ++ [(q, ⟨q.1, (stepR r q.1 q.2).2⟩)])

omit [Fintype M] [DecidableEq M] in
/-- Shifting the accumulated inside history of `Program.probInvoke` when two bodies on possibly
different outside port types (sharing the reply type `V₁ o₁`) agree on all extensions. -/
lemma probInvoke_eq_of_shift {S O₁ O₂ J R : Type} {U₁ : O₁ → Type} {U₂ : O₂ → Type}
    {V₁ : O₁ → Type} {X Y : J → Type}
    {s₁ s₂ : S} {o₁ : O₁} {o₂ : O₂} {u₁ : U₁ o₁} {u₂ : U₂ o₂}
    (P₁ : Program S O₁ J U₁ V₁ X Y)
    (P₂ : Program S O₂ J U₂ (fun _ => V₁ o₁) X Y)
    (stepR : ProbStep R J X Y)
    (pref : List ((Σ j, X j) × (Σ j, Y j)))
    (hshift : ∀ t, P₁ s₁ o₁ u₁ (pref ++ t) = P₂ s₂ o₂ u₂ t) :
    ∀ n r t,
      P₁.probInvoke stepR s₁ o₁ u₁ n r (pref ++ t) = P₂.probInvoke stepR s₂ o₂ u₂ n r t := by
  intro n
  induction n with
  | zero =>
    intro r t
    simp only [Program.probInvoke, hshift t]
    cases P₂ s₂ o₂ u₂ t <;> rfl
  | succ n ih =>
    intro r t
    simp only [Program.probInvoke, hshift t]
    cases P₂ s₂ o₂ u₂ t with
    | inl a => rfl
    | inr q =>
      apply bindK_congr
      intro p' _
      simp only [List.append_assoc]
      exact ih p'.1 (t ++ [(q, p'.2)])

/-- Function presentation of a permutation on `PrimitiveInterface p Q`. -/
def permFn (Q : ℕ) (π : Equiv.Perm (ByteState p.stateBytes)) :
    ∀ j : (PrimitiveInterface p Q).I, (PrimitiveInterface p Q).X j → (PrimitiveInterface p Q).Y j
  | Bidirectional.Port.forward, x => π x
  | Bidirectional.Port.inverse, y => π.symm y

/-- Function presentation of the real sponge system under a fixed permutation `π`. -/
def spongeRealFn {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (π : Equiv.Perm (ByteState p.stateBytes)) :
    ∀ o : (spec.toInterface ⊗ PrimitiveInterface p q_pub).I,
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o →
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o
  | Sum.inl Evaluation.Port.eval, m => spongeHash p π (encode m)
  | Sum.inr Bidirectional.Port.forward, x => π x
  | Sum.inr Bidirectional.Port.inverse, y => π.symm y

omit [Fintype M] [DecidableEq M] in
/-- Any deterministic function system equals a constant-state automaton. -/
lemma ofFunction_eq_ofAutomaton (A : Interface) (f : ∀ i, A.X i → A.Y i) :
    TypedSystem.ofFunction (A := A) f =
      TypedSystem.ofAutomaton A (fun (s : Unit) i x => (s, f i x)) (ProbDist.single ()) := by
  symm
  refine TypedSystem.eq_ofFunction _ f fun h hadm hall => ?_
  rw [TypedSystem.ofAutomaton_mass, ProbDist.single, mass_single]
  have hdd := Interface.automatonDDS_eq_ofFunction A (fun (_ : Unit) => f) ()
  have hrep : Replies (filterDom A.domain (automatonSystem (fun (s : Unit) i x => (s, f i x)) ()))
      (h.map Prod.fst) (h.map Prod.snd) := by
    change Replies (A.automatonDDS (fun (s : Unit) i x => (s, f i x)) ()).1
      (h.map Prod.fst) (h.map Prod.snd)
    rw [hdd, DDS.replies_ofFunction_iff, List.map_eq_nil_iff, List.map_map, List.map_eq_map_iff]
    exact ⟨hadm, hall⟩
  exact ite_eq_left hrep

omit [DecidableEq M] in
/-- Exact transcript mass of `spongePublic • StrongURP` as a uniform permutation probability. -/
lemma spongePublic_smul_strongURP_mass_aux {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (π : Equiv.Perm (ByteState p.stateBytes)) :
    spongePublic p M spec q_pub •
        TypedSystem.ofFunction (A := PrimitiveInterface p (w + q_pub)) (permFn p (w + q_pub) π) =
      TypedSystem.ofFunction (A := spec.toInterface ⊗ PrimitiveInterface p q_pub)
        (spongeRealFn p M spec q_pub π) := by
  classical
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let B := PrimitiveInterface p (w + q_pub)
  let permStep : Unit → (j : B.I) → B.X j → Unit × B.Y j :=
    fun s j x => (s, permFn p (w + q_pub) π j x)
  rw [ofFunction_eq_ofAutomaton B (permFn p (w + q_pub) π), spongePublic,
    TypedConverter.ofCostedProgram_smul_ofAutomaton]
  have hfold : ∀ (blocks : List (ByteState p.rateBytes)) (n : ℕ)
      (state : ByteState p.stateBytes) (hn : blocks.length ≤ n),
      Program.invoke (O := Unit) (U := fun _ => Unit) (V := fun _ => ByteState p.outputBytes)
        (fun _ _ _ =>
          forEach blocks
            (fun block k s =>
              callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p s block) k)
            (fun s => returnProg ((), digestPart p s)) state)
        permStep () () () n () [] =
      some (((), ()), digestPart p (absorbBlocks (absorbBlock p) π state blocks)) := by
    intro blocks
    induction blocks with
    | nil =>
      intro n state _
      cases n <;> simp only [forEach, List.foldr_nil, returnProg, Program.invoke, absorbBlocks_nil,
        Sum.elim_inl]
    | cons b rest ih =>
      intro n state hn
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
        simp only [List.length_cons] at hn
        simp only [forEach, List.foldr_cons, Program.invoke, callProg, List.nil_append]
        have hsh := invoke_eq_of_shift
          (P₁ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p state b)
              (fun next =>
                forEach rest
                  (fun block k s => callProg (X := B.X) (Y := B.Y)
                    Bidirectional.Port.forward (absorbBlock p s block) k)
                  (fun s => returnProg ((), digestPart p s)) next))
          (P₂ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            forEach rest
              (fun block k s => callProg (X := B.X) (Y := B.Y)
                Bidirectional.Port.forward (absorbBlock p s block) k)
              (fun s => returnProg ((), digestPart p s)) (π (absorbBlock p state b)))
          permStep (s₁ := ()) (s₂ := ()) (o₁ := ()) (o₂ := ()) (u₁ := ()) (u₂ := ())
          [(⟨Bidirectional.Port.forward, absorbBlock p state b⟩,
            ⟨Bidirectional.Port.forward, π (absorbBlock p state b)⟩)]
          (fun t => by simp only [List.singleton_append, callProg, ↓reduceDIte])
          n () []
        simp only [List.append_nil] at hsh
        simpa only [permStep, permFn, absorbBlocks_cons] using
          hsh.trans (ih n (π (absorbBlock p state b)) (by omega))
  have hcomb :
      (spongePublicProgram p M spec q_pub (w + q_pub)).combine permStep
        (spongePublicProgram_bounded p M spec q_pub (w + q_pub)) =
      fun sr o u => (sr, spongeRealFn p M spec q_pub π o u) := by
    funext ⟨s, r⟩ o u
    cases s; cases r
    have hinv_eq :
        (spongePublicProgram p M spec q_pub (w + q_pub)).invoke permStep () o u
          (spongePublicMaxStep p M encode) () [] =
        some (((), ()), spongeRealFn p M spec q_pub π o u) := by
      rcases o with o | o
      · cases o
        have hbd : (paddedBlocks p (encode u)).length ≤ spongePublicMaxStep p M encode := by
          rw [length_paddedBlocks]
          exact paddedBlockCount_le_spongePublicMaxStep p M encode u
        have hsame := invoke_eq_of_shift
          (P₁ := spongePublicProgram p M spec q_pub (w + q_pub))
          (P₂ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            forEach (paddedBlocks p (encode u))
              (fun block k s =>
                callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward
                  (absorbBlock p s block) k)
              (fun s => returnProg ((), digestPart p s)) (zeroState p.stateBytes))
          permStep (s₁ := ()) (s₂ := ()) (o₁ := Sum.inl Evaluation.Port.eval) (o₂ := ())
          (u₁ := u) (u₂ := ()) [] (fun _ => rfl)
          (spongePublicMaxStep p M encode) () []
        exact hsame.trans (hfold (paddedBlocks p (encode u)) (spongePublicMaxStep p M encode)
          (zeroState p.stateBytes) hbd)
      · have h1 : 1 ≤ spongePublicMaxStep p M encode := one_le_spongePublicMaxStep p M encode
        obtain ⟨k, hk⟩ : ∃ k, spongePublicMaxStep p M encode = k + 1 :=
          ⟨_, (Nat.sub_add_cancel h1).symm⟩
        rw [hk]
        cases o with
        | forward =>
          cases k <;> simp only [Program.invoke, spongePublicProgram, callProg, returnProg,
            List.nil_append, ↓reduceDIte, permStep, permFn, spongeRealFn, Sum.elim_inl]
        | inverse =>
          cases k <;> simp only [Program.invoke, spongePublicProgram, callProg, returnProg,
            List.nil_append, ↓reduceDIte, permStep, permFn, spongeRealFn, Sum.elim_inl]
    simp only [Program.combine, hinv_eq, Option.get_some]
  rw [hcomb]
  refine TypedSystem.eq_ofFunction _ (spongeRealFn p M spec q_pub π) fun t hadm hall => ?_
  rw [TypedSystem.ofAutomaton_mass, ProbDist.map_val, ProbDist.single, fTransform_single,
    mass_single]
  have hdd := Interface.automatonDDS_eq_ofFunction A
    (fun (_ : Unit × Unit) => spongeRealFn p M spec q_pub π) ((), ())
  have hrep : Replies (filterDom A.domain (automatonSystem
      (fun sr o u => (sr, spongeRealFn p M spec q_pub π o u)) ((), ())))
      (t.map Prod.fst) (t.map Prod.snd) := by
    change Replies (A.automatonDDS (fun sr o u => (sr, spongeRealFn p M spec q_pub π o u)) ((),
      ())).1
      (t.map Prod.fst) (t.map Prod.snd)
    rw [hdd, DDS.replies_ofFunction_iff, List.map_eq_nil_iff, List.map_map, List.map_eq_map_iff]
    exact ⟨hadm, hall⟩
  exact ite_eq_left hrep

omit [DecidableEq M] in
/-- Exact transcript mass of `spongePublic • StrongURP` as a uniform permutation probability. -/
theorem spongePublic_smul_strongURP_mass {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (hadm : h = [] ∨ (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst)) :
    (spongePublic p M spec q_pub •
        StrongURP (ByteState p.stateBytes) (q := w + q_pub)).1 h =
      (uniform (Equiv.Perm (ByteState p.stateBytes))).mass fun π =>
        ∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2 := by
  classical
  rw [StrongURP, TypedConverter.smul_sample, TypedSystem.sample_mass]
  have hunif : ∀ (h₁ h₂ : Fintype (Equiv.Perm (ByteState p.stateBytes))),
      @uniform (Equiv.Perm (ByteState p.stateBytes)) h₁ _ =
        @uniform (Equiv.Perm (ByteState p.stateBytes)) h₂ _ := fun h₁ h₂ => by
    congr 1
    exact Subsingleton.elim h₁ h₂
  rw [hunif _ inferInstance]
  have hcongr : ∀ π : Equiv.Perm (ByteState p.stateBytes),
      (spongePublic p M spec q_pub •
        TypedSystem.ofFunction (A := PrimitiveInterface p (w + q_pub))
          (permFn p (w + q_pub) π)).1 h =
      if ∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2 then 1 else 0 := by
    intro π
    rw [spongePublic_smul_strongURP_mass_aux p M spec q_pub π, TypedSystem.ofFunction_mass]
    simp only [hadm, true_and]
    have heq :
        (∀ z ∈ h, z.2 = ⟨z.1.1, spongeRealFn p M spec q_pub π z.1.1 z.1.2⟩) ↔
        (∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2) := by
      constructor
      · intro hr z hz
        have h1 := (hr z hz).symm
        rcases z with ⟨⟨o, u⟩, y⟩
        rcases o with o | o
        · cases o; exact h1
        · cases o <;> exact h1
      · intro hr z hz
        have h1 := (hr z hz).symm
        rcases z with ⟨⟨o, u⟩, y⟩
        rcases o with o | o
        · cases o; exact h1
        · cases o <;> exact h1
    by_cases hp : ∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2
    · rw [ite_eq_left (heq.mpr hp), ite_eq_left hp]
    · rw [ite_eq_right (mt heq.mp hp), ite_eq_right hp]
  simp only [mass, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro π _
  trans (uniform (Equiv.Perm (ByteState p.stateBytes))) π *
      if ∀ z ∈ h, spongeRealAnswer p M spec q_pub π z.1 = z.2 then 1 else 0
  · congr 1
    refine (congrArg (fun f =>
        (spongePublic p M spec q_pub •
          TypedSystem.ofFunction (A := Bidirectional (ByteState p.stateBytes) (w + q_pub)) f).1 h)
      ?_).trans (hcongr π)
    funext j x
    cases j <;> rfl
  · rw [mul_ite, mul_one, mul_zero]
    split_ifs <;> rfl

/-! #### Hop-1 automaton presentation of `spongePublic • LazyBidirectionalRF` -/

/-- Run a sequence of rate blocks sequentially against `lazyBidirectionalRFStep`. -/
noncomputable def absorbRFBlocks (q : ℕ) :
    List (ByteState p.stateBytes × ByteState p.stateBytes) → ByteState p.stateBytes →
      List (ByteState p.rateBytes) →
      ProbDist (List (ByteState p.stateBytes × ByteState p.stateBytes) × ByteState p.stateBytes)
  | table, state, [] => ProbDist.single (table, state)
  | table, state, block :: rest =>
    (lazyBidirectionalRFStep q table Bidirectional.Port.forward (absorbBlock p state block)).bind
      fun p' => absorbRFBlocks q p'.1 p'.2 rest

/-- Combined transition law of `spongePublic • LazyBidirectionalRF`. -/
noncomputable def realRFStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep (List (ByteState p.stateBytes × ByteState p.stateBytes))
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y
  | table, Sum.inl Evaluation.Port.eval, m =>
    (absorbRFBlocks p (w + q_pub) table (zeroState p.stateBytes) (paddedBlocks p (encode m))).map
      fun p' => (p'.1, digestPart p p'.2)
  | table, Sum.inr Bidirectional.Port.forward, x =>
    lazyBidirectionalRFStep (w + q_pub) table Bidirectional.Port.forward x
  | table, Sum.inr Bidirectional.Port.inverse, y =>
    lazyBidirectionalRFStep (w + q_pub) table Bidirectional.Port.inverse y

omit [DecidableEq M] in
/-- Attaching `spongePublic` to `LazyBidirectionalRF` yields the explicit automaton `realRFStep`. -/
theorem spongePublic_smul_lazyBidirectionalRF_eq {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    spongePublic p M spec q_pub •
        LazyBidirectionalRF (ByteState p.stateBytes) (w + q_pub) =
      TypedSystem.ofProbAutomaton (spec.toInterface ⊗ PrimitiveInterface p q_pub)
        (realRFStep p M spec q_pub) (ProbDist.single []) := by
  classical
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  let B := PrimitiveInterface p (w + q_pub)
  rw [spongePublic, LazyBidirectionalRF, ofCostedProgram_smul_ofProbAutomaton]
  have hfold : ∀ (blocks : List (ByteState p.rateBytes)) (n : ℕ)
      (table : List (ByteState p.stateBytes × ByteState p.stateBytes))
      (state : ByteState p.stateBytes) (hn : blocks.length ≤ n),
      Program.probInvoke (O := Unit) (U := fun _ => Unit) (V := fun _ => ByteState p.outputBytes)
        (fun _ _ _ =>
          forEach blocks
            (fun block k s =>
              callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p s block) k)
            (fun s => returnProg ((), digestPart p s)) state)
        (lazyBidirectionalRFStep (w + q_pub)) () () () n table [] =
      ((absorbRFBlocks p (w + q_pub) table state blocks).map
        fun p' => (((), p'.1), digestPart p p'.2)).1 := by
    intro blocks
    induction blocks with
    | nil =>
      intro n table state _
      cases n <;>
        simp only [forEach, List.foldr_nil, returnProg, Program.probInvoke, absorbRFBlocks,
          ProbDist.map_val, ProbDist.single, fTransform_single]
    | cons b rest ih =>
      intro n table state hn
      cases n with
      | zero => simp only [List.length_cons] at hn; omega
      | succ n =>
        simp only [List.length_cons] at hn
        simp only [forEach, List.foldr_cons, Program.probInvoke, callProg, List.nil_append,
          absorbRFBlocks, ProbDist.map_val, ProbDist.bind_val, fTransform_bindK]
        rw [ProbStep.outcome, bindK_fTransform]
        apply bindK_congr
        intro p' _
        have hsh := probInvoke_eq_of_shift
          (P₁ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward (absorbBlock p state b)
              (fun next =>
                forEach rest
                  (fun block k s => callProg (X := B.X) (Y := B.Y)
                    Bidirectional.Port.forward (absorbBlock p s block) k)
                  (fun s => returnProg ((), digestPart p s)) next))
          (P₂ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            forEach rest
              (fun block k s => callProg (X := B.X) (Y := B.Y)
                Bidirectional.Port.forward (absorbBlock p s block) k)
              (fun s => returnProg ((), digestPart p s)) p'.2)
          (lazyBidirectionalRFStep (w + q_pub)) (s₁ := ()) (s₂ := ()) (o₁ := ()) (o₂ := ())
          (u₁ := ()) (u₂ := ())
          [(⟨Bidirectional.Port.forward, absorbBlock p state b⟩,
            ⟨Bidirectional.Port.forward, p'.2⟩)]
          (fun t => by simp only [List.singleton_append, callProg, ↓reduceDIte])
          n p'.1 []
        simp only [List.append_nil] at hsh
        simpa only [Function.comp_def, ProbStep.tagged, ProbDist.map_val] using
          hsh.trans (ih n p'.1 p'.2 (by omega))
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A)
    ((spongePublicProgram p M spec q_pub (w + q_pub)).probCombine
      (lazyBidirectionalRFStep (w + q_pub)) (spongePublicProgram_bounded p M spec q_pub (w +
        q_pub)))
    (realRFStep p M spec q_pub)
    (fun sr => ProbDist.single sr.2)
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (by
      intro _ ⟨s, table⟩ ⟨o, u⟩ _ _
      cases s
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbDist.single,
        fTransform_single, bindK_single, one_smul, Function.comp_def,
        bindK_fTransform, ProbStep.tagged, Program.probCombine_val]
      rw [bindK_single_comp]
      rcases o with o | o
      · cases o
        have hbd : (paddedBlocks p (encode u)).length ≤ spongePublicMaxStep p M encode := by
          rw [length_paddedBlocks]
          exact paddedBlockCount_le_spongePublicMaxStep p M encode u
        have hsame := probInvoke_eq_of_shift
          (P₁ := spongePublicProgram p M spec q_pub (w + q_pub))
          (P₂ := fun (_ : Unit) (_ : Unit) (_ : Unit) =>
            forEach (paddedBlocks p (encode u))
              (fun block k s =>
                callProg (X := B.X) (Y := B.Y) Bidirectional.Port.forward
                  (absorbBlock p s block) k)
              (fun s => returnProg ((), digestPart p s)) (zeroState p.stateBytes))
          (lazyBidirectionalRFStep (w + q_pub)) (s₁ := ()) (s₂ := ())
          (o₁ := Sum.inl Evaluation.Port.eval) (o₂ := ()) (u₁ := u) (u₂ := ())
          [] (fun _ => rfl) (spongePublicMaxStep p M encode) table []
        simp only [List.nil_append] at hsame
        have hstep := hsame.trans (hfold (paddedBlocks p (encode u))
          (spongePublicMaxStep p M encode) table (zeroState p.stateBytes) hbd)
        rw [hstep]
        simp only [realRFStep, ProbDist.map_val, fTransform_fTransform, Function.comp_def]
        rfl
      · have h1 : 1 ≤ spongePublicMaxStep p M encode := one_le_spongePublicMaxStep p M encode
        obtain ⟨k, hk⟩ : ∃ k, spongePublicMaxStep p M encode = k + 1 :=
          ⟨_, (Nat.sub_add_cancel h1).symm⟩
        cases o with
        | forward =>
          rw [hk]
          simp only [Program.probInvoke, spongePublicProgram, callProg, List.nil_append,
            ProbStep.outcome, bindK_fTransform, realRFStep]
          rw [fTransform_bindK]
          have hfin : ∀ p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
              ByteState p.stateBytes,
              fTransform (fun x : (Unit × List (ByteState p.stateBytes × ByteState p.stateBytes)) ×
                  A.Y (Sum.inr Bidirectional.Port.forward) =>
                (x.1.2, (⟨Sum.inr Bidirectional.Port.forward, x.2⟩ : Σ i, A.Y i)))
                ((spongePublicProgram p M spec q_pub (w + q_pub)).probInvoke
                  (lazyBidirectionalRFStep (w + q_pub)) () (Sum.inr Bidirectional.Port.forward) u
                  k (ProbStep.tagged (Y := B.Y)
                      (⟨Bidirectional.Port.forward, u⟩ : Σ j, B.X j) p').1
                  [(⟨Bidirectional.Port.forward, u⟩,
                    (ProbStep.tagged (Y := B.Y)
                      (⟨Bidirectional.Port.forward, u⟩ : Σ j, B.X j) p').2)]) =
              Finsupp.single (ProbStep.tagged (Y := A.Y)
                (⟨Sum.inr Bidirectional.Port.forward, u⟩ : Σ i, A.X i) p') 1 := by
            intro p'
            cases k <;>
              simp only [Program.probInvoke, spongePublicProgram, callProg, ↓reduceDIte,
                returnProg, fTransform_single, ProbStep.tagged]
          rw [← bindK_single_comp]
          exact bindK_congr fun p' _ => (hfin p').symm
        | inverse =>
          rw [hk]
          simp only [Program.probInvoke, spongePublicProgram, callProg, List.nil_append,
            ProbStep.outcome, bindK_fTransform, realRFStep]
          rw [fTransform_bindK]
          have hfin : ∀ p' : List (ByteState p.stateBytes × ByteState p.stateBytes) ×
              ByteState p.stateBytes,
              fTransform (fun x : (Unit × List (ByteState p.stateBytes × ByteState p.stateBytes)) ×
                  A.Y (Sum.inr Bidirectional.Port.inverse) =>
                (x.1.2, (⟨Sum.inr Bidirectional.Port.inverse, x.2⟩ : Σ i, A.Y i)))
                ((spongePublicProgram p M spec q_pub (w + q_pub)).probInvoke
                  (lazyBidirectionalRFStep (w + q_pub)) () (Sum.inr Bidirectional.Port.inverse) u
                  k (ProbStep.tagged (Y := B.Y)
                      (⟨Bidirectional.Port.inverse, u⟩ : Σ j, B.X j) p').1
                  [(⟨Bidirectional.Port.inverse, u⟩,
                    (ProbStep.tagged (Y := B.Y)
                      (⟨Bidirectional.Port.inverse, u⟩ : Σ j, B.X j) p').2)]) =
              Finsupp.single (ProbStep.tagged (Y := A.Y)
                (⟨Sum.inr Bidirectional.Port.inverse, u⟩ : Σ i, A.X i) p') 1 := by
            intro p'
            cases k <;>
              simp only [Program.probInvoke, spongePublicProgram, callProg, ↓reduceDIte,
                returnProg, fTransform_single, ProbStep.tagged]
          rw [← bindK_single_comp]
          exact bindK_congr fun p' _ => (hfin p').symm)
    ((ProbDist.single []).map fun r => ((), r)) (fun _ _ => trivial)
  rw [hsim]
  congr 1
  apply Subtype.ext
  simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
    bindK_single, one_smul]

/-! #### Ideal automaton presentations of `(H ◁ spongeSimulator) • sharedIdealRO` -/

/-- Combined probabilistic step placing a deterministic function `f` on `A` beside `step` on `B`. -/
noncomputable def parallelFnProbStep {A B : Interface} {S : Type}
    (f : ∀ i, A.X i → A.Y i) (step : ProbStep S B.I B.X B.Y) :
    ProbStep S (A ⊗ B).I (A ⊗ B).X (A ⊗ B).Y
  | s, Sum.inl i, x => ProbDist.single (s, f i x)
  | s, Sum.inr j, y => step s j y

omit [Fintype M] [DecidableEq M] in
open Classical in
lemma parallelFnProbStep_transition_inl {A B : Interface} {S : Type}
    (f : ∀ i, A.X i → A.Y i) (step : ProbStep S B.I B.X B.Y)
    (μ : Distribution S) (i : A.I) (u : A.X i) (yq : Σ o, (A ⊗ B).Y o) :
    (parallelFnProbStep f step).transition μ ⟨Sum.inl i, u⟩ yq =
      if (⟨Sum.inl i, f i u⟩ : Σ o, (A ⊗ B).Y o) = yq then μ else 0 := by
  simp only [ProbStep.transition, ProbStep.outcome, parallelFnProbStep, ProbDist.single,
    fTransform_single, ProbStep.tagged, Distribution.single_restrict]
  by_cases h : (⟨Sum.inl i, f i u⟩ : Σ o, (A ⊗ B).Y o) = yq
  · simp only [h, ↓reduceIte, fTransform_single, bindK_single_one]
  · simp only [h, ↓reduceIte, fTransform_zero, bindK_zero_right]

omit [Fintype M] [DecidableEq M] in
lemma parallelFnProbStep_transition_inr_inl {A B : Interface} {S : Type}
    (f : ∀ i, A.X i → A.Y i) (step : ProbStep S B.I B.X B.Y)
    (μ : Distribution S) (j : B.I) (u : B.X j) (i' : A.I) (v : A.Y i') :
    (parallelFnProbStep f step).transition μ ⟨Sum.inr j, u⟩ ⟨Sum.inl i', v⟩ = 0 := by
  classical
  simp only [ProbStep.transition, ProbStep.outcome, parallelFnProbStep]
  have hr : ∀ s' : S,
      fTransform Prod.fst
        ((fTransform (ProbStep.tagged (⟨Sum.inr j, u⟩ : Σ o, (A ⊗ B).X o))
            (step s' j u).1).restrict fun sy =>
          sy.2 = (⟨Sum.inl i', v⟩ : Σ o, (A ⊗ B).Y o)) = 0 := by
    intro s'
    rw [Distribution.restrict_fTransform]
    have hfalse : ∀ x : S × B.Y j,
        ((ProbStep.tagged (⟨Sum.inr j, u⟩ : Σ o, (A ⊗ B).X o) x).2 =
          (⟨Sum.inl i', v⟩ : Σ o, (A ⊗ B).Y o)) ↔ False := by
      intro x
      simp only [ProbStep.tagged, iff_false]
      intro hEq
      have h1 := congrArg Sigma.fst hEq
      simp only [reduceCtorEq] at h1
    refine (congrArg (fTransform Prod.fst)
      (congrArg (fTransform (ProbStep.tagged (Y := (A ⊗ B).Y)
          (⟨Sum.inr j, u⟩ : Σ o, (A ⊗ B).X o)))
        ((Distribution.restrict_congr _ hfalse).trans (Distribution.restrict_false _)))).trans ?_
    rw [fTransform_zero, fTransform_zero]
  simp only [hr, bindK_zero_right]

omit [Fintype M] [DecidableEq M] in
lemma parallelFnProbStep_transition_inr_inr {A B : Interface} {S : Type}
    (f : ∀ i, A.X i → A.Y i) (step : ProbStep S B.I B.X B.Y)
    (μ : Distribution S) (j : B.I) (u : B.X j) (j' : B.I) (v : B.Y j') :
    (parallelFnProbStep f step).transition μ ⟨Sum.inr j, u⟩ ⟨Sum.inr j', v⟩ =
      step.transition μ ⟨j, u⟩ ⟨j', v⟩ := by
  classical
  simp only [ProbStep.transition, ProbStep.outcome, parallelFnProbStep]
  apply bindK_congr
  intro s' _
  rw [Distribution.restrict_fTransform, Distribution.restrict_fTransform,
    fTransform_fTransform, fTransform_fTransform]
  have hpred : ∀ x : S × B.Y j,
      ((ProbStep.tagged (⟨Sum.inr j, u⟩ : Σ o, (A ⊗ B).X o) x).2 =
        (⟨Sum.inr j', v⟩ : Σ o, (A ⊗ B).Y o)) ↔
      ((ProbStep.tagged (⟨j, u⟩ : Σ k, B.X k) x).2 = (⟨j', v⟩ : Σ k, B.Y k)) := by
    intro x
    simp only [ProbStep.tagged]
    constructor
    · intro hEq
      rcases Sigma.mk.inj_iff.mp hEq with ⟨hj, hv⟩
      obtain rfl : j = j' := Sum.inr.inj hj
      cases eq_of_heq hv
      rfl
    · intro hEq
      rcases Sigma.mk.inj_iff.mp hEq with ⟨rfl, hv⟩
      cases eq_of_heq hv
      rfl
  exact congrArg (fTransform Prod.fst) (Distribution.restrict_congr _ hpred)

omit [Fintype M] [DecidableEq M] in
/-- Parallel composition of a deterministic function on `A` with a probabilistic automaton on `B`.
-/
lemma parallel_ofFunction_ofProbAutomaton {A B : Interface} {S : Type}
    (f : ∀ i, A.X i → A.Y i) (step : ProbStep S B.I B.X B.Y) (init : ProbDist S) :
    TypedSystem.parallel (TypedSystem.ofFunction (A := A) f)
        (TypedSystem.ofProbAutomaton B step init) =
      TypedSystem.ofProbAutomaton (A ⊗ B) (parallelFnProbStep f step) init := by
  classical
  let eX := sumAlphabet (Sum.rec A.X B.X)
  let eY := sumAlphabet (Sum.rec A.Y B.Y)
  have hbelief : ∀ h : List ((Σ o, (A ⊗ B).X o) × (Σ o, (A ⊗ B).Y o)),
      (parallelFnProbStep f step).belief (A ⊗ B).inputDomain init.1 h =
        let p := h.map (eX.symm.prodCongr eY.symm)
        if RandomSystem.parallelConsistent p ∧
            (h = [] ∨ (A ⊗ B).domain (h.map Prod.fst)) ∧
            (∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) then
          step.belief B.inputDomain init.1 (RandomSystem.parallelRight p)
        else 0 := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      simp only [ProbStep.belief, ProbStep.beliefRev, List.reverse_nil, List.map_nil,
        RandomSystem.parallelConsistent, RandomSystem.parallelLeft, RandomSystem.parallelRight,
        List.filterMap_nil, List.not_mem_nil, false_implies, implies_true, true_and, true_or,
        ↓reduceIte]
    | append_singleton h z ih =>
      rcases z with ⟨⟨o, u⟩, ⟨o', v⟩⟩
      let xq : Σ o, (A ⊗ B).X o := ⟨o, u⟩
      let yq : Σ o, (A ⊗ B).Y o := ⟨o', v⟩
      let p := h.map (eX.symm.prodCongr eY.symm)
      have hmap : (h ++ [(xq, yq)]).map (eX.symm.prodCongr eY.symm) =
          p ++ [(eX.symm xq, eY.symm yq)] := by
        simp only [List.map_append, List.map_singleton, Equiv.prodCongr_apply, Prod.map_apply, p]
      rw [ProbStep.belief_snoc, ih]
      by_cases hadm : (A ⊗ B).domain (h.map Prod.fst ++ [xq])
      · have hadm' : (h ++ [(xq, yq)]) = [] ∨
            (A ⊗ B).domain ((h ++ [(xq, yq)]).map Prod.fst) :=
          Or.inr (by simpa only [List.map_append, List.map_singleton] using hadm)
        have hdom_pre : h = [] ∨ (A ⊗ B).domain (h.map Prod.fst) := by
          cases h with
          | nil => exact Or.inl rfl
          | cons w rest =>
            exact Or.inr ((A ⊗ B).nonempty_prefix.2 (List.prefix_append _ _)
              (List.cons_ne_nil _ _) hadm)
        have hdom_snoc : (A ⊗ B).inputDomain h xq := hadm
        rw [ite_eq_left hdom_snoc]
        rcases o with i | j <;> rcases o' with i' | j'
        · have hcons : RandomSystem.parallelConsistent (p ++ [(eX.symm xq, eY.symm yq)]) ↔
              RandomSystem.parallelConsistent p := by
            simp only [RandomSystem.parallelConsistent_snoc, xq, yq, eX, eY, sumAlphabet,
              Equiv.coe_fn_symm_mk, and_true]
          have hL : RandomSystem.parallelLeft (p ++ [(eX.symm xq, eY.symm yq)]) =
              RandomSystem.parallelLeft p ++ [(⟨i, u⟩, ⟨i', v⟩)] := by
            simp only [RandomSystem.parallelLeft, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, xq, yq, eX, eY, sumAlphabet, Equiv.coe_fn_symm_mk]
          have hR : RandomSystem.parallelRight (p ++ [(eX.symm xq, eY.symm yq)]) =
              RandomSystem.parallelRight p := by
            simp only [RandomSystem.parallelRight, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, List.append_nil, xq, yq, eX, eY, sumAlphabet,
                Equiv.coe_fn_symm_mk]
          dsimp only at hmap ⊢
          rw [hmap, hcons, hL, hR, parallelFnProbStep_transition_inl]
          have heq_iff : (⟨Sum.inl i, f i u⟩ : Σ o, (A ⊗ B).Y o) = yq ↔
              (⟨i', v⟩ : Σ k, A.Y k) = ⟨i, f i u⟩ := by
            constructor
            · intro hEq
              rcases Sigma.mk.inj_iff.mp hEq with ⟨h1, h2⟩
              obtain rfl : i = i' := Sum.inl.inj h1
              cases eq_of_heq h2
              rfl
            · intro hEq
              rcases Sigma.mk.inj_iff.mp hEq with ⟨rfl, h2⟩
              cases eq_of_heq h2
              rfl
          by_cases heq : (⟨Sum.inl i, f i u⟩ : Σ o, (A ⊗ B).Y o) = yq
          · rw [ite_eq_left heq]
            by_cases hcond : RandomSystem.parallelConsistent p ∧
                (∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩)
            · have hsnoc : RandomSystem.parallelConsistent p ∧
                  (h ++ [(xq, yq)] = [] ∨ (A ⊗ B).domain ((h ++ [(xq, yq)]).map Prod.fst)) ∧
                  ∀ z ∈ RandomSystem.parallelLeft p ++ [(⟨i, u⟩, ⟨i', v⟩)],
                    z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩ := by
                refine ⟨hcond.1, hadm', fun w hw => ?_⟩
                rcases List.mem_append.mp hw with hw | hw
                · exact hcond.2 w hw
                · rw [List.mem_singleton.mp hw]; exact heq_iff.mp heq
              rw [ite_eq_left ⟨hcond.1, hdom_pre, hcond.2⟩, ite_eq_left hsnoc]
            · have hnot1 : ¬ (RandomSystem.parallelConsistent p ∧
                  (h = [] ∨ (A ⊗ B).domain (h.map Prod.fst)) ∧
                  ∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) :=
                fun ⟨h1, _, h2⟩ => hcond ⟨h1, h2⟩
              have hnot2 : ¬ (RandomSystem.parallelConsistent p ∧
                  (h ++ [(xq, yq)] = [] ∨ (A ⊗ B).domain ((h ++ [(xq, yq)]).map Prod.fst)) ∧
                  ∀ z ∈ RandomSystem.parallelLeft p ++ [(⟨i, u⟩, ⟨i', v⟩)],
                    z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) :=
                fun ⟨h1, _, h2⟩ => hcond ⟨h1, fun w hw => h2 w (List.mem_append_left _ hw)⟩
              rw [ite_eq_right hnot1, ite_eq_right hnot2]
          · rw [ite_eq_right heq]
            have hns : ¬ (RandomSystem.parallelConsistent p ∧
                (h ++ [(xq, yq)] = [] ∨ (A ⊗ B).domain ((h ++ [(xq, yq)]).map Prod.fst)) ∧
                ∀ z ∈ RandomSystem.parallelLeft p ++ [(⟨i, u⟩, ⟨i', v⟩)],
                  z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) := fun ⟨_, _, hall⟩ =>
              heq (heq_iff.mpr (hall _ (List.mem_append_right _ (List.mem_singleton_self _))))
            rw [ite_eq_right hns]
        · have hnc : ¬ RandomSystem.parallelConsistent (p ++ [(eX.symm xq, eY.symm yq)]) := by
            simp only [RandomSystem.parallelConsistent_snoc, xq, yq, eX, eY, sumAlphabet,
              Equiv.coe_fn_symm_mk, reduceCtorEq, and_false, not_false_eq_true]
          have hne : (⟨Sum.inl i, f i u⟩ : Σ o, (A ⊗ B).Y o) ≠ yq := by
            intro hEq
            have h1 := congrArg Sigma.fst hEq
            simp only [yq, reduceCtorEq] at h1
          dsimp only at hmap ⊢
          rw [hmap, parallelFnProbStep_transition_inl, ite_eq_right hne,
            ite_eq_right (fun h' => hnc h'.1)]
        · have hnc : ¬ RandomSystem.parallelConsistent (p ++ [(eX.symm xq, eY.symm yq)]) := by
            simp only [RandomSystem.parallelConsistent_snoc, xq, yq, eX, eY, sumAlphabet,
              Equiv.coe_fn_symm_mk, reduceCtorEq, and_false, not_false_eq_true]
          dsimp only at hmap ⊢
          rw [hmap, parallelFnProbStep_transition_inr_inl, ite_eq_right (fun h' => hnc h'.1)]
        · have hcons : RandomSystem.parallelConsistent (p ++ [(eX.symm xq, eY.symm yq)]) ↔
              RandomSystem.parallelConsistent p := by
            simp only [RandomSystem.parallelConsistent_snoc, xq, yq, eX, eY, sumAlphabet,
              Equiv.coe_fn_symm_mk, and_true]
          have hL : RandomSystem.parallelLeft (p ++ [(eX.symm xq, eY.symm yq)]) =
              RandomSystem.parallelLeft p := by
            simp only [RandomSystem.parallelLeft, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, List.append_nil, xq, yq, eX, eY, sumAlphabet,
                Equiv.coe_fn_symm_mk]
          have hR : RandomSystem.parallelRight (p ++ [(eX.symm xq, eY.symm yq)]) =
              RandomSystem.parallelRight p ++ [(⟨j, u⟩, ⟨j', v⟩)] := by
            simp only [RandomSystem.parallelRight, List.filterMap_append, List.filterMap_cons,
              List.filterMap_nil, xq, yq, eX, eY, sumAlphabet, Equiv.coe_fn_symm_mk]
          dsimp only at hmap ⊢
          rw [hmap, hcons, hL, hR, parallelFnProbStep_transition_inr_inr]
          by_cases hcond : RandomSystem.parallelConsistent p ∧
              (∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩)
          · rw [ite_eq_left ⟨hcond.1, hdom_pre, hcond.2⟩, ite_eq_left ⟨hcond.1, hadm', hcond.2⟩]
            have hBdom : B.inputDomain (RandomSystem.parallelRight p) ⟨j, u⟩ := by
              change B.domain ((RandomSystem.parallelRight p).map Prod.fst ++ [⟨j, u⟩])
              have hr2 := hadm.2.2
              have hq : SystemAlgebra.restrict (some ())
                  ((h.map Prod.fst ++ [xq]).map eX.symm) =
                  (RandomSystem.parallelRight p).map Prod.fst ++ [⟨j, u⟩] := by
                rw [List.map_append, List.map_singleton, SystemAlgebra.restrict_append]
                have htail : SystemAlgebra.restrict (some ()) [eX.symm xq] = [⟨j, u⟩] := by
                  simp only [xq, eX, sumAlphabet, Equiv.coe_fn_symm_mk, SystemAlgebra.restrict,
                    ↓reduceDIte]
                rw [htail]
                congr 1
                have hrq := RandomSystem.parallelRight_queries hcond.1
                have hpm : p.map Prod.fst = (h.map Prod.fst).map eX.symm := by
                  simp only [p, List.map_map]; rfl
                rw [← hpm, hrq]
              rw [hq] at hr2
              rcases hr2 with he | hd
              · exact False.elim (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) he)
              · exact hd
            rw [ProbStep.belief_snoc, ite_eq_left hBdom]
          · rw [ite_eq_right (fun ⟨h1, _, h2⟩ => hcond ⟨h1, h2⟩),
              ite_eq_right (fun ⟨h1, _, h2⟩ => hcond ⟨h1, h2⟩), ProbStep.transition_zero]
      · have hdom_snoc : ¬ (A ⊗ B).inputDomain h xq := hadm
        have hnot : ¬ (h ++ [(xq, yq)] = [] ∨
            (A ⊗ B).domain ((h ++ [(xq, yq)]).map Prod.fst)) := by
          rw [List.map_append, List.map_singleton]
          exact not_or.mpr ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), hadm⟩
        rw [ite_eq_right hdom_snoc, ite_eq_right (fun h' => hnot h'.2.1)]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedSystem.ofProbAutomaton_mass, hbelief, TypedSystem.parallel_mass,
    RandomSystem.parallel_mass]
  let p := h.map (eX.symm.prodCongr eY.symm)
  by_cases hcons : RandomSystem.parallelConsistent p
  · rw [ite_eq_left hcons]
    have hLmass : (TypedSystem.ofFunction (A := A) f).1 (RandomSystem.parallelLeft p) =
        if (RandomSystem.parallelLeft p = [] ∨
          A.domain ((RandomSystem.parallelLeft p).map Prod.fst)) ∧
          (∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩) then 1 else 0 :=
      TypedSystem.ofFunction_mass f (RandomSystem.parallelLeft p)
    rw [hLmass, TypedSystem.ofProbAutomaton_mass]
    have hdom_iff :
        (h = [] ∨ (A ⊗ B).domain (h.map Prod.fst)) ↔
        ((RandomSystem.parallelLeft p = [] ∨
            A.domain ((RandomSystem.parallelLeft p).map Prod.fst)) ∧
          (RandomSystem.parallelRight p = [] ∨
            B.domain ((RandomSystem.parallelRight p).map Prod.fst))) := by
      have hpm : p.map Prod.fst = (h.map Prod.fst).map eX.symm := by
        simp only [p, List.map_map]; rfl
      have hLq : (RandomSystem.parallelLeft p).map Prod.fst =
          SystemAlgebra.restrict none ((h.map Prod.fst).map eX.symm) := by
        rw [← hpm]
        exact RandomSystem.parallelLeft_queries hcons
      have hRq : (RandomSystem.parallelRight p).map Prod.fst =
          SystemAlgebra.restrict (some ()) ((h.map Prod.fst).map eX.symm) := by
        rw [← hpm]
        exact RandomSystem.parallelRight_queries hcons
      rw [hLq, hRq]
      cases h with
      | nil =>
        simp only [List.map_nil, RandomSystem.parallelLeft, RandomSystem.parallelRight,
          List.filterMap_nil, true_or, and_self, p]
      | cons w rest =>
        have hne : (w :: rest).map Prod.fst ≠ [] := List.cons_ne_nil _ _
        simp only [List.cons_ne_nil, false_or]
        have hLnil : RandomSystem.parallelLeft p = [] ↔
            SystemAlgebra.restrict none ((List.map Prod.fst (w :: rest)).map eX.symm) = [] := by
          rw [← List.map_eq_nil_iff (f := Prod.fst), hLq]
        have hRnil : RandomSystem.parallelRight p = [] ↔
            SystemAlgebra.restrict (some ()) ((List.map Prod.fst (w :: rest)).map eX.symm) =
              [] := by
          rw [← List.map_eq_nil_iff (f := Prod.fst), hRq]
        rw [hLnil, hRnil]
        exact ⟨fun hd => ⟨hd.2.1, hd.2.2⟩, fun ⟨h1, h2⟩ => ⟨hne, h1, h2⟩⟩
    have hw0 : (0 : Distribution S).weight = 0 := by
      simp only [Distribution.weight, Finsupp.sum_zero_index]
    by_cases hB : RandomSystem.parallelRight p = [] ∨
        B.domain ((RandomSystem.parallelRight p).map Prod.fst)
    · by_cases hA : (RandomSystem.parallelLeft p = [] ∨
          A.domain ((RandomSystem.parallelLeft p).map Prod.fst)) ∧
          (∀ z ∈ RandomSystem.parallelLeft p, z.2 = ⟨z.1.1, f z.1.1 z.1.2⟩)
      · rw [ite_eq_left hA, one_mul, ite_eq_left ⟨hcons, hdom_iff.mpr ⟨hA.1, hB⟩, hA.2⟩]
      · rw [ite_eq_right hA, zero_mul,
          ite_eq_right (fun ⟨_, hd, hf⟩ => hA ⟨(hdom_iff.mp hd).1, hf⟩), hw0]
    · have hzero : step.belief B.inputDomain init.1 (RandomSystem.parallelRight p) = 0 := by
        cases hpr : RandomSystem.parallelRight p using List.reverseRecOn with
        | nil => exact False.elim (hB (Or.inl hpr))
        | append_singleton pre z =>
          rw [hpr] at hB
          have hnd : ¬ B.inputDomain pre z.1 := by
            intro hd
            have hd' : B.domain (pre.map Prod.fst ++ [z.1]) := hd
            exact hB (Or.inr (by simpa only [List.map_append, List.map_singleton] using hd'))
          rw [ProbStep.belief_snoc, ite_eq_right hnd]
      rw [hzero, hw0, mul_zero]
      dsimp only
      split_ifs with hc
      · exact False.elim (hB (hdom_iff.mp hc.2.1).2)
      · rw [hw0]
  · have hw0 : (0 : Distribution S).weight = 0 := by
      simp only [Distribution.weight, Finsupp.sum_zero_index]
    rw [ite_eq_right hcons, ite_eq_right (fun h' => hcons h'.1), hw0]

/-- Explicit single-step transition of `spongeSimulator` against a fixed random oracle `ro`. -/
noncomputable def simFixedROStep (encode : M → List (BitVec 8)) (q_pub : ℕ)
    (ro : M → ByteState p.outputBytes) :
    ProbStep (List (PermutationEdge (ByteState p.stateBytes)))
      (PrimitiveInterface p q_pub).I
      (PrimitiveInterface p q_pub).X
      (PrimitiveInterface p q_pub).Y
  | table, Bidirectional.Port.forward, x =>
    match lookupForwardEdge table x with
    | some y => ProbDist.single (table, y)
    | none =>
      match completingMessage p encode table x with
      | some m =>
        (𝒰[ByteState (tailBytes p)]).map fun t =>
          let y := assembleState p (ro m) t
          (recordForwardEdge table x y, y)
      | none =>
        (𝒰[ByteState p.stateBytes]).map fun y =>
          (recordForwardEdge table x y, y)
  | table, Bidirectional.Port.inverse, y =>
    match lookupInverseEdge table y with
    | some x => ProbDist.single (table, x)
    | none =>
      (𝒰[ByteState p.stateBytes]).map fun x =>
        (recordInverseEdge table x y, x)

omit [Fintype M] [DecidableEq M] in
lemma ofMemoryless_eq_ofProbAutomaton_fresh {A : Interface}
    (ν : ∀ i, A.X i → ProbDist (A.Y i)) :
    TypedSystem.ofMemoryless A ν =
      TypedSystem.ofProbAutomaton A (ProbStep.fresh ν) (ProbDist.single ()) :=
  Subtype.ext (RandomSystem.ofProbAutomaton_eq_memoryless A.inputDomain
    (ProbStep.memoryless_fresh ν) (ProbDist.single ())).symm

omit [DecidableEq M] in
/-- Attaching `spongeSimulator` to a fixed random oracle `ro` yields `simFixedROStep ro`. -/
theorem spongeSimulator_smul_ro_eq (hp : p.Valid) (encode : M → List (BitVec 8)) (q_pub : ℕ)
    (ro : M → ByteState p.outputBytes) :
    spongeSimulator p M encode q_pub •
        TypedSystem.ofFunction (A := SimROInterface p M q_pub) (fun _ m => ro m) =
      TypedSystem.ofProbAutomaton (PrimitiveInterface p q_pub)
        (simFixedROStep p M encode q_pub ro) (ProbDist.single []) := by
  let B := SimROInterface p M q_pub
  let C := SimCoinInterface p q_pub
  let stepC : ProbStep Unit C.I C.X C.Y :=
    ProbStep.fresh (fun _ _ => 𝒰[ByteState p.stateBytes])
  have hcoin : simCoinSource p q_pub =
      TypedSystem.ofProbAutomaton C stepC (ProbDist.single ()) :=
    ofMemoryless_eq_ofProbAutomaton_fresh (A := C) (fun _ _ => 𝒰[ByteState p.stateBytes])
  rw [spongeSimulator, TypedConverter.comp_smul, TypedConverter.attach_rightContext,
    hcoin, parallel_ofFunction_ofProbAutomaton, spongeSimCore,
    ofPreservingProgram_smul_ofProbAutomaton]
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation
    (A := PrimitiveInterface p q_pub)
    ((spongeSimProgram p M encode q_pub).probCombine
      (parallelFnProbStep (A := B) (fun _ m => ro m) stepC)
      (spongeSimProgram_bounded p M encode q_pub))
    (simFixedROStep p M encode q_pub ro)
    (fun sr => ProbDist.single sr.1)
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (by
      intro _ ⟨table, uState⟩ ⟨o, u⟩ _ _
      cases uState
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, ProbDist.single,
        fTransform_single, bindK_single, one_smul, Function.comp_def,
        bindK_fTransform, Program.probCombine_val]
      rw [bindK_single_comp]
      cases o with
      | forward =>
        simp only [simFixedROStep]
        cases hlu : lookupForwardEdge table u with
        | some y =>
          simp only [Program.probInvoke, spongeSimProgram, hlu, returnProg,
            ProbDist.single, fTransform_single, ProbStep.tagged]
        | none =>
          cases hcm : completingMessage p encode table u with
          | some m =>
            simp only [Program.probInvoke, spongeSimProgram, hlu, hcm, callProg,
              List.nil_append, ProbStep.outcome, parallelFnProbStep, ProbDist.single,
              fTransform_single, bindK_single, one_smul, ↓reduceDIte, ProbStep.tagged,
              stepC, ProbStep.fresh, ProbDist.map_val, bindK_fTransform]
            rw [fTransform_bindK]
            simp only [Function.comp_def, List.singleton_append, ↓reduceDIte,
              returnProg, fTransform_single, ProbStep.tagged]
            rw [bindK_single_comp, fTransform_fTransform]
            have htail := fTransform_tailPart_uniform p (hp.2.2.2.1.trans hp.2.1.le)
            have hcomp :
                fTransform (fun z : ByteState p.stateBytes =>
                  (recordForwardEdge table u (assembleState p (ro m) (tailPart p z)),
                    (⟨Bidirectional.Port.forward, assembleState p (ro m) (tailPart p z)⟩ :
                      Σ j, (PrimitiveInterface p q_pub).Y j)))
                  (uniform (ByteState p.stateBytes)) =
                fTransform (fun t : ByteState (tailBytes p) =>
                  (recordForwardEdge table u (assembleState p (ro m) t),
                    (⟨Bidirectional.Port.forward, assembleState p (ro m) t⟩ :
                      Σ j, (PrimitiveInterface p q_pub).Y j)))
                  (uniform (ByteState (tailBytes p))) := by
              rw [← htail, fTransform_fTransform]
              rfl
            exact hcomp.symm
          | none =>
            simp only [Program.probInvoke, spongeSimProgram, hlu, hcm, callProg,
              List.nil_append, ProbStep.outcome, parallelFnProbStep, ProbStep.tagged,
              stepC, ProbStep.fresh, ProbDist.map_val, bindK_fTransform]
            rw [fTransform_bindK]
            simp only [Function.comp_def, ↓reduceDIte, returnProg, fTransform_single,
              ProbStep.tagged]
            rw [bindK_single_comp, fTransform_fTransform]
            rfl
      | inverse =>
        simp only [simFixedROStep]
        cases hlu : lookupInverseEdge table u with
        | some x =>
          simp only [Program.probInvoke, spongeSimProgram, hlu, returnProg,
            ProbDist.single, fTransform_single, ProbStep.tagged]
        | none =>
          simp only [Program.probInvoke, spongeSimProgram, hlu, callProg,
            List.nil_append, ProbStep.outcome, parallelFnProbStep, ProbStep.tagged,
            stepC, ProbStep.fresh, ProbDist.map_val, bindK_fTransform]
          rw [fTransform_bindK]
          simp only [Function.comp_def, ↓reduceDIte, returnProg, fTransform_single,
            ProbStep.tagged]
          rw [bindK_single_comp, fTransform_fTransform]
          rfl)
    ((ProbDist.single ()).map fun r => ([], r)) (fun _ _ => trivial)
  rw [hsim]
  congr 1
  apply Subtype.ext
  simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
    bindK_single, one_smul]

/-- Ideal sponge step for a fixed random oracle `ro`: honest `H` replies `ro m`,
public `P` runs `simFixedROStep ro`. -/
noncomputable abbrev idealFixedROStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (ro : M → ByteState p.outputBytes) :
    ProbStep (List (PermutationEdge (ByteState p.stateBytes)))
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y :=
  parallelFnProbStep (A := spec.toInterface) (fun _ m => ro m)
    (simFixedROStep p M encode q_pub ro)

/-- Ideal sponge system expressed as a mixture over `ro ∼ 𝒰[M → D]` of `idealFixedROStep ro`. -/
theorem idealSponge_eq_sample (hp : p.Valid) {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub =
      TypedSystem.sample (uniform (M → ByteState p.outputBytes)) fun ro =>
        TypedSystem.ofProbAutomaton (spec.toInterface ⊗ PrimitiveInterface p q_pub)
          (idealFixedROStep p M spec q_pub ro) (ProbDist.single []) := by
  rw [sharedIdealRO, TypedConverter.smul_sample]
  congr 1
  funext ro
  change (TypedConverter.parallel (𝟙 spec.toInterface)
      (spongeSimulator p M encode q_pub) • _) = _
  rw [TypedConverter.parallel_attach, Interface.identity_attach,
    spongeSimulator_smul_ro_eq p M hp encode q_pub ro,
    parallel_ofFunction_ofProbAutomaton]

omit [Fintype M] [DecidableEq M] in
/-- A mixture of probabilistic automata over `θ ∼ μ` equals a single automaton retaining `θ`. -/
lemma sample_ofProbAutomaton_eq {A : Interface} {Θ S : Type}
    (μ : ProbDist Θ) (step : Θ → ProbStep S A.I A.X A.Y) (init : Θ → ProbDist S) :
    TypedSystem.sample μ.1 (fun θ => TypedSystem.ofProbAutomaton A (step θ) (init θ)) =
      TypedSystem.ofProbAutomaton A
        (fun ps o u => (step ps.1 ps.2 o u).map fun sy => ((ps.1, sy.1), sy.2))
        (μ.bind fun θ => (init θ).map fun s => (θ, s)) := by
  classical
  let liftStep : ProbStep (Θ × S) A.I A.X A.Y :=
    fun ps o u => (step ps.1 ps.2 o u).map fun sy => ((ps.1, sy.1), sy.2)
  have htrans : ∀ (ν : Θ → Distribution S) (xq : Σ i, A.X i) (yq : Σ i, A.Y i),
      liftStep.transition (μ.1.bindK fun θ => fTransform (fun s => (θ, s)) (ν θ)) xq yq =
        μ.1.bindK fun θ => fTransform (fun s => (θ, s)) ((step θ).transition (ν θ) xq yq) := by
    intro ν ⟨o, u⟩ yq
    simp only [ProbStep.transition, ProbStep.outcome, liftStep]
    rw [bindK_bindK]
    apply bindK_congr
    intro θ _
    rw [bindK_fTransform, fTransform_bindK]
    apply bindK_congr
    intro s _
    simp only [Function.comp_def, ProbDist.map_val, fTransform_fTransform]
    rw [Distribution.restrict_fTransform, Distribution.restrict_fTransform,
      fTransform_fTransform, fTransform_fTransform]
    have hpred : ∀ x : S × A.Y o,
        ((ProbStep.tagged ⟨o, u⟩ ((θ, x.1), x.2)).2 = yq) ↔
        ((ProbStep.tagged ⟨o, u⟩ x).2 = yq) := fun _ => Iff.rfl
    have hr := Distribution.restrict_congr (step θ s o u).1 hpred
    simp only [Function.comp_def, ProbStep.tagged]
  have hbel : ∀ h : List ((Σ i, A.X i) × Σ i, A.Y i),
      liftStep.belief A.inputDomain
        (μ.bind fun θ => (init θ).map fun s => (θ, s)).1 h =
      μ.1.bindK fun θ =>
        fTransform (fun s => (θ, s)) ((step θ).belief A.inputDomain (init θ).1 h) := by
    intro h
    induction h using List.reverseRecOn with
    | nil =>
      simp only [ProbStep.belief, ProbStep.beliefRev, List.reverse_nil, ProbDist.bind_val,
        ProbDist.map_val]
    | append_singleton h z ih =>
      rw [ProbStep.belief_snoc, ih]
      by_cases hd : A.inputDomain h z.1
      · rw [ite_eq_left hd, htrans]
        apply bindK_congr
        intro θ _
        rw [ProbStep.belief_snoc, ite_eq_left hd]
      · rw [ite_eq_right hd]
        have hz : ∀ θ : Θ,
            fTransform (fun s => (θ, s))
              ((step θ).belief A.inputDomain (init θ).1 (h ++ [z])) = 0 := by
          intro θ
          rw [ProbStep.belief_snoc, ite_eq_right hd, fTransform_zero]
        simp only [hz, bindK_zero_right]
  apply Subtype.ext
  apply RandomSystem.ext
  intro h
  rw [TypedSystem.sample_mass, TypedSystem.ofProbAutomaton_mass, hbel]
  rw [Distribution.weight_bindK]
  simp only [Distribution.weight_fTransform, TypedSystem.ofProbAutomaton_mass]
  rfl

omit [Fintype M] [DecidableEq M] in
lemma lookup_append_singleton_of_none {α β : Type*} [DecidableEq α]
    (l : List (α × β)) (a : α) (b : β) (hnone : l.lookup a = none) (x : α) :
    (l ++ [(a, b)]).lookup x = if x = a then some b else l.lookup x := by
  induction l with
  | nil =>
    simp only [List.nil_append, List.lookup_cons, List.lookup_nil]
    by_cases hx : x = a
    · subst hx; simp only [beq_self_eq_true, ↓reduceIte]
    · simp only [beq_eq_false_iff_ne.mpr hx, ite_eq_right hx]
  | cons hd tl ih =>
    rcases hd with ⟨k, v⟩
    simp only [List.cons_append, List.lookup_cons] at hnone ⊢
    by_cases hka : a == k
    · simp only [hka, reduceCtorEq] at hnone
    · simp only [Bool.not_eq_true] at hka
      simp only [hka] at hnone
      by_cases hxk : x == k
      · have hne : x ≠ a := by
          intro hxa
          subst hxa
          rw [hxk] at hka
          exact Bool.noConfusion hka
        simp only [hxk, ite_eq_right hne]
      · simp only [Bool.not_eq_true] at hxk
        simp only [hxk]
        exact ih hnone

/-- Lazy ideal sponge transition: samples both the public permutation table and the shared RO
on demand. -/
noncomputable def idealLazyStep {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    ProbStep (List (PermutationEdge (ByteState p.stateBytes)) ×
        List (M × ByteState p.outputBytes))
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).I
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).X
      (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y
  | (table, ro), Sum.inl Evaluation.Port.eval, m =>
    match ro.lookup m with
    | some d => ProbDist.single ((table, ro), d)
    | none =>
      (𝒰[ByteState p.outputBytes]).map fun d =>
        ((table, ro ++ [(m, d)]), d)
  | (table, ro), Sum.inr Bidirectional.Port.forward, x =>
    match lookupForwardEdge table x with
    | some y => ProbDist.single ((table, ro), y)
    | none =>
      match completingMessage p encode table x with
      | some m =>
        match ro.lookup m with
        | some d =>
          (𝒰[ByteState (tailBytes p)]).map fun t =>
            let y := assembleState p d t
            ((recordForwardEdge table x y, ro), y)
        | none =>
          (𝒰[ByteState p.stateBytes]).map fun y =>
            ((recordForwardEdge table x y, ro ++ [(m, digestPart p y)]), y)
      | none =>
        (𝒰[ByteState p.stateBytes]).map fun y =>
          ((recordForwardEdge table x y, ro), y)
  | (table, ro), Sum.inr Bidirectional.Port.inverse, y =>
    match lookupInverseEdge table y with
    | some x => ProbDist.single ((table, ro), x)
    | none =>
      (𝒰[ByteState p.stateBytes]).map fun x =>
        ((recordInverseEdge table x y, ro), x)

/-- Completion law extending a lazy RO table `roList` to a full uniform function `M → D`. -/
noncomputable def roCompletionDist (roList : List (M × ByteState p.outputBytes)) :
    ProbDist (M → ByteState p.outputBytes) :=
  ProbDist.pi fun m : M =>
    match roList.lookup m with
    | some d => ProbDist.single d
    | none => 𝒰[ByteState p.outputBytes]

lemma roCompletionDist_nil :
    (roCompletionDist p M []).1 = uniform (M → ByteState p.outputBytes) := by
  apply Finsupp.ext
  intro f
  change (∏ _ : M, (uniform (ByteState p.outputBytes)) _) =
    (uniform (M → ByteState p.outputBytes)) f
  simp only [uniform_apply, Fintype.card_fun, Finset.prod_const, Finset.card_univ,
    Nat.cast_pow, one_div_pow]

lemma roCompletionDist_lookup_some (roList : List (M × ByteState p.outputBytes))
    (m : M) (d : ByteState p.outputBytes) (hlu : roList.lookup m = some d)
    {ro : M → ByteState p.outputBytes} (hmem : ro ∈ (roCompletionDist p M roList).1.support) :
    ro m = d := by
  have hcoord := (ProbDist.mem_support_pi_iff _ ro).mp hmem m
  simp only [hlu, ProbDist.single, Finsupp.mem_support_iff, Finsupp.single_apply] at hcoord
  by_contra hne
  exact hcoord (ite_eq_right (Ne.symm hne))

lemma roCompletionDist_disintegrate (roList : List (M × ByteState p.outputBytes))
    (m : M) (hnone : roList.lookup m = none) :
    (roCompletionDist p M roList).1 =
      (uniform (ByteState p.outputBytes)).bindK fun d =>
        (roCompletionDist p M (roList ++ [(m, d)])).1 := by
  rw [roCompletionDist, ProbDist.pi_val, pi_eq_bindK_update _ m]
  simp only [hnone]
  apply bindK_congr
  intro d _
  congr 1
  funext m'
  dsimp only
  rw [lookup_append_singleton_of_none roList m d hnone m']
  by_cases hm : m' = m
  · subst hm
    simp only [Function.update_self, ↓reduceIte, ProbDist.single]
  · simp only [Function.update_of_ne hm, ite_eq_right hm]

omit [Fintype M] [DecidableEq M] in
lemma bindK_fTransform_comm {α β γ : Type}
    (μ : Distribution α) (ν : Distribution β) (f : α → β → γ) :
    μ.bindK (fun a => fTransform (f a) ν) =
      ν.bindK (fun b => fTransform (fun a => f a b) μ) := by
  classical
  have hL : μ.bindK (fun a => fTransform (f a) ν) =
      μ.bindK (fun a => ν.bindK fun b => Finsupp.single (f a b) 1) :=
    bindK_congr fun a _ => (bindK_single_comp ν (f a)).symm
  have hR : ν.bindK (fun b => fTransform (fun a => f a b) μ) =
      ν.bindK (fun b => μ.bindK fun a => Finsupp.single (f a b) 1) :=
    bindK_congr fun b _ => (bindK_single_comp μ (fun a => f a b)).symm
  rw [hL, hR]
  apply Finsupp.ext
  intro c
  simp only [bindK_apply, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The ideal sponge system `(id ⊗ spongeSimulator) • sharedIdealRO` equals the lazy automaton
`idealLazyStep`. -/
theorem idealSponge_eq_lazy (hp : p.Valid) {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ) :
    (spec.toInterface ◁ spongeSimulator p M encode q_pub) •
        sharedIdealRO p M spec q_pub =
      TypedSystem.ofProbAutomaton (spec.toInterface ⊗ PrimitiveInterface p q_pub)
        (idealLazyStep p M spec q_pub) (ProbDist.single ([], [])) := by
  let A := spec.toInterface ⊗ PrimitiveInterface p q_pub
  rw [idealSponge_eq_sample p M hp spec q_pub]
  have hsam := sample_ofProbAutomaton_eq (A := A) (μ := 𝒰[M → ByteState p.outputBytes])
    (fun ro => idealFixedROStep p M spec q_pub ro) (fun _ => ProbDist.single [])
  change TypedSystem.sample (𝒰[M → ByteState p.outputBytes]).1 _ = _
  rw [hsam]
  let liftStep : ProbStep ((M → ByteState p.outputBytes) ×
      List (PermutationEdge (ByteState p.stateBytes))) A.I A.X A.Y :=
    fun ps o u =>
      (idealFixedROStep p M spec q_pub ps.1 ps.2 o u).map fun sy => ((ps.1, sy.1), sy.2)
  let K : List (PermutationEdge (ByteState p.stateBytes)) × List (M × ByteState p.outputBytes) →
      ProbDist ((M → ByteState p.outputBytes) ×
        List (PermutationEdge (ByteState p.stateBytes))) :=
    fun sr => (roCompletionDist p M sr.2).map fun ro => (ro, sr.1)
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation (A := A)
    (idealLazyStep p M spec q_pub) liftStep K
    (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (by
      intro _ ⟨table, roList⟩ ⟨o, u⟩ _ _
      simp only [ProbStep.SimulatesAt, ProbStep.outcome, K, ProbDist.map_val, bindK_fTransform]
      rcases o with o | o
      · cases o
        simp only [idealLazyStep]
        cases hlu : roList.lookup u with
        | some d =>
          simp only [ProbDist.single, fTransform_single, bindK_single, one_smul,
            Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep, parallelFnProbStep,
            ProbDist.map_val, fTransform_fTransform]
          rw [← bindK_single_comp]
          apply bindK_congr
          intro ro hro
          rw [roCompletionDist_lookup_some p M roList u d hlu hro]
        | none =>
          simp only [ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
            Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep, parallelFnProbStep,
            ProbDist.single, fTransform_single]
          rw [roCompletionDist_disintegrate p M roList u hlu, bindK_bindK]
          apply bindK_congr
          intro d _
          rw [← bindK_single_comp]
          apply bindK_congr
          intro ro hro
          have hlu' : (roList ++ [(u, d)]).lookup u = some d := by
            rw [lookup_append_singleton_of_none roList u d hlu u, ite_eq_left rfl]
          rw [roCompletionDist_lookup_some p M (roList ++ [(u, d)]) u d hlu' hro]
      · cases o with
        | forward =>
          simp only [idealLazyStep]
          cases hlu : lookupForwardEdge table u with
          | some y =>
            simp only [ProbDist.single, fTransform_single, bindK_single, one_smul,
              Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep, parallelFnProbStep,
              simFixedROStep, hlu, ProbDist.map_val, fTransform_fTransform]
            rw [← bindK_single_comp]
          | none =>
            cases hcm : completingMessage p encode table u with
            | some m =>
              cases hro : roList.lookup m with
              | some d =>
                simp only [hro, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
                  Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep,
                  parallelFnProbStep, simFixedROStep, hlu, hcm]
                have hsub :
                    (roCompletionDist p M roList).1.bindK (fun ro =>
                      fTransform (fun t : ByteState (tailBytes p) =>
                        ((ro, recordForwardEdge table u (assembleState p (ro m) t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p (ro m) t⟩ :
                            Σ i, A.Y i)))
                        (uniform (ByteState (tailBytes p)))) =
                    (roCompletionDist p M roList).1.bindK (fun ro =>
                      fTransform (fun t : ByteState (tailBytes p) =>
                        ((ro, recordForwardEdge table u (assembleState p d t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ :
                            Σ i, A.Y i)))
                        (uniform (ByteState (tailBytes p)))) := by
                  apply bindK_congr
                  intro ro hmem
                  rw [roCompletionDist_lookup_some p M roList m d hro hmem]
                exact hsub.trans (bindK_fTransform_comm (roCompletionDist p M roList).1
                  (uniform (ByteState (tailBytes p)))
                  (fun ro t => ((ro, recordForwardEdge table u (assembleState p d t)),
                    (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ : Σ i, A.Y i))))
              | none =>
                simp only [hro, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
                  Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep,
                  parallelFnProbStep, simFixedROStep, hlu, hcm]
                rw [roCompletionDist_disintegrate p M roList m hro, bindK_bindK]
                have hunifS : (𝒰[ByteState p.stateBytes]).1 =
                    fTransform (fun dt : ByteState p.outputBytes × ByteState (tailBytes p) =>
                      assembleState p dt.1 dt.2)
                      ((uniform (ByteState p.outputBytes)).prod
                        (uniform (ByteState (tailBytes p)))) :=
                  (uniform_state_eq_assemble p (hp.2.2.2.1.trans hp.2.1.le)).symm
                rw [hunifS, bindK_fTransform, prod_eq_bindK, bindK_bindK]
                apply bindK_congr
                intro d _
                rw [bindK_fTransform]
                have hsub :
                    (roCompletionDist p M (roList ++ [(m, d)])).1.bindK (fun ro =>
                      fTransform (fun t : ByteState (tailBytes p) =>
                        ((ro, recordForwardEdge table u (assembleState p (ro m) t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p (ro m) t⟩ :
                            Σ i, A.Y i)))
                        (uniform (ByteState (tailBytes p)))) =
                    (roCompletionDist p M (roList ++ [(m, d)])).1.bindK (fun ro =>
                      fTransform (fun t : ByteState (tailBytes p) =>
                        ((ro, recordForwardEdge table u (assembleState p d t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ :
                            Σ i, A.Y i)))
                        (uniform (ByteState (tailBytes p)))) := by
                  apply bindK_congr
                  intro ro hmem
                  have hlu' : (roList ++ [(m, d)]).lookup m = some d := by
                    rw [lookup_append_singleton_of_none roList m d hro m, ite_eq_left rfl]
                  rw [roCompletionDist_lookup_some p M (roList ++ [(m, d)]) m d hlu' hmem]
                have hdig :
                    (uniform (ByteState (tailBytes p))).bindK (fun t =>
                      fTransform (fun ro : M → ByteState p.outputBytes =>
                        ((ro, recordForwardEdge table u (assembleState p d t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ :
                            Σ i, A.Y i)))
                        (roCompletionDist p M (roList ++ [(m, digestPart p
                          (assembleState p d t))])).1) =
                    (uniform (ByteState (tailBytes p))).bindK (fun t =>
                      fTransform (fun ro : M → ByteState p.outputBytes =>
                        ((ro, recordForwardEdge table u (assembleState p d t)),
                          (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ :
                            Σ i, A.Y i)))
                        (roCompletionDist p M (roList ++ [(m, d)])).1) := by
                  apply bindK_congr
                  intro t _
                  rw [digestPart_assembleState p (hp.2.2.2.1.trans hp.2.1.le) d t]
                exact (hsub.trans (bindK_fTransform_comm
                  (roCompletionDist p M (roList ++ [(m, d)])).1
                  (uniform (ByteState (tailBytes p)))
                  (fun ro t => ((ro, recordForwardEdge table u (assembleState p d t)),
                    (⟨Sum.inr Bidirectional.Port.forward, assembleState p d t⟩ : Σ i,
                      A.Y i))))).trans
                  hdig.symm
            | none =>
              simp only [ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
                Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep,
                parallelFnProbStep, simFixedROStep, hlu, hcm]
              exact bindK_fTransform_comm (roCompletionDist p M roList).1
                (uniform (ByteState p.stateBytes))
                (fun ro y => ((ro, recordForwardEdge table u y),
                  (⟨Sum.inr Bidirectional.Port.forward, y⟩ : Σ i, A.Y i)))
        | inverse =>
          simp only [idealLazyStep]
          cases hlu : lookupInverseEdge table u with
          | some x =>
            simp only [ProbDist.single, fTransform_single, bindK_single, one_smul,
              Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep, parallelFnProbStep,
              simFixedROStep, hlu, ProbDist.map_val, fTransform_fTransform]
            rw [← bindK_single_comp]
          | none =>
            simp only [ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
              Function.comp_def, ProbStep.tagged, liftStep, idealFixedROStep, parallelFnProbStep,
              simFixedROStep, hlu]
            exact bindK_fTransform_comm (roCompletionDist p M roList).1
              (uniform (ByteState p.stateBytes))
              (fun ro x => ((ro, recordInverseEdge table x u),
                (⟨Sum.inr Bidirectional.Port.inverse, x⟩ : Σ i, A.Y i))))
    (ProbDist.single ([], [])) (fun _ _ => trivial)
  rw [hsim]
  congr 1
  apply Subtype.ext
  simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
    bindK_single, one_smul, K, roCompletionDist_nil]
  rw [← bindK_single_comp]
  rfl

end RealAndIdealSemantics

/-! ### Shared transcript accounting and partial-table extension lemmas -/

section SharedHelpers

variable (p : Parameters) (M : Type) [Fintype M] [DecidableEq M]

/-- Count of public (`Sum.inr`) queries in a transcript `h`. -/
def publicQueryCount {A B : Interface}
    (h : List ((Σ o, (A ⊗ B).X o) × (Σ o, (A ⊗ B).Y o))) : ℕ :=
  (h.filter fun z => z.1.1.isRight).length

omit [Fintype M] [DecidableEq M] in
lemma publicQueryCount_nil {A B : Interface} :
    publicQueryCount (A := A) (B := B) [] = 0 := rfl

omit [Fintype M] [DecidableEq M] in
lemma publicQueryCount_snoc {A B : Interface}
    (h : List ((Σ o, (A ⊗ B).X o) × (Σ o, (A ⊗ B).Y o)))
    (xq : Σ o, (A ⊗ B).X o) (yq : Σ o, (A ⊗ B).Y o) :
    publicQueryCount (h ++ [(xq, yq)]) =
      publicQueryCount h + if xq.1.isRight then 1 else 0 := by
  simp only [publicQueryCount, List.filter_append, List.length_append, List.filter_cons,
    List.filter_nil]
  cases xq.1 <;> simp only [Sum.isRight_inl, Sum.isRight_inr, Bool.false_eq_true, ↓reduceIte,
    List.length_nil, List.length_singleton]

omit [Fintype M] [DecidableEq M] in
lemma publicQueryCount_le_bound {A : Interface} {q_pub : ℕ}
    (h : List ((Σ o, (A ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (A ⊗ PrimitiveInterface p q_pub).Y o)))
    (hadm : h = [] ∨ (A ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst)) :
    publicQueryCount h ≤ q_pub := by
  let eX := sumAlphabet (Sum.rec A.X (PrimitiveInterface p q_pub).X)
  have hlen : ∀ l : List ((Σ o, (A ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (A ⊗ PrimitiveInterface p q_pub).Y o)),
      (SystemAlgebra.restrict (some ()) ((l.map Prod.fst).map eX.symm)).length =
        publicQueryCount l := by
    intro l
    unfold publicQueryCount
    induction l with
    | nil => rfl
    | cons z rest ih =>
      rcases z with ⟨⟨o, u⟩, y⟩
      rcases o with i | j
      · have hhead : eX.symm ⟨Sum.inl i, u⟩ = ⟨none, ⟨i, u⟩⟩ := rfl
        rw [List.map_cons, List.map_cons, hhead]
        simp only [SystemAlgebra.restrict, reduceCtorEq, ↓reduceDIte, List.filter_cons,
          Sum.isRight_inl, Bool.false_eq_true, ↓reduceIte, ih]
      · have hhead : eX.symm ⟨Sum.inr j, u⟩ = ⟨some (), ⟨j, u⟩⟩ := rfl
        rw [List.map_cons, List.map_cons, hhead]
        simp only [SystemAlgebra.restrict, ↓reduceDIte, List.length_cons, List.filter_cons,
          Sum.isRight_inr, ↓reduceIte, ih]
  rcases hadm with rfl | hd
  · exact Nat.zero_le _
  · rcases hd.2.2 with hnil | hdom
    · rw [← hlen h, hnil]; exact Nat.zero_le _
    · rw [← hlen h]; exact hdom.2

/-- Honest message queries extracted from a transcript `h` (in order). -/
def honestMessages {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o))) : List M :=
  h.filterMap fun z =>
    match z.1 with
    | ⟨Sum.inl Evaluation.Port.eval, m⟩ => some m
    | ⟨Sum.inr _, _⟩ => none

omit [DecidableEq M] in
lemma honestMessages_work_le {encode : M → List (BitVec 8)} {w : ℕ}
    (spec : HonestWorkSpec p M encode w) (q_pub : ℕ)
    (h : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)))
    (hadm : h = [] ∨ (spec.toInterface ⊗ PrimitiveInterface p q_pub).domain (h.map Prod.fst)) :
    ((honestMessages p M spec q_pub h).map fun m => paddedBlockCount p (encode m).length).sum ≤
      w := by
  let eX := sumAlphabet (Sum.rec spec.toInterface.X (PrimitiveInterface p q_pub).X)
  have hmap : ∀ l : List ((Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).X o) ×
      (Σ o, (spec.toInterface ⊗ PrimitiveInterface p q_pub).Y o)),
      (SystemAlgebra.restrict none ((l.map Prod.fst).map eX.symm)).map
          (fun x : Σ o : Evaluation.Port, spec.toInterface.X o => x.2) =
        honestMessages p M spec q_pub l := by
    intro l
    unfold honestMessages
    induction l with
    | nil => rfl
    | cons z rest ih =>
      rcases z with ⟨⟨o, u⟩, y⟩
      rcases o with i | j
      · cases i
        have hhead : eX.symm ⟨Sum.inl Evaluation.Port.eval, u⟩ =
            ⟨none, ⟨Evaluation.Port.eval, u⟩⟩ := rfl
        rw [List.map_cons, List.map_cons, hhead]
        simp only [SystemAlgebra.restrict, ↓reduceDIte, List.map_cons, List.filterMap_cons, ih]
      · have hhead : eX.symm ⟨Sum.inr j, u⟩ = ⟨some (), ⟨j, u⟩⟩ := rfl
        rw [List.map_cons, List.map_cons, hhead]
        simp only [SystemAlgebra.restrict, reduceCtorEq, ↓reduceDIte, List.filterMap_cons, ih]
  rcases hadm with rfl | hd
  · simp only [honestMessages, List.filterMap_nil, List.map_nil, List.sum_nil, Nat.zero_le]
  · rcases hd.2.1 with hnil | hdom
    · rw [← hmap h, hnil]
      simp only [List.map_nil, List.sum_nil, Nat.zero_le]
    · rw [← hmap h, List.map_map]
      exact spec.work_le _ hdom


omit [Fintype M] [DecidableEq M] in
lemma recordForwardEdge_eq_append_of_avoids
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    {x y : ByteState p.stateBytes}
    (hy : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table) :
    recordForwardEdge table x y = table ++ [⟨x, y, false⟩] := by
  unfold recordForwardEdge
  exact ite_eq_left (output_not_mem_of_avoidsOccupied (capacityPart p)
    (zeroState p.capacityBytes) table (x := x) (y := y) hy)

omit [Fintype M] [DecidableEq M] in
lemma recordInverseEdge_eq_append_of_avoids
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    {x y : ByteState p.stateBytes}
    (hx : capacityPart p x ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table) :
    recordInverseEdge table x y = table ++ [⟨x, y, true⟩] := by
  unfold recordInverseEdge
  exact ite_eq_left (input_not_mem_of_avoidsOccupied (capacityPart p)
    (zeroState p.capacityBytes) table (x := x) (y := y) hx)

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_recordForwardEdge_of_completing (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {x y : ByteState p.stateBytes} (hlu : lookupForwardEdge table x = none)
    (hy : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    {m : M} (hcm : completingMessage p encode table x = some m) :
    evalAbsorption p (recordForwardEdge table x y) (zeroState p.stateBytes)
      (paddedBlocks p (encode m)) = some y := by
  have hm := (completingMessage_eq_some_iff p hp encode henc table hpb hg x m).mp hcm
  rcases hm with ⟨parent, last, hsplit, hpar, habs⟩
  conv_lhs => rw [hsplit]
  rw [recordForwardEdge_eq_append_of_avoids p table hy, evalAbsorption_append,
    evalAbsorption_mono p hpar]
  simp only [Option.bind_some, evalAbsorption, habs, lookupForwardEdge_append_of_none hlu,
    lookupForwardEdge, ↓reduceIte]

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_none_of_completing (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {x : ByteState p.stateBytes} (hlu : lookupForwardEdge table x = none)
    {m : M} (hcm : completingMessage p encode table x = some m) :
    evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m)) = none := by
  have hm := (completingMessage_eq_some_iff p hp encode henc table hpb hg x m).mp hcm
  rcases hm with ⟨parent, last, hsplit, hpar, habs⟩
  conv_lhs => rw [hsplit]
  rw [evalAbsorption_append, hpar]
  simp only [Option.bind_some, evalAbsorption, habs, hlu]

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_recordForwardEdge_other_none (hp : p.Valid)
    (encode : M → List (BitVec 8)) (henc : Function.Injective encode)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (hpb : IsPartialBijection (toPairs table))
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    {x y : ByteState p.stateBytes}
    (hy : capacityPart p y ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    {m' : M}
    (hnone : evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m')) = none)
    (hne : completingMessage p encode table x ≠ some m') :
    evalAbsorption p (recordForwardEdge table x y) (zeroState p.stateBytes)
      (paddedBlocks p (encode m')) = none := by
  by_contra hsome
  cases hnew : evalAbsorption p (recordForwardEdge table x y) (zeroState p.stateBytes)
      (paddedBlocks p (encode m')) with
  | none => exact hsome hnew
  | some out =>
    rw [recordForwardEdge_eq_append_of_avoids p table hy] at hnew
    have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) table
        ⟨x, y, false⟩ := hy
    have hne_nil := paddedBlocks_ne_nil p hp.1 (encode m')
    rcases no_preexisting_extension p table ⟨x, y, false⟩ hf _ hne_nil hnew hnone with
      ⟨_, parent, last, hsplit, hpar, habs, _⟩
    have hm : MatchesCompletion p encode table x m' :=
      ⟨parent, last, hsplit, hpar, habs⟩
    exact hne ((completingMessage_eq_some_iff p hp encode henc table hpb hg x m').mpr hm)

omit [Fintype M] [DecidableEq M] in
lemma evalAbsorption_recordInverseEdge_none (hp : p.Valid)
    (encode : M → List (BitVec 8))
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    {x y : ByteState p.stateBytes}
    (hx : capacityPart p x ∉
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table)
    (m' : M)
    (hnone : evalAbsorption p table (zeroState p.stateBytes) (paddedBlocks p (encode m')) = none) :
    evalAbsorption p (recordInverseEdge table x y) (zeroState p.stateBytes)
      (paddedBlocks p (encode m')) = none := by
  by_contra hsome
  cases hnew : evalAbsorption p (recordInverseEdge table x y) (zeroState p.stateBytes)
      (paddedBlocks p (encode m')) with
  | none => exact hsome hnew
  | some out =>
    rw [recordInverseEdge_eq_append_of_avoids p table hx] at hnew
    have hf : AvoidsOccupiedCapacity (capacityPart p) (zeroState p.capacityBytes) table
        ⟨x, y, true⟩ := hx
    have hne_nil := paddedBlocks_ne_nil p hp.1 (encode m')
    rcases no_preexisting_extension p table ⟨x, y, true⟩ hf _ hne_nil hnew hnone with ⟨hinv, _⟩
    cases hinv


omit [Fintype M] [DecidableEq M] in
lemma capacityPart_mem_occupied_of_evalAbsorption
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    (pref : List (ByteState p.rateBytes)) {s_cur : ByteState p.stateBytes}
    (hev : evalAbsorption p table (zeroState p.stateBytes) pref = some s_cur) :
    capacityPart p s_cur ∈
      occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
  have haux : ∀ (st : ByteState p.stateBytes) (bs : List (ByteState p.rateBytes)),
      capacityPart p st ∈ occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table →
      evalAbsorption p table st bs = some s_cur →
      capacityPart p s_cur ∈
        occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
    intro st bs
    induction bs generalizing st with
    | nil =>
      intro hst he
      simp only [evalAbsorption, Option.some.injEq] at he
      rwa [← he]
    | cons b rest ih =>
      intro _ he
      simp only [evalAbsorption] at he
      cases hl : lookupForwardEdge table (absorbBlock p st b) with
      | none => rw [hl] at he; cases he
      | some next =>
        rw [hl] at he
        rcases lookupForwardEdge_eq_some_mem hl with ⟨e, he_mem, _, hout⟩
        have hnext : capacityPart p next ∈
            occupiedCapacities (capacityPart p) (zeroState p.capacityBytes) table := by
          rw [← hout]
          exact occupiedCapacities_output (capacityPart p) (zeroState p.capacityBytes) table he_mem
        exact ih next hnext he
  exact haux (zeroState p.stateBytes) pref
    (by rw [capacityPart_zeroState]; exact occupiedCapacities_zero _ _ table) hev


end SharedHelpers

end Commons.Sponge

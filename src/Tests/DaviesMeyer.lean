module

public import Commons.Schemes.Cipher.MultiContext
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Tests for ideal-cipher Davies–Meyer PRF and context replacement

Exercises:
* Planting involution (`DaviesMeyer.plant_hidden`, `exchange_involutive`, `plant_uniform`).
* Public-ideal-cipher PRF security (`DaviesMeyer.chainingCipherPRF_security` with XOR on `Bool`,
  and `chainingCipherPRF_addGroup_security` for any finite `AddGroup`).
* Single-root cipher-dependent context replacement (`CipherContext.security`) where each query
  combines a challenge evaluation with a follow-up public cipher encryption.
* Multi-root shared-cipher context replacement (`CipherMultiContext.security`).
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.DaviesMeyer

open SystemAlgebra Probability Commons Commons.DaviesMeyer
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped NNReal SystemAlgebra

/-- XOR feed-forward on `Bool` is a permutation in each argument. -/
def xorMask (k : Bool) : Equiv.Perm Bool where
  toFun y := xor k y
  invFun y := xor k y
  left_inv y := by cases k <;> cases y <;> rfl
  right_inv y := by cases k <;> cases y <;> rfl

/-- XOR feed-forward is injective in the key argument for every fixed cipher output. -/
lemma xorMask_injective (y : Bool) : Function.Injective (fun k => xorMask k y) := by
  intro a b h
  cases a <;> cases b <;> cases y <;> simp only [xorMask, Equiv.coe_fn_mk, Bool.xor_false,
    Bool.xor_true, Bool.not_false, Bool.not_true, reduceCtorEq] at h ⊢

/-- Planting with `xorMask` recovers `F m` and defines an involution preserving the uniform
cipher marginal. -/
example (k : Bool) (E : CipherFamily Bool Bool) (F : Bool → Bool) (m : Bool) :
    xorMask k (DaviesMeyer.plant xorMask k E F m k) = F m :=
  DaviesMeyer.plant_hidden xorMask k E F m

example (k : Bool) (pair : CipherFamily Bool Bool × (Bool → Bool)) :
    DaviesMeyer.exchange xorMask k (DaviesMeyer.exchange xorMask k pair) = pair :=
  DaviesMeyer.exchange_involutive xorMask k pair

example {Block State : Type} [Fintype Block] [Fintype State] [Nonempty State]
    (mask : State → Equiv.Perm State) (k : State) :
    letI := Classical.decEq Block
    letI := Classical.decEq State
    Distribution.fTransform (fun pair => DaviesMeyer.plant mask k pair.1 pair.2)
      (Distribution.uniform (CipherFamily Block State × (Block → State))) =
        Distribution.uniform (CipherFamily Block State) :=
  DaviesMeyer.plant_uniform mask k

example (k : Bool) :
    Distribution.fTransform (fun pair => DaviesMeyer.plant xorMask k pair.1 pair.2)
      (Distribution.uniform (CipherFamily Bool Bool × (Bool → Bool))) =
        Distribution.uniform (CipherFamily Bool Bool) := by
  convert DaviesMeyer.plant_uniform (Block := Bool) xorMask k

/-- Public-ideal-cipher PRF bound instantiated with XOR feed-forward on `Bool`. -/
example (q r : Nat) :
    Δ (DaviesMeyer.chainingCipherPRFReal (Block := Bool) xorMask q r)
      (DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r) ≤
        (DaviesMeyer.cipherKeyGuessing Bool r : ℝ≥0) :=
  DaviesMeyer.chainingCipherPRF_security xorMask xorMask_injective q r

/-- Group-addition feed-forward achieves the same `2r / |State|` bound for any finite `AddGroup`. -/
example {Block State : Type} [Fintype Block] [Fintype State] [AddGroup State] (q r : Nat) :
    Δ (DaviesMeyer.chainingCipherPRFReal (Block := Block) (fun k : State => Equiv.addRight k) q r)
      (DaviesMeyer.chainingCipherPRFIdeal (Block := Block) (State := State) q r) ≤
        (DaviesMeyer.cipherKeyGuessing State r : ℝ≥0) :=
  DaviesMeyer.chainingCipherPRF_addGroup_security (Block := Block) (State := State) q r

/-- A cipher-dependent context that queries the challenge table at `m` and encrypts the result
under the shared ideal cipher `E` at block `m`. -/
def chainedEvaluation {Block State : Type} [Fintype Block] [Fintype State] (q : Nat)
    (_ : Unit) (F : Block → State) (E : CipherFamily Block State) :
    ∀ i, (Commons.Evaluation Block State q).X i → (Commons.Evaluation Block State q).Y i
  | _, m => E m (F m)

/-- The single encryption call made by `chainedEvaluation` at query `x`. -/
def chainedCalls {Block State : Type} [Fintype Block] [Fintype State] (q : Nat)
    (_ : Unit) (F : Block → State) (_ : CipherFamily Block State)
    (x : Σ i, (Commons.Evaluation Block State q).X i) : List (CipherQuery Block State) :=
  [(false, x.2, F x.2)]

/-- `CipherContext.security` replaces the hidden-key Davies–Meyer table inside `chainedEvaluation`
with `Δ` loss at most `2q / |State|`. -/
example {Block State : Type} [Fintype Block] [Fintype State] [Nonempty State]
    (mask : State → Equiv.Perm State) (mask_injective : ∀ y, Function.Injective (fun k => mask k y))
    (q : Nat) :
    Δ (CipherContext.real (Distribution.uniform Unit) mask (chainedEvaluation (Block := Block) q))
      (CipherContext.ideal (Distribution.uniform Unit) (chainedEvaluation (Block := Block) q)) ≤
        (DaviesMeyer.cipherKeyGuessing State q : ℝ≥0) := by
  apply CipherContext.security (Distribution.uniform Unit) mask (chainedEvaluation q) mask_injective
    (chainedCalls q) q
  · intro _ F E E' x he
    exact he (false, x.2, F x.2) List.mem_cons_self
  · intro _ F E xs hd
    have hlen : (xs.flatMap (chainedCalls q () F E)).length = xs.length := by
      simp only [chainedCalls, List.length_flatMap, List.length_singleton, List.map_const',
        List.sum_replicate, smul_eq_mul, mul_one]
    rw [hlen]
    rcases hd with rfl | hd
    · exact Nat.zero_le _
    · exact hd.2

/-- Multi-user context evaluating slot `u` on `m` and encrypting the result under shared `E`. -/
def multiUserEvaluation {Block State : Type} [Fintype Block] [Fintype State] (users q : Nat)
    (_ : Unit) (G : Fin users × Block → State) (E : CipherFamily Block State) :
    ∀ i, (Commons.Evaluation (Fin users × Block) State q).X i →
      (Commons.Evaluation (Fin users × Block) State q).Y i
  | _, um => E um.2 (G um)

/-- `CipherMultiContext.security` replaces all `users` hidden-key slots inside
`multiUserEvaluation` with total loss `users * (2 * (2 * q) / |State|)`. -/
example {Block State : Type} [Fintype Block] [Fintype State] [Nonempty State]
    (users q : Nat) (mask : State → Equiv.Perm State)
    (mask_injective : ∀ y, Function.Injective (fun k => mask k y)) :
    Δ (CipherMultiContext.real users (Distribution.uniform Unit) mask
        (multiUserEvaluation (Block := Block) users q))
      (CipherMultiContext.ideal users (Distribution.uniform Unit)
        (multiUserEvaluation (Block := Block) users q)) ≤
      ((users : ℝ≥0) * DaviesMeyer.cipherKeyGuessing State (2 * q) : ℝ≥0) := by
  let challengeCalls : Unit → (Fin users × Block → State) → CipherFamily Block State →
      Sigma (Commons.Evaluation (Fin users × Block) State q).X → List (Fin users × Block) :=
    fun _ _ _ x => [x.2]
  let cipherCalls : Unit → (Fin users × Block → State) → CipherFamily Block State →
      Sigma (Commons.Evaluation (Fin users × Block) State q).X → List (CipherQuery Block State) :=
    fun _ G _ x => [(false, x.2.2, G x.2)]
  apply CipherMultiContext.security users (Distribution.uniform Unit) mask
    (multiUserEvaluation users q) challengeCalls cipherCalls mask_injective (2 * q)
  · intro _ G G' E E' x hG hE
    have h1 : G' x.2 = G x.2 := hG x.2 List.mem_cons_self
    have h2 : E' x.2.2 (G x.2) = E x.2.2 (G x.2) := hE (false, x.2.2, G x.2) List.mem_cons_self
    change E' x.2.2 (G' x.2) = E x.2.2 (G x.2)
    rw [h1, h2]
  · intro _ G E xs hd
    have h1 : (xs.flatMap (challengeCalls () G E)).length = xs.length := by
      simp only [challengeCalls, List.length_flatMap, List.length_singleton, List.map_const',
        List.sum_replicate, smul_eq_mul, mul_one]
    have h2 : (xs.flatMap (cipherCalls () G E)).length = xs.length := by
      simp only [cipherCalls, List.length_flatMap, List.length_singleton, List.map_const',
        List.sum_replicate, smul_eq_mul, mul_one]
    rw [h1, h2]
    rcases hd with rfl | hd
    · exact Nat.zero_le _
    · have hq := hd.2
      omega

/-- `cc_calc statistical` and `cc_normalize` compose `chainingCipherPRF_security` under an outer
converter `α` and parallel composition with a side system `S`. -/
example {Out Side : Interface} (q r : Nat)
    (α : Out ⟶ ChainingCipherPRFInterface Bool Bool q r)
    (S : TypedSystem Side) (T : TypedSystem (Out ⊗ Side)) (δ : ENNReal)
    (hT : Δ ((α • DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r) ∥ S)
      T ≤ δ) :
    Δ ((α ⊗ₘ 𝟙 Side) • (DaviesMeyer.chainingCipherPRFReal (Block := Bool) xorMask q r ∥ S)) T ≤
      (DaviesMeyer.cipherKeyGuessing Bool r : ℝ≥0) + δ := by
  let ε : ENNReal := (DaviesMeyer.cipherKeyGuessing Bool r : ℝ≥0)
  have hpar :
      Δ (DaviesMeyer.chainingCipherPRFReal (Block := Bool) xorMask q r ∥ S)
        (DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r ∥ S) ≤ ε :=
    (Interface.distance_parallel_left_le _ _ S).trans
      (DaviesMeyer.chainingCipherPRF_security (Block := Bool) xorMask xorMask_injective q r)
  have hnorm :
      (α ⊗ₘ 𝟙 Side) • (DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r ∥ S) =
      (α • DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r) ∥ S := by
    cc_normalize
  cc_calc statistical
    (α ⊗ₘ 𝟙 Side) • (DaviesMeyer.chainingCipherPRFReal (Block := Bool) xorMask q r ∥ S) ≈[ε]
      (α ⊗ₘ 𝟙 Side) •
        (DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r ∥ S) := hpar
    _ = (α • DaviesMeyer.chainingCipherPRFIdeal (Block := Bool) (State := Bool) q r) ∥ S := hnorm
    _ ≈[δ] T := hT

/-- `cc_calc statistical` chains `CipherContext.security` through an outer converter `α` with a
downstream statistical step. -/
example {Block State : Type} [Fintype Block] [Fintype State] [Nonempty State]
    {Out : Interface} (q : Nat)
    (mask : State → Equiv.Perm State) (mask_injective : ∀ y, Function.Injective (fun k => mask k y))
    (α : Out ⟶ Commons.Evaluation Block State q) (T : TypedSystem Out) (δ : ENNReal)
    (hT : Δ (α • CipherContext.ideal (Distribution.uniform Unit)
      (chainedEvaluation (Block := Block) q)) T ≤ δ) :
    Δ (α • CipherContext.real (Distribution.uniform Unit) mask
      (chainedEvaluation (Block := Block) q)) T ≤
      (DaviesMeyer.cipherKeyGuessing State q : ℝ≥0) + δ := by
  have hctx :
      Δ (CipherContext.real (Distribution.uniform Unit) mask
          (chainedEvaluation (Block := Block) q))
        (CipherContext.ideal (Distribution.uniform Unit)
          (chainedEvaluation (Block := Block) q)) ≤
        (DaviesMeyer.cipherKeyGuessing State q : ℝ≥0) := by
    apply CipherContext.security (Distribution.uniform Unit) mask (chainedEvaluation q)
      mask_injective (chainedCalls q) q
    · intro _ F E E' x he
      exact he (false, x.2, F x.2) List.mem_cons_self
    · intro _ F E xs hd
      have hlen : (xs.flatMap (chainedCalls q () F E)).length = xs.length := by
        simp only [chainedCalls, List.length_flatMap, List.length_singleton, List.map_const',
          List.sum_replicate, smul_eq_mul, mul_one]
      rw [hlen]
      rcases hd with rfl | hd
      · exact Nat.zero_le _
      · exact hd.2
  cc_calc statistical
    α • CipherContext.real (Distribution.uniform Unit) mask
        (chainedEvaluation (Block := Block) q) ≈[(DaviesMeyer.cipherKeyGuessing State q : ℝ≥0)]
      α • CipherContext.ideal (Distribution.uniform Unit)
        (chainedEvaluation (Block := Block) q) := hctx
    _ ≈[δ] T := hT

#print axioms Probability.Counting.uniform_mass_mem_list_le
#print axioms Probability.Counting.fTransform_update_uniform
#print axioms SystemAlgebra.TypedSystem.sample_const
#print axioms SystemAlgebra.TypedSystem.parallel_ofFunction
#print axioms SystemAlgebra.TypedSystem.sample_uniform_equiv
#print axioms SystemAlgebra.TypedSystem.distance_le_of_transcript_ratio
#print axioms SystemAlgebra.TypedSystem.transcript_ratio_chain
#print axioms SystemAlgebra.TypedSystem.sample_ratio_of_bad_keys
#print axioms SystemAlgebra.TypedSystem.sample_distance_le_of_bad_keys
#print axioms SystemAlgebra.TypedSystem.sample_distance_le_of_key_guesses
#print axioms DaviesMeyer.plant_uniform
#print axioms DaviesMeyer.chainingCipherPRF_security
#print axioms CipherContext.security
#print axioms CipherMultiContext.security

end Tests.DaviesMeyer

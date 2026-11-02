module

public import Commons.Constructions.KEMDEM.Correctness

/-!
# KEM–DEM key flow

The example shows why key-support compatibility matters: the KEM always encapsulates `false`,
whereas the DEM contract covers only `true`. Both components satisfy their own correctness
contracts, but their composition rejects every encryption.
-/

@[expose] public section

namespace Tests.KEMDEM

open Commons Probability Distribution

/-- The unique key pair encapsulates `(true, false)`; `true` decapsulates to key `false`,
while ciphertext `false` is rejected. -/
noncomputable def falseKeyKEM : KEM Unit Unit Bool Bool where
  gen := ProbDist.single ((), ())
  encaps _ := ProbDist.single (true, false)
  decaps _ ck := if ck then some false else none

/-- Generate key `true`; encryption returns `(k, m)`. Decryption recovers `m` under `true`
and rejects under `false`. -/
noncomputable def trueKeyDEM : SymmetricEncryption Bool ℕ (Bool × ℕ) where
  gen := ProbDist.single true
  enc k m := ProbDist.single (k, m)
  dec k c := if k then some c.2 else none

/-- Each encapsulation recovers key `false`, as required by the KEM's own contract. -/
lemma falseKeyKEM_correct : falseKeyKEM.Correct := by
  intro pk sk _ ck k h
  have hk := ((Finsupp.mem_support_single (ck, k) (true, false) (1 : ℝ)).mp h).1
  cases hk
  rfl

/-- The DEM recovers messages at its sole generated key, `true`. -/
lemma trueKeyDEM_correct : trueKeyDEM.Correct := by
  intro k hk m c hc
  have hk' := ((Finsupp.mem_support_single k true (1 : ℝ)).mp hk).1
  have hc' := ((Finsupp.mem_support_single c (k, m) (1 : ℝ)).mp hc).1
  subst k c
  rfl

/-- Encryption uses the encapsulated `false` key; it never draws the DEM's generated key. -/
lemma encryption_key (m : ℕ) :
    (Commons.KEMDEM.scheme falseKeyKEM trueKeyDEM).enc () m =
      ProbDist.single (true, (false, m)) := by
  apply Subtype.ext
  simp only [Commons.KEMDEM.scheme, falseKeyKEM, trueKeyDEM, ProbDist.bind_val,
    ProbDist.map_val, ProbDist.single, bindK_single, one_smul, fTransform_single]

/-- Decapsulation succeeds, but DEM decryption rejects under the recovered key outside its contract. -/
example (m : ℕ) :
    (Commons.KEMDEM.scheme falseKeyKEM trueKeyDEM).dec () (true, (false, m)) = none := rfl

/-- Failed decapsulation rejects before the DEM is used. -/
example (m : ℕ) :
    (Commons.KEMDEM.scheme falseKeyKEM trueKeyDEM).dec () (false, (false, m)) = none :=
  Commons.KEMDEM.dec_eq_none_of_decaps_eq_none falseKeyKEM trueKeyDEM () false (false, m) rfl

/-- Component correctness alone does not imply correctness of the composed scheme. -/
example : ¬(Commons.KEMDEM.scheme falseKeyKEM trueKeyDEM).Correct := by
  intro correct
  -- The generated pair and encryption output both have singleton support.
  have hkeys : ((), ()) ∈ falseKeyKEM.gen.1.support := by
    exact (Finsupp.mem_support_single _ _ (1 : ℝ)).mpr ⟨rfl, one_ne_zero⟩
  have hc : (true, (false, 0)) ∈
      ((Commons.KEMDEM.scheme falseKeyKEM trueKeyDEM).enc () 0).1.support := by
    rw [encryption_key]
    exact (Finsupp.mem_support_single _ _ (1 : ℝ)).mpr ⟨rfl, one_ne_zero⟩
  -- Correctness would require recovery, but DEM decryption at the encapsulated key rejects.
  have recovered := correct () () hkeys 0 (true, (false, 0)) hc
  cases recovered

#print axioms Commons.KEMDEM.correct

end Tests.KEMDEM

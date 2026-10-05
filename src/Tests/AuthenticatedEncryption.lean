import Examples.AuthenticatedEncryption.Security
import Examples.Games

/-!
# Authenticated encryption: checks and axioms

The one-time pad on bits instantiates the scheme, the collision step, also through the games
layer, and the implication; the plaintext filter and the ideal transformation reject a ciphertext
before any encryption. The development depends only on `propext`, `Classical.choice` and
`Quot.sound`.
-/

open SystemAlgebra SystemAlgebra.Interface Probability
open Commons
open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra

namespace AuthenticatedEncryptionTests

open AuthenticatedEncryption

/-- The one-time pad on bits: a uniform key, `Enc_k(m) = k ⊕ m` and `Dec_k(c) = k ⊕ c`. -/
noncomputable def oneTimePad : SymmetricEncryption Bool Bool Bool where
  gen := DSL.uniform Bool
  enc k m := Distribution.ProbDist.single (xor k m)
  dec k c := some (xor k c)

/-- The collision step on the one-time pad: within `q_e² / 2`. -/
theorem oneTimePad_hybrid_ideal (q : AE.Port → ℕ) :
    Δ (Hybrid oneTimePad q) (AE.Ideal.perPort Bool Bool (budget := q) •
        Encryption.Real.perPort oneTimePad : Interface.Resource (AE.perPort Bool Bool q)) ≤
      ENNReal.ofReal ((q .enc : ℝ) ^ 2 / 2) := by
  simpa using hybrid_ideal_distance_le oneTimePad q

/-- The collision step on the one-time pad, through the games layer: every solver's advantage is
within `q_e² / 2`. -/
theorem oneTimePad_hybrid_ideal_advantage (q : AE.Port → ℕ) {s}
    (hs : s ∈ Games.solvers (AE.perPort Bool Bool q)) :
    |s.1 (Hybrid oneTimePad q) - s.1 (AE.Ideal.perPort Bool Bool (budget := q) •
        Encryption.Real.perPort oneTimePad : Interface.Resource (AE.perPort Bool Bool q))| ≤
      (q .enc : ℝ) ^ 2 / 2 := by
  simpa using GameExamples.hybrid_ideal_advantage_le oneTimePad q hs

/-- The corrected chain on the one-time pad uses each assumption twice. -/
theorem oneTimePad_usage (q : AE.Port → ℕ) :
    (correctedChain oneTimePad q).usageCount .cca = 2 ∧
      (correctedChain oneTimePad q).usageCount .ptxt = 2 :=
  ⟨correctedChain_cca oneTimePad q, correctedChain_ptxt oneTimePad q⟩

/-- The implication applies to the one-time pad for any admitted distinguishers. -/
example (q : AE.Port → ℕ) [AdmissibleDistinguishers]
    (εptxt εcca : (AE.perPort Bool Bool q).inputDomain.DistinguisherBehavior → ENNReal)
    (ptxt : AE.INTPTXT oneTimePad εptxt) (cca : AE.INDCCA oneTimePad εcca) :
    ∃ error, AE.Secure oneTimePad (q := q) error :=
  ⟨_, ae_of_ind_cca_int_ptxt oneTimePad q εptxt εcca ptxt cca⟩

/-- Before any encryption, the plaintext filter rejects every decryption. -/
theorem ptxtDecrypt_initial {Ω : Type} (decrypt : Ω → List Bool → Bool → Option Bool) (ω : Ω)
    (c : Bool) : ptxtDecrypt decrypt ω [] c = none := by
  simp [ptxtDecrypt, AE.retain]

/-- Before any encryption, the ideal transformation rejects every ciphertext. -/
theorem idealDecrypt_initial {Ω : Type} {k : ℕ} (encrypt : Ω → ℕ → Bool → Bool)
    (ω : Ω × (Fin k → Bool)) (c : Bool) :
    idealDecrypt (DSL.uniform Bool) encrypt ω [] c = none := by
  simp [idealDecrypt, AE.replay]

end AuthenticatedEncryptionTests

-- The scheme, the oracle automata and each system as an oracle.
#print axioms AuthenticatedEncryption.real_bisim
#print axioms AuthenticatedEncryption.encryptionReal_bisim
#print axioms AuthenticatedEncryption.oracle_system_congr
#print axioms AuthenticatedEncryption.ptxt_bisim
#print axioms AuthenticatedEncryption.cca_bisim
#print axioms AuthenticatedEncryption.aeIdeal_bisim
#print axioms AuthenticatedEncryption.real_eq
#print axioms AuthenticatedEncryption.encryptionReal_eq
#print axioms AuthenticatedEncryption.ptxt_smul
#print axioms AuthenticatedEncryption.cca_smul
#print axioms AuthenticatedEncryption.aeIdeal_smul
#print axioms AuthenticatedEncryption.hybrid_mass
#print axioms AuthenticatedEncryption.ideal_mass

-- The collision step.
#print axioms AuthenticatedEncryption.collision_mass_le
#print axioms AuthenticatedEncryption.hybridDecrypt_eq
#print axioms AuthenticatedEncryption.ideal_truncate
#print axioms AuthenticatedEncryption.ideal_mass_hybridTables
#print axioms AuthenticatedEncryption.collisionGame_conditionallyEquivalent
#print axioms AuthenticatedEncryption.collisionGame_badProbability_le
#print axioms AuthenticatedEncryption.hybrid_ideal_distance_le

-- The collision step through the games layer.
#print axioms GameExamples.collision
#print axioms GameExamples.collision_visible
#print axioms GameExamples.collision_conditionallyEquivalent
#print axioms GameExamples.collision_win_le
#print axioms GameExamples.hybrid_ideal_advantage_le
#print axioms GameExamples.attach_hybrid_ideal_advantage_le

-- Reductions in any compatible solver class.
#print axioms GameExamples.advantage_attach_le_win
#print axioms GameExamples.advantage_attach_le
#print axioms GameExamples.win_attach_comp_le
#print axioms GameExamples.win_le_of_reduction

-- The implication.
#print axioms AuthenticatedEncryption.correctedChain
#print axioms AuthenticatedEncryption.correctedChain_cca
#print axioms AuthenticatedEncryption.correctedChain_ptxt
#print axioms AuthenticatedEncryption.ae_of_ind_cca_int_ptxt
#print axioms AuthenticatedEncryption.real_ideal_distance_le

-- Checks.
#print axioms AuthenticatedEncryptionTests.oneTimePad_hybrid_ideal
#print axioms AuthenticatedEncryptionTests.oneTimePad_hybrid_ideal_advantage
#print axioms AuthenticatedEncryptionTests.oneTimePad_usage
#print axioms AuthenticatedEncryptionTests.ptxtDecrypt_initial
#print axioms AuthenticatedEncryptionTests.idealDecrypt_initial

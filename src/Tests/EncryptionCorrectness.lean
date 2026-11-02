module

public import Commons.Definitions.AEAD

/-!
# Symmetric-encryption correctness clients

An arbitrary scheme supplies correctness as an explicit hypothesis. The same contract gives
probability-one decryption for supported keys without finite carrier assumptions, and typed
encryption/decryption replies for supported draws of the system's encryption-table law.
-/

@[expose] public section

open Commons Probability

namespace EncryptionCorrectnessTests

/-- A symbolic scheme's supported encryptions decrypt with probability one. -/
example
    -- `K`, `M`, `C` may be infinite; their probability laws still have finite support.
    {K M C : Type} (scheme : SymmetricEncryption K M C) (correct : scheme.Correct)
    -- `hkey` witnesses generated `key`; `message` is the chosen plaintext.
    (key : K) (hkey : key ∈ scheme.gen.1.support) (message : M) :
    (scheme.enc key message).1.mass (fun c => scheme.dec key c = some message) = 1 :=
  correct.mass_dec_eq_one hkey message

/-- The symbolic typed client decrypts the ciphertext returned by its encryption query. -/
example
    -- The existing DSL interface requires finite key, message and ciphertext types.
    {K M C : Type} [Fintype K] [Fintype M] [Fintype C] [DecidableEq K] [DecidableEq M]
    -- The scheme's correctness is supplied explicitly, independently of any security notion.
    (scheme : SymmetricEncryption K M C) (correct : scheme.Correct)
    -- `hkey` and `htable` support `key` and `table` under the system's named laws.
    (key : K) (hkey : key ∈ scheme.gen.1.support)
    (table : K × M → C) (htable : table ∈ scheme.encryptions.1.support) (message : M)
    -- `henc` records the actual `ciphertext` reply to this encryption query.
    (ciphertext : C)
    (henc : AE.system.body scheme (some key) .enc message
      [(⟨.inr (), ()⟩, ⟨.inr (), table⟩)] = .inl (some key, ciphertext)) :
    AE.system.body scheme (some key) .dec ciphertext [] = .inl (some key, some message) := by
  have replies := AE.system.enc_dec_eq_of_correct scheme correct hkey htable message
  -- The encryption equation identifies the ciphertext which the decryption equation recovers.
  have hc : ciphertext = table (key, message) :=
    congrArg Prod.snd (Sum.inl.inj (henc.symm.trans replies.1))
  rw [hc]
  exact replies.2

/-- A supported encryption that rejects is a direct witness of failed correctness. -/
example
    -- `K`, `M`, `C` carry the keys, messages and ciphertexts of `scheme`.
    {K M C : Type} (scheme : SymmetricEncryption K M C)
    -- `hkey` and `hc` support `key` and `ciphertext`; `rejects` records decryption failure.
    (key : K) (hkey : key ∈ scheme.gen.1.support) (message : M) (ciphertext : C)
    (hc : ciphertext ∈ (scheme.enc key message).1.support)
    (rejects : scheme.dec key ciphertext = none) : ¬ scheme.Correct := by
  intro correct
  -- Correctness at this supported ciphertext would require `none = some message`.
  have h := correct key hkey message ciphertext hc
  rw [rejects] at h
  cases h

#print axioms Probability.Distribution.ProbDist.mem_support_pi_iff
#print axioms Probability.Distribution.ProbDist.mass_eq_one_of_support
#print axioms Commons.SymmetricEncryption.Correct.mass_dec_eq_one
#print axioms Commons.SymmetricEncryption.Correct.dec_eq_some_of_mem_encryptions
#print axioms Commons.AE.system.enc_dec_eq_of_correct

end EncryptionCorrectnessTests

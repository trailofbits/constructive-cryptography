module

public import Commons.Definitions.PublicKeyEncryption

/-!
# Public-key encryption correctness checks

A scheme with correlated keys and infinite message and ciphertext carriers checks correctness
on joint key support. Mismatched keys and impossible ciphertexts can reject. The local body
check assumes a retained pair and supplied table response, then recovers its encryption reply.
-/

@[expose] public section

open Commons Probability

namespace PublicKeyEncryptionCorrectnessTests

/-- Draw `b ∼ 𝒰[Bool]` and retain `(b,b)`. Encryption returns `(pk, some m)`; decryption
returns the payload exactly when its key matches the ciphertext's key. Messages and ciphertexts
have infinite carriers, with a singleton encryption law for each query. -/
noncomputable def correlatedKeysScheme : PublicKeyEncryption Bool Bool ℕ (Bool × Option ℕ) where
  gen := Distribution.ProbDist.map (fun b => (b, b)) 𝒰[Bool]
  enc pk message := Distribution.ProbDist.single (pk, some message)
  dec sk ciphertext := if sk = ciphertext.1 then ciphertext.2 else none

/-- The generated keys have identical values, and each equal pair has positive mass. -/
lemma correlatedKeysScheme_mem_support_gen_iff (pk sk : Bool) :
    (pk, sk) ∈ correlatedKeysScheme.gen.1.support ↔ pk = sk := by
  constructor
  · -- Support of the diagonal pushforward supplies one shared key for both coordinates.
    intro hkeys
    obtain ⟨key, _, hkey⟩ := Distribution.mem_support_fTransform _ _ hkeys
    exact (congrArg Prod.fst hkey).symm.trans (congrArg Prod.snd hkey)
  · -- Each diagonal pair has the positive mass of its uniform source key.
    rintro rfl
    change (pk, pk) ∈ (Distribution.fTransform (fun b : Bool => (b, b))
      (Distribution.uniform Bool)).support
    rw [Finsupp.mem_support_iff, Distribution.fTransform_injective_apply _ _
      (fun _ _ h => congrArg Prod.fst h), Distribution.uniform_apply]
    norm_num

/-- Joint support pairs the decryption key with the key carried by each supported ciphertext. -/
lemma correlatedKeysScheme_correct : correlatedKeysScheme.Correct := by
  intro pk sk hkeys message ciphertext hc
  have hkey := (correlatedKeysScheme_mem_support_gen_iff pk sk).mp hkeys
  -- The point-mass support fixes the returned key and message together.
  have hc' : ciphertext = (pk, some message) := by
    simpa only [correlatedKeysScheme, Distribution.ProbDist.single,
      Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] using hc
  simp only [correlatedKeysScheme, hc', hkey, ↓reduceIte]

/-- Probability-one recovery needs no finite instance on messages or ciphertexts. -/
example (key : Bool) (message : ℕ) :
    (correlatedKeysScheme.enc key message).1.mass
      (fun c => correlatedKeysScheme.dec key c = some message) = 1 :=
  correlatedKeysScheme_correct.mass_dec_eq_one
    ((correlatedKeysScheme_mem_support_gen_iff key key).mpr rfl) message

/-- Both key values occur, but a mismatched pair rejects: marginal support would be too strong. -/
example (message : ℕ) :
    (true, true) ∈ correlatedKeysScheme.gen.1.support ∧
    (false, false) ∈ correlatedKeysScheme.gen.1.support ∧
    correlatedKeysScheme.dec false (true, some message) = none :=
  ⟨(correlatedKeysScheme_mem_support_gen_iff _ _).mpr rfl,
    (correlatedKeysScheme_mem_support_gen_iff _ _).mpr rfl, rfl⟩

/-- Correctness permits rejection of an impossible encryption output at a generated key. -/
example (key : Bool) : correlatedKeysScheme.dec key (key, none) = none := by
  simp only [correlatedKeysScheme, ↓reduceIte]

/-- A local body check recovers an encryption reply at a supported retained pair and table. -/
example
    -- `PK`, `M`, `C` form the finite interface; `SK` is finite for the internal key source.
    {PK SK M C : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C]
    [DecidableEq PK] [DecidableEq M]
    -- `correct` supplies the recovery contract for `scheme`.
    (scheme : PublicKeyEncryption PK SK M C) (correct : scheme.Correct)
    -- `hkeys` keeps generated keys paired; `htable` puts `table` in the encryption-law support.
    (pk : PK) (sk : SK) (hkeys : (pk, sk) ∈ scheme.gen.1.support)
    (table : PK × M → C) (htable : table ∈ scheme.encryptions.1.support) (message : M)
    -- `henc` identifies `ciphertext` as the actual encryption reply from this draw.
    (ciphertext : C) (henc : PKE.system.body scheme (some (pk, sk)) .enc message
      [(⟨.inr (), ()⟩, ⟨.inr (), table⟩)] = .inl (some (pk, sk), ciphertext)) :
    PKE.system.body scheme (some (pk, sk)) .dec ciphertext [] =
      .inl (some (pk, sk), some message) := by
  have hencrypt := PKE.system.enc_eq scheme pk sk table message
  -- The encryption equation identifies the returned ciphertext with the supported table entry.
  have hc : table (pk, message) = ciphertext :=
    congrArg Prod.snd (Sum.inl.inj (hencrypt.symm.trans henc))
  rw [← hc]
  exact PKE.system.dec_eq_of_correct scheme correct hkeys htable message

#print axioms Commons.PublicKeyEncryption.Correct.mass_dec_eq_one
#print axioms Commons.PublicKeyEncryption.Correct.dec_eq_some_of_mem_encryptions
#print axioms Commons.PKE.system.publicKey_eq
#print axioms Commons.PKE.system.enc_eq
#print axioms Commons.PKE.system.dec_eq_of_correct
#print axioms PublicKeyEncryptionCorrectnessTests.correlatedKeysScheme_correct

end PublicKeyEncryptionCorrectnessTests

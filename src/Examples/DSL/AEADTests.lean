import Examples.DSL.AEAD
import Commons.Tests.AES

/-!
# Checks of the AEAD example

The interaction paths of `EncryptThenMAC` at every query budget: encryption, decryption with a
tag that verifies, and rejection of one that does not. Arithmetic facts about the encodings, and
the combination as functions, encrypting with `CTR.crypt` and `PMAC.pmac` under AES-256 and
decrypting after verifying the tag: decryption inverts encryption, and a change of the nonce, the
associated data, the ciphertext or the tag is rejected. The known-answer tests of CTR and PMAC are
in `Commons.Tests`.
-/

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

namespace DSLExamples.Authenticated
open Commons DSLExamples.Cipher

/-- Each invocation makes at least one inside call. -/
theorem bound_pos : 0 < EncryptThenMAC.bound :=
  EncryptThenMAC.bound_spec none AEAD.Port.encrypt (0, ⟨[], by norm_num⟩, ⟨[], by norm_num⟩) []
    ⟨.inl StreamCipher.Port.crypt, (0, ⟨[], by norm_num⟩)⟩
    (Program.consistent_nil EncryptThenMAC.body none _ _) (by simp [EncryptThenMAC.body, callProg])

/-- Encryption calls CTR, tags the ciphertext, then returns the pair. -/
theorem encrypt_transcript {q : ℕ} (hq : 1 ≤ q) (nonce : Nonce)
    (ad message ciphertext : Message) (tag : Block) :
    (EncryptThenMAC (budget := q)).1
      [(⟨⟨none, AEAD.Port.encrypt⟩, (nonce, ad, message)⟩,
        ⟨⟨some (), .inl StreamCipher.Port.crypt⟩, (nonce, message)⟩),
       (⟨⟨some (), .inl StreamCipher.Port.crypt⟩, ciphertext⟩,
        ⟨⟨some (), .inr Tagging.Port.tag⟩, (nonce, ad, ciphertext)⟩),
       (⟨⟨some (), .inr Tagging.Port.tag⟩, tag⟩,
        ⟨⟨none, AEAD.Port.encrypt⟩, (ciphertext, tag)⟩)] = 1 := by
  simp only [EncryptThenMAC, EncryptThenMAC.program, Interface.Converter.ofProgram,
    Interface.ofDDC_apply]
  rw [if_pos]
  refine ⟨rfl, fun k hk _ => ?_⟩
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hk
  rcases k with _ | _ | _ | k <;> first
  | omega
  | simp [DDC.ofProgramOn, filterDom, DDC.ofProgram, Program.after, Program.run, Program.step,
      Program.emit, EncryptThenMAC.body, callProg, returnProg, outsideInputs, splitIn, hq]

/-- A tag that verifies permits exactly the requested decryption call. -/
theorem decrypt_transcript {q : ℕ} (hq : 1 ≤ q) (nonce : Nonce)
    (ad ciphertext message : Message) (tag : Block) :
    (EncryptThenMAC (budget := q)).1
      [(⟨⟨none, AEAD.Port.decrypt⟩, (nonce, ad, ciphertext, tag)⟩,
        ⟨⟨some (), .inr Tagging.Port.verify⟩, ((nonce, ad, ciphertext), tag)⟩),
       (⟨⟨some (), .inr Tagging.Port.verify⟩, true⟩,
        ⟨⟨some (), .inl StreamCipher.Port.crypt⟩, (nonce, ciphertext)⟩),
       (⟨⟨some (), .inl StreamCipher.Port.crypt⟩, message⟩,
        ⟨⟨none, AEAD.Port.decrypt⟩, some message⟩)] = 1 := by
  simp only [EncryptThenMAC, EncryptThenMAC.program, Interface.Converter.ofProgram,
    Interface.ofDDC_apply]
  rw [if_pos]
  refine ⟨rfl, fun k hk _ => ?_⟩
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hk
  rcases k with _ | _ | _ | k <;> first
  | omega
  | simp [DDC.ofProgramOn, filterDom, DDC.ofProgram, Program.after, Program.run, Program.step,
      Program.emit, EncryptThenMAC.body, callProg, returnProg, outsideInputs, splitIn, hq]

/-- A tag that does not verify returns failure without querying the cipher. -/
theorem decrypt_rejects {q : ℕ} (hq : 1 ≤ q) (nonce : Nonce) (ad ciphertext : Message)
    (tag : Block) :
    (EncryptThenMAC (budget := q)).1
      [(⟨⟨none, AEAD.Port.decrypt⟩, (nonce, ad, ciphertext, tag)⟩,
        ⟨⟨some (), .inr Tagging.Port.verify⟩, ((nonce, ad, ciphertext), tag)⟩),
       (⟨⟨some (), .inr Tagging.Port.verify⟩, false⟩,
        ⟨⟨none, AEAD.Port.decrypt⟩, none⟩)] = 1 := by
  simp only [EncryptThenMAC, EncryptThenMAC.program, Interface.Converter.ofProgram,
    Interface.ofDDC_apply]
  rw [if_pos]
  refine ⟨rfl, fun k hk _ => ?_⟩
  simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at hk
  rcases k with _ | _ | k <;> first
  | omega
  | simp [DDC.ofProgramOn, filterDom, DDC.ofProgram, Program.after, Program.run, Program.step,
      Program.emit, EncryptThenMAC.body, callProg, returnProg, outsideInputs, splitIn, hq]

/-- A message needs at most `2³²` counter blocks, so the 32-bit counter does not wrap. -/
theorem blockCount_le (message : Message) : CTR.blockCount message.val.length ≤ 2 ^ 32 := by
  have hm := message.property
  simp only [CTR.blockCount]
  omega

/-- No input to the authenticator reaches PMAC's oversized-message case. -/
theorem authenticationBytes_length (nonce : Nonce) (ad ciphertext : Message) :
    (authenticationBytes (nonce, ad, ciphertext)).length ≤ 16 * 2 ^ 128 := by
  have ha := ad.property
  have hc := ciphertext.property
  simp only [authenticationBytes, encodeNat, List.length_append, List.length_map, List.length_range,
    Vector.length_toList]
  omega

/-- AES-256 under a key. -/
def aes (key : AES.Key .aes256) : Block → Block := AES.cipher .aes256 key

/-- Encryption: CTR under the encryption key from the nonce's counter block, and the PMAC tag of
the nonce, the associated data and the ciphertext under the authentication key. -/
def aeadEncrypt (encryptionKey authenticationKey : AES.Key .aes256) (nonce : Nonce) (ad : Message)
    (message : Message) : Message × Block :=
  let ciphertext : Message :=
    ⟨CTR.crypt (aes encryptionKey) (CTR.initialBlock nonce) message.val,
      (CTR.length_xorStream _ _).trans message.property⟩
  (ciphertext, PMAC.pmac (aes authenticationKey) (authenticationBytes (nonce, ad, ciphertext)))

/-- Decryption when the tag verifies. -/
def aeadDecrypt (encryptionKey authenticationKey : AES.Key .aes256) (nonce : Nonce) (ad : Message)
    (ciphertext : Message) (tag : Block) : Option (List UInt8) :=
  if PMAC.pmac (aes authenticationKey) (authenticationBytes (nonce, ad, ciphertext)) == tag then
    some (CTR.crypt (aes encryptionKey) (CTR.initialBlock nonce) ciphertext.val)
  else none

/-- **Decryption inverts encryption.** -/
theorem aeadDecrypt_aeadEncrypt (encryptionKey authenticationKey : AES.Key .aes256)
    (nonce : Nonce) (ad message : Message) :
    let encrypted := aeadEncrypt encryptionKey authenticationKey nonce ad message
    aeadDecrypt encryptionKey authenticationKey nonce ad encrypted.1 encrypted.2 =
      some message.val := by
  simp only [aeadEncrypt, aeadDecrypt, beq_self_eq_true, if_true, CTR.crypt_crypt]

/-- A message of the given bytes. -/
def message (xs : List UInt8) (h : xs.length ≤ 2 ^ 36) : Message := ⟨xs, h⟩

-- One key pair encrypts messages of different lengths, including the empty message; decryption
-- rejects a change of the nonce, the associated data, the ciphertext or the tag.
#guard
  let encryptionKey : AES.Key .aes256 := Tests.hexBytes _ (String.ofList (List.replicate 64 '0'))
  let authenticationKey : AES.Key .aes256 :=
    Tests.hexBytes _ (String.ofList (List.replicate 63 '0') ++ "1")
  let nonce : Nonce := Tests.hexBytes _ "000000000000000000000007"
  let ad := message [0x61, 0x64] (by norm_num)
  let messages := [message [] (by norm_num), message [1, 2, 3] (by norm_num),
    message (List.replicate 33 0x42) (by norm_num)]
  messages.all fun m =>
    let (ciphertext, tag) := aeadEncrypt encryptionKey authenticationKey nonce ad m
    let decrypt := aeadDecrypt encryptionKey authenticationKey
    decrypt nonce ad ciphertext tag == some m.val &&
    decrypt nonce (message [0x62, 0x64] (by norm_num)) ciphertext tag == none &&
    decrypt (Tests.hexBytes _ "000000000000000000000008") ad ciphertext tag == none &&
    decrypt nonce ad (message [0xff] (by norm_num)) tag == none &&
    decrypt nonce ad ciphertext (tag ^^^ Tests.hexBytes _ "00000000000000000000000000000001") ==
      none

end DSLExamples.Authenticated

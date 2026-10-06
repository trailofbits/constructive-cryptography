import Commons

/-!
# Axioms of the Commons library

The ideal systems, the block-cipher systems, the CDH systems, the systems and notions of
symmetric, authenticated and public-key encryption, of KEMs, MACs, signatures, PRGs, universal and
collision-resistant hash functions, AES, CTR, PMAC and NMAC, the hash functions, ML-KEM and
ML-DSA depend only on `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Commons.Definitions.Ideal
#print axioms Commons.URF
#print axioms Commons.URP
#print axioms Commons.StrongURP
#print axioms Commons.TweakableURP
#print axioms Commons.TweakableStrongURP
#print axioms Commons.MemorylessSource.memoryless_eq

-- Commons.Definitions.Cipher
#print axioms Commons.BlockCipher.perm
#print axioms Commons.BlockCipher.encrypt_decrypt
#print axioms Commons.BlockCipher.Real
#print axioms Commons.BlockCipher.StrongReal

-- Commons.Definitions.DiffieHellman
#print axioms Commons.CDH.Real
#print axioms Commons.CDH.Ideal
#print axioms Commons.CDH.Assumption.systems
#print axioms Commons.CDH.Assumption

-- Commons.Definitions.Encryption
#print axioms Commons.SymmetricEncryption.encryptions
#print axioms Commons.Encryption.Real
#print axioms Commons.Encryption.CPA
#print axioms Commons.Encryption.INDCPA.systems
#print axioms Commons.Encryption.INDCPA
#print axioms Commons.Encryption.Left
#print axioms Commons.Encryption.Right
#print axioms Commons.Encryption.LORCPA.systems
#print axioms Commons.Encryption.LORCPA

-- Commons.Definitions.AEAD
#print axioms Commons.AE.Real
#print axioms Commons.AE.CCA
#print axioms Commons.AE.PTXT
#print axioms Commons.AE.CTXT
#print axioms Commons.AE.CTXT.perPort
#print axioms Commons.AE.Ideal
#print axioms Commons.AE.Ideal.perPort
#print axioms Commons.AE.INDCCA.systems
#print axioms Commons.AE.INTPTXT.systems
#print axioms Commons.AE.INTCTXT.systems
#print axioms Commons.AE.Secure.systems
#print axioms Commons.AE.INDCCA
#print axioms Commons.AE.INTPTXT
#print axioms Commons.AE.INTCTXT
#print axioms Commons.AE.Secure

-- Commons.Definitions.KEM
#print axioms Commons.KEM.Correct
#print axioms Commons.KEM.encapsulations
#print axioms Commons.KEM.Real
#print axioms Commons.KEM.CCA
#print axioms Commons.KEM.INDCCA.systems
#print axioms Commons.KEM.INDCCA
#print axioms Commons.KEM.INDCPA.systems
#print axioms Commons.KEM.INDCPA

-- Commons.Definitions.PublicKeyEncryption
#print axioms Commons.PublicKeyEncryption.encryptions
#print axioms Commons.PKE.Real
#print axioms Commons.PKE.CCA
#print axioms Commons.PKE.INDCCA.systems
#print axioms Commons.PKE.INDCCA
#print axioms Commons.PKE.INDCPA.systems
#print axioms Commons.PKE.INDCPA

-- Commons.Definitions.MAC
#print axioms Commons.MAC.Correct
#print axioms Commons.MAC.tags
#print axioms Commons.MAC.Real
#print axioms Commons.MAC.EUF
#print axioms Commons.MAC.SUF
#print axioms Commons.MAC.EUFCMA.systems
#print axioms Commons.MAC.SUFCMA.systems
#print axioms Commons.MAC.EUFCMA
#print axioms Commons.MAC.SUFCMA

-- Commons.Definitions.PRG
#print axioms Commons.PRG.Secure.systems
#print axioms Commons.PRG.Secure

-- Commons.Definitions.UniversalHash
#print axioms Commons.UniversalHash.Real
#print axioms Commons.UniversalHash.Ideal
#print axioms Commons.UniversalHash.DifferenceReal
#print axioms Commons.UniversalHash.DifferenceIdeal
#print axioms Commons.UniversalHash.UHF.systems
#print axioms Commons.UniversalHash.UHF
#print axioms Commons.UniversalHash.DUF.systems
#print axioms Commons.UniversalHash.DUF

-- Commons.Definitions.Hash
#print axioms Commons.Hash.Real
#print axioms Commons.Hash.Ideal
#print axioms Commons.Hash.CR.systems
#print axioms Commons.Hash.CR

-- Commons.Definitions.Signature
#print axioms Commons.SignatureScheme.Correct
#print axioms Commons.SignatureScheme.signatures
#print axioms Commons.SignatureScheme.Real
#print axioms Commons.SignatureScheme.EUF
#print axioms Commons.SignatureScheme.SUF
#print axioms Commons.SignatureScheme.EUFCMA.systems
#print axioms Commons.SignatureScheme.SUFCMA.systems
#print axioms Commons.SignatureScheme.EUFCMA
#print axioms Commons.SignatureScheme.SUFCMA

-- Commons.Schemes.BlockCipher.AES
#print axioms Commons.AES.cipher
#print axioms Commons.AES.invCipher
#print axioms Commons.AES.invMixColumn_mixColumn
#print axioms Commons.AES.invCipher_cipher
#print axioms Commons.AES.blockCipher

-- Commons.Schemes.Stream.CTR
#print axioms Commons.CTR.crypt
#print axioms Commons.CTR.crypt_crypt
#print axioms Commons.CTR

-- Commons.Schemes.MAC.NMAC
#print axioms Commons.NMAC.cascade
#print axioms Commons.NMAC.nmac
#print axioms Commons.NMAC.Real

-- Commons.Schemes.MAC.PMAC
#print axioms Commons.PMAC.pmac
#print axioms Commons.PMAC.mac
#print axioms Commons.PMAC.mac_correct
#print axioms Commons.PMAC

-- Commons.Schemes.Hash
#print axioms Commons.SHA256.sha256
#print axioms Commons.Keccak.keccakF
#print axioms Commons.Keccak.sha3_256
#print axioms Commons.Keccak.shake128
#print axioms Commons.Keccak.keccak256

-- Commons.Schemes.KEM.MLKEM
#print axioms MLKEM.keygenInternal
#print axioms MLKEM.encapsInternal
#print axioms MLKEM.decaps
#print axioms MLKEM.toKEM
#print axioms MLKEM.Concrete.concretePrimitives
#print axioms MLKEM.Concrete.concreteNTTRingLaws
#print axioms MLKEM.Concrete.nttCoeffs_pair_eval
#print axioms MLKEM.Concrete.ntt_negacyclicMul

-- Commons.Schemes.Signature.MLDSA
#print axioms MLDSA.keyGenFromSeed
#print axioms MLDSA.fipsSign
#print axioms MLDSA.fipsVerify
#print axioms MLDSA.toSignatureScheme
#print axioms MLDSA.fipsSign_fipsVerify_correct
#print axioms MLDSA.Concrete.concretePrimitives
#print axioms MLDSA.Concrete.concretePrimitives_laws
#print axioms MLDSA.Concrete.nttCoeffs_apply
#print axioms MLDSA.Concrete.ntt_negacyclicMul
#print axioms MLDSA.Concrete.concreteNTTRingLaws
#print axioms MLDSA.Concrete.fipsSign_fipsVerify

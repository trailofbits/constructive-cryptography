module

public import Commons.Definitions.KEM
public import Commons.Definitions.Encryption
public import Commons.Definitions.PublicKeyEncryption

/-!
# KEM–DEM composition

`KEMDEM.scheme kem dem` uses the KEM key pair and encrypts each message with a freshly
encapsulated key. Its ciphertext is `(encapsulation, encrypted message)`.
`dec_eq_none_of_decaps_eq_none` gives the rejection branch; `dec_eq_of_decaps_eq_some`
passes a recovered key directly to DEM decryption.

```text
pk ──encaps──▶ (ck, k)     m ──dem.enc k──▶ cd     ciphertext: (ck, cd)
sk, ck ──decaps──▶ k       cd ──dem.dec k──▶ m
```

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons.KEMDEM

open Probability Distribution

-- `PK`, `SK` carry asymmetric keys; `K` is the encapsulated symmetric key.
-- `CK`, `CD` carry the KEM and DEM ciphertexts; `M` carries messages.
variable {PK SK K CK CD M : Type}

/-- The hybrid `scheme kem dem` generates KEM keys and encrypts as
`(ck, k) ← kem.encaps pk; cd ← dem.enc k m; return (ck, cd)`.
Decryption is `(kem.decaps sk ck).bind (dem.dec · cd)`, rejecting failed decapsulation.
[1, Exercise 11.9, p. 461]: “The key generation algorithm for E is the same as that of Ekem.” -/
noncomputable def scheme
    -- `kem` generates keys and encapsulates/decapsulates; `dem` encrypts/decrypts with that key.
    (kem : KEM PK SK CK K) (dem : SymmetricEncryption K M CD) :
    PublicKeyEncryption PK SK M (CK × CD) where
  gen := kem.gen
  enc pk m := (kem.encaps pk).bind fun encapsulation =>
    ProbDist.map (Prod.mk encapsulation.1) (dem.enc encapsulation.2 m)
  dec sk c := (kem.decaps sk c.1).bind fun k => dem.dec k c.2

/-- A failed decapsulation makes the composed decryption reject. -/
lemma dec_eq_none_of_decaps_eq_none
    -- `kem` supplies decapsulation; `dem` supplies decryption with the recovered key.
    (kem : KEM PK SK CK K) (dem : SymmetricEncryption K M CD)
    -- `failed` rejects the first component `ck`; the DEM ciphertext `cd` is unused.
    (sk : SK) (ck : CK) (cd : CD) (failed : kem.decaps sk ck = none) :
    (scheme kem dem).dec sk (ck, cd) = none := by
  change (kem.decaps sk ck).bind _ = none
  rw [failed, Option.bind_none]

/-- Successful decapsulation supplies exactly its recovered key to DEM decryption. -/
lemma dec_eq_of_decaps_eq_some
    -- `kem` supplies decapsulation; `dem` supplies decryption with the recovered key.
    (kem : KEM PK SK CK K) (dem : SymmetricEncryption K M CD)
    -- `recovered` identifies the key `k` used to decrypt `cd`.
    (sk : SK) (ck : CK) (cd : CD) (k : K) (recovered : kem.decaps sk ck = some k) :
    (scheme kem dem).dec sk (ck, cd) = dem.dec k cd := by
  change (kem.decaps sk ck).bind _ = _
  rw [recovered, Option.bind_some]

end Commons.KEMDEM

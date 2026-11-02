module

public import Commons.Constructions.KEMDEM

/-!
# Correctness of KEM–DEM

`KEMDEM.correct` composes the KEM and DEM correctness contracts. A supported encryption
first supplies a supported encapsulation `(ck, k)`, then a supported DEM ciphertext `cd`.
KEM correctness recovers `k`; DEM correctness recovers the message.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons.KEMDEM

open Probability Distribution

/-- KEM and DEM correctness imply correctness of their hybrid scheme.
[1, Exercise 11.9(a), p. 461] asks that the hybrid “satisfies the correctness requirement”.
Here `kem`, `dem` are the source's `Ekem`, `Es`. Its DEM requirement covers the whole key space;
`dem.Correct` covers generated keys, so `compatible` places each encapsulated key there. -/
theorem correct
    -- `PK`, `SK` carry asymmetric keys, `K` symmetric keys, `CK`, `CD` ciphertexts, `M` messages.
    {PK SK K CK CD M : Type}
    (kem : KEM PK SK CK K) (dem : SymmetricEncryption K M CD)
    -- `kemCorrect` recovers every supported encapsulated key; `demCorrect` recovers messages.
    (kemCorrect : kem.Correct) (demCorrect : dem.Correct)
    -- `compatible` puts every key encapsulated under a generated pair in the DEM contract.
    (compatible : ∀ pk sk, (pk, sk) ∈ kem.gen.1.support →
      ∀ ck k, (ck, k) ∈ (kem.encaps pk).1.support → k ∈ dem.gen.1.support) :
    (scheme kem dem).Correct := by
  intro pk sk hkeys message ciphertext hc
  -- Split the supported composed encryption into its two successive supported draws.
  obtain ⟨⟨ck, k⟩, hk, hcd⟩ := mem_support_bindK hc
  obtain ⟨cd, hd, rfl⟩ := mem_support_fTransform (Prod.mk ck) (dem.enc k message).1 hcd
  -- Decapsulation restores the DEM key, whose support contract now gives the message.
  rw [dec_eq_of_decaps_eq_some kem dem sk ck cd k (kemCorrect pk sk hkeys ck k hk)]
  exact demCorrect k (compatible pk sk hkeys ck k hk) message cd hd

end Commons.KEMDEM

import Commons.Definitions.Encryption

/-!
# Authenticated encryption

Banfi, §2.3.4 (printed pp. 18–21). The correlated encryption and decryption oracles
`⟦E_k, D_k⟧` of a symmetric-key encryption scheme, the transformations `ρ^cca`, `ρ^ptxt`,
`ρ^ctxt` and `ρ^ae`, and the security notions ind-cca, int-ptxt, int-ctxt and ae as
substitutions (Definitions 2.3.5–2.3.8), declared in the DSL on the interface `AE M C` with a
budget per port.

`ρ^ctxt` and `ρ^ae` act on `E_k` alone: they are converters from `AE M C` to `Encryption M C`,
whose decryption queries nothing inside, attached to the system `E_k` of `Encryption.Real`.

A notion is the pair of its systems `(X₀, X₁)` (Banfi, §2.3.1), independent of the substitution
relation; the predicate of the same name states it for the admitted distinguishers, `X₀ ≃[ε] X₁`.

Planned: nonces and associated data.

## Main definitions

* `AE M C`: the encryption and decryption interface
* `AE.Real scheme`: `⟦E_k, D_k⟧` for `k ← Gen`
* `AE.CCA`, `AE.PTXT`, `AE.CTXT`, `AE.Ideal`: the transformations `ρ^cca`, `ρ^ptxt`, `ρ^ctxt`
  and `ρ^ae`, written so with `open Commons`
* `AE.INDCCA.systems`, `AE.INTPTXT.systems`, `AE.INTCTXT.systems`, `AE.Secure.systems`: the
  systems of ind-cca, int-ptxt, int-ctxt and ae
* `AE.INDCCA`, `AE.INTPTXT`, `AE.INTCTXT`, `AE.Secure`: these notions for the distinguisher
  advantage, within an error
-/

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface AE(M C : Type) [Fintype M] [Fintype C]
  enc(message : M) → C
  dec(ciphertext : C) → Option M

/-- Banfi, printed p. 18, footnote 2: the first inserted message whose ciphertext is `c`. -/
def AE.replay {M C : Type} [DecidableEq C] (table : List (M × C)) (c : C) : Option M :=
  (table.find? fun entry => entry.2 == c).map Prod.fst

/-- Banfi, printed p. 19: “if `m ∈ Q` then output `m`, otherwise output `⊥`”. -/
def AE.retain {M : Type} [DecidableEq M] (known : List M) (message : Option M) : Option M :=
  message.bind fun m => if m ∈ known then some m else none

noncomputable section

variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]

-- `⟦E_k, D_k⟧` for `k ← Gen`: on `m`, output `c ← Enc_k(m)`; on `c`, output `Dec_k(c)`.
system AE.Real(scheme : SymmetricEncryption K M C) [DecidableEq K] [DecidableEq M] : AE M C
  initialize
    key ←$ scheme.gen
  on enc(message : M) → C
    encryptions ←$ scheme.encryptions
    return encryptions (key, message)
  on dec(ciphertext : C) → Option M
    return scheme.dec key ciphertext

-- `ρ^cca`: encrypt a random message `m̃` instead of `m` and record `(m, c)`; on `c`, output its
-- first recorded message, otherwise forward `c`.
converter AE.CCA(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] [Nonempty M] : AE M C
  inside ae : AE M C
  initialize
    table ← ([] : List (M × C))
  on enc(message : M) → C
    replacement ←$ 𝒰[M]
    ciphertext ← ae.enc(replacement)
    table ← table ++ [(message, ciphertext)]
    return ciphertext
  on dec(ciphertext : C) → Option M
    match AE.replay table ciphertext
    | some message →
      return some message
    | none →
      result ← ae.dec(ciphertext)
      return result

-- `ρ^ptxt`: record each encrypted message; output a decryption only if its message was
-- recorded, otherwise `⊥`.
converter AE.PTXT(M C : Type) [Fintype M] [Fintype C] [DecidableEq M] : AE M C
  inside ae : AE M C
  initialize
    queried ← ([] : List M)
  on enc(message : M) → C
    queried ← queried ++ [message]
    ciphertext ← ae.enc(message)
    return ciphertext
  on dec(ciphertext : C) → Option M
    message ← ae.dec(ciphertext)
    return AE.retain queried message

-- `ρ^ctxt`: on `m`, output `c ← E_k(m)` and record `(m, c)`; on `c`, output its first recorded
-- message, otherwise `⊥`.
converter AE.CTXT(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] : AE M C
  inside encryption : Encryption M C
  initialize
    table ← ([] : List (M × C))
  on enc(message : M) → C
    ciphertext ← encryption.enc(message)
    table ← table ++ [(message, ciphertext)]
    return ciphertext
  on dec(ciphertext : C) → Option M
    return AE.replay table ciphertext

-- `ρ^ae`: on `m`, output `c ← E_k(m̃)` for a random message `m̃` and record `(m, c)`; on `c`,
-- output its first recorded message, otherwise `⊥`.
converter AE.Ideal(M C : Type) [Fintype M] [Fintype C] [DecidableEq C] [Nonempty M] : AE M C
  inside encryption : Encryption M C
  initialize
    table ← ([] : List (M × C))
  on enc(message : M) → C
    replacement ←$ 𝒰[M]
    ciphertext ← encryption.enc(replacement)
    table ← table ++ [(message, ciphertext)]
    return ciphertext
  on dec(ciphertext : C) → Option M
    return AE.replay table ciphertext

/-- `ρ^cca`, as Banfi writes it. -/
scoped notation "ρ^cca" => AE.CCA.perPort _ _

/-- `ρ^ptxt`, as Banfi writes it. -/
scoped notation "ρ^ptxt" => AE.PTXT.perPort _ _

/-- `ρ^ctxt`, as Banfi writes it. -/
scoped notation "ρ^ctxt" => AE.CTXT.perPort _ _

/-- `ρ^ae`, as Banfi writes it. -/
scoped notation "ρ^ae" => AE.Ideal.perPort _ _

/-- **The systems of ind-cca** (Banfi, Definition 2.3.5): `⟦E_k, D_k⟧` and `ρ^cca(⟦E_k, D_k⟧)`,
for `k ← Gen`, at the budget `q` per port. -/
def AE.INDCCA.systems [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    Interface.Resource (AE.perPort M C q) × Interface.Resource (AE.perPort M C q) :=
  (AE.Real.perPort scheme, AE.CCA.perPort M C • AE.Real.perPort scheme)

/-- **The systems of int-ptxt** (Banfi, Definition 2.3.6): `⟦E_k, D_k⟧` and
`ρ^ptxt(⟦E_k, D_k⟧)`, for `k ← Gen`, at the budget `q` per port. -/
def AE.INTPTXT.systems [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    Interface.Resource (AE.perPort M C q) × Interface.Resource (AE.perPort M C q) :=
  (AE.Real.perPort scheme, AE.PTXT.perPort M C • AE.Real.perPort scheme)

/-- **The systems of int-ctxt** (Banfi, Definition 2.3.7): `⟦E_k, D_k⟧` and `ρ^ctxt(E_k)`, for
`k ← Gen`, at the budget `q` per port. -/
def AE.INTCTXT.systems [DecidableEq K] [DecidableEq M] [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    Interface.Resource (AE.perPort M C q) × Interface.Resource (AE.perPort M C q) :=
  (AE.Real.perPort scheme, AE.CTXT.perPort M C • Encryption.Real.perPort scheme)

/-- **The systems of ae** (Banfi, Definition 2.3.8): `⟦E_k, D_k⟧` and
`⟦E$_k, D^⊥⟧ = ρ^ae(E_k)`, for `k ← Gen`, at the budget `q` per port. -/
def AE.Secure.systems [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    Interface.Resource (AE.perPort M C q) × Interface.Resource (AE.perPort M C q) :=
  (AE.Real.perPort scheme, AE.Ideal.perPort M C • Encryption.Real.perPort scheme)

/-- **ind-cca** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^cca(⟦E_k, D_k⟧)`. -/
def AE.INDCCA [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    (error : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (AE.INDCCA.systems scheme q).1 ≃[error] (AE.INDCCA.systems scheme q).2

/-- **int-ptxt** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^ptxt(⟦E_k, D_k⟧)`. -/
def AE.INTPTXT [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    (error : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (AE.INTPTXT.systems scheme q).1 ≃[error] (AE.INTPTXT.systems scheme q).2

/-- **int-ctxt** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^ctxt(E_k)`. -/
def AE.INTCTXT [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] (scheme : SymmetricEncryption K M C)
    {q : AE.Port → ℕ} (error : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) :
    Prop :=
  (AE.INTCTXT.systems scheme q).1 ≃[error] (AE.INTCTXT.systems scheme q).2

/-- **ae** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes for
`⟦E$_k, D^⊥⟧ = ρ^ae(E_k)`. -/
def AE.Secure [Interface.AdmissibleDistinguishers]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    (error : (AE.perPort M C q).inputDomain.DistinguisherBehavior → ENNReal) : Prop :=
  (AE.Secure.systems scheme q).1 ≃[error] (AE.Secure.systems scheme q).2

end

end Commons

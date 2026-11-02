module

public import Commons.Definitions.Encryption

/-!
# Authenticated encryption

`AE.system` exposes encryption and decryption with one retained key, the correlated oracles
`⟦E_k, D_k⟧` of [1, §2.3.4, p. 18]. `AE.CCA`, `AE.PTXT`, `AE.CTXT` and `AE.Ideal` implement
the transformations `ρ^cca`, `ρ^ptxt`, `ρ^ctxt` and `ρ^ae` [1, pp. 18–19]. Each call to
encryption draws a fresh ciphertext; both ports share the key drawn from `scheme.gen`.

The latter two transformations expose `AE M C` using only the encryption interface
`Encryption M C`: decryption reads their retained table without an inside query. Their
component is `Encryption.system`, the encryption oracle of the same scheme.

The pairs `AE.INDCCA.systems`, `AE.INTPTXT.systems`, `AE.INTCTXT.systems` and `AE.Secure.systems`
state ind-cca, int-ptxt, int-ctxt and ae [1, Definitions 2.3.5–2.3.8, pp. 20–21]. Their security
predicates bound each selected typed distinguisher's advantage by `error d`, following
[1, §2.3.1, p. 14]. `AdmissibleDistinguishers` selects the tests, with no closure assumed.
The interface carries plaintexts and ciphertexts, with a query budget per port.

`AE.replay` uses `List.lookup` after swapping each message/ciphertext pair.
`List.lookup_append` preserves earlier matches when new records are appended.
`AE.replay_eq_find?` gives the first-match form used by `AuthenticatedEncryption.replay_mem`
in `Examples.AuthenticatedEncryption.Collision` to show that replay returns a recorded message.

## Main definitions

* `AE M C`: the encryption and decryption interface
* `AE.system scheme`: `⟦E_k, D_k⟧` for `k ← Gen`
* `AE.CCA`, `AE.PTXT`, `AE.CTXT`, `AE.Ideal`: the transformations `ρ^cca`, `ρ^ptxt`, `ρ^ctxt`
  and `ρ^ae`, written so with `open Commons`
* `AE.INDCCA.systems`, `AE.INTPTXT.systems`, `AE.INTCTXT.systems`, `AE.Secure.systems`: the
  systems of ind-cca, int-ptxt, int-ctxt and ae
* `AE.INDCCA`, `AE.INTPTXT`, `AE.INTCTXT`, `AE.Secure`: these notions for the distinguisher
  advantage, within an error

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability
open scoped SystemAlgebra SystemAlgebra.DSL

interface AE(M C : Type) [Fintype M] [Fintype C]
  enc(message : M) → C
  dec(ciphertext : C) → Option M

/-- The first inserted message whose ciphertext is `c`, or `none` when absent:
[1, p. 18, footnote 2], “the first corresponding element inserted in Q is taken.” -/
def AE.replay
    -- `M` carries messages and `C` ciphertexts; only ciphertexts are compared.
    {M C : Type} [DecidableEq C]
    -- `table` records message/ciphertext pairs chronologically; `c` is the requested ciphertext.
    (table : List (M × C)) (c : C) : Option M :=
  (table.map Prod.swap).lookup c

/-- Replay is the message projection of the first record with ciphertext `c`. -/
lemma AE.replay_eq_find?
    -- `M` carries messages and `C` ciphertexts, with decidable ciphertext equality.
    {M C : Type} [DecidableEq C]
    -- `table` records message/ciphertext pairs in insertion order; `c` selects the first match.
    (table : List (M × C)) (c : C) :
    AE.replay table c = (table.find? fun entry => entry.2 == c).map Prod.fst := by
  -- Both searches return the first successful optional value, with the pair fields exchanged.
  rw [AE.replay, List.lookup_eq_findSome?, List.findSome?_map,
    List.find?_eq_findSome?_guard, List.map_findSome?]
  congr 1
  funext entry
  simp only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, Option.guard]
  rw [BEq.comm (a := c)]
  split <;> rfl

/-- [1, p. 19]: “if `m ∈ Q` then output `m`, otherwise output `⊥`”. -/
def AE.retain {M : Type} [DecidableEq M] (known : List M) (message : Option M) : Option M :=
  message.bind fun m => if m ∈ known then some m else none

noncomputable section

-- `K`, `M`, `C` carry keys, fixed-length messages and ciphertexts.
variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]

-- Retain one `k ← scheme.gen` shared by `enc(m)` and `dec(c)` [1, §2.3.4, p. 18].
-- Encryption draws a fresh `scheme.enc k m`; decryption returns `scheme.dec k c`.
-- The interface admits the selected total or per-port query budget.
system AE.system
    -- `scheme` supplies the common key law and both operations.
    (scheme : SymmetricEncryption K M C) [DecidableEq K] [DecidableEq M] : AE M C
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

/-- The replaying random-message transformation `ρ^cca` of [1, §2.3.4, p. 18]. -/
scoped notation "ρ^cca" => AE.CCA.perPort _ _

/-- The plaintext-integrity transformation `ρ^ptxt` of [1, §2.3.4, p. 19]. -/
scoped notation "ρ^ptxt" => AE.PTXT.perPort _ _

/-- The ciphertext-integrity transformation `ρ^ctxt` of [1, §2.3.4, p. 19]. -/
scoped notation "ρ^ctxt" => AE.CTXT.perPort _ _

/-- The authenticated-encryption transformation `ρ^ae` of [1, §2.3.4, p. 19]. -/
scoped notation "ρ^ae" => AE.Ideal.perPort _ _

/-- **The systems of ind-cca** [1, Definition 2.3.5, p. 20]: `⟦E_k, D_k⟧` and `ρ^cca(⟦E_k, D_k⟧)`,
for `k ← Gen`, at the budget `q` per port. -/
def AE.INDCCA.systems [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    TypedSystem (AE.perPort M C q) × TypedSystem (AE.perPort M C q) :=
  (AE.system.perPort scheme, AE.CCA.perPort M C • AE.system.perPort scheme)

/-- **The systems of int-ptxt** [1, Definition 2.3.6, p. 21]: `⟦E_k, D_k⟧` and
`ρ^ptxt(⟦E_k, D_k⟧)`, for `k ← Gen`, at the budget `q` per port. -/
def AE.INTPTXT.systems [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C)
    (q : AE.Port → ℕ) :
    TypedSystem (AE.perPort M C q) × TypedSystem (AE.perPort M C q) :=
  (AE.system.perPort scheme, AE.PTXT.perPort M C • AE.system.perPort scheme)

/-- **The systems of int-ctxt** [1, Definition 2.3.7, p. 21]: `⟦E_k, D_k⟧` and `ρ^ctxt(E_k)`, for
`k ← Gen`, at the budget `q` per port. -/
def AE.INTCTXT.systems [DecidableEq K] [DecidableEq M] [DecidableEq C]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    TypedSystem (AE.perPort M C q) × TypedSystem (AE.perPort M C q) :=
  (AE.system.perPort scheme, AE.CTXT.perPort M C • Encryption.system.perPort scheme)

/-- **The systems of ae** [1, Definition 2.3.8, p. 21]: `⟦E_k, D_k⟧` and
`⟦E$_k, D^⊥⟧ = ρ^ae(E_k)`, for `k ← Gen`, at the budget `q` per port. -/
def AE.Secure.systems [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) (q : AE.Port → ℕ) :
    TypedSystem (AE.perPort M C q) × TypedSystem (AE.perPort M C q) :=
  (AE.system.perPort scheme, AE.Ideal.perPort M C • Encryption.system.perPort scheme)

/-- **ind-cca** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^cca(⟦E_k, D_k⟧)`. -/
def AE.INDCCA [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (AE.perPort M C q)) → ENNReal) : Prop :=
  (AE.INDCCA.systems scheme q).1 ≃[error] (AE.INDCCA.systems scheme q).2

/-- **int-ptxt** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^ptxt(⟦E_k, D_k⟧)`. -/
def AE.INTPTXT [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (AE.perPort M C q)) → ENNReal) : Prop :=
  (AE.INTPTXT.systems scheme q).1 ≃[error] (AE.INTPTXT.systems scheme q).2

/-- **int-ctxt** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes
for `ρ^ctxt(E_k)`. -/
def AE.INTCTXT [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] (scheme : SymmetricEncryption K M C)
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    {q : AE.Port → ℕ} (error : (TypedDistinguisher (AE.perPort M C q)) → ENNReal) :
    Prop :=
  (AE.INTCTXT.systems scheme q).1 ≃[error] (AE.INTCTXT.systems scheme q).2

/-- **ae** within `error`: against the admitted distinguishers, `⟦E_k, D_k⟧` substitutes for
`⟦E$_k, D^⊥⟧ = ρ^ae(E_k)`. -/
def AE.Secure [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    [DecidableEq K] [DecidableEq M] [DecidableEq C] [Nonempty M]
    (scheme : SymmetricEncryption K M C) {q : AE.Port → ℕ}
    -- `q` is the query budget per port; `error d` bounds the advantage of each admitted `d`.
    (error : (TypedDistinguisher (AE.perPort M C q)) → ENNReal) : Prop :=
  (AE.Secure.systems scheme q).1 ≃[error] (AE.Secure.systems scheme q).2

end

end Commons

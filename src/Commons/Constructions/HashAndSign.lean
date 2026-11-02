module

public import Commons.Definitions.Signature.Keyed

/-!
# Hash-and-sign

`hashAndSign H q` exposes `Signing PK M Sig q` using `Signing PK D Sig q`, for `H : M → D`.
`hashAndSign.body_bounded` certifies the query budget; `hashAndSign.query_eq` and
`hashAndSign.reply_eq` give the exact single call.

```text
  signing = SignatureScheme.system scheme  [retains (pk, sk) ∼ scheme.gen]

  publicKey()  ────────────────────────────► signing.publicKey() ──pk──► pk
  sign(m)      ──H(m)───────────────────────► signing.sign(H(m)) ──σ────► σ
  verify(m, σ) ──(H(m), σ)──────────────────► signing.verify(H(m), σ) ──► valid
```

This is the “hash-and-sign paradigm” of [1, §13.2, p. 532]: the original key generation
and the two message translations of [1, (13.1), p. 532].
`hashAndSign.system H scheme q` attaches this converter to `SignatureScheme.system scheme`,
which draws each signing reply freshly under its retained secret key.

`hashAndSign.smul_ofMemoryless` gives the attachment equation at a fixed reply law.
`SignatureScheme.system.eq_keyed` from `Commons.Definitions.Signature.Keyed` and
`hashAndSign.system.eq_keyed` expose the retained pair throughout the assembled interaction.
`hashAndSign.system.sign_verify_eq_of_correct` then transfers the component support contract
through `TypedSystem.keyed_snoc_snoc_eq_of_support`: after a transcript `h` with
`h.length + 2 ≤ q`, verifying a returned signature on the same message with reply `true`
preserves the signing-prefix mass.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra

noncomputable section

-- `PK` carries public keys, `M` outside messages, `D` digests, and `Sig` signatures.
-- Budget `0` below names their port alphabets, which are independent of the query allowance.
variable {PK M D Sig : Type} [Fintype PK] [Fintype M] [Fintype D] [Fintype Sig]

/-- Keep `publicKey()` unchanged; map `sign(m)` to `sign(H m)` and
`verify(m, σ)` to `verify(H m, σ)`, preserving the queried port. -/
def hashAndSign.input
    -- `H` maps outside messages in `M` to inside signing messages in `D`.
    (H : M → D) :
    ∀ i, (Signing PK M Sig 0).X i → (Signing PK D Sig 0).X i
  | .publicKey, () => ()
  | .sign, m => H m
  | .verify, (m, σ) => (H m, σ)

/-- Query `input H i x` once at port `i`, then return its reply unchanged; retain only `()`. -/
def hashAndSign.body
    -- `H` gives the message hash used by both signing and verification.
    (H : M → D) :
    Program Unit Signing.Port Signing.Port (Signing PK M Sig 0).X (Signing PK M Sig 0).Y
      (Signing PK D Sig 0).X (Signing PK D Sig 0).Y :=
  fun _ i x => callProg i (hashAndSign.input H i x) (fun y => returnProg ((), y))

/-- Every invocation makes at most one inside query. -/
lemma hashAndSign.body_bounded
    -- `H` transforms the input without making an additional inside query.
    (H : M → D) :
    (hashAndSign.body (PK := PK) (Sig := Sig) H).Bounded 1 := by
  intro s i x
  exact callBound_call _ _ _ (fun y => callBound_return 0 ((), y))

/-- At budget `q`, send each `i(x)` to `i(input H i x)` and return its reply unchanged.
Every outside query uses one inside query. -/
def hashAndSign
    -- `H` maps messages to digests; `q` is the same total allowance outside and inside.
    (H : M → D) (q : ℕ) :
    TypedConverter (Signing PK M Sig q) (Signing PK D Sig q) :=
  TypedConverter.ofProgram () (hashAndSign.body H) (hashAndSign.body_bounded H)
    (fun xs hne hl => ⟨hne, by simpa only [Nat.one_mul] using hl⟩)

/-- The first action requests the transformed input at the original port. -/
lemma hashAndSign.query_eq
    -- `H` is the hash; `s = ()` is the state and `i(x)` the outside query.
    (H : M → D) (s : Unit)
    (i : Signing.Port) (x : (Signing PK M Sig 0).X i) :
    hashAndSign.body (PK := PK) (Sig := Sig) H s i x [] =
      .inr ⟨i, hashAndSign.input H i x⟩ := rfl

/-- Every reply at the requested port is returned unchanged to the outside caller. -/
lemma hashAndSign.reply_eq
    -- `H` is the hash; `s`, `i(x)` give the invocation and `y` is its inside reply.
    (H : M → D) (s : Unit)
    (i : Signing.Port) (x : (Signing PK M Sig 0).X i) (y : (Signing PK D Sig 0).Y i) :
    hashAndSign.body (PK := PK) (Sig := Sig) H s i x
      [(⟨i, hashAndSign.input H i x⟩, ⟨i, y⟩)] = .inl ((), y) := by
  simp only [hashAndSign.body, callProg, returnProg, ↓reduceDIte]

/-- `hashAndSign H q • ofMemoryless ν = ofMemoryless (fun i x => ν i (input H i x))`. -/
lemma hashAndSign.smul_ofMemoryless
    -- `H` hashes messages; `ν` supplies a normalized inside reply law at every port and input.
    (H : M → D)
    (ν : ∀ i, (Signing PK D Sig 0).X i → ProbDist ((Signing PK D Sig 0).Y i))
    -- `q` bounds both the outside and inside histories because each call costs one query.
    (q : ℕ) :
    hashAndSign (PK := PK) (Sig := Sig) H q • TypedSystem.ofMemoryless (Signing PK D Sig q) ν =
      TypedSystem.ofMemoryless (Signing PK M Sig q)
        (fun i x => ν i (hashAndSign.input H i x)) := by
  -- Apply bounded program attachment, then the one-query and unchanged-reply equations.
  rw [hashAndSign]
  apply TypedConverter.ofProgram_smul_ofMemoryless _ _ _ _ rfl
  intro s i x
  simp only [Program.memorylessReplyLaw,
    (hashAndSign.query_eq (PK := PK) (M := M) (D := D) (Sig := Sig)),
    (hashAndSign.reply_eq (PK := PK) (M := M) (D := D) (Sig := Sig)),
    List.nil_append]
  exact bindK_single_one _

-- `SK` carries retained signing keys; decidable equality indexes each freshly sampled
-- `SK × D` signature table in the component system.
variable {SK : Type} [Fintype SK] [DecidableEq SK] [DecidableEq D]

/-- Retain `(pk, sk) ∼ scheme.gen`. Publish `pk`, sign `H m` freshly under `sk`, and verify
`(H m, σ)` under `pk`, on the outside interface `Signing PK M Sig q`. -/
def hashAndSign.system
    -- `H` hashes outside messages; `scheme` signs and verifies digests in `D`.
    (H : M → D) (scheme : SignatureScheme PK SK D Sig)
    -- `q` bounds the outside and inside queries equally.
    (q : ℕ) : TypedSystem (Signing PK M Sig q) :=
  hashAndSign H q • SignatureScheme.system scheme

/-- The named system is the hash converter attached to the retained signature component. -/
lemma hashAndSign.system_eq
    -- `H`, `scheme` supply the converter and component; `q` is their common allowance.
    (H : M → D) (scheme : SignatureScheme PK SK D Sig) (q : ℕ) :
    hashAndSign.system H scheme q = hashAndSign H q • SignatureScheme.system scheme := rfl

/-- At retained `keys = (pk, sk)`, publish `pk` and use “S′(sk, m) := S(sk, H(m))” and
“V′(pk, m, σ) := V(pk, H(m), σ)” [1, (13.1), p. 532]. Signing gives the normalized law
`scheme.sign sk (H m)`; verification gives the point law at `scheme.verify pk (H m) σ`. -/
def hashAndSign.system.replyLaw
    -- `H` hashes messages; `scheme`, `keys` supply the signature operations at the retained pair.
    (H : M → D) (scheme : SignatureScheme PK SK D Sig) (keys : PK × SK) :
    ∀ i, (Signing PK M Sig 0).X i → ProbDist ((Signing PK M Sig 0).Y i) :=
  fun i x => SignatureScheme.system.replyLaw scheme keys i (hashAndSign.input H i x)

/-- `system H scheme q = keyed scheme.gen (replyLaw H scheme)`: retain one pair and
answer each query from the component law at its transformed input. -/
lemma hashAndSign.system.eq_keyed
    -- `H` transforms messages; `scheme` supplies one retained pair; `q` is the query budget.
    (H : M → D) (scheme : SignatureScheme PK SK D Sig) (q : ℕ) :
    hashAndSign.system H scheme q =
      TypedSystem.keyed (A := Signing PK M Sig q) scheme.gen
        (hashAndSign.system.replyLaw H scheme) := by
  -- Rewrite the component once, then scope its retained draw through attachment.
  rw [hashAndSign.system_eq, SignatureScheme.system.eq_keyed]
  simp only [TypedSystem.keyed, TypedConverter.smul_sample]
  congr 1
  funext keys
  exact hashAndSign.smul_ofMemoryless H (SignatureScheme.system.replyLaw scheme keys) q

/-- For `R = system H scheme q`, `R[h, sign(m) → σ, verify(m, σ) → true] = R[h, sign(m) → σ]`,
where `R[t] = R.1 t` is the cumulative probability of transcript `t`. At a positive-mass
signing prefix, verification therefore accepts with probability one.
The component contract says a signature is “always accepted by V” [1, Definition 13.1, p. 529]. -/
theorem hashAndSign.system.sign_verify_eq_of_correct
    -- `H` is any message hash; `scheme`, `correct` supply signing and its support contract.
    (H : M → D) (scheme : SignatureScheme PK SK D Sig) (correct : scheme.Correct)
    -- `h` is the prior transcript; `hq` admits its signing/verification extension at budget `q`.
    (q : ℕ) (h : List ((Σ i, (Signing PK M Sig q).X i) × (Σ i, (Signing PK M Sig q).Y i)))
    (hq : h.length + 2 ≤ q)
    -- `m` is the outside message; `σ` is the signing reply reused for its verification.
    (m : M) (σ : Sig) :
    (hashAndSign.system H scheme q).1
        ((h ++ [(⟨.sign, m⟩, ⟨.sign, σ⟩)]) ++ [(⟨.verify, (m, σ)⟩, ⟨.verify, true⟩)]) =
      (hashAndSign.system H scheme q).1 (h ++ [(⟨.sign, m⟩, ⟨.sign, σ⟩)]) := by
  -- Both successive queries fit the total allowance `q`.
  have hdSign : (Signing PK M Sig q).inputDomain h ⟨.sign, m⟩ := by
    apply Interface.queryBudget_inputDomain_iff.mpr
    omega
  have hdVerify : (Signing PK M Sig q).inputDomain
      (h ++ [(⟨.sign, m⟩, ⟨.sign, σ⟩)]) ⟨.verify, (m, σ)⟩ := by
    apply Interface.queryBudget_inputDomain_iff.mpr
    simp only [List.length_append, List.length_singleton]
    omega
  -- At every supported pair, the signature on `H m` verifies against that same digest.
  rw [hashAndSign.system.eq_keyed]
  apply TypedSystem.keyed_snoc_snoc_eq_of_support (hd := hdSign) (hd' := hdVerify)
  intro keys hkeys hσ
  simp only [hashAndSign.system.replyLaw, hashAndSign.input, SignatureScheme.system.replyLaw,
    correct keys.1 keys.2 hkeys (H m) σ hσ, ProbDist.single, Finsupp.single_eq_same]

end

end Commons

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Frost.Algebra

/-!
# The FROST protocol, concretely (RFC 9591 functional core)

The actual protocol — signing (this half assumes the threshold keys
`KEYS^t`) and the Pedersen/Feldman DKG (the de-idealization) — as pure
functions over an abstract prime-order group (`F`-module `V` with
generator `g`), with all randomness explicit as inputs (MauRen16 §3.5:
coins are a *resource*, so the protocol maps are deterministic and
everything provable about them is proved here, carrier-free).  Hashes
(`H1` for binding factors, `H2` for the challenge) are parameters —
the random-oracle *resource* instantiates them at the carrier.

## Sources, per half

As in `Applications.Frost.Algebra`, the two halves have **different** sources, and each
declaration is cited individually:

* **signing** — RFC 9591 §4 (helpers) and §5 (the two-round protocol),
  with verification in App. A/B.  §5's framing: "FROST requires two
  rounds to complete.  In the first round, participants generate and
  publish one-time-use commitments…"
* **the DKG** — Komlo–Goldberg (SAC 2020).  RFC 9591 §1: "Key generation
  for FROST signing is out of scope for this document.  However, for
  completeness, key generation with a trusted dealer is specified in
  Appendix C."  The RFC's App. C is a *single* trusted dealer; the
  distributed, multi-dealer version below is Komlo–Goldberg's, and its
  per-dealer pieces (`dealShare`, `vssCommit`, `feldmanCheck`) coincide
  with App. C's `polynomial_evaluate` / `vss_commit` / `vss_verify`, so
  those carry RFC citations.  **Flagged**: Komlo–Goldberg is not in the
  repo — its citations are attributions, not quotations.

Fully proved (no leaves):

* signing: per-share verification accepts honest shares
  (`shareVerify_signShare`), and **completeness** — the aggregate of a
  quorum's honest shares passes plain Schnorr verification against the
  group key (`verify_aggregate`, and `verify_aggregate_shamir` with the
  key given as a Shamir-shared polynomial);
* DKG: Feldman share checks accept honest dealings
  (`feldmanCheck_dealShare`), the group key aggregates the dealers'
  constants (`groupKey_eq`), any quorum of combined shares reconstructs
  the joint secret (`dkg_reconstruct`), hence **any two quorums agree**
  (`dkg_reconstruct_agree`).

What is *not* here, by design, is the concrete security content: the per-`Z`
simulator leaves and the carrier reduction establishing the ideal
unforgeability game bound. Their carrier-free contracts and composition are
stated in `Applications.Frost.Construction`; a concrete carrier must supply
the leaves.
-/

open Polynomial Finset

namespace AbstractCryptography
namespace Frost

variable {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-! ### Signing, RFC 9591 §4–§5 (assumes the threshold keys) -/

/-- RFC 9591 §5.1 (Round One - Commitment): the signer's
`(hiding_nonce, binding_nonce)` pair for one signing session, "one-time
use".  Here it comes from the coin resource rather than from §4.1's
`nonce_generate`, which is the carrier's job (`FrostRfc9591`). -/
structure NoncePair (F : Type*) where
  d : F
  e : F

/-- RFC 9591 §5.1: the public
`(hiding_nonce_commitment, binding_nonce_commitment)`, `(D, E) =
(g^d, g^e)`. -/
structure NonceCommitment (V : Type*) where
  D : V
  E : V

/-- RFC 9591 §5.1 (Round One - Commitment): commit to the nonces,
`G.ScalarBaseMult` of each. -/
def commitNonce (g : V) (np : NoncePair F) : NonceCommitment V :=
  ⟨np.d • g, np.e • g⟩

/-- RFC 9591 §4.5, `compute_group_commitment`:

    def compute_group_commitment(commitment_list, binding_factor_list):
      group_commitment = G.Identity()
      for (identifier, hiding_nonce_commitment,
           binding_nonce_commitment) in commitment_list:
        binding_factor = binding_factor_for_participant(
            binding_factor_list, identifier)
        binding_nonce = G.ScalarMult(
            binding_nonce_commitment,
            binding_factor)
        group_commitment = (
            group_commitment +
            hiding_nonce_commitment +
            binding_nonce)

i.e. `R = Π_{l∈S} D_l · E_l^{ρ_l}`, additively. -/
def groupCommitment (S : Finset ι) (coms : ι → NonceCommitment V)
    (ρ : ι → F) : V :=
  ∑ l ∈ S, ((coms l).D + ρ l • (coms l).E)

/-- RFC 9591 §5.2 (Round Two - Signature Share Generation), `sign`'s
signature share:

    # Compute the signature share
    (hiding_nonce, binding_nonce) = nonce_i
    sig_share = hiding_nonce + (binding_nonce * binding_factor) +
        (lambda_i * sk_i * challenge)

i.e. `z_l = d_l + e_l·ρ_l + λ_l·s_l·c`.  `ρ`, `λ`, `c` are parameters
here; the RFC computes them (§4.4, §4.2, §4.6) — that is
`FrostRfc9591.signShare`'s job. -/
def signShare (np : NoncePair F) (ρ lam s c : F) : F :=
  np.d + np.e * ρ + lam * s * c

/-- RFC 9591 §5.3 (Signature Share Aggregation), `aggregate`'s scalar
half: "`# Compute aggregated signature` / `z = Scalar(0)` / `for z_i in
sig_shares:` / `z = z + z_i`" — i.e. `z = Σ_{l∈S} z_l`. -/
def aggregate (S : Finset ι) (zs : ι → F) : F :=
  ∑ l ∈ S, zs l

/-- RFC 9591 App. B, `prime_order_verify`'s relation: "`l =
G.ScalarBaseMult(z)` / `r = R + G.ScalarMult(PK, c)` / `return l == r`" —
i.e. `g^z = R · Y^c`, additively. -/
def schnorrVerify (g Y R : V) (c z : F) : Prop :=
  z • g = R + c • Y

/-- RFC 9591 §5.3, `verify_signature_share`'s relation — "The
Coordinator can verify each signature share before aggregating":

    comm_share = hiding_nonce_commitment + G.ScalarMult(
        binding_nonce_commitment, binding_factor)
    …
    l = G.ScalarBaseMult(sig_share_i)
    r = comm_share + G.ScalarMult(PK_i, challenge * lambda_i)

i.e. `g^{z_l} = D_l · E_l^{ρ_l} · Y_l^{c·λ_l}`. -/
def shareVerify (g : V) (com : NonceCommitment V) (Yl : V)
    (ρ lam c zl : F) : Prop :=
  zl • g = com.D + ρ • com.E + (c * lam) • Yl

/-- **Honest shares pass the per-share check**: the §5.2 `sign` share is
accepted by the §5.3 `verify_signature_share` relation.
`frost_share_verify` in protocol form.  (Completeness only — that a
*dishonest* share is rejected is the RFC's §5.4 identifiable-abort claim,
not proved here.) -/
theorem shareVerify_signShare (g : V) (np : NoncePair F) (ρ lam s c : F) :
    shareVerify g (commitNonce g np) (s • g) ρ lam c
      (signShare np ρ lam s c) := by
  unfold shareVerify commitNonce signShare
  simpa using frost_share_verify g np.d np.e ρ lam s c

omit [DecidableEq ι] in
/-- **Completeness**: the §5.3 `aggregate` of a quorum's honest §5.2
`sign` shares is accepted by App. B's `prime_order_verify` against the
group key `Y = g^x`, provided the Lagrange-weighted shares reconstruct
`x`.  `frost_aggregate` in protocol form.

This is the theorem RFC 9591 §5.3 asserts in prose when it says the
output "is the output signature `(R, z)`" and "The Coordinator SHOULD
verify this signature using the group public key". -/
theorem verify_aggregate (g : V) (S : Finset ι) (np : ι → NoncePair F)
    (ρ lam s : ι → F) (c x : F)
    (hx : ∑ l ∈ S, lam l * s l = x) :
    schnorrVerify g (x • g)
      (groupCommitment S (fun l => commitNonce g (np l)) ρ) c
      (aggregate S (fun l => signShare (np l) (ρ l) (lam l) (s l) c)) := by
  unfold schnorrVerify groupCommitment aggregate commitNonce
  simpa using
    frost_aggregate g S (fun l => (np l).d) (fun l => (np l).e) ρ lam s
      (fun l => signShare (np l) (ρ l) (lam l) (s l) c) c x
      (fun l _ => rfl) hx

/-- Completeness with the key in Shamir-shared form — i.e. over a key
produced by RFC 9591 App. C's trusted dealer: shares `s_l = f(v_l)` of
the secret polynomial (App. C.1 `secret_share_shard`), Lagrange
coefficients at the quorum (§4.2 `derive_interpolating_value`).  The `hx`
hypothesis is discharged by `shamir_reconstruct` (App. C.1.1
`polynomial_interpolate_constant`). -/
theorem verify_aggregate_shamir (g : V) {S : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v S) {f : F[X]} (hdeg : f.degree < #S)
    (np : ι → NoncePair F) (ρ : ι → F) (c : F) :
    schnorrVerify g (f.eval 0 • g)
      (groupCommitment S (fun l => commitNonce g (np l)) ρ) c
      (aggregate S (fun l => signShare (np l) (ρ l)
        (lagrangeZero S v l) (f.eval (v l)) c)) :=
  verify_aggregate g S np ρ _ _ c _ (shamir_reconstruct hvs hdeg)

/-! ### The Pedersen/Feldman DKG (the de-idealization)

Komlo–Goldberg (SAC 2020), *not* RFC 9591 — see the header.  The
per-dealer pieces coincide with RFC 9591 App. C (Trusted Dealer Key
Generation) and are cited to it; the multi-dealer aggregation is not in
the RFC and is attributed to Komlo–Goldberg without a section number.
-/

/-- Dealer `j`'s polynomial in coefficient form `a : ℕ → F` (degree
`< t`), evaluated at `x` — RFC 9591 App. C.1.1 `polynomial_evaluate`,
"for evaluating a polynomial `f(x)` at a particular point `x` using
Horner's method, i.e., computing `y = f(x)`".  (Horner's method is the
RFC's evaluation strategy; the sum-of-monomials form here is
extensionally the same polynomial — see `coeffPoly_eval`.)

App. C.1's coefficient convention, which this matches: "A polynomial of
maximum degree `t` is represented as a list of `t+1` coefficients, where
the constant term of the polynomial is in the first position and the
highest-degree coefficient is in the last position." -/
def dealShare (a : ℕ → F) (t : ℕ) (x : F) : F :=
  ∑ k ∈ Finset.range t, a k * x ^ k

/-- Dealer `j`'s public Feldman commitment vector `φ_k = g^{a_k}` — RFC
9591 App. C.2, `vss_commit`:

    def vss_commit(coeffs):
      vss_commitment = []
      for coeff in coeffs:
        A_i = G.ScalarBaseMult(coeff)
        vss_commitment.append(A_i)
      return vss_commitment -/
def vssCommit (g : V) (a : ℕ → F) (k : ℕ) : V :=
  a k • g

/-- The Feldman check run by the receiver at point `x` — RFC 9591
App. C.2, `vss_verify`'s relation: "`S_i = G.ScalarBaseMult(sk_i)` …
`for j in range(0, MIN_PARTICIPANTS): S_i' += G.ScalarMult(
vss_commitment[j], pow(i, j))` / `return S_i == S_i'`", i.e.
`g^{share} = Π_k φ_k^{x^k}`.

App. C.2: "If `vss_verify` fails, the participant MUST abort the
protocol, and the failure should be investigated out of band." -/
def feldmanCheck (g : V) (φ : ℕ → V) (t : ℕ) (x : F) (share : F) : Prop :=
  share • g = ∑ k ∈ Finset.range t, x ^ k • φ k

/-- **Honest dealings pass the Feldman check**: an App. C.1.1
`polynomial_evaluate` share of a polynomial whose coefficients were
committed by App. C.2 `vss_commit` is accepted by `vss_verify`.
`share_check` in protocol form.  Completeness only — the binding
direction is the VSS security claim, not proved here. -/
theorem feldmanCheck_dealShare (g : V) (a : ℕ → F) (t : ℕ) (x : F) :
    feldmanCheck g (vssCommit g a) t x (dealShare a t x) :=
  share_check g a t x

/-- The group public key from the dealers' constant commitments,
`Y = Π_j φ_{j,0} = g^{Σ_j a_j(0)}` — `key_aggregation` in protocol form.

**Komlo–Goldberg**, not RFC 9591: the RFC's single-dealer analogue is
App. C.2 `derive_group_info`, "`PK = vss_commitment[0]`", which has no
product over dealers. -/
theorem groupKey_eq (g : V) (P : Finset κ) (a : κ → ℕ → F) :
    ∑ j ∈ P, vssCommit g (a j) 0 = (∑ j ∈ P, a j 0) • g :=
  (key_aggregation g fun j => a j 0).symm

/-- Coefficient-form polynomial, for bridging to the `Polynomial` API. -/
private noncomputable def coeffPoly (a : ℕ → F) (t : ℕ) : F[X] :=
  ∑ k ∈ Finset.range t, Polynomial.C (a k) * Polynomial.X ^ k

private theorem coeffPoly_eval (a : ℕ → F) (t : ℕ) (x : F) :
    (coeffPoly a t).eval x = dealShare a t x := by
  simp [coeffPoly, dealShare, Polynomial.eval_finset_sum]

private theorem coeffPoly_degree_lt (a : ℕ → F) {t n : ℕ} (h : t ≤ n) :
    (coeffPoly a t).degree < n := by
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)]
  intro k hk
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
  exact_mod_cast lt_of_lt_of_le (Finset.mem_range.mp hk) h

private theorem coeffPoly_eval_zero (a : ℕ → F) {t : ℕ} (ht : 0 < t) :
    (coeffPoly a t).eval 0 = a 0 := by
  rw [coeffPoly_eval]
  unfold dealShare
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · intro h
    exact absurd (Finset.mem_range.mpr ht) h

/-- **DKG reconstruction** (Komlo–Goldberg): the combined shares
`s_i = Σ_j dealShare_j(v_i)` of any quorum of size `≥ t` reconstruct the
joint secret `Σ_j a_j(0)` — `sum_shares_reconstruct` in protocol form.

The RFC's App. C.1 states the single-dealer version of this guarantee:
"any cooperating subset of at least MIN_PARTICIPANTS participants can
recover the secret".  `hcard : t ≤ #S` is that quorum bound; `hvs` is
"distinct x coordinates". -/
theorem dkg_reconstruct (P : Finset κ) (a : κ → ℕ → F) {t : ℕ}
    (ht : 0 < t) {S : Finset ι} {v : ι → F} (hvs : Set.InjOn v S)
    (hcard : t ≤ #S) :
    ∑ i ∈ S, lagrangeZero S v i * (∑ j ∈ P, dealShare (a j) t (v i))
      = ∑ j ∈ P, a j 0 := by
  have h := sum_shares_reconstruct (P := P)
    (fun j => coeffPoly (a j) t) (s := S) (v := v) hvs
    (fun j _ => coeffPoly_degree_lt (a j) hcard)
  simp only [coeffPoly_eval, coeffPoly_eval_zero _ ht] at h
  exact h

/-- **Quorum agreement**: any two quorums reconstruct the same secret.

This is what RFC 9591 App. C.2 names as the point of the VSS check:
"This check ensures that all participants have a point (their share) on
the same polynomial, ensuring that they can reconstruct the correct
secret later."  Here it is a theorem about the honest path, over the
multi-dealer (Komlo–Goldberg) key. -/
theorem dkg_reconstruct_agree (P : Finset κ) (a : κ → ℕ → F) {t : ℕ}
    (ht : 0 < t) {S S' : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v S) (hvs' : Set.InjOn v S')
    (hcard : t ≤ #S) (hcard' : t ≤ #S') :
    ∑ i ∈ S, lagrangeZero S v i * (∑ j ∈ P, dealShare (a j) t (v i))
      = ∑ i ∈ S', lagrangeZero S' v i * (∑ j ∈ P, dealShare (a j) t (v i)) := by
  rw [dkg_reconstruct P a ht hvs hcard, dkg_reconstruct P a ht hvs' hcard']

/-- **End-to-end completeness over a DKG key**: a quorum signing with
the DKG's combined shares verifies against the DKG's aggregated group
key.  The whole honest protocol path — deal (App. C.1.1), combine, commit
(§5.1), sign (§5.2), aggregate (§5.3), verify (App. B) — proved as one
theorem, over a Komlo–Goldberg distributed key rather than the RFC's
trusted-dealer one. -/
theorem verify_aggregate_dkg (g : V) (P : Finset κ) (a : κ → ℕ → F)
    {t : ℕ} (ht : 0 < t) {S : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v S) (hcard : t ≤ #S)
    (np : ι → NoncePair F) (ρ : ι → F) (c : F) :
    schnorrVerify g (∑ j ∈ P, vssCommit g (a j) 0)
      (groupCommitment S (fun l => commitNonce g (np l)) ρ) c
      (aggregate S (fun l => signShare (np l) (ρ l)
        (lagrangeZero S v l) (∑ j ∈ P, dealShare (a j) t (v l)) c)) := by
  rw [groupKey_eq]
  exact verify_aggregate g S np ρ _ _ c _ (dkg_reconstruct P a ht hvs hcard)

end Frost
end AbstractCryptography

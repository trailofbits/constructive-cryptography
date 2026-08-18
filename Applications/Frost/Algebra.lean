/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Module

/-!
# The FROST algebra: Shamir, Schnorr, and aggregation identities (M3)

The complete *correctness* content of FROST as theorems over any field
`F` and `F`-module `V` — zero cryptographic leaves.  Everything is stated
in the exponent, additively: for a prime-order group `G` with generator
`g`, `Additive G` is a `ZMod q`-module and `x • g` reads `g^x`; that
instantiation is the carrier's (trivial) job.

## Which source says what

Two sources, and they do **not** cover the same ground — each declaration
is cited individually.

* **RFC 9591** (*The Flexible Round-Optimized Schnorr Threshold (FROST)
  Protocol for Two-Round Schnorr Signatures*) covers signing (§4, §5),
  verification (App. A, App. B), and *trusted-dealer* key generation
  (App. C).  Section numbers below are the RFC's own.
* **Komlo–Goldberg** (SAC 2020) covers the *distributed* key generation.
  RFC 9591 §1 is explicit that this is out of its scope: "Key generation
  for FROST signing is out of scope for this document.  However, for
  completeness, key generation with a trusted dealer is specified in
  Appendix C."  So the DKG-only content here (`sum_shares_reconstruct` —
  the *summed*-polynomial chain, which the RFC's single-dealer Appendix C
  does not have) is attributed to Komlo–Goldberg and **not** given an RFC
  section.  **Flagged**: that paper is not in the repo, so its citations
  here are attributions only, not quotations.

Contents:

* `lagrangeZero` — RFC 9591 §4.2 `derive_interpolating_value`.
* `shamir_reconstruct` — RFC 9591 App. C.1.1
  `polynomial_interpolate_constant` (`Lagrange.eq_interpolate` doing the
  work).
* `sum_shares_reconstruct` — the DKG chain (Komlo–Goldberg): shares of
  the *summed* polynomial (each participant contributes `f_j`, shares are
  `s_i = Σ_j f_j(i)`) reconstruct the summed secret `Σ_j f_j(0)`.
* `share_check` — RFC 9591 App. C.2 `vss_verify`.
* `schnorr_verify` — the Schnorr equation behind App. B
  `prime_order_verify`.
* `frost_share_verify` — RFC 9591 §5.3 `verify_signature_share`.
* `frost_aggregate` — the aggregation identity behind §5.3 `aggregate`:
  Lagrange in the exponent, the heart of FROST's correctness.
-/

open Polynomial Finset

namespace AbstractCryptography
namespace Frost

variable {F : Type*} [Field F] {ι κ : Type*} [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

/-- RFC 9591 §4.2 (Polynomials), `derive_interpolating_value` — "The
function `derive_interpolating_value` derives a value that is used for
polynomial interpolation.  It is provided a list of x-coordinates as
input, each of which cannot equal 0."

    def derive_interpolating_value(L, x_i):
      …
      numerator = Scalar(1)
      denominator = Scalar(1)
      for x_j in L:
        if x_j == x_i: continue
        numerator *= x_j
        denominator *= x_j - x_i

      value = numerator / denominator
      return value

i.e. `λ_i = Π_{j≠i} v_j / Π_{j≠i} (v_j − v_i)`, which is the Lagrange
basis polynomial for node `i` of the node set `s`, evaluated at `0`. -/
noncomputable def lagrangeZero (s : Finset ι) (v : ι → F) (i : ι) : F :=
  (Lagrange.basis s v i).eval 0

/-- **Shamir reconstruction** — RFC 9591 App. C.1.1,
`polynomial_interpolate_constant`, "for recovering the constant term of
an interpolating polynomial defined by a set of points":

    Inputs:
    - points, a set of t points with distinct x coordinates on
      a polynomial f, …
    Outputs:
    - f_zero, the constant term of f, i.e., f(0), a Scalar.

    def polynomial_interpolate_constant(points):
      x_coords = []
      for (x, y) in points:
        x_coords.append(x)

      f_zero = Scalar(0)
      for (x, y) in points:
        delta = y * derive_interpolating_value(x_coords, x)
        f_zero += delta

      return f_zero

App. C.1 on why: "In Shamir secret sharing, a dealer distributes a secret
Scalar `s` to `n` participants in such a way that any cooperating subset
of at least MIN_PARTICIPANTS participants can recover the secret."

`hvs`/`hdeg` are the RFC's two side conditions: "distinct x coordinates",
and a quorum at least as large as the polynomial's degree. -/
theorem shamir_reconstruct {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) {f : F[X]} (hdeg : f.degree < #s) :
    ∑ i ∈ s, lagrangeZero s v i * f.eval (v i) = f.eval 0 := by
  conv_rhs => rw [Lagrange.eq_interpolate hvs hdeg]
  rw [Lagrange.interpolate_apply, Polynomial.eval_finset_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, lagrangeZero, mul_comm]

/-- **Ours**: `shamir_reconstruct` pushed through `• g`, i.e. read in the
exponent — shares of the secret key recombine to the key, as group
elements.  This is the form App. C.2's `vss_verify` and §5.3's
`verify_signature_share` consume. -/
theorem shamir_reconstruct_smul (g : V) {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) {f : F[X]} (hdeg : f.degree < #s) :
    ∑ i ∈ s, lagrangeZero s v i • (f.eval (v i) • g) = f.eval 0 • g := by
  rw [← shamir_reconstruct hvs hdeg, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => smul_smul ..

/-- **The DKG chain** — Komlo–Goldberg (SAC 2020), the *distributed* key
generation, **not** RFC 9591 content: the RFC's App. C has a single
trusted dealer with a single polynomial, and §1 puts DKG out of scope
("Key generation for FROST signing is out of scope for this document").

With each participant `j` contributing a sharing polynomial `f_j` (all of
degree below the quorum size), the summed shares `s_i = Σ_j f_j(i)`
reconstruct the summed secret `Σ_j f_j(0)` — Pedersen-style additive key
generation composes with Shamir.

**Flagged**: Komlo–Goldberg is not in the repo, so this is an attribution
by content, not a quotation; no section number is claimed for it. -/
theorem sum_shares_reconstruct {P : Finset κ} (f : κ → F[X])
    {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    (hdeg : ∀ j ∈ P, (f j).degree < #s) :
    ∑ i ∈ s, lagrangeZero s v i * (∑ j ∈ P, (f j).eval (v i))
      = ∑ j ∈ P, (f j).eval 0 := by
  have h : ∀ i ∈ s, lagrangeZero s v i * (∑ j ∈ P, (f j).eval (v i))
      = ∑ j ∈ P, lagrangeZero s v i * (f j).eval (v i) :=
    fun i _ => Finset.mul_sum ..
  rw [Finset.sum_congr rfl h, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj => shamir_reconstruct hvs (hdeg j hj)

/-- **Commitment consistency** — RFC 9591 App. C.2 (Verifiable Secret
Sharing), the `vss_verify` relation:

    def vss_verify(share_i, vss_commitment)
      (i, sk_i) = share_i
      S_i = G.ScalarBaseMult(sk_i)
      S_i' = G.Identity()
      for j in range(0, MIN_PARTICIPANTS):
        S_i' += G.ScalarMult(vss_commitment[j], pow(i, j))
      return S_i == S_i'

i.e. `g^{f(j)} = Π_k φ_k^{j^k}` with `φ_k = g^{a_k}` (App. C.2
`vss_commit`: "`A_i = G.ScalarBaseMult(coeff)`").

App. C.2 on what the check buys: "Feldman's Verifiable Secret Sharing
(VSS) builds upon Shamir secret sharing, adding a verification step to
demonstrate the consistency of a participant's share with a public
commitment to the polynomial `f` for which the secret `s` is the constant
term.  This check ensures that all participants have a point (their
share) on the same polynomial, ensuring that they can reconstruct the
correct secret later."

This theorem is the *completeness* half only — honest dealings pass.  The
binding half is the RFC's security claim, not proved here. -/
theorem share_check (g : V) (a : ℕ → F) (t : ℕ) (j : F) :
    (∑ k ∈ Finset.range t, a k * j ^ k) • g
      = ∑ k ∈ Finset.range t, j ^ k • (a k • g) := by
  rw [Finset.sum_smul]
  exact Finset.sum_congr rfl fun k _ => by
    rw [smul_smul, mul_comm]

/-- **The Schnorr verification identity** — the algebra behind RFC 9591
App. B (Schnorr Signature Generation and Verification for Prime-Order
Groups), `prime_order_verify`:

    def prime_order_verify(msg, sig = (R, z), PK):
      …
      c = H2(challenge_input)

      l = G.ScalarBaseMult(z)
      r = R + G.ScalarMult(PK, c)
      return l == r

`z = k + c·x` gives `g^z = R · Y^c` for `R = g^k`, `Y = g^x`. -/
theorem schnorr_verify (g : V) (k x c : F) :
    (k + c * x) • g = k • g + c • (x • g) := by
  module

/-- **FROST per-share verification** — RFC 9591 §5.3,
`verify_signature_share`'s relation ("The Coordinator can verify each
signature share before aggregating"):

    # Compute the commitment share
    (hiding_nonce_commitment, binding_nonce_commitment) = comm_i
    comm_share = hiding_nonce_commitment + G.ScalarMult(
        binding_nonce_commitment, binding_factor)
    …
    # Compute relation values
    l = G.ScalarBaseMult(sig_share_i)
    r = comm_share + G.ScalarMult(PK_i, challenge * lambda_i)

    return l == r

So `z_l = d_l + e_l·ρ_l + λ_l·s_l·c` (the §5.2 `sign` formula) gives
`g^{z_l} = D_l · E_l^{ρ_l} · Y_l^{c·λ_l}` for `D_l = g^{d_l}`,
`E_l = g^{e_l}`, `Y_l = g^{s_l}`. -/
theorem frost_share_verify (g : V) (d e ρ lam sh c : F) :
    (d + e * ρ + lam * sh * c) • g
      = d • g + ρ • (e • g) + (c * lam) • (sh • g) := by
  module

omit [DecidableEq ι] in
/-- **The FROST aggregation identity** — Lagrange in the exponent, the
heart of the scheme's correctness.  The statement that RFC 9591 §5.3's
`aggregate` produces a signature App. B's `prime_order_verify` accepts.

With the response shares `z_l = d_l + e_l·ρ_l + λ_l·s_l·c` (§5.2 `sign`:
"`sig_share = hiding_nonce + (binding_nonce * binding_factor) +
(lambda_i * sk_i * challenge)`") and the key reconstruction
`Σ_l λ_l·s_l = x` (App. C.1.1 `polynomial_interpolate_constant`), the
aggregate `z = Σ_l z_l` (§5.3: "`z = z + z_i`") passes plain Schnorr
verification against the group commitment `R = Π_l D_l·E_l^{ρ_l}` (§4.5
`compute_group_commitment`) and the group key `Y = g^x`:

  `g^z = R · Y^c` -/
theorem frost_aggregate (g : V) (S : Finset ι) (d e ρ lam sh : ι → F)
    (z : ι → F) (c x : F)
    (hz : ∀ l ∈ S, z l = d l + e l * ρ l + lam l * sh l * c)
    (hx : ∑ l ∈ S, lam l * sh l = x) :
    (∑ l ∈ S, z l) • g
      = (∑ l ∈ S, (d l • g + ρ l • (e l • g))) + c • (x • g) := by
  have hsum : ∑ l ∈ S, z l = (∑ l ∈ S, (d l + e l * ρ l)) + c * x := by
    rw [← hx, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun l hl => by rw [hz l hl]; ring
  rw [hsum, add_smul, mul_smul, Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by
    rw [add_smul, smul_smul, mul_comm (e l) (ρ l), mul_smul]

/-- Additive key aggregation (DKG round 1) — **Komlo–Goldberg**, not RFC
9591: the group key is the product of the participants' commitment
constants, `Y = Π_j φ_{j,0}` for the secret `x = Σ_j a_{j,0}`.

The RFC's single-dealer counterpart is App. C.2's `derive_group_info`,
which just reads the constant commitment off the one dealer's vector
("`PK = vss_commitment[0]`"); there is no product over dealers because
there is only one.  **Flagged** as an attribution, per the header. -/
theorem key_aggregation (g : V) {P : Finset κ} (a : κ → F) :
    (∑ j ∈ P, a j) • g = ∑ j ∈ P, a j • g :=
  Finset.sum_smul

/-! ### Bias absorption: the honest/dishonest key split

The Pedersen/GJKR bias the uniform-key impossibility (carrier-side
`uniform_key_dkg_impossible`) forces the ideal to absorb.  The group key
`Y = (∑_j a_j(0))·g` splits along a partition of the dealers into honest
`H` and dishonest `D`, and — this is what "bias-absorbing" *means* — the
simulator, observing the dishonest summand `Y_D` from the Feldman
commitments and holding the ideal's group key `Y`, can always present an
honest contribution reconstructing exactly `Y`.  So the ideal key is
reachable for *every* adversarial bias, which is precisely the algebraic
fact that lets the DKG simulator distance be zero. -/

/-- **Key bias decomposition**: over a partition `P = H ∪ D` of the dealers
into honest and dishonest, the group key is the sum of the honest and
dishonest constant-term contributions in the exponent. -/
theorem key_bias_decomposition [DecidableEq κ] (g : V) {H D : Finset κ}
    (hdisj : Disjoint H D) (a : κ → F) :
    (∑ j ∈ H ∪ D, a j) • g = (∑ j ∈ H, a j) • g + (∑ j ∈ D, a j) • g := by
  rw [Finset.sum_union hdisj, add_smul]

/-- **The simulator can hit any ideal key** (bias absorption, realizability
form): given the ideal group key `target` and the dishonest contribution
`dishonest`, the honest contribution `target - dishonest` completes to
exactly `target`.  Whatever the adversary biases toward, the simulator
matches the ideal — the algebraic reason the bias-absorbing key ideal
admits a zero-distance DKG simulator, where the uniform-key ideal could
not. -/
theorem key_bias_absorb (target dishonest : V) :
    (target - dishonest) + dishonest = target :=
  sub_add_cancel target dishonest

/-! ### Special soundness: discrete-log extraction from two forgeries

The algebraic heart of the FROST → AOMDL reduction.  A rewinding /
forking adversary produces two accepting Schnorr transcripts sharing one
commitment `R` but with distinct challenges; the two verification
equations then *determine the discrete logarithm* as an explicit scalar.
This is Schnorr special soundness; the reduction's probabilistic content
(the forking-lemma success bound) sits above it in the carrier, but the
extraction itself is exact group algebra and carrier-free. -/

/-- **Schnorr special soundness** — the discrete-log extractor.  Two
accepting transcripts `(R, c, z)` and `(R, c', z')` on the *same*
commitment `R` against the same key `Y`, with distinct challenges
`c ≠ c'`, pin the key's discrete logarithm:

  `Y = ((c − c')⁻¹ · (z − z')) • g`.

Subtracting the two verification equations `z•g = R + c•Y` and
`z'•g = R + c'•Y` cancels `R` and leaves `(z − z')•g = (c − c')•Y`;
dividing by the nonzero `c − c'` reads off `dlog_g Y`.  The reduction
returns exactly this scalar as its one-more discrete log. -/
theorem schnorr_extract (g Y R : V) (c c' z z' : F)
    (h : z • g = R + c • Y) (h' : z' • g = R + c' • Y) (hne : c ≠ c') :
    Y = ((c - c')⁻¹ * (z - z')) • g := by
  have hcc : c - c' ≠ 0 := sub_ne_zero.mpr hne
  have key : (z - z') • g = (c - c') • Y := by
    rw [sub_smul, h, h', sub_smul]; abel
  calc Y = (c - c')⁻¹ • ((c - c') • Y) := by
            rw [smul_smul, inv_mul_cancel₀ hcc, one_smul]
    _ = (c - c')⁻¹ • ((z - z') • g) := by rw [key]
    _ = ((c - c')⁻¹ * (z - z')) • g := by rw [smul_smul]

/-- **The extracted scalar is the discrete logarithm**: reading
`schnorr_extract` as "the responses and challenges compute `dlog_g Y`",
the scalar `(c − c')⁻¹·(z − z')` satisfies `x • g = Y` — the AOMDL
solver's output for the challenge point `Y`. -/
theorem schnorr_extract_dlog (g Y R : V) (c c' z z' : F)
    (h : z • g = R + c • Y) (h' : z' • g = R + c' • Y) (hne : c ≠ c') :
    ((c - c')⁻¹ * (z - z')) • g = Y :=
  (schnorr_extract g Y R c c' z z' h h' hne).symm

/-- **FROST per-signer extraction** — special soundness at one signer's
partial verification equation (`frost_share_verify`'s relation).  Two
accepting shares `(D, E, ρ, c, z)` and `(D, E, ρ, c', z')` for signer `l`
sharing the round-one commitments `(D, E)` and binding factor `ρ` but with
distinct challenges pin the signer's key share `Yₗ` by the same
subtraction, the `c·λ` weighting cancelling with `λ ≠ 0`:

  `Yₗ = ((c − c')⁻¹ · λ⁻¹ · (z − z')) • g`.

This is what the reduction extracts when it forks a *single* signer whose
key share is the embedded AOMDL challenge. -/
theorem frost_share_extract (g Yl D E : V) (ρ lam c c' z z' : F)
    (h : z • g = D + ρ • E + (c * lam) • Yl)
    (h' : z' • g = D + ρ • E + (c' * lam) • Yl)
    (hc : c ≠ c') (hlam : lam ≠ 0) :
    Yl = ((c - c')⁻¹ * lam⁻¹ * (z - z')) • g := by
  have hcc : c - c' ≠ 0 := sub_ne_zero.mpr hc
  have hw : (c - c') * lam ≠ 0 := mul_ne_zero hcc hlam
  have key : (z - z') • g = ((c - c') * lam) • Yl := by
    rw [sub_smul, h, h', sub_mul, sub_smul]; abel
  calc Yl = ((c - c') * lam)⁻¹ • (((c - c') * lam) • Yl) := by
            rw [smul_smul, inv_mul_cancel₀ hw, one_smul]
    _ = ((c - c') * lam)⁻¹ • ((z - z') • g) := by rw [key]
    _ = ((c - c')⁻¹ * lam⁻¹ * (z - z')) • g := by
            rw [smul_smul, mul_inv]

end Frost
end AbstractCryptography

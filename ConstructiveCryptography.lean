/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import AbstractCryptography
import AbstractCryptography.SemanticRegistry
import ConstructiveCryptography.Generalizations.ContextRestricted
import ConstructiveCryptography.Multiparty.Basic

/-!
# Constructive Cryptography

The selected, choice-free constructive-cryptography specialization of the
public Abstract Cryptography API. This module is both the public import root
and the root of the modules under `ConstructiveCryptography/`; it contains the
implementation itself.

Two modules live under the directory root:

* `ConstructiveCryptography.Generalizations.ContextRestricted` — Jost's thesis
  §4.2, context-restricted constructions.
* `ConstructiveCryptography.Multiparty.Basic` — the multiparty layer owned by
  the `ConstructiveCryptographyMultipartyComputation` Lake target and imported
  by `ConstructiveCryptography.MultipartyComputation`.

## History

Two earlier trees have been removed from this root.

* The vendored `ResourceTheory` subtree (the `Signature`/`ResourceAlgebra`
  `⊗`-carrier and its examples) was deleted 2026-07-18. Its sponge functional
  core and indifferentiability statement were ported to `Applications/Sponge.lean`,
  and its distinguisher-class metric derivation to
  `AbstractCryptography/Metric/Distinguisher.lean`.
* The bundled `CCAlgebra` rendering — `AbstractCryptography.Algebra.Bundled`,
  `.Composition`, `.Bridge`, `.SpecBridge`, and
  `ConstructiveCryptography.Multiparty.TwoParty` — was deleted 2026-08-13. It was a
  closed loop reached only from this root and the `AbstractCryptography` root, its
  `NNReal`-valued distance could not express `⊤`, and `Algebra.SpecBridge`
  imported `ConstructiveCryptography.Multiparty.TwoParty`, making the abstract layer
  depend on the CC layer. See `SALVAGE.md` at the repository root for the two
  pieces worth re-deriving on the unbundled foundation and for the commit and
  paths that hold them.

The separate `Rendering` proof-widget library is not part of this tree.
-/

namespace ConstructiveCryptography

open AbstractCryptography

universe u v w

variable {I : Type u} {Γ : I → Type v} {Φ : Type w}
variable [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
variable [PseudoEMetricSpace Φ]

open Classical in
/-- Maurer11 Section 5.1, Definition 3: a protocol securely constructs `S`
from `R` within `ε` when both availability and security hold.

`Z` is the one fixed set of dishonest interfaces. `protocol` is attached at
the honest interfaces `Zᶜ`, while the special `bottom` converter is attached at
`Z` for availability. The security clause supplies one simulator from the
already assembled adversary-side tuple monoid `simulators`:

* availability compares `protocol (bottom R)` with `bottom S`;
* security compares `protocol R` with `simulator S` for some admitted
  simulator.

For the paper's Alice--Bob--Eve presentation, take `Z = {E}`, put the two
protocol converters at `A` and `B`, and choose `simulators` to contain the
tuples supported at `E`. The general interface type is intentional, but this
remains the basic fixed-`Z` CC definition: it does not enumerate corruption
patterns or state MauRen11 Theorem 2. Equality on `Φ` is already behavioral
equality, and `ENNReal` is the selected pseudo-emetric error codomain. -/
@[crypto_rule "cc.securely_constructs" cc_construction constructive_crypto]
def SecurelyConstructs
    (Z : Set I) (simulators : Submonoid (∀ i, Γ i))
    (protocol bottom : ∀ i, Γ i) (ε : ENNReal) (R S : Φ) : Prop :=
  edist
      (patternAttach Zᶜ protocol • (patternAttach Z bottom • R))
      (patternAttach Z bottom • S) ≤ ε ∧
    ∃ simulator ∈ simulators,
      edist (patternAttach Zᶜ protocol • R) (simulator • S) ≤ ε

open Classical in
/-- The availability clause as a selected MauRen16 Definition 1 construction.
The multiplication label makes the nested action in Maurer11 Definition 3
explicit: `bottom` acts first, followed by the honest protocol. -/
theorem SecurelyConstructs.availability_constructs
    {Z : Set I} {simulators : Submonoid (∀ i, Γ i)}
    {protocol bottom : ∀ i, Γ i} {ε : ENNReal} {R S : Φ}
    (h : SecurelyConstructs Z simulators protocol bottom ε R S) :
    Constructs (patternAttach Zᶜ protocol * patternAttach Z bottom)
      ({R} : Set Φ)
      (Relaxation.epsilonRelaxation ε ({patternAttach Z bottom • S} : Set Φ)) := by
  apply constructs_singleton_epsilonRelaxation_iff.mpr
  simpa only [mul_smul] using h.1

open Classical in
/-- The security clause as the selected simulator-to-construction theorem.
The simulator is absorbed into the `star`-relaxed ideal specification rather
than becoming part of the construction relation itself. -/
theorem SecurelyConstructs.security_constructs
    {Z : Set I} {simulators : Submonoid (∀ i, Γ i)}
    {protocol bottom : ∀ i, Γ i} {ε : ENNReal} {R S : Φ}
    (h : SecurelyConstructs Z simulators protocol bottom ε R S) :
    Constructs (patternAttach Zᶜ protocol) ({R} : Set Φ)
      (Relaxation.epsilonRelaxation ε ((Relaxation.star simulators) {S})) := by
  obtain ⟨simulator, hsimulator, hsecurity⟩ := h.2
  ac_simulator simulator
  · exact hsimulator
  · exact hsecurity

open Classical in
/-- Maurer11 Theorem 1(i): selected secure constructions compose serially.

The right factor acts first, so the protocols compose as
`protocol' * protocol`. The simulator produced by the first construction is
outermost on the ideal side and therefore composes as
`simulator * simulator'`, the opposite written order highlighted in the
paper's footnote 15. The explicit commutation premise is exactly the part of
the paper's honest/adversarial interface disjointness used by the proof. -/
@[crypto_rule "cc.securely_constructs.serial" cc_construction constructive_crypto]
theorem SecurelyConstructs.trans [IsNonexpandingSMul (∀ i, Γ i) Φ]
    {Z : Set I} {simulators : Submonoid (∀ i, Γ i)}
    {protocol protocol' bottom : ∀ i, Γ i}
    {ε ε' : ENNReal} {R S T : Φ}
    (hRS : SecurelyConstructs Z simulators protocol bottom ε R S)
    (hST : SecurelyConstructs Z simulators protocol' bottom ε' S T)
    (hcomm : ∀ simulator ∈ simulators,
      Commute (patternAttach Zᶜ protocol') simulator) :
    SecurelyConstructs Z simulators (protocol' * protocol) bottom
      (ε + ε') R T := by
  rcases hRS with ⟨havailable, simulator, hsimulator, hsecurity⟩
  rcases hST with ⟨havailable', simulator', hsimulator', hsecurity'⟩
  constructor
  · rw [patternAttach_mul]
    apply le_trans (edist_triangle _ (patternAttach Zᶜ protocol' •
      (patternAttach Z bottom • S)) _)
    apply add_le_add
    · have h := le_trans
        (edist_smul_le (patternAttach Zᶜ protocol')
          (patternAttach Zᶜ protocol • (patternAttach Z bottom • R))
          (patternAttach Z bottom • S)) havailable
      simpa only [mul_smul] using h
    · exact havailable'
  · refine ⟨simulator * simulator', mul_mem hsimulator hsimulator', ?_⟩
    rw [patternAttach_mul]
    apply le_trans (edist_triangle _
      (simulator • (patternAttach Zᶜ protocol' • S)) _)
    apply add_le_add
    · have h := le_trans
        (edist_smul_le (patternAttach Zᶜ protocol')
          (patternAttach Zᶜ protocol • R) (simulator • S)) hsecurity
      have heq : patternAttach Zᶜ protocol' • (simulator • S) =
          simulator • (patternAttach Zᶜ protocol' • S) := by
        rw [← mul_smul, (hcomm simulator hsimulator).eq, mul_smul]
      rw [heq] at h
      simpa only [mul_smul] using h
    · have h := le_trans
        (edist_smul_le simulator
          (patternAttach Zᶜ protocol' • S) (simulator' • T)) hsecurity'
      simpa only [mul_smul] using h

open Classical in
/-- Maurer11 Theorem 1(iii): the neutral protocol securely constructs every
resource from itself with zero error. The neutral element of `simulators` is
the security witness. -/
@[crypto_rule "cc.securely_constructs.identity" cc_construction constructive_crypto]
theorem SecurelyConstructs.refl
    (Z : Set I) (simulators : Submonoid (∀ i, Γ i))
    (bottom : ∀ i, Γ i) (R : Φ) :
    SecurelyConstructs Z simulators 1 bottom 0 R R := by
  constructor
  · simp [patternAttach_one]
  · exact ⟨1, one_mem simulators, by simp [patternAttach_one]⟩

open Classical in
/-- Maurer11 Theorem 1(ii): selected secure constructions compose in
parallel, with additive error.

The two action-level hypotheses state exactly how the componentwise parallel
protocol and the bottom filter act on a displayed parallel resource. They are
kept explicit because the abstract `Par` classes do not postulate
`1 ∥ 1 = 1`, and MauRen11 footnote 23 does not license that stronger law.
The remaining premise says that the admitted simulator class contains the
componentwise parallel simulator used by the proof. -/
@[crypto_rule "cc.securely_constructs.parallel" cc_construction constructive_crypto]
theorem SecurelyConstructs.par
    [Par (∀ i, Γ i)] [Par Φ] [SMulParClass (∀ i, Γ i) Φ]
    [IsNonexpandingPar Φ]
    {Z : Set I} {simulators : Submonoid (∀ i, Γ i)}
    {protocol protocol' bottom : ∀ i, Γ i}
    {ε ε' : ENNReal} {R S R' S' : Φ}
    (hprotocol : ∀ X Y : Φ,
      patternAttach Zᶜ (Par.par protocol protocol') • Par.par X Y =
        Par.par (patternAttach Zᶜ protocol • X)
          (patternAttach Zᶜ protocol' • Y))
    (hbottom : ∀ X Y : Φ,
      patternAttach Z bottom • Par.par X Y =
        Par.par (patternAttach Z bottom • X)
          (patternAttach Z bottom • Y))
    (hsimulators : ∀ simulator ∈ simulators,
      ∀ simulator' ∈ simulators,
        Par.par simulator simulator' ∈ simulators)
    (hRS : SecurelyConstructs Z simulators protocol bottom ε R S)
    (hR'S' : SecurelyConstructs Z simulators protocol' bottom ε' R' S') :
    SecurelyConstructs Z simulators (Par.par protocol protocol') bottom
      (ε + ε') (Par.par R R') (Par.par S S') := by
  rcases hRS with ⟨havailable, simulator, hsimulator, hsecurity⟩
  rcases hR'S' with ⟨havailable', simulator', hsimulator', hsecurity'⟩
  constructor
  · rw [hbottom R R', hprotocol, hbottom S S']
    exact (edist_par_par_le _ _ _ _).trans
      (add_le_add havailable havailable')
  · refine ⟨Par.par simulator simulator',
      hsimulators simulator hsimulator simulator' hsimulator', ?_⟩
    rw [hprotocol, smul_par]
    exact (edist_par_par_le _ _ _ _).trans
      (add_le_add hsecurity hsecurity')

open Classical in
/-- A secure construction remains valid with an unchanged resource in the
right parallel context, the consequence stated after Maurer11 Theorem 1.

Only the action law for the displayed extension `protocol ∥ 1` and one-sided
simulator closure are required; no equality identifying `α ∥ 1` with `α` is
assumed. -/
@[crypto_rule "cc.securely_constructs.context" cc_construction constructive_crypto]
theorem SecurelyConstructs.par_left
    [Par (∀ i, Γ i)] [Par Φ] [SMulParClass (∀ i, Γ i) Φ]
    [IsNonexpandingPar Φ]
    {Z : Set I} {simulators : Submonoid (∀ i, Γ i)}
    {protocol bottom : ∀ i, Γ i} {ε : ENNReal} {R S : Φ}
    (hprotocol : ∀ X Y : Φ,
      patternAttach Zᶜ (Par.par protocol 1) • Par.par X Y =
        Par.par (patternAttach Zᶜ protocol • X) Y)
    (hbottom : ∀ X Y : Φ,
      patternAttach Z bottom • Par.par X Y =
        Par.par (patternAttach Z bottom • X)
          (patternAttach Z bottom • Y))
    (hsimulators : ∀ simulator ∈ simulators,
      Par.par simulator 1 ∈ simulators)
    (hRS : SecurelyConstructs Z simulators protocol bottom ε R S)
    (T : Φ) :
    SecurelyConstructs Z simulators (Par.par protocol 1) bottom ε
      (Par.par R T) (Par.par S T) := by
  rcases hRS with ⟨havailable, simulator, hsimulator, hsecurity⟩
  constructor
  · rw [hbottom R T, hprotocol, hbottom S T]
    exact (edist_par_left_le _ _ _).trans havailable
  · refine ⟨Par.par simulator 1, hsimulators simulator hsimulator, ?_⟩
    rw [hprotocol, smul_par, one_smul]
    exact (edist_par_left_le _ _ _).trans hsecurity

end ConstructiveCryptography

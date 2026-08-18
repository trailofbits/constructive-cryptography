/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import ConstructiveCryptography.MultipartyComputation

/-!
# FROST as a two-stage construction (M4)

The first Constructive-Cryptography treatment of threshold signatures
(none exists in the literature to mid-2026; `MPC_TSS_PLAN.md`), stated
**carrier-free** on the abstract cryptographic algebra — `Φ` any resource
set, converters the tuple monoid `∀ i, Γ i`, `tupleGamma` the
per-interface classes.  Everything below is LiuMau20 §2's calculus (the
`∗Z`-relaxation, per-`Z` construction, game specification) instantiated at
the tuple carrier; the carrier (random systems) enters only to discharge
the named leaves.

## The composition

A broadcast channel and authenticated channels are **assumed** — the
assumption level of RFC 9591 / Komlo–Goldberg / BCKMTZ22 — and bundled with
the network, random oracle, and per-party coins into one assumed resource
`ASSUMED = [NET, BC, RO, COIN]`.  Constructing broadcast is out of scope, so
LiuMau20's `Q³` regime plays no role and a dishonest majority is tolerated.

The construction is then a **two-rung ladder**, each rung a per-`Z`
construction into the `∗Z`-relaxed next ideal:

```
Rung C (DKG):      ASSUMED     —[π_dkg ; ε_dkg]→  KEYS^{∗Z}
Rung D (signing):  KEYS^{∗Z}   —[π_sign ; ε_sign]→ TSS^{∗Z}
─────────────────────────────────────────────────────────  compose
End-to-end:        ASSUMED     —[π_sign·π_dkg ; ε_dkg+ε_sign]→ TSS^{∗Z}
```

for every tolerated dishonest set `Z` (`|Z| ≤ t`, the threshold adversary
structure).  Composition is `Constructs.trans` (exact) / `.epsilonRelaxation_trans`
(the errors add); the constructor label multiplies in function-composition
order, `π_sign · π_dkg` = "π_dkg then π_sign".  Alongside the construction,
the ideal `TSS`'s unforgeability **game bound `ε_game` transfers to the real
constructed system** (`gameSpec_of_edistD_le`), so the real system meets
`ε_game + (ε_dkg + ε_sign)`.

**What is proved here** is the construction *calculus*: the two rungs
compose to the end-to-end statement and the game bound transfers.  **The
leaves** the carrier discharges are the two per-`Z` simulators (DKG:
RO-programming, statistical; signing: nonce simulation, statistical —
CGRS23) and the ideal's unforgeability game bound.  That game bound is the
CC-native game relaxation (CR18 Def 5.10, sound via the random-systems
repo's Thm 4.17), discharged by a reduction to OMDL/AOMDL *in the carrier*
(BCKMTZ22 static; CGRS23 for DKG+FROST3), with OMDL a bounded-advantage
assumption there.  (UC4Free's game ⟺ **UC** equivalence is corroboration
in a different framework, not the license — see `Multiparty.gameSpec`.)
The deterministic cores are the `Frost.*` identities
(`verify_aggregate`, `feldmanCheck_dealShare`, `dkg_reconstruct`).

The generic `∗Z`/adversary-structure calculus is in
`ConstructiveCryptography.Multiparty.Basic` (`mpc_step`, `zStar_subset_gameSpec`,
`tupleGamma`); the four statements below are what is specific to FROST's
two-stage shape.
-/

open scoped ENNReal
open Pointwise

namespace AbstractCryptography

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}
  [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

/-- **Stage 1 — FROST signing from the ideal threshold keys**: per-`Z`
simulator leaves over the (relaxed) `KEYS` specification give the
construction of the gate-`γ` ideal TSS.  The leaf's deterministic core is
`Frost.verify_aggregate`; its probabilistic content (nonce simulation, RO
programming) is the carrier's. -/
theorem frost_sign_from_keys (𝒵 : AdversaryStructure I)
    (πsign : ∀ i, Γ i) (KEYSspec : Set I → Set Φ) (TSS : Φ)
    (hleaf : ∀ Z ∈ 𝒵.sets, ∀ R ∈ KEYSspec Z, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      patternAttach Zᶜ πsign • R = s • TSS) :
    ConstructsForAdversaryStructure 𝒵 πsign KEYSspec
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS}) :=
  mpc_step 𝒵 πsign KEYSspec TSS
    (fun Z _ => (zStar (Sigma := ∀ j, Γ j) tupleGamma Z).le_toFun (KEYSspec Z)) hleaf

/-- **Stage 2 — the de-idealized DKG**: per-`Z` simulator leaves over the
assumed `[NET, BC, RO]` specification construct the (relaxed) ideal
threshold keys — the `∗Z` absorbing the Pedersen key bias (GJKR) by
design.  The leaf's deterministic core is `Frost.feldmanCheck_dealShare` +
`Frost.dkg_reconstruct`. -/
theorem frost_dkg_to_keys (𝒵 : AdversaryStructure I)
    (πdkg : ∀ i, Γ i) (NETspec : Set I → Set Φ) (KEYS : Φ)
    (hleaf : ∀ Z ∈ 𝒵.sets, ∀ R ∈ NETspec Z, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      patternAttach Zᶜ πdkg • R = s • KEYS) :
    ConstructsForAdversaryStructure 𝒵 πdkg NETspec
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS}) :=
  mpc_step 𝒵 πdkg NETspec KEYS
    (fun Z _ => (zStar (Sigma := ∀ j, Γ j) tupleGamma Z).le_toFun (NETspec Z)) hleaf

/-- **The FROST statement shape** (M4's deliverable): over an adversary
structure, the DKG step and the signing step compose to the construction of
the `∗Z`-relaxed ideal TSS from the assumed specification, and — via
`Z`-closed unforgeability tests and the ideal's game bound (the CC game
relaxation, discharged by a carrier reduction to OMDL) — the real
constructed system satisfies the per-`Z` unforgeability bounds.  The four
hypotheses are the leaves the carrier discharges; everything else is
calculus. -/
theorem frost_statement (𝒵 : AdversaryStructure I)
    (assumed DKGspec : Set I → Set Φ) (TSS : Φ)
    (πdkg πsign : ∀ i, Γ i)
    (Ts : Set I → Set (Φ → ℝ≥0∞)) (ε : ℝ≥0∞)
    (hdkg : ConstructsForAdversaryStructure 𝒵 πdkg assumed DKGspec)
    (hsign : ConstructsForAdversaryStructure 𝒵 πsign DKGspec
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS}))
    (hcl : ∀ Z ∈ 𝒵.sets, ZClosed (Sigma := ∀ j, Γ j) tupleGamma Z (Ts Z))
    (hunforg : ∀ Z ∈ 𝒵.sets, TSS ∈ gameSpec (Ts Z) ε) :
    ConstructsForAdversaryStructure 𝒵 (πsign * πdkg) assumed
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS})
    ∧ ∀ Z ∈ 𝒵.sets, ∀ R ∈ assumed Z,
        patternAttach Zᶜ (πsign * πdkg) • R ∈ gameSpec (Ts Z) ε := by
  have hcomp := hdkg.trans hsign
  refine ⟨hcomp, fun Z hZ R hR => ?_⟩
  have hmem := hcomp Z (Set.smul_mem_smul_set hR)
  simp only [if_pos hZ] at hmem
  exact zStar_subset_gameSpec tupleGamma (hcl Z hZ) (hunforg Z hZ) hmem

/-- **The FROST theorem, end-to-end**: from the two stages' simulator
leaves and the gated ideal's game bound, the composed protocol
`π_sign · π_dkg` constructs the `∗Z`-relaxed gated TSS from `[NET, BC, RO]`
alone, and the real constructed system satisfies the per-`Z`
unforgeability bounds — for every tolerated `Z`.  All remaining hypotheses
are the carrier's named leaves. -/
theorem frost_end_to_end (𝒵 : AdversaryStructure I)
    (πdkg πsign : ∀ i, Γ i)
    (NETspec : Set I → Set Φ) (KEYS TSS : Φ)
    (Ts : Set I → Set (Φ → ℝ≥0∞)) (ε : ℝ≥0∞)
    (hdkg : ∀ Z ∈ 𝒵.sets, ∀ R ∈ NETspec Z, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      patternAttach Zᶜ πdkg • R = s • KEYS)
    (hsign : ∀ Z ∈ 𝒵.sets, ∀ R ∈ zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS},
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ πsign • R = s • TSS)
    (hcl : ∀ Z ∈ 𝒵.sets, ZClosed (Sigma := ∀ j, Γ j) tupleGamma Z (Ts Z))
    (hunforg : ∀ Z ∈ 𝒵.sets, TSS ∈ gameSpec (Ts Z) ε) :
    ConstructsForAdversaryStructure 𝒵 (πsign * πdkg) NETspec
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS})
    ∧ ∀ Z ∈ 𝒵.sets, ∀ R ∈ NETspec Z,
        patternAttach Zᶜ (πsign * πdkg) • R ∈ gameSpec (Ts Z) ε :=
  frost_statement 𝒵 NETspec (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS}) TSS
    πdkg πsign Ts ε
    (frost_dkg_to_keys 𝒵 πdkg NETspec KEYS hdkg)
    (frost_sign_from_keys 𝒵 πsign
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS}) TSS hsign)
    hcl hunforg

/-- **Non-vacuity of `frost_end_to_end`**: its premises are simultaneously
satisfiable, so the statement is not true-by-empty-hypothesis.  The
degenerate witness — identity protocols, assumed spec already the
`∗Z`-relaxed keys, `TSS := KEYS`, empty forgery family — meets both
simulator leaves (`s' = s`, via `patternAttach_one`) and, over the empty
test family, the `ZClosed` and game-bound obligations vacuously, so the
theorem fires and yields an actual (degenerate) construction. -/
example (𝒵 : AdversaryStructure I) (KEYS : Φ) (ε : ℝ≥0∞) : True :=
  have _ := frost_end_to_end 𝒵 (1 : ∀ i, Γ i) 1
    (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS}) KEYS KEYS
    (fun _ => ∅) ε
    (fun _ _ R hR => by
      obtain ⟨s, hs, r, hr, rfl⟩ := hR
      obtain rfl : r = KEYS := hr
      exact ⟨s, hs, by rw [patternAttach_one, one_smul]⟩)
    (fun _ _ R hR => by
      obtain ⟨s, hs, r, hr, rfl⟩ := hR
      obtain rfl : r = KEYS := hr
      exact ⟨s, hs, by rw [patternAttach_one, one_smul]⟩)
    (fun _ _ t ht => absurd ht (Set.notMem_empty t))
    (fun _ _ t ht => absurd ht (Set.notMem_empty t))
  trivial

/-- **FROST at a threshold adversary structure** (the headline
instantiation): for `t < n/3`, from the two stages' simulator leaves and
the ideal's game bound, the composed protocol `π_sign · π_dkg` constructs
the `∗Z`-relaxed ideal TSS from `[NET, BC, RO]` for every set of at most `t`
dishonest parties, and the real constructed system meets the per-`Z`
unforgeability bound.  The forgery family is built by dishonest-side
closure (`dishonestClosure`), so its `Z`-closure is **automatic** — the
`ZClosed` obligation is discharged here, not assumed.  `3*t < n` moreover
yields `Q³` (surfaced as the first conjunct), the regime the carrier's
simulator leaves need. -/
theorem frost_threshold {n t : ℕ} {Γ : Fin n → Type*} {Φ : Type*}
    [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
    (ht : 3 * t < n) (πdkg πsign : ∀ i, Γ i)
    (NETspec : Set (Fin n) → Set Φ) (KEYS TSS : Φ)
    (T0 : Set (Fin n) → Set (Φ → ℝ≥0∞)) (ε : ℝ≥0∞)
    (hdkg : ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ NETspec Z,
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ πdkg • R = s • KEYS)
    (hsign : ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
      ∀ R ∈ zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS},
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ πsign • R = s • TSS)
    (hunforg : ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
      TSS ∈ gameSpec (dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε) :
    (AdversaryStructure.threshold n t).Q3
    ∧ ConstructsForAdversaryStructure (AdversaryStructure.threshold n t)
        (πsign * πdkg) NETspec (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS})
    ∧ ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ NETspec Z,
        patternAttach Zᶜ (πsign * πdkg) • R
          ∈ gameSpec (dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε :=
  ⟨AdversaryStructure.threshold_Q3 ht,
   frost_end_to_end (AdversaryStructure.threshold n t) πdkg πsign NETspec KEYS TSS
     (fun Z => dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε
     hdkg hsign
     (fun Z _ => zClosed_dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma (T0 Z))
     hunforg⟩

/-- **FROST unforgeability needs no honest majority**: the same statement
as `frost_threshold` with the `3*t < n` hypothesis and its `Q³` conjunct
removed.  The `[NET, BC, RO]` resources are *assumed* here, so LiuMau20's
`Q³` regime — needed when broadcast must itself be constructed from
pairwise channels — plays no role: FROST's own security analyses
(BCKMTZ22; CGRS23) are static-corruption `t`-out-of-`n` statements
tolerating any dishonest set of size `≤ t`, including a dishonest
majority.  For a signing quorum of size `τ`, instantiate `t := τ - 1`.
`frost_threshold` remains the endpoint to compose with a future broadcast
de-idealization, where its `Q³` conjunct is the needed regime. -/
theorem frost_threshold_unforgeability {n t : ℕ} {Γ : Fin n → Type*} {Φ : Type*}
    [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
    (πdkg πsign : ∀ i, Γ i)
    (NETspec : Set (Fin n) → Set Φ) (KEYS TSS : Φ)
    (T0 : Set (Fin n) → Set (Φ → ℝ≥0∞)) (ε : ℝ≥0∞)
    (hdkg : ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ NETspec Z,
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ πdkg • R = s • KEYS)
    (hsign : ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
      ∀ R ∈ zStar (Sigma := ∀ j, Γ j) tupleGamma Z {KEYS},
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ πsign • R = s • TSS)
    (hunforg : ∀ Z ∈ (AdversaryStructure.threshold n t).sets,
      TSS ∈ gameSpec (dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε) :
    ConstructsForAdversaryStructure (AdversaryStructure.threshold n t)
      (πsign * πdkg) NETspec (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {TSS})
    ∧ ∀ Z ∈ (AdversaryStructure.threshold n t).sets, ∀ R ∈ NETspec Z,
        patternAttach Zᶜ (πsign * πdkg) • R
          ∈ gameSpec (dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε :=
  frost_end_to_end (AdversaryStructure.threshold n t) πdkg πsign NETspec KEYS TSS
    (fun Z => dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma Z (T0 Z)) ε
    hdkg hsign
    (fun Z _ => zClosed_dishonestClosure (Sigma := ∀ j, Γ j) tupleGamma (T0 Z))
    hunforg
/-! ### The ε-relaxed end-to-end theorem

`frost_end_to_end_eps` — the two stages' simulators only `edist ≤ ε`-close,
with the game bound picking up the simulation slack — is stated over an
`AbstractCryptography.DistinguisherClass`, MauRen11 Definition 15/16
provenance, and therefore moved to `Applications.Frost.ConstructionEps`
behind the provenance fence on 2026-08-17.  See `LEDGER.md` PROVENANCE
FENCE. -/

end AbstractCryptography

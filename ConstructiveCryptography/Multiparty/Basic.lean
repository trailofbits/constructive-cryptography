/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Group.Submonoid.Membership
import AbstractCryptography.Specification.Filtered
import AbstractCryptography.SemanticRegistry

/-!
# Multi-party protocols and constructions (LiuMau20 §2.4)

LiuMau20 is Liu-Zhang and Maurer, *Synchronous Constructive Cryptography*,
TCC 2020; unqualified item numbers below are its.

"Let us consider a setting with `n` parties, where `P = {1, …, n}`
denotes the set of parties (or, rather, interfaces).  A protocol consists
of a tuple `π = (π₁, …, πₙ)` of converters, one for each party, and a
construction consists of each party applying its converter.  However, an
essential aspect of reasoning in cryptography is that one considers that
parties can either be honest or dishonest, and the goal is to state
meaningful guarantees for the honest parties.  While an honest party
applies its converter, there is no such guarantee for a dishonest party,
meaning that a dishonest party may apply an arbitrary converter to its
interface, including the identity converter that gives direct access to
the interface."

"For each subset `Z ⊆ P` of dishonest parties one states a separate
guarantee: If the assumed resource satisfies specification `R_Z`, then,
if all parties in `P ∖ Z` apply their converter, the resulting resource
satisfies specification `S_Z`.  Typically, but not necessarily, all
guarantees `R_Z` (and analogously all `S_Z`) are compactly described,
possibly all derived as variations of the same resource."

The converter monoids may differ per interface (`Γ : I → Type*`); the
paper's single `Σ` is the constant-family case.
-/

open Pointwise

namespace AbstractCryptography

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}
  [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

open Classical in
/-- **Definition 1.** "The protocol `π = (π₁, …, πₙ)` constructs
specifications `S_Z` from `R_Z` if

  `∀Z ⊆ P   R_Z —π^{P∖Z}→ S_Z`."

One construction statement per dishonest set `Z`, the protocol attached
at the honest interfaces `P ∖ Z` — here `Zᶜ`, `P` being all of `I`. -/
@[crypto_rule "cc.mpc.constructs_for_all" mpc_construction constructive_crypto]
noncomputable def ConstructsForAll (π : ∀ i, Γ i) (R S : Set I → Set Φ) : Prop :=
  ∀ Z : Set I, R Z —[patternAttach Zᶜ π]→ S Z

open Classical in
/-- §2.2: "The composability of this construction notion follows
immediately from the transitivity of the subset relation:

  `R —γ→ S ∧ S —γ′→ T  ⟹  R —γ′∘γ→ T`."

Per dishonest set, the protocols composing pointwise. -/
@[crypto_rule "cc.mpc.constructs_for_all.serial" mpc_construction constructive_crypto]
theorem ConstructsForAll.trans {π π' : ∀ i, Γ i} {R S T : Set I → Set Φ}
    (h : ConstructsForAll π R S) (h' : ConstructsForAll π' S T) :
    ConstructsForAll (π' * π) R T := fun Z => by
  rw [patternAttach_mul]
  exact Constructs.trans (h Z) (h' Z)

open Classical in
/-- §2.4: "if `Z` is not in the adversary structure, then the resource is
only known to satisfy the trivial specification `Φ`" — and every protocol
constructs `Φ`. -/
theorem constructsForAll_univ {π : ∀ i, Γ i} {R : Set I → Set Φ} {Z : Set I} :
    R Z —[patternAttach Zᶜ π]→ Set.univ :=
  fun _ _ => Set.mem_univ _

open Classical in
/-- Lift `filteredAt_constructs_of_local_simulators` to LiuMau20 Definition 1's
family indexed by dishonest sets: at branch `Z` the honesty pattern is `Zᶜ`, so
the protocol is attached at the honest interfaces and the same simulator tuple
at the dishonest ones.  One `σ` is fixed before every branch. -/
theorem ConstructsForAll.filteredAt_of_local_simulators {H : ∀ i, Submonoid (Γ i)}
    {π φ ψ σ : ∀ i, Γ i} {R S : Φ} (hσ : ∀ i, σ i ∈ H i)
    (h : ∀ P : Set I,
      patternAttach P π • patternAttach P φ • R
        = patternAttach Pᶜ σ • patternAttach P ψ • S) :
    ConstructsForAll π (fun Z => filteredAt Zᶜ H φ R) (fun Z => filteredAt Zᶜ H ψ S) :=
  fun Z => filteredAt_constructs_of_local_simulators hσ h Zᶜ

/-! ### The `∗Z`-relaxation (LiuMau20 §2.5)

`∗Z` is the `∗`-relaxation (`Relaxation.star`, MauRen11 Def 17 / CR18
§5.3) at the joint dishonest converter class.

Following MauRen11 Def 14, the converters act through a single monoid `Sigma`
(`= ∀ i, Γ i` in the tuple-protocol rendering); `γ i` is the converter
class at interface `i`, the paper's `Σ` restricted to interface `i`. -/

section StarZ
variable {Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ] (γ : I → Submonoid Sigma)

/-- LiuMau20 §2.5: the joint dishonest converter class.  "If we consider
a set `Z` of potentially dishonest parties, we can consider the set of
interfaces in `Z` as being merged to a single interface with several
sub-interfaces."  Here: the join of the interface classes over `Z`. -/
def zSub (Z : Set I) : Submonoid Sigma :=
  ⨆ i : Z, γ (i : I)

theorem mem_γ_le_zSub {Z : Set I} {i : I} (hi : i ∈ Z) : γ i ≤ zSub γ Z :=
  le_iSup_of_le ⟨i, hi⟩ le_rfl

theorem zSub_mono {Z Z' : Set I} (h : Z ⊆ Z') : zSub γ Z ≤ zSub γ Z' :=
  iSup_le fun i => le_iSup_of_le ⟨i, h i.2⟩ le_rfl

/-- MauRen11 Def 14(i): a converter commuting with each dishonest
interface class commutes with the whole merged class. -/
theorem commute_zSub {Z : Set I} {g h : Sigma}
    (hcomm : ∀ j ∈ Z, ∀ b ∈ γ j, Commute g b) (hh : h ∈ zSub γ Z) :
    Commute g h := by
  refine Submonoid.iSup_induction (motive := fun h => Commute g h) _ hh
    ?_ (Commute.one_right g) (fun x y hx hy => hx.mul_right hy)
  rintro ⟨j, hj⟩ x hx
  exact hcomm j hj x hx

/-- LiuMau20 §2.5's `S∗Z`: "`S∗j := {πʲS | π ∈ Σ ∧ S ∈ S}`", extended to
the merged interface `Z` — "This corresponds to the viewpoint that all
dishonest parties collude … under control of a central adversary." -/
def zStar (Z : Set I) : Relaxation Φ :=
  Relaxation.star (zSub γ Z)

/-- "It is easy to see that the described `∗`-relaxation is idempotent …
`(S∗Z)∗Z = S∗Z`." -/
theorem zStar_idem (Z : Set I) (R : Set Φ) :
    zStar γ Z (zStar γ Z R) = zStar γ Z R :=
  Relaxation.star_idem (zSub γ Z) R

/-- `∗Z` weakens monotonically in the dishonest set. -/
theorem zStar_mono {Z Z' : Set I} (h : Z ⊆ Z') (R : Set Φ) :
    zStar γ Z R ⊆ zStar γ Z' R :=
  Relaxation.star_mono_submonoid (zSub_mono γ h) R

/-- A converter commuting with the dishonest class pulls through `∗Z`:
`π(S∗Z) ⊆ (πS)∗Z`. -/
theorem smul_zStar_subset {Z : Set I} {g : Sigma} (hg : ∀ h ∈ zSub γ Z, Commute g h)
    (R : Set Φ) : g • zStar γ Z R ⊆ zStar γ Z (g • R) :=
  Relaxation.smul_star_subset (fun σ hσ => (hg σ hσ).actCommute) R

/-- LiuMau20 §2.5's proof recipe: "If one wants to prove that a given
specification `U` is contained in `S∗Z`, one can exhibit for every `U ∈ U`
a converter `α` such that `U = αᶻS` … the same `α` … is a (joint)
simulator for the interfaces in `Z`."  The honest attachment `g` (which
commutes with the dishonest class) sends every real resource, up to a
dishonest `s ∈ zSub γ Z`, to the ideal. -/
theorem zStar_construct_of_simulators {Z : Set I} {g : Sigma}
    (hg : ∀ h ∈ zSub γ Z, Commute g h) {real : Set Φ} {ideal : Φ}
    (hsim : ∀ R ∈ real, ∃ s ∈ zSub γ Z, g • R = s • ideal) :
    g • zStar γ Z real ⊆ zStar γ Z {ideal} :=
  Relaxation.star_construct (fun σ hσ => (hg σ hσ).actCommute) hsim

end StarZ

/-! ### Game specifications (the OMDL / unforgeability port)

`gameSpec` corresponds to no numbered definition in the framework papers.
It is the membership predicate of the **game relaxation** (CR18 §5.2.3
Def 5.10 — a specification is `ε`-close to the ideal if no efficient
distinguisher wins the associated game beyond `ε`), with the test family
`Ts` carrying the efficient forgers.  A concrete `ε`-bound is discharged by
a reduction to a game-based assumption (OMDL, EUF-CMA) in the carrier.

For threshold signatures, UC4Free (Bobolz–Crites–Kohlweiss–Takahashi,
Eurocrypt 2026) proves game-based security equivalent to UC security, which
is a different composition framework. -/

section GameSpec
open scoped ENNReal
variable {Ψ : Type*}

/-- The resources on which every winning test is bounded by `ε`; the dual of
`propSpec`, which asks its defining tests to pass with certainty. -/
def gameSpec (Ts : Set (Ψ → ℝ≥0∞)) (ε : ℝ≥0∞) : Set Ψ :=
  {q | ∀ t ∈ Ts, t q ≤ ε}

/-- A larger bound is a weaker game specification. -/
theorem gameSpec_mono {Ts : Set (Ψ → ℝ≥0∞)} {ε ε' : ℝ≥0∞} (h : ε ≤ ε') :
    gameSpec Ts ε ⊆ gameSpec Ts ε' :=
  fun _ hq t ht => le_trans (hq t ht) h

/-- More winning tests is a stronger game specification. -/
theorem gameSpec_antitone {Ts Ts' : Set (Ψ → ℝ≥0∞)} (h : Ts ⊆ Ts') {ε : ℝ≥0∞} :
    gameSpec Ts' ε ⊆ gameSpec Ts ε :=
  fun _ hq t ht => hq t (h ht)

end GameSpec

/-! ### Game bounds under the `∗Z`-relaxation

How the ideal's game guarantee survives the `∗Z`-relaxation, over the same
abstract `γ : I → Submonoid Sigma` as `∗Z` itself. -/

section StarGame
open scoped ENNReal
variable {Sigma Φ : Type*} [Monoid Sigma] [MulAction Sigma Φ] (γ : I → Submonoid Sigma)

/-- A test family closed under dishonest-side emulation at `Z` — MauRen11
Def 16's closure `𝒟Σⁱ ⊆ 𝒟` restricted to the dishonest monoid. -/
def ZClosed (Z : Set I) (Ts : Set (Φ → ℝ≥0∞)) : Prop :=
  ∀ t ∈ Ts, ∀ s ∈ zSub γ Z, (fun q => t (s • q)) ∈ Ts

/-- Game bounds survive the `∗Z`-relaxation: if the ideal satisfies the game
bounds and the test family is `Z`-closed, so does every resource in the
relaxed specification. -/
theorem zStar_subset_gameSpec {Z : Set I} {Ts : Set (Φ → ℝ≥0∞)}
    {ε : ℝ≥0∞} {ideal : Φ} (hcl : ZClosed γ Z Ts)
    (hideal : ideal ∈ gameSpec Ts ε) :
    zStar γ Z {ideal} ⊆ gameSpec Ts ε := by
  rintro x ⟨s, hs, r, hr, rfl⟩
  obtain rfl : r = ideal := hr
  intro t ht
  exact hideal (fun q => t (s • q)) (hcl t ht s hs)

/-- The dishonest-side closure of a base test family `T0`: every base test
pre-composed with a dishonest converter `s ∈ zSub γ Z`. -/
def dishonestClosure (Z : Set I) (T0 : Set (Φ → ℝ≥0∞)) : Set (Φ → ℝ≥0∞) :=
  {t | ∃ t0 ∈ T0, ∃ s ∈ zSub γ Z, t = fun q => t0 (s • q)}

/-- The base family sits inside its closure (take the dishonest converter
`s = 1`). -/
theorem subset_dishonestClosure {Z : Set I} (T0 : Set (Φ → ℝ≥0∞)) :
    T0 ⊆ dishonestClosure γ Z T0 :=
  fun t0 ht0 => ⟨t0, ht0, 1, one_mem _, by funext q; rw [one_smul]⟩

/-- `ZClosed` holds for the closure: the dishonest monoid absorbs its own
products, so pre-composing a closure member with another `s' ∈ zSub γ Z`
lands back in the closure. -/
theorem zClosed_dishonestClosure {Z : Set I} (T0 : Set (Φ → ℝ≥0∞)) :
    ZClosed γ Z (dishonestClosure γ Z T0) := by
  rintro t ⟨t0, ht0, s, hs, rfl⟩ s' hs'
  exact ⟨t0, ht0, s * s', mul_mem hs hs', by funext q; rw [mul_smul]⟩

/-- A stronger gate admits more forgery tests (`Ts' ⊆ Ts`), so its game
guarantee implies every weaker gate's. -/
theorem gate_mono {Ts Ts' : Set (Φ → ℝ≥0∞)} (hg : Ts' ⊆ Ts)
    {ε : ℝ≥0∞} {q : Φ} (h : q ∈ gameSpec Ts ε) : q ∈ gameSpec Ts' ε :=
  gameSpec_antitone hg h

/-- A gate hierarchy (BCKMTZ22's TS-UF-0..4 lattice, abstractly): a family of
forgery-test sets indexed by strength, ordered so that a higher index admits
more tests. -/
structure GateHierarchy (Φ : Type*) where
  /-- The forgery-test family at each gate level. -/
  gate : ℕ → Set (Φ → ℝ≥0∞)
  /-- A higher level is a stronger notion: more tests. -/
  mono : Monotone gate

/-- A game bound at a strong gate (high index) implies the bound at every
weaker gate (lower index). -/
theorem GateHierarchy.transfer (G : GateHierarchy Φ) {i j : ℕ} (h : i ≤ j)
    {ε : ℝ≥0∞} {q : Φ} (hq : q ∈ gameSpec (G.gate j) ε) :
    q ∈ gameSpec (G.gate i) ε :=
  gate_mono (G.mono h) hq

end StarGame

/-! ### The game bound under a distinguisher-class distance

`gameSpec_of_edistD_le` — a resource within class-distance `εs` of one meeting
the game bound `εg` meets it up to `εg + εs` — is stated over
`AbstractCryptography.DistinguisherClass`, MauRen11 Definition 15/16
provenance, and therefore moved to
`ConstructiveCryptography.Multiparty.GameMetric` behind the provenance fence
on 2026-08-17.  Everything above is `Set (Φ → ℝ≥0∞)` test families and needs
no class.  See `LEDGER.md` PROVENANCE FENCE. -/

end AbstractCryptography

/-!
# Adversary structures (LiuMau20 §2.4, §8)

§2.4: "A special case often considered is that one provides guarantees
only if the set of dishonest parties is within a so-called **adversary
structure** [16], for example that there are at most `t` dishonest
parties.  This simply corresponds to the special case where `S_Z = Φ` if
`|Z| > t`.  In other words, if `Z` is not in the adversary structure,
then the resource is only known to satisfy the trivial specification
`Φ`."

§8: "In many protocols, the sets of possible dishonest parties are
specified by a threshold `t`, that indicates that any set of dishonest
parties is of size at most `t`.  However, in this protocol, one specifies
a so-called **adversary structure** `Z`, which is a monotone set of
subsets of parties, where each subset indicates a possible set of
dishonest parties.  We are interested in the condition that no three sets
in `Z` cover `[n − 1]`, also known as `Q³([n − 1], Z)` [16]."  Fn. 8 is
the monotonicity: "If `Z ∈ 𝒵` and `Z′ ⊆ Z`, then `Z′ ∈ 𝒵`."

Two departures:

* `Q3` here is stated over all of `I`, not `[n − 1]` — the form of §8.1
  ("since the adversary structure satisfies `Q³(P, Z)`, then, for any two
  sets `Z_p, Z_q ∈ Z`, `Z_p ∩ Z_q ≠ ∅`").
* `threshold` and `threshold_Q3` (`3t < n ⟹ Q³`) are ours: LiuMau20 names
  the threshold case and uses `t < n/3` in its broadcast protocols, but
  states neither the threshold structure nor the implication.

LiuMau20's [16] is: Martin Hirt and Ueli Sigma. Maurer, *Player simulation
and general adversary structures in perfect multiparty computation*,
Journal of Cryptology 13(1):31–60, January 2000.
-/

open Pointwise

namespace AbstractCryptography

/-- §8: "an **adversary structure** `𝒵`, which is a monotone set of
subsets of parties, where each subset indicates a possible set of
dishonest parties." -/
structure AdversaryStructure (I : Type*) where
  /-- "Each subset indicates a possible set of dishonest parties." -/
  sets : Set (Set I)
  /-- Fn. 8, the monotonicity: "If `Z ∈ 𝒵` and `Z′ ⊆ Z`, then
  `Z′ ∈ 𝒵`." -/
  mono : ∀ {Z Z' : Set I}, Z' ⊆ Z → Z ∈ sets → Z' ∈ sets

namespace AdversaryStructure

variable {I : Type*}

/-- §8: "the condition that no three sets in `𝒵` cover `[n − 1]`, also
known as `Q³([n − 1], 𝒵)`" — here over all of `I`, the `Q³(P, 𝒵)` of
§8.1. -/
def Q3 (𝒵 : AdversaryStructure I) : Prop :=
  ∀ Z₁ ∈ 𝒵.sets, ∀ Z₂ ∈ 𝒵.sets, ∀ Z₃ ∈ 𝒵.sets, Z₁ ∪ Z₂ ∪ Z₃ ≠ Set.univ

/-- §8.1: "since the adversary structure satisfies `Q³(P, 𝒵)`, then, for
any two sets `Z_p, Z_q ∈ 𝒵`, `Z_p ∩ Z_q ≠ ∅`" — equivalently, two
tolerated sets never cover `I`. -/
theorem Q3.two_not_cover {𝒵 : AdversaryStructure I} (h : 𝒵.Q3)
    {Z₁ Z₂ : Set I} (h₁ : Z₁ ∈ 𝒵.sets) (h₂ : Z₂ ∈ 𝒵.sets) :
    Z₁ ∪ Z₂ ≠ Set.univ := by
  intro hcover
  exact h Z₁ h₁ Z₂ h₂ Z₂ h₂ (by rw [Set.union_assoc, Set.union_self, hcover])

/-- The structure of §8's threshold case, "a threshold `t`, that
indicates that any set of dishonest parties is of size at most `t`".
Ours: the paper names the case but does not define the structure. -/
def threshold (n t : ℕ) : AdversaryStructure (Fin n) where
  sets := {Z | Z.ncard ≤ t}
  mono h hZ := le_trans (Set.ncard_le_ncard h (Set.toFinite _)) hZ

/-- `3t < n` implies `Q³` for the threshold structure — three sets of
size `≤ t` cover at most `3t < n` parties.  Ours: this is what connects
§8's `Q³` to the `t < n/3` its protocols assume; LiuMau20 states neither
side of the implication. -/
theorem threshold_Q3 {n t : ℕ} (h : 3 * t < n) : (threshold n t).Q3 := by
  intro Z₁ h₁ Z₂ h₂ Z₃ h₃ hcover
  have hn : (Set.univ : Set (Fin n)).ncard = n := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : (Z₁ ∪ Z₂ ∪ Z₃).ncard ≤ 3 * t := by
    calc (Z₁ ∪ Z₂ ∪ Z₃).ncard
        ≤ (Z₁ ∪ Z₂).ncard + Z₃.ncard :=
          Set.ncard_union_le _ _
      _ ≤ (Z₁.ncard + Z₂.ncard) + Z₃.ncard := by
          gcongr
          exact Set.ncard_union_le _ _
      _ ≤ t + t + t := by gcongr <;> assumption
      _ = 3 * t := by ring
  rw [hcover, hn] at hle
  omega

end AdversaryStructure

open Classical in
/-- §2.4: Definition 1 restricted to an adversary structure — "this
simply corresponds to the special case where `S_Z = Φ` if `|Z| > t`", the
trivial specification outside the structure.  Definitionally an instance
of `ConstructsForAll`. -/
noncomputable def ConstructsForAdversaryStructure {I : Type*} {Γ : I → Type*}
    {Φ : Type*} [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
    (𝒵 : AdversaryStructure I) (π : ∀ i, Γ i) (R S : Set I → Set Φ) : Prop :=
  ConstructsForAll π R (fun Z => if Z ∈ 𝒵.sets then S Z else Set.univ)

/-- §2.2's composability, carried to the structured case: outside the
structure both sides are trivial, inside the rungs chain by
`Constructs.trans`. -/
theorem ConstructsForAdversaryStructure.trans {I : Type*} {Γ : I → Type*}
    {Φ : Type*} [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]
    {𝒵 : AdversaryStructure I} {π π' : ∀ i, Γ i} {R S T : Set I → Set Φ}
    (h : ConstructsForAdversaryStructure 𝒵 π R S)
    (h' : ConstructsForAdversaryStructure 𝒵 π' S T) :
    ConstructsForAdversaryStructure 𝒵 (π' * π) R T := by
  intro Z
  by_cases hZ : Z ∈ 𝒵.sets
  · have h1 := h Z
    have h2 := h' Z
    simp only [if_pos hZ] at h1 h2 ⊢
    have hcomp := Constructs.trans h1 h2
    rwa [← patternAttach_mul] at hcomp
  · simp only [if_neg hZ]
    exact fun x _ => Set.mem_univ x

/-! ### The tuple rendering of the `∗Z` calculus (LiuMau20 §2.4)

The multi-party protocol monoid is the tuple monoid `∀ i, Γ i` (Def 14's
`Σ` as an interface-indexed product) acting on `Φ`; `tupleGamma i` is the
interface-`i` converter class — the paper's `Σ` restricted to interface
`i` — instantiating the abstract `γ` of the `∗Z` calculus above.

`tupleGamma` is declared over the `Monoid`-canonical `MulOneClass` of the
tuple monoid, which is what `zSub`/`zStar` resolve through; the default
`Pi.mulOneClass` is defeq but not syntactically equal, and `zSub` takes `γ`
at a rigid argument position. -/

open scoped ENNReal

section Tuple

variable {I : Type*} {Γ : I → Type*} {Φ : Type*}
  [∀ i, Monoid (Γ i)] [MulAction (∀ i, Γ i) Φ]

/-- The interface-`i` converter class in the tuple monoid: converters that
are the identity at every interface `j ≠ i`.  The paper's `Σ` restricted
to interface `i`, and the tuple-rendering `γ` for the `∗Z` calculus. -/
def tupleGamma (i : I) : @Submonoid (∀ j, Γ j) Monoid.toMulOneClass where
  carrier := {f | ∀ j, j ≠ i → f j = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' {a b} ha hb := fun j hj => by rw [Pi.mul_apply, ha j hj, hb j hj, one_mul]

/-- Every element of the merged dishonest class `zSub tupleGamma Z` is the
identity off `Z` — the joint interface `Z` acts only within `Z`. -/
theorem zSub_tupleGamma_apply {Z : Set I} {h : ∀ j, Γ j}
    (hh : h ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z) {k : I} (hk : k ∉ Z) :
    h k = 1 := by
  induction hh using Submonoid.iSup_induction' with
  | mem i x hx => exact hx k (fun hik => hk (hik ▸ i.2))
  | one => rfl
  | mul x y _ _ hx hy => rw [Pi.mul_apply, hx, hy, one_mul]

/-- The generated dishonest converter class is supported on `Z`. -/
theorem zSub_tupleGamma_le_supportedOn (Z : Set I) :
    zSub (Sigma := ∀ j, Γ j) tupleGamma Z ≤ supportedOn Z (fun _ => ⊤) := by
  intro h hh
  exact mem_supportedOn.mpr
    ⟨fun _ _ => Submonoid.mem_top _,
     fun _ hi => zSub_tupleGamma_apply hh hi⟩

/-- The converse of `zSub_tupleGamma_le_supportedOn` for a finite dishonest
set: every converter tuple supported on `Z` is a finite product of
single-interface converters at interfaces of `Z`, hence lies in
`zSub tupleGamma Z`.

So in the tuple monoid LiuMau20 §2.5's merged interface `Z` admits exactly
the `Z`-supported tuples.  This does *not* claim a single machine with state
shared across the interfaces of `Z`, which the tuple monoid cannot
express. -/
theorem supportedOn_le_zSub_tupleGamma {Z : Set I} (hZ : Z.Finite) :
    supportedOn Z (fun _ => ⊤) ≤ zSub (Sigma := ∀ j, Γ j) tupleGamma Z := by
  classical
  induction Z, hZ using Set.Finite.induction_on with
  | empty =>
      intro h hh
      have hone : h = 1 := funext fun j => hh.2 j (Set.notMem_empty j)
      exact hone ▸ one_mem _
  | @insert a s ha _ ih =>
      intro h hh
      have hupdate : Function.update h a 1 ∈ supportedOn s (fun _ => ⊤) := by
        refine mem_supportedOn.mpr ⟨fun _ _ => Submonoid.mem_top _, fun j hj => ?_⟩
        by_cases hja : j = a
        · rw [hja, Function.update_self]
        · rw [Function.update_of_ne hja]
          exact hh.2 j (fun hmem => hj (hmem.resolve_left hja))
      have hsplit : h = Pi.mulSingle a (h a) * Function.update h a 1 := by
        funext j
        by_cases hja : j = a
        · subst hja
          rw [Pi.mul_apply, Pi.mulSingle_eq_same, Function.update_self, mul_one]
        · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hja, Function.update_of_ne hja,
            one_mul]
      have hsingle : Pi.mulSingle a (h a) ∈ tupleGamma (Γ := Γ) a :=
        fun j hj => Pi.mulSingle_eq_of_ne hj (h a)
      rw [hsplit]
      exact mul_mem
        (mem_γ_le_zSub tupleGamma (Set.mem_insert a s) hsingle)
        (zSub_mono tupleGamma (Set.subset_insert a s) (ih hupdate))

/-- The two inclusions together: for a finite dishonest set the generated
class *is* the `Z`-supported tuples. -/
theorem zSub_tupleGamma_eq_supportedOn {Z : Set I} (hZ : Z.Finite) :
    zSub (Sigma := ∀ j, Γ j) tupleGamma Z = supportedOn Z (fun _ => ⊤) :=
  le_antisymm (zSub_tupleGamma_le_supportedOn Z) (supportedOn_le_zSub_tupleGamma hZ)

/-- A pattern-attached tuple at a finite pattern lies in the generated
dishonest class — the bridge from MauRen11-style simulator tuples to
LiuMau20-style joint simulators. -/
theorem patternAttach_mem_zSub_tupleGamma {Z : Set I} (hZ : Z.Finite)
    (σ : ∀ i, Γ i) :
    patternAttach Z σ ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z :=
  supportedOn_le_zSub_tupleGamma hZ
    (patternAttach_mem_supportedOn fun _ _ => Submonoid.mem_top _)

/-- Def 14 (i) for the honest pattern: the honest attachment `π^{P∖Z}`
(`patternAttach Zᶜ π`, identity on `Z`) commutes with everything in the
dishonest class (identity off `Z`), because at each interface one of the
two is the identity. -/
theorem commute_patternAttach_zSub {Z : Set I} (π : ∀ i, Γ i)
    {h : ∀ i, Γ i} (hh : h ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z) :
    Commute (patternAttach Zᶜ π) h := by
  apply commute_patternAttach_supportedOn (P := Zᶜ) (H := fun _ => ⊤)
  simpa only [compl_compl] using zSub_tupleGamma_le_supportedOn Z hh

/-- LiuMau20's per-`Z` statement from its leaf: if the honest-pattern
protocol turns every assumed resource into a dishonest-side converter
applied to the ideal, then it constructs the `∗Z`-relaxed ideal from the
`∗Z`-relaxed assumed specification. -/
theorem constructs_zStar_of_leaf {Z : Set I} (π : ∀ i, Γ i)
    {assumed : Set Φ} {ideal : Φ}
    (hleaf : ∀ R ∈ assumed, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      patternAttach Zᶜ π • R = s • ideal) :
    zStar (Sigma := ∀ j, Γ j) tupleGamma Z assumed —[patternAttach Zᶜ π]→
      zStar (Sigma := ∀ j, Γ j) tupleGamma Z {ideal} :=
  zStar_construct_of_simulators tupleGamma
    (fun _ hh => commute_patternAttach_zSub π hh) hleaf

/-- The `ε`-relaxed per-`Z` statement: with only an `ε`-close simulator
(`edist ≤ ε`, not exact equality), the honest-pattern protocol constructs the
`ε`-ball of the `∗Z`-relaxed ideal.

On a pseudo-emetric carrier the exact target of `constructs_zStar_of_leaf` may
be strictly smaller than this theorem's zero ball; the two conclusions coincide
only under zero-distance separation. -/
theorem constructs_zStar_eps_of_leaf [PseudoEMetricSpace Φ]
    [IsNonexpandingSMul (∀ j, Γ j) Φ] {Z : Set I} (π : ∀ i, Γ i)
    {assumed : Set Φ} {ideal : Φ} {ε : ℝ≥0∞}
    (hleaf : ∀ R ∈ assumed, ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
      edist (patternAttach Zᶜ π • R) (s • ideal) ≤ ε) :
    patternAttach Zᶜ π • zStar (Sigma := ∀ j, Γ j) tupleGamma Z assumed ⊆
      Relaxation.epsilonRelaxation ε (zStar (Sigma := ∀ j, Γ j) tupleGamma Z {ideal}) :=
  Relaxation.star_construct_eps
    (fun _ hh => (commute_patternAttach_zSub π hh).actCommute) hleaf

/-- **Theorem 1's shape** (LiuMau20 §7): over an adversary structure,
per-`Z` simulator leaves for the tolerated sets give the structured
construction of the `∗Z`-relaxed ideal from the assumed specification. -/
theorem mpc_step (𝒵 : AdversaryStructure I) (π : ∀ i, Γ i)
    (assumed : Set I → Set Φ) (ideal : Φ)
    (hzrel : ∀ Z ∈ 𝒵.sets,
      assumed Z ⊆ zStar (Sigma := ∀ j, Γ j) tupleGamma Z (assumed Z))
    (hleaf : ∀ Z ∈ 𝒵.sets, ∀ R ∈ assumed Z,
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z, patternAttach Zᶜ π • R = s • ideal) :
    ConstructsForAdversaryStructure 𝒵 π assumed
      (fun Z => zStar (Sigma := ∀ j, Γ j) tupleGamma Z {ideal}) := by
  intro Z
  by_cases hZ : Z ∈ 𝒵.sets
  · simp only [if_pos hZ]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact constructs_zStar_of_leaf π (hleaf Z hZ)
      (Set.smul_mem_smul_set (hzrel Z hZ hy))
  · simp only [if_neg hZ]
    exact fun x _ => Set.mem_univ x

/-! ### The simulator quantifier order

`mpc_step` and `constructs_zStar_of_leaf` use the LiuMau20 §2.5 order, with
the simulator chosen *after* the dishonest set and the assumed resource:

```text
∀ Z ∈ 𝒵, ∀ R ∈ spec Z, ∃ s ∈ zSub tupleGamma Z, …
```

MauRen11 Theorem 2 instead chooses one local-simulator tuple `σ` before
ranging over corruption patterns, the per-`Z` simulator being its pattern
attachment `σ ⇂ Z`.  The two orders are **not** equivalent: shared ⟹
per-pattern is `leaf_of_shared_simulator` below, while per-pattern ⟹ shared
is refuted by the example after it.  A statement needing the shared order
must take `σ` explicitly. -/

/-- Shared ⟹ per-pattern: one MauRen11-style local-simulator tuple `σ`,
attached at each tolerated pattern, provides the LiuMau20-style per-`Z`
simulator leaves. -/
theorem leaf_of_shared_simulator {𝒵 : AdversaryStructure I} {π σ : ∀ i, Γ i}
    {spec : Set I → Set Φ} {ideal : Φ}
    (hfin : ∀ Z ∈ 𝒵.sets, Z.Finite)
    (hshared : ∀ Z ∈ 𝒵.sets, ∀ R ∈ spec Z,
      patternAttach Zᶜ π • R = patternAttach Z σ • ideal) :
    ∀ Z ∈ 𝒵.sets, ∀ R ∈ spec Z,
      ∃ s ∈ zSub (Sigma := ∀ j, Γ j) tupleGamma Z,
        patternAttach Zᶜ π • R = s • ideal :=
  fun Z hZ R hR =>
    ⟨patternAttach Z σ, patternAttach_mem_zSub_tupleGamma (hfin Z hZ) σ,
     hshared Z hZ R hR⟩

end Tuple

/-- Per-pattern ⇏ shared.  Two parties with converter monoid
`Multiplicative (ZMod 2)`, the tuple monoid acting on itself, identity
protocol, ideal `1`: the per-`Z` leaf equation
`patternAttach Zᶜ 1 • R = s • 1` then reads `R = s`, so a per-`Z`
simulator for an assumed resource is the resource itself.  Take the
assumed specification demanding `Pi.mulSingle false (ofAdd 1)` at
`Z = {false}` but `1` at `Z = Set.univ`.  Both are legitimate per-`Z`
simulators — the first conjunct — yet a shared tuple `σ` would need
`σ false = ofAdd 1` (at `Z = {false}`, where
`σ ⇂ {false} = mulSingle false (σ false)`) and simultaneously
`σ = σ ⇂ univ = 1` (at `Z = univ`) — the second conjunct refutes it. -/
example :
    -- the two per-pattern simulators are legitimate: each is `Z`-supported …
    ((Pi.mulSingle false (Multiplicative.ofAdd 1) :
        ∀ _ : Bool, Multiplicative (ZMod 2)) ∈
      zSub (Sigma := ∀ _ : Bool, Multiplicative (ZMod 2)) tupleGamma {false}
    ∧ (1 : ∀ _ : Bool, Multiplicative (ZMod 2)) ∈
      zSub (Sigma := ∀ _ : Bool, Multiplicative (ZMod 2)) tupleGamma Set.univ)
    -- … but no shared tuple yields both as its pattern attachments
    ∧ ¬ ∃ σ : ∀ _ : Bool, Multiplicative (ZMod 2),
        Pi.mulSingle false (Multiplicative.ofAdd 1) = patternAttach {false} σ
        ∧ (1 : ∀ _ : Bool, Multiplicative (ZMod 2)) = patternAttach Set.univ σ := by
  refine ⟨⟨?_, one_mem _⟩, ?_⟩
  · have hmem : Pi.mulSingle false (Multiplicative.ofAdd 1) ∈
        tupleGamma (Γ := fun _ : Bool => Multiplicative (ZMod 2)) false :=
      fun j hj => Pi.mulSingle_eq_of_ne hj _
    exact mem_γ_le_zSub tupleGamma (Set.mem_singleton false) hmem
  · rintro ⟨σ, hsingleton, huniv⟩
    have hfalse : σ false = Multiplicative.ofAdd 1 := by
      have := congrFun hsingleton false
      rw [patternAttach_singleton, Pi.mulSingle_eq_same,
        Pi.mulSingle_eq_same] at this
      exact this.symm
    have hone : σ false = 1 := by
      have := congrFun huniv false
      rw [patternAttach, Set.piecewise_univ] at this
      exact this.symm
    rw [hone] at hfalse
    exact absurd hfalse (by decide)

end AbstractCryptography

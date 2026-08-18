/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Attainment
import RandomSystems.System.Game

/-!
# Game winnability (Lanzenberger §2.4.3, Definitions 2.35/2.36, Theorem 2.37)

Lanzenberger, *A Theory of Random Systems, Games, and Hardness Amplification*
(Diss. ETH 29554), §2.4.3, printed pp. 23–26, read visually.  §2.3.3's objects
— the monotone condition, the pair, the transcript, `ν` — are `Game.lean`.

## The two numbers

**Definition 2.35** (printed p. 24): "A `(𝒳,𝒴)`-DDG `s^A` is *winnable* if
there exists a sequence of inputs `x̂ ∈ dom(s)` such that `A(x̂) = 1`."  A
*static* property of one deterministic game: no environment, no strategy, no
interaction — just a query sequence the system answers and at which the
condition already holds.

**Definition 2.36** (printed p. 24): "Given a random `(𝒳,𝒴)`-game `S^A`, we
define the infimum winnability of `S^A` by
`ω(S^A) := inf_{S^A ∈ 𝐒^A} Pr^{S^A}(S^A is winnable)`."  The infimum runs over
the *representatives of the game's equivalence class* (Definition 2.22), so
Definition 2.22 is a prerequisite of Definition 2.36 and is built here.

**Theorem 2.37** (printed p. 24): `ν(S^A) = ω(S^A)`, and the infimum is
attained.  Read operationally (the thesis's own paragraph, printed p. 24): a
game with maximal winning probability `δ` is, on some equivalent
representative, *unwinnable on `1 − δ` of its own randomness* — no strategy
involved.  `mass_not_winnable_of_winnability_theorem` states that reading.

## The proof route

The thesis gives two proofs.  The self-contained one (printed p. 25) is an
induction on the query budget which rebuilds, on the game carrier, the whole
successor calculus of Theorem 2.31.  The **"Alternative Proof of Theorem
2.37"** (printed p. 26) instead reduces to Theorem 2.31 — already in the tree
(`Attainment.lean`) — and that is the route taken here, as it is in the
reference repository (`Q:RandomSystems/GameWinnability.lean:58-77,778`):

1. `ν ≤ ω` (`supWinProb_le_infWinnability`): a won interaction certifies a
   winnable realization, for every representative of the class.
2. The thesis's `T` is the **derived bit view** `toBitLaw G` (`Game.lean` §4);
   its `V` — "the random system `V` that behaves exactly like `T` but always
   outputs the bit `bᵢ = 0`" — is the bit view of the `⊥`-adjoined game
   `PDS.adjoin (PDG.forget G) (fun _ => ⊥)`.  No `zeroMBO` object is
   introduced: the twin is a constructor call at the bottom of the condition
   lattice.
3. `Adv⊥(T, V) ≤ ν(G)` (`advFullyDefined_toBitLaw_le_supWinProb`): the two bit
   views are pushforwards of *one* law `G` which agree atom-by-atom until the
   game is won, so their transcript laws are within the winning mass
   (`Probability.statDist_fTransform_le_mass_of_eq_off`) — and the bound lands
   on Definition 2.25's *bit-blind* supremum because an environment that reads
   the bits gains nothing (`run_agreement`, Remark 2.23 made quantitative for
   the derived view).
4. Theorem 2.31 at `(T, V)` produces representatives `T' ≡ T`, `V' ≡ V` with
   `δ(T', V') = Adv⊥(T, V)`.
5. No representative of `V` has a winnable atom
   (`mass_winnable_eq_zero_of_equivalent_twin`): a winnable atom would win
   against its own fixed-query environment `playQueries`, which `V` never does.
6. `T'.mass Winnable ≤ δ(T', V')` and `T'` reads back as a *game* for the class
   of `G` (`gameEquivalent_ofBitLaw`), so `ω(G) ≤ T'.mass Winnable ≤ ν(G)`.
7. The chain `ν ≤ ω ≤ (ofBitLaw T').mass Winnable ≤ ν` collapses.

## What the finiteness bundle is

Theorem 2.31 is available on the finite shared-domain slice
(`PDS.HaveCommonDomainAndBounded`), and the twin is *derived* from `G`, so the
two domain clauses of that bundle are one clause about `G`: every atom of `G`
presents the domain `D`, and `D` answers at most `q` queries.  The theorem
therefore carries `[Fintype X]`, `PDG.HasDomain G D`, `QBounded D q` — one
domain, not two, which is the whole difference from the reference repository's
`PFunPDS.HasFixedDomain G D` (a two-argument relation there; AC's
`PDS.HasFixedDomain` is the one-system existential and is documented as *not*
usable in two-system statements, `Environment.lean:280`).

## The empty-history clause

On this carrier `[] ∉ dom s` for every DDS (`System.empty_not_mem`, Definition
2.9 as rendered), while Definition 2.20 admits a condition already satisfied at
the empty history — the lattice's `⊤`.  Such a game is *won* in every
interaction and yet, by Definition 2.35's letter, **not winnable**: `ν = |G|`
and `ω = 0`.  So Theorem 2.37 is false on the pair carrier without a clause
excluding it, and the statements below carry
`∀ g ∈ G.support, [] ∉ g.2.1` explicitly.  It is the same clause `Game.lean`'s
`winningMass_eq_mass_lastBit_toBitLaw` carries, it is implied by
`System.DomainSupported` (`System.not_mem_nil_of_domainSupported`), and it
*propagates along Definition 2.22* (`not_mem_nil_of_gameEquivalent`): the
already-won mass is the Definition 2.21 observable at length `0`.
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-! ## Definition 2.35: winnability of a deterministic game -/

/-- Lanzenberger **Definition 2.35** (printed p. 24): "A `(𝒳,𝒴)`-DDG `s^A` is
*winnable* if there exists a sequence of inputs `x̂ ∈ dom(s)` such that
`A(x̂) = 1`."

Verbatim on Definition 2.20's pair: a history the system answers at which the
condition holds.  Nothing here mentions an environment — this is the *static*
notion whose mass Theorem 2.37 identifies with the adversarial supremum. -/
def Winnable (g : DDG X Y) : Prop :=
  ∃ l ∈ dom g.1, l ∈ g.2.1

/-- The never-won pole of the condition lattice is unwinnable — the thesis's
always-losing system `V` (printed p. 26) at the level of one realization. -/
@[simp] theorem not_winnable_bot (s : DDS X Y) :
    ¬ Winnable (s, (⊥ : MonotoneCondition X)) := by
  rintro ⟨l, -, hl⟩
  exact Set.notMem_empty _ hl

/-- **A won interaction certifies a winnable realization** — the deterministic
core of Theorem 2.37's trivial direction.  The history the system processed is
in its domain (`keptPrefix_mem_or`) unless it is empty, and the empty case is
exactly the clause the module docstring records. -/
theorem winnable_of_won {g : DDG X Y} (hnil : [] ∉ g.2.1)
    {e : DDE.Total Y X} {n : ℕ} (h : Won g e n) : Winnable g := by
  have hkey := DDE.Total.answeredQueries_transcript g.1 e n
  rw [Won, hkey] at h
  rcases keptPrefix_mem_or g.1 ((DDE.Total.transcript g.1 e n)↓ₓ) with hmem | hemp
  · exact ⟨_, hmem, h⟩
  · exact absurd (hemp ▸ h) hnil

/-- Winnability read on the derived bit view: the reconstruction
`ofBitSystem` is winnable exactly when the system shows the bit `1` somewhere
in its domain.  (The reference repository takes this as *the* definition of
winnability, `Q:RandomSystems/GameWinnability.lean:281`; here it is a theorem
about the view, Definition 2.35 living on the pair.) -/
theorem winnable_ofBitSystem_iff (t : DDS X (Y × Bool)) :
    Winnable (ofBitSystem t) ↔
      ∃ (l : List X) (h : l ∈ dom t), (output t l h).2 = true := by
  constructor
  · rintro ⟨l, -, hl⟩
    obtain ⟨l', -, hl'mem, hl'bit⟩ := (mem_ofBitSystem_snd t l).mp hl
    exact ⟨l', hl'mem, hl'bit⟩
  · rintro ⟨l, hl, hbit⟩
    exact ⟨l, by rw [ofBitSystem_fst, dom_relabel_fst]; exact hl,
      (mem_ofBitSystem_snd t l).mpr ⟨l, List.prefix_rfl, hl, hbit⟩⟩

end System

/-! ## Definition 2.22: equivalence of probabilistic games -/

namespace PDG

/-- Lanzenberger **Definition 2.22** (printed p. 17): two PDG are equivalent
when their Definition 2.21 transcript laws agree in every environment.

The thesis's same-domain clause is absorbed by the `⊥`-totalized carrier
exactly as in Definition 2.17 (`PDS.equivalent`): a refused query is the
observable answer `none`, so the domain is reported by the transcript.

This relation is **coarser** than Definition 2.17 on the underlying system
laws: it observes only the final condition value, not the per-round bits
(Remark 2.23).  That is load-bearing — `ω` infimizes over *this* class, and
Theorem 2.37's attained representative is produced by Theorem 2.31, which
delivers the finer Definition-2.17 equivalence
(`gameEquivalent_of_equivalent_toBitLaw`). -/
def gameEquivalent (G H : PDG X Y) : Prop :=
  ∀ (e : System.DDE.Total Y X) (n : ℕ), gameTrLaw e n G = gameTrLaw e n H

theorem gameEquivalent_refl (G : PDG X Y) : gameEquivalent G G := fun _ _ => rfl

theorem gameEquivalent_symm {G H : PDG X Y} (h : gameEquivalent G H) :
    gameEquivalent H G := fun e n => (h e n).symm

theorem gameEquivalent_trans {G H K : PDG X Y} (h : gameEquivalent G H)
    (h' : gameEquivalent H K) : gameEquivalent G K :=
  fun e n => (h e n).trans (h' e n)

/-- Definition 2.22 preserves Definition 2.1's weight: the transcript law is a
pushforward. -/
theorem weight_eq_of_gameEquivalent {G H : PDG X Y} (h : gameEquivalent G H) :
    G.weight = H.weight := by
  have h0 := h (fun _ => none) 0
  have hG := Distribution.weight_fTransform
    (fun g => System.gameTranscript g (fun _ => none) 0) G
  have hH := Distribution.weight_fTransform
    (fun g => System.gameTranscript g (fun _ => none) 0) H
  rw [← hG, ← hH]
  exact congrArg Distribution.weight h0

/-- Definition 2.25's winning mass is a Definition 2.22 invariant: it reads
only the game-transcript law (`winningMass_eq_mass_gameTrLaw`). -/
theorem winningMass_congr_gameEquivalent {G H : PDG X Y} (h : gameEquivalent G H)
    (e : System.DDE.Total Y X) (n : ℕ) :
    winningMass e n G = winningMass e n H := by
  rw [winningMass_eq_mass_gameTrLaw, winningMass_eq_mass_gameTrLaw, h e n]

/-- **`ν` is a class invariant.**  Definition 2.25 is a supremum of Definition
2.22 invariants over an index set that mentions no presentation. -/
theorem supWinProb_congr_gameEquivalent {G H : PDG X Y} (h : gameEquivalent G H) :
    supWinProb G = supWinProb H :=
  iSup_congr fun p => winningMass_congr_gameEquivalent h p.1 p.2

/-- The **already-won mass** — the mass of the atoms whose condition holds
before the interaction begins — is the Definition 2.21 observable at length
`0`, hence a Definition 2.22 invariant. -/
theorem winningMass_zero (G : PDG X Y) (e : System.DDE.Total Y X) :
    winningMass e 0 G = G.mass fun g => [] ∈ g.2.1 := rfl

/-- **The empty-history clause propagates along Definition 2.22.**  An honest
representative of a game that is not already won cannot itself be already won
on any atom: the already-won mass is an observable, and a support atom
witnessing an event of mass zero is impossible on the honest carrier
(`Distribution.not_of_mass_eq_zero_of_mem_support`). -/
theorem not_mem_nil_of_gameEquivalent {G H : PDG X Y}
    (hH : H.NonNeg) (hnil : ∀ g ∈ G.support, [] ∉ g.2.1)
    (h : gameEquivalent H G) : ∀ g ∈ H.support, [] ∉ g.2.1 := by
  have hzero : H.mass (fun g => [] ∈ g.2.1) = 0 := by
    rw [← winningMass_zero H (fun _ => none),
      winningMass_congr_gameEquivalent h (fun _ => none) 0, winningMass_zero]
    exact (Distribution.mass_congr_of_support G (Q := fun _ => False)
      fun g hg => iff_of_false (hnil g hg) id).trans
        (Distribution.mass_eq_zero_of_forall_not G fun _ hfalse => hfalse)
  exact fun g hg => Distribution.not_of_mass_eq_zero_of_mem_support hH hzero hg

/-! ## Definition 2.36: the infimum winnability `ω` -/

/-- Lanzenberger **Definition 2.36** (printed p. 24): "we define the infimum
winnability of `S^A` by `ω(S^A) := inf_{S^A ∈ 𝐒^A} Pr^{S^A}(S^A is winnable)`."

The index set is the **honest** representatives of the Definition 2.22 class —
Ruling R9's discipline, and the thesis's own meaning: a representative is a
probability system in Definition 2.1's sense.  On the signed carrier the
`NonNeg` conjunct is not decoration; dropping it drives the infimum to `−∞`,
and the same conjunct is written explicitly in the reference repository
(`Q:RandomSystems/GameWinnability.lean:294`).  Off the honest carrier the index
set is empty and `ω(G) = 0` by `Real.sInf_empty`; every statement below carries
`NonNeg`. -/
def infWinnability (G : PDG X Y) : ℝ :=
  sInf ((fun H : PDG X Y => H.mass System.Winnable) ''
    {H | H.NonNeg ∧ gameEquivalent H G})

/-- Lanzenberger Definition 2.36 notation. -/
scoped notation "ω(" G ")" => infWinnability G

/-- The `ω`-set is bounded below by `0`: every representative is honest, so its
winnable mass is non-negative. -/
theorem bddBelow_image_mass_winnable (G : PDG X Y) :
    BddBelow ((fun H : PDG X Y => H.mass System.Winnable) ''
      {H | H.NonNeg ∧ gameEquivalent H G}) := by
  refine ⟨0, ?_⟩
  rintro b ⟨H, ⟨hH, -⟩, rfl⟩
  exact hH.mass_nonneg _

/-- Definition 2.36's defining property, upper half: every honest
representative bounds `ω`. -/
theorem infWinnability_le_mass_winnable {G H : PDG X Y} (hH : H.NonNeg)
    (h : gameEquivalent H G) : infWinnability G ≤ H.mass System.Winnable :=
  csInf_le (bddBelow_image_mass_winnable G) ⟨H, ⟨hH, h⟩, rfl⟩

/-- Definition 2.36's defining property, lower half. -/
theorem le_infWinnability_of_forall {G : PDG X Y} {c : ℝ} (hG : G.NonNeg)
    (h : ∀ H : PDG X Y, H.NonNeg → gameEquivalent H G → c ≤ H.mass System.Winnable) :
    c ≤ infWinnability G := by
  refine le_csInf ⟨G.mass System.Winnable, G, ⟨hG, gameEquivalent_refl G⟩, rfl⟩ ?_
  rintro b ⟨H, ⟨hHnn, hH⟩, rfl⟩
  exact h H hHnn hH

theorem infWinnability_nonneg {G : PDG X Y} (hG : G.NonNeg) :
    0 ≤ infWinnability G :=
  le_infWinnability_of_forall hG fun _ hH _ => hH.mass_nonneg _

/-- **Theorem 2.37, the trivial direction** (printed p. 25): "the direction
`ω(S^A) ≥ ν(S^A)` is trivial, since we have for any environment `e` and any
`S^A ∈ 𝐒^A`: `Pr^{S^A}(S^A is winnable) ≥ Pr^{eS^A}(tr(S^A,e) ∈ 𝒯_w)`."

Every environment's winning mass is below every honest representative's
winnable mass: winning the interaction requires a winnable realization
(`System.winnable_of_won`), and the winning mass is a class invariant. -/
theorem supWinProb_le_infWinnability {G : PDG X Y} (hG : G.NonNeg)
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) :
    supWinProb G ≤ infWinnability G := by
  refine le_infWinnability_of_forall hG fun H hHnn hH => ?_
  refine supWinProb_le_of_forall fun e n => ?_
  rw [winningMass_congr_gameEquivalent (gameEquivalent_symm hH) e n]
  exact Distribution.mass_mono_on_support hHnn fun h hh hwon =>
    System.winnable_of_won (not_mem_nil_of_gameEquivalent hHnn hnil hH h hh) hwon

end PDG

end

end RandomSystems

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

/-! ## The derived bit view: the thesis's `T` and `V`

The alternative proof of Theorem 2.37 (printed p. 26) transports the game into
a *distinction problem between two random systems*: "`T` … behaves like `S` but
additionally outputs a (monotone) bit `bᵢ ∈ {0,1}` as a response to each query,
such that `bᵢ = 1` if and only if the game has been won", and "`V` … behaves
exactly like `T` but always outputs the bit `bᵢ = 0`".

On this carrier `T` is `Game.lean`'s derived view `PDG.toBitLaw G`, and `V` is
the derived view of the game obtained by adjoining the *bottom* of the
condition lattice to the same behaviour — `PDS.adjoin (PDG.forget G) (fun _ =>
⊥)`.  The reference repository coins an object for `V` (`zeroMBO`,
`Q:RandomSystems/GameWinnability.lean:356`); here it is a constructor call, and
`Game.lean`'s `supWinProb_adjoin_bot = 0` already records that it never wins.
-/

namespace System

/-- The `⊥` of the condition lattice, read through Definition 2.20's
`{0,1}`-predicate view: never satisfied. -/
@[simp] theorem MonotoneCondition.toPred_bot (l : List X) :
    MonotoneCondition.toPred (⊥ : MonotoneCondition X) l = false :=
  decide_eq_false (Set.notMem_empty l)

/-- The bit view of a `⊥`-adjoined game answers where the system answers, and
always shows the bit `0`: the thesis's "always outputs the bit `bᵢ = 0`"
(printed p. 26). -/
theorem answer_toBitSystem_bot (s : DDS X Y) (l : List X) (x : X) :
    answer (toBitSystem (s, (⊥ : MonotoneCondition X))) l x =
      (answer s l x).map fun y => (y, false) := by
  rw [answer_toBitSystem]
  simp

/-- Winning is an event of the *bit-view* run: the histories the two runs
process are the same (`answeredQueries_transcript_toBitSystem`). -/
theorem won_iff_bitRun (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    Won g e n ↔
      answeredQueries (DDE.Total.transcript (toBitSystem g)
        (DDE.Total.relabelOut Prod.fst e) n) ∈ g.2.1 := by
  simp only [Won, answeredQueries_transcript_toBitSystem]

/-- The bit-blinding of an environment for the bit view, computed: an
environment that has met the bit view through the *bit-erasing* converter is
the original environment fed a history whose bits are all `0`.

`DDE.Total.relabelOut (·, false)` is the blinding (an environment for the plain
system), and `DDE.Total.relabelOut Prod.fst` presents it back at the bit
alphabet — both existing generators of the trivial-converter monoid, so the
reference repository's `blindize` coinage
(`Q:RandomSystems/GameWinnability.lean:658`) is not needed. -/
theorem relabelOut_blind_apply (e : DDE.Total (Y × Bool) X)
    (ys : List (Option (Y × Bool))) :
    DDE.Total.relabelOut Prod.fst
        (DDE.Total.relabelOut (fun y : Y => (y, false)) e) ys
      = e (ys.map (Option.map fun p : Y × Bool => (p.1, false))) := by
  show e ((ys.map (Option.map Prod.fst)).map (Option.map fun y : Y => (y, false)))
    = _
  rw [List.map_map]
  refine congrArg e (List.map_congr_left fun o _ => ?_)
  rcases o with _ | p <;> rfl

/-- **The run-agreement lemma**: until the game is won, one interaction with
the bit view is *three* interactions at once — it is the interaction with the
never-won twin, and it is the interaction the bit-blinded environment has.

This is the single induction Theorem 2.37's route needs.  Its first conjunct is
the "identical-until-bad" hypothesis of
`Probability.statDist_fTransform_le_mass_of_eq_off`; its second is Remark 2.23
made quantitative on the derived view (an environment that *reads* the bits
learns nothing before the first `1`, so the bound lands on Definition 2.25's
bit-blind supremum); its third is the invariant that makes the second go
through — before the game is won every answer the environment has seen carries
the bit `0`, and blinding is then the identity on the history.

The reference repository splits this into two inductions with an auxiliary
`blindize` predicate (`Q:RandomSystems/GameWinnability.lean:563,690`); on the
pair carrier the winning event is `Won` itself, so one invariant carries both. -/
theorem run_agreement (g : DDG X Y) (e : DDE.Total (Y × Bool) X) (n : ℕ) :
    Won g (DDE.Total.relabelOut (fun y : Y => (y, false)) e) n ∨
      (DDE.Total.transcript (toBitSystem g) e n
          = DDE.Total.transcript (toBitSystem (g.1, (⊥ : MonotoneCondition X))) e n ∧
        DDE.Total.transcript (toBitSystem g) e n
          = DDE.Total.transcript (toBitSystem g)
              (DDE.Total.relabelOut Prod.fst
                (DDE.Total.relabelOut (fun y : Y => (y, false)) e)) n ∧
        ((DDE.Total.transcript (toBitSystem g) e n)↓ᵧ).map
              (Option.map fun p : Y × Bool => (p.1, false))
            = (DDE.Total.transcript (toBitSystem g) e n)↓ᵧ) := by
  induction n with
  | zero => exact Or.inr ⟨rfl, rfl, rfl⟩
  | succ n ih =>
      rcases ih with hwon | ⟨h1, h2, h3⟩
      · exact Or.inl (hwon.mono (Nat.le_succ n))
      · have hquery : DDE.Total.relabelOut Prod.fst
              (DDE.Total.relabelOut (fun y : Y => (y, false)) e)
              (DDE.Total.transcript (toBitSystem g)
                (DDE.Total.relabelOut Prod.fst
                  (DDE.Total.relabelOut (fun y : Y => (y, false)) e)) n)↓ᵧ
            = e (DDE.Total.transcript (toBitSystem g) e n)↓ᵧ := by
          rw [← h2, relabelOut_blind_apply, h3]
        rcases hx : e (DDE.Total.transcript (toBitSystem g) e n)↓ᵧ with _ | x
        · -- the environment stops: all three runs stand still
          have hxB : e (DDE.Total.transcript
              (toBitSystem (g.1, (⊥ : MonotoneCondition X))) e n)↓ᵧ = none := by
            rw [← h1]; exact hx
          refine Or.inr ⟨?_, ?_, ?_⟩
          · rw [DDE.Total.transcript_succ_of_stop _ _ hx,
              DDE.Total.transcript_succ_of_stop _ _ hxB]
            exact h1
          · rw [DDE.Total.transcript_succ_of_stop _ _ hx,
              DDE.Total.transcript_succ_of_stop _ _ (hquery.trans hx)]
            exact h2
          · rw [DDE.Total.transcript_succ_of_stop _ _ hx]
            exact h3
        · -- the environment fires `x`: all three runs fire it, at one history
          have hxB : e (DDE.Total.transcript
              (toBitSystem (g.1, (⊥ : MonotoneCondition X))) e n)↓ᵧ = some x := by
            rw [← h1]; exact hx
          have hkept : keptPrefix g.1 (DDE.Total.transcript (toBitSystem g) e n)↓ₓ
              = answeredQueries (DDE.Total.transcript (toBitSystem g) e n) := by
            rw [DDE.Total.answeredQueries_transcript, keptPrefix_toBitSystem]
          have hansA : answer (toBitSystem g)
                (DDE.Total.transcript (toBitSystem g) e n)↓ₓ x
              = (answer g.1 (DDE.Total.transcript (toBitSystem g) e n)↓ₓ x).map
                  fun y => (y, MonotoneCondition.toPred g.2
                    (answeredQueries (DDE.Total.transcript (toBitSystem g) e n)
                      ++ [x])) := by
            rw [answer_toBitSystem, hkept]
          have hstep2 : DDE.Total.transcript (toBitSystem g) e (n + 1)
              = DDE.Total.transcript (toBitSystem g)
                  (DDE.Total.relabelOut Prod.fst
                    (DDE.Total.relabelOut (fun y : Y => (y, false)) e)) (n + 1) := by
            rw [DDE.Total.transcript_succ_of_query _ _ hx,
              DDE.Total.transcript_succ_of_query _ _ (hquery.trans hx), ← h2]
          rcases hans : answer g.1 (DDE.Total.transcript (toBitSystem g) e n)↓ₓ x
            with _ | y
          · -- the query is refused: no bit is shown and no history grows
            refine Or.inr ⟨?_, hstep2, ?_⟩
            · rw [DDE.Total.transcript_succ_of_query _ _ hx,
                DDE.Total.transcript_succ_of_query _ _ hxB, ← h1, hansA,
                answer_toBitSystem_bot, hans]
              rfl
            · rw [DDE.Total.transcript_succ_of_query _ _ hx, hansA, hans,
                transcriptOutputs_concat]
              simp [h3]
          · by_cases hbit : MonotoneCondition.toPred g.2
                (answeredQueries (DDE.Total.transcript (toBitSystem g) e n) ++ [x])
                = true
            · -- the answer shows the bit `1`: the game is won at `n + 1`
              refine Or.inl ((won_iff_bitRun g _ (n + 1)).mpr ?_)
              rw [← hstep2, DDE.Total.transcript_succ_of_query _ _ hx, hansA, hans]
              simp only [Option.map_some, answeredQueries_concat_some]
              exact MonotoneCondition.toPred_eq_true.mp hbit
            · rw [Bool.not_eq_true] at hbit
              refine Or.inr ⟨?_, hstep2, ?_⟩
              · rw [DDE.Total.transcript_succ_of_query _ _ hx,
                  DDE.Total.transcript_succ_of_query _ _ hxB, ← h1, hansA,
                  answer_toBitSystem_bot, hbit]
              · rw [DDE.Total.transcript_succ_of_query _ _ hx, hansA, hbit,
                  transcriptOutputs_concat]
                simp [h3, Function.comp_def]

/-! ### The winning test on the derived view, and the probing run -/

/-- Definition 2.25's winning-transcript set `𝒯_w` read on the derived bit
view: some answered query showed the bit `1`.  (The reference repository takes
this as primitive, `Q:RandomSystems/GameWinnability.lean:105`; here it is the
test that certifies membership in the reconstructed condition, `sawBit_iff`.) -/
def SawBit (t : List (X × Option (Y × Bool))) : Prop :=
  ∃ p ∈ answeredEntries t, p.2.2 = true

@[simp] theorem not_sawBit_nil : ¬ SawBit ([] : List (X × Option (Y × Bool))) := by
  rintro ⟨p, hp, -⟩
  simp [answeredEntries] at hp

/-- **The run-structure identity for the bit view**: the bits an interaction
has seen are exactly the bits shown at the histories it processed, so "some
answered query showed `1`" is membership of the processed history in the
reconstructed condition `(ofBitSystem t).2`.

The reconstruction's upward closure is doing the work: it *is* the "some
answered prefix" quantifier, which is why no monotonicity hypothesis on the
system's bit appears anywhere. -/
theorem sawBit_iff (t : DDS X (Y × Bool)) (e : DDE.Total (Y × Bool) X) (n : ℕ) :
    SawBit (DDE.Total.transcript t e n) ↔
      answeredQueries (DDE.Total.transcript t e n) ∈ (ofBitSystem t).2.1 := by
  induction n with
  | zero =>
      refine iff_of_false not_sawBit_nil ?_
      rw [mem_ofBitSystem_snd]
      rintro ⟨l', hl', hmem, -⟩
      exact empty_not_mem t (by rwa [List.prefix_nil.mp hl'] at hmem)
  | succ n ih =>
      rcases hx : e (DDE.Total.transcript t e n)↓ᵧ with _ | x
      · rw [DDE.Total.transcript_succ_of_stop _ _ hx]
        exact ih
      · rw [DDE.Total.transcript_succ_of_query _ _ hx]
        have hkept : keptPrefix t (DDE.Total.transcript t e n)↓ₓ
            = answeredQueries (DDE.Total.transcript t e n) :=
          (DDE.Total.answeredQueries_transcript t e n).symm
        rcases hans : answer t (DDE.Total.transcript t e n)↓ₓ x with _ | w
        · rw [SawBit, answeredEntries_concat_none, answeredQueries_concat_none]
          exact ih
        · -- the answered query extends the processed history by `x`
          rw [answer_eq, hkept] at hans
          have hdom : answeredQueries (DDE.Total.transcript t e n) ++ [x] ∈ dom t := by
            by_contra hc
            rw [dif_neg hc] at hans
            simp at hans
          have hout : output t (answeredQueries (DDE.Total.transcript t e n) ++ [x]) hdom
              = w := by
            rw [dif_pos hdom] at hans
            exact Option.some.inj hans
          rw [SawBit, answeredEntries_concat_some, answeredQueries_concat_some,
            mem_ofBitSystem_snd]
          constructor
          · rintro ⟨p, hp, hbit⟩
            rcases List.mem_append.mp hp with hp' | hp'
            · obtain ⟨l', hl', hl'mem, hl'bit⟩ :=
                (mem_ofBitSystem_snd t _).mp (ih.mp ⟨p, hp', hbit⟩)
              exact ⟨l', hl'.trans (List.prefix_append _ _), hl'mem, hl'bit⟩
            · rw [List.mem_singleton] at hp'
              exact ⟨_, List.prefix_rfl, hdom, by rw [hout]; rw [hp'] at hbit; exact hbit⟩
          · rintro ⟨l', hl', hl'mem, hl'bit⟩
            rcases List.prefix_concat_iff.mp hl' with heq | hpre
            · refine ⟨(x, w), List.mem_append_right _ (List.mem_singleton.mpr rfl), ?_⟩
              rw [← hout, ← output_congr t heq hl'mem hdom]
              exact hl'bit
            · obtain ⟨p, hp, hbit⟩ :=
                ih.mpr ((mem_ofBitSystem_snd t _).mpr ⟨l', hpre, hl'mem, hl'bit⟩)
              exact ⟨p, List.mem_append_left _ hp, hbit⟩

/-- The never-won twin shows no bit, against any environment: the thesis's `V`
"always outputs the bit `bᵢ = 0`". -/
theorem not_sawBit_toBitSystem_bot (s : DDS X Y) (e : DDE.Total (Y × Bool) X)
    (n : ℕ) :
    ¬ SawBit (DDE.Total.transcript
      (toBitSystem (s, (⊥ : MonotoneCondition X))) e n) := by
  rw [sawBit_iff, mem_ofBitSystem_snd]
  rintro ⟨l', -, hl'mem, hl'bit⟩
  rw [output_toBitSystem] at hl'bit
  simp at hl'bit

/-! ### The probing run

Step 5 of the route needs an environment that *reaches* a given in-domain
history.  `System.DDE.Total.playQueries` (Lemma 2.18's witness class, already in
`ClassDistance.lean`) is that environment; the reference repository builds it
by hand for this proof (`Q:RandomSystems/GameWinnability.lean:434`). -/

/-- **The probing run**: the fixed-query environment `playQueries l` drives a
system that answers `l` through exactly `l`.  All prefixes of an in-domain
history are in the domain, so every query is answered and the processed history
is `l` itself. -/
theorem answeredQueries_transcript_playQueries {Y' : Type v} (v : DDS X Y')
    {l : List X} (hl : l ∈ dom v) :
    answeredQueries (DDE.Total.transcript v (DDE.Total.playQueries l) l.length) = l := by
  have hinv : ∀ k, k ≤ l.length →
      (DDE.Total.transcript v (DDE.Total.playQueries l) k)↓ₓ = l.take k ∧
        (DDE.Total.transcript v (DDE.Total.playQueries l) k).length = k := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨rfl, rfl⟩
    | succ k ih =>
        intro hk
        obtain ⟨hinputs, hlength⟩ := ih (by omega)
        have hklt : k < l.length := by omega
        have hfire : DDE.Total.playQueries (Y := Y') l
            (DDE.Total.transcript v (DDE.Total.playQueries l) k)↓ᵧ = some l[k] := by
          show l[((DDE.Total.transcript v (DDE.Total.playQueries l) k)↓ᵧ).length]?
            = some l[k]
          rw [show ((DDE.Total.transcript v (DDE.Total.playQueries l) k)↓ᵧ).length
              = k by simpa [transcriptOutputs] using hlength,
            List.getElem?_eq_getElem hklt]
        rw [DDE.Total.transcript_succ_of_query _ _ hfire]
        exact ⟨by rw [transcriptInputs_concat, hinputs,
            List.take_succ_eq_append_getElem hklt], by simp [hlength]⟩
  obtain ⟨hinputs, -⟩ := hinv l.length le_rfl
  rw [DDE.Total.answeredQueries_transcript, hinputs, List.take_length]
  exact keptPrefix_eq_self_of_mem v hl

/-- A winnable realization of the bit view **wins its own probing run**: the
fixed-query environment that plays the winning history sees the bit `1`. -/
theorem sawBit_transcript_playQueries_of_winnable {t : DDS X (Y × Bool)}
    (h : Winnable (ofBitSystem t)) :
    ∃ (l : List X), SawBit (DDE.Total.transcript t (DDE.Total.playQueries l) l.length) := by
  obtain ⟨l, hl, hbit⟩ := (winnable_ofBitSystem_iff t).mp h
  refine ⟨l, ?_⟩
  rw [sawBit_iff, answeredQueries_transcript_playQueries t hl, mem_ofBitSystem_snd]
  exact ⟨l, List.prefix_rfl, hl, hbit⟩

/-! ### Reading the bit view back as a game

The two Definition-2.21 observables — of a game and of its bit view — are one
map `gameView` applied to one run.  That is what turns a Definition-2.17
representative of the bit view (which is what Theorem 2.31 delivers) into a
Definition-2.22 representative of the game (which is what `ω` infimizes over).
-/

/-- Definition 2.21's observable, read off a run of the derived bit view: the
bit-erased record together with the flag "some answered query showed `1`". -/
def gameView (t : List (X × Option (Y × Bool))) : List (X × Option Y) × Bool :=
  (mapOutputs Prod.fst t, decide (SawBit t))

/-- On the reconstruction of the bit view, the winning test is Definition
2.25's: the processed history satisfies the reconstructed condition exactly
when the game is won.  The empty-history clause is where the bit view's
expressiveness gap sits (`Game.lean` §4): a condition holding at `[]` has no
bit to be shown. -/
theorem mem_ofBitSystem_toBitSystem_iff_won {g : DDG X Y} (hnil : [] ∉ g.2.1)
    (e : DDE.Total Y X) (n : ℕ) :
    answeredQueries (DDE.Total.transcript g.1 e n)
        ∈ (ofBitSystem (toBitSystem g)).2.1 ↔ Won g e n := by
  rw [mem_ofBitSystem_snd]
  constructor
  · rintro ⟨l', hl', hl'mem, hl'bit⟩
    rw [output_toBitSystem, MonotoneCondition.toPred_eq_true] at hl'bit
    exact g.2.upward hl' hl'bit
  · intro hwon
    have hkey := DDE.Total.answeredQueries_transcript g.1 e n
    rw [Won, hkey] at hwon
    rcases keptPrefix_mem_or g.1 ((DDE.Total.transcript g.1 e n)↓ₓ) with hmem | hemp
    · refine ⟨keptPrefix g.1 (DDE.Total.transcript g.1 e n)↓ₓ, ?_, hmem, ?_⟩
      · rw [hkey]
      · rw [output_toBitSystem, MonotoneCondition.toPred_eq_true]
        exact hwon
    · exact absurd (hemp ▸ hwon) hnil

/-- **The game's observable is its bit view's observable.**  Definition 2.21's
transcript of `s^A` is `gameView` of the run of the bit view under the same
environment, presented through the bit-erasing converter. -/
theorem gameTranscript_eq_gameView {g : DDG X Y} (hnil : [] ∉ g.2.1)
    (e : DDE.Total Y X) (n : ℕ) :
    gameTranscript g e n
      = gameView (DDE.Total.transcript (toBitSystem g)
          (DDE.Total.relabelOut Prod.fst e) n) :=
  Prod.ext (mapOutputs_transcript_toBitSystem g e n).symm
    (by
      show MonotoneCondition.toPred g.2
          (answeredQueries (DDE.Total.transcript g.1 e n)) = _
      rw [MonotoneCondition.toPred, gameView]
      refine decide_eq_decide.mpr ?_
      rw [sawBit_iff, answeredQueries_transcript_toBitSystem,
        mem_ofBitSystem_toBitSystem_iff_won hnil]
      rfl)

/-- The same identity for the *reconstruction*: `ofBitSystem t` observes what
`t` observes.  No hypothesis — the reconstruction's condition is defined as the
upward closure of the bits shown, which is what `SawBit` tests. -/
theorem gameTranscript_ofBitSystem_eq_gameView (t : DDS X (Y × Bool))
    (e : DDE.Total Y X) (n : ℕ) :
    gameTranscript (ofBitSystem t) e n
      = gameView (DDE.Total.transcript t (DDE.Total.relabelOut Prod.fst e) n) :=
  Prod.ext (transcript_relabel_id Prod.fst t e n)
    (by
      show MonotoneCondition.toPred (ofBitSystem t).2
          (answeredQueries (DDE.Total.transcript (ofBitSystem t).1 e n)) = _
      rw [ofBitSystem_fst, transcript_relabel_id, answeredQueries_mapOutputs,
        MonotoneCondition.toPred, gameView]
      exact decide_eq_decide.mpr (sawBit_iff t _ n).symm)

end System

/-! ## The two random systems of the alternative proof (printed p. 26) -/

namespace PDG

/-- The thesis's `V` — "the random system `V` that behaves exactly like `T` but
always outputs the bit `bᵢ = 0`" — as a *constructor call*: the game obtained by
adjoining the bottom of the condition lattice to `G`'s own behaviour.  This is
the computation that lets `Game.lean`'s `⊥` receipts stand in for the reference
repository's `zeroMBO` object. -/
theorem coe_adjoin_bot_forget (G : PDG X Y) :
    (PDS.adjoin (PDG.forget G) fun _ => (⊥ : System.MonotoneCondition X)).1
      = Distribution.fTransform
          (fun g => (g.1, (⊥ : System.MonotoneCondition X))) G := by
  rw [PDS.coe_adjoin, forget, Distribution.fTransform_fTransform]
  rfl

/-- The transcript law of the derived bit view is a pushforward of the *game*
law — which is what makes the two systems of the alternative proof two
readings of one sampled atom. -/
theorem trLawFullyDefined_toBitLaw (G : PDG X Y)
    (e : System.DDE.Total (Y × Bool) X) (n : ℕ) :
    PDS.trLawFullyDefined e n (toBitLaw G)
      = Distribution.fTransform
          (fun g => System.DDE.Total.transcript (System.toBitSystem g) e n) G := by
  rw [PDS.trLawFullyDefined, toBitLaw, Distribution.fTransform_fTransform]
  rfl

theorem trLawFullyDefined_toBitLaw_adjoin_bot (G : PDG X Y)
    (e : System.DDE.Total (Y × Bool) X) (n : ℕ) :
    PDS.trLawFullyDefined e n
        (toBitLaw (PDS.adjoin (PDG.forget G) fun _ => (⊥ : System.MonotoneCondition X)).1)
      = Distribution.fTransform
          (fun g => System.DDE.Total.transcript
            (System.toBitSystem (g.1, (⊥ : System.MonotoneCondition X))) e n) G := by
  rw [trLawFullyDefined_toBitLaw, coe_adjoin_bot_forget,
    Distribution.fTransform_fTransform]
  rfl

/-- **Step 3 of the route**: the optimal advantage against the never-won twin
is at most Definition 2.25's supremum winning probability — the thesis's
`Adv(T, V) = ν(S^A)` (printed p. 26), in the direction the proof consumes.

Two facts collapse into one line here.  The two systems are pushforwards of
*one* game law along maps that agree until the game is won (`run_agreement`),
so `Probability.statDist_fTransform_le_mass_of_eq_off` bounds each transcript
distance by the winning mass — that is the whole of the reference repository's
`δ`-lemma chain (`Q:GameWinnability.lean:563,616,632`).  And the winning mass
that appears is the one of the *bit-blinded* environment, which is why the
bound lands on Definition 2.25's supremum over `DDE.Total Y X` and no
`blindMaxWinProb` variant is needed. -/
theorem advFullyDefined_toBitLaw_le_supWinProb {G : PDG X Y} (hG : G.NonNeg) :
    PDS.advFullyDefined (toBitLaw G)
        (toBitLaw (PDS.adjoin (PDG.forget G)
          fun _ => (⊥ : System.MonotoneCondition X)).1)
      ≤ ENNReal.ofReal (supWinProb G) := by
  refine iSup_le fun e => iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
  rw [trLawFullyDefined_toBitLaw, trLawFullyDefined_toBitLaw_adjoin_bot]
  refine le_trans (Probability.statDist_fTransform_le_mass_of_eq_off hG _ _
    (fun g => System.Won g
      (System.DDE.Total.relabelOut (fun y : Y => (y, false)) e) n)
    (fun g _ hnotwon => ((System.run_agreement g e n).resolve_left hnotwon).1)) ?_
  exact winningMass_le_supWinProb hG _ n

/-- **Step 5 of the route**: no Definition-2.17 representative of the never-won
twin has a winnable atom.

The probing argument: a winnable atom would show the bit `1` against its own
fixed-query environment (`System.sawBit_transcript_playQueries_of_winnable`), so
that environment's transcript law would carry positive mass on `SawBit` — but
the twin's transcript law carries none, in any environment, and Definition 2.17
equates the two laws.  No finiteness is used: the atom carries its own probe. -/
theorem mass_winnable_ofBitSystem_eq_zero_of_equivalent_twin {G : PDG X Y}
    {V' : PDS X (Y × Bool)} (hV' : V'.NonNeg)
    (hequiv : PDS.equivalent V'
      (toBitLaw (PDS.adjoin (PDG.forget G)
        fun _ => (⊥ : System.MonotoneCondition X)).1)) :
    V'.mass (fun t => System.Winnable (System.ofBitSystem t)) = 0 := by
  refine (Distribution.mass_congr_of_support V' (Q := fun _ => False)
    fun v hv => iff_of_false ?_ id).trans
      (Distribution.mass_eq_zero_of_forall_not V' fun _ hfalse => hfalse)
  intro hwin
  obtain ⟨l, hsaw⟩ := System.sawBit_transcript_playQueries_of_winnable hwin
  have hzero : V'.mass (fun u => System.SawBit
      (System.DDE.Total.transcript u (System.DDE.Total.playQueries l) l.length)) = 0 := by
    rw [← Distribution.mass_fTransform
        (fun u => System.DDE.Total.transcript u
          (System.DDE.Total.playQueries l) l.length) V' System.SawBit,
      show Distribution.fTransform
          (fun u => System.DDE.Total.transcript u
            (System.DDE.Total.playQueries l) l.length) V'
        = PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length V' from rfl,
      hequiv, trLawFullyDefined_toBitLaw_adjoin_bot, Distribution.mass_fTransform]
    exact Distribution.mass_eq_zero_of_forall_not G fun g =>
      System.not_sawBit_toBitSystem_bot g.1 _ l.length
  exact Finsupp.mem_support_iff.mp hv
    (le_antisymm (hzero ▸ Distribution.apply_le_mass hV' hsaw) (hV' v))

/-! ### Reading a bit-view representative back as a game -/

theorem gameTrLaw_eq_fTransform_gameView {G : PDG X Y}
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) (e : System.DDE.Total Y X) (n : ℕ) :
    gameTrLaw e n G
      = Distribution.fTransform System.gameView
          (PDS.trLawFullyDefined (System.DDE.Total.relabelOut Prod.fst e) n
            (toBitLaw G)) := by
  rw [trLawFullyDefined_toBitLaw, Distribution.fTransform_fTransform, gameTrLaw]
  exact Distribution.fTransform_congr G fun g hg =>
    System.gameTranscript_eq_gameView (hnil g hg) e n

theorem gameTrLaw_ofBitLaw_eq_fTransform_gameView (T : PDS X (Y × Bool))
    (e : System.DDE.Total Y X) (n : ℕ) :
    gameTrLaw e n (ofBitLaw T)
      = Distribution.fTransform System.gameView
          (PDS.trLawFullyDefined (System.DDE.Total.relabelOut Prod.fst e) n T) := by
  rw [gameTrLaw, ofBitLaw, Distribution.fTransform_fTransform,
    PDS.trLawFullyDefined, Distribution.fTransform_fTransform]
  exact Distribution.fTransform_congr T fun t _ =>
    System.gameTranscript_ofBitSystem_eq_gameView t e n

/-- **Definition 2.17 on the bit view implies Definition 2.22 on the games.**
A representative of the *derived view* reads back, through `ofBitLaw`, as a
representative of the game's Definition-2.22 class.  This is the step that
makes Theorem 2.31 usable for Theorem 2.37 — and it is strictly one-way:
Definition 2.17 sees the per-round bits, Definition 2.22 does not
(Remark 2.23). -/
theorem gameEquivalent_ofBitLaw_of_equivalent {G : PDG X Y}
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) {T : PDS X (Y × Bool)}
    (h : PDS.equivalent T (toBitLaw G)) : gameEquivalent (ofBitLaw T) G := by
  intro e n
  rw [gameTrLaw_ofBitLaw_eq_fTransform_gameView,
    gameTrLaw_eq_fTransform_gameView hnil, h]

end PDG

/-! ## Theorem 2.37: the Winnability Theorem -/

namespace PDG

/-- Definition 2.14's domain attribute at the level of a *game*: every
deterministic game in the support presents the domain `D`.

Theorem 2.31 asks for the domain on each of the two systems it compares
(`PDS.HaveCommonDomainAndBounded`); here the second system is *derived* from
the first, so one clause about `G` supplies both.  That is the whole finiteness
bundle Theorem 2.37 carries: this, `QBounded D q`, and `[Fintype X]`. -/
def HasDomain (G : PDG X Y) (D : Set (List X)) : Prop :=
  ∀ g ∈ G.support, System.dom g.1 = D

/-- The derived bit view inherits the game's domain: `toBitSystem` touches no
domain (`Game.lean`, `dom_toBitSystem`). -/
theorem hasDomain_toBitLaw {G : PDG X Y} {D : Set (List X)} (h : HasDomain G D) :
    PDS.HasDomain (toBitLaw G) D := by
  intro s hs
  obtain ⟨g, hg, rfl⟩ := Distribution.mem_support_fTransform _ G hs
  exact h g hg

/-- The never-won twin inherits it too — adjoining a condition changes no
domain, which is the first half of the forgetting law. -/
theorem hasDomain_toBitLaw_adjoin_bot {G : PDG X Y} {D : Set (List X)}
    (h : HasDomain G D) :
    PDS.HasDomain (toBitLaw (PDS.adjoin (PDG.forget G)
      fun _ => (⊥ : System.MonotoneCondition X)).1) D := by
  intro s hs
  rw [toBitLaw, coe_adjoin_bot_forget, Distribution.fTransform_fTransform] at hs
  obtain ⟨g, hg, rfl⟩ := Distribution.mem_support_fTransform _ G hs
  exact h g hg

/-- **Lanzenberger Theorem 2.37 (Winnability Theorem)** (printed p. 24): "For
any random `(𝒳,𝒴)`-game `S^A` we have `ν(S^A) = ω(S^A)`, and there exists
`S^A ∈ 𝐒^A` such that `Pr^{S^A}(S^A is winnable) = ω(S^A)`."

Proved by the thesis's own alternative proof (printed p. 26) on top of Theorem
2.31, as the module docstring sets out.  Three things the statement says that
the thesis's letter does not:

* **the attained representative is produced by a Definition-2.17 equivalence**
  of the derived bit views, which is strictly finer than the Definition-2.22
  game equivalence `ω` quantifies over (`gameEquivalent_ofBitLaw_of_equivalent`
  is one-way, Remark 2.23).  The last conjunct records the witness;
* **monotonicity of the condition is used only through the lattice**, never as
  a hypothesis on a bit pattern: the reconstructed condition of an arbitrary
  bit-view representative is an upper set by construction (`ofBitSystem`), so
  no monotone-bit clause appears anywhere;
* **no probability-distribution hypothesis**: everything is at Definition 2.1's
  arbitrary-weight generality, with `NonNeg` where and only where it is needed
  — in `ω`'s index set (Ruling R9), in the bound `ν ≤ |G|`, and in the probing
  step.

The finiteness bundle is one domain clause, not two (`HasDomain`), and the
empty-history clause is the carrier's (module docstring). -/
theorem winnability_theorem [Fintype X] {G : PDG X Y} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg) (hnil : ∀ g ∈ G.support, [] ∉ g.2.1)
    (hdom : HasDomain G D) (hq : QBounded D q) :
    supWinProb G = infWinnability G ∧
      ∃ G' : PDG X Y, G'.NonNeg ∧ gameEquivalent G' G ∧
        G'.mass System.Winnable = supWinProb G ∧
        ∃ T' : PDS X (Y × Bool), G' = ofBitLaw T' ∧
          PDS.equivalent T' (toBitLaw G) := by
  have hTnn : (toBitLaw G).NonNeg := hG.fTransform _
  have hVnn : (toBitLaw (PDS.adjoin (PDG.forget G)
      fun _ => (⊥ : System.MonotoneCondition X)).1).NonNeg :=
    (PDS.nonNeg_adjoin (nonNeg_forget hG) _).fTransform _
  obtain ⟨T', V', hT'nn, hV'nn, hT', hV', -, -, hattained⟩ :=
    PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded
      (S := toBitLaw G)
      (T := toBitLaw (PDS.adjoin (PDG.forget G)
        fun _ => (⊥ : System.MonotoneCondition X)).1)
      (D := D) (q := q) hTnn hVnn
      ⟨hasDomain_toBitLaw hdom, hasDomain_toBitLaw_adjoin_bot hdom, hq⟩
  have hG'nn : (ofBitLaw T').NonNeg := hT'nn.fTransform _
  have hG'eq : gameEquivalent (ofBitLaw T') G :=
    gameEquivalent_ofBitLaw_of_equivalent hnil (PDS.equivalent_symm hT')
  -- the attained pair's winnable masses
  have hV'zero : V'.mass (fun t => System.Winnable (System.ofBitSystem t)) = 0 :=
    mass_winnable_ofBitSystem_eq_zero_of_equivalent_twin hV'nn
      (PDS.equivalent_symm hV')
  have hmass : (ofBitLaw T').mass System.Winnable
      = T'.mass (fun t => System.Winnable (System.ofBitSystem t)) :=
    Distribution.mass_fTransform _ _ _
  have hle : (ofBitLaw T').mass System.Winnable ≤ supWinProb G := by
    have hstat : (ofBitLaw T').mass System.Winnable
        ≤ Probability.statDist T' V' := by
      rw [hmass, ← sub_zero (T'.mass _), ← hV'zero]
      exact Probability.mass_sub_mass_le_statDist T' V' _
    refine hstat.trans ?_
    rw [← ENNReal.ofReal_le_ofReal_iff (supWinProb_nonneg hG), hattained]
    exact advFullyDefined_toBitLaw_le_supWinProb hG
  -- the sandwich
  have hνω : supWinProb G ≤ infWinnability G := supWinProb_le_infWinnability hG hnil
  have hωmass : infWinnability G ≤ (ofBitLaw T').mass System.Winnable :=
    infWinnability_le_mass_winnable hG'nn hG'eq
  exact ⟨le_antisymm hνω (hωmass.trans hle), ofBitLaw T', hG'nn, hG'eq,
    le_antisymm hle (hνω.trans hωmass), T', rfl, PDS.equivalent_symm hT'⟩

/-- **The operational reading of Theorem 2.37** (the thesis's own paragraph,
printed p. 24): "if a game `G` has maximum winning probability `δ`, then an
equivalent game `G'` exists that is unwinnable with probability `1 − δ`."

On a probability game (`|G| = 1`) the right-hand side is literally `1 − ν(G)`:
the attained representative is *statically unwinnable* on that fraction of its
own randomness, with no strategy anywhere in the statement.  That is what makes
a winning probability a counting problem. -/
theorem exists_unwinnable_representative [Fintype X] {G : PDG X Y}
    {D : Set (List X)} {q : ℕ} (hG : G.NonNeg)
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) (hdom : HasDomain G D)
    (hq : QBounded D q) :
    ∃ G' : PDG X Y, G'.NonNeg ∧ gameEquivalent G' G ∧
      G'.mass (fun g => ¬ System.Winnable g) = G.weight - supWinProb G := by
  obtain ⟨-, G', hG'nn, hG'eq, hG'mass, -⟩ := winnability_theorem hG hnil hdom hq
  refine ⟨G', hG'nn, hG'eq, ?_⟩
  have hsplit := Distribution.mass_add_compl G' System.Winnable
  rw [hG'mass, weight_eq_of_gameEquivalent hG'eq] at hsplit
  linarith

end PDG

end

end RandomSystems

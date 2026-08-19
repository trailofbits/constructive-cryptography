/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Winnability
import RandomSystems.System.FilterPhi
import Probability.Conditional

/-!
# Conditional equivalence

PAPER-FAITHFUL

Maurer, *Indistinguishability of Random Systems* (EUROCRYPT 2002; ETH
preprint, self-numbered pages), §4; Maurer, *Conditional Equivalence of Random
Systems and Indistinguishability Proofs* (ISIT 2013), printed pp. 3152–3154;
Cachin–Renner(–Maurer), *Lecture Notes on Cryptography* §4.10–4.11, printed
pp. 105–110 (historical provenance only — CR18 is fallback-only under the
source hierarchy).  Every statement cited below was read on the rendered page.

## What the technique is

Adjoin to a system `S` a monotone condition `A` — Lanzenberger Definition 2.20's
pair `S^A`, here `PDG X Y` — and compare the *not-won part* of the game's
transcript law against a second system `T`.  If the two agree, the
distinguishing advantage between `S` and `T` is at most the probability of
making the condition fire, a one-system quantity.

## The four objects

Everything is a definition over the landed observables — the game pair
(`RandomSystems.PDG`), its Definition 2.21 transcript law (`PDG.gameTrLaw`),
Definition 2.25's `ν` (`PDG.supWinProb`), the transcript law
(`PDS.trLawFullyDefined`) and Ruling R4's metric (`PDS.advFullyDefined`), and
the T0 conditioning layer (`Probability.Distribution.condProb`).  No system,
game, condition or conditioning notion is introduced here, and no `S⁻`, `Γ` or
`Γᵇ` operator exists (PHI-SPEC R11(a)).  The *blind* right-hand side of
Maurer13b Theorem 3 / CR18 Theorem 4.17 lives in `Technique/BlindWinning.lean`
and also introduces no operator: it is this same `ν` with its index set cut
down to the landed `NonAdaptive` environments.

* `PDG.notWonMass e n G` — Maurer13b's `p^S_{Aᵢ=0|Xⁱ}` (printed p. 3153): the
  mass of the not-won slice of `gameTrLaw`.
* `PDG.notWonLaw e n G` — Maurer13b's `p^S_{Yⁱ,Aᵢ=0|Xⁱ}`: that slice's
  transcript marginal, an *unnormalized* law.  Both are read off `gameTrLaw`,
  and `notWonMass + winningMass = |G|`.
* `PDG.EquivalentAsGames` — **Maurer13b Definition 11, printed p. 3153**:
  "Two `(𝒳,𝒴×{0,1})`-systems with MBO, `S` and `T`, are *equivalent as games*,
  denoted `S ≡ᵍ T`, if, for `i ≥ 1`, `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^T_{Yⁱ,Aᵢ=0|Xⁱ}`."
  The `i ≥ 1` is taken literally (`l ≠ []`); quantifying over `[]` too would be
  strictly stronger than Definition 11
  (`PDS.exists_equivalentAsGames_notWonLaw_nil_ne`).
* `PDG.CondEquiv` — **Maurer13b Definition 13, printed p. 3153**: `S|𝒜 ≡ T`
  iff `p^S_{Yⁱ|Xⁱ,Aᵢ=0} = p^T_{Yⁱ|Xⁱ}` for `i ≥ 1`, stated in the paper's own
  **division-free product form**, printed on the same page: "Since
  `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^S_{Aᵢ=0|Xⁱ}·p^S_{Yⁱ|Xⁱ,Aᵢ=0}`, the above condition is
  equivalent to `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^S_{Aᵢ=0|Xⁱ}·p^T_{Yⁱ|Xⁱ}`."
  (CR18 eq. (4.38), printed p. 108, is the same identity.)  The two normalizers
  are cleared, so the relation carries no positivity guard at all;
  `condEquiv_iff_condProb` is the guarded quotient form of Definition 13's
  first display, and it *is* Maurer13b footnote 9 / CR18 footnote 29 — "two
  conditional probability distributions are considered to be equal if they are
  equal for all arguments for which they are both defined".

## Where the fixed input sequence sits

Maurer13b Definition 13 fixes `Xⁱ` and compares conditional output laws.  On
this carrier a fixed input sequence is the non-adaptive environment
`System.DDE.Total.playQueries l` run for `l.length` moves (Lanzenberger fn. 6,
`ClassDistance.lean`), so both relations quantify over `l : List X` and nothing
else.  That the *adaptive* metric is nevertheless bounded is the content of the
endpoint, and the mechanism is the deterministic fiber factorization
(`System.DDE.Total.transcript_eq_iff_of_consistent`): the mass a transcript law
puts on a value `t` is cut out by a condition on the system alone, so the
adaptive environment's fiber at `t` is the fiber of `playQueries t↓ₓ`.  That is
the `η`-cancellation of the H-coefficient factorization, available here as a
fiber identity because environments are deterministic.

## The endpoints

Every bound is stated against `Adv⊥` (Ruling R4) with the right-hand side
written `ν[G]` — the `ℝ≥0∞` reading of Definition 2.25 declared beside
`PDG.supWinProb` in `System/Game.lean`, and `ω[G]` its Definition 2.36
companion in `System/Winnability.lean`.  The notation is display only: it
unfolds to `ENNReal.ofReal (ν(G))`, and the underlying real-valued `ν`/`ω` are
untouched.

* `PDG.fundamental_lemma_of_game_playing` —
  **Maurer13b Lemma 2, printed p. 3153**: "If `S ≡ᵍ T`, then, for any
  distinguisher `D` and any `q`, `Δ^D_q(S⁻,T⁻) ≤ Γ^D_q(S)`", the statement the
  paper says "implies the so-called fundamental lemma of game playing".
  (CR18 Lemma 4.16, printed p. 107.)  It carries `‖G‖ = ‖H‖`, which Maurer13b
  has standing (its objects are systems, hence probability distributions) and
  which Definition 11's `i ≥ 1` makes necessary — see the theorem's docstring.
* `PDG.conditional_equivalence_theorem` — **Maurer02
  Theorem 1(i), preprint p. 12**: "If `F^𝒜 ≡ G^ℬ` or `F|𝒜 ≡ G`, then
  `Δₖ(F,G) ≤ ν(F, Āₖ)`", the **adaptive** right-hand side; equivalently the
  first half of Maurer13b Theorem 3 (printed p. 3154) and of CR18 Theorem 4.17
  (printed p. 110) before their blinding step.
* `PDS.conditional_equivalence_theorem_adjoin` — the same bound
  taking the *base* system and the condition, with the game constructed in the
  statement by `PDS.adjoin`.
* `PDS.conditional_equivalence_theorem_gamesFor` — the same bound for an
  arbitrary game *for* `S` (`PDS.GamesFor`), where the forgetting law holds
  only up to Lanzenberger Definition 2.17.
* `PDG.conditional_equivalence_theorem_infWinnability` — the
  right-hand side replaced, through Lanzenberger Theorem 2.37
  (`Winnability.lean`), by `ω`: the *static* infimum winnability, in which no
  environment occurs at all.  Theorem 2.37 says `ω = ν`, so this is **not** a
  smaller bound — it is the same number presented as a counting quantity
  rather than as a supremum over strategies.  The papers' non-adaptive
  `Γ^{NA}(Ŝ)` / `Γ(bŜ)` **is** strictly smaller in general, and is **not**
  obtained here: it is
  `PDG.conditional_equivalence_theorem_blind` (`Technique/BlindWinning.lean`),
  which carries two clauses this endpoint does not (see the adaptivity note
  below).

## The receipts, and what they are evidence of

The `⊥`/`⊤` poles show the relation is satisfiable and not free, but they do
**not** pin the placement of the two scalars — see the receipts section.  The
interpolation family `PDS.condEquivInterp` is the non-degenerate witness: for
`0 < c < 1` it satisfies every hypothesis of the endpoint with
`forget G ≠ T` and `0 < ν = c·‖S₀‖ < ‖G‖`, so the endpoint is neither vacuous
nor trivial.  `PDS.exists_equivalentAsGames_notWonLaw_nil_ne` separates
Definition 11 from its `[]`-including variant.  The last two were built by the
T3 adversarial audit (`t3-audit/check2.lean`, and its §3.1 observation) and are
landed here so they travel with the definitions.  No *application* (switching
lemma, CBC-MAC, sum of permutations) is discharged in this module.

## Reading the papers against this file

* **Polarity.**  Maurer02's `Aᵢ = 1` means the condition is *satisfied*
  (good), and its Theorem 1 bounds by `ν(F, Āₖ)`, the probability of the
  *failure* event.  Maurer13b, MPR07, CR18 and this file use the opposite
  convention: the condition firing is *winning*, and `Aᵢ = 0` is the not-won
  slice.  A Maurer02 statement must be flipped before comparison.
* **One-step vs joint.**  Maurer02 Definition 6 (preprint p. 8) is the
  *one-step* form `P^F_{Yᵢ|XⁱYⁱ⁻¹Aᵢ} = P^G_{Yᵢ|XⁱYⁱ⁻¹}`.  Maurer13b
  Definition 13 and CR18 Definition 4.19 are the *joint* form
  `p_{Yⁱ|Xⁱ,Aᵢ=0}`.  `CondEquiv` is the joint form.
* **Adaptive vs blind.**  The right-hand side proved here is Definition 2.25's
  `ν` — a supremum over *all* total environments, hence adaptive, and hence
  Maurer02 Theorem 1's right-hand side.  Maurer13b Theorem 3 and CR18
  Theorem 4.17 reach the strictly stronger non-adaptive right-hand side
  through the non-adaptive distinguisher `⟦DT⟧` (printed p. 3152) or the
  reply-blocking converter `b` (CR18 Definition 4.20, printed p. 109).
  **Both are built** — in `Technique/BlindWinning.lean` and
  `System/BlockReplies.lean` respectively, and proved to agree
  (`PDG.supWinProb_blockRepliesGame`) — but not in this module, and citing
  Maurer02 for a blind right-hand side would still be a false citation.
* **Definition numbers collide across the papers**, so every citation above
  carries paper *and* printed page.

## Carrier deltas against the reference repository's proven development

The reference repository's `CondEquiv.lean`/`Theorem417.lean` chain is the
route transported here (PHI-SPEC R11(b)); three of its nodes collapse on this
carrier and are therefore absent:

* its `MonotoneMBO` hypothesis and the `massAllFalse = massAfalse` bridge —
  a `System.MonotoneCondition` is an upper set *by construction*, so "not won
  at `i`" and "not won at every prefix" are the same event
  (`System.Won.mono`);
* its `TotalOnNonempty` hypotheses — refusal is an observable answer here
  (Ruling R2), so a partial system needs no totality clause to have a
  transcript law;
* its `gameEnhance` (the `T̂` of the unnumbered enhancement display in the
  proof of CR18 Theorem 4.17, printed p. 110) and the `verdictProb` chain —
  the statement-facing metric `Adv⊥` is already a `δ`-shaped supremum of
  statistical distances of transcript laws, so the enhancement's only job,
  turning a two-game comparison into a system comparison, is not needed:
  `notWonLaw_le_trLawFullyDefined_of_condEquiv` compares `G`'s not-won law
  with `T`'s law directly.  `advFullyDefined_forget_le_supWinProb_of_notWonLaw_le` is
  the shared coupling core both endpoints factor through: the same idea as
  `Winnability.lean`'s `advFullyDefined_toBitLaw_le_supWinProb` — bound each
  fiber's excess by its winning part — carried out for *two* laws instead of
  two readings of one law.  It is not a literal generalization of that
  statement, which lives at the output alphabet `𝒴 × {0,1}`; what it shares is
  the coupling, and `Probability.statDist_fTransform_le_mass_of_eq_off` is
  unavailable here precisely because the two laws are not pushforwards of one
  distribution.
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

-- `ν[·]` and `ω[·]` (`System/Game.lean`, `System/Winnability.lean`) are the
-- `ℝ≥0∞` readings of Definitions 2.25 and 2.36 that every bound against `Adv⊥`
-- is stated in; they are scoped to `PDG` and used here from `PDS` too.
open scoped RandomSystems.PDG

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-! ## Two deterministic receipts

Both are consequences of the factorization already proved in
`ClassDistance.lean`; they are stated here because conditional equivalence is
their only consumer so far.  UPSTREAM-CANDIDATES for
`System/ClassDistance.lean`. -/

/-- **The winning event reads the run, not the environment.**  Two interactions
of one deterministic game that produce the same transcript are won together:
Lanzenberger Definition 2.25's test (printed p. 18) reads `answeredQueries` of
the transcript
and nothing else. -/
theorem won_congr_transcript {g : DDG X Y} {e e' : DDE.Total Y X} {n n' : ℕ}
    {t : List (X × Option Y)}
    (h : DDE.Total.transcript g.1 e n = t)
    (h' : DDE.Total.transcript g.1 e' n' = t) :
    Won g e n ↔ Won g e' n' := by
  unfold Won
  rw [h, h']

/-- **The fiber of an adaptive environment is the fiber of a fixed query
list.**  At a value `t` the adaptive `e` can produce, "the transcript is `t`"
is the same condition on the system as it is for the non-adaptive
`playQueries t↓ₓ` at `t`'s own length — both unfold, by
`DDE.Total.transcript_eq_iff_of_consistent`, to the system-side condition that
each entry's answer is the completion's answer.  This is the exchange step
inside `equivalent_of_nonAdaptive`, isolated. -/
theorem transcript_eq_iff_playQueries {e : DDE.Total Y X} {n : ℕ}
    {t : List (X × Option Y)}
    (hq : ∀ k, (hk : k < t.length) →
      e (transcriptOutputs (t.take k)) = some t[k].1)
    (hlen : t.length = n ∨ (t.length < n ∧ e (transcriptOutputs t) = none))
    (s : DDS X Y) :
    DDE.Total.transcript s e n = t ↔
      DDE.Total.transcript s
        (DDE.Total.playQueries (transcriptInputs t)) t.length = t := by
  rw [DDE.Total.transcript_eq_iff_of_consistent hq hlen s,
    DDE.Total.transcript_eq_iff_of_consistent
      (DDE.Total.consistent_playQueries t) (Or.inl rfl) s]

@[simp] theorem length_transcriptInputs (t : List (X × Option Y)) :
    (transcriptInputs t).length = t.length := by
  simp [transcriptInputs]

/-- The complement of Lanzenberger Definition 2.25's winning test (printed
p. 18), on the Definition 2.21 pair (printed p. 17): the not-won slice is the
transcripts ending with `(·,0)`.
`Bool`-level companion of `won_iff_gameTranscript`. -/
theorem not_won_iff_gameTranscript (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    ¬ Won g e n ↔ (gameTranscript g e n).2 = false := by
  rw [won_iff_gameTranscript]
  cases (gameTranscript g e n).2 <;> simp

/-- The condition that fires as soon as one query has been answered: the upper
set of nonempty histories.  Upward closure is immediate — an extension of a
nonempty history is nonempty.  Unlike the lattice's `⊥` and `⊤` (Lanzenberger
Definition 2.20's two poles, printed p. 17, `Game.lean`) this one fires
*during* the interaction, which is what makes it a separating witness for
Maurer13b Definition 11's `i ≥ 1` clause (printed p. 3153)
(`PDS.exists_equivalentAsGames_notWonLaw_nil_ne`). -/
def MonotoneCondition.nonNil : MonotoneCondition X :=
  ⟨{l : List X | l ≠ []}, fun _ _ hpre ht hnil => ht (List.prefix_nil.mp (hnil ▸ hpre))⟩

@[simp] theorem MonotoneCondition.mem_nonNil {l : List X} :
    l ∈ (MonotoneCondition.nonNil : MonotoneCondition X).1 ↔ l ≠ [] :=
  Iff.rfl

end System

namespace PDG

/-! ## The not-won slice of the Definition 2.21 transcript law -/

/-- Maurer13b's `p^S_{Aᵢ=0|Xⁱ}` (printed p. 3153): the mass of the *not-won*
slice of Lanzenberger Definition 2.21's game transcript law.  It is
`PDG.winningMass`'s complement (`winningMass_add_notWonMass`) and, like it, an
observable of `gameTrLaw` alone. -/
def notWonMass (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) : ℝ :=
  (gameTrLaw e n G).mass fun t => t.2 = false

/-- Maurer13b's `p^S_{Yⁱ,Aᵢ=0|Xⁱ}` (printed p. 3153): the transcript marginal
of the not-won slice of `gameTrLaw`, as an **unnormalized** law.  Its weight is
`notWonMass`, and dividing by that weight is what Definition 13's first display
does — which is exactly what the product form avoids. -/
def notWonLaw (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) :
    Distribution (List (X × Option Y)) :=
  Distribution.fTransform Prod.fst ((gameTrLaw e n G).restrict fun t => t.2 = false)

theorem notWonMass_eq_mass_not_won (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) :
    notWonMass e n G = G.mass fun g => ¬ System.Won g e n := by
  rw [notWonMass, gameTrLaw, Distribution.mass_fTransform]
  exact Distribution.mass_congr _ fun g =>
    (System.not_won_iff_gameTranscript g e n).symm

/-- The not-won law read at one transcript value: the mass of the realizations
that produce it without winning. -/
theorem notWonLaw_apply (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y)
    (t : List (X × Option Y)) :
    notWonLaw e n G t
      = G.mass fun g =>
          ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t := by
  rw [notWonLaw, Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict,
    gameTrLaw, Distribution.mass_fTransform]
  refine Distribution.mass_congr _ fun g => ?_
  rw [System.not_won_iff_gameTranscript g e n]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- The same, kept in `gameTrLaw` form: the numerator of Maurer13b Definition
13's first display (printed p. 3153), before any normalizer is cleared. -/
theorem notWonLaw_apply_eq_mass_gameTrLaw (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) (t : List (X × Option Y)) :
    notWonLaw e n G t
      = (gameTrLaw e n G).mass fun p => p.1 = t ∧ p.2 = false := by
  rw [notWonLaw, Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict]

@[simp] theorem weight_notWonLaw (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) : (notWonLaw e n G).weight = notWonMass e n G := by
  rw [notWonLaw, Distribution.weight_fTransform, Distribution.weight_restrict,
    notWonMass]

theorem nonNeg_notWonLaw {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : (notWonLaw e n G).NonNeg :=
  ((hG.fTransform _).restrict _).fTransform _

/-- Lanzenberger Definition 2.25's winning mass (printed p. 18) and the not-won
mass partition the game's weight. -/
theorem winningMass_add_notWonMass (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) :
    winningMass e n G + notWonMass e n G = G.weight := by
  rw [notWonMass_eq_mass_not_won]
  exact Distribution.mass_add_compl G _

theorem notWonMass_nonneg {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : 0 ≤ notWonMass e n G := by
  rw [notWonMass_eq_mass_not_won]; exact hG.mass_nonneg _

theorem notWonMass_le_weight {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : notWonMass e n G ≤ G.weight := by
  rw [notWonMass_eq_mass_not_won]; exact Distribution.mass_le_weight hG _

/-- **The not-won law is dominated by the system's own transcript law.**
Dropping the condition can only add mass: the not-won realizations producing a
transcript are among all the realizations producing it. -/
theorem notWonLaw_le_trLawFullyDefined_forget {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)) :
    notWonLaw e n G t ≤ PDS.trLawFullyDefined e n (forget G) t := by
  rw [notWonLaw_apply, PDS.trLawFullyDefined, forget,
    Distribution.fTransform_fTransform, Distribution.fTransform_apply_eq_mass]
  exact Distribution.mass_mono hG fun g hg => hg.2

theorem notWonLaw_le_weight {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)) :
    notWonLaw e n G t ≤ G.weight := by
  rw [notWonLaw_apply]
  exact Distribution.mass_le_weight hG _

/-- Before the first move every realization has produced the empty transcript,
so the length-`0` transcript law is `S`'s weight concentrated at `[]`.  This is
the index at which Maurer13b Definition 11's `i ≥ 1` clause (printed p. 3153)
bites (`EquivalentAsGames`
says nothing there, and the honest weight hypothesis carries the step
instead). -/
theorem trLawFullyDefined_zero_apply_nil (e : System.DDE.Total Y X)
    (S : PDS X Y) :
    PDS.trLawFullyDefined e 0 S ([] : List (X × Option Y)) = S.weight := by
  rw [PDS.trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
  exact (Distribution.mass_congr S
    (P := fun s => System.DDE.Total.transcript s e 0 = ([] : List (X × Option Y)))
    (Q := fun _ => True) (fun _ => iff_of_true rfl trivial)).trans
      (Distribution.mass_true S)

/-! ## Maurer13b Definition 11 and Definition 13 -/

/-- **Maurer13b Definition 11** (printed p. 3153): "Two `(𝒳,𝒴×{0,1})`-systems
with MBO, `S` and `T`, are *equivalent as games*, denoted `S ≡ᵍ T`, if, for
`i ≥ 1`, `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^T_{Yⁱ,Aᵢ=0|Xⁱ}`."  (CR18 Definition 4.16,
printed p. 105.)

The fixed input sequence `Xⁱ` is the non-adaptive environment
`playQueries l` at its own length, as the module docstring explains, and the
**`i ≥ 1` restriction is taken literally**: `l` ranges over the *nonempty*
query lists only.  That is not cosmetic — the `[]` instance would additionally
demand that the two games have the same *already-won* mass at the empty
history, which Definition 11 does not ask and which the `i ≥ 1` family does not
imply (`PDS.exists_equivalentAsGames_notWonLaw_nil_ne`).  Definition 13
(printed p. 3153) is the opposite case: there the `[]` instance is an
unconditional identity (`smul_notWonLaw_nil`), which is why `CondEquiv`
quantifies over every `l`.

This is *weaker* than Lanzenberger Definition 2.22 (printed p. 17,
`PDG.gameEquivalent`),
which compares the whole game transcript law: the two games may differ freely
after the condition has fired (`equivalentAsGames_of_gameEquivalent`). -/
def EquivalentAsGames (G H : PDG X Y) : Prop :=
  ∀ l : List X, l ≠ [] →
    notWonLaw (System.DDE.Total.playQueries l) l.length G
      = notWonLaw (System.DDE.Total.playQueries l) l.length H

@[inherit_doc EquivalentAsGames]
scoped notation:50 G " ≡ᵍ " H => EquivalentAsGames G H

theorem equivalentAsGames_refl (G : PDG X Y) : EquivalentAsGames G G :=
  fun _ _ => rfl

theorem EquivalentAsGames.symm {G H : PDG X Y} (h : EquivalentAsGames G H) :
    EquivalentAsGames H G := fun l hl => (h l hl).symm

theorem EquivalentAsGames.trans {G H K : PDG X Y} (h : EquivalentAsGames G H)
    (h' : EquivalentAsGames H K) : EquivalentAsGames G K :=
  fun l hl => (h l hl).trans (h' l hl)

/-- Lanzenberger Definition 2.22 (printed p. 17) refines Maurer13b Definition 11
(printed p. 3153): agreeing on
the *whole* game transcript law in every environment implies agreeing on the
not-won slice at the fixed query lists. -/
theorem equivalentAsGames_of_gameEquivalent {G H : PDG X Y}
    (h : gameEquivalent G H) : EquivalentAsGames G H := fun l _ => by
  rw [notWonLaw, notWonLaw, h]

/-- **Maurer13b Definition 13** (printed p. 3153), in the paper's own
division-free product form: `S|𝒜 ≡ T` iff
`p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^S_{Aᵢ=0|Xⁱ} · p^T_{Yⁱ|Xⁱ}` for `i ≥ 1`.  (CR18
eq. (4.38), printed p. 108.)  Maurer13b Definition 13 is on printed p. 3153.

`p^T_{Yⁱ|Xⁱ}` is a *normalized* conditional law in the papers, while
`PDS.trLawFullyDefined` carries `T`'s weight; the definition therefore clears
`T`'s normalizer as well, which is what makes it hold with no positivity guard
anywhere.  On the intended objects (`T.weight = 1`) the left factor is `1`.

`condEquiv_iff_condProb` is the guarded quotient form — Definition 13's first
display read through the T0 conditioning layer, with Maurer13b footnote 9's
"equal for all arguments for which they are both defined" (printed p. 3153) as
the two guards. -/
def CondEquiv (G : PDG X Y) (T : PDS X Y) : Prop :=
  ∀ l : List X,
    T.weight • notWonLaw (System.DDE.Total.playQueries l) l.length G
      = notWonMass (System.DDE.Total.playQueries l) l.length G
          • PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T

@[inherit_doc CondEquiv]
scoped notation:50 G " |≡ " T => CondEquiv G T

/-- **The index the papers exclude carries no information — for Definition 13.**
Maurer13b Definition 13 (printed p. 3153) and CR18 Definition 4.19 (printed
p. 108) both quantify over `i ≥ 1`,
while `CondEquiv` quantifies over every query list, `[]` included.  Nothing is
strengthened: at the empty query list the interaction is the empty transcript in
every realization, so both sides of the product form are the **not-yet-won**
mass at the empty history times `T`'s weight, concentrated at `[]`.  The two
quantifications therefore define the same relation.

The reason this works is that Definition 13's `[]` instance compares `G` with
*itself* — `notWonMass` occurs on both sides.  Definition 11 (printed p. 3153)
compares two different games, and there the `[]` instance is a real constraint,
which is why
`EquivalentAsGames` carries `l ≠ []`
(`PDS.exists_equivalentAsGames_notWonLaw_nil_ne`). -/
theorem smul_notWonLaw_nil (G : PDG X Y) (T : PDS X Y) :
    T.weight • notWonLaw (System.DDE.Total.playQueries ([] : List X))
        ([] : List X).length G
      = notWonMass (System.DDE.Total.playQueries ([] : List X))
          ([] : List X).length G
        • PDS.trLawFullyDefined (System.DDE.Total.playQueries ([] : List X))
          ([] : List X).length T := by
  ext t
  rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
    notWonLaw_apply, notWonMass_eq_mass_not_won, PDS.trLawFullyDefined,
    Distribution.fTransform_apply_eq_mass]
  by_cases h : ([] : List (X × Option Y)) = t
  · rw [Distribution.mass_congr G
      (Q := fun g => ¬ System.Won g (System.DDE.Total.playQueries ([] : List X))
        ([] : List X).length)
      (fun g => ⟨fun hg => hg.1, fun hg => ⟨hg, h⟩⟩),
      Distribution.mass_congr T
        (P := fun a : System.DDS X Y =>
          System.DDE.Total.transcript a
            (System.DDE.Total.playQueries ([] : List X)) ([] : List X).length = t)
        (Q := fun _ => True) (fun _ => iff_of_true h trivial),
      Distribution.mass_true, mul_comm]
  · rw [Distribution.mass_eq_zero_of_forall_not G
      (P := fun g : System.DDG X Y =>
        ¬ System.Won g (System.DDE.Total.playQueries ([] : List X))
            ([] : List X).length ∧
          System.DDE.Total.transcript g.1
            (System.DDE.Total.playQueries ([] : List X)) ([] : List X).length = t)
      (fun g hg => h hg.2),
      Distribution.mass_eq_zero_of_forall_not T
        (P := fun a : System.DDS X Y =>
          System.DDE.Total.transcript a
            (System.DDE.Total.playQueries ([] : List X)) ([] : List X).length = t)
        (fun _ hs => h hs),
      mul_zero, mul_zero]

/-- The definition read at one output transcript: Maurer13b Definition 13's
product form (printed p. 3153), pointwise. -/
theorem condEquiv_apply {G : PDG X Y} {T : PDS X Y} (h : CondEquiv G T)
    (l : List X) (t : List (X × Option Y)) :
    T.weight * notWonLaw (System.DDE.Total.playQueries l) l.length G t
      = notWonMass (System.DDE.Total.playQueries l) l.length G
          * PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t := by
  have := congrArg (fun d : Distribution (List (X × Option Y)) => d t) (h l)
  simpa using this

/-- Conditional equivalence to `T` is a statement about the not-won slice
alone, so it transports along Maurer13b Definition 11 (printed p. 3153).
Maurer13b uses exactly this move inside Theorem 3 (printed p. 3154,
"`Γ^D_q(Ŝ) = Γ^D_q(T̂)` by Lemma 1", printed p. 3153).  The `i = 0` index
Definition 11 omits costs nothing: there the product form is an identity for
*every* game (`smul_notWonLaw_nil`). -/
theorem CondEquiv.congr_equivalentAsGames {G H : PDG X Y} {T : PDS X Y}
    (h : CondEquiv G T) (hGH : EquivalentAsGames G H) : CondEquiv H T := by
  intro l
  rcases eq_or_ne l ([] : List X) with rfl | hl
  · exact smul_notWonLaw_nil H T
  · have hmass : notWonMass (System.DDE.Total.playQueries l) l.length G
        = notWonMass (System.DDE.Total.playQueries l) l.length H := by
      rw [← weight_notWonLaw, ← weight_notWonLaw, hGH l hl]
    rw [← hGH l hl, ← hmass]
    exact h l

end PDG

/-! ## The coupling core

One inequality carries both endpoints: if at every fixed query list the game's
not-won law is pointwise dominated by `T`'s transcript law, then the *adaptive*
`Adv⊥` is at most Definition 2.25's `ν`.  The reference repository reaches the
same place through the enhanced game `T̂` of CR18 Theorem 4.17's proof (the
unnumbered display above eq. (4.39), printed p. 110) and a verdict-probability
chain; on this carrier `Adv⊥` is already a supremum of statistical distances of
transcript laws, so the comparison is direct (module docstring, carrier
deltas). -/

namespace PDG

/-- **The coupling core**, at one environment and one interaction length.

The three moves are: split each transcript value's mass by whether the game was
won (`Distribution.mass_and_add_mass_not_and`); exchange the adaptive
environment for the fixed query list `t↓ₓ` on the fiber over `t`
(`System.transcript_eq_iff_playQueries`, and `System.won_congr_transcript` for
the winning event, which is where the environment's adaptivity is spent); and
sum the won parts back over the fibers
(`Distribution.mass_eq_sum_mass_fiber`).

This generalizes `Winnability.lean`'s `advFullyDefined_toBitLaw_le_supWinProb`,
which is the case of one law read two ways
(`Probability.statDist_fTransform_le_mass_of_eq_off`), to two laws compared
through the not-won slice. -/
theorem statDist_trLawFullyDefined_forget_le_winningMass {G : PDG X Y}
    {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg)
    (hle : ∀ t : List (X × Option Y),
      notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
          t.length G t
        ≤ PDS.trLawFullyDefined
            (System.DDE.Total.playQueries (System.transcriptInputs t))
            t.length T t)
    (e : System.DDE.Total Y X) (n : ℕ) :
    statDist (PDS.trLawFullyDefined e n (forget G))
        (PDS.trLawFullyDefined e n T)
      ≤ winningMass e n G := by
  classical
  set μ := PDS.trLawFullyDefined e n (forget G) with hμdef
  set ν := PDS.trLawFullyDefined e n T with hνdef
  have hμ : μ = Distribution.fTransform
      (fun g => System.DDE.Total.transcript g.1 e n) G := by
    rw [hμdef, PDS.trLawFullyDefined, forget, Distribution.fTransform_fTransform]
    rfl
  have hνnn : ν.NonNeg := by rw [hνdef, PDS.trLawFullyDefined]; exact hT.fTransform _
  set s : Finset (List (X × Option Y)) :=
    (G.support.image fun g => System.DDE.Total.transcript g.1 e n) ∪ (μ - ν).support
    with hsdef
  have hsub : (μ - ν).support ⊆ s := Finset.subset_union_right
  have hcover : ∀ g ∈ G.support,
      System.DDE.Total.transcript g.1 e n ∈ s := fun g hg =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hg)
  have hterm : ∀ t ∈ s, max (μ t - ν t) 0
      ≤ G.mass fun g =>
          System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t := by
    intro t _
    by_cases hE : (∀ k, (hk : k < t.length) →
          e (System.transcriptOutputs (t.take k)) = some t[k].1) ∧
        (t.length = n ∨
          (t.length < n ∧ e (System.transcriptOutputs t) = none))
    · have hfib : ∀ u : System.DDS X Y,
          System.DDE.Total.transcript u e n = t ↔
            System.DDE.Total.transcript u
              (System.DDE.Total.playQueries (System.transcriptInputs t))
              t.length = t :=
        fun u => System.transcript_eq_iff_playQueries hE.1 hE.2 u
      have hsplit : μ t
          = (G.mass fun g =>
              System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t)
            + G.mass fun g =>
              ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t := by
        rw [hμ, Distribution.fTransform_apply_eq_mass]
        exact (Distribution.mass_and_add_mass_not_and G _ _).symm
      have hnw : (G.mass fun g =>
            ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t)
          ≤ ν t := by
        have hrewrite : (G.mass fun g =>
              ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t)
            = notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
                t.length G t := by
          rw [notWonLaw_apply]
          refine Distribution.mass_congr G fun g => ?_
          constructor
          · rintro ⟨hw, ht⟩
            have ht' := (hfib g.1).mp ht
            exact ⟨fun hc =>
              hw ((System.won_congr_transcript ht ht').mpr hc), ht'⟩
          · rintro ⟨hw, ht'⟩
            have ht := (hfib g.1).mpr ht'
            exact ⟨fun hc =>
              hw ((System.won_congr_transcript ht ht').mp hc), ht⟩
        have hν : ν t
            = PDS.trLawFullyDefined
                (System.DDE.Total.playQueries (System.transcriptInputs t))
                t.length T t := by
          rw [hνdef, PDS.trLawFullyDefined, PDS.trLawFullyDefined,
            Distribution.fTransform_apply_eq_mass,
            Distribution.fTransform_apply_eq_mass]
          exact Distribution.mass_congr T fun u => hfib u
        rw [hrewrite, hν]
        exact hle t
      refine max_le ?_ (hG.mass_nonneg _)
      rw [hsplit]
      linarith
    · have hz : μ t = 0 := by
        rw [hμ, Distribution.fTransform_apply_eq_mass]
        refine Distribution.mass_eq_zero_of_forall_not G fun g hcontra => ?_
        subst hcontra
        exact hE ⟨(System.DDE.Total.transcript_consistent g.1 e n).1.1,
          (System.DDE.Total.transcript_consistent g.1 e n).1.2⟩
      have : max (μ t - ν t) 0 = 0 := by
        rw [hz]
        exact max_eq_right (by linarith [hνnn t])
      rw [this]
      exact hG.mass_nonneg _
  calc statDist μ ν = ∑ t ∈ s, max (μ t - ν t) 0 :=
        Probability.statDist_eq_sum_of_support_subset μ ν hsub
    _ ≤ ∑ t ∈ s, G.mass fun g =>
          System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t :=
        Finset.sum_le_sum hterm
    _ = G.mass fun g => System.Won g e n :=
        (Distribution.mass_eq_sum_mass_fiber G _ _ s hcover).symm
    _ = winningMass e n G := rfl

/-- **The coupling core at the metric.**  Pointwise domination of the not-won
law at every fixed query list bounds the *adaptive* `Adv⊥` by Lanzenberger
Definition 2.25's `ν` (printed p. 18). -/
theorem advFullyDefined_forget_le_supWinProb_of_notWonLaw_le {G : PDG X Y} {T : PDS X Y}
    (hG : G.NonNeg) (hT : T.NonNeg)
    (hle : ∀ t : List (X × Option Y),
      notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
          t.length G t
        ≤ PDS.trLawFullyDefined
            (System.DDE.Total.playQueries (System.transcriptInputs t))
            t.length T t) :
    PDS.advFullyDefined (forget G) T ≤ ν[G] := by
  refine iSup_le fun e => iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
  exact (statDist_trLawFullyDefined_forget_le_winningMass hG hT hle e n).trans
    (winningMass_le_supWinProb hG e n)

/-! ## Maurer13b Lemma 2 — the fundamental lemma of game playing -/

/-- **Maurer13b Lemma 2** (printed p. 3153): "If `S ≡ᵍ T`, then, for any
distinguisher `D` and any `q`, `Δ^D_q(S⁻,T⁻) ≤ Γ^D_q(S)`."  The paper adds:
"It implies the so-called 'fundamental lemma of game playing' [Bellare–Rogaway]
which is stated (and proved) only for a specific type of system description."
(CR18 Lemma 4.16, printed p. 107, in its `⟨S⁻|T⁻⟩ ≤ S̄` form.)

Here `S⁻` is `PDG.forget` — Maurer13b **Definition 12** (printed p. 3153):
"`S⁻` … the `(𝒳,𝒴)`-system resulting from `S` by ignoring the MBO, i.e.
`p^{S⁻}_{Yⁱ|Xⁱ} = p^S_{Yⁱ|Xⁱ}`", the *marginal*, not an operator with content
(CR18 Definition 4.18, printed p. 107, is the same, as provenance).  PHI-SPEC
R11(a) bars `S⁻` as an operator; the landed `forget = fTransform Prod.fst` is
exactly Definition 12's marginal.  The advantage is Ruling R4's `Adv⊥`, and
`Γ^D_q` is Lanzenberger Definition 2.25's `ν` (printed p. 18) — one number
rather than a per-distinguisher family, since `Adv⊥` already takes the
supremum.

**The weight hypothesis is not decoration.**  Definition 11 (printed p. 3153)
constrains only
`i ≥ 1`, so it says nothing at the empty history, where the two transcript laws
are `‖G‖·δ_[]` and `‖H‖·δ_[]`: at `n = 0` the statement reads
`max(‖G‖ − ‖H‖, 0) ≤ ν(G)` and is false for a heavy `G` against a light `H`.
Maurer13b states Lemma 2 for *systems*, i.e. probability distributions, so
`‖G‖ = ‖H‖` is its own standing hypothesis; it is also the bundle `Adv⊥`'s
symmetry needs (`advFullyDefined_comm_of_weight_eq`) and the one the
Definition 13 endpoint (printed p. 3153) already carries. -/
theorem fundamental_lemma_of_game_playing
    {G H : PDG X Y} (hG : G.NonNeg) (hH : H.NonNeg) (hw : G.weight = H.weight)
    (h : EquivalentAsGames G H) :
    PDS.advFullyDefined (forget G) (forget H)
      ≤ ν[G] := by
  refine advFullyDefined_forget_le_supWinProb_of_notWonLaw_le hG (nonNeg_forget hH)
    fun t => ?_
  rcases eq_or_ne t ([] : List (X × Option Y)) with rfl | ht
  · -- Definition 11 is silent at `i = 0`; the weight hypothesis carries it.
    calc notWonLaw (System.DDE.Total.playQueries
            (System.transcriptInputs ([] : List (X × Option Y))))
          ([] : List (X × Option Y)).length G ([] : List (X × Option Y))
        ≤ G.weight := notWonLaw_le_weight hG _ _ _
      _ = (forget H).weight := by rw [hw, weight_forget]
      _ = _ := (trLawFullyDefined_zero_apply_nil _ (forget H)).symm
  · have hnil : System.transcriptInputs t ≠ [] := by
      simpa [System.transcriptInputs] using ht
    have hEq := h (System.transcriptInputs t) hnil
    simp only [System.length_transcriptInputs] at hEq
    rw [hEq]
    exact notWonLaw_le_trLawFullyDefined_forget hH _ _ t

/-! ## Maurer02 Theorem 1 / Maurer13b Theorem 3 — the adaptive endpoint -/

/-- Conditional equivalence, read as the domination the coupling core wants:
the not-won law is `p^S_{Aᵢ=0|Xⁱ}/|T|` times `T`'s transcript law, and that
factor is at most one on games and systems of equal weight. -/
theorem notWonLaw_le_trLawFullyDefined_of_condEquiv {G : PDG X Y} {T : PDS X Y}
    (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hCE : CondEquiv G T) (l : List X) (t : List (X × Option Y)) :
    notWonLaw (System.DDE.Total.playQueries l) l.length G t
      ≤ PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t := by
  have hTw : 0 ≤ T.weight := by
    rw [← Distribution.mass_true T]; exact hT.mass_nonneg _
  have hνnn : (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T).NonNeg := by
    rw [PDS.trLawFullyDefined]; exact hT.fTransform _
  rcases eq_or_lt_of_le hTw with hzero | hpos
  · -- degenerate weight: both sides vanish
    have hGw : G.weight = 0 := by rw [hw, ← hzero]
    have hleft : notWonLaw (System.DDE.Total.playQueries l) l.length G t ≤ 0 := by
      rw [notWonLaw_apply]
      exact le_trans (Distribution.mass_le_weight hG _) (le_of_eq hGw)
    exact hleft.trans (hνnn t)
  · have hkey := condEquiv_apply hCE l t
    have hmass : notWonMass (System.DDE.Total.playQueries l) l.length G ≤ T.weight :=
      (notWonMass_le_weight hG _ _).trans (le_of_eq hw)
    have hstep :
        T.weight * notWonLaw (System.DDE.Total.playQueries l) l.length G t
          ≤ T.weight
            * PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t := by
      rw [hkey]
      exact mul_le_mul_of_nonneg_right hmass (hνnn t)
    exact le_of_mul_le_mul_left hstep hpos

/-- **Maurer02 Theorem 1(i)** (ETH preprint, printed p. 12): "If `F^𝒜 ≡ G^ℬ` or
`F|𝒜 ≡ G`, then `Δₖ(F,G) ≤ ν(F, Āₖ)`" — the **adaptive** right-hand side.
Equivalently the first half of **Maurer13b Theorem 3** (printed p. 3154), "If
for an `(𝒳,𝒴)`-system `S` one can define an MBO `A₀,A₁,…` such that
`Ŝ|𝒜 ≡ T`, then, for every `D`, `Δ^D_q(S,T) ≤ Γ^{⟦DT⟧}_q(Ŝ)`", and of **CR18
Theorem 4.17** (printed p. 110), before either takes its blinding step.

Reading the statement: `S = Ŝ⁻` is `PDG.forget G`, `Δ` is Ruling R4's `Adv⊥`,
and `ν(F, Āₖ)` is Lanzenberger Definition 2.25's `ν` (printed p. 18) after the
Maurer02 polarity flip (his
`Aᵢ = 1` is the condition *satisfied*; the condition firing is winning here).
The right-hand side is a supremum over *all* total environments, hence
adaptive; the papers' non-adaptive `Γ^{NA}`/`Γ(bŜ)` is the separate endpoint
`PDG.conditional_equivalence_theorem_blind` (`Technique/BlindWinning.lean`),
which is strictly stronger and pays two further clauses for it.

Hypotheses: non-negativity of both laws and equal weight — the honest bundle
`Adv⊥`'s own symmetry statement carries (`advFullyDefined_comm_of_weight_eq`),
and satisfied by any pair of probability laws.  No query bound, no `Fintype`,
no totality clause: refusal is an observable answer (Ruling R2) and the
condition's monotonicity is the carrier's (module docstring). -/
theorem conditional_equivalence_theorem {G : PDG X Y}
    {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ ν[G] := by
  refine advFullyDefined_forget_le_supWinProb_of_notWonLaw_le hG hT fun t => ?_
  have h := notWonLaw_le_trLawFullyDefined_of_condEquiv hG hT hw hCE
    (System.transcriptInputs t) t
  simpa using h

/-- **The right-hand side with no strategy in it.**  Lanzenberger Theorem 2.37
(`Winnability.lean`, printed p. 24) identifies Definition 2.25's adversarial
`ν` (printed p. 18) with Definition 2.36's *static* `ω` (printed p. 24) — the
infimum, over the game's own equivalence class, of the mass of realizations
that are winnable at all.
Composing it with the endpoint replaces the supremum over environments by a
counting quantity: no environment, adaptive or blind, occurs on the right.

**This is not a smaller bound.**  Theorem 2.37 is an equality, so `ω` is the
*adaptive* number written differently — which is the whole point (a winning
probability becomes a counting problem), but it must not be read as the papers'
non-adaptive right-hand side.  Maurer13b Theorem 3's `Γ^{NA}_q(Ŝ)` (printed
p. 3154) and CR18 Theorem 4.17's `Γ(bŜ)` (printed p. 110) satisfy
`Γ^{NA} ≤ Γ = ν = ω` and are strictly smaller
in general; they are reached by `PDG.conditional_equivalence_theorem_blind`
(`Technique/BlindWinning.lean`), at the price of a normalized `T` and one
shared Lanzenberger Definition 2.14 domain (printed p. 15).

The finiteness bundle is Theorem 2.37's own — one domain clause, a query
bound, `[Fintype X]`, and the empty-history clause the pair carrier needs. -/
theorem conditional_equivalence_theorem_infWinnability [Fintype X]
    {G : PDG X Y} {T : PDS X Y} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) (hdom : HasDomain G D)
    (hq : QBounded D q) (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ ω[G] := by
  rw [← (winnability_theorem hG hnil hdom hq).1]
  exact conditional_equivalence_theorem hG hT hw hCE

/-! ## Definition 13's first display, through the T0 conditioning layer -/

/-- **Maurer13b Definition 13 as printed, with its footnote** (printed
p. 3153).  Definition 13's first display is the equality of two *conditional*
laws,
`p^S_{Yⁱ|Xⁱ,Aᵢ=0} = p^T_{Yⁱ|Xⁱ}`, and footnote 9 (printed p. 3153) reads: "Two
conditional probability distributions are considered to be equal if they are
equal for all arguments for which they are both defined.  (Here one considers
only `xⁱ` for which `Aᵢ` has non-zero probability.)"  CR18 footnote 29 (printed
p. 108) is the same sentence.

That is exactly this statement: the two guards are the two normalizers, the
conditioning is T0's `Probability.Distribution.condProb` (never re-rolled), and
the equivalence with the product form `CondEquiv` is T0's cross-multiplication
lemma `condProb_eq_condProb_iff_mul_eq_mul`.  The right-hand conditional
divides by `T`'s weight — conditioning on the whole space, T0's
`condProb_true` — which is how `p^T_{Yⁱ|Xⁱ}`'s normalization enters.

The equivalence is genuine, not one-directional: off the guards both sides of
the product form vanish on a non-negative carrier, so the guarded conditional
statement loses nothing. -/
theorem condEquiv_iff_condProb {G : PDG X Y} {T : PDS X Y} (hG : G.NonNeg)
    (hT : T.NonNeg) :
    CondEquiv G T ↔
      ∀ l : List X,
        notWonMass (System.DDE.Total.playQueries l) l.length G ≠ 0 →
        T.weight ≠ 0 →
        ∀ t : List (X × Option Y),
          (gameTrLaw (System.DDE.Total.playQueries l) l.length G).condProb
              (fun p => p.1 = t) (fun p => p.2 = false)
            = (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T).condProb
              (fun u => u = t) (fun _ => True) := by
  have hTmass : ∀ l : List X,
      (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T).mass
        (fun _ => True) = T.weight := fun l => by
    rw [Distribution.mass_true, PDS.weight_trLawFullyDefined]
  have hpoint : ∀ (l : List X) (t : List (X × Option Y)),
      (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T).mass
          (fun u => u = t ∧ True)
        = PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t :=
    fun l t => by
      rw [Distribution.mass_congr _ (Q := fun u => u = t) fun u => by simp,
        Distribution.mass_singleton]
  have hiff : ∀ (l : List X),
      notWonMass (System.DDE.Total.playQueries l) l.length G ≠ 0 → T.weight ≠ 0 →
      ∀ t : List (X × Option Y),
        ((gameTrLaw (System.DDE.Total.playQueries l) l.length G).condProb
            (fun p => p.1 = t) (fun p => p.2 = false)
          = (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T).condProb
            (fun u => u = t) (fun _ => True))
        ↔ notWonLaw (System.DDE.Total.playQueries l) l.length G t * T.weight
            = PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t
              * notWonMass (System.DDE.Total.playQueries l) l.length G := by
    intro l hR hS t
    rw [Distribution.condProb_eq_condProb_iff_mul_eq_mul _ _ _ _ _ _ hR
      (by rw [hTmass l]; exact hS), notWonLaw_apply_eq_mass_gameTrLaw, hTmass l,
      hpoint l t]
    rfl
  constructor
  · intro h l hR hS t
    rw [hiff l hR hS t]
    have hkey := condEquiv_apply h l t
    linarith
  · intro h l
    ext t
    rw [Finsupp.smul_apply, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul]
    by_cases hR : notWonMass (System.DDE.Total.playQueries l) l.length G = 0
    · have hzero : notWonLaw (System.DDE.Total.playQueries l) l.length G t = 0 := by
        refine le_antisymm ?_ (nonNeg_notWonLaw hG _ _ t)
        rw [notWonLaw_apply, ← hR, notWonMass_eq_mass_not_won]
        exact Distribution.mass_mono hG fun g hg => hg.1
      rw [hR, hzero, mul_zero, zero_mul]
    · by_cases hS : T.weight = 0
      · have hνnn : (PDS.trLawFullyDefined (System.DDE.Total.playQueries l)
            l.length T).NonNeg := by
          rw [PDS.trLawFullyDefined]; exact hT.fTransform _
        have hzero : PDS.trLawFullyDefined (System.DDE.Total.playQueries l)
            l.length T t = 0 := by
          refine le_antisymm ?_ (hνnn t)
          rw [← Distribution.mass_singleton _ t, ← hS, ← PDS.weight_trLawFullyDefined
            (System.DDE.Total.playQueries l) l.length T]
          exact Distribution.mass_le_weight hνnn _
        rw [hS, hzero, mul_zero, zero_mul]
      · have := (hiff l hR hS t).mp (h l hR hS t)
        linarith

end PDG

/-! ## Transport through a converter

CR18 proves conditional equivalence for a pair of systems and then *applies a
converter to both sides* without further comment: "Hence we have proved (6.2),
which is of course still true when both systems are restricted by `θ_r`"
(**printed p. 127**, equation (6.3)), and again in the proof of Theorem 6.2,
"This is of course still true when the systems are restricted by `[r]`, i.e.,
`[r]casc[Ŝ,R_{m,n}] ⊨ [r]V_n`" (**printed p. 128**).

The step is free in the source because its systems *are* conditional
distributions, so restricting the input alphabet restricts the family.  Here a
converter is a map on deterministic systems and `CondEquiv` (Maurer13b
Definition 13, printed p. 3153) is a statement about the *not-won slice* of the
Definition 2.21 transcript law at each fixed query list.  Applying a converter
changes which queries reach the system, so the relation has to be carried
through the converter's **absorption witness** — the same data
`PDS.advFullyDefined_fTransform_le` (`System/Absorb.lean`) consumes, and this
proof is that one's architecture with the metric replaced by the two laws.

The witness must say two things at each *outer* query list `l'`, uniformly in
the deterministic system: which *inner* query list `l` the converter produces,
and how the outer transcript is read off the inner one (`p`).  With those, both
sides of Definition 13's product form are pushforwards along the same `p`, and
pushforward is `ℝ`-linear, so the identity transports verbatim.  Nothing else
is needed: no positivity, no weight condition, no hypothesis on the
condition. -/

namespace PDG

namespace Plumbing

/-- Restriction reads its predicate on the support only. -/
theorem restrict_congr {A : Type*} (D : Distribution A) {P Q : A → Prop}
    (h : ∀ a ∈ D.support, P a ↔ Q a) : D.restrict P = D.restrict Q := by
  ext a
  rw [Distribution.restrict_apply, Distribution.restrict_apply]
  by_cases ha : a ∈ D.support
  · by_cases hP : P a
    · rw [if_pos hP, if_pos ((h a ha).mp hP)]
    · rw [if_neg hP, if_neg (fun hQ => hP ((h a ha).mpr hQ))]
  · have hzero : D a = 0 := by simpa using ha
    rw [hzero]
    simp

/-- Restricting a pushforward is the pushforward of the pulled-back
restriction. -/
theorem restrict_fTransform {A B : Type*} (f : A → B) (D : Distribution A)
    (P : B → Prop) :
    (Distribution.fTransform f D).restrict P
      = Distribution.fTransform f (D.restrict fun a => P (f a)) := by
  ext b
  rw [Distribution.restrict_apply, Distribution.fTransform_apply_eq_mass,
    Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict]
  by_cases hb : P b
  · rw [if_pos hb]
    exact (Distribution.mass_congr (P := fun a => f a = b ∧ P (f a))
      (Q := fun a => f a = b) D fun a => ⟨fun h => h.1, fun h => ⟨h, h ▸ hb⟩⟩).symm
  · rw [if_neg hb]
    exact (Distribution.mass_eq_zero_of_forall_not (P := fun a => f a = b ∧ P (f a)) D
      fun a ha => hb (ha.1 ▸ ha.2)).symm

end Plumbing

/-- **The not-won law as a pushforward of a restricted game law.**  Maurer13b's
`p^S_{Yⁱ,Aᵢ=0|Xⁱ}` (printed p. 3153) read on the realizations rather than on
`gameTrLaw`: restrict the game law to the realizations that have not won, then
push forward along the transcript.  This is the form every transport argument
uses, because both operations commute with a further pushforward. -/
theorem notWonLaw_eq_fTransform_restrict (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) :
    notWonLaw e n G
      = Distribution.fTransform (fun γ => System.DDE.Total.transcript γ.1 e n)
          (G.restrict fun γ => ¬ System.Won γ e n) := by
  rw [notWonLaw, gameTrLaw, Plumbing.restrict_fTransform,
    Distribution.fTransform_fTransform]
  refine congrArg (Distribution.fTransform _) ?_
  refine Plumbing.restrict_congr _ fun γ _ => ?_
  exact (System.not_won_iff_gameTranscript γ e n).symm

/-- **Conditional equivalence survives a converter applied to both sides** —
CR18 equation (6.3), printed p. 127 ("of course still true when both systems
are restricted by `θ_r`"), as a theorem about the absorption witness.

`g` is the converter's action on deterministic systems and `gG` its action on
the Definition 2.21 pairs; the witness `habs` supplies, for each outer query
list `l'`, an inner query list `l` and a post-processing `p` of the inner
transcript, together with the two facts that make the two slices correspond:
the outer interaction is won exactly when the inner one is, and the outer
transcript is `p` of the inner one.

**Scope of the witness.**  Only the two *equations* are support-local; the
schedule is not.  `l` and `p` are chosen before either support is quantified,
so the inner query list is one fixed list — the schedule is **non-adaptive**,
and it is the **same list for every system** in `G.support` and in
`T.support`.  A converter whose inner queries depend on the inner answers, or
whose admitted schedule genuinely differs between two systems of the support,
has no witness here and is outside this lemma.  What support-locality buys is
only that the two equations may fail off the supports.

The architecture is `PDS.advFullyDefined_fTransform_le`'s
(`System/Absorb.lean`): a witness that is uniform in the deterministic system,
then one pushforward identity per side.  What replaces the data-processing
inequality is linearity of pushforward — the two scalars of Maurer13b
Definition 13's product form (printed p. 3153) travel through `p` untouched. -/
theorem condEquiv_fTransform {X' : Type*} {Y' : Type*}
    (g : System.DDS X Y → System.DDS X' Y')
    (gG : System.DDG X Y → System.DDG X' Y')
    {G : PDG X Y} {T : PDS X Y}
    (habs : ∀ l' : List X', ∃ (l : List X)
      (p : List (X × Option Y) → List (X' × Option Y')),
        (∀ γ ∈ G.support,
          (System.Won (gG γ) (System.DDE.Total.playQueries l') l'.length ↔
              System.Won γ (System.DDE.Total.playQueries l) l.length) ∧
            System.DDE.Total.transcript (gG γ).1
                (System.DDE.Total.playQueries l') l'.length =
              p (System.DDE.Total.transcript γ.1
                (System.DDE.Total.playQueries l) l.length)) ∧
        ∀ s ∈ T.support,
          System.DDE.Total.transcript (g s)
              (System.DDE.Total.playQueries l') l'.length =
            p (System.DDE.Total.transcript s
              (System.DDE.Total.playQueries l) l.length))
    (h : CondEquiv G T) :
    CondEquiv (Distribution.fTransform gG G) (Distribution.fTransform g T) := by
  intro l'
  obtain ⟨l, p, hgame, hsys⟩ := habs l'
  have hlaw :
      notWonLaw (System.DDE.Total.playQueries l') l'.length
          (Distribution.fTransform gG G)
        = Distribution.fTransform p
            (notWonLaw (System.DDE.Total.playQueries l) l.length G) := by
    rw [notWonLaw_eq_fTransform_restrict, notWonLaw_eq_fTransform_restrict,
      Plumbing.restrict_fTransform, Distribution.fTransform_fTransform,
      Distribution.fTransform_fTransform,
      Plumbing.restrict_congr G (Q := fun γ =>
        ¬ System.Won γ (System.DDE.Total.playQueries l) l.length)
        (fun γ hγ => not_congr (hgame γ hγ).1)]
    refine Distribution.fTransform_congr _ fun γ hγ => ?_
    have hγG : γ ∈ G.support := by
      have hne := Finsupp.mem_support_iff.mp hγ
      refine Finsupp.mem_support_iff.mpr fun h0 => hne ?_
      rw [Distribution.restrict_apply, h0]
      exact ite_self 0
    exact (hgame γ hγG).2
  have hmass :
      notWonMass (System.DDE.Total.playQueries l') l'.length
          (Distribution.fTransform gG G)
        = notWonMass (System.DDE.Total.playQueries l) l.length G := by
    rw [← weight_notWonLaw, ← weight_notWonLaw, hlaw, Distribution.weight_fTransform]
  have htr :
      PDS.trLawFullyDefined (System.DDE.Total.playQueries l') l'.length
          (Distribution.fTransform g T)
        = Distribution.fTransform p
            (PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T) := by
    rw [PDS.trLawFullyDefined, PDS.trLawFullyDefined,
      Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
    exact Distribution.fTransform_congr _ hsys
  rw [hlaw, hmass, htr, Distribution.weight_fTransform,
    ← Distribution.fTransform_smul, ← Distribution.fTransform_smul, h l]

/-- **The transport at an unchanged condition.**  When the converter leaves the
query alphabet alone and the monotone condition is carried over unchanged — the
shape CR18 uses, where `θ_r Ŝ` is the augmented system behind the restriction
converter — the winning clause of `condEquiv_fTransform` is exactly the
statement that the two interactions answer the *same* queries: Lanzenberger
Definition 2.25's test (printed p. 18) reads `answeredQueries` and nothing
else. -/
theorem condEquiv_fTransform_of_answeredQueries {Y' : Type*}
    (g : System.DDS X Y → System.DDS X Y')
    {G : PDG X Y} {T : PDS X Y}
    (habs : ∀ l' : List X, ∃ (l : List X)
      (p : List (X × Option Y) → List (X × Option Y')),
        (∀ γ ∈ G.support,
          System.answeredQueries (System.DDE.Total.transcript (g γ.1)
              (System.DDE.Total.playQueries l') l'.length)
            = System.answeredQueries (System.DDE.Total.transcript γ.1
              (System.DDE.Total.playQueries l) l.length) ∧
          System.DDE.Total.transcript (g γ.1)
              (System.DDE.Total.playQueries l') l'.length =
            p (System.DDE.Total.transcript γ.1
              (System.DDE.Total.playQueries l) l.length)) ∧
        ∀ s ∈ T.support,
          System.DDE.Total.transcript (g s)
              (System.DDE.Total.playQueries l') l'.length =
            p (System.DDE.Total.transcript s
              (System.DDE.Total.playQueries l) l.length))
    (h : CondEquiv G T) :
    CondEquiv
      (Distribution.fTransform
        (fun γ : System.DDG X Y => ((g γ.1, γ.2) : System.DDG X Y')) G)
      (Distribution.fTransform g T) := by
  refine condEquiv_fTransform g _ (fun l' => ?_) h
  obtain ⟨l, p, hgame, hsys⟩ := habs l'
  refine ⟨l, p, fun γ hγ => ⟨?_, (hgame γ hγ).2⟩, hsys⟩
  show System.answeredQueries _ ∈ γ.2.1 ↔ System.answeredQueries _ ∈ γ.2.1
  rw [(hgame γ hγ).1]

namespace Plumbing

open System

/-- A transcript never has more entries than the interaction had rounds. -/
theorem length_transcript_le (s : System.DDS X Y) (e : System.DDE.Total Y X) (n : ℕ) :
    (System.DDE.Total.transcript s e n).length ≤ n := by
  induction n with
  | zero => simp [System.DDE.Total.transcript]
  | succ n ih =>
      rcases hx : e (System.DDE.Total.transcript s e n)↓ᵧ with _ | x
      · rw [System.DDE.Total.transcript_succ_of_stop s e hx]
        omega
      · rw [System.DDE.Total.transcript_succ_of_query s e hx, List.length_append]
        simpa using ih

/-- Two fixed query lists that agree below the interaction length give the same
interaction: `playQueries` reads its list by position. -/
theorem transcript_playQueries_congr (s : System.DDS X Y) (L L' : List X) :
    ∀ n : ℕ, (∀ k < n, L[k]? = L'[k]?) →
      System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n
        = System.DDE.Total.transcript s (System.DDE.Total.playQueries L') n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro h
      have ihn := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
      have hstep : System.DDE.Total.playQueries (Y := Y) L
            (System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n)↓ᵧ
          = System.DDE.Total.playQueries (Y := Y) L'
            (System.DDE.Total.transcript s (System.DDE.Total.playQueries L') n)↓ᵧ := by
        show L[_]? = L'[_]?
        simp only [System.transcriptOutputs, List.length_map, ihn]
        exact h _ (Nat.lt_succ_of_le (length_transcript_le s _ n))
      rcases hx : System.DDE.Total.playQueries (Y := Y) L'
          (System.DDE.Total.transcript s (System.DDE.Total.playQueries L') n)↓ᵧ with
        _ | x
      · rw [System.DDE.Total.transcript_succ_of_stop s _ (hstep.trans hx),
          System.DDE.Total.transcript_succ_of_stop s _ hx, ihn]
      · rw [System.DDE.Total.transcript_succ_of_query s _ (hstep.trans hx),
          System.DDE.Total.transcript_succ_of_query s _ hx, ihn]

/-- An interaction whose answers are all defined answers exactly its input
list. -/
theorem answeredQueries_of_isSome {t : List (X × Option Y)}
    (h : ∀ p ∈ t, p.2 ≠ none) : System.answeredQueries t = t↓ₓ := by
  induction t with
  | nil => rfl
  | cons p t ih =>
      rcases hp : p.2 with _ | y
      · exact absurd hp (h p (by simp))
      · have hpair : p = (p.1, some y) := by
          rcases p with ⟨a, b⟩; simp at hp; simp [hp]
        rw [hpair]
        simpa [System.answeredQueries, System.transcriptInputs] using
          ih fun q hq => h q (by simp [hq])

/-- A system whose completion never refuses runs the whole fixed query list:
after `n ≤ L.length` rounds the transcript has `n` entries, its inputs are
`L.take n`, and every answer is defined. -/
theorem transcript_playQueries_total {s : System.DDS X Y}
    (hs : ∀ (l : List X) (x : X), System.answer s l x ≠ none) (L : List X) :
    ∀ n, n ≤ L.length →
      (System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n).length = n ∧
        (System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n)↓ₓ
          = L.take n ∧
        ∀ p ∈ System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n,
          p.2 ≠ none := by
  intro n
  induction n with
  | zero => intro _; exact ⟨rfl, rfl, by simp [System.DDE.Total.transcript]⟩
  | succ n ih =>
      intro hn
      obtain ⟨hlen, hinp, hsome⟩ := ih (Nat.le_of_succ_le hn)
      have hlt : n < L.length := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hn
      have hq : System.DDE.Total.playQueries (Y := Y) L
          (System.DDE.Total.transcript s (System.DDE.Total.playQueries L) n)↓ᵧ
          = some L[n] := by
        show L[_]? = _
        simp only [System.transcriptOutputs, List.length_map, hlen]
        exact List.getElem?_eq_getElem hlt
      rw [System.DDE.Total.transcript_succ_of_query s _ hq]
      refine ⟨by simp [hlen], ?_, ?_⟩
      · rw [System.transcriptInputs_concat, hinp, List.take_add_one,
          List.getElem?_eq_getElem hlt]
        rfl
      · intro p hp
        rcases List.mem_append.mp hp with hp' | hp'
        · exact hsome p hp'
        · rw [List.mem_singleton.mp hp']
          exact hs _ _

/-- The refusal pass of CR18 Definition 3.10's filter (printed p. 62), on an
answer stream with no refusals in it: the first `q` answers pass and the rest
are refused. -/
theorem refuseAfter_of_isSome (q : ℕ) :
    ∀ ys : List (Option Y), (∀ o ∈ ys, o ≠ none) →
      System.refuseAfter q ys
        = ys.take q ++ List.replicate (ys.length - q) none := by
  intro ys
  induction ys generalizing q with
  | nil => intro _; simp
  | cons o t ih =>
      intro h
      rcases o with _ | y
      · exact absurd rfl (h none (by simp))
      · cases q with
        | zero =>
            show none :: System.refuseAfter 0 t = _
            rw [ih 0 fun o ho => h o (by simp [ho])]
            simp [List.replicate_succ]
        | succ q =>
            show some y :: System.refuseAfter q t = _
            rw [ih q fun o ho => h o (by simp [ho])]
            simp

/-- Appending refused entries changes no answered query. -/
theorem answeredQueries_append_none (t : List (X × Option Y)) (xs : List X) :
    System.answeredQueries (t ++ xs.map (fun x => (x, (none : Option Y))))
      = System.answeredQueries t := by
  show (t ++ _).filterMap _ = t.filterMap _
  rw [List.filterMap_append]
  have hnil : ∀ ys : List X,
      (ys.map (fun x => (x, (none : Option Y)))).filterMap
        (fun entry : X × Option Y => entry.2.map fun _ => entry.1) = [] := by
    intro ys
    induction ys with
    | nil => rfl
    | cons x ys ih => simp [ih]
  rw [hnil, List.append_nil]

theorem zip_replicate_none (xs : List X) :
    xs.zip (List.replicate xs.length (none : Option Y))
      = xs.map (fun x => (x, (none : Option Y))) := by
  induction xs with
  | nil => rfl
  | cons x t ih => simpa [List.replicate_succ] using ih

/-- **The query-limited interaction at a fixed query list, computed.**  CR18
Definition 3.10's `[q]` (printed p. 62) run against a system that never
refuses: the first `q` queries are the interaction with the truncated list, and
every later query is refused.  This is the absorption witness of
`condEquiv_fTransform` for the filter, with the inner query list `L.take q`
and the post-processing "append the refusals". -/
theorem transcript_filterQueries_playQueries {s : System.DDS X Y}
    (hs : ∀ (l : List X) (x : X), System.answer s l x ≠ none) (q : ℕ) (l' : List X) :
    System.DDE.Total.transcript (System.filterQueries q s)
        (System.DDE.Total.playQueries l') l'.length
      = System.DDE.Total.transcript s
            (System.DDE.Total.playQueries (l'.take q)) (l'.take q).length
          ++ (l'.drop q).map (fun x => (x, (none : Option Y))) := by
  classical
  set T := System.DDE.Total.transcript s (System.DDE.Total.playQueries l') l'.length
    with hT
  obtain ⟨hTlen, hTinp, hTsome⟩ :=
    transcript_playQueries_total hs l' l'.length le_rfl
  rw [List.take_length] at hTinp
  have houter : System.DDE.Total.transcript (System.filterQueries q s)
      (System.DDE.Total.playQueries l') l'.length
      = List.zip T↓ₓ (System.refuseAfter q T↓ᵧ) :=
    System.transcript_filterQueries q s (System.DDE.Total.playQueries l')
      (System.DDE.Total.playQueries l')
      (fun ys => by
        show l'[ys.length]? = l'[_]?
        rw [System.refuseAfter_length]) l'.length
  have hos : ∀ o ∈ T↓ᵧ, o ≠ none := by
    intro o ho
    obtain ⟨pr, hpr, rfl⟩ := List.mem_map.mp ho
    exact hTsome pr hpr
  have hylen : (T↓ᵧ).length = l'.length := by
    simp only [System.transcriptOutputs, List.length_map]; exact hTlen
  rw [houter, refuseAfter_of_isSome q _ hos, hTinp, hylen]
  have hq' : (l'.take q).length = min q l'.length := by simp
  set m := l'.length - q with hm
  have hlen1 : (l'.take q).length = ((T↓ᵧ).take q).length := by
    rw [List.length_take, List.length_take, hylen]
  have hzip : List.zip l' ((T↓ᵧ).take q ++ List.replicate m (none : Option Y))
      = List.zip (l'.take q) ((T↓ᵧ).take q)
        ++ List.zip (l'.drop q) (List.replicate m (none : Option Y)) := by
    conv_lhs => rw [← List.take_append_drop q l']
    exact List.zip_append hlen1
  rw [hzip]
  have hdroplen : (l'.drop q).length = m := by simp [hm]
  have hsecond : List.zip (l'.drop q) (List.replicate m (none : Option Y))
      = (l'.drop q).map (fun x => (x, (none : Option Y))) := by
    rw [← hdroplen]; exact zip_replicate_none _
  have hfirst : List.zip (l'.take q) ((T↓ᵧ).take q)
      = System.DDE.Total.transcript s
          (System.DDE.Total.playQueries (l'.take q)) (l'.take q).length := by
    have hzt : List.zip (l'.take q) ((T↓ᵧ).take q) = T.take q := by
      rw [← hTinp]
      exact (List.zip_of_prod List.map_take List.map_take).symm
    have hpre : System.DDE.Total.transcript s (System.DDE.Total.playQueries l')
        (min q l'.length) <+: T :=
      System.DDE.Total.transcript_prefix s _ (min_le_right q l'.length)
    obtain ⟨hlen2, -, -⟩ :=
      transcript_playQueries_total hs l' (min q l'.length) (min_le_right q l'.length)
    have hmin : T.take q = T.take (min q l'.length) := by
      rcases le_or_gt q l'.length with hle | hgt
      · rw [min_eq_left hle]
      · rw [min_eq_right (le_of_lt hgt),
          List.take_of_length_le (by rw [hTlen]; omega),
          List.take_of_length_le (by rw [hTlen])]
    have hcut : T.take (min q l'.length)
        = System.DDE.Total.transcript s (System.DDE.Total.playQueries l')
            (min q l'.length) := by
      have hpt := (List.prefix_iff_eq_take).mp hpre
      rw [hlen2] at hpt
      exact hpt.symm
    rw [hzt, hmin, hcut, hq']
    refine transcript_playQueries_congr s l' (l'.take q) (min q l'.length) ?_
    intro k hk
    rw [List.getElem?_take_of_lt (by omega)]
  rw [hfirst, hsecond]

end Plumbing

/-- **CR18's `[r]` instance of the transport** (printed p. 128): "This is of
course still true when the systems are restricted by `[r]`, i.e.,
`[r]casc[Ŝ,R_{m,n}] ⊨ [r]V_n`."

**Scope.**  This is the step in the proof of CR18 **Theorem 6.2**, printed
p. 128, at the query-count filter `[r]`.  It is **not** Theorem 6.1's `θ_r`
instance (equation (6.3), printed p. 127), which restricts by a block-count
predicate: that is `filterPhi` at a different prefix-closed predicate — a
block count, not a query count — and is not landed.

Definition 3.10's filter (printed p. 62) applied to both sides of a
conditional equivalence, with the monotone condition carried over unchanged.

**The side condition — that the systems in play never refuse — is a design
hypothesis of this development, and carries no page claim.**  Ruling R1 makes
the official interaction carrier the fully defined slice, and that is the
slice on which the filter's admitted schedule `l'.take q` is a function of
`l'` alone.  It is not padding: `System.refuseAfter` (`System/FilterPhi.lean`)
does not consume budget on a refusal, so against a refusing system the queries
that actually reach the system are a function of the system's own refusal
pattern, the uniform witness `l = l'.take q` fails, and `condEquiv_fTransform`
demands one list good for both supports at once.  No counterexample is landed,
so that necessity is argued structurally, not proved. -/
theorem condEquiv_filterQueries (q : ℕ) {G : PDG X Y} {T : PDS X Y}
    (hG : ∀ γ ∈ G.support, ∀ (l : List X) (x : X), System.answer γ.1 l x ≠ none)
    (hT : ∀ s ∈ T.support, ∀ (l : List X) (x : X), System.answer s l x ≠ none)
    (h : CondEquiv G T) :
    CondEquiv
      (Distribution.fTransform
        (fun γ : System.DDG X Y =>
          ((System.filterQueries q γ.1, γ.2) : System.DDG X Y)) G)
      (Distribution.fTransform (System.filterQueries q) T) := by
  refine condEquiv_fTransform_of_answeredQueries (System.filterQueries q)
    (fun l' => ⟨l'.take q,
      fun t => t ++ (l'.drop q).map (fun x => (x, (none : Option Y))), ?_, ?_⟩) h
  · intro γ hγ
    have hcomp := Plumbing.transcript_filterQueries_playQueries (hG γ hγ) q l'
    exact ⟨by rw [hcomp, Plumbing.answeredQueries_append_none], hcomp⟩
  · intro s hsmem
    exact Plumbing.transcript_filterQueries_playQueries (hT s hsmem) q l'

end PDG

namespace PDS

/-- **The endpoint at the constructor.**  Maurer02 Theorem 1(i) (preprint p. 12)
/ Maurer13b Theorem 3 (printed p. 3154) taking the *base* system `S` and a
per-atom condition `A`, with the game built inside the statement by
Lanzenberger Remark 2.24's constructor `PDS.adjoin` (printed p. 17).
Nothing is assumed about the game: `adjoin` discharges the forgetting law on
the nose (`forget_adjoin`) and monotonicity lives in `MonotoneCondition`, so
the only hypothesis about the pair is the conditional equivalence itself. -/
theorem conditional_equivalence_theorem_adjoin {S T : PDS X Y}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (A : System.DDS X Y → System.MonotoneCondition X)
    (hCE : PDG.CondEquiv (adjoin S A).1 T) :
    advFullyDefined S T ≤ ν[(adjoin S A).1] := by
  have h := PDG.conditional_equivalence_theorem
    (nonNeg_adjoin hS A) hT (by rw [GamesFor.weight_eq (adjoin S A)]; exact hw) hCE
  rwa [forget_adjoin] at h

/-- The same endpoint for an arbitrary game *for* `S`, where the forgetting law
holds only up to **Lanzenberger Definition 2.17**'s system equivalence (printed
p. 16: "Two `(𝒳,𝒴)`-PDS `S` and `T` are equivalent, denoted by `S ≡ T`, if they
have the same domain and `tr(S,e) = tr(T,e)` for all compatible `(𝒴,𝒳)`-DDE
`e`") — here `PDS.equivalent`, via `PDS.GamesFor` membership.
`Adv⊥` transports along equivalence in both slots
(`PDS.advFullyDefined_congr`), so which representative a construction happens
to produce is not a modeling wrinkle. -/
theorem conditional_equivalence_theorem_gamesFor {S T : PDS X Y}
    (G : GamesFor S) (hG : G.1.NonNeg) (hT : T.NonNeg)
    (hw : G.1.weight = T.weight) (hCE : PDG.CondEquiv G.1 T) :
    advFullyDefined S T ≤ ν[G.1] := by
  rw [advFullyDefined_congr (equivalent_symm G.2) (equivalent_refl T)]
  exact PDG.conditional_equivalence_theorem hG hT hw hCE

/-! ### Worked receipts: the two poles of the condition lattice

`Game.lean`'s `⊥`/`⊤` receipts, read through conditional equivalence.  They
bracket the technique: adjoining the never-won condition to `T` itself is
conditionally equivalent to `T` and wins with probability `0`, so the endpoint
returns `Adv⊥(T,T) ≤ 0`; adjoining the already-won condition is conditionally
equivalent to *every* `T` — the not-won slice is empty and Maurer13b's product
form is `0 = 0` — and the endpoint returns the trivial bound `Adv⊥(S,T) ≤ |S|`.

**What the poles do and do not test.**  They show the relation is satisfiable
and that it is not satisfiable for free.  They do **not** pin the placement of
the two scalars: at the `⊥` pole `notWonMass = ‖T‖` (`notWonMass_adjoin_bot`),
so the two scalars of the product form are *literally the same number* there
and the receipt is discharged verbatim by the scalar-exchanged relation and by
the `‖G‖`-in-place-of-`‖T‖` variant as well.  (Kernel-checked by the T3
adversarial audit, `t3-audit/check3.lean`, which built both rivals; an earlier
version of this comment claimed the pole detects a misplaced `‖T‖`, and that
claim was false.)  What the pole does detect is the *total absence* of a
scalar.  The definition's faithfulness rests instead on the algebra — both
sides of the landed identity are of degree one in `G` and degree one in `T`, so
it is equivalent to Maurer13b's printed form at every pair of weights, not only
at weight one — and its non-degeneracy on the interpolation family below. -/

@[simp] theorem notWonMass_adjoin_bot (T : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonMass e n (adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1
      = T.weight := by
  rw [PDG.notWonMass_eq_mass_not_won, coe_adjoin, Distribution.mass_fTransform,
    Distribution.mass_congr T (Q := fun _ => True)
      (fun s => iff_of_true (System.not_won_bot s e n) trivial),
    Distribution.mass_true]

@[simp] theorem notWonLaw_adjoin_bot (T : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonLaw e n (adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1
      = trLawFullyDefined e n T := by
  ext t
  rw [PDG.notWonLaw_apply, coe_adjoin, Distribution.mass_fTransform,
    trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
  exact Distribution.mass_congr T fun s =>
    ⟨fun h => h.2, fun h => ⟨System.not_won_bot s e n, h⟩⟩

/-- The never-won game over `T` is conditionally equivalent to `T`. -/
theorem condEquiv_adjoin_bot (T : PDS X Y) :
    PDG.CondEquiv (adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1 T :=
  fun l => by rw [notWonLaw_adjoin_bot, notWonMass_adjoin_bot]

@[simp] theorem notWonMass_adjoin_top (S : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonMass e n (adjoin S fun _ => (⊤ : System.MonotoneCondition X)).1
      = 0 := by
  rw [PDG.notWonMass_eq_mass_not_won, coe_adjoin, Distribution.mass_fTransform]
  exact Distribution.mass_eq_zero_of_forall_not S fun s hs =>
    hs (System.won_top s e n)

@[simp] theorem notWonLaw_adjoin_top (S : PDS X Y)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonLaw e n (adjoin S fun _ => (⊤ : System.MonotoneCondition X)).1
      = 0 := by
  ext t
  rw [PDG.notWonLaw_apply, coe_adjoin, Distribution.mass_fTransform]
  exact (Distribution.mass_eq_zero_of_forall_not S fun s hs =>
    hs.1 (System.won_top s e n)).trans rfl

/-- The already-won game over `S` is conditionally equivalent to *every*
system: the not-won slice is empty, so Maurer13b Definition 13's product form
(printed p. 3153) holds with both sides `0`.  The endpoint then returns `ν = |S|`, the trivial bound — the
technique's degenerate corner, not a soundness hole. -/
theorem condEquiv_adjoin_top (S T : PDS X Y) :
    PDG.CondEquiv (adjoin S fun _ => (⊤ : System.MonotoneCondition X)).1 T :=
  fun l => by rw [notWonLaw_adjoin_top, notWonMass_adjoin_top, smul_zero, zero_smul]

/-! ### Definition 11's `i ≥ 1` is load-bearing

`EquivalentAsGames` renders Definition 11 literally, over nonempty query lists
only.  The witness below shows the omitted `[]` index is a genuine extra
demand rather than a free consequence: two games that agree on the not-won
slice at **every** nonempty query list, and disagree at the empty one.

It is not a degenerate-alphabet artefact — it lives at any `X` whatever, on a
system that answers every nonempty history (`System.functionEvaluator`), with a
condition that fires as soon as one query is answered.  This is also the shape
the T3 audit recorded as missing from the interpolation family below, whose
condition fires already at `[]`. -/

/-- The mass of an event under a law concentrated on one deterministic system.
UPSTREAM-CANDIDATE for `System/ProbabilisticSystem.lean`, beside `PDS.ofDDS`. -/
theorem mass_ofDDS (s : System.DDS X Y) (P : System.DDS X Y → Prop) :
    (ofDDS s).mass P = if P s then 1 else 0 := by
  rw [ofDDS, Distribution.mass]
  exact Finsupp.sum_single_index (by simp)

theorem nonNeg_ofDDS (s : System.DDS X Y) : (ofDDS s).NonNeg := by
  intro a
  rw [ofDDS, Finsupp.single_apply]
  split <;> norm_num

/-- **Maurer13b Definition 11's `i ≥ 1` clause is not cosmetic** (printed
p. 3153).  Two games over one
system — the same total system, carrying the condition "some query has been
answered" and the already-won condition `⊤` — agree on the not-won slice at
every nonempty query list (both slices are empty: the condition has fired) and
disagree at the empty one (nothing has fired yet in the first, everything has
in the second).

So quantifying `EquivalentAsGames` over `[]` as well would be strictly stronger
than Maurer13b Definition 11, and the corresponding Lemma 2 (printed p. 3153)
correspondingly weaker.  This is why the definition carries `l ≠ []` and Lemma 2 carries the
weight hypothesis instead. -/
theorem exists_equivalentAsGames_notWonLaw_nil_ne [Nonempty Y] :
    ∃ G H : PDG X Y, G.NonNeg ∧ H.NonNeg ∧ PDG.EquivalentAsGames G H ∧
      PDG.notWonLaw (System.DDE.Total.playQueries ([] : List X))
          ([] : List X).length G
        ≠ PDG.notWonLaw (System.DDE.Total.playQueries ([] : List X))
          ([] : List X).length H := by
  classical
  set s₀ : System.DDS X Y :=
    System.functionEvaluator (fun _ => (Classical.arbitrary Y)) with hs₀
  set S : PDS X Y := ofDDS s₀ with hS
  refine ⟨(adjoin S fun _ => System.MonotoneCondition.nonNil).1,
    (adjoin S fun _ => (⊤ : System.MonotoneCondition X)).1,
    nonNeg_adjoin (nonNeg_ofDDS s₀) _, nonNeg_adjoin (nonNeg_ofDDS s₀) _,
    ?_, ?_⟩
  · -- the two not-won slices are empty at every nonempty query list
    intro l hl
    rw [notWonLaw_adjoin_top]
    ext t
    rw [PDG.notWonLaw_apply, coe_adjoin, Distribution.mass_fTransform, hS,
      mass_ofDDS, if_neg, Finsupp.zero_apply]
    rintro ⟨hnotwon, -⟩
    refine hnotwon ?_
    show System.answeredQueries (System.DDE.Total.transcript s₀
      (System.DDE.Total.playQueries l) l.length) ∈ _
    rw [System.answeredQueries_transcript_playQueries s₀
      (by rw [hs₀, System.dom_functionEvaluator]; exact hl)]
    exact hl
  · -- but they disagree at the empty query list
    rw [notWonLaw_adjoin_top]
    intro hEq
    have happ := DFunLike.congr_fun hEq ([] : List (X × Option Y))
    rw [PDG.notWonLaw_apply, coe_adjoin, Distribution.mass_fTransform, hS,
      mass_ofDDS, if_pos ⟨fun hc => hc rfl, rfl⟩, Finsupp.zero_apply] at happ
    exact one_ne_zero happ

/-! ### The interior: a one-parameter family strictly between the poles

The poles alone leave open whether `CondEquiv G T` at equal weights forces
`forget G = T` — in which case the endpoint would be `Adv⊥ = 0 ≤ ν` and say
nothing.  It does not, and the witness is built from the two pole games alone:
mixing them with weight `c` gives, for every `c`, a game conditionally
equivalent to `T` whose forgetful image is the mixture `(1−c)·T + c·S₀` and
whose winning probability is exactly `c·‖S₀‖`.  Instantiating at
`0 < c < 1`, `S₀ ≠ T`, `‖S₀‖ = ‖T‖ > 0`, every hypothesis of the endpoint holds
(`nonNeg_condEquivInterp`, `weight_condEquivInterp`, `condEquiv_condEquivInterp`),
the forgetful image is *not* `T` (`forget_condEquivInterp_ne`), and the bound is
`c·‖S₀‖` (`supWinProb_condEquivInterp`) — strictly between `0` and the game's
weight, by arithmetic from those last two.  So the endpoint is neither vacuous
nor trivial.

Origin: the T3 adversarial audit built and kernel-checked this family in its
scratch `t3-audit/check2.lean` while attacking the endpoint for vacuity; it is
landed here so the non-degeneracy travels with the definition.

**What it does not witness** (recorded by the audit as the honest residual):
the condition that fires here is `⊤`, already satisfied at the empty history,
so the family does *not* satisfy the empty-history clause the `ω` endpoint
carries.  Swapping `⊤` for `System.MonotoneCondition.nonNil` repairs that — the
product form still holds at `[]`, since both sides pick up the same
`(1−c)‖T‖ + c‖S₀‖` factor — but it needs `S₀`'s realizations to answer a first
query, which is a totality clause this module does not otherwise carry, and it
is not built.  Maurer13b's own non-degeneracy witnesses are Examples 7 and 8
(printed p. 3153) — a URF is conditionally equivalent to a beacon, and to a
URP — and they need concrete systems, i.e. an application. -/

/-- The interpolation between the two pole games: the never-won game over `T`
with weight `1 − c`, the already-won game over `S₀` with weight `c`. -/
def condEquivInterp (T S₀ : PDS X Y) (c : ℝ) : PDG X Y :=
  (1 - c) • (adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1
    + c • (adjoin S₀ fun _ => (⊤ : System.MonotoneCondition X)).1

@[simp] theorem notWonLaw_condEquivInterp (T S₀ : PDS X Y) (c : ℝ)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonLaw e n (condEquivInterp T S₀ c)
      = (1 - c) • trLawFullyDefined e n T := by
  ext t
  rw [PDG.notWonLaw_apply, condEquivInterp, Distribution.mass_add,
    Distribution.mass_smul, Distribution.mass_smul, Finsupp.smul_apply,
    smul_eq_mul]
  have h1 : ((adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1.mass
      fun g => ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t)
      = trLawFullyDefined e n T t := by
    rw [← PDG.notWonLaw_apply, notWonLaw_adjoin_bot]
  have h2 : ((adjoin S₀ fun _ => (⊤ : System.MonotoneCondition X)).1.mass
      fun g => ¬ System.Won g e n ∧ System.DDE.Total.transcript g.1 e n = t)
      = 0 := by
    rw [← PDG.notWonLaw_apply, notWonLaw_adjoin_top]
    rfl
  rw [h1, h2, mul_zero, add_zero]

@[simp] theorem notWonMass_condEquivInterp (T S₀ : PDS X Y) (c : ℝ)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.notWonMass e n (condEquivInterp T S₀ c) = (1 - c) * T.weight := by
  rw [← PDG.weight_notWonLaw, notWonLaw_condEquivInterp,
    Distribution.weight_smul, weight_trLawFullyDefined]

/-- **Every member of the family is conditionally equivalent to `T`.** -/
theorem condEquiv_condEquivInterp (T S₀ : PDS X Y) (c : ℝ) :
    PDG.CondEquiv (condEquivInterp T S₀ c) T := by
  intro l
  rw [notWonLaw_condEquivInterp, notWonMass_condEquivInterp]
  ext t
  simp only [Finsupp.smul_apply, smul_eq_mul]
  ring

/-- The forgetful image is the mixture of the two systems, not `T`. -/
theorem forget_condEquivInterp (T S₀ : PDS X Y) (c : ℝ) :
    PDG.forget (condEquivInterp T S₀ c) = (1 - c) • T + c • S₀ := by
  rw [condEquivInterp, PDG.forget, Distribution.fTransform_add,
    Distribution.fTransform_smul, Distribution.fTransform_smul, ← PDG.forget,
    ← PDG.forget, forget_adjoin, forget_adjoin]

@[simp] theorem winningMass_condEquivInterp (T S₀ : PDS X Y) (c : ℝ)
    (e : System.DDE.Total Y X) (n : ℕ) :
    PDG.winningMass e n (condEquivInterp T S₀ c) = c * S₀.weight := by
  rw [PDG.winningMass, condEquivInterp, Distribution.mass_add,
    Distribution.mass_smul, Distribution.mass_smul]
  have h1 : ((adjoin T fun _ => (⊥ : System.MonotoneCondition X)).1.mass
      fun g => System.Won g e n) = 0 := by
    rw [coe_adjoin, Distribution.mass_fTransform]
    exact Distribution.mass_eq_zero_of_forall_not T fun s hs =>
      System.not_won_bot s e n hs
  have h2 : ((adjoin S₀ fun _ => (⊤ : System.MonotoneCondition X)).1.mass
      fun g => System.Won g e n) = S₀.weight := by
    rw [coe_adjoin, Distribution.mass_fTransform,
      Distribution.mass_congr S₀ (Q := fun _ => True)
        (fun s => iff_of_true (System.won_top s e n) trivial),
      Distribution.mass_true]
  rw [h1, h2, mul_zero, zero_add]

/-- **The bound the endpoint returns on the family is `ν = c·‖S₀‖`** — neither
`0` nor the whole weight. -/
theorem supWinProb_condEquivInterp (T S₀ : PDS X Y) (c : ℝ) :
    PDG.supWinProb (condEquivInterp T S₀ c) = c * S₀.weight := by
  have hbdd : BddAbove (Set.range fun p : System.DDE.Total Y X × ℕ =>
      PDG.winningMass p.1 p.2 (condEquivInterp T S₀ c)) := by
    refine ⟨c * S₀.weight, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact le_of_eq (winningMass_condEquivInterp T S₀ c p.1 p.2)
  refine le_antisymm (PDG.supWinProb_le_of_forall fun e n => ?_) ?_
  · rw [winningMass_condEquivInterp]
  · rw [← winningMass_condEquivInterp T S₀ c (fun _ => none) 0]
    exact le_ciSup hbdd ((fun _ => none), 0)

theorem weight_condEquivInterp (T S₀ : PDS X Y) (c : ℝ)
    (h : S₀.weight = T.weight) : (condEquivInterp T S₀ c).weight = T.weight := by
  rw [← Distribution.mass_true, condEquivInterp, Distribution.mass_add,
    Distribution.mass_smul, Distribution.mass_smul, Distribution.mass_true,
    Distribution.mass_true, ← PDG.weight_forget, ← PDG.weight_forget,
    forget_adjoin, forget_adjoin, h]
  ring

theorem nonNeg_condEquivInterp {T S₀ : PDS X Y} (hT : T.NonNeg) (hS : S₀.NonNeg)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : (condEquivInterp T S₀ c).NonNeg := by
  intro g
  have hA := (nonNeg_adjoin hT fun _ => (⊥ : System.MonotoneCondition X)) g
  have hB := (nonNeg_adjoin hS fun _ => (⊤ : System.MonotoneCondition X)) g
  have h1 : (0:ℝ) ≤ 1 - c := by linarith
  show (0:ℝ) ≤ (condEquivInterp T S₀ c) g
  rw [condEquivInterp]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  nlinarith [mul_nonneg h1 hA, mul_nonneg hc0 hB]

/-- **Conditional equivalence does not force `forget G = T`.**  The one fact
that makes the endpoint worth stating: its hypothesis is satisfiable by games
whose forgetful image is genuinely different from `T`. -/
theorem forget_condEquivInterp_ne (T S₀ : PDS X Y) {c : ℝ} (hc : c ≠ 0)
    (hne : S₀ ≠ T) : PDG.forget (condEquivInterp T S₀ c) ≠ T := by
  rw [forget_condEquivInterp]
  intro hEq
  refine hne ?_
  have h2 : c • S₀ = c • T := by
    have hd := congrArg (fun z : PDS X Y => z - (1 - c) • T) hEq
    simpa [sub_smul, one_smul, sub_sub_cancel] using hd
  exact smul_right_injective _ hc h2

end PDS

end

end RandomSystems

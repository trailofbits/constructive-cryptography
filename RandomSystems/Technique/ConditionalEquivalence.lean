/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Winnability
import Probability.Conditional

/-!
# Conditional equivalence

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
game, condition or conditioning notion is introduced here, and no `S⁻`, `Γ`,
`Γᵇ` or blinded-system operator exists (PHI-SPEC R11(a)).

* `PDG.notWonMass e n G` — Maurer13b's `p^S_{Aᵢ=0|Xⁱ}` (printed p. 3153): the
  mass of the not-won slice of `gameTrLaw`.
* `PDG.notWonLaw e n G` — Maurer13b's `p^S_{Yⁱ,Aᵢ=0|Xⁱ}`: that slice's
  transcript marginal, an *unnormalized* law.  Both are read off `gameTrLaw`,
  and `notWonMass + winningMass = |G|`.
* `PDG.EquivalentAsGames` — **Maurer13b Definition 11, printed p. 3153**:
  "Two `(𝒳,𝒴×{0,1})`-systems with MBO, `S` and `T`, are *equivalent as games*,
  denoted `S ≡ᵍ T`, if, for `i ≥ 1`, `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^T_{Yⁱ,Aᵢ=0|Xⁱ}`."
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
endpoint, and the mechanism is the deterministic fibre factorization
(`System.DDE.Total.transcript_eq_iff_of_consistent`): the mass a transcript law
puts on a value `t` is cut out by a condition on the system alone, so the
adaptive environment's fibre at `t` is the fibre of `playQueries t↓ₓ`.  That is
the `η`-cancellation of the H-coefficient factorization, available here as a
fibre identity because environments are deterministic.

## The endpoints

* `PDG.advFullyDefined_forget_le_supWinProb_of_equivalentAsGames` —
  **Maurer13b Lemma 2, printed p. 3153**: "If `S ≡ᵍ T`, then, for any
  distinguisher `D` and any `q`, `Δ^D_q(S⁻,T⁻) ≤ Γ^D_q(S)`", the statement the
  paper says "implies the so-called fundamental lemma of game playing".
  (CR18 Lemma 4.16, printed p. 107.)
* `PDG.advFullyDefined_forget_le_supWinProb_of_condEquiv` — **Maurer02
  Theorem 1(i), preprint p. 12**: "If `F^𝒜 ≡ G^ℬ` or `F|𝒜 ≡ G`, then
  `Δₖ(F,G) ≤ ν(F, Āₖ)`", the **adaptive** right-hand side; equivalently the
  first half of Maurer13b Theorem 3 (printed p. 3154) and of CR18 Theorem 4.17
  (printed p. 110) before their blinding step.
* `PDS.advFullyDefined_le_supWinProb_adjoin_of_condEquiv` — the same bound
  taking the *base* system and the condition, with the game constructed in the
  statement by `PDS.adjoin`.
* `PDG.advFullyDefined_forget_le_infWinnability_of_condEquiv` — the
  right-hand side replaced, through Lanzenberger Theorem 2.37
  (`Winnability.lean`), by `ω`: the *static* infimum winnability, in which no
  environment occurs at all.  Theorem 2.37 says `ω = ν`, so this is **not** a
  smaller bound — it is the same number presented as a counting quantity
  rather than as a supremum over strategies.  The papers' non-adaptive
  `Γ^{NA}(Ŝ)` / `Γ(bŜ)` **is** strictly smaller in general and is **not**
  obtained here (see the adaptivity note below).

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
  through a blinding operator (`⟦DT⟧`, printed p. 3152) or a blocking
  converter (`b`, CR18 Definition 4.20, printed p. 109); neither is built
  here, and citing Maurer02 for a blind right-hand side would be a false
  citation.
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
* its `gameEnhance` (CR18 eq. (4.39)'s `T̂`) and the `verdictProb` chain —
  the statement-facing metric `Adv⊥` is already a `δ`-shaped supremum of
  statistical distances of transcript laws, so the enhancement's only job,
  turning a two-game comparison into a system comparison, is not needed:
  `notWonLaw_le_trLawFullyDefined_of_condEquiv` compares `G`'s not-won law
  with `T`'s law directly.  `advFullyDefined_forget_le_supWinProb_of_le` is
  the shared coupling core both endpoints factor through: the same idea as
  `Winnability.lean`'s `advFullyDefined_toBitLaw_le_supWinProb` — bound each
  fibre's excess by its winning part — carried out for *two* laws instead of
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
Lanzenberger Definition 2.25's test reads `answeredQueries` of the transcript
and nothing else. -/
theorem won_congr_transcript {g : DDG X Y} {e e' : DDE.Total Y X} {n n' : ℕ}
    {t : List (X × Option Y)}
    (h : DDE.Total.transcript g.1 e n = t)
    (h' : DDE.Total.transcript g.1 e' n' = t) :
    Won g e n ↔ Won g e' n' := by
  unfold Won
  rw [h, h']

/-- **The fibre of an adaptive environment is the fibre of a fixed query
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

/-- The complement of Lanzenberger Definition 2.25's winning test, on the
Definition 2.21 pair: the not-won slice is the transcripts ending with `(·,0)`.
`Bool`-level companion of `won_iff_gameTranscript`. -/
theorem not_won_iff_gameTranscript (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    ¬ Won g e n ↔ (gameTranscript g e n).2 = false := by
  rw [won_iff_gameTranscript]
  cases (gameTranscript g e n).2 <;> simp

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

/-- The same, kept in `gameTrLaw` form: the numerator of Definition 13's first
display, before any normalizer is cleared. -/
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

/-- Definition 2.25's winning mass and the not-won mass partition the game's
weight. -/
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

/-! ## Maurer13b Definition 11 and Definition 13 -/

/-- **Maurer13b Definition 11** (printed p. 3153): "Two `(𝒳,𝒴×{0,1})`-systems
with MBO, `S` and `T`, are *equivalent as games*, denoted `S ≡ᵍ T`, if, for
`i ≥ 1`, `p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^T_{Yⁱ,Aᵢ=0|Xⁱ}`."  (CR18 Definition 4.16,
printed p. 105.)

The fixed input sequence `Xⁱ` is the non-adaptive environment
`playQueries l` at its own length, as the module docstring explains.  This is
*weaker* than Lanzenberger Definition 2.22 (`PDG.gameEquivalent`), which
compares the whole game transcript law: the two games may differ freely after
the condition has fired (`equivalentAsGames_of_gameEquivalent`). -/
def EquivalentAsGames (G H : PDG X Y) : Prop :=
  ∀ l : List X,
    notWonLaw (System.DDE.Total.playQueries l) l.length G
      = notWonLaw (System.DDE.Total.playQueries l) l.length H

@[inherit_doc EquivalentAsGames]
scoped notation:50 G " ≡ᵍ " H => EquivalentAsGames G H

theorem equivalentAsGames_refl (G : PDG X Y) : EquivalentAsGames G G :=
  fun _ => rfl

theorem EquivalentAsGames.symm {G H : PDG X Y} (h : EquivalentAsGames G H) :
    EquivalentAsGames H G := fun l => (h l).symm

theorem EquivalentAsGames.trans {G H K : PDG X Y} (h : EquivalentAsGames G H)
    (h' : EquivalentAsGames H K) : EquivalentAsGames G K :=
  fun l => (h l).trans (h' l)

/-- Lanzenberger Definition 2.22 refines Maurer13b Definition 11: agreeing on
the *whole* game transcript law in every environment implies agreeing on the
not-won slice at the fixed query lists. -/
theorem equivalentAsGames_of_gameEquivalent {G H : PDG X Y}
    (h : gameEquivalent G H) : EquivalentAsGames G H := fun l => by
  rw [notWonLaw, notWonLaw, h]

/-- **Maurer13b Definition 13** (printed p. 3153), in the paper's own
division-free product form: `S|𝒜 ≡ T` iff
`p^S_{Yⁱ,Aᵢ=0|Xⁱ} = p^S_{Aᵢ=0|Xⁱ} · p^T_{Yⁱ|Xⁱ}` for `i ≥ 1`.  (CR18
eq. (4.38), printed p. 108.)

`p^T_{Yⁱ|Xⁱ}` is a *normalized* conditional law in the papers, while
`PDS.trLawFullyDefined` carries `T`'s weight; the definition therefore clears
`T`'s normalizer as well, which is what makes it hold with no positivity guard
anywhere.  On the intended objects (`T.weight = 1`) the left factor is `1`.

`condEquiv_iff_condProb` is the guarded quotient form — Definition 13's first
display read through the T0 conditioning layer, with Maurer13b footnote 9's
"equal for all arguments for which they are both defined" as the two guards. -/
def CondEquiv (G : PDG X Y) (T : PDS X Y) : Prop :=
  ∀ l : List X,
    T.weight • notWonLaw (System.DDE.Total.playQueries l) l.length G
      = notWonMass (System.DDE.Total.playQueries l) l.length G
          • PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T

@[inherit_doc CondEquiv]
scoped notation:50 G " |≡ " T => CondEquiv G T

/-- **The index the papers exclude carries no information.**  Maurer13b
Definition 13 and CR18 Definition 4.19 both quantify over `i ≥ 1`, while
`CondEquiv` quantifies over every query list, `[]` included.  Nothing is
strengthened: at the empty query list the interaction is the empty transcript
in every realization, so both sides of the product form are the already-won
mass times `T`'s weight, concentrated at `[]`.  The two quantifications
therefore define the same relation. -/
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

/-- The definition read at one output transcript: Maurer13b's product form,
pointwise. -/
theorem condEquiv_apply {G : PDG X Y} {T : PDS X Y} (h : CondEquiv G T)
    (l : List X) (t : List (X × Option Y)) :
    T.weight * notWonLaw (System.DDE.Total.playQueries l) l.length G t
      = notWonMass (System.DDE.Total.playQueries l) l.length G
          * PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T t := by
  have := congrArg (fun d : Distribution (List (X × Option Y)) => d t) (h l)
  simpa using this

/-- Conditional equivalence to `T` is a statement about the not-won slice
alone, so it transports along Definition 11. -/
theorem CondEquiv.congr_equivalentAsGames {G H : PDG X Y} {T : PDS X Y}
    (h : CondEquiv G T) (hGH : EquivalentAsGames G H) : CondEquiv H T := by
  intro l
  have hmass : notWonMass (System.DDE.Total.playQueries l) l.length G
      = notWonMass (System.DDE.Total.playQueries l) l.length H := by
    rw [← weight_notWonLaw, ← weight_notWonLaw, hGH l]
  rw [← hGH l, ← hmass]
  exact h l

end PDG

/-! ## The coupling core

One inequality carries both endpoints: if at every fixed query list the game's
not-won law is pointwise dominated by `T`'s transcript law, then the *adaptive*
`Adv⊥` is at most Definition 2.25's `ν`.  The reference repository reaches the
same place through CR18 eq. (4.39)'s enhanced game `T̂` and a verdict-probability
chain; on this carrier `Adv⊥` is already a supremum of statistical distances of
transcript laws, so the comparison is direct (module docstring, carrier
deltas). -/

namespace PDG

/-- **The coupling core**, at one environment and one interaction length.

The three moves are: split each transcript value's mass by whether the game was
won (`Distribution.mass_and_add_mass_not_and`); exchange the adaptive
environment for the fixed query list `t↓ₓ` on the fibre over `t`
(`System.transcript_eq_iff_playQueries`, and `System.won_congr_transcript` for
the winning event, which is where the environment's adaptivity is spent); and
sum the won parts back over the fibres
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
law at every fixed query list bounds the *adaptive* `Adv⊥` by Definition 2.25's
`ν`. -/
theorem advFullyDefined_forget_le_supWinProb_of_le {G : PDG X Y} {T : PDS X Y}
    (hG : G.NonNeg) (hT : T.NonNeg)
    (hle : ∀ t : List (X × Option Y),
      notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
          t.length G t
        ≤ PDS.trLawFullyDefined
            (System.DDE.Total.playQueries (System.transcriptInputs t))
            t.length T t) :
    PDS.advFullyDefined (forget G) T ≤ ENNReal.ofReal (supWinProb G) := by
  refine iSup_le fun e => iSup_le fun n => ENNReal.ofReal_le_ofReal ?_
  exact (statDist_trLawFullyDefined_forget_le_winningMass hG hT hle e n).trans
    (winningMass_le_supWinProb hG e n)

/-! ## Maurer13b Lemma 2 — the fundamental lemma of game playing -/

/-- **Maurer13b Lemma 2** (printed p. 3153): "If `S ≡ᵍ T`, then, for any
distinguisher `D` and any `q`, `Δ^D_q(S⁻,T⁻) ≤ Γ^D_q(S)`."  The paper adds:
"It implies the so-called 'fundamental lemma of game playing' [Bellare–Rogaway]
which is stated (and proved) only for a specific type of system description."
(CR18 Lemma 4.16, printed p. 107, in its `⟨S⁻|T⁻⟩ ≤ S̄` form.)

Here `S⁻` is `PDG.forget` (PHI-SPEC R11(a): the forgetful map, never an
operator), the advantage is Ruling R4's `Adv⊥`, and `Γ^D_q` is Definition
2.25's `ν` — one number rather than a per-distinguisher family, since `Adv⊥`
already takes the supremum. -/
theorem advFullyDefined_forget_le_supWinProb_of_equivalentAsGames
    {G H : PDG X Y} (hG : G.NonNeg) (hH : H.NonNeg)
    (h : EquivalentAsGames G H) :
    PDS.advFullyDefined (forget G) (forget H)
      ≤ ENNReal.ofReal (supWinProb G) := by
  refine advFullyDefined_forget_le_supWinProb_of_le hG (nonNeg_forget hH) fun t => ?_
  have hEq := h (System.transcriptInputs t)
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
and `ν(F, Āₖ)` is Definition 2.25's `ν` after the Maurer02 polarity flip (his
`Aᵢ = 1` is the condition *satisfied*; the condition firing is winning here).
The right-hand side is a supremum over *all* total environments, hence
adaptive; the papers' non-adaptive `Γ^{NA}`/`Γ(bŜ)` needs the blinding
machinery and is not claimed.

Hypotheses: non-negativity of both laws and equal weight — the honest bundle
`Adv⊥`'s own symmetry statement carries (`advFullyDefined_comm_of_weight_eq`),
and satisfied by any pair of probability laws.  No query bound, no `Fintype`,
no totality clause: refusal is an observable answer (Ruling R2) and the
condition's monotonicity is the carrier's (module docstring). -/
theorem advFullyDefined_forget_le_supWinProb_of_condEquiv {G : PDG X Y}
    {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ ENNReal.ofReal (supWinProb G) := by
  refine advFullyDefined_forget_le_supWinProb_of_le hG hT fun t => ?_
  have h := notWonLaw_le_trLawFullyDefined_of_condEquiv hG hT hw hCE
    (System.transcriptInputs t) t
  simpa using h

/-- **The right-hand side with no strategy in it.**  Lanzenberger Theorem 2.37
(`Winnability.lean`, printed p. 24) identifies Definition 2.25's adversarial
`ν` with Definition 2.36's *static* `ω` — the infimum, over the game's own
equivalence class, of the mass of realizations that are winnable at all.
Composing it with the endpoint replaces the supremum over environments by a
counting quantity: no environment, adaptive or blind, occurs on the right.

**This is not a smaller bound.**  Theorem 2.37 is an equality, so `ω` is the
*adaptive* number written differently — which is the whole point (a winning
probability becomes a counting problem), but it must not be read as the papers'
non-adaptive right-hand side.  Maurer13b Theorem 3's `Γ^{NA}_q(Ŝ)` and CR18
Theorem 4.17's `Γ(bŜ)` satisfy `Γ^{NA} ≤ Γ = ν = ω` and are strictly smaller
in general; reaching them needs the blinding machinery R11(a) does not admit.

The finiteness bundle is Theorem 2.37's own — one domain clause, a query
bound, `[Fintype X]`, and the empty-history clause the pair carrier needs. -/
theorem advFullyDefined_forget_le_infWinnability_of_condEquiv [Fintype X]
    {G : PDG X Y} {T : PDS X Y} {D : Set (List X)} {q : ℕ}
    (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hnil : ∀ g ∈ G.support, [] ∉ g.2.1) (hdom : HasDomain G D)
    (hq : QBounded D q) (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ ENNReal.ofReal (infWinnability G) := by
  rw [← (winnability_theorem hG hnil hdom hq).1]
  exact advFullyDefined_forget_le_supWinProb_of_condEquiv hG hT hw hCE

/-! ## Definition 13's first display, through the T0 conditioning layer -/

/-- **Maurer13b Definition 13 as printed, with its footnote.**  Definition 13's
first display is the equality of two *conditional* laws,
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

namespace PDS

/-- **The endpoint at the constructor.**  Maurer02 Theorem 1(i) / Maurer13b
Theorem 3 taking the *base* system `S` and a per-atom condition `A`, with the
game built inside the statement by Remark 2.24's constructor `PDS.adjoin`.
Nothing is assumed about the game: `adjoin` discharges the forgetting law on
the nose (`forget_adjoin`) and monotonicity lives in `MonotoneCondition`, so
the only hypothesis about the pair is the conditional equivalence itself. -/
theorem advFullyDefined_le_supWinProb_adjoin_of_condEquiv {S T : PDS X Y}
    (hS : S.NonNeg) (hT : T.NonNeg) (hw : S.weight = T.weight)
    (A : System.DDS X Y → System.MonotoneCondition X)
    (hCE : PDG.CondEquiv (adjoin S A).1 T) :
    advFullyDefined S T ≤ ENNReal.ofReal (PDG.supWinProb (adjoin S A).1) := by
  have h := PDG.advFullyDefined_forget_le_supWinProb_of_condEquiv
    (nonNeg_adjoin hS A) hT (by rw [GamesFor.weight_eq (adjoin S A)]; exact hw) hCE
  rwa [forget_adjoin] at h

/-- The same endpoint for an arbitrary game *for* `S`, where the forgetting law
holds only up to Lanzenberger Definition 2.17 (`PDS.GamesFor` membership).
`Adv⊥` transports along equivalence in both slots
(`PDS.advFullyDefined_congr`), so which representative a construction happens
to produce is not a modeling wrinkle. -/
theorem advFullyDefined_le_supWinProb_of_condEquiv_gamesFor {S T : PDS X Y}
    (G : GamesFor S) (hG : G.1.NonNeg) (hT : T.NonNeg)
    (hw : G.1.weight = T.weight) (hCE : PDG.CondEquiv G.1 T) :
    advFullyDefined S T ≤ ENNReal.ofReal (PDG.supWinProb G.1) := by
  rw [advFullyDefined_congr (equivalent_symm G.2) (equivalent_refl T)]
  exact PDG.advFullyDefined_forget_le_supWinProb_of_condEquiv hG hT hw hCE

/-! ### Worked receipts: the two poles of the condition lattice

`Game.lean`'s `⊥`/`⊤` receipts, read through conditional equivalence.  They
bracket the technique and pin the definition's normalization: adjoining the
never-won condition to `T` itself is conditionally equivalent to `T` and wins
with probability `0`, so the endpoint returns `Adv⊥(T,T) ≤ 0`; adjoining the
already-won condition is conditionally equivalent to *every* `T` — the not-won
slice is empty and Maurer13b's product form is `0 = 0` — and the endpoint
returns the trivial bound `Adv⊥(S,T) ≤ |S|`.  Non-vacuity in both directions:
the relation is satisfiable, and it is not satisfiable for free. -/

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
system: the not-won slice is empty, so Maurer13b's product form holds with
both sides `0`.  The endpoint then returns `ν = |S|`, the trivial bound — the
technique's degenerate corner, not a soundness hole. -/
theorem condEquiv_adjoin_top (S T : PDS X Y) :
    PDG.CondEquiv (adjoin S fun _ => (⊤ : System.MonotoneCondition X)).1 T :=
  fun l => by rw [notWonLaw_adjoin_top, notWonMass_adjoin_top, smul_zero, zero_smul]

end PDS

end

end RandomSystems

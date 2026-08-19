/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import RandomSystems.Technique.BlindWinning
import RandomSystems.System.ParFace

/-!
# The game-relaxation (CR18 Definition 5.10)

CR18 **Definition 5.10** (printed p. 120): "For a system `T`, enhanced with an
MBO to a game `T̂`, the *game-relaxation* of `T̂`, denoted `T̂^⊥`, is the set of
PDS that behave as `T` as long as the MBO is `0` and behave arbitrarily once
the MBO is `1`."  Its footnote 7: "It is not difficult to make this definition
mathematically rigorous."

This module takes the source up on that footnote, and does it with the landed
observables rather than a second stack (Ruling R11).  "Behaves as `T` as long
as the MBO is `0`" is *already* a named relation on this carrier: Maurer13b
Definition 11 / CR18 Definition 4.16, `PDG.EquivalentAsGames` (`≡ᵍ`,
`Technique/ConditionalEquivalence.lean`), which equates the **not-won slices**
of the two game transcript laws — `PDG.notWonLaw`, the restriction of
`PDG.gameTrLaw` to the transcripts whose condition bit is `false`.  And
"behaves arbitrarily once the MBO is `1`" is the *absence* of any constraint on
the complementary slice, which is exactly what Definition 11 leaves free.

So a system lies in `T̂^⊥` when it can be enhanced with an MBO of its own so
that the resulting game agrees with `T̂` before `T̂`'s MBO fires.  The `∃` over
MBOs is **forced**, not a strengthening: a member of `T̂^⊥` is a plain PDS, and
"behaves as `T` as long as the MBO is `0`" cannot be read off it without an MBO
on it.

**The reading is a choice, and it has a price.**  With it, CR18's **Lemma 5.2**
(printed p. 121) — "If `Ŝ` is game-equivalent to a game `T̂`, then `S` is
contained in the game-relaxation of `T̂`" — becomes a *definitional unfolding*:
`forget_mem_gameRelaxation_of_equivalentAsGames` is literally `⟨H, hH, hw, h, rfl⟩`.
The source states 5.2 as a **lemma** ("we state two lemmas without proofs"),
which is weak evidence that the intended `T̂^⊥` is *larger* than the
`≡ᵍ`-image of games under `forget` — i.e. that the landed set may be smaller
than the source's.  Recorded, not decided: footnote 7 leaves the definition
open, and the strength of the agreement relation is the dial.  The stronger
alternative (Lanzenberger Definition 2.22's `gameEquivalent`, which gives a
*smaller* relaxation) is reachable without touching any containment below, via
`gameRelaxation_subset_of_equivalentAsGames` and
`equivalentAsGames_of_gameEquivalent`.  The `NonNeg` and equal-weight clauses
are signed-carrier artifacts (Ruling R9) and should be dropped if an honest
sub-carrier is ever installed.

## What this module claims, and what it does not

* `gameRelaxation ⊆ epsilonRelaxation ν[T̂] {forget T̂}` is a **containment,
  not an equality**.  The `ε`-ball is strictly larger: it constrains only the
  distance, while membership in `T̂^⊥` constrains the whole not-won slice at
  every fixed query sequence.  The relaxation is therefore *defined* off the
  condition and only *compared* to a ball; defining it as a ball would lose the
  conditional content the source's Lemma 5.2 and §5.4 rely on.
* CR18's **Lemma 5.3** (printed p. 121) **is** built here, as
  `forget_mem_gameRelaxation_of_condEquiv`.  It reads
  "`Ŝ |≡ T ⟹ S ⊆ T̂^⊥`, where … the inputs to `T` are also given to `bŜ` and
  the MBO (of `T̂`) is the MBO of `Ŝ`, i.e. the MBO is defined independently of
  `T`" — that is, `T̂` is built by running `Ŝ`'s condition *alongside* `T` on
  the same inputs, which is exactly the enhanced game of CR18 eq. (4.39),
  landed as `PDG.enhance` (`Technique/BlindWinning.lean`).  Given that game,
  Lemma 5.3 is Lemma 5.2 applied to eq. (4.39) — the same chaining the source's
  own proof of Theorem 4.17 performs.
  **This supersedes FLAG F-8**, which had recorded Lemma 5.3 as blocked pending
  a ruling on a "blinded-system object".  The escalation rested on a
  misidentification of `b`: CR18 Definition 4.20 (printed p. 109) makes it
  **reply-side** — "transparent for the queries `Xᵢ` but blocks the replies
  `Yᵢ`" — while the landed `block`/`filterPhi` family is **query-side**, a
  domain filter.  The reply-eraser is an ordinary attachment engine, inner-total
  and uniformly budgeted, hence a member of the metric-facing `Σ`
  (`System/BlockReplies.lean`, `blockReplies_mem_converterMonoidAt`); no new
  object stack was ever required, and Ruling R11(a) never barred one.
  What is also landed is the composition the lemma is used for, now at both
  radii: Definition 2.36's static `ω` through Lanzenberger Theorem 2.37's
  `ν ≤ ω` (`PDG.supWinProb_le_infWinnability`), and CR18 Theorem 4.17's
  *non-adaptive* `Γ(bŜ)` through `PDG.supWinProb_enhance_le_blindSupWinProb`
  (`gameRelaxation_enhance_subset_epsilonRelaxation_blind`).
* **Theorem 5.4** (authentication amplification, printed p. 122) is out of
  scope: an application rider, per the LEDGER's APPLICATION discipline.
* Compatibility (CR18 Definitions 5.6/5.7, "we point out that game-relaxation
  is compatible according to Definitions 5.6 and 5.7", printed p. 121) descends
  here in both halves, and neither is re-proved.  The **converter** half is
  `AbstractCryptography.Relaxation.epsilonRelaxation_compatible`, and it holds
  over any `Σ` acting non-expandingly on `Φ` — both `converterMonoidAt` and
  `converterMonoidAtProb` (`System/ProbabilisticConverter.lean`) qualify.  The
  **parallel** half is `ParFace.lean`'s Φ-level Definition 5.7, which is
  conditional by necessity: `Relaxation.epsilonRelaxation_parCompatible` takes
  `[IsNonexpandingPar Φ]`, recorded NOT OBTAINABLE at this carrier (spike G6.f,
  with `scripts/ledgerAudit.sh` check 5 as the tripwire).  So the two clauses
  arrive separately and asymmetrically — `epsilonRelaxation_parF_left_subset`
  costs sub-probability of the partner, `epsilonRelaxation_parF_right_subset_of_support`
  additionally costs a common separating splitting — and the descent below
  carries exactly those hypotheses, invents none, and claims no unconditional
  `ParCompatible`.
-/

namespace RandomSystems

open Probability (Distribution)
open Pointwise
open scoped ENNReal

universe u

namespace PDG

/-! ## Definition 5.10

Stated at the AC carrier `Φ = PDS Uni Uni` (Ruling R1), which is where the
specification calculus and the pseudo-emetric live.  There is no second,
alphabet-generic copy: Ruling R11 bars parallel object stacks, and every
consumer of Definition 5.10 — the `ε`-ball comparison, Definitions 5.6/5.7 —
is a statement about specifications of `Φ`. -/

/-- **CR18 Definition 5.10** (printed p. 120), made rigorous the way the
source's footnote 7 invites: `T̂^⊥` is the set of systems that admit an MBO of
their own under which they agree with `T̂` **before `T̂`'s condition fires** —
Definition 4.16's `≡ᵍ` (`EquivalentAsGames`), i.e. equality of the not-won
slices `PDG.notWonLaw` of the two Definition 2.21 transcript laws — and are
unconstrained after.

The honesty and weight clauses are the source's own standing reading of "PDS":
Definition 3.14's systems are probability distributions, and on the signed
carrier (Ruling R9) that is a hypothesis, not a structure.  The weight clause
is a condition on the *member* rather than on the witness, since
`PDG.weight_forget` makes `H.weight = S.weight`.

`Specification Φ`, not `Relaxation`: Definition 5.10 relaxes one game, while
the `Relaxation` interface (a monotone map on specifications) is what CR18
§5.2.2 asks of `·^ε` and `·^*`, not of `·^⊥`. -/
def gameRelaxation (G : PDG Uni.{u} Uni.{u}) :
    AbstractCryptography.Specification Phi.{u} :=
  {S | ∃ H : PDG Uni.{u} Uni.{u},
    H.NonNeg ∧ H.weight = G.weight ∧ EquivalentAsGames H G ∧ forget H = S}

/-- **CR18 Lemma 5.2** (printed p. 121): "If `Ŝ` is game-equivalent to a game
`T̂`, then `S` is contained in the game-relaxation of `T̂`: `Ŝ ≡ᵍ T̂ ⟹ S ⊆ T̂^⊥`."

The source states it without proof, and on this reading of Definition 5.10 it
is the introduction rule: the witness is `Ŝ` itself, and the proof is the
anonymous constructor.  That the printed *lemma* degrades here to a
*definitional unfolding* is the price of the reading, and is weak evidence
that the intended `T̂^⊥` is larger than the `≡ᵍ`-image — see the module
docstring's hedge. -/
theorem forget_mem_gameRelaxation_of_equivalentAsGames {H G : PDG Uni.{u} Uni.{u}}
    (hH : H.NonNeg) (hw : H.weight = G.weight) (h : EquivalentAsGames H G) :
    forget H ∈ gameRelaxation G :=
  ⟨H, hH, hw, h, rfl⟩

/-- The game's own system is in its game-relaxation — Lemma 5.2 at the
reflexive instance, and the statement that makes the containment below a
*relaxation* of a specification rather than a bound on the empty set. -/
theorem forget_mem_gameRelaxation {G : PDG Uni.{u} Uni.{u}} (hG : G.NonNeg) :
    forget G ∈ gameRelaxation G :=
  forget_mem_gameRelaxation_of_equivalentAsGames hG rfl (equivalentAsGames_refl G)

/-- Membership is preserved along Definition 2.22's game equivalence of the
*center*: a coarser identification of the center cannot change what agrees with
it off the condition, because `≡ᵍ` is implied by `gameEquivalent`
(`equivalentAsGames_of_gameEquivalent`) and is transitive. -/
theorem gameRelaxation_subset_of_equivalentAsGames {G G' : PDG Uni.{u} Uni.{u}}
    (h : EquivalentAsGames G G') (hw : G.weight = G'.weight) :
    gameRelaxation G ⊆ gameRelaxation G' := by
  rintro S ⟨H, hH, hwH, hHG, rfl⟩
  exact ⟨H, hH, hwH.trans hw, hHG.trans h, rfl⟩

/-! ## The containment in the `ε`-ball -/

open AbstractCryptography in
/-- **The game-relaxation is inside the `ν`-ball around the game's own system**
— and only inside it.

Every member is within Definition 2.25's supremum winning probability of the
center, by Maurer13b Lemma 2 (`fundamental_lemma_of_game_playing`, the
`Technique/ConditionalEquivalence.lean` endpoint): two games that agree off the
condition have transcript laws that agree until the condition fires, so the
whole distance is carried by the winning mass.  The radius is the **center's**
`ν`, which is what the symmetric reading of the metric supplies: at equal
weight `edist` is `Adv⊥` in either order
(`edist_eq_advFullyDefined_of_weight_eq`), so the lemma may be applied with the
center in the first slot.

**Containment, not equality — deliberately.**  The ball is strictly larger: it
records one number, while `T̂^⊥` records agreement of the entire not-won law at
every fixed query sequence.  Defining the game-relaxation as a ball would
discard exactly the conditional content CR18 §5.4 uses. -/
theorem gameRelaxation_subset_epsilonRelaxation {G : PDG Uni.{u} Uni.{u}}
    (hG : G.NonNeg) :
    gameRelaxation G ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation ν[G] {forget G} := by
  rintro S ⟨H, hHnn, hw, hHG, rfl⟩
  refine AbstractCryptography.Relaxation.mem_epsilonRelaxation_iff.mpr
    ⟨forget G, rfl, ?_⟩
  have hwe : (ofPhi (forget G)).weight = (ofPhi (forget H)).weight := by
    show (forget G).weight = (forget H).weight
    rw [weight_forget, weight_forget, hw]
  rw [edist_comm, edist_eq_advFullyDefined_of_weight_eq hwe]
  exact fundamental_lemma_of_game_playing hG hHnn hw.symm hHG.symm

/-- **The static radius**: Definition 2.36's `ω` in place of Definition 2.25's
`ν`, by Lanzenberger Theorem 2.37's trivial direction
(`supWinProb_le_infWinnability`) composed with the containment above.

This is one of the two compositions CR18's Lemma 5.3 is used for — "one can
view `S` as if it were `T`, as long as the game is not won", with a right-hand
side that mentions no environment.  Lemma 5.3 itself is
`forget_mem_gameRelaxation_of_condEquiv` below, and the *non-adaptive* radius
CR18 Theorem 4.17 reaches is
`gameRelaxation_enhance_subset_epsilonRelaxation_blind`.

Theorem 2.37 is an equality on the finite slice, so this is not a weaker bound
— it is the same number written without a supremum over strategies. -/
theorem gameRelaxation_subset_epsilonRelaxation_infWinnability
    {G : PDG Uni.{u} Uni.{u}} (hG : G.NonNeg)
    (hnil : ∀ g ∈ G.support, ([] : List Uni.{u}) ∉ g.2.1) :
    gameRelaxation G ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation ω[G] {forget G} := by
  intro S hS
  obtain ⟨R, hR, hSR⟩ :=
    AbstractCryptography.Relaxation.mem_epsilonRelaxation_iff.mp
      (gameRelaxation_subset_epsilonRelaxation hG hS)
  exact AbstractCryptography.Relaxation.mem_epsilonRelaxation_iff.mpr ⟨R, hR,
    hSR.trans (ENNReal.ofReal_le_ofReal (supWinProb_le_infWinnability hG hnil))⟩

/-! ## CR18 Lemma 5.3 -/

/-- **CR18 Lemma 5.3** (printed p. 121): "Consider a game `Ŝ` and a system `T`.
We have `Ŝ ⊨ T ⟹ S ⊆ T̂^⊥`, where the MBO for `T` (to result in game `T̂`) is
as described in the proof of Theorem 4.17, i.e., the inputs to `T` are also
given to `bŜ` and the MBO (of `T̂`) is the MBO of `Ŝ`, i.e., the MBO is defined
independently of `T`."

The game `T̂` the statement names is `PDG.enhance G T` — CR18 eq. (4.39) /
Maurer13b Theorem 3's display, landed in `Technique/BlindWinning.lean` — and
with it the lemma is **Lemma 5.2 applied to eq. (4.39)**: conditional
equivalence gives `Ŝ ≡ᵍ T̂` (`PDG.equivalentAsGames_enhance`), and Lemma 5.2
turns a `≡ᵍ` into a membership.  That is the source's own chaining; the proof
of Theorem 4.17 (printed p. 110) performs the same two steps.

The hypothesis bundle is eq. (4.39)'s: `T` normalized (a product law's weight
is a product) and one shared Definition 2.14 domain (the MBO of `Ŝ` reads the
history `Ŝ` answered, and `T̂`'s transcript exposes the history `T` answered).
See `Technique/BlindWinning.lean`'s module docstring for why neither is
totality.

This retires FLAG F-8: nothing here is a blinded-system *object*.  `bŜ` is the
landed attachment `attachEngineFully Set.univ (blockReplies Set.univ c)`
(`System/BlockReplies.lean`), and it does not even occur in the statement —
CR18 mentions it only to say where the MBO's inputs come from, and on this
carrier that is the second factor of a product law. -/
theorem forget_mem_gameRelaxation_of_condEquiv {G : PDG Uni.{u} Uni.{u}}
    {T : PDS Uni.{u} Uni.{u}} {D : Set (List Uni.{u})} (hG : G.NonNeg)
    (hT1 : T.weight = 1) (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    (hCE : CondEquiv G T) :
    forget G ∈ gameRelaxation (enhance G T) :=
  forget_mem_gameRelaxation_of_equivalentAsGames hG
    (by rw [weight_enhance, hT1, one_mul])
    (equivalentAsGames_enhance hT1 hdomG hdomT hCE)

open AbstractCryptography in
/-- **The non-adaptive radius**: CR18 Theorem 4.17's `Γ(bŜ)` in place of
Definition 2.25's `ν`, obtained by composing the `ν`-ball containment with
`PDG.supWinProb_enhance_le_blindSupWinProb` — Maurer13b Theorem 3's last step,
"`⟦DT⟧ ∈ NA` for any `D`".

This is the second composition Lemma 5.3 is used for, and the sharper of the
two: `νᴺᴬ ≤ ν = ω`, generally strictly (CR18 printed p. 109).  Note where the
radius is measured — it is the *original* game's blind winning probability, not
the enhanced game's `ν`, which is the whole content of the step. -/
theorem gameRelaxation_enhance_subset_epsilonRelaxation_blind
    {G : PDG Uni.{u} Uni.{u}} {T : PDS Uni.{u} Uni.{u}} {D : Set (List Uni.{u})}
    (hG : G.NonNeg) (hT : T.NonNeg) (hT1 : T.weight = 1)
    (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D) :
    gameRelaxation (enhance G T) ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation νᴺᴬ[G]
        {forget (enhance G T)} := by
  intro S hS
  obtain ⟨R, hR, hSR⟩ :=
    AbstractCryptography.Relaxation.mem_epsilonRelaxation_iff.mp
      (gameRelaxation_subset_epsilonRelaxation (nonNeg_enhance hG hT) hS)
  exact AbstractCryptography.Relaxation.mem_epsilonRelaxation_iff.mpr ⟨R, hR,
    hSR.trans (ENNReal.ofReal_le_ofReal
      (supWinProb_enhance_le_blindSupWinProb hG hT hT1 hdomG hdomT))⟩

/-! ## Compatibility (CR18 Definitions 5.6 and 5.7) -/

/-- **CR18 Definition 5.6 for the game-relaxation, converter half** (printed
p. 121: "We point out that game-relaxation is compatible according to
Definitions 5.6 and 5.7").

Descended, not re-proved: the containment above places `T̂^⊥` inside a
`ν`-ball, and `Relaxation.epsilonRelaxation_compatible` — CR18 §5.2.3's
criterion, "if all `γ ∈ Γ` are non-expanding for `d`, then the `ǫ`-relaxation
is compatible with `Γ`" — moves a converter across the ball.  Composing the two
says that applying a converter to any member of the game-relaxation lands
inside the `ν[T̂]`-ball around the converted centre — Definition 5.6's own
shape `π(ℛ^ρ) ⊆ (πℛ)^ρ`, with `ρ` read as the ball the game-relaxation sits
in.  (`Set.smul_set_singleton` turns the right-hand side into the singleton
`{π • T}` wherever a caller wants it.)

Stated over an arbitrary `Σ` acting non-expandingly on `Φ`, so it holds at once
for `converterMonoidAt` (the metric-facing Σ) and for `converterMonoidAtProb`
(CR18 Definition 3.17's converters, `System/ProbabilisticConverter.lean`); both
instances are registered.

The **parallel** half (Definition 5.7) is deferred: see the module docstring —
it needs the Φ-level conditional form of `IsNonexpandingPar`, which is S-14's
and lives in `ParFace.lean`'s metric section. -/
theorem smul_gameRelaxation_subset_epsilonRelaxation {Sigma : Type*}
    [SMul Sigma Phi.{u}] [AbstractCryptography.IsNonexpandingSMul Sigma Phi.{u}]
    (π : Sigma) {G : PDG Uni.{u} Uni.{u}} (hG : G.NonNeg) :
    π • gameRelaxation G ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation ν[G]
        (π • ({forget G} : AbstractCryptography.Specification Phi.{u})) :=
  subset_trans (Set.smul_set_mono (gameRelaxation_subset_epsilonRelaxation hG))
    (AbstractCryptography.Relaxation.epsilonRelaxation_compatible
      (Sigma := Sigma) (Φ := Phi.{u}) ν[G] π
      ({forget G} : AbstractCryptography.Specification Phi.{u}))

open scoped AbstractCryptography in
/-- **CR18 Definition 5.7 for the game-relaxation, second clause** — the frame
on the LEFT: `[𝒯, T̂^⊥] ⊆ [𝒯, T]^{ν[T̂]}`.

Descended, not re-proved: the containment in the `ν`-ball, then
`epsilonRelaxation_parF_left_subset` (`ParFace.lean`, S-14).  The hypotheses
are that theorem's own — sub-probability of every partner law — and nothing is
asked of the game.

Definition 5.7's unconditional `Relaxation.ParCompatible` is *not* claimed:
it needs `IsNonexpandingPar Φ`, which this carrier does not have (module
docstring). -/
theorem par_gameRelaxation_subset_epsilonRelaxation
    (𝒯 : AbstractCryptography.Specification Phi.{u}) {G : PDG Uni.{u} Uni.{u}}
    (hG : G.NonNeg) (h0 : ∀ T ∈ 𝒯, ∀ t, 0 ≤ ofPhi T t)
    (h1 : ∀ T ∈ 𝒯, (ofPhi T).weight ≤ 1) :
    𝒯 ∥ gameRelaxation G ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation ν[G]
        (𝒯 ∥ ({forget G} : AbstractCryptography.Specification Phi.{u})) := by
  refine subset_trans ?_ (epsilonRelaxation_parF_left_subset ν[G]
    ({forget G} : AbstractCryptography.Specification Phi.{u}) 𝒯 h0 h1)
  rintro x ⟨T, hT, y, hy, rfl⟩
  exact AbstractCryptography.par_mem_par hT
    (gameRelaxation_subset_epsilonRelaxation hG hy)

open scoped AbstractCryptography in
/-- **CR18 Definition 5.7 for the game-relaxation, first clause** — the frame
on the RIGHT: `[T̂^⊥, 𝒯] ⊆ [T, 𝒯]^{ν[T̂]}`.

Descended from `epsilonRelaxation_parF_right_subset_of_support` (`ParFace.lean`,
S-14), whose price this clause inherits in full: `parF · T` moves its own
splitting with its argument, so beyond sub-probability of the partner one
splitting `c` has to carry the game's own system *and* every member of the
game-relaxation, while missing the partner's face.  Those three hypotheses are
lane-A's, quoted here, not weakened. -/
theorem gameRelaxation_par_subset_epsilonRelaxation {c : Set Uni.{u}}
    (𝒯 : AbstractCryptography.Specification Phi.{u}) {G : PDG Uni.{u} Uni.{u}}
    (hG : G.NonNeg) (h0 : ∀ T ∈ 𝒯, ∀ t, 0 ≤ ofPhi T t)
    (h1 : ∀ T ∈ 𝒯, (ofPhi T).weight ≤ 1)
    (hT : ∀ T ∈ 𝒯, Disjoint (RandomSystems.support T) c)
    (hcentre : RandomSystems.support (forget G) ⊆ c)
    (hmem : ∀ S ∈ gameRelaxation G, RandomSystems.support S ⊆ c) :
    gameRelaxation G ∥ 𝒯 ⊆
      AbstractCryptography.Relaxation.epsilonRelaxation ν[G]
        (({forget G} : AbstractCryptography.Specification Phi.{u}) ∥ 𝒯) := by
  refine subset_trans ?_ (epsilonRelaxation_parF_right_subset_of_support ν[G]
    ({forget G} : AbstractCryptography.Specification Phi.{u}) 𝒯 h0 h1 hT ?_)
  · rintro x ⟨y, hy, T, hT', rfl⟩
    exact AbstractCryptography.par_mem_par
      ⟨gameRelaxation_subset_epsilonRelaxation hG hy, hmem y hy⟩ hT'
  · intro R hR
    have hRG : R = forget G := hR
    exact hRG ▸ hcentre

end PDG

end RandomSystems

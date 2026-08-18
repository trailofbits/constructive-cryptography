/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Technique.ConditionalEquivalence

/-!
# Completeness of the bad-event method

Maurer, Pietrzak, Renner, *Indistinguishability Amplification* (CRYPTO 2007),
printed pp. 138-142.  Every statement cited below was read on the rendered
page.

## What the technique's completeness says

`Technique/ConditionalEquivalence.lean` proves the *bound*: a game whose
not-won slice agrees with a second system bounds the distinguishing advantage
by Definition 2.25's `ν`.  Nothing there says the bound can be made tight, so a
lossy application leaves the reader unable to tell a real gap from a bad choice
of condition.  **MPR07 Lemma 5** (printed p. 140) is the converse of the bound:

> "For any two `(𝒳,𝒴)`-systems `S` and `T` there exist `(𝒳,𝒴×{0,1})`-random
> systems `Ŝ` and `T̂` with MBOs such that (i) `Ŝ⁻ ≡ S`, (ii) `T̂⁻ ≡ T`,
> (iii) `Ŝ⊣ ≡ T̂⊣`, and (iv) `δ_k^D(S,T) = ν_k^D(Ŝ) = ν_k^D(T̂)` for all `D`."

with footnote 16 "This also implies, for example, `Δ_k(S,T) = ν_k(Ŝ)`".

Its converse partner is **Lemma 4** (printed p. 139), which is the landed
`PDG.fundamental_lemma_of_game_playing`: restricted equivalence bounds the
transcript distance by `ν`.  Lemma 5 is *not* the converse of Maurer13b
Definition 13's conditional equivalence — that relation is genuinely
incomplete, and the reason is recorded in the obstruction section below.

## The recast dictionary (PHI-SPEC R11(a)) — no new objects

* `Ŝ`, `T̂` — games, `RandomSystems.PDG`, Lanzenberger Definition 2.22's pairs.
  MPR07's `(𝒳,𝒴×{0,1})` presentation is the derived view (`PDG.toBitLaw`), not
  a second carrier.
* `Ŝ⁻ ≡ S` (Definition 9(i), printed p. 138) — `PDS.GamesFor S` membership:
  `PDG.forget` is the marginal, and the forgetting law is stated against
  Lanzenberger Definition 2.17's class, not against a representative.
* `Ŝ⊣ ≡ T̂⊣` (Definition 9(ii) + **Definition 10**, printed p. 138: restricted
  equivalence, "equivalent as long as the MBO is 0") — equality of the two
  games' not-won laws, `PDG.notWonLaw`.  `PDG.EquivalentAsGames` (Maurer13b
  Definition 11) is the same relation at the fixed query lists.  No `S⊣` and no
  `S⁻` operator is introduced (R11(a)).
* `δ_k^D` (**Definition 12**, printed p. 140) — `Probability.statDist` of the
  two transcript laws at one environment and one interaction length; `Adv⊥`
  (Ruling R4) is the supremum of exactly that, so the `Δ`-versus-`δ` gap MPR07
  flags on p. 140 does not arise here (LEDGER finding F1).
* `ν_k^D` (Definition 11, printed p. 139) — `PDG.winningMass` at one `(e,n)`,
  and `PDG.supWinProb` = `ν[·]` for the supremum.

## What is proved here, and what is not

**Proved.**  MPR07's proof runs on two identities, and both transport.

* **eq. (3)** (printed p. 140) `δ(P,Q) = 1 − ∑ min(P,Q)` — the `Fintype`-free
  form the transcript carrier needs,
  `Probability.statDist_eq_weight_sub_sum_min_of_support_subset`, landed in
  `Probability/StatisticalDistance.lean` beside its `[Fintype]` instance.
* **eq. (4)** (printed p. 141) `p^Ŝ_{YⁱAᵢ|Xⁱ}(yⁱ,0,xⁱ) = m = min(p^S,p^T)` — here
  in three parts: `PDG.winningMass_eq_statDist_iff_notWonLaw_eq_min` shows the
  minimum is not one choice among many but the **only** not-won law a
  restricted-equivalent pair attaining the distance can have;
  `PDS.exists_gamesFor_notWonLaw_eq_trLawFullyDefined` is MPR07's "it remains
  to verify that there exists a system `Ŝ` satisfying (4)" — every sub-law of
  `S` is the not-won law of a game for `S`; and `PDS.notWonPart` is equation
  (4)'s split itself.

From them:

* `PDG.advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min` and its
  class-level form `PDS.advFullyDefined_eq_supWinProb_of_notWonLaw_eq_min` —
  **Lemma 5(iv) and footnote 16**: a restricted-equivalent pair whose common
  not-won law is `m` satisfies `Adv⊥(S,T) = ν(Ŝ) = ν(T̂)`.  This is the
  consumable half of completeness: exhibiting such a pair turns
  `fundamental_lemma_of_game_playing`'s bound into an equality.
* `PDS.exists_gamesFor_notWonLaw_eq_min` — **Lemma 5 at a fixed
  distinguisher**: for any honest `S`, `T` of equal weight and any one
  environment and interaction length, the tight pair exists, built by equation
  (4) on that interaction's transcript law.
* `PDS.exists_gamesFor_notWonLaw_eq_min_of_equivalent` — the equivalent corner,
  where the whole of Lemma 5 does hold uniformly, with Definition 2.20's
  never-won pole as the condition.
* `PDS.winning_probability_attainment_theorem` — **footnote 16 at the
  supremum**, with the pair *produced* rather than assumed: on Lanzenberger
  Theorem 2.31's attained representatives the atom-level meet `S′ ⊓ T′` carries
  the whole not-won mass, so `Adv⊥(S,T) = ν(Ŝ) = ν(T̂)` outright.  Its witness is
  two-valued, hence won at the empty history and **not** per-`D` tight — the
  theorem's docstring proves why no two-valued condition can be.

**Not proved: the quantifier order.**  Lemma 5's content is
`∀ S,T ∃ Ŝ,T̂ ∀ D ∀ k` — *one* pair of games serving every distinguisher — and
the games built above depend on `(e, n)`.  What blocks the uniform statement is
**a fixed presentation**, not the carrier: with the atoms of `S` themselves, two
environments sharing a prefix draw their surviving mass from the same branch
point (`PDG.mass_notWon_add_mass_notWon_le_notWonMass`), while equation (4)
prescribes each branch's surviving mass independently.  It is dissolved by a
Definition-2.17-equivalent **re-decomposition** of `S`, which Lanzenberger
licenses on the page (printed p. 23 fn. 8: a DDS defined for first inputs
`{x₁,…,x_q}` "can be represented equivalently as a tuple `(s_{x₁},…,s_{x_q})`";
printed p. 25, in the proof of Theorem 2.37: "an *arbitrary* joint distribution
of such PDS … defines a (unique) PDS") and for which AC has the machinery landed
(`System.DDS.glue`, `PDS.exists_finiteClassJointWitness_of_common_side_weights`
= Lemma 2.33, `PDS.successorTransform`/`PDS.prependTransform`).  The route is
MPR07 p. 141's own alive-conditional recursion
`p^Ŝ_{Y_i A_i | Xⁱ Yⁱ⁻¹ Aⁱ⁻¹}(y_i, 0, …) = m_{xⁱ,yⁱ} / m_{xⁱ⁻¹,yⁱ⁻¹}`
(footnote 17: `m_{x⁰,y⁰} = 1`) run by the landed Theorem-2.31 induction with
`min` in place of the coupling.

`PDG.notWonMass_eq_zero_of_condEquiv` records the other
half of the charter's correction: the relation MPR07 Lemma 5 completes is
**Lemma 4**'s restricted equivalence, not Maurer13b Definition 13's conditional
equivalence.

## Reading the papers against this file

* **Polarity.**  MPR07 (like Maurer13b, CR18 and this tree) reads `Aᵢ = 1` as
  *won*; Maurer02 reads `Aᵢ = 1` as the condition *satisfied*.  A Maurer02
  statement must be flipped before comparison.
* **`δ` versus `Δ`.**  MPR07 p. 140: "in general `Δ_k^D(S,T) ≤ δ_k^D(S,T)`, but
  for a computationally unbounded `D` that chooses the output bit optimally, we
  have `Δ_k^D = δ_k^D`."  Lemma 5's equality is with `δ`, the transcript
  distance.  `Adv⊥` is a `δ`-shaped object by construction, so the statements
  here need no optimal-decision hypothesis.
* **Definition numbers collide across the papers** (MPR07 Definition 9 is the
  MBO; Maurer02 Definition 9 is the distinguisher; Maurer13b Definition 9 is
  the game), so every citation carries paper *and* printed page.
-/


namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

open scoped RandomSystems.PDG

universe u v

variable {X : Type u} {Y : Type v}


namespace PDG

/-! ## MPR07 Definition 10 and equation (4), at one interaction

MPR07 **Definition 10** (printed p. 138) calls two systems with MBOs
*restricted equivalent* when `S⊣ ≡ T⊣`, i.e. "if they are equivalent as long as
the MBO is 0".  On this carrier that is equality of the two games' *not-won
laws*: `PDG.notWonLaw` is the transcript marginal of the not-won slice of
Lanzenberger Definition 2.21's game transcript law, and masking the output once
the condition has fired changes nothing else about the interaction record.
`PDG.EquivalentAsGames` (Maurer13b **Definition 11**, printed p. 3153) is the
same relation stated at the fixed query lists.  No `S⊣` operator is introduced
(PHI-SPEC R11(a)). -/

/-- Restricted equivalence forces the common not-won law below **both**
transcript laws: it is dominated by its own game's law
(`notWonLaw_le_trLawFullyDefined_forget`) and, being the other game's not-won
law as well, by that game's law too.

This is the inequality that makes MPR07 equation (4)'s `min` the *only*
candidate: `m_{xⁱ,yⁱ} := min(p^S_{Yⁱ|Xⁱ}, p^T_{Yⁱ|Xⁱ})` is not a choice, it is
the ceiling. -/
theorem notWonLaw_le_min_of_eq {G H : PDG X Y} (hG : G.NonNeg) (hH : H.NonNeg)
    {e : System.DDE.Total Y X} {n : ℕ}
    (h : notWonLaw e n G = notWonLaw e n H) (t : List (X × Option Y)) :
    notWonLaw e n G t
      ≤ min (PDS.trLawFullyDefined e n (forget G) t)
          (PDS.trLawFullyDefined e n (forget H) t) :=
  le_min (notWonLaw_le_trLawFullyDefined_forget hG e n t)
    (by rw [h]; exact notWonLaw_le_trLawFullyDefined_forget hH e n t)

/-- The not-won law lives inside the support of its own game's transcript law:
non-negativity plus the domination `notWonLaw ≤ trLaw (forget G)`. -/
theorem support_notWonLaw_subset {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) :
    (notWonLaw e n G).support ⊆ (PDS.trLawFullyDefined e n (forget G)).support := by
  intro t ht
  rw [Finsupp.mem_support_iff] at ht ⊢
  intro hzero
  exact ht (le_antisymm (hzero ▸ notWonLaw_le_trLawFullyDefined_forget hG e n t)
    (nonNeg_notWonLaw hG e n t))

/-- **MPR07 equation (4), printed p. 141, as a characterization.**  For a
restricted-equivalent pair of games, the winning probability at one environment
and one interaction length equals MPR07 Definition 12's transcript distance
`δ_k^D` **exactly when** the common not-won law is the pointwise minimum of the
two transcript laws — which is what equation (4) writes as
`p^Ŝ_{YⁱAᵢ|Xⁱ}(yⁱ,0,xⁱ) := m_{xⁱ,yⁱ} = min(p^S_{Yⁱ|Xⁱ}, p^T_{Yⁱ|Xⁱ})`.

The proof is MPR07's own: equation (3) (printed p. 140) writes `δ` as
`|S| − ∑ min`, Definition 2.25's winning mass is `|G| − ∑ notWonLaw`
(`winningMass_add_notWonMass`), and `notWonLaw ≤ min` pointwise
(`notWonLaw_le_min_of_eq`), so the two sums agree exactly when the summands do.

Neither direction needs equal weights or a query bound: both sides are read at
one and the same interaction. -/
theorem winningMass_eq_statDist_iff_notWonLaw_eq_min {G H : PDG X Y}
    (hG : G.NonNeg) (hH : H.NonNeg) {e : System.DDE.Total Y X} {n : ℕ}
    (h : notWonLaw e n G = notWonLaw e n H) :
    winningMass e n G
        = statDist (PDS.trLawFullyDefined e n (forget G))
            (PDS.trLawFullyDefined e n (forget H))
      ↔ ∀ t, notWonLaw e n G t
          = min (PDS.trLawFullyDefined e n (forget G) t)
              (PDS.trLawFullyDefined e n (forget H) t) := by
  classical
  set μ := PDS.trLawFullyDefined e n (forget G) with hμ
  set ν := PDS.trLawFullyDefined e n (forget H) with hν
  set s : Finset (List (X × Option Y)) := μ.support ∪ ν.support with hs
  have hμs : μ.support ⊆ s := Finset.subset_union_left
  have hνs : ν.support ⊆ s := Finset.subset_union_right
  have hws : (notWonLaw e n G).support ⊆ s :=
    (support_notWonLaw_subset hG e n).trans hμs
  have hle : ∀ t ∈ s, notWonLaw e n G t ≤ min (μ t) (ν t) :=
    fun t _ => notWonLaw_le_min_of_eq hG hH h t
  have hδ : statDist μ ν = G.weight - ∑ t ∈ s, min (μ t) (ν t) := by
    rw [Probability.statDist_eq_weight_sub_sum_min_of_support_subset μ ν hμs hνs,
      hμ, PDS.weight_trLawFullyDefined, weight_forget]
  have hwin : winningMass e n G = G.weight - ∑ t ∈ s, notWonLaw e n G t := by
    have h1 : notWonMass e n G = ∑ t ∈ s, notWonLaw e n G t :=
      (weight_notWonLaw e n G).symm.trans
        (Distribution.weight_eq_sum_of_support_subset _ hws)
    linarith [winningMass_add_notWonMass e n G]
  constructor
  · intro heq t
    have hsum : ∑ t ∈ s, notWonLaw e n G t = ∑ t ∈ s, min (μ t) (ν t) := by
      rw [hδ, hwin] at heq; linarith
    by_cases hts : t ∈ s
    · exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum t hts
    · have hμz : μ t = 0 := by
        by_contra hc; exact hts (hμs (Finsupp.mem_support_iff.mpr hc))
      have hνz : ν t = 0 := by
        by_contra hc; exact hts (hνs (Finsupp.mem_support_iff.mpr hc))
      have hwz : notWonLaw e n G t = 0 := by
        by_contra hc; exact hts (hws (Finsupp.mem_support_iff.mpr hc))
      rw [hwz, hμz, hνz, min_self]
  · intro hpt
    rw [hδ, hwin, Finset.sum_congr rfl fun t _ => hpt t]

/-- **MPR07 Lemma 5(iv)'s second equality**, `ν_k^D(Ŝ) = ν_k^D(T̂)`: a
restricted-equivalent pair of games of equal weight wins with the same
probability at every interaction.  Equal weight is Lemma 5's standing setting
(its objects are probability systems) and is what `Adv⊥`'s own symmetry
statement carries (`PDS.advFullyDefined_comm_of_weight_eq`). -/
theorem winningMass_eq_winningMass_of_notWonLaw_eq {G H : PDG X Y}
    (hw : G.weight = H.weight) {e : System.DDE.Total Y X} {n : ℕ}
    (h : notWonLaw e n G = notWonLaw e n H) :
    winningMass e n G = winningMass e n H := by
  have hm : notWonMass e n G = notWonMass e n H := by
    rw [← weight_notWonLaw, ← weight_notWonLaw, h]
  linarith [winningMass_add_notWonMass e n G, winningMass_add_notWonMass e n H]

/-- Definition 2.25's supremum inherits the previous equality. -/
theorem supWinProb_eq_supWinProb_of_notWonLaw_eq {G H : PDG X Y}
    (hw : G.weight = H.weight)
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ), notWonLaw e n G = notWonLaw e n H) :
    supWinProb G = supWinProb H :=
  iSup_congr fun p => winningMass_eq_winningMass_of_notWonLaw_eq hw (h p.1 p.2)

/-! ## MPR07 Lemma 5(iv) and footnote 16, at the metric -/

/-- **MPR07 Lemma 5(iv)**, `δ_k^D(S,T) = ν_k^D(Ŝ)`, at every environment and
interaction length: a restricted-equivalent pair of games whose common not-won
law is equation (4)'s minimum wins with exactly the transcript distance.  This
is the hypothesis-side reading of
`winningMass_eq_statDist_iff_notWonLaw_eq_min`, packaged for the two
metric-level consumers below. -/
theorem winningMass_eq_statDist_of_notWonLaw_eq_min {G H : PDG X Y}
    (hG : G.NonNeg) (hH : H.NonNeg)
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ), notWonLaw e n G = notWonLaw e n H)
    (hmin : ∀ (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)),
      notWonLaw e n G t
        = min (PDS.trLawFullyDefined e n (forget G) t)
            (PDS.trLawFullyDefined e n (forget H) t))
    (e : System.DDE.Total Y X) (n : ℕ) :
    winningMass e n G
      = statDist (PDS.trLawFullyDefined e n (forget G))
          (PDS.trLawFullyDefined e n (forget H)) :=
  (winningMass_eq_statDist_iff_notWonLaw_eq_min hG hH (h e n)).mpr (hmin e n)

/-- **MPR07 Lemma 5, footnote 16** (printed p. 140): "This also implies, for
example, `Δ_k(S,T) = ν_k(Ŝ)`."  Under Ruling R4 the left-hand side is `Adv⊥`,
which is the supremum over environments and interaction lengths of exactly
MPR07 Definition 12's `δ_k^D`, so the footnote's step is the supremum of the
per-interaction equality — the `Δ`-versus-`δ` maximisation MPR07 needs on
p. 140 does not arise (LEDGER finding F1).

`≤` is `fundamental_lemma_of_game_playing`'s bound read at each interaction;
`≥` is the same equality in the other direction, transported across
`ENNReal.ofReal` by the finiteness of the advantage (a supremum of statistical
distances of laws of equal weight). -/
theorem advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min {G H : PDG X Y}
    (hG : G.NonNeg) (hH : H.NonNeg)
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ), notWonLaw e n G = notWonLaw e n H)
    (hmin : ∀ (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)),
      notWonLaw e n G t
        = min (PDS.trLawFullyDefined e n (forget G) t)
            (PDS.trLawFullyDefined e n (forget H) t)) :
    PDS.advFullyDefined (forget G) (forget H) = ν[G] := by
  have htight := winningMass_eq_statDist_of_notWonLaw_eq_min hG hH h hmin
  refine le_antisymm (iSup_le fun e => iSup_le fun n => ?_) ?_
  · exact ENNReal.ofReal_le_ofReal
      ((htight e n) ▸ winningMass_le_supWinProb hG e n)
  · rcases eq_or_ne (PDS.advFullyDefined (forget G) (forget H)) ⊤ with htop | htop
    · rw [htop]; exact le_top
    · refine le_trans (ENNReal.ofReal_le_ofReal ?_)
        (le_of_eq (ENNReal.ofReal_toReal htop))
      refine supWinProb_le_of_forall fun e n => ?_
      refine (ENNReal.ofReal_le_iff_le_toReal htop).mp ?_
      rw [htight e n]
      exact le_iSup_of_le e (le_iSup_of_le n le_rfl)


end PDG


namespace PDS

/-! ## MPR07 equation (4) built: the tight condition at one interaction

MPR07's proof (printed p. 141) *defines* `Ŝ` by equation (4),
`p^Ŝ_{YⁱAᵢ|Xⁱ}(yⁱ,0,xⁱ) := m_{xⁱ,yⁱ} = min(p^S_{Yⁱ|Xⁱ}, p^T_{Yⁱ|Xⁱ})`, and then
verifies "that there exists a system `Ŝ` satisfying (4)".  On this carrier a
game is a law over Lanzenberger Definition 2.20 pairs, so the verification is a
construction: split each deterministic atom's mass into the part that keeps the
condition unfired and the part that fires it, in the ratio equation (4)
prescribes for the transcript that atom produces.

`notWonPart` is that split.  Its own transcript law is exactly `m`
(`trLawFullyDefined_notWonPart`), which is the whole content of equation (4)
at one interaction. -/

/-- The part of `S` that equation (4) (MPR07, printed p. 141) leaves not won at
the interaction `(e, n)`: each deterministic atom keeps the fraction
`m_{xⁱ,yⁱ} / p^S_{Yⁱ|Xⁱ}` of its mass, where the transcript `(xⁱ,yⁱ)` is the one
that atom produces against `e` in `n` moves and `m` is equation (4)'s minimum.

Division by zero is `0` in this library's scalars, which is the right value:
an atom whose transcript carries no `S`-mass carries none here either.  The two
facts that matter are `notWonPart_le` (it is a sub-law of `S`) and
`trLawFullyDefined_notWonPart` (its transcript law is `m` on the nose). -/
def notWonPart (e : System.DDE.Total Y X) (n : ℕ) (S T : PDS X Y) : PDS X Y :=
  Finsupp.onFinset S.support
    (fun s =>
      min (trLawFullyDefined e n S (System.DDE.Total.transcript s e n))
          (trLawFullyDefined e n T (System.DDE.Total.transcript s e n))
        / trLawFullyDefined e n S (System.DDE.Total.transcript s e n) * S s)
    (fun s hs => by
      by_contra hc
      simp only [Finsupp.notMem_support_iff.mp hc, mul_zero, ne_eq,
        not_true_eq_false] at hs)

@[simp] theorem notWonPart_apply (e : System.DDE.Total Y X) (n : ℕ)
    (S T : PDS X Y) (s : System.DDS X Y) :
    notWonPart e n S T s =
      min (trLawFullyDefined e n S (System.DDE.Total.transcript s e n))
          (trLawFullyDefined e n T (System.DDE.Total.transcript s e n))
        / trLawFullyDefined e n S (System.DDE.Total.transcript s e n) * S s :=
  rfl

theorem support_notWonPart_subset (e : System.DDE.Total Y X) (n : ℕ)
    (S T : PDS X Y) : (notWonPart e n S T).support ⊆ S.support :=
  Finsupp.support_onFinset_subset

/-- Equation (4)'s fraction is a fraction: between `0` and `1` on honest laws. -/
theorem notWonPart_ratio_mem (e : System.DDE.Total Y X) (n : ℕ)
    {S T : PDS X Y} (hS : S.NonNeg) (hT : T.NonNeg) (t : List (X × Option Y)) :
    0 ≤ min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)
          / trLawFullyDefined e n S t ∧
      min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)
          / trLawFullyDefined e n S t ≤ 1 := by
  have hSt : 0 ≤ trLawFullyDefined e n S t := by
    rw [trLawFullyDefined]; exact hS.fTransform _ t
  have hTt : 0 ≤ trLawFullyDefined e n T t := by
    rw [trLawFullyDefined]; exact hT.fTransform _ t
  rcases eq_or_lt_of_le hSt with hzero | hpos
  · rw [← hzero, div_zero]; exact ⟨le_rfl, zero_le_one⟩
  · refine ⟨div_nonneg (le_min hSt hTt) hSt, ?_⟩
    rw [div_le_one hpos]
    exact min_le_left _ _

theorem notWonPart_nonNeg (e : System.DDE.Total Y X) (n : ℕ)
    {S T : PDS X Y} (hS : S.NonNeg) (hT : T.NonNeg) :
    (notWonPart e n S T).NonNeg := fun s => by
  rw [notWonPart_apply]
  exact mul_nonneg (notWonPart_ratio_mem e n hS hT _).1 (hS s)

theorem notWonPart_le (e : System.DDE.Total Y X) (n : ℕ)
    {S T : PDS X Y} (hS : S.NonNeg) (hT : T.NonNeg) (s : System.DDS X Y) :
    notWonPart e n S T s ≤ S s := by
  rw [notWonPart_apply]
  calc _ ≤ 1 * S s :=
        mul_le_mul_of_nonneg_right (notWonPart_ratio_mem e n hS hT _).2 (hS s)
    _ = S s := one_mul _

theorem nonNeg_sub_notWonPart (e : System.DDE.Total Y X) (n : ℕ)
    {S T : PDS X Y} (hS : S.NonNeg) (hT : T.NonNeg) :
    (S - notWonPart e n S T).NonNeg := fun s => by
  rw [Finsupp.sub_apply, sub_nonneg]
  exact notWonPart_le e n hS hT s

/-- **MPR07 equation (4)** (printed p. 141) at one interaction: the transcript
law of the not-won part is the pointwise minimum `m_{xⁱ,yⁱ}` of the two
transcript laws.

The computation is the paper's: the fraction equation (4) prescribes depends on
the atom only through the transcript it produces, so it comes out of the fiber
sum and multiplies `p^S_{Yⁱ|Xⁱ}` back to `m`. -/
theorem trLawFullyDefined_notWonPart (e : System.DDE.Total Y X) (n : ℕ)
    {S T : PDS X Y} (hS : S.NonNeg) (hT : T.NonNeg) (t : List (X × Option Y)) :
    trLawFullyDefined e n (notWonPart e n S T) t
      = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t) := by
  classical
  have hSt : 0 ≤ trLawFullyDefined e n S t := by
    rw [trLawFullyDefined]; exact hS.fTransform _ t
  have hTt : 0 ≤ trLawFullyDefined e n T t := by
    rw [trLawFullyDefined]; exact hT.fTransform _ t
  have hmassS : S.mass (fun s => System.DDE.Total.transcript s e n = t)
      = trLawFullyDefined e n S t := by
    rw [trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
  have key : trLawFullyDefined e n (notWonPart e n S T) t
      = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)
          / trLawFullyDefined e n S t
        * S.mass fun s => System.DDE.Total.transcript s e n = t := by
    rw [trLawFullyDefined, Distribution.fTransform_apply_eq_mass,
      Distribution.mass_eq_sum_of_support_subset _
        (support_notWonPart_subset e n S T) _,
      Distribution.mass_eq_sum_of_support_subset S (le_refl S.support) _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [notWonPart_apply, (Finset.mem_filter.mp hs).2]
  rw [key, hmassS]
  rcases eq_or_lt_of_le hSt with hzero | hpos
  · rw [← hzero, div_zero, zero_mul, min_eq_left (hzero ▸ hTt)]
  · rw [div_mul_cancel₀ _ (ne_of_gt hpos)]

/-! ## "It remains to verify that there exists a system `Ŝ` satisfying (4)"

MPR07's verification step (printed p. 141).  On this carrier it is the
statement that **every sub-law of `S` is the not-won law of a game for `S`**:
split each atom's mass, give the kept part Lanzenberger Definition 2.20's
never-won condition `⊥` and the discarded part the already-won condition `⊤`.
Remark 2.24's `adjoin` cannot do this — it attaches *one* condition per atom —
which is exactly the "degrees of freedom in the definition of `Ŝ`" MPR07
records on the same page. -/

/-- Every sub-law `R` of `S` is the not-won law of a game for `S`, at **every**
environment and interaction length: `R` carries the never-won condition and
`S − R` the already-won one, so the forgetting law holds on the nose and the
not-won slice is `R`'s own transcript law.

This is MPR07's p. 141 consistency step in the form this carrier needs, and it
is also the exact statement of what a *two-valued* condition can do: the
resulting not-won law has the constant weight `|R|` at every interaction.  A
condition that fires *during* the interaction is what a varying not-won mass
needs — see `PDG.notWonMass_playQueries_mono` below. -/
theorem exists_gamesFor_notWonLaw_eq_trLawFullyDefined {S R : PDS X Y}
    (hR : R.NonNeg) (hSR : (S - R).NonNeg) :
    ∃ G : GamesFor S, G.1.NonNeg ∧ PDG.forget G.1 = S ∧
      ∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.notWonLaw e n G.1 = trLawFullyDefined e n R := by
  classical
  set G : PDG X Y :=
    Distribution.fTransform (fun s => (s, (⊥ : System.MonotoneCondition X))) R
      + Distribution.fTransform
          (fun s => (s, (⊤ : System.MonotoneCondition X))) (S - R) with hGdef
  have hforget : PDG.forget G = S := by
    have h1 : Distribution.fTransform (Prod.fst ∘ fun s : System.DDS X Y =>
        (s, (⊥ : System.MonotoneCondition X))) R = R := Distribution.fTransform_id R
    have h2 : Distribution.fTransform (Prod.fst ∘ fun s : System.DDS X Y =>
        (s, (⊤ : System.MonotoneCondition X))) (S - R) = S - R :=
      Distribution.fTransform_id (S - R)
    rw [hGdef, PDG.forget, Distribution.fTransform_add,
      Distribution.fTransform_fTransform, Distribution.fTransform_fTransform,
      h1, h2]
    abel
  have hnn : G.NonNeg := by
    rw [hGdef]
    intro g
    exact add_nonneg (hR.fTransform _ g) (hSR.fTransform _ g)
  have hlaw : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      PDG.notWonLaw e n G = trLawFullyDefined e n R := by
    intro e n
    refine Finsupp.ext fun t => ?_
    rw [PDG.notWonLaw_apply, hGdef, Distribution.mass_add,
      Distribution.mass_fTransform, Distribution.mass_fTransform,
      Distribution.mass_eq_zero_of_forall_not (S - R)
        (P := fun s => ¬ System.Won (s, (⊤ : System.MonotoneCondition X)) e n ∧
          System.DDE.Total.transcript s e n = t)
        (fun s hs => hs.1 (System.won_top s e n)),
      add_zero, trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
    exact Distribution.mass_congr R fun s =>
      ⟨fun h => h.2, fun h => ⟨System.not_won_bot s e n, h⟩⟩
  exact ⟨⟨G, hforget ▸ equivalent_refl S⟩, hnn, hforget, hlaw⟩

/-- **MPR07 Lemma 5 at a fixed distinguisher** (printed p. 140, construction
eq. (4) p. 141).  For any two honest systems of equal weight and any one
environment and interaction length there are games `Ŝ` for `S` and `T̂` for `T`
with

* (i)/(ii) the forgetting law on the nose — `PDG.forget Ŝ = S`, `PDG.forget T̂ = T`
  (`PDS.GamesFor` membership is Lemma 5's `Ŝ⁻ ≡ S`, and here it holds as an
  equality of laws, not merely up to Definition 2.17);
* (iii) restricted equivalence *at that interaction* — the two not-won laws are
  equal, and both are equation (4)'s minimum `m_{xⁱ,yⁱ}`;
* (iv) `δ_k^D(S,T) = ν_k^D(Ŝ) = ν_k^D(T̂)` at that interaction, with
  `δ` = `Probability.statDist` of the two transcript laws (Definition 12,
  printed p. 140).

**This is not Lemma 5.**  Lemma 5 quantifies `∃ Ŝ,T̂` *before* `∀ D`; here the
games depend on `(e, n)`.  The obstruction is recorded in the section below,
and it is a carrier fact: the not-won mass of a *fixed* game is monotone along
the query tree, while the quantity it must equal, `|S| − δ`, is monotone in the
same direction only in aggregate, not along each atom. -/
theorem exists_gamesFor_notWonLaw_eq_min {S T : PDS X Y} (hS : S.NonNeg)
    (hT : T.NonNeg) (hw : S.weight = T.weight) (e : System.DDE.Total Y X)
    (n : ℕ) :
    ∃ (G : GamesFor S) (H : GamesFor T),
      G.1.NonNeg ∧ H.1.NonNeg ∧ PDG.forget G.1 = S ∧ PDG.forget H.1 = T ∧
      PDG.notWonLaw e n G.1 = PDG.notWonLaw e n H.1 ∧
      (∀ t, PDG.notWonLaw e n G.1 t
        = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)) ∧
      PDG.winningMass e n G.1
        = statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T) ∧
      PDG.winningMass e n H.1
        = statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T) := by
  obtain ⟨G, hGnn, hGforget, hGlaw⟩ :=
    exists_gamesFor_notWonLaw_eq_trLawFullyDefined
      (S := S) (R := notWonPart e n S T) (notWonPart_nonNeg e n hS hT)
      (nonNeg_sub_notWonPart e n hS hT)
  obtain ⟨H, hHnn, hHforget, hHlaw⟩ :=
    exists_gamesFor_notWonLaw_eq_trLawFullyDefined
      (S := T) (R := notWonPart e n T S) (notWonPart_nonNeg e n hT hS)
      (nonNeg_sub_notWonPart e n hT hS)
  have hGmin : ∀ t, PDG.notWonLaw e n G.1 t
      = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t) := fun t => by
    rw [hGlaw e n]; exact trLawFullyDefined_notWonPart e n hS hT t
  have hHmin : ∀ t, PDG.notWonLaw e n H.1 t
      = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t) := fun t => by
    rw [hHlaw e n, trLawFullyDefined_notWonPart e n hT hS t, min_comm]
  have heq : PDG.notWonLaw e n G.1 = PDG.notWonLaw e n H.1 :=
    Finsupp.ext fun t => (hGmin t).trans (hHmin t).symm
  have hGwin : PDG.winningMass e n G.1
      = statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T) := by
    have := (PDG.winningMass_eq_statDist_iff_notWonLaw_eq_min hGnn hHnn heq).mpr
      (by rw [hGforget, hHforget]; exact hGmin)
    rwa [hGforget, hHforget] at this
  have hHwin : PDG.winningMass e n H.1
      = statDist (trLawFullyDefined e n S) (trLawFullyDefined e n T) := by
    rw [← hGwin]
    exact (PDG.winningMass_eq_winningMass_of_notWonLaw_eq
      (by rw [GamesFor.weight_eq G, GamesFor.weight_eq H, hw]) heq).symm
  exact ⟨G, H, hGnn, hHnn, hGforget, hHforget, heq, hGmin, hGwin, hHwin⟩


/-! ## The endpoint at the equivalence class

MPR07 states Lemma 5 for *random systems*, and p. 133 §1.3 is explicit that
`Ŝ` and `T̂` are "**new systems** … which are **equivalent** to `S` and `T`".
`PDS.GamesFor` carries exactly that: membership is Lanzenberger Definition
2.17's relation, so the endpoint below never mentions a representative. -/

/-- **MPR07 Lemma 5(iv) + footnote 16, at the class.**  A pair of games — one
for `S`, one for `T` — that is restricted equivalent at every interaction and
whose common not-won law is equation (4)'s minimum attains the distance:
`Adv⊥(S,T) = ν(Ŝ) = ν(T̂)`.

This is the *consumable* half of completeness.  It says that exhibiting such a
pair turns the `fundamental_lemma_of_game_playing` bound into an equality, so a
gap left by an application is a gap in the chosen condition and not in the
technique.  The existential half — that such a pair always exists — is MPR07's
own statement and is discussed in the obstruction section. -/
theorem advFullyDefined_eq_supWinProb_of_notWonLaw_eq_min {S T : PDS X Y}
    (hw : S.weight = T.weight)
    (G : GamesFor S) (H : GamesFor T) (hG : G.1.NonNeg) (hH : H.1.NonNeg)
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ),
      PDG.notWonLaw e n G.1 = PDG.notWonLaw e n H.1)
    (hmin : ∀ (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)),
      PDG.notWonLaw e n G.1 t
        = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)) :
    advFullyDefined S T = ν[G.1] ∧ advFullyDefined S T = ν[H.1] := by
  have hmin' : ∀ (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)),
      PDG.notWonLaw e n G.1 t
        = min (trLawFullyDefined e n (PDG.forget G.1) t)
            (trLawFullyDefined e n (PDG.forget H.1) t) := by
    intro e n t
    rw [G.2 e n, H.2 e n]
    exact hmin e n t
  have hadv : advFullyDefined S T = ν[G.1] := by
    rw [advFullyDefined_congr (equivalent_symm G.2) (equivalent_symm H.2)]
    exact PDG.advFullyDefined_forget_eq_supWinProb_of_notWonLaw_eq_min hG hH h hmin'
  refine ⟨hadv, hadv.trans ?_⟩
  exact congrArg ENNReal.ofReal
    (PDG.supWinProb_eq_supWinProb_of_notWonLaw_eq
      (by rw [GamesFor.weight_eq G, GamesFor.weight_eq H]; exact hw) h)

/-! ### Receipt: the equivalent corner, uniformly in the distinguisher

Where `S ≡ T` the whole of Lemma 5 holds on this carrier with Lanzenberger
Definition 2.20's never-won pole as the condition: the not-won law is the
transcript law itself, hence equation (4)'s minimum at every interaction, and
both sides of Lemma 5(iv) are `0`.  It is the degenerate corner, and it is the
one place where the `∀ D` quantifier costs nothing. -/
theorem exists_gamesFor_notWonLaw_eq_min_of_equivalent {S T : PDS X Y}
    (hS : S.NonNeg) (hT : T.NonNeg) (heq : equivalent S T) :
    ∃ (G : GamesFor S) (H : GamesFor T),
      G.1.NonNeg ∧ H.1.NonNeg ∧
      (∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.notWonLaw e n G.1 = PDG.notWonLaw e n H.1) ∧
      (∀ (e : System.DDE.Total Y X) (n : ℕ) (t : List (X × Option Y)),
        PDG.notWonLaw e n G.1 t
          = min (trLawFullyDefined e n S t) (trLawFullyDefined e n T t)) ∧
      advFullyDefined S T = ν[G.1] ∧ advFullyDefined S T = ν[H.1] := by
  refine ⟨adjoin S fun _ => ⊥, adjoin T fun _ => ⊥,
    nonNeg_adjoin hS _, nonNeg_adjoin hT _, fun e n => ?_, fun e n t => ?_, ?_⟩
  · rw [notWonLaw_adjoin_bot, notWonLaw_adjoin_bot, heq e n]
  · rw [notWonLaw_adjoin_bot, heq e n, min_self]
  · refine advFullyDefined_eq_supWinProb_of_notWonLaw_eq_min
      (weight_eq_of_equivalent heq) _ _
      (nonNeg_adjoin hS _) (nonNeg_adjoin hT _) (fun e n => ?_) (fun e n t => ?_)
    · rw [notWonLaw_adjoin_bot, notWonLaw_adjoin_bot, heq e n]
    · rw [notWonLaw_adjoin_bot, heq e n, min_self]

/-! ## MPR07 footnote 16 at the supremum

Footnote 16 (printed p. 140) reads: "This also implies, for example,
`Δ_k(S,T) = ν_k(Ŝ)` and `Δ_k^NA(S,T) = ν_k^NA(Ŝ)`."  At the *supremum* — where
`Adv⊥` lives, Ruling R4 — that consequence can be produced outright rather than
assumed, because Lanzenberger **Theorem 2.31**'s attainment half supplies
representatives whose own atom laws are exactly `Adv⊥(S,T)` apart
(`PDS.exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded`),
and at *those* representatives the atom-level minimum `S′ ⊓ T′` — the diagonal
of `Probability.optimalJoint` — already carries the whole not-won mass.

The coupling kernel is the right engine **there, and only there**: at an
arbitrary presentation the atom-level distance over-counts against the
transcript distance, which is why the per-interaction statements above run on
equation (3)'s min form and the atomwise split `PDS.notWonPart` instead. -/

/-- **MPR07 Lemma 5 footnote 16** (printed p. 140), at the supremum: for any two
honest systems of equal weight on a common `q`-bounded domain there exist a
game `Ŝ` for a representative of `S` and a game `T̂` for a representative of `T`
which are restricted equivalent at **every** environment and interaction length
(their not-won laws are equal) and whose winning probabilities are the distance:

  `Adv⊥(S,T) = ν(Ŝ) = ν(T̂)`.

So the `fundamental_lemma_of_game_playing` bound is *attained*: a gap left by an
application is a gap in the chosen condition, not in the technique.

**This is not Lemma 5.**  Lemma 5(iv) asks for `δ_k^D(S,T) = ν_k^D(Ŝ)` at every
distinguisher *separately*, and the witness built here provably fails that.  Its
condition is two-valued — Lanzenberger Definition 2.20's `⊤` on the discarded
mass — so `ν` is already achieved at `n = 0`, where the witness is **won at the
empty history**: outside MPR07 p. 138's "this bit … is initially set to 0"
reading and outside the `hnil` clause the `ω`/winnability endpoints carry.
Concretely, at `n = 0` both transcript laws are the point mass at `[]` with the
systems' (equal) weights, so `δ_0^D(S,T) = 0` while `ν_0^D(Ŝ) = Adv⊥(S,T)`;
per-`D` tightness would force `Adv⊥(S,T) = 0`.  More generally a condition that
never fires *during* the interaction has constant not-won mass, while equation
(4)'s is `|S| − δ_k^D`.

The hypothesis bundle is Theorem 2.31's own (`[Fintype X]`, honesty, one named
common domain, a query bound) plus **equal weight**, which is not decoration:
without it the `T̂` side reads `ν(T̂) = δ(S′,T′) + (|T′| − |S′|)`.  MPR07 has
equal weight standing — its objects are probability systems. -/
theorem winning_probability_attainment_theorem [Fintype X] {S T : PDS X Y}
    {D : Set (List X)} {q : ℕ} (hS : S.NonNeg) (hT : T.NonNeg)
    (hw : S.weight = T.weight) (hb : HaveCommonDomainAndBounded S T D q) :
    ∃ (S' T' : PDS X Y) (G : GamesFor S') (H : GamesFor T'),
      equivalent S S' ∧ equivalent T T' ∧ G.1.NonNeg ∧ H.1.NonNeg ∧
      PDG.forget G.1 = S' ∧ PDG.forget H.1 = T' ∧
      (∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.notWonLaw e n G.1 = PDG.notWonLaw e n H.1) ∧
      advFullyDefined S T = ν[G.1] ∧ advFullyDefined S T = ν[H.1] := by
  classical
  obtain ⟨S', T', hS'nn, hT'nn, hSS', hTT', hwS, hwT, hatt⟩ :=
    exists_equivalent_statDist_eq_advFullyDefined_of_commonDomain_bounded hS hT hb
  have hww : S'.weight = T'.weight := by rw [hwS, hwT, hw]
  have hsupp : (S' ⊓ T').support ⊆ S'.support ∪ T'.support := by
    intro a ha
    rw [Finsupp.mem_support_iff, Finsupp.inf_apply] at ha
    by_contra hc
    rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff,
      not_or, not_not, not_not] at hc
    rw [hc.1, hc.2, min_self] at ha
    exact ha rfl
  have hRw : (S' ⊓ T').weight = S'.weight - statDist S' T' := by
    rw [Distribution.weight_eq_sum_of_support_subset _ hsupp,
      Probability.statDist_eq_weight_sub_sum_min_of_support_subset S' T'
        Finset.subset_union_left Finset.subset_union_right]
    simp [Finsupp.inf_apply]
  have hRnn : (S' ⊓ T').NonNeg := fun a => by
    rw [Finsupp.inf_apply]; exact le_min (hS'nn a) (hT'nn a)
  obtain ⟨G, hGnn, hGf, hGlaw⟩ :=
    exists_gamesFor_notWonLaw_eq_trLawFullyDefined (S := S') (R := S' ⊓ T') hRnn
      (fun a => by rw [Finsupp.sub_apply, Finsupp.inf_apply, sub_nonneg]
                   exact min_le_left _ _)
  obtain ⟨H, hHnn, hHf, hHlaw⟩ :=
    exists_gamesFor_notWonLaw_eq_trLawFullyDefined (S := T') (R := S' ⊓ T') hRnn
      (fun a => by rw [Finsupp.sub_apply, Finsupp.inf_apply, sub_nonneg]
                   exact min_le_right _ _)
  have hconst : ∀ {U : PDS X Y} (K : GamesFor U), PDG.forget K.1 = U →
      (∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.notWonLaw e n K.1 = trLawFullyDefined e n (S' ⊓ T')) →
      U.weight = S'.weight →
      ∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.winningMass e n K.1 = statDist S' T' := by
    intro U K hKf hKlaw hUw e n
    have h1 : PDG.notWonMass e n K.1 = (S' ⊓ T').weight := by
      rw [← PDG.weight_notWonLaw, hKlaw e n, weight_trLawFullyDefined]
    have h2 : K.1.weight = U.weight := by rw [← PDG.weight_forget, hKf]
    have h3 := PDG.winningMass_add_notWonMass e n K.1
    rw [h1, h2, hUw] at h3
    linarith [hRw]
  have hwinG := hconst G hGf hGlaw rfl
  have hwinH := hconst H hHf hHlaw hww.symm
  have hsup : ∀ {U : PDS X Y} (K : GamesFor U), K.1.NonNeg →
      (∀ (e : System.DDE.Total Y X) (n : ℕ),
        PDG.winningMass e n K.1 = statDist S' T') →
      PDG.supWinProb K.1 = statDist S' T' := by
    intro U K hKnn hK
    refine le_antisymm (PDG.supWinProb_le_of_forall fun e n => le_of_eq (hK e n)) ?_
    have := PDG.winningMass_le_supWinProb hKnn
      (System.DDE.Total.playQueries ([] : List X)) 0
    rwa [hK] at this
  refine ⟨S', T', G, H, hSS', hTT', hGnn, hHnn, hGf, hHf, fun e n => ?_, ?_, ?_⟩
  · rw [hGlaw e n, hHlaw e n]
  · rw [hsup G hGnn hwinG, hatt]
  · rw [hsup H hHnn hwinH, hatt]


end PDS

namespace PDG

/-! ## The obstruction, and what it does and does not bind

MPR07's `Ŝ` is a *random system* — a family of conditional distributions
`p^Ŝ_{YⁱAᵢ|Xⁱ}` — and equation (4) fixes that family one query sequence at a
time.  A game here is Lanzenberger Definition 2.22's law over pairs `(s, A)`,
so a single realization commits, before the interaction starts, to an answer at
*every* input history and to a condition that fires at *every* input history.
Two environments that share a prefix and then diverge are two branches of one
commitment.

`mass_notWon_add_mass_notWon_le_notWonMass` is that constraint.  Read it with
`P₁`/`P₂` two disjoint classes of realizations and `e₁`, `e₂` two environments
agreeing up to move `m`: the masses that survive down the two branches are
drawn from the *same* mass that survived to the branch point.  MPR07 equation
(4) prescribes the surviving mass on each branch independently — it is
`min(p^S, p^T)` computed on that branch's own transcript law — and the two
prescriptions can exceed what the branch point has to give.

**What that binds is a fixed presentation, not the carrier.**  The bite comes
from atoms that answer a query the same way wherever it occurs; once `S` may be
re-decomposed — which Lanzenberger licenses, printed p. 23 fn. 8 and the
Theorem-2.37 proof on p. 25 — the surviving realizations may answer `x` one way
as the second query and another way as the third, and the inequality is
satisfied.  So the lemma is a tool for proving "*this* presentation cannot",
which is what it does in the worked example, and not a barrier to Lemma 5.  The
uniform statement is a construction (module docstring), not an open problem.

This is also why the completeness statement is about MPR07 Lemma 4's
restricted equivalence and not about Maurer13b Definition 13's conditional
equivalence: `CondEquiv G T` forces the not-won law to be a *multiple of `T`'s
whole transcript law*, while equation (4) makes it the pointwise minimum, and
the two agree only when one law dominates the other. -/

/-- **Why the completed relation is Lemma 4's and not Definition 13's.**
Maurer13b **Definition 13**'s conditional equivalence (`PDG.CondEquiv`) makes
the not-won law a *scalar multiple of `T`'s whole transcript law*, while MPR07
equation (4) makes it the *pointwise minimum* of the two transcript laws.  Where
`T` puts transcript mass that `S` does not, the two cannot be reconciled: the
minimum is `0` there, and conditional equivalence propagates that zero to the
whole not-won mass — the game is already won with probability one at that query
list, and `ν` returns the trivial bound `|G|`.

No tightness hypothesis is needed for this: honesty alone forces the not-won law
below `PDG.forget G`'s transcript law
(`notWonLaw_le_trLawFullyDefined_forget`), so the conclusion holds for **every**
game for `S`, not only for the ones equation (4) would pick.  Concretely, for
`S = ½δ_a + ½δ_b` and `T = ½δ_a + ½δ_c` at one query the distance is `½` while
every `CondEquiv` game for `S` against `T` has `ν = |G|`.

MPR07 Lemma 5 is therefore the converse of **Lemma 4** (restricted
equivalence), which is what the file proves; it is not a completeness statement
for Definition 13. -/
theorem notWonMass_eq_zero_of_condEquiv {G : PDG X Y} (hG : G.NonNeg)
    {T : PDS X Y} (hCE : CondEquiv G T) (l : List X)
    {t : List (X × Option Y)}
    (hzero : PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length
      (forget G) t = 0)
    (hpos : 0 < PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length
      T t) :
    notWonMass (System.DDE.Total.playQueries l) l.length G = 0 := by
  have h0 : notWonLaw (System.DDE.Total.playQueries l) l.length G t = 0 :=
    le_antisymm (hzero ▸ notWonLaw_le_trLawFullyDefined_forget hG _ _ t)
      (nonNeg_notWonLaw hG _ _ t)
  have hkey := condEquiv_apply hCE l t
  rw [h0, mul_zero] at hkey
  exact (mul_eq_zero.mp hkey.symm).resolve_right (ne_of_gt hpos)

/-- **The branch constraint.**  Two disjoint classes of realizations, followed
down two environments that agree up to move `m`, cannot between them keep more
mass unfired than the interaction had unfired at move `m`.

The three ingredients are all landed: `System.Won.mono` (winning is monotone
along one interaction), `System.won_congr_transcript` (the winning event reads
the run, not the environment), and the inclusion-exclusion identity
`Distribution.mass_or_add_mass_and`. -/
theorem mass_notWon_add_mass_notWon_le_notWonMass {G : PDG X Y} (hG : G.NonNeg)
    {e₁ e₂ : System.DDE.Total Y X} {m n₁ n₂ : ℕ} (h₁ : m ≤ n₁) (h₂ : m ≤ n₂)
    (hagree : ∀ g ∈ G.support,
      System.DDE.Total.transcript g.1 e₁ m = System.DDE.Total.transcript g.1 e₂ m)
    {P₁ P₂ : System.DDG X Y → Prop} (hdisj : ∀ g, ¬ (P₁ g ∧ P₂ g)) :
    G.mass (fun g => ¬ System.Won g e₁ n₁ ∧ P₁ g)
        + G.mass (fun g => ¬ System.Won g e₂ n₂ ∧ P₂ g)
      ≤ notWonMass e₁ m G := by
  classical
  have hstep₁ : G.mass (fun g => ¬ System.Won g e₁ n₁ ∧ P₁ g)
      ≤ G.mass (fun g => ¬ System.Won g e₁ m ∧ P₁ g) :=
    Distribution.mass_mono hG fun g hg => ⟨fun hc => hg.1 (hc.mono h₁), hg.2⟩
  have hstep₂ : G.mass (fun g => ¬ System.Won g e₂ n₂ ∧ P₂ g)
      ≤ G.mass (fun g => ¬ System.Won g e₁ m ∧ P₂ g) := by
    have h2a : G.mass (fun g => ¬ System.Won g e₂ n₂ ∧ P₂ g)
        ≤ G.mass (fun g => ¬ System.Won g e₂ m ∧ P₂ g) :=
      Distribution.mass_mono hG fun g hg => ⟨fun hc => hg.1 (hc.mono h₂), hg.2⟩
    have h2b : G.mass (fun g => ¬ System.Won g e₂ m ∧ P₂ g)
        = G.mass (fun g => ¬ System.Won g e₁ m ∧ P₂ g) :=
      Distribution.mass_congr_of_support G fun g hg =>
        and_congr_left fun _ =>
          not_congr (System.won_congr_transcript rfl (hagree g hg))
    exact h2a.trans (le_of_eq h2b)
  have hcover : G.mass (fun g => (¬ System.Won g e₁ m ∧ P₁ g)
        ∨ (¬ System.Won g e₁ m ∧ P₂ g))
      ≤ notWonMass e₁ m G := by
    rw [notWonMass_eq_mass_not_won]
    exact Distribution.mass_mono hG fun g hg => by rcases hg with h | h <;> exact h.1
  have hinter : G.mass (fun g => (¬ System.Won g e₁ m ∧ P₁ g)
      ∧ (¬ System.Won g e₁ m ∧ P₂ g)) = 0 :=
    Distribution.mass_eq_zero_of_forall_not G fun g hg => hdisj g ⟨hg.1.2, hg.2.2⟩
  have hsum := Distribution.mass_or_add_mass_and G
    (fun g => ¬ System.Won g e₁ m ∧ P₁ g) (fun g => ¬ System.Won g e₁ m ∧ P₂ g)
  linarith

end PDG



end

end RandomSystems

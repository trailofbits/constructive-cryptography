/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.Behaviour
import RandomSystems.System.Relabel

/-!
# Random games (Lanzenberger §2.3.3, Definitions 2.20–2.25)

Lanzenberger, *A Theory of Random Systems, Games, and Hardness Amplification*
(Diss. ETH 29554), §2.3.3, printed pp. 16–17.  The definitions are quoted in
the docstrings and were checked against the printed pages.

## The carrier: the pair is primitive

**Definition 2.20** (printed p. 17): "A *monotone condition* (or MC) for an
`(𝒳,𝒴)`-DDS `s` is a monotone predicate `A : 𝒳* → {0,1}`. A *deterministic
discrete `(𝒳,𝒴)`-game* (or an `(𝒳,𝒴)`-DDG) is a pair `(s, A)`, denoted by
`s^A`."  **Definition 2.22**: "A *probabilistic discrete `(𝒳,𝒴)`-game* (or an
`(𝒳,𝒴)`-PDG) is a distribution over `(𝒳,𝒴)`-DDG."

So `DDG X Y = DDS X Y × MonotoneCondition X` and `PDG X Y = Distribution (DDG
X Y)`: the probabilistic game is a *joint* law over (system, condition) pairs,
which is what makes Remark 2.24's adjoining expressible — the condition
sampled with a deterministic system may depend on that system, and that
dependence is the whole content of `p^A_{Aᵢ|XⁱYⁱAᵢ₋₁}` conditioning on the
outputs.  A law over pairs is *not* the same object as a pair of laws, and it
is not the same object as a system at a paired output alphabet.

The `(𝒳, 𝒴 × {0,1})` presentation (Maurer13b Definition 9; the form CR18 and
the quarry use) is a **derived view**, built here as `toBitSystem` with an
inverse on monotone-bit systems and both round-trip equalities.  The view is
faithful exactly on the conditions the domain supports (`DomainSupported`),
and the round trip records the one thing it cannot express: a condition
already satisfied at the empty history.

## Remark 2.23 holds by construction

**Remark 2.23**: "In general, an environment does not observe the monotone
condition.  This matters in the probabilistic case, where being able to
observe the MC may reveal information about the system's internal state that
would not be observable just from the system's outputs."

An environment here is `System.DDE.Total Y X = List (Option Y) → Option X`
(CR18 Definitions 3.6/3.7, the tree's total presentation).  Its argument type
mentions `Y` only: there is no term of the environment's type that could read
a condition, and the winning probability `supWinProb` quantifies over exactly
that type.  Blindness is therefore not a hypothesis, a converter, or a
predicate on environments — it is the type of the environment.  §6 below
proves the corresponding statement for the *derived* bit view, where the bit
is a real output and blindness has content: the environment sees the bit view
through `System.relabel id Prod.fst`, an existing generator of the converter
monoid, and its whole interaction record erases to the plain one.

## Definition 2.21 on the total presentation (the one carrier delta)

**Definition 2.21**: "The transcript of an `(𝒳,𝒴)`-DDG `s^A` under
`(𝒴,𝒳)`-DDE `e` … is the pair `(t, A(t'))`, where `t = tr(s,e)` … and
`t' ∈ 𝒳*` is `t` projected to the inputs."

The thesis interacts through *compatible* environments, which never query
outside the domain, so `t` projected to the inputs is the input history the
system processed.  This carrier interacts through the `⊥`-completion (Ruling
R1/R2): a query outside the domain is answered `none` and deleted from the
system-side history (CR18 Definition 3.3).  The condition is therefore
evaluated at `answeredQueries t = keptPrefix s (t↓ₓ)`
(`System.DDE.Total.answeredQueries_transcript`) — the input history the system
actually processed, which is the thesis's `t'` whenever no query is refused.
The quarry makes the same reading (`Q:RandomSystems/GameWinnability.lean:31`).
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v

variable {X : Type u} {Y : Type v}

/-! ## Definition 2.20: monotone conditions and deterministic games -/

/-- Lanzenberger **Definition 2.20**, footnote 7: "by *monotone* we mean that
if `A(t) = 1` then `A(t|t') = 1` for any extension `t|t'` of `t`".

COINAGE (the name only): the thesis says "monotone", and the tree already
spells the dual clause `PrefixClosed` this way, so the prefix order is written
out rather than routed through an order instance on `List X`. -/
def PrefixMonotone (A : List X → Bool) : Prop :=
  ∀ ⦃t t' : List X⦄, t <+: t' → A t = true → A t' = true

/-- Lanzenberger **Definition 2.20**: "A *monotone condition* (or MC) for an
`(𝒳,𝒴)`-DDS `s` is a monotone predicate `A : 𝒳* → {0,1}`."

The condition is an *input* predicate — it reads the query history and
nothing else — and it is attached to a system only by Definition 2.20's pair,
never bundled into it. -/
abbrev MonotoneCondition (X : Type u) : Type u :=
  {A : List X → Bool // PrefixMonotone A}

/-- Lanzenberger **Definition 2.20**: "A *deterministic discrete
`(𝒳,𝒴)`-game* (or an `(𝒳,𝒴)`-DDG) is a pair `(s, A)`, denoted by `s^A`."

The pair is the primitive object (PHI-SPEC R10); the `(𝒳, 𝒴 × {0,1})` form is
the derived view of §4. -/
abbrev DDG (X : Type u) (Y : Type v) : Type (max u v) :=
  DDS X Y × MonotoneCondition X

/-- The upper-set reading of Definition 2.20, as a lemma and not as the
definition (PHI-SPEC R10 refinement): a condition is monotone exactly when the
histories satisfying it are closed under extension — footnote 7's `A(t|t')`
with the extension written out. -/
theorem prefixMonotone_iff_append {A : List X → Bool} :
    PrefixMonotone A ↔ ∀ t t' : List X, A t = true → A (t ++ t') = true :=
  ⟨fun h t t' => h ⟨t', rfl⟩, fun h _ _ ⟨_, hpre⟩ ht => hpre ▸ h _ _ ht⟩

/-- The constantly false condition is monotone.  With it, Definition 2.20's
pair is the *never-won* game — the thesis's unnamed always-losing system `V`
in the alternative proof of Theorem 2.37 (printed p. 26), which the quarry
coins `zeroMBO` (`Q:RandomSystems/GameWinnability.lean:356`). -/
theorem prefixMonotone_const_false :
    PrefixMonotone (fun _ : List X => false) := by
  intro _ _ _ h
  simp at h

/-- The constantly true condition is monotone: the game already won at the
empty history.  It is the witness that Definition 2.20's pair says strictly
more than the bit-output view of §4 can (`domainSupported_ofBitSystem`). -/
theorem prefixMonotone_const_true :
    PrefixMonotone (fun _ : List X => true) := by
  intro _ _ _ _
  rfl

/-! ## Definition 2.21: the transcript of a game -/

/-- Lanzenberger **Definition 2.21**: "The transcript of an `(𝒳,𝒴)`-DDG `s^A`
under `(𝒴,𝒳)`-DDE `e`, denoted by `tr(s^A, e)`, is the pair `(t, A(t'))`,
where `t = tr(s,e)` is the transcript of `s` under `e` … and `t' ∈ 𝒳*` is `t`
projected to the inputs."

Stated over the tree's total presentation, at interaction length `n`: `t` is
`System.DDE.Total.transcript`, and `t'` is `answeredQueries t`, the input
history the system processed (see the module docstring). -/
def gameTranscript (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    List (X × Option Y) × Bool :=
  (DDE.Total.transcript g.1 e n,
    g.2.1 (answeredQueries (DDE.Total.transcript g.1 e n)))

@[simp] theorem gameTranscript_fst (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    (gameTranscript g e n).1 = DDE.Total.transcript g.1 e n := rfl

@[simp] theorem gameTranscript_snd (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    (gameTranscript g e n).2 =
      g.2.1 (answeredQueries (DDE.Total.transcript g.1 e n)) := rfl

/-- Lanzenberger **Definition 2.25**'s winning transcripts `𝒯_w`: "the
transcripts ending with `(·, 1)`" — the Definition 2.21 pair whose second
component is `1`.  A *winner* wins the game when the condition occurs during
the interaction (printed p. 17). -/
def Won (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) : Prop :=
  (gameTranscript g e n).2 = true

theorem won_iff (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    Won g e n ↔ g.2.1 (answeredQueries (DDE.Total.transcript g.1 e n)) = true :=
  Iff.rfl

/-- Winning is monotone along the interaction: Definition 2.20's monotonicity
of the condition, transported by `DDE.Total.answeredQueries_prefix`.  This is why
Definition 2.25's "ends with `(·,1)`" and the `∃`-form "some prefix of the
interaction satisfies the condition" describe the same event
(`exists_won_iff`) — the reading the quarry had to choose explicitly
(`Q:RandomSystems/GameWinnability.lean:105`). -/
theorem Won.mono {g : DDG X Y} {e : DDE.Total Y X} {m n : ℕ} (hmn : m ≤ n)
    (h : Won g e m) : Won g e n :=
  g.2.2 (DDE.Total.answeredQueries_prefix g.1 e hmn) h

theorem exists_won_iff (g : DDG X Y) (e : DDE.Total Y X) (n : ℕ) :
    (∃ m ≤ n, Won g e m) ↔ Won g e n :=
  ⟨fun ⟨_, hmn, h⟩ => h.mono hmn, fun h => ⟨n, le_rfl, h⟩⟩

end

end System

/-! ## Definition 2.22: probabilistic games -/

noncomputable section

open Classical

open Probability (Distribution)

universe u v

variable {X : Type u} {Y : Type v}

/-- Lanzenberger **Definition 2.22**: "A *probabilistic discrete
`(𝒳,𝒴)`-game* (or an `(𝒳,𝒴)`-PDG) is a distribution over `(𝒳,𝒴)`-DDG."

The distribution is over Definition 2.20's *pairs*, so the system and the
condition are jointly distributed; §5's `adjoin` is the constructor that
builds such a joint law from a system law and a per-atom condition. -/
abbrev PDG (X : Type u) (Y : Type v) : Type (max u v) :=
  Distribution (System.DDG X Y)

namespace PDG

/-- The Definition 2.21 observable at the law level: the distribution of the
game transcript `tr(S^A, e)` after `n` environment moves.  Definition 2.22's
equivalence of games, and Definition 2.25's `ν`, are functions of this law
alone (`winningMass_eq_mass_gameTrLaw`). -/
def gameTrLaw (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) :
    Distribution (List (X × Option Y) × Bool) :=
  Distribution.fTransform (fun g => System.gameTranscript g e n) G

/-- The mass of Definition 2.25's winning transcripts in one environment at
one interaction length: `Pr^{tr(S^A)}(tr(S^A,e) ∈ 𝒯_w)`. -/
def winningMass (e : System.DDE.Total Y X) (n : ℕ) (G : PDG X Y) : ℝ :=
  G.mass fun g => System.Won g e n

/-- Winning is an observable of the Definition 2.21 transcript law: the
winning mass reads only `gameTrLaw`, never the presentation. -/
theorem winningMass_eq_mass_gameTrLaw (e : System.DDE.Total Y X) (n : ℕ)
    (G : PDG X Y) :
    winningMass e n G = (gameTrLaw e n G).mass fun t => t.2 = true := by
  rw [gameTrLaw, Distribution.mass_fTransform]
  rfl

/-- Lanzenberger **Definition 2.25**: "For a random `(𝒳,𝒴)`-game `S^A`, we
define the supremum winning probability of `S^A` by
`ν(S^A) := sup_e Pr^{tr S^A}(tr(S^A,e) ∈ 𝒯_w)`, where `𝒯_w` denotes the set of
all winning transcripts, i.e., the transcripts ending with `(·,1)`."

The supremum is over *deterministic* environments — the thesis's own remark
before Definition 2.25: "This is sufficient, since in an information-theoretic
setting, one can always fix the randomness of a probabilistic environment to
be optimal."  On the tree's total presentation the environment is
`System.DDE.Total`, and the interaction length is a second index of the
supremum rather than a stopping hypothesis, exactly as in `advFullyDefined`
(Ruling R4).  **The index type is the whole content of Remark 2.23**: an
environment is a function of the output history alone, so no environment in
the supremum can observe the condition. -/
def supWinProb (G : PDG X Y) : ℝ :=
  ⨆ p : System.DDE.Total Y X × ℕ, winningMass p.1 p.2 G

/-- Lanzenberger Definition 2.25 notation: `ν(G)` is the supremum winning
probability. -/
scoped notation "ν(" G ")" => supWinProb G

theorem winningMass_nonneg {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : 0 ≤ winningMass e n G :=
  hG.mass_nonneg _

theorem winningMass_le_weight {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : winningMass e n G ≤ G.weight :=
  Distribution.mass_le_weight hG _

/-- The winning masses are bounded above by the weight, so Definition 2.25's
supremum is a genuine least upper bound.  Non-negativity is the hypothesis
that makes it one: on the signed carrier a supremum of masses need not be
bounded, which is the same phenomenon the thesis's `ω` guards against with its
own `NonNeg` conjunct. -/
theorem bddAbove_range_winningMass {G : PDG X Y} (hG : G.NonNeg) :
    BddAbove (Set.range fun p : System.DDE.Total Y X × ℕ =>
      winningMass p.1 p.2 G) := by
  refine ⟨G.weight, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact winningMass_le_weight hG p.1 p.2

/-- Definition 2.25's defining property, upper half. -/
theorem winningMass_le_supWinProb {G : PDG X Y} (hG : G.NonNeg)
    (e : System.DDE.Total Y X) (n : ℕ) : winningMass e n G ≤ supWinProb G :=
  le_ciSup (bddAbove_range_winningMass hG) (e, n)

/-- Definition 2.25's defining property, lower half. -/
theorem supWinProb_le_of_forall {G : PDG X Y} {c : ℝ}
    (h : ∀ (e : System.DDE.Total Y X) (n : ℕ), winningMass e n G ≤ c) :
    supWinProb G ≤ c :=
  ciSup_le fun p => h p.1 p.2

theorem supWinProb_nonneg {G : PDG X Y} (hG : G.NonNeg) : 0 ≤ supWinProb G :=
  le_trans (winningMass_nonneg hG (fun _ => none) 0)
    (winningMass_le_supWinProb hG (fun _ => none) 0)

theorem supWinProb_le_weight {G : PDG X Y} (hG : G.NonNeg) :
    supWinProb G ≤ G.weight :=
  supWinProb_le_of_forall fun e n => winningMass_le_weight hG e n

end PDG

end

end RandomSystems

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import RandomSystems.Technique.ConditionalEquivalence
import RandomSystems.System.BlockReplies

/-!
# Blind winning, and conditional equivalence at the non-adaptive bound

PAPER-FAITHFUL

Maurer, *Conditional Equivalence of Random Systems and Indistinguishability
Proofs* (ISIT 2013), **Definition 7 and Theorem 3, printed pp. 3152 and 3154**;
Cachin–Renner(–Maurer), *Lecture Notes on Cryptography*, **Definition 4.20 and
Theorem 4.17, printed pp. 109–110** (historical provenance — CR18 is
fallback-only under the source hierarchy).  Every statement cited below was
read on the rendered page.

## The one sentence this module formalizes

CR18 Definition 4.20 (printed p. 109), after defining the reply-blocking
converter `b`: "To win game `bS` means to win game `S` **blindly**, without
seeing the outputs.  Equivalently, this means to win the game *non-adaptively*
since the inputs `x₁,…,x_q` can be interpreted as being chosen in advance,
before seeing any outputs."  Maurer13b says the same thing from the other side
(Definition 7, printed p. 3152): `⟦DT⟧` is "the *non-adaptive* distinguisher …
that generates `Xᵢ` by interacting with `T` … ignoring `Yᵢ`".

So "blind" has two renderings, and the source asserts they agree:

* **the environment side** — restrict Definition 2.25's supremum to
  environments that cannot react to what they see, which on this carrier is the
  landed `System.DDE.Total.NonAdaptive` (Lanzenberger fn. 6,
  `System/ClassDistance.lean`);
* **the converter side** — leave the environment alone and put CR18 Definition
  4.20's `b` in front of the game, which on this carrier is the landed
  attachment `attachEngineFully` of the reply-erasing engine
  (`System/BlockReplies.lean`).

`PDG.supWinProb_blockRepliesGame` is that agreement, proved in both directions.
Per the T3.9 decision the tree states `ν` **once**: `blindSupWinProb` is
Definition 2.25's own supremum with its index set cut down, not a second
winning-probability operator, and `PDG.winningMass` is untouched.

## The theorem

`PDG.conditional_equivalence_theorem_blind` is Maurer13b **Theorem 3**'s "in
particular" clause / CR18 **Theorem 4.17**'s: conditional equivalence bounds
the *adaptive* distinguishing advantage by the *non-adaptive* winning
probability.  It is strictly stronger than the landed
`conditional_equivalence_theorem`, whose right-hand side is the adaptive `ν`
(and than `conditional_equivalence_theorem_infWinnability`, which is the same
number as `ν` by Theorem 2.37) — `νᴺᴬ ≤ ν = ω`, with the inequality strict in
general (CR18 p. 109: "generally lower").

The proof is the printed proof, three steps, each one named lemma:

1. `PDG.equivalentAsGames_enhance` — Theorem 3's display / CR18 eq. (4.39):
   enhance `T` with `Ŝ`'s MBO, independently of `T`, and the result is
   game-equivalent to `Ŝ`;
2. `PDG.fundamental_lemma_of_game_playing` (landed, Maurer13b Lemma 2) applied
   to that pair — this is the printed proof's "according to Lemma 2 … and
   Lemma 1, `Γ^D_q(Ŝ) = Γ^D_q(T̂)`, it suffices to analyze `Γ^D_q(T̂)`", which
   here is one application because `Adv⊥` is symmetric at equal weight
   (`PDS.advFullyDefined_comm_of_weight_eq`) and the landed lemma may therefore
   be read with the *enhanced* game supplying the radius;
3. `PDG.supWinProb_enhance_le_blindSupWinProb` — "the distinguisher `D`
   together with `T` can be seen as a non-adaptive distinguisher … `⟦DT⟧ ∈ NA`
   for any `D`": `T̂`'s winning mass is an average, over the query sequences
   `T` produces, of `Ŝ`'s winning masses at fixed query sequences, and an
   average is at most a supremum.

CR18's eq. (4.40) `T̂ = T̃bŜ` and its Definition 4.21 converter `T̃` do not
appear: they are the source's way of *reading* the enhanced game as a composite
of converters, and step 3 above states what that reading is for — the winner
is blind — directly about the game.  Nothing is lost, and no `Γ`/`Γᵇ` operator
and no blinded-system object stack enters (PHI-SPEC R11(a)).

## The hypothesis bundle, and what is *not* in it

Beyond the landed endpoint's `NonNeg`/equal-weight bundle, two clauses:

* `T.weight = 1` — Maurer13b's standing reading of "system" as a probability
  distribution.  It is genuinely used: `enhance` is a product law, whose weight
  is the *product* of the weights, and eq. (4.39) is an equality of unnormalized
  laws.  The landed adaptive endpoint does not need it because it never forms a
  product.
* `PDG.HasDomain G D` **and** `PDS.HasDomain T D` at **one** `D` — Definition
  2.14's domain attribute, shared.  This is the carrier's price for the
  source's phrase "the inputs to `T` are also given to `bŜ`": the MBO of `Ŝ`
  reads the history `Ŝ` answered, while the enhanced game's transcript exposes
  the history `T` answered, and on the `⊥`-total carrier (Ruling R2) those are
  the same list exactly when the two systems delete the same queries.  It is
  **not** totality — a common domain may refuse anything it likes, as long as
  both systems refuse it — and it is the same clause the landed `ω` endpoint
  carries for Theorem 2.37 (`conditional_equivalence_theorem_infWinnability`).

Not in the bundle: `[Fintype X]`, a query bound `QBounded`, or any totality
clause.  The adaptive endpoint's own route — the coupling core, which replaces
CR18's `T̂`/verdict chain on this carrier — is *also* available for the blind
right-hand side and needs no domain clause at all; it is recorded as
`PDG.advFullyDefined_forget_le_blindSupWinProb_of_condEquiv`, and the headline
above is the paper's route, kept because CR18 Lemma 5.3 consumes its
intermediate node (`Game/GameRelaxation.lean`).
-/

namespace RandomSystems

noncomputable section

open Classical

open Probability (Distribution statDist)

open scoped ENNReal

open scoped RandomSystems.PDG

universe u v

variable {X : Type u} {Y : Type v}

namespace System

/-! ## Four deterministic receipts

All four are about the landed `keptPrefix`/`playQueries` pair and mention no
game.  UPSTREAM-CANDIDATES for `System/DiscreteSystem.lean` and
`System/ClassDistance.lean`; they are stated here because the blind layer is
their only consumer so far. -/

/-- **CR18 Definition 3.3's deletion pass reads only the domain** (printed
p. 58).  Two systems
that decline the same histories keep the same prefixes — which is what makes
"common domain" (`PDS.HasDomain`) a statement one can carry
between two systems of different output alphabets. -/
theorem keptPrefix_congr_of_dom_eq {Y' : Type*} (S : DDS X Y) (T : DDS X Y')
    (h : dom S = dom T) (l : List X) : keptPrefix S l = keptPrefix T l := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton m x ih =>
      rw [keptPrefix_append_singleton, keptPrefix_append_singleton, ih]
      by_cases hc : keptPrefix T m ++ [x] ∈ dom S
      · rw [if_pos hc, if_pos (h ▸ hc)]
      · rw [if_neg hc, if_neg (fun hd => hc (h ▸ hd))]

/-- The deletion pass is idempotent: a kept prefix is kept. -/
theorem keptPrefix_keptPrefix (S : DDS X Y) (l : List X) :
    keptPrefix S (keptPrefix S l) = keptPrefix S l :=
  keptPrefix_eq_self_of_mem_or_empty S (keptPrefix_mem_or S l)

/-- **The fixed-query environment asks exactly its list**, at its own length —
the input side of `answeredQueries_transcript_playQueries`, which additionally
assumes the list is in the domain and concludes about the *answered* history.
Here nothing is assumed: refused queries still count as asked. -/
theorem transcriptInputs_transcript_playQueries (s : DDS X Y) (l : List X) :
    ∀ n, n ≤ l.length →
      (DDE.Total.transcript s (DDE.Total.playQueries l) n)↓ₓ = l.take n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have hik := ih (Nat.le_of_succ_le hn)
      have hlen : (DDE.Total.transcript s (DDE.Total.playQueries l) n).length = n := by
        have h2 : (DDE.Total.transcript s (DDE.Total.playQueries l) n).length
            = ((DDE.Total.transcript s (DDE.Total.playQueries l) n)↓ₓ).length := by
          simp [transcriptInputs]
        rw [h2, hik, List.length_take]
        omega
      have hlt : n < l.length := hn
      have hq : DDE.Total.playQueries l
          ((DDE.Total.transcript s (DDE.Total.playQueries l) n)↓ᵧ) = some l[n] := by
        show l[((DDE.Total.transcript s (DDE.Total.playQueries l) n)↓ᵧ).length]? = _
        rw [show ((DDE.Total.transcript s (DDE.Total.playQueries l) n)↓ᵧ).length = n by
            simpa [transcriptOutputs] using hlen,
          List.getElem?_eq_getElem hlt]
      rw [DDE.Total.transcript]
      simp only [hq, transcriptInputs, List.map_append, List.map_cons, List.map_nil]
      have hik' : List.map Prod.fst (DDE.Total.transcript s (DDE.Total.playQueries l) n)
          = List.take n l := hik
      rw [hik', List.take_add_one, List.getElem?_eq_getElem hlt]
      rfl

@[simp] theorem transcriptInputs_transcript_playQueries_length (s : DDS X Y)
    (l : List X) :
    (DDE.Total.transcript s (DDE.Total.playQueries l) l.length)↓ₓ = l := by
  rw [transcriptInputs_transcript_playQueries s l l.length le_rfl, List.take_length]

/-- **A probing run answers the kept prefix of its list.**  Combining the
previous receipt with `DDE.Total.answeredQueries_transcript`: what the system
processed during `playQueries l` is `keptPrefix s l`, whether or not `l` is in
its domain. -/
theorem answeredQueries_transcript_playQueries_keptPrefix (s : DDS X Y)
    (l : List X) :
    answeredQueries (DDE.Total.transcript s (DDE.Total.playQueries l) l.length)
      = keptPrefix s l := by
  rw [DDE.Total.answeredQueries_transcript, transcriptInputs_transcript_playQueries_length]

/-- **A blind environment asks the same queries of every system.**  Lanzenberger
fn. 6's non-adaptivity says the query at step `k` depends only on `k`, so the
input projection of the run does not mention the system at all.  This is the
formal content of CR18 Definition 4.20's "the inputs `x₁,…,x_q` can be
interpreted as being chosen in advance, before seeing any outputs" (printed
p. 109). -/
theorem transcriptInputs_congr_of_nonAdaptive {e : DDE.Total Y X}
    (he : DDE.Total.NonAdaptive e) (s s' : DDS X Y) (n : ℕ) :
    (DDE.Total.transcript s e n)↓ₓ = (DDE.Total.transcript s' e n)↓ₓ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlen : (DDE.Total.transcript s e n).length
          = (DDE.Total.transcript s' e n).length := by
        have h1 : (DDE.Total.transcript s e n).length
            = ((DDE.Total.transcript s e n)↓ₓ).length := by simp [transcriptInputs]
        have h2 : (DDE.Total.transcript s' e n).length
            = ((DDE.Total.transcript s' e n)↓ₓ).length := by simp [transcriptInputs]
        rw [h1, h2, ih]
      have hq : e (DDE.Total.transcript s e n)↓ᵧ = e (DDE.Total.transcript s' e n)↓ᵧ :=
        he _ _ (by simpa [transcriptOutputs] using hlen)
      rw [DDE.Total.transcript, DDE.Total.transcript]
      rcases hx : e (DDE.Total.transcript s e n)↓ᵧ with _ | x
      · rw [← hq]
        simp only [hx]
        exact ih
      · rw [← hq]
        simp only [hx, transcriptInputs, List.map_append, List.map_cons, List.map_nil]
        exact congrArg (fun t => t ++ [x]) ih

/-- The blind environments are a nonempty class — `playQueries []` is one.
Registered so that the restricted Definition 2.25 supremum below has the
`ciSup` API (`ciSup_le`) available without a hypothesis. -/
instance : Nonempty {e : DDE.Total Y X // DDE.Total.NonAdaptive e} :=
  ⟨⟨DDE.Total.playQueries [], DDE.Total.nonAdaptive_playQueries []⟩⟩

/-- The constant system deletes nothing: it is defined on every nonempty
history, so its kept prefix is the identity. -/
@[simp] theorem keptPrefix_functionEvaluator (f : X → Y) (l : List X) :
    keptPrefix (functionEvaluator f) l = l := by
  refine keptPrefix_eq_self_of_mem_or_empty _ ?_
  rcases eq_or_ne l ([] : List X) with rfl | hne
  · exact Or.inr rfl
  · exact Or.inl (by rw [dom_functionEvaluator]; exact hne)

end System

namespace PDG

/-! ## Definition 2.25's supremum, restricted to blind environments -/

/-- **Maurer13b's `Γ^{NA}`** (printed p. 3154) and **CR18's `Γ(bS)`** (printed
p. 109): Lanzenberger Definition 2.25's supremum winning probability with its
index set cut down to the environments that cannot react — Lanzenberger fn. 6's
`NonAdaptive`, the landed class `PDS.equivalent_iff_nonAdaptive` already
quantifies over.

**This is `ν`, not a second winning-probability notion.**  `PDG.winningMass` —
Definition 2.25's per-environment quantity — is the same function here as in
`supWinProb`; only the index type of the supremum changes.  `PDG.supWinProb`
remains the tree's single statement of Definition 2.25 (T3.9), and
`blindSupWinProb_le_supWinProb` places the two.

The identification with the *converter* rendering, `Γ(bS)` proper, is
`supWinProb_blockRepliesGame`. -/
def blindSupWinProb (G : PDG X Y) : ℝ :=
  ⨆ p : {e : System.DDE.Total Y X // System.DDE.Total.NonAdaptive e} × ℕ,
    winningMass p.1.1 p.2 G

/-- Maurer13b's `Γ^{NA}` notation (printed p. 3154), written as the restricted
Definition 2.25 supremum it is. -/
scoped notation "νᴺᴬ(" G ")" => blindSupWinProb G

/-- `νᴺᴬ` read at the metric's carrier, exactly as `ν[·]`/`ω[·]` are: this is
display, not a carrier, and it exists so that no endpoint statement has to
repeat `ENNReal.ofReal`. -/
scoped notation "νᴺᴬ[" G "]" => ENNReal.ofReal (RandomSystems.PDG.blindSupWinProb G)

theorem bddAbove_range_winningMass_nonAdaptive {G : PDG X Y} (hG : G.NonNeg) :
    BddAbove (Set.range fun p : {e : System.DDE.Total Y X //
        System.DDE.Total.NonAdaptive e} × ℕ => winningMass p.1.1 p.2 G) := by
  refine ⟨G.weight, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact winningMass_le_weight hG p.1.1 p.2

/-- The defining property, upper half. -/
theorem winningMass_le_blindSupWinProb {G : PDG X Y} (hG : G.NonNeg)
    {e : System.DDE.Total Y X} (he : System.DDE.Total.NonAdaptive e) (n : ℕ) :
    winningMass e n G ≤ blindSupWinProb G :=
  le_ciSup (bddAbove_range_winningMass_nonAdaptive hG) (⟨e, he⟩, n)

/-- The defining property at the witness class: a fixed query list is a blind
strategy (`System.DDE.Total.nonAdaptive_playQueries`). -/
theorem winningMass_playQueries_le_blindSupWinProb {G : PDG X Y} (hG : G.NonNeg)
    (l : List X) (n : ℕ) :
    winningMass (System.DDE.Total.playQueries l) n G ≤ blindSupWinProb G :=
  winningMass_le_blindSupWinProb hG (System.DDE.Total.nonAdaptive_playQueries l) n

/-- The defining property, lower half. -/
theorem blindSupWinProb_le_of_forall {G : PDG X Y} {c : ℝ}
    (h : ∀ (e : System.DDE.Total Y X), System.DDE.Total.NonAdaptive e →
      ∀ n : ℕ, winningMass e n G ≤ c) :
    blindSupWinProb G ≤ c :=
  ciSup_le fun p => h p.1.1 p.1.2 p.2

theorem blindSupWinProb_nonneg {G : PDG X Y} (hG : G.NonNeg) :
    0 ≤ blindSupWinProb G :=
  le_trans (winningMass_nonneg hG (System.DDE.Total.playQueries []) 0)
    (winningMass_playQueries_le_blindSupWinProb hG [] 0)

/-- **CR18 printed p. 109**: "The best probability in winning a game `S`
non-adaptively (i.e. `Γ(bS)`) is generally lower than the best probability in
winning it adaptively (i.e. `Γ(S)`)."  The comparison holds always; that it is
*strict* in general is the source's word "generally", and no separating witness
is claimed here. -/
theorem blindSupWinProb_le_supWinProb {G : PDG X Y} (hG : G.NonNeg) :
    blindSupWinProb G ≤ supWinProb G :=
  blindSupWinProb_le_of_forall fun e _ n => winningMass_le_supWinProb hG e n

theorem blindSupWinProb_le_weight {G : PDG X Y} (hG : G.NonNeg) :
    blindSupWinProb G ≤ G.weight :=
  blindSupWinProb_le_of_forall fun e _ n => winningMass_le_weight hG e n

/-- Winning at a fixed query list, spelled as a counting statement about the
game's realizations: the list is asked in full, and the condition is tested
against what the realization answered. -/
theorem winningMass_playQueries_eq_mass {G : PDG X Y} (l : List X) :
    winningMass (System.DDE.Total.playQueries l) l.length G
      = G.mass fun g => System.keptPrefix g.1 l ∈ g.2.1 := by
  refine Distribution.mass_congr G fun g => ?_
  rw [System.Won, System.answeredQueries_transcript_playQueries_keptPrefix]

/-- The not-won half of `winningMass_playQueries_eq_mass`. -/
theorem notWonMass_playQueries_eq_mass {G : PDG X Y} (l : List X) :
    notWonMass (System.DDE.Total.playQueries l) l.length G
      = G.mass fun g => System.keptPrefix g.1 l ∉ g.2.1 := by
  rw [notWonMass_eq_mass_not_won]
  refine Distribution.mass_congr G fun g => ?_
  rw [System.Won, System.answeredQueries_transcript_playQueries_keptPrefix]

/-! ## CR18 eq. (4.39): `T` enhanced with the game's own MBO -/

/-- **Maurer13b Theorem 3's construction** (printed p. 3154) / **CR18
eq. (4.39)** (printed p. 110): "One can enhance `T` with an MBO `A₀,A₁,A₂…` to
a game `T̂`, as follows: `p^T̂_{Yⁱ,Aᵢ|Xⁱ} = p^T_{Yⁱ|Xⁱ} · p^Ŝ_{Aᵢ|Xⁱ}`" — the
outputs come from `T`, the MBO from `Ŝ`, **independently given the inputs**.
CR18 Lemma 5.3 (printed p. 121) names the same object in words: "the inputs to
`T` are also given to `bŜ` and the MBO (of `T̂`) is the MBO of `Ŝ`, i.e. the
MBO is defined independently of `T`."

On this carrier "independent given the inputs" is the independent product of
the two laws (`Probability.Distribution.prod`), and "the MBO of `Ŝ`, read on
the history `Ŝ` processed" is the landed substitution
`System.MonotoneCondition.comap` along `Ŝ`'s own deletion pass — Definition
2.21 evaluates every condition along exactly that map (`System/Game.lean`,
`prefixMonotoneMap_keptPrefix`).  So `enhance` is a definition **over** landed
objects: a product of landed laws pushed through a map assembled from landed
constructors, no second object stack (PHI-SPEC R11(a)).

The two systems must share a domain for this to be the source's object; see
`equivalentAsGames_enhance`. -/
def enhance (G : PDG X Y) (T : PDS X Y) : PDG X Y :=
  Distribution.fTransform
    (fun p : System.DDS X Y × System.DDG X Y =>
      (p.1, System.MonotoneCondition.comap (System.keptPrefix p.2.1)
        (System.MonotoneCondition.prefixMonotoneMap_keptPrefix p.2.1) p.2.2))
    (Distribution.prod T G)

/-- **`T̂⁻ = T`** (Maurer13b Theorem 3's proof, printed p. 3154): forgetting the
adjoined MBO returns `T`, up to the weight of the discarded factor.  At the
intended normalization `‖Ŝ‖ = 1` the scalar is `1`. -/
theorem forget_enhance (G : PDG X Y) (T : PDS X Y) :
    forget (enhance G T) = G.weight • T := by
  rw [forget, enhance, Distribution.fTransform_fTransform]
  exact Distribution.fTransform_fst_prod T G

@[simp] theorem weight_enhance (G : PDG X Y) (T : PDS X Y) :
    (enhance G T).weight = T.weight * G.weight := by
  rw [enhance, Distribution.weight_fTransform, Distribution.weight_prod]

theorem nonNeg_enhance {G : PDG X Y} {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg) :
    (enhance G T).NonNeg :=
  (hT.prod hG).fTransform _

/-- **The enhanced game's winning event, on its own support.**  The condition
of `T̂` is `Ŝ`'s condition read along `Ŝ`'s deletion pass; when the two systems
share a domain (`PDS.HasDomain`) that pass is `T`'s own, and `T`'s
answered history is already deleted, so the test lands on the history `T`
answered — which is what an environment interacting with `T̂` sees.

This is the exact point at which the carrier charges for the source's "the
inputs to `T` are also given to `bŜ`": in CR18 the two systems receive the same
inputs and there are no refusals, here they receive the same inputs and delete
the same ones. -/
theorem won_enhance_atom_iff {G : PDG X Y} {T : PDS X Y} {D : Set (List X)}
    (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    {p : System.DDS X Y × System.DDG X Y}
    (hp : p ∈ (Distribution.prod T G).support)
    (e : System.DDE.Total Y X) (n : ℕ) :
    System.Won (p.1, System.MonotoneCondition.comap (System.keptPrefix p.2.1)
        (System.MonotoneCondition.prefixMonotoneMap_keptPrefix p.2.1) p.2.2) e n
      ↔ System.answeredQueries (System.DDE.Total.transcript p.1 e n) ∈ p.2.2.1 := by
  have hmem := Finset.mem_product.mp (Distribution.support_prod_subset T G hp)
  have hd : System.dom p.2.1 = System.dom p.1 := by
    rw [hdomG p.2 hmem.2, hdomT p.1 hmem.1]
  show System.keptPrefix p.2.1
      (System.answeredQueries (System.DDE.Total.transcript p.1 e n)) ∈ p.2.2.1 ↔ _
  rw [System.keptPrefix_congr_of_dom_eq _ _ hd,
    System.DDE.Total.answeredQueries_transcript, System.keptPrefix_keptPrefix,
    ← System.DDE.Total.answeredQueries_transcript]

/-- The enhanced game's Definition 2.25 winning mass (printed p. 17): the condition is `Ŝ`'s,
tested against what `T` answered. -/
theorem winningMass_enhance {G : PDG X Y} {T : PDS X Y} {D : Set (List X)}
    (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    (e : System.DDE.Total Y X) (n : ℕ) :
    winningMass e n (enhance G T)
      = (Distribution.prod T G).mass fun p =>
          System.answeredQueries (System.DDE.Total.transcript p.1 e n) ∈ p.2.2.1 := by
  rw [winningMass, enhance, Distribution.mass_fTransform]
  exact Distribution.mass_congr_of_support _ fun p hp =>
    won_enhance_atom_iff hdomG hdomT hp e n

/-- **The enhanced game's not-won law factorizes** — Maurer13b's display
`p^T̂_{Yⁱ,Aᵢ=0|Xⁱ} = p^T̂_{Aᵢ=0|Xⁱ} · p^T̂_{Yⁱ|Xⁱ}` (printed p. 3154, the
underbraces): the transcript comes from `T` and the condition from `Ŝ`, and
once the transcript value is fixed the two factors are independent. -/
theorem notWonLaw_enhance {G : PDG X Y} {T : PDS X Y} {D : Set (List X)}
    (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    (e : System.DDE.Total Y X) (n : ℕ) (τ : List (X × Option Y)) :
    notWonLaw e n (enhance G T) τ
      = PDS.trLawFullyDefined e n T τ
          * G.mass fun g => System.answeredQueries τ ∉ g.2.1 := by
  rw [notWonLaw_apply, enhance, Distribution.mass_fTransform]
  rw [Distribution.mass_congr_of_support (Distribution.prod T G)
    (Q := fun p : System.DDS X Y × System.DDG X Y =>
      (System.DDE.Total.transcript p.1 e n = τ) ∧
        (System.answeredQueries τ ∉ p.2.2.1)) ?_]
  · rw [PDS.trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
    exact Distribution.mass_prod_and T G
      (fun s : System.DDS X Y => System.DDE.Total.transcript s e n = τ)
      (fun g : System.DDG X Y => System.answeredQueries τ ∉ g.2.1)
  · intro p hp
    have hw := won_enhance_atom_iff hdomG hdomT hp e n
    constructor
    · rintro ⟨hnw, ht⟩
      refine ⟨ht, ?_⟩
      rw [← ht]
      exact fun hc => hnw (hw.mpr hc)
    · rintro ⟨ht, hnw⟩
      refine ⟨?_, ht⟩
      rw [ht] at hw
      exact fun hc => hnw (hw.mp hc)

/-- **Maurer13b Theorem 3's first display (printed p. 3154) / CR18 eq. (4.39)
(printed p. 110)**: `Ŝ ≡ᵍ T̂`.

Printed p. 3154: "Then `Ŝ ≡ᵍ T̂` since
`p^Ŝ_{Yⁱ,Aᵢ=0|Xⁱ} = p^Ŝ_{Aᵢ=0|Xⁱ} · p^Ŝ_{Yⁱ|Xⁱ,Aᵢ=0} = p^T̂_{Yⁱ,Aᵢ=0|Xⁱ}`",
the middle equality being conditional equivalence itself.  This is that
computation: the enhanced game's not-won law factorizes
(`notWonLaw_enhance`), conditional equivalence says the game's own not-won law
factorizes the same way (`condEquiv_apply`), and the two scalar factors agree
because both count the `Ŝ`-realizations whose condition has not fired on the
answered history.

`T.weight = 1` is used, and is Maurer13b's standing reading of "system": the
enhanced game is a *product* law, so an unnormalized `T` would rescale one side
and not the other.  The common domain is `won_enhance_atom_iff`'s. -/
theorem equivalentAsGames_enhance {G : PDG X Y} {T : PDS X Y} {D : Set (List X)}
    (hT1 : T.weight = 1) (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    (hCE : CondEquiv G T) :
    EquivalentAsGames G (enhance G T) := by
  intro l _
  ext τ
  have hkey := condEquiv_apply hCE l τ
  rw [hT1, one_mul] at hkey
  rw [notWonLaw_enhance hdomG hdomT, hkey]
  by_cases hz : PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T τ = 0
  · rw [hz, mul_zero, zero_mul]
  · obtain ⟨t, ht, hteq⟩ :=
      Distribution.mem_support_fTransform (fun s => System.DDE.Total.transcript s
        (System.DDE.Total.playQueries l) l.length) T
        (b := τ) (Finsupp.mem_support_iff.mpr hz)
    have haq : System.answeredQueries τ = System.keptPrefix t l := by
      rw [← hteq, System.answeredQueries_transcript_playQueries_keptPrefix]
    rw [haq, notWonMass_playQueries_eq_mass, mul_comm]
    refine congrArg
      (fun r : ℝ => PDS.trLawFullyDefined (System.DDE.Total.playQueries l) l.length T τ * r) ?_
    exact Distribution.mass_congr_of_support G fun g hg => by
      rw [System.keptPrefix_congr_of_dom_eq g.1 t (by rw [hdomG g hg, hdomT t ht])]

/-! ## `⟦DT⟧ ∈ NA`: the enhanced game is won blindly -/

/-- A scalar factors out of an event mass written as a `Finsupp` sum. -/
theorem sum_ite_const_mul {A : Type*} (Z : Distribution A) (P : A → Prop) (c : ℝ) :
    (Z.sum fun a w => if P a then c * w else 0) = c * Z.mass P := by
  rw [Distribution.mass, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  by_cases h : P a <;> simp [h]

/-- **Maurer13b Theorem 3's last step** (printed p. 3154): "The way `T̂` is
defined (namely, as `T` enhanced with an independent system `Ŝ` generating an
MBO from the inputs `X₁,X₂,…`), the distinguisher `D` together with `T` can be
seen as a non-adaptive distinguisher or game winner `⟦DT⟧` … The claim
`Δ_q(S,T) ≤ Γ^{NA}_q(Ŝ)` follows since `⟦DT⟧ ∈ NA` for any `D`."

On this carrier `⟦DT⟧` is not built as an object: the sentence says that the
query sequence driving `Ŝ`'s MBO is generated by `T` alone, and that is
visible in the product law.  The enhanced game's winning mass at *any*
environment is the `T`-average of `Ŝ`'s winning masses at the fixed query
sequences `T` produced, and an average of numbers below a supremum is below
that supremum.  Adaptivity is spent exactly where the source spends it — the
environment may be as adaptive as it likes against `T`, but what it hands `Ŝ`
is a list. -/
theorem supWinProb_enhance_le_blindSupWinProb {G : PDG X Y} {T : PDS X Y}
    {D : Set (List X)} (hG : G.NonNeg) (hT : T.NonNeg) (hT1 : T.weight = 1)
    (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D) :
    supWinProb (enhance G T) ≤ blindSupWinProb G := by
  refine supWinProb_le_of_forall fun e n => ?_
  rw [winningMass_enhance hdomG hdomT, Distribution.mass_prod_eq_double_sum]
  have hinner : ∀ t ∈ T.support,
      (G.sum fun g wg =>
          if System.answeredQueries (System.DDE.Total.transcript t e n) ∈ g.2.1
          then T t * wg else 0)
        ≤ T t * blindSupWinProb G := by
    intro t ht
    rw [sum_ite_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hT t)
    have ha : (G.mass fun g =>
          System.answeredQueries (System.DDE.Total.transcript t e n) ∈ g.2.1)
        = winningMass
            (System.DDE.Total.playQueries
              (System.answeredQueries (System.DDE.Total.transcript t e n)))
            (System.answeredQueries (System.DDE.Total.transcript t e n)).length G := by
      rw [winningMass_playQueries_eq_mass]
      refine (Distribution.mass_congr_of_support G fun g hg => ?_).symm
      rw [System.keptPrefix_congr_of_dom_eq g.1 t (by rw [hdomG g hg, hdomT t ht]),
        System.DDE.Total.answeredQueries_transcript, System.keptPrefix_keptPrefix]
    rw [ha]
    exact winningMass_playQueries_le_blindSupWinProb hG _ _
  calc (T.sum fun t wt => G.sum fun g wg =>
          if System.answeredQueries (System.DDE.Total.transcript t e n) ∈ g.2.1
          then wt * wg else 0)
      ≤ ∑ t ∈ T.support, T t * blindSupWinProb G := Finset.sum_le_sum hinner
    _ = T.weight * blindSupWinProb G := by
        rw [← Finset.sum_mul]
        rfl
    _ = blindSupWinProb G := by rw [hT1, one_mul]

/-! ## The endpoint -/

/-- **Maurer13b Theorem 3** (printed p. 3154), the "in particular" clause: "If
for an `(𝒳,𝒴)`-system `S` one can define an MBO `A₀,A₁,A₂…`, such that
`Ŝ|𝒜 ≡ T`, then, for every `D`, `Δ^D_q(S,T) ≤ Γ^{⟦DT⟧}_q(Ŝ)`.  In particular,
`Δ_q(S,T) ≤ Γ^{NA}_q(Ŝ)`."  Equivalently **CR18 Theorem 4.17** (printed
p. 110): "If for an `(𝒳,𝒴)`-system `S` one can define an MBO such that
`Ŝ ⊨ T`, then `⟨S|T⟩ ≤ bŜ ∘ ρ^T̃`.  In particular, `Δ(S,T) ≤ Γ(bŜ)`."

Reading the statement: `S = Ŝ⁻` is `PDG.forget G`, `Δ` is Ruling R4's `Adv⊥`,
and `Γ^{NA}` / `Γ(bŜ)` is `blindSupWinProb`, whose identification with the
converter rendering `Γ(bŜ)` proper is `supWinProb_blockRepliesGame`.

**This is strictly stronger than `conditional_equivalence_theorem`**, whose
right-hand side is the adaptive `ν` (CR18 printed p. 109: the non-adaptive
optimum "is generally lower than" the adaptive one), and than
`conditional_equivalence_theorem_infWinnability`, which by Theorem 2.37 is the
same number as `ν`.

Hypotheses: the landed endpoint's bundle (`NonNeg` twice, equal weight), plus
the two clauses the printed route costs on this carrier — `T` normalized, and
one shared Definition 2.14 domain.  See the module docstring for why each is
there and why neither is totality. -/
theorem conditional_equivalence_theorem_blind {G : PDG X Y} {T : PDS X Y}
    {D : Set (List X)} (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hT1 : T.weight = 1) (hdomG : HasDomain G D) (hdomT : PDS.HasDomain T D)
    (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ νᴺᴬ[G] := by
  have hG1 : G.weight = 1 := hw.trans hT1
  have hfe : forget (enhance G T) = T := by rw [forget_enhance, hG1, one_smul]
  have hwE : (enhance G T).weight = G.weight := by rw [weight_enhance, hT1, one_mul]
  calc PDS.advFullyDefined (forget G) T
      = PDS.advFullyDefined (forget (enhance G T)) (forget G) := by
        rw [hfe, PDS.advFullyDefined_comm_of_weight_eq _ _
          (by rw [weight_forget, hG1, hT1])]
    _ ≤ ν[enhance G T] :=
        fundamental_lemma_of_game_playing (nonNeg_enhance hG hT) hG hwE
          (equivalentAsGames_enhance hT1 hdomG hdomT hCE).symm
    _ ≤ νᴺᴬ[G] :=
        ENNReal.ofReal_le_ofReal
          (supWinProb_enhance_le_blindSupWinProb hG hT hT1 hdomG hdomT)

/-! ## The same endpoint on the coupling core, with no domain clause

The route above is the printed one.  This section records that the *landed*
route — the coupling core of `Technique/ConditionalEquivalence.lean`, which is
what CR18's `T̂`/verdict chain collapses to on this carrier — reaches the same
blind right-hand side with a strictly smaller hypothesis bundle: no shared
domain and no normalization.  Both are kept: the printed route because CR18
Lemma 5.3 consumes its intermediate node `enhance`, this one because it is the
sharper statement. -/

/-- **The coupling core, sharpened to the blind bound**, at one environment and
one interaction length.

The landed `statDist_trLawFullyDefined_forget_le_winningMass` bounds each
transcript value's excess by the *won* mass at that value and then sums to
`winningMass e n G` — the adaptive number.  The sharpening keeps the same
coupling and reads the excess the other way round: at equal weight the metric
may be taken in either order (`Probability.statDist_symm_of_eq_weight`), and
then conditional equivalence gives the excess *proportionally* —
`T`'s mass at `t` times the fraction of `G` that has already won on `t`'s query
list.  Summing a proportion against `T`'s own law is an average, so the bound
is a supremum over **fixed query lists**, not over environments.  This is the
same mechanism as Maurer13b Theorem 3's `⟦DT⟧ ∈ NA` (printed p. 3154) — the
query sequences are distributed by `T` — carried out on the metric directly. -/
theorem statDist_trLawFullyDefined_forget_le_blindSupWinProb {G : PDG X Y}
    {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hCE : CondEquiv G T) (e : System.DDE.Total Y X) (n : ℕ) :
    statDist (PDS.trLawFullyDefined e n (forget G)) (PDS.trLawFullyDefined e n T)
      ≤ blindSupWinProb G := by
  classical
  set μ := PDS.trLawFullyDefined e n (forget G) with hμdef
  set ν := PDS.trLawFullyDefined e n T with hνdef
  have hμnn : μ.NonNeg := by
    rw [hμdef, PDS.trLawFullyDefined]; exact (nonNeg_forget hG).fTransform _
  have hνnn : ν.NonNeg := by rw [hνdef, PDS.trLawFullyDefined]; exact hT.fTransform _
  have hνw : ν.weight = T.weight := by rw [hνdef, PDS.weight_trLawFullyDefined]
  have hμeq : μ = Distribution.fTransform
      (fun g => System.DDE.Total.transcript g.1 e n) G := by
    rw [hμdef, PDS.trLawFullyDefined, forget, Distribution.fTransform_fTransform]
    rfl
  have hTw : 0 ≤ T.weight := by
    rw [← Distribution.mass_true T]; exact hT.mass_nonneg _
  have hbnn : 0 ≤ blindSupWinProb G := blindSupWinProb_nonneg hG
  -- the per-value bound, uniform in `t`
  have key : ∀ t : List (X × Option Y),
      T.weight * max (ν t - μ t) 0 ≤ blindSupWinProb G * ν t := by
    intro t
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
      have hν : ν t = PDS.trLawFullyDefined
          (System.DDE.Total.playQueries (System.transcriptInputs t)) t.length T t := by
        rw [hνdef, PDS.trLawFullyDefined, PDS.trLawFullyDefined,
          Distribution.fTransform_apply_eq_mass, Distribution.fTransform_apply_eq_mass]
        exact Distribution.mass_congr T fun u => hfib u
      have hnwle : notWonLaw
          (System.DDE.Total.playQueries (System.transcriptInputs t)) t.length G t ≤ μ t := by
        rw [notWonLaw_apply, hμeq, Distribution.fTransform_apply_eq_mass]
        refine Distribution.mass_mono hG fun g hg => ?_
        exact (hfib g.1).mpr hg.2
      have hprod := condEquiv_apply hCE (System.transcriptInputs t) t
      simp only [System.length_transcriptInputs] at hprod hν
      have hsplit := winningMass_add_notWonMass
        (System.DDE.Total.playQueries (System.transcriptInputs t)) t.length G
      have hWle : winningMass
          (System.DDE.Total.playQueries (System.transcriptInputs t)) t.length G
            ≤ blindSupWinProb G :=
        winningMass_playQueries_le_blindSupWinProb hG _ _
      have hνt : 0 ≤ ν t := hνnn t
      have hstep : T.weight * (ν t - μ t)
          ≤ blindSupWinProb G * ν t := by
        have h1 : T.weight * (ν t - μ t) ≤ T.weight * (ν t
            - notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
                t.length G t) :=
          mul_le_mul_of_nonneg_left (by linarith) hTw
        have h2 : T.weight * (ν t
            - notWonLaw (System.DDE.Total.playQueries (System.transcriptInputs t))
                t.length G t)
            = winningMass (System.DDE.Total.playQueries (System.transcriptInputs t))
                t.length G * ν t := by
          rw [mul_sub, hprod, hν, ← hw]
          nlinarith [hsplit]
        have h3 : winningMass (System.DDE.Total.playQueries (System.transcriptInputs t))
            t.length G * ν t ≤ blindSupWinProb G * ν t :=
          mul_le_mul_of_nonneg_right hWle hνt
        linarith [h1, h2 ▸ h1]
      rcases le_or_gt (ν t - μ t) 0 with hle | hlt
      · rw [max_eq_right hle, mul_zero]
        exact mul_nonneg hbnn hνt
      · rw [max_eq_left hlt.le]
        exact hstep
    · have hzμ : μ t = 0 := by
        rw [hμeq, Distribution.fTransform_apply_eq_mass]
        refine Distribution.mass_eq_zero_of_forall_not G fun g hcontra => ?_
        subst hcontra
        exact hE ⟨(System.DDE.Total.transcript_consistent g.1 e n).1.1,
          (System.DDE.Total.transcript_consistent g.1 e n).1.2⟩
      have hzν : ν t = 0 := by
        rw [hνdef, PDS.trLawFullyDefined, Distribution.fTransform_apply_eq_mass]
        refine Distribution.mass_eq_zero_of_forall_not T fun u hcontra => ?_
        subst hcontra
        exact hE ⟨(System.DDE.Total.transcript_consistent u e n).1.1,
          (System.DDE.Total.transcript_consistent u e n).1.2⟩
      rw [hzμ, hzν, sub_zero, max_eq_right le_rfl, mul_zero, mul_zero]
  -- sum the per-value bound over a finite cover
  set s : Finset (List (X × Option Y)) := ν.support ∪ (ν - μ).support with hsdef
  have hsub : (ν - μ).support ⊆ s := Finset.subset_union_right
  have hνsum : ∑ t ∈ s, ν t = ν.weight := by
    rw [Distribution.weight, Finsupp.sum]
    exact (Finset.sum_subset Finset.subset_union_left
      fun t _ ht => Finsupp.notMem_support_iff.mp ht).symm
  have hsymm : statDist μ ν = statDist ν μ :=
    Probability.statDist_symm_of_eq_weight _ _
      (by rw [hμdef, hνdef, PDS.weight_trLawFullyDefined, PDS.weight_trLawFullyDefined,
        weight_forget, hw])
  have hbig : T.weight * statDist ν μ ≤ blindSupWinProb G * T.weight := by
    rw [Probability.statDist_eq_sum_of_support_subset ν μ hsub, Finset.mul_sum]
    calc ∑ t ∈ s, T.weight * max (ν t - μ t) 0
        ≤ ∑ t ∈ s, blindSupWinProb G * ν t := Finset.sum_le_sum fun t _ => key t
      _ = blindSupWinProb G * T.weight := by
          rw [← Finset.mul_sum, hνsum, hνw]
  rcases eq_or_lt_of_le hTw with hzero | hpos
  · -- a weightless `T` forces both laws to vanish
    have hzν : ∀ t, ν t = 0 := by
      intro t
      refine le_antisymm ?_ (hνnn t)
      rw [← Distribution.mass_singleton ν t]
      exact (Distribution.mass_le_weight hνnn _).trans (by rw [hνw, ← hzero])
    have : statDist ν μ = 0 := by
      rw [Probability.statDist_eq_sum_of_support_subset ν μ hsub]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [hzν t, zero_sub, max_eq_right (by linarith [hμnn t])]
    rw [hsymm, this]
    exact hbnn
  · rw [hsymm, mul_comm (blindSupWinProb G) T.weight] at *
    exact le_of_mul_le_mul_left hbig hpos

/-- **Maurer13b Theorem 3's "in particular" clause, on the landed coupling
core** (printed p. 3154): the same blind bound as
`conditional_equivalence_theorem_blind`, with **neither** the shared-domain
clause **nor** the normalization of `T` — the hypothesis bundle is exactly the
landed adaptive endpoint's.

Both statements are kept deliberately.  This one is the sharper theorem; the
paper-route one is the one whose intermediate node (`enhance`, CR18 eq. (4.39),
printed p. 110) CR18 Lemma 5.3 consumes, and whose proof reads as the printed
proof.  Where a caller only wants the bound, this is the one to use. -/
theorem advFullyDefined_forget_le_blindSupWinProb_of_condEquiv {G : PDG X Y}
    {T : PDS X Y} (hG : G.NonNeg) (hT : T.NonNeg) (hw : G.weight = T.weight)
    (hCE : CondEquiv G T) :
    PDS.advFullyDefined (forget G) T ≤ νᴺᴬ[G] :=
  iSup_le fun e => iSup_le fun n => ENNReal.ofReal_le_ofReal
    (statDist_trLawFullyDefined_forget_le_blindSupWinProb hG hT hw hCE e n)

/-! ## The two renderings of "blind" agree

CR18 Definition 4.20, printed p. 109: "To win game `bS` means to win game `S`
blindly, without seeing the outputs.  **Equivalently**, this means to win the
game *non-adaptively*."  That sentence is a theorem here, and both halves of it
are true. -/

/-- **CR18 Definition 4.20's `bŜ`** (printed p. 109), assembled from landed
parts at the `Φ` carrier: the game whose *system* is the resource with its
replies erased (`System.attachEngineFully` of `System.blockReplies`, the
ratified attachment primitive) and whose *condition* is the original game's,
read along the original system's deletion pass — because `b` is "transparent
for the queries", the inner system receives exactly the outer queries, and its
own answered history is what its MBO tests.

This is a definition **over** landed objects, in the same shape as `enhance`;
no blinded-system object stack enters (PHI-SPEC R11(a)). -/
def blockRepliesGame (c : Uni.{u}) (G : PDG Uni.{u} Uni.{u}) : PDG Uni.{u} Uni.{u} :=
  Distribution.fTransform
    (fun g : System.DDG Uni.{u} Uni.{u} =>
      (System.attachEngineFully Set.univ (System.blockReplies Set.univ c) g.1,
        System.MonotoneCondition.comap (System.keptPrefix g.1)
          (System.MonotoneCondition.prefixMonotoneMap_keptPrefix g.1) g.2)) G

/-- **The inputs chosen in advance** (CR18 printed p. 109: "the inputs
`x₁,…,x_q` can be interpreted as being chosen in advance, before seeing any
outputs"): the query list an environment produces when every answer it gets is
the same constant.  Reading it off a run of the constant system rather than
defining a second interaction semantics keeps the object inside the landed
transcript calculus. -/
def blindQueries {X : Type u} {Y : Type v} (c : Y) (e : System.DDE.Total Y X)
    (n : ℕ) : List X :=
  System.transcriptInputs
    (System.DDE.Total.transcript (System.functionEvaluator fun _ : X => c) e n)

/-- Winning the reply-erased game is winning the original game on the query
list chosen in advance — and that list does not mention the resource
(`System.attachEngineFully_blockReplies_univ`). -/
theorem won_blockRepliesGame_atom_iff (c : Uni.{u}) (g : System.DDG Uni.{u} Uni.{u})
    (e : System.DDE.Total Uni.{u} Uni.{u}) (n : ℕ) :
    System.Won
        (System.attachEngineFully Set.univ (System.blockReplies Set.univ c) g.1,
          System.MonotoneCondition.comap (System.keptPrefix g.1)
            (System.MonotoneCondition.prefixMonotoneMap_keptPrefix g.1) g.2) e n
      ↔ System.keptPrefix g.1 (blindQueries c e n) ∈ g.2.1 := by
  show System.keptPrefix g.1 (System.answeredQueries (System.DDE.Total.transcript
      (System.attachEngineFully Set.univ (System.blockReplies Set.univ c) g.1) e n))
        ∈ g.2.1 ↔ _
  rw [System.attachEngineFully_blockReplies_univ,
    System.DDE.Total.answeredQueries_transcript, System.keptPrefix_functionEvaluator]
  rfl

/-- The reply-erased game's winning mass at *any* environment is the original
game's winning mass at a **fixed query list**. -/
theorem winningMass_blockRepliesGame (c : Uni.{u}) (G : PDG Uni.{u} Uni.{u})
    (e : System.DDE.Total Uni.{u} Uni.{u}) (n : ℕ) :
    winningMass e n (blockRepliesGame c G)
      = winningMass (System.DDE.Total.playQueries (blindQueries c e n))
          (blindQueries c e n).length G := by
  rw [winningMass, blockRepliesGame, Distribution.mass_fTransform,
    winningMass_playQueries_eq_mass]
  exact Distribution.mass_congr G fun g => won_blockRepliesGame_atom_iff c g e n

/-- A blind environment wins the reply-erased game exactly as often as it wins
the game itself: it was already not using the answers
(`System.transcriptInputs_congr_of_nonAdaptive`). -/
theorem winningMass_blockRepliesGame_of_nonAdaptive (c : Uni.{u})
    (G : PDG Uni.{u} Uni.{u}) {e : System.DDE.Total Uni.{u} Uni.{u}}
    (he : System.DDE.Total.NonAdaptive e) (n : ℕ) :
    winningMass e n (blockRepliesGame c G) = winningMass e n G := by
  rw [winningMass_blockRepliesGame, winningMass_playQueries_eq_mass, winningMass]
  refine (Distribution.mass_congr G fun g => ?_).symm
  show System.answeredQueries (System.DDE.Total.transcript g.1 e n) ∈ g.2.1 ↔ _
  rw [System.DDE.Total.answeredQueries_transcript,
    System.transcriptInputs_congr_of_nonAdaptive he g.1
      (System.functionEvaluator (fun _ : Uni.{u} => c)) n]
  rfl

/-- **The two renderings of "blind" are one number** — CR18 Definition 4.20's
"equivalently" (printed p. 109), in both directions.

`≤`: an environment facing `bŜ` gets the same constant back whatever it asks,
so the queries it asks are a fixed list, and its winning mass is the winning
mass of that list — a blind strategy.  `≥`: a blind environment never used the
answers, so erasing them changes nothing.

The theorem is uniform in the constant `c` the eraser answers, which is the
formal reason CR18 leaves it unnamed: a blocked reply carries no information. -/
theorem supWinProb_blockRepliesGame (c : Uni.{u}) {G : PDG Uni.{u} Uni.{u}}
    (hG : G.NonNeg) :
    supWinProb (blockRepliesGame c G) = blindSupWinProb G := by
  have hnn : (blockRepliesGame c G).NonNeg := hG.fTransform _
  refine le_antisymm (supWinProb_le_of_forall fun e n => ?_)
    (blindSupWinProb_le_of_forall fun e he n => ?_)
  · rw [winningMass_blockRepliesGame]
    exact winningMass_playQueries_le_blindSupWinProb hG _ _
  · rw [← winningMass_blockRepliesGame_of_nonAdaptive c G he n]
    exact winningMass_le_supWinProb hnn e n

end PDG

end

end RandomSystems

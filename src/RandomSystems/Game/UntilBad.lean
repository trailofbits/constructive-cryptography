import RandomSystems.Distance.UntilBad
import RandomSystems.Game.DiscreteMBO
import Probability.Coupling

/-!
# Games identical until bad

The part of a game with every MBO unset lies below its visible system, and a step from a
transcript `h` by a query `x` loses from it the probability that the game sets the MBO at `x`.
Suppose that, from every transcript with every MBO unset, the game sets the MBO at the next query
`x` with probability at most `β h x` times the probability of the transcript, and that every
possible transcript costs at most `ε`. The union bound over the steps
(`RandomSystem.one_sub_le_sum_tSupp`) then bounds the mass missing from the unset part along the
transcripts of a winner, which is the winning probability: every winner wins with probability at
most `ε`. Two games equivalent as games have the same unset part, so it is a common part of
their visible systems, and the per-step costs bound its missing mass: the visible systems are
within `ε` (`RandomSystem.transcriptDistance_le_of_transcriptCost_le`).

Two discrete games are equivalent as games when they are coupled: a joint law of the two whose
pairs have one condition and systems that answer alike while the condition does not hold.

Sources: CR18, Definition 4.16 (equivalence as games); Maurer 2002, Definition 5;
Lanzenberger–Maurer, Theorem 2 (a joint distribution, or coupling, of two PDSs).

## Main results

* `RandomSystem.mass_unsetMBOs_sub_sum_le`: a step loses from the unset part the probability
  that the game sets the MBO
* `RandomSystem.winProbability_le_of_transcriptCost_le`,
  `Domain.Distinguisher.winProbability_le_of_transcriptCost_le`: a game that sets the MBO at each
  step with probability at most the cost of the step is won with probability at most the largest
  cost of a possible transcript
* `RandomSystem.GameEquivalent.transcriptDistance_visible_le`: two games equivalent as games, the
  first of which sets the MBO at each step with probability at most its cost, have visible
  systems within the largest cost of a possible transcript
* `PDG.gameEquivalent_behavior_of_isCoupling`: coupled discrete games whose systems answer alike
  while the condition does not hold are equivalent as games
-/

namespace SystemAlgebra

open Probability
open scoped NNReal

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

/-! ## The unset part of a game -/

/-- The part of a game with every MBO unset lies below its visible system: `G (h with every MBO
unset)` is one term of the sum over the MBOs. -/
theorem RandomSystem.mass_unsetMBOs_le_visible
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE))
    (h : List ((Σ i, X i) × Σ i, Y i)) : G (unsetMBOs h) ≤ G.visible h := by
  have := le_sumMBO G.mass_nonneg (unsetMBOs h)
  rwa [forgetMBOs_unsetMBOs, ← RandomSystem.visible_apply] at this

/-- **A step loses from the unset part the probability of setting the MBO**: from a transcript
`h` with every MBO unset, the replies to an admitted query `x` with the MBO unset weigh the
probability of `h` with every MBO unset minus the probability that `G` sets the MBO at `x`. So
if that probability is at most `b` times the probability of `h` with every MBO unset, with
`b ≥ 0`, the unset part loses at most `b` times the probability of `h` in the visible system. -/
theorem RandomSystem.mass_unsetMBOs_sub_sum_le
    (G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE))
    {h : List ((Σ i, X i) × Σ i, Y i)} {x : Σ i, X i} (hx : E (h.map Prod.fst ++ [x])) {b : ℝ}
    (hb : 0 ≤ b) (hset : ∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)]) ≤ b * G (unsetMBOs h)) :
    G (unsetMBOs h) - ∑ y, G (unsetMBOs (h ++ [(x, y)])) ≤ b * G.visible h := by
  -- Unsetting the MBOs keeps the queries, and unsets the MBO of the last reply.
  have hfst : (unsetMBOs h).map Prod.fst = h.map Prod.fst := by
    simp [unsetMBOs, Function.comp_def]
  have hsnoc : ∀ y, unsetMBOs (h ++ [(x, y)]) = unsetMBOs h ++ [(x, tagMBO false y)] :=
    fun y => by simp [unsetMBOs]
  -- The replies to the admitted x with both MBOs weigh G(h unset) (sum_tagMBO), so the loss is
  -- the probability that G sets the MBO at x.
  have hsum := G.sum_tagMBO (unsetMBOs h) x
  rw [hfst, if_pos hx, Finset.sum_add_distrib] at hsum
  simp only [hsnoc]
  calc G (unsetMBOs h) - ∑ y, G (unsetMBOs h ++ [(x, tagMBO false y)])
      = ∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)]) := by linarith
    _ ≤ b * G (unsetMBOs h) := hset
    -- G(h unset) ≤ G⁻(h), and b ≥ 0.
    _ ≤ b * G.visible h := mul_le_mul_of_nonneg_left (G.mass_unsetMBOs_le_visible h) hb

/-! ## Winning, bounded by the costs of the steps -/

/-- **Winning is bounded by the costs of the steps**, for a deterministic distinguisher: if, from
every transcript `h` with every MBO unset, the game `G` sets the MBO at the next admitted query
`x` with probability at most `β h x` times the probability of `h` with every MBO unset, and every
possible transcript of the visible system costs at most `ε`, then `G` is won with probability at
most `ε`. This is the union bound over the steps. -/
theorem RandomSystem.winProbability_le_of_transcriptCost_le
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    {β : List ((Σ i, X i) × Σ i, Y i) → (Σ i, X i) → ℝ} (hβ : ∀ h x, 0 ≤ β h x)
    (hset : ∀ h x, E (h.map Prod.fst ++ [x]) →
      ∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)]) ≤ β h x * G (unsetMBOs h))
    {ε : ℝ} (hcost : ∀ h, G.visible h ≠ 0 → transcriptCost β h ≤ ε)
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D) :
    G.winProbability D hD ≤ ε := by
  -- Plan. The winner is D's environment e, blind to the MBO, for n rounds:
  --
  --   ┌────────────────┐ ───── x ─────▶ ┌───┐
  --   │ W = blindMBO e │                │ G │
  --   └────────────────┘ ◀─── (y, a) ── └───┘
  --
  -- Write g(h) = G(h with every MBO 0), the unset part of G, and G⁻ for the visible system.
  -- 1. Γ_D(G) = 1 − |ν|, with ν the unset part on the transcripts of e within n rounds
  --    (exists_unset_winProbability).
  -- 2. g ≤ G⁻, and a step from h by an admitted x loses from g the probability that G sets the
  --    MBO at x:
  --      g(h) − Σ_y g(h, x, y) = Σ_y G(h unset, (x, (y, 1))) ≤ β h x · g(h) ≤ β h x · G⁻(h).
  -- 3. The union bound over the steps, for G⁻ and g (one_sub_le_sum_tSupp): |ν| ≥ 1 − ε.
  -- Step 1.
  obtain ⟨ν, hν, hwin⟩ := G.exists_unset_winProbability hG hm D hD hdc
  set e := ddeOf hD
  set n := hD.2.1.choose
  -- Step 2. g ≤ G⁻, and the loss of a step (mass_unsetMBOs_sub_sum_le).
  have hgV := G.mass_unsetMBOs_le_visible
  have hloss : ∀ h x, G.visible h ≠ 0 → (Domain.ofInputs E m hE) h x →
      G (unsetMBOs h) - ∑ y, G (unsetMBOs (h ++ [(x, y)])) ≤ β h x * G.visible h :=
    fun h x _ hx => G.mass_unsetMBOs_sub_sum_le hx (hβ h x) (hset h x hx)
  -- Step 3. G⁻ is compatible with e, as D is compatible with the input domain; the union
  -- bound over the steps gives the unset part at least 1 − ε on the transcripts of e.
  have hpot := G.visible.one_sub_le_sum_tSupp (hdc.environment hD _ hG.visible) hgV G.mass_nil
    hloss hcost n
  -- |ν| is that mass: ν is the unset part on the transcripts of e, and lives on those that G⁻
  -- makes possible, since g ≤ G⁻.
  have hsupp : ν.support ⊆ tSupp G.visible e.1 n := by
    intro h hh
    rw [Finsupp.mem_support_iff, hν] at hh
    split_ifs at hh with hgood
    · exact mem_tSupp hgood (ne_of_gt (lt_of_lt_of_le
        (lt_of_le_of_ne (G.mass_nonneg _) (Ne.symm hh)) (hgV h)))
    · exact absurd rfl hh
  have hw : ν.weight = ∑ h ∈ tSupp G.visible e.1 n, G (unsetMBOs h) := by
    rw [Distribution.weight_eq_sum_of_support_subset ν hsupp]
    exact Finset.sum_congr rfl fun h hh => by rw [hν, if_pos (tSupp_good hh)]
  -- Γ_D(G) = 1 − |ν| ≤ ε.
  rw [hwin, hw]
  linarith

/-- **Winning is bounded by the costs of the steps**: if, from every transcript `h` with every
MBO unset, the game `G` sets the MBO at the next admitted query `x` with probability at most
`β h x` times the probability of `h` with every MBO unset, and every possible transcript of the
visible system costs at most `ε`, then every distinguisher wins `G` with probability at most
`ε`. -/
theorem Domain.Distinguisher.winProbability_le_of_transcriptCost_le
    (P : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).Distinguisher)
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    {β : List ((Σ i, X i) × Σ i, Y i) → (Σ i, X i) → ℝ} (hβ : ∀ h x, 0 ≤ β h x)
    (hset : ∀ h x, E (h.map Prod.fst ++ [x]) →
      ∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)]) ≤ β h x * G (unsetMBOs h))
    {ε : ℝ} (hcost : ∀ h, G.visible h ≠ 0 → transcriptCost β h ≤ ε) :
    P.winProbability G ≤ ε := by
  -- Γ_P(G) = Σ_D P(D)·Γ_D(G) ≤ Σ_D P(D)·ε = ε.
  calc P.winProbability G ≤ P.1.sum fun _ w => w * ε := by
        -- Termwise, by the deterministic case scaled by P(D) ≥ 0.
        simp only [Domain.Distinguisher.winProbability, Finsupp.sum]
        exact Finset.sum_le_sum fun D _ => mul_le_mul_of_nonneg_left
          (RandomSystem.winProbability_le_of_transcriptCost_le hG hm hβ hset hcost D.1 D.2.1
            D.2.2) (P.2.1 D)
    _ = ε := by
        -- Σ_D P(D)·ε = (Σ_D P(D))·ε = ε, as P's weights sum to 1.
        simp only [Finsupp.sum, ← Finset.sum_mul]
        rw [show (∑ D ∈ P.1.support, P.1 D) = 1 from P.2.2, one_mul]

/-- **Games identical until bad**: two games equivalent as games, such that from every
transcript `h` with every MBO unset the first sets the MBO at the next admitted query `x` with
probability at most `β h x` times the probability of `h` with every MBO unset, and every possible
transcript of its visible system costs at most `ε`, have visible systems within `ε`. Equivalence
as games (CR18, Definition 4.16; Maurer 2002, Definition 5) makes the part of the games with every
MBO unset common to both: it lies below both visible systems. The per-step costs bound the mass
missing from it, `RandomSystem.transcriptDistance_le_of_transcriptCost_le`. Neither game needs to
be monotone, and only the first needs to reply at the queried interface. -/
theorem RandomSystem.GameEquivalent.transcriptDistance_visible_le
    {G H : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (he : G.GameEquivalent H)
    {β : List ((Σ i, X i) × Σ i, Y i) → (Σ i, X i) → ℝ} (hβ : ∀ h x, 0 ≤ β h x)
    (hset : ∀ h x, E (h.map Prod.fst ++ [x]) →
      ∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)]) ≤ β h x * G (unsetMBOs h))
    {ε : ℝ≥0} (hcost : ∀ h, G.visible h ≠ 0 → transcriptCost β h ≤ ε) :
    G.visible.transcriptDistance H.visible ≤ ε :=
  -- An environment plays the visible systems, which drop the MBO:
  --
  --   ┌───┐ ──x──▶ ┌───┐                    ┌───┐ ──x──▶ ┌───┐
  --   │ E │        │ G │ ──▶ a (dropped)    │ E │        │ H │ ──▶ a (dropped)
  --   └───┘ ◀──y── └───┘                    └───┘ ◀──y── └───┘
  --
  -- The common part is g(h) = G(h with every MBO 0), whole at the empty transcript:
  --   g ≤ G⁻                                  (one term of the sum over the MBOs)
  --   g(h) = H(h with every MBO 0) ≤ H⁻        (equivalence as games, then the same for H)
  -- A step of G⁻ loses from g the probability that G sets the MBO, at most β h x · G⁻(h)
  -- (mass_unsetMBOs_sub_sum_le), so Δ(G⁻, H⁻) ≤ ε (transcriptDistance_le_of_transcriptCost_le).
  RandomSystem.transcriptDistance_le_of_transcriptCost_le hG.visible G.mass_unsetMBOs_le_visible
    (fun h => (he h).trans_le (H.mass_unsetMBOs_le_visible h)) G.mass_nil
    (fun h x _ hx => G.mass_unsetMBOs_sub_sum_le hx (hβ h x) (hset h x hx)) hcost

/-! ## Coupled discrete games -/

/-- **Coupled discrete games are equivalent as games**: if `J` is a joint distribution of the
discrete games `P₀` and `P₁` (Lanzenberger–Maurer, Theorem 2, printed p. 15: "PDS S ∈ S and
T ∈ T with a joint distribution (or coupling)"), and each pair of deterministic games in its
support has one condition and systems that answer alike while the condition does not hold, then
the games they present are equivalent as games (CR18, Definition 4.16; Maurer 2002,
Definition 5). Two discrete games sampled together, `P₀` and `P₁` the pushforwards of one sample
law `Q` along `f₀` and `f₁`, are the case of `J` the pushforward of `Q` along `(f₀, f₁)`. -/
theorem PDG.gameEquivalent_behavior_of_isCoupling
    {P₀ P₁ : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)} (h₀ : P₀.isProbDist)
    (h₁ : P₁.isProbDist)
    {J : Distribution
      ({g : DDG (Σ i, X i) (Σ i, Y i) // HasDomain (Domain.ofInputs E m hE) g.1.1} ×
        {g : DDG (Σ i, X i) (Σ i, Y i) // HasDomain (Domain.ofInputs E m hE) g.1.1})}
    (hJ : Distribution.IsCoupling J P₀ P₁) (condition : ∀ gg ∈ J.support, gg.1.1.2 = gg.2.1.2)
    (agree : ∀ gg ∈ J.support, ∀ xs ys, ¬ gg.1.1.2.1 xs →
      (Replies gg.1.1.1.1 xs ys ↔ Replies gg.2.1.1.1 xs ys)) :
    (P₀.behavior h₀).GameEquivalent (P₁.behavior h₁) := by
  -- Each game gives a transcript h with every MBO unset the mass of its deterministic games that
  -- reply h with every MBO unset. Both masses are masses of J, the first of an event on the
  -- first game of a pair, the second on the second; on each pair in the support of J the two
  -- events agree:
  --
  --            ┌──────────────┐
  --            │ (g₀, g₁) ~ J │   g₀ ~ P₀, g₁ ~ P₁, one condition c
  --            └──────────────┘
  --   g₀ replies h unset  ⟺  s₀ replies h ∧ ¬ c(queries of h)
  --                       ⟺  s₁ replies h ∧ ¬ c(queries of h)   (they answer alike until c)
  --                       ⟺  g₁ replies h unset.
  intro h
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  -- The empty transcript: both games give it probability one.
  · exact ((P₀.behavior h₀).mass_nil).trans ((P₁.behavior h₁).mass_nil).symm
  · rw [List.concat_eq_append]
    -- Unsetting the MBOs keeps the queries and tags each reply with MBO 0.
    have hfst : (unsetMBOs (p ++ [z])).map Prod.fst = (p ++ [z]).map Prod.fst := by
      simp [unsetMBOs, Function.comp_def]
    have hsnd : (unsetMBOs (p ++ [z])).map Prod.snd =
        ((p ++ [z]).map Prod.snd).map (tagMBO false) := by
      simp [unsetMBOs, Function.comp_def]
    -- Both masses as masses of J: P₀ and P₁ are its marginals.
    rw [PDG.behavior_apply, PDG.behavior_apply, ← hJ.1, ← hJ.2, Distribution.mass_fTransform,
      Distribution.mass_fTransform]
    apply Distribution.mass_congr_of_support
    intro gg hgg
    -- On a nonempty transcript, a game with the MBO replies it unset iff its system replies it
    -- and the condition does not hold (replies_withMBO_unset_iff); the condition is common.
    rw [hfst, hsnd, DDG.replies_withMBO_unset_iff _ (by simp),
      DDG.replies_withMBO_unset_iff _ (by simp), ← condition gg hgg]
    -- While the condition does not hold, the two systems answer alike.
    exact ⟨fun ⟨hr, hb⟩ => ⟨(agree gg hgg _ _ hb).mp hr, hb⟩,
      fun ⟨hr, hb⟩ => ⟨(agree gg hgg _ _ hb).mpr hr, hb⟩⟩

end SystemAlgebra

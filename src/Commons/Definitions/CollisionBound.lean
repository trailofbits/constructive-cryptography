module

public import Commons.Definitions.CollisionGame
public import ConstructiveCryptography.Instances.Game
public import Probability.Counting.Collision
public import RandomSystems.Game.UntilBad

/-!
# Adaptive collisions in a uniform random function

`collisionGame_win_le` bounds every winner of `URF.collisionGame` by `C(r, 2) / |Y|` on a
single-port domain admitting at most `r` distinct tested inputs. The domain still has its
original length bound, and admitted repeated queries cost zero. This refines the pair count in
[1, proof of Theorem 4.6, p. 138] by charging only fresh inputs. The primitive is the retained
uniform function of [2, §3.2, p. 6]: “a uniformly chosen function table F”.

The cumulative unset law `collisionGame_unsetMBOs_eq`, in `CollisionGame`, restricts URF mass
to transcripts whose equal replies came from identical inputs. `collisionGame_unset_snoc_eq`
expresses one more unset reply as the table event that no new collision occurs.
`collisionGame_set_mass_eq` uses normalization to identify the next set-bit mass with the
new-collision event. The distinct-input bound in `Probability.Counting.Collision` then gives
`collisionGame_set_mass_le`:
a fresh query costs `d / |Y|` after `d` distinct earlier inputs, and a repeat costs zero.

`transcriptCost_distinct_eq_choose`, in `RandomSystems.Distance.UntilBad`, sums these
costs to `C(d, 2) / |Y|`. The domain hypothesis bounds `d` by `r`.
`collisionGame_winProbability_le` supplies these two contracts to the adaptive game bound in
`RandomSystems.Game.UntilBad`; `collisionGame_win_le` lifts it to admitted game winners.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back).
   In *Theory of Cryptography*, TCC 2016-B, LNCS 9985, pp. 3–24, Springer, 2016.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution
open scoped BigOperators NNReal

namespace Commons.URF

-- `I` is the sole port; `X`, `Y` are its finite alphabets, with inhabited replies.
variable {I X Y : Type} [Unique I] [Fintype X] [Fintype Y] [Nonempty Y]
    -- `D` admits query lists; `hD` excludes the empty list and closes nonempty prefixes.
    (D : List (Σ _ : I, X) → Prop)
    (hD : ¬ D [] ∧ ∀ {p h}, p <+: h → p ≠ [] → D h → D p)
    -- `q` bounds interaction length; `hq` certifies that bound on every admitted list.
    (q : ℕ) (hq : ∀ xs, D xs → xs.length ≤ q)

-- `A` retains this exact domain; `G` is its URF game with hidden MBOs.
local notation "A" => (Interface.mk I (fun _ => X) (fun _ => Y) D hD q hq)
local notation "G" => Subtype.val (Subtype.val (collisionGame A))

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- After collision-free replies, one further reply is collision-free exactly when its value
matches no earlier reply at a distinct input. -/
lemma replies_injective_append_iff
    -- `h` is the earlier transcript; `good` excludes collisions between its distinct inputs.
    {h : List ((Σ _ : I, X) × Σ _ : I, Y)}
    (good : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1)
    -- `x`, `y` are the next query/reply; `f` supplies this reply through `reply`.
    (x : Σ _ : I, X) (y : Σ _ : I, Y) (f : X → Y)
    (reply : f x.2 = y.2) :
    (∀ a ∈ h ++ [(x, y)], ∀ b ∈ h ++ [(x, y)], a.2 = b.2 → a.1 = b.1) ↔
      ¬ ∃ z ∈ h, z.1.2 ≠ x.2 ∧ f x.2 = z.2.2 := by
  -- Any new collision pairs the last reply with one earlier reply.
  constructor
  · intro hg hb
    obtain ⟨z, hz, hne, he⟩ := hb
    have ho : z.2 = y := Sigma.ext (Subsingleton.elim _ _) (heq_of_eq (he.symm.trans reply))
    exact hne (congrArg Sigma.snd
      (hg z (List.mem_append_left _ hz) (x, y)
        (List.mem_append_right _ (List.mem_singleton_self _)) ho))
  · intro noBad a ha b hb he
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact good a ha b hb he
    · obtain rfl := List.mem_singleton.mp hb
      apply Sigma.ext (Subsingleton.elim _ _)
      apply heq_of_eq
      by_contra hn
      exact noBad ⟨a, ha, hn, reply.trans (congrArg Sigma.snd he).symm⟩
    · obtain rfl := List.mem_singleton.mp ha
      apply Eq.symm
      apply Sigma.ext (Subsingleton.elim _ _)
      apply heq_of_eq
      by_contra hn
      exact noBad ⟨b, hb, hn, reply.trans (congrArg Sigma.snd he)⟩
    · obtain rfl := List.mem_singleton.mp ha
      obtain rfl := List.mem_singleton.mp hb
      rfl

open Classical in
/-- The next cumulative mass with MBOs unset is the joint table mass of all visible replies
and no new collision. -/
lemma collisionGame_unset_snoc_eq
    -- `h` has collision-free replies by `good`; `x`, `y` extend it within `D` by `admitted`.
    {h : List ((Σ _ : I, X) × Σ _ : I, Y)}
    (good : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1)
    (x : Σ _ : I, X) (y : Σ _ : I, Y) (admitted : D (h.map Prod.fst ++ [x])) :
    G (unsetMBOs (h ++ [(x, y)])) = (uniform (X → Y)).mass (fun f =>
      ((∀ z ∈ h, f z.1.2 = z.2.2) ∧ f x.2 = y.2) ∧
        ¬ ∃ z ∈ h, z.1.2 ≠ x.2 ∧ f x.2 = z.2.2) := by
  classical
  -- The unset-law identity reduces the game to its function-table probability.
  rw [collisionGame_unsetMBOs_eq,
    single_mass D hD q hq _
      (Or.inr (by simpa only [List.map_append, List.map_singleton] using admitted))]
  by_cases hg : ∀ a ∈ h ++ [(x, y)], ∀ b ∈ h ++ [(x, y)], a.2 = b.2 → a.1 = b.1
  · rw [ite_eq_left hg]
    apply mass_congr
    intro f
    simp only [List.forall_mem_append, List.forall_mem_singleton]
    exact ⟨fun hr => ⟨hr, (replies_injective_append_iff good x y f hr.2).mp hg⟩, And.left⟩
  · rw [ite_eq_right hg]
    symm
    exact mass_eq_zero_of_forall_not _ fun f hf =>
      hg ((replies_injective_append_iff good x y f hf.1.2).mpr hf.2)

open Classical in
/-- After collision-free replies, the next set-bit mass is precisely the uniform-table mass
of those replies jointly with a collision at the next input. -/
lemma collisionGame_set_mass_eq
    -- `h` has collision-free replies by `good`; `admitted` permits the next query `x`.
    (h : List ((Σ _ : I, X) × Σ _ : I, Y))
    (good : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1)
    (x : Σ _ : I, X) (admitted : D (h.map Prod.fst ++ [x])) :
    (∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)])) =
      (uniform (X → Y)).mass (fun f =>
        (∀ z ∈ h, f z.1.2 = z.2.2) ∧ ∃ z ∈ h, z.1.2 ≠ x.2 ∧ f x.2 = z.2.2) := by
  classical
  have hadm : h = [] ∨ D (h.map Prod.fst) := by
    by_cases hn : h = []
    · exact Or.inl hn
    · exact Or.inr (hD.2 (List.prefix_append _ _)
        (fun he => hn (List.map_eq_nil_iff.mp he)) admitted)
  -- On a good transcript, the unset game has the full URF transcript mass.
  have hmass : G (unsetMBOs h) =
      (uniform (X → Y)).mass (fun f => ∀ z ∈ h, f z.1.2 = z.2.2) := by
    rw [collisionGame_unsetMBOs_eq, ite_eq_left good, single_mass D hD q hq h hadm]
  -- Sum over the next reply: the unset extensions are precisely tables with no new collision.
  have hsum : (∑ y : Σ _ : I, Y, G (unsetMBOs (h ++ [(x, y)]))) =
      (uniform (X → Y)).mass (fun f =>
        (¬ ∃ z ∈ h, z.1.2 ≠ x.2 ∧ f x.2 = z.2.2) ∧
          (∀ z ∈ h, f z.1.2 = z.2.2)) := by
    simp only [collisionGame_unset_snoc_eq D hD q hq good x _ admitted]
    rw [mass_eq_sum_mass_fiber _ _ (fun f => f x.2) Finset.univ (fun _ _ => Finset.mem_univ _)]
    -- The sole port carries no choice; sum over reply values using the product equivalence.
    let e : (Σ _ : I, Y) ≃ Y :=
      (Equiv.sigmaEquivProd I Y).trans (Equiv.uniqueProd Y I)
    apply Fintype.sum_equiv e
    intro y
    apply mass_congr
    intro f
    change (((∀ z ∈ h, f z.1.2 = z.2.2) ∧ f x.2 = y.2) ∧ _) ↔
      ((_) ∧ (∀ z ∈ h, f z.1.2 = z.2.2)) ∧ f x.2 = y.2
    exact ⟨fun hf => ⟨⟨hf.2, hf.1.1⟩, hf.1.2⟩,
      fun hf => ⟨⟨hf.1.2, hf.2⟩, hf.1.1⟩⟩
  -- The common normalization law splits unset extensions from the set-bit extensions.
  have norm := RandomSystem.sum_unsetMBOs_add_sum_tagMBO G admitted
  rw [hsum, hmass] at norm
  -- Partition agreeing tables by the new collision; the true-bit mass is the bad part.
  have split := mass_and_add_mass_not_and (uniform (X → Y))
    (fun f => ∃ z ∈ h, z.1.2 ≠ x.2 ∧ f x.2 = z.2.2)
    (fun f => ∀ z ∈ h, f z.1.2 = z.2.2)
  rw [mass_congr _ (fun _ => and_comm)]
  linarith

open Classical in
/-- A repeated input costs zero; a fresh input costs at most `d / |Y|` times the unset mass,
where `d` counts distinct earlier inputs. -/
lemma collisionGame_set_mass_le
    -- `h` records the earlier queries/replies; `x` is admitted after its input history.
    (h : List ((Σ _ : I, X) × Σ _ : I, Y))
    (x : Σ _ : I, X) (admitted : D (h.map Prod.fst ++ [x])) :
    (∑ y, G (unsetMBOs h ++ [(x, tagMBO true y)])) ≤
      (if x.2 ∈ h.map (fun z => z.1.2) then 0 else
        ((h.map (fun z => z.1.2)).toFinset.card : ℝ) / Fintype.card Y) *
          G (unsetMBOs h) := by
  classical
  by_cases good : ∀ a ∈ h, ∀ b ∈ h, a.2 = b.2 → a.1 = b.1
  · have hadm : h = [] ∨ D (h.map Prod.fst) := by
      by_cases hn : h = []
      · exact Or.inl hn
      · exact Or.inr (hD.2 (List.prefix_append _ _)
          (fun he => hn (List.map_eq_nil_iff.mp he)) admitted)
    -- The exact next-bit and unset laws reduce the game bound to the conditional table bound.
    rw [collisionGame_set_mass_eq D hD q hq h good x admitted,
      collisionGame_unsetMBOs_eq, ite_eq_left good, single_mass D hD q hq h hadm]
    -- Removing the sole port preserves replies; apply the distinct-input conditional bound.
    have hg : ∀ a ∈ h.map (fun z => (z.1.2, z.2.2)),
        ∀ b ∈ h.map (fun z => (z.1.2, z.2.2)), a.2 = b.2 → a.1 = b.1 := by
      intro a ha b hb he
      obtain ⟨a0, ha0, rfl⟩ := List.mem_map.mp ha
      obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
      exact congrArg Sigma.snd (good a0 ha0 b0 hb0
        (Sigma.ext (Subsingleton.elim _ _) (heq_of_eq he)))
    have count := Counting.uniform_mass_transcript_collision_le_card
      (h.map (fun z => (z.1.2, z.2.2))) x.2 hg
    simp only [List.forall_mem_map, List.map_map, Function.comp_def] at count
    simpa only [List.mem_map, exists_exists_and_eq_and] using count
  · -- A transcript already containing a collision has no all-unset continuation.
    have zero : G (unsetMBOs h) = 0 := by
      rw [collisionGame_unsetMBOs_eq, ite_eq_right good]
    rw [zero, mul_zero]
    exact le_of_eq (Finset.sum_eq_zero fun y _ =>
      RandomSystem.mass_eq_zero_of_prefix G (List.prefix_append _ _) zero)

open Classical in
/-- Every compatible stopping distinguisher wins with probability at most `C(r, 2) / |Y|`
when the selected domain permits at most `r` distinct tested inputs. -/
lemma collisionGame_winProbability_le
    -- `r` bounds distinct inputs, certified by `tested` on the exact selected domain `D`.
    (r : ℕ)
    (tested : ∀ xs, D xs → (xs.map Sigma.snd).toFinset.card ≤ r)
    -- `P` is a law over deterministic distinguishers compatible with `D` and guaranteed to stop.
    (P : (Interface.inputDomain A).Distinguisher) :
    P.winProbability G ≤ ((r.choose 2 : ℝ≥0) / Fintype.card Y : ℝ≥0) := by
  classical
  -- The existing adaptive game bound consumes the step cost and its total along each path.
  apply P.winProbability_le_of_transcriptCost_le (collisionGame A).1.2 (collisionGame A).2
    (β := fun h x => if x.2 ∈ h.map (Sigma.snd ∘ Prod.fst) then 0 else
      ((h.map (Sigma.snd ∘ Prod.fst)).toFinset.card : ℝ) / Fintype.card Y)
    (fun _ _ => by
      split_ifs
      · exact le_rfl
      · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    (fun h x hx => collisionGame_set_mass_le D hD q hq h x hx)
  intro h hh
  -- Positive visible mass puts a nonempty transcript in `D`, where `tested` bounds its inputs.
  have hn : (h.map (Sigma.snd ∘ Prod.fst)).toFinset.card ≤ r := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
    · simp only [List.map_nil, List.toFinset_nil, Finset.card_empty, Nat.zero_le]
    · rw [List.concat_eq_append] at hh
      have hadm : D ((h ++ [z]).map Prod.fst) := by
        by_contra hd
        apply hh
        exact RandomSystem.mass_eq_zero_of_not_admitted (G).visible
          (by change ¬ D (h.map Prod.fst ++ [z.1])
              simpa only [List.map_append, List.map_singleton] using hd) z.2
      simpa only [List.concat_eq_append, List.map_map] using tested _ hadm
  -- Only fresh inputs add pairs: the total is `C(d, 2) / |Y|`, with `d ≤ r`.
  rw [transcriptCost_distinct_eq_choose (fun x : Σ _ : I, X => x.2) (Fintype.card Y : ℝ) h]
  change ((h.map (Sigma.snd ∘ Prod.fst)).toFinset.card.choose 2 : ℝ) / Fintype.card Y ≤
    (r.choose 2 : ℝ) / Fintype.card Y
  exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.choose_le_choose 2 hn)) (Nat.cast_nonneg _)

open Classical in
/-- Every admitted winner has URF collision probability at most `C(r, 2) / |Y|`.
[1, proof of Theorem 4.6, p. 138] counts collisions among `Q` default draws in `X`:
“as there are less than Q²/2 such pairs, we have Pr[Z] ≤ Q²/2N”. Here the range `Y` is
independent of the input alphabet, so `N` becomes `|Y|`. Charging only distinct tested inputs
replaces the source's `Q` draws by at most `r` tests and retains the exact pair count. -/
theorem collisionGame_win_le
    -- `r` bounds distinct inputs; `tested` supplies that bound for every list admitted by `D`.
    (r : ℕ)
    (tested : ∀ xs, D xs → (xs.map Sigma.snd).toFinset.card ≤ r)
    -- `hw` admits `winner` as the winning view of a compatible stopping solver on `A`.
    {winner : TypedGame A → ℝ} (hw : winner ∈ ConstructiveCryptography.Games.winners A) :
    winner (collisionGame A) ≤ ((r.choose 2 : ℝ≥0) / Fintype.card Y : ℝ≥0) :=
  Interface.win_le (collisionGame_winProbability_le D hD q hq r tested) hw

end Commons.URF

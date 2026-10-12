import RandomSystems.Game.MBO

/-!
# Discrete games: presentations of games

A deterministic discrete game is a DDS paired with a hidden monotone condition on query
sequences; a probabilistic discrete game on a domain is a finite distribution over
deterministic discrete games whose systems have that domain (Lanzenberger, Definitions
2.20–2.22, printed p. 17; with the common domain of Lanzenberger–Maurer, Definition 8). A
probabilistic discrete game presents a game, as a PDS presents a random system: each reply of a
deterministic discrete game carries the condition on the queries so far as its MBO, and the game
is the behavior of these systems. Its visible system is the behavior of the visible systems, and
on a fixed admitted sequence of queries its MBO stays unset with the probability that the
condition does not hold. The game is conditionally equivalent to a random system `S` when the
replies with the condition unset factor through `S`.

## Main definitions

* `MC X`, `DDG X Y`, `PDG X Y D`: monotone conditions, deterministic discrete games, and
  probabilistic discrete games on the domain `D`
* `PDG.underlying`, `PDG.badProbability`, `PDG.goodProbability`: the PDS of the visible systems,
  the condition on a query sequence, and the replies jointly with the condition unset
* `DDG.withMBO`: a deterministic discrete game, with the condition as the MBO of its replies
* `PDG.withMBO`, `PDG.behavior`: a probabilistic discrete game with the MBO, and the game it
  presents

## Main results

* `PDG.visible_behavior`: the visible system is the behavior of the visible systems
* `PDG.monotoneMBO_behavior`: the MBO, once set, stays set
* `PDG.unsetProbability_behavior`: the MBO is unset on admitted fixed queries with the
  probability that the condition does not hold
* `PDG.one_sub_le_unsetProbability_behavior`: a bound on the condition at every admitted query
  sequence bounds the probability that the MBO is set
* `PDG.conditionallyEquivalent_behavior`: conditional equivalence from the factorization of the
  replies with the condition unset
-/

namespace SystemAlgebra

open Probability

section Discrete

/-- A hidden predicate which remains true under extension of the query list. -/
abbrev MC (X : Type) :=
  {bad : List X → Prop // ∀ ⦃h k⦄, h <+: k → bad h → bad k}

/-- A deterministic discrete game: its visible DDS and hidden monotone condition. -/
abbrev DDG (X Y : Type) := DDS X Y × MC X

/-- A probabilistic discrete game on the domain `D`: a finite distribution over
deterministic games whose systems have domain `D`. -/
abbrev PDG (X Y : Type) [Fintype X] [Fintype Y] (D : Domain X Y) :=
  Distribution {g : DDG X Y // HasDomain D g.1.1}

namespace PDG

variable {X Y : Type} [Fintype X] [Fintype Y] {D : Domain X Y}

/-- The PDS of the visible systems. -/
noncomputable def underlying (G : PDG X Y D) : PDS X Y D :=
  Distribution.fTransform (fun g => ⟨g.1.1.1, g.1.1.2, g.2⟩) G

/-- The probability that the condition holds on a query sequence. -/
noncomputable def badProbability (G : PDG X Y D) (xs : List X) : ℝ :=
  G.mass (fun g => g.1.2.1 xs)

/-- Joint probability of the visible replies and an unset condition. -/
noncomputable def goodProbability (G : PDG X Y D) (h : List (X × Y)) : ℝ :=
  G.mass (fun g => Replies g.1.1.1 (h.map Prod.fst) (h.map Prod.snd) ∧
    ¬ g.1.2.1 (h.map Prod.fst))

theorem underlying_probability {G : PDG X Y D} (hG : G.isProbDist) :
    G.underlying.isProbDist := Distribution.fTransform_isProbDist _ hG

end PDG

end Discrete

variable {I : Type} {X Y : I → Type}

/-- A reply with the MBO `c` is `v` exactly when the reply is `v` with its MBO forgotten and
the MBO of `v` is `c`. -/
theorem map_tagMBO_eq_some_iff {p : Part (Σ i, Y i)} {c : Bool} {v : Σ i, withMBO Y i} :
    p.map (tagMBO c) = Part.some v ↔ p = Part.some (forgetMBO v) ∧ v.2.2 = c := by
  -- Read both equations `_ = Part.some _` as membership, and unfold membership in a map.
  rw [Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  constructor
  -- (→) The reply `a ∈ p`, tagged with `c`, is `v`: so `forgetMBO v = a ∈ p` and the MBO
  -- of `v` is `c`.
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, rfl⟩
  -- (←) Take `a = forgetMBO v`; tagging it with `c`, the MBO of `v`, gives back `v`.
  · rintro ⟨ha, hc⟩
    exact ⟨forgetMBO v, ha, (eq_tagMBO_iff.mpr ⟨rfl, hc⟩).symm⟩

namespace DDG

open scoped Classical in
/-- **A deterministic game with the MBO**: each reply of its DDS carries the condition on the
queries so far. -/
noncomputable def withMBO (g : DDG (Σ i, X i) (Σ i, Y i)) :
    DDS (Σ i, X i) (Σ i, withMBO Y i) :=
  -- The deterministic discrete game `g` with its MBO. The DDS `g.1` answers each query; the
  -- hidden condition `g.2`, evaluated on the queries so far, is attached to the reply as its
  -- MBO (`tagMBO`). The winner `W` sees the replies yₖ but not the MBOs aₖ:
  --
  --   ┌───┐ ──xₖ──▶ ┌───────────────┐
  --   │ W │         │ DDS g.1       │ ──▶ a₁ a₂ …   (once 1, stays 1)
  --   └───┘ ◀──yₖ── │ condition g.2 │
  --                 └───────────────┘
  --
  --   yₖ = g.1 (x₁ … xₖ),   aₖ = 1 ⟺ g.2 (x₁ … xₖ).
  --
  -- Tagging leaves the domain of `g.1` unchanged, so the tagged system is again a DDS:
  -- silent before the first query, with a prefix-closed domain.
  ⟨fun h => (g.1.1 h).map (tagMBO (decide (g.2.1 h))), g.1.2.1,
    fun _ _ hp hn hd => g.1.2.2 hp hn hd⟩

/-- Forgetting the MBO gives the DDS of the game. -/
theorem relabel_withMBO (g : DDG (Σ i, X i) (Σ i, Y i)) :
    relabel (withMBO g).1 id forgetMBO = g.1.1 := by
  -- Compare the two systems at each query history `h`.
  funext h
  -- Unfold: the reply of `g.1` is tagged with the condition and then the MBO is forgotten.
  simp only [relabel, List.map_id, withMBO, Part.map_map]
  -- `forgetMBO (tagMBO b y) = y`, so the composite map is the identity.
  exact Part.map_id' (fun _ => rfl) _

open scoped Classical in
/-- The transcripts of a game with the MBO: the transcripts of its DDS, each reply with the
condition on the queries so far. -/
theorem replies_withMBO_iff (g : DDG (Σ i, X i) (Σ i, Y i)) (xs : List (Σ i, X i))
    (ys : List (Σ i, SystemAlgebra.withMBO Y i)) :
    Replies (withMBO g).1 xs ys ↔ Replies g.1.1 xs (ys.map forgetMBO) ∧
      ∀ k (hk : k < ys.length), ys[k].2.2 = decide (g.2.1 (xs.take (k + 1))) := by
  -- Unfold `Replies`: equal lengths, and at each k the system answers x₁ … x_{k+1} with
  -- ys[k]. A reply of the game with the MBO is the reply of `g.1` tagged with the condition
  -- on x₁ … x_{k+1}.
  simp only [Replies, List.length_map, List.getElem_map, withMBO]
  constructor
  -- (→) Split each tagged reply with `map_tagMBO_eq_some_iff`: the reply of `g.1` is
  -- `forgetMBO ys[k]`, and the MBO of ys[k] is the condition.
  · rintro ⟨hl, h⟩
    exact ⟨⟨hl, fun k hk hk' => (map_tagMBO_eq_some_iff.mp (h k hk hk')).1⟩,
      fun k hk => (map_tagMBO_eq_some_iff.mp (h k (hl ▸ hk) hk)).2⟩
  -- (←) Reassemble each tagged reply from the reply of `g.1` and the MBO.
  · rintro ⟨⟨hl, h⟩, ht⟩
    exact ⟨hl, fun k hk hk' => map_tagMBO_eq_some_iff.mpr ⟨h k hk hk', ht k hk'⟩⟩

/-- Along a transcript of a game with the MBO, the MBO, once set, stays set. -/
theorem pairwise_withMBO {g : DDG (Σ i, X i) (Σ i, Y i)} {xs : List (Σ i, X i)}
    {ys : List (Σ i, SystemAlgebra.withMBO Y i)} (hr : Replies (withMBO g).1 xs ys) :
    (ys.map fun y => y.2.2).Pairwise (· ≤ ·) := by
  -- By `replies_withMBO_iff`, the k-th MBO is the condition on x₁ … x_{k+1}.
  have ht := ((replies_withMBO_iff g xs ys).mp hr).2
  -- Check `≤` at every pair of positions i < j.
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map] at hi hj
  -- Both MBOs become the condition on x₁ … x_{i+1} and on x₁ … x_{j+1}.
  simp only [List.getElem_map, ht i hi, ht j hj]
  -- If the condition holds at i, it holds at j, since x₁ … x_{i+1} is a prefix of
  -- x₁ … x_{j+1} and the condition is monotone: 1 ≤ 1. Otherwise the MBO at i is 0.
  by_cases hb : g.2.1 (xs.take (i + 1))
  · have hb' : g.2.1 (xs.take (j + 1)) :=
      g.2.2 ((List.take_prefix_take_left (by omega) : xs.take (i + 1) <+: xs.take (j + 1))) hb
    simp [hb, hb']
  · simp [hb]

open scoped Classical in
/-- On a nonempty transcript, the MBO is unset throughout exactly when the condition does not
hold on its queries. -/
theorem replies_withMBO_unset_iff (g : DDG (Σ i, X i) (Σ i, Y i)) {xs : List (Σ i, X i)}
    (hxs : xs ≠ []) (ys : List (Σ i, Y i)) :
    Replies (withMBO g).1 xs (ys.map (tagMBO false)) ↔ Replies g.1.1 xs ys ∧ ¬ g.2.1 xs := by
  -- By `replies_withMBO_iff`: the replies with the MBO forgotten are replies of `g.1`, and
  -- each MBO is the condition on the queries so far.
  rw [replies_withMBO_iff]
  simp only [List.map_map, List.length_map]
  -- Forgetting an unset MBO undoes `tagMBO false`, so the first part is `Replies g.1 xs ys`.
  have hf : forgetMBO ∘ tagMBO false = (id : (Σ i, Y i) → Σ i, Y i) := rfl
  rw [hf, List.map_id]
  -- That part is common to both sides; match the MBO part with `¬ g.2 xs`.
  refine and_congr_right fun hr => ?_
  have hl := hr.length
  constructor
  -- (→) If the condition held on xs, the MBO of the last reply (k = |xs| - 1, the condition
  -- on all of xs) would be 1; but every MBO is 0.
  · intro ht hb
    have hk : xs.length - 1 < ys.length := by
      have := List.length_pos_iff.mpr hxs
      omega
    have := ht _ hk
    rw [Nat.sub_add_cancel (List.length_pos_iff.mpr hxs), List.take_length,
      List.getElem_map] at this
    simp [hb, tagMBO] at this
  -- (←) If the condition fails on xs, it fails on each prefix x₁ … x_{k+1} (monotonicity),
  -- so every MBO is 0, as the unset tag says.
  · intro hb k hk
    have hnb : ¬ g.2.1 (xs.take (k + 1)) := fun hb' => hb (g.2.2 (List.take_prefix _ _) hb')
    rw [List.getElem_map]
    simp [hnb, tagMBO]

end DDG

variable [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

namespace PDG

/-- **A probabilistic game with the MBO**: its deterministic games with the MBO. -/
noncomputable def withMBO (G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)) :
    PDS (Σ i, X i) (Σ i, SystemAlgebra.withMBO Y i) (Domain.ofInputs E m hE) :=
  -- Push `G` forward along g ↦ g with its MBO (`DDG.withMBO`); it remains to show that the
  -- tagged system has the domain.
  Distribution.fTransform (fun g => ⟨(DDG.withMBO g.1).1, (DDG.withMBO g.1).2, fun h x hr => by
    -- The DDS of `g` has the domain (`g.2`); apply this to `h` with its MBOs forgotten, which
    -- is a transcript of that DDS by `replies_withMBO_iff`.
    have hd := g.2 (forgetMBOs h) x (by
      rw [map_fst_forgetMBOs, map_snd_forgetMBOs]
      exact ((DDG.replies_withMBO_iff g.1 _ _).mp hr).1)
    -- Forgetting the MBOs keeps the queries. Tagging does not change where a reply is defined,
    -- and the input domain reads only the queries, so `hd` is the claim.
    rw [map_fst_forgetMBOs] at hd
    exact hd.trans (by simp only [Domain.ofInputs_apply, map_fst_forgetMBOs])⟩) G

theorem withMBO_isProbDist {G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hG : G.isProbDist) : G.withMBO.isProbDist :=
  Distribution.fTransform_isProbDist _ hG

/-- **The game a probabilistic discrete game presents**: the behavior of its deterministic
games with the MBO. -/
noncomputable def behavior (G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE))
    (hG : G.isProbDist) :
    RandomSystem (Σ i, X i) (Σ i, SystemAlgebra.withMBO Y i) (Domain.ofInputs E m hE) :=
  PDS.behavior G.withMBO (withMBO_isProbDist hG)

theorem behavior_apply (G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE))
    (hG : G.isProbDist) (h : List ((Σ i, X i) × Σ i, SystemAlgebra.withMBO Y i)) :
    G.behavior hG h =
      G.mass fun g => Replies (DDG.withMBO g.1).1 (h.map Prod.fst) (h.map Prod.snd) := by
  -- Unfold: the behavior gives `h` the mass of the samples that reply `h`, and the samples
  -- are the games with the MBO.
  rw [behavior, PDS.behavior_mass, behaviorMass, withMBO, Distribution.mass_fTransform]

variable {G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)} (hG : G.isProbDist)

open scoped Classical in
/-- **The visible system of the game of a probabilistic discrete game** is the behavior of its
visible systems. -/
theorem visible_behavior :
    (G.behavior hG).visible = PDS.behavior G.underlying (underlying_probability hG) := by
  -- Compare the two random systems transcript by transcript.
  apply RandomSystem.ext
  intro h
  -- Left: the visible system sums the game over the MBOs of `h` (`sumMBO`). Right: the mass
  -- of the visible systems (the DDS of each `g`) that reply `h`.
  rw [RandomSystem.visible_apply, PDS.behavior_mass, behaviorMass, underlying,
    Distribution.mass_fTransform]
  -- The game, as a finite sum over the support of `G`: k ↦ Σ_g G g · [g with MBO replies k].
  have he : (fun k => G.behavior hG k) = fun k => ∑ g ∈ G.support,
      G g * if Replies (DDG.withMBO g.1).1 (k.map Prod.fst) (k.map Prod.snd) then 1 else 0 := by
    funext k
    rw [behavior_apply]
    simp only [Distribution.mass, Finsupp.sum, mul_boole]
  -- Exchange the sum over MBOs and the sum over `g` (`sumMBO_sum`); write the right side as
  -- a sum over the support as well.
  rw [show sumMBO (G.behavior hG) h = sumMBO (fun k => G.behavior hG k) h from rfl, he,
    sumMBO_sum]
  simp only [Distribution.mass, Finsupp.sum]
  -- Compare term by term, for each `g` in the support.
  apply Finset.sum_congr rfl
  intro g _
  --   Σ_MBOs G g · [g with MBO replies k]
  --     = G g · Σ_MBOs [g with MBO replies k]            (sumMBO_const_mul)
  --     = G g · [g with MBO, MBO forgotten, replies h]    (sumMBO_replies)
  --     = G g · [the DDS of g replies h]                  (relabel_withMBO)
  --
  -- When the DDS of g replies `h`, exactly one choice of MBOs (the condition on the queries
  -- so far) gives a transcript of g with the MBO; otherwise none does.
  rw [sumMBO_const_mul, sumMBO_replies, DDG.relabel_withMBO, mul_boole]

/-- **The game of a probabilistic discrete game is a game**: its MBO, once set, stays set. -/
theorem monotoneMBO_behavior : (G.behavior hG).MonotoneMBO := by
  -- Take a transcript `h` of positive probability.
  intro h hne
  -- Its probability is the mass of the games with the MBO that reply `h`.
  rw [behavior_apply] at hne
  -- A nonzero finite sum has a nonzero term: some `g` in the support of `G`.
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  -- That term is nonzero only if `g` with the MBO replies `h`.
  have hr : Replies (DDG.withMBO g.1).1 (h.map Prod.fst) (h.map Prod.snd) := by
    by_contra hr
    simp [hr] at hg
  -- Along a transcript of a single game with the MBO, the MBO once set stays set
  -- (`DDG.pairwise_withMBO`).
  simpa only [List.map_map, Function.comp_def] using DDG.pairwise_withMBO hr

/-- The game replies at the queried interface when its visible systems do. -/
theorem repliesAtQueriedInterface_behavior
    (hU : (PDS.behavior G.underlying (underlying_probability hG)).RepliesAtQueriedInterface) :
    (G.behavior hG).RepliesAtQueriedInterface :=
  -- The game replies at the queried interface when its visible system does (`of_visible`),
  -- and its visible system is the behavior of the visible systems (`visible_behavior`).
  RandomSystem.RepliesAtQueriedInterface.of_visible ((visible_behavior hG).symm ▸ hU)

variable (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)

omit [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
include hE' in
/-- On an admitted query sequence, a deterministic game with the MBO answers every query. -/
theorem exists_transcript_withMBO
    (g : {g : DDG (Σ i, X i) (Σ i, Y i) // HasDomain (Domain.ofInputs E m hE) g.1.1})
    {xs : List (Σ i, X i)} (hxs : E xs) :
    ∃ ys, Transcript (DDG.withMBO g.1).1 (fixedQueries xs) xs ys := by
  -- `xs` is reachable for g with the MBO: each nonempty prefix of `xs` is in `E`
  -- (prefix-closed), the DDS of g answers exactly the histories in `E`
  -- (`hasDomain_ofInputs_iff`), and tagging keeps where replies are defined.
  have reach : Reach (DDG.withMBO g.1).1 xs := fun p e hp hn =>
    (((hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2) p).mpr (hE'.2 ⟨e, hp.symm⟩ hn hxs)
  -- The fixed queries `xs` on a reachable history produce a transcript
  -- (`transcript_fixedQueries`).
  exact (transcript_fixedQueries (s := (DDG.withMBO g.1).1) xs [] (List.append_nil xs).symm).mp
    reach

include hE' in
/-- **On an admitted query sequence, the MBO is unset with the probability that the condition
does not hold.** -/
theorem unsetProbability_behavior {xs : List (Σ i, X i)} (hxs : E xs) :
    (G.behavior hG).unsetProbability xs = 1 - G.badProbability xs := by
  -- Plan:
  --   1. With the fixed queries xs, every transcript of positive probability is complete; so
  --      `unsetProbability xs` is the mass of the completed transcripts with every MBO 0.
  --   2. By `sLaw_completed_eq_mass`, this is the `G`-mass of the games whose completed
  --      transcript with the MBO has every MBO 0; and 1 - badProbability xs is the `G`-mass
  --      of the games where the condition fails on xs.
  --   3. Game by game: the completed transcript has every MBO 0 iff the condition fails.
  --
  --   unsetProbability xs
  --     = Pr_sLaw[h complete ∧ every MBO 0]                     (step 1)
  --     = Σ_g G g · [g's completed transcript has every MBO 0]   (step 2)
  --     = Σ_g G g · [¬ c_g(xs)]                                  (step 3)
  --     = 1 - Pr_G[c_g(xs)]
  --
  -- where c_g is the condition of the game g.
  --
  -- `xs` is admitted and `E []` fails, so `xs` is nonempty.
  have hne : xs ≠ [] := fun he => hE'.1 (he ▸ hxs)
  -- After |xs| replies the fixed-query environment asks nothing more.
  have hstop : ∀ ys : List (Σ i, SystemAlgebra.withMBO Y i), ys.length = xs.length →
      ¬ (fixedQueries xs ys).Dom := by
    intro ys hl
    simp [fixedQueries, hl]
  -- Step 1: add "complete" to the event; it changes nothing on the support of the law.
  -- Every transcript of the fixed queries is complete.
  have hdone : (G.behavior hG).unsetProbability xs =
      ((G.behavior hG).sLaw (fixedQueries xs) xs.length).mass
        (fun h => ¬ (fixedQueries xs (h.map Prod.snd)).Dom ∧ ∀ z ∈ h, z.2.2.2 = false) := by
    apply Distribution.mass_congr_of_support
    intro h hh
    -- A transcript in the support of the transcript law follows the queries and is done.
    have hgood : Good (fixedQueries xs) xs.length h := by
      by_contra hn
      apply Finsupp.mem_support_iff.mp hh
      rw [RandomSystem.sLaw_apply]
      exact if_neg hn
    refine ⟨fun hu => ⟨?_, hu⟩, fun hu => hu.2⟩
    -- Done: either |h| = |xs|, after which there is no further query, or the environment has
    -- stopped already.
    rcases hgood.2 with hl | ⟨-, hd⟩
    · exact hstop _ (by rw [List.length_map, hl])
    · exact hd
  -- Step 2: the `G`-masses of the condition on xs and of its negation sum to 1.
  have hcompl := Distribution.mass_add_compl G (fun g => g.1.2.1 xs)
  rw [hG.2] at hcompl
  -- The completed-transcript mass is a `G`-mass of games (`sLaw_completed_eq_mass`; the
  -- game is the `G`-mixture of the games with the MBO, `behavior_apply`), and
  -- 1 - badProbability xs is the `G`-mass of ¬ c_g(xs).
  rw [hdone, RandomSystem.sLaw_completed_eq_mass (G.behavior hG) G hG.1
    (fun g => (DDG.withMBO g.1).1) (behavior_apply G hG), badProbability,
    show 1 - G.mass (fun g => g.1.2.1 xs) = G.mass (fun g => ¬ g.1.2.1 xs) by linarith]
  -- Step 3: compare the two events game by game.
  apply Distribution.mass_congr
  intro g
  -- `g` with the MBO has a transcript `ys` on all of xs (`exists_transcript_withMBO`).
  obtain ⟨ys, tr⟩ := exists_transcript_withMBO hE' g hxs
  have hl := tr.length_eq
  constructor
  · rintro ⟨h, tr', -, hd, hu⟩
    -- (→) Completed transcripts are unique (`eq_of_stopped`): the replies of `h` are `ys`.
    obtain ⟨-, hy⟩ := tr.eq_of_stopped tr' (hstop ys hl.symm) hd
    -- Every reply of `h` has MBO 0, so `ys` is its replies with the MBO forgotten and then
    -- tagged unset.
    have hys : ys = ((h.map Prod.snd).map forgetMBO).map (tagMBO false) := by
      rw [hy, List.map_map]
      conv_lhs => rw [← List.map_id (h.map Prod.snd)]
      apply List.map_congr_left
      intro y hy'
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy'
      exact eq_tagMBO_iff.mpr ⟨rfl, hu z hz⟩
    -- A transcript on nonempty xs with every MBO unset forces ¬ c_g(xs)
    -- (`replies_withMBO_unset_iff`).
    rw [hys] at tr
    exact ((DDG.replies_withMBO_unset_iff g.1 hne _).mp tr.replies).2
  -- (←) If the condition fails on xs, the witness is the transcript with queries xs and
  -- replies ys.
  · intro hb
    refine ⟨xs.zip ys, ?_, ?_, ?_, ?_⟩
    -- It is a transcript of g with the MBO under the fixed queries;
    · rwa [List.map_fst_zip (by omega), List.map_snd_zip (by omega)]
    -- its length is |xs|;
    · simp
    -- after |xs| replies there is no further query;
    · rw [List.map_snd_zip (by omega)]
      exact hstop ys hl.symm
    -- and its k-th MBO is the condition on x₁ … x_{k+1} (`replies_withMBO_iff`), which fails
    -- since the condition fails on xs and is monotone.
    · intro z hz
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
      have hk' : k < ys.length := by
        simp only [List.length_zip] at hk
        omega
      rw [List.getElem_zip]
      change ys[k].2.2 = false
      rw [((DDG.replies_withMBO_iff g.1 xs ys).mp tr.replies).2 k hk', decide_eq_false_iff_not]
      exact fun hb' => hb (g.1.2.2 (List.take_prefix _ _) hb')


include hE' in
/-- **A bound on the condition bounds the set MBO**: if the condition holds with probability at
most `ε` on the empty and on every admitted query sequence, the MBO stays unset with probability
at least `1 - ε` on the queries of each possible transcript of a random system on the domain. -/
theorem one_sub_le_unsetProbability_behavior
    {S : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)} {ε : ℝ}
    (hbad : ∀ xs, xs = [] ∨ E xs → G.badProbability xs ≤ ε) (h : List ((Σ i, X i) × Σ i, Y i))
    (hh : S h ≠ 0) : 1 - ε ≤ (G.behavior hG).unsetProbability (h.map Prod.fst) := by
  -- Split `h` into [] or p ++ [z].
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  -- h = []: the MBO is unset with probability 1, and ε ≥ badProbability [] ≥ 0.
  · rw [List.map_nil, RandomSystem.unsetProbability_nil]
    linarith [(hG.1.mass_nonneg _).trans (hbad [] (Or.inl rfl))]
  -- h = p ++ [z]:
  · simp only [List.concat_eq_append] at hh ⊢
    -- its queries are admitted: otherwise the last query is not admitted after `p`, and `S`
    -- would give `h` probability 0.
    have hadm : E ((p ++ [z]).map Prod.fst) := by
      by_contra hd
      exact hh (S.mass_eq_zero_of_not_admitted (by simpa using hd) z.2)
    -- On admitted queries the MBO is unset with probability 1 - badProbability ≥ 1 - ε.
    rw [unsetProbability_behavior hG hE' hadm]
    linarith [hbad _ (Or.inr hadm)]

include hE' in
/-- **Conditional equivalence from the factorization of the unset replies**: the game a
probabilistic discrete game presents is conditionally equivalent to a random system `S` when,
on each transcript, the probability of the replies with the condition unset is the probability
that the condition does not hold on the queries times the probability of the transcript under
`S`. -/
theorem conditionallyEquivalent_behavior
    {S : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (factor : ∀ h, G.goodProbability h = (1 - G.badProbability (h.map Prod.fst)) * S h) :
    (G.behavior hG).ConditionallyEquivalent S := by
  -- Show, for each transcript h:
  --   G(h with every MBO unset) = unsetProbability(queries of h) · S h.
  intro h
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  -- h = []: both sides are 1.
  · simp only [unsetMBOs, List.map_nil, RandomSystem.mass_nil, RandomSystem.unsetProbability_nil,
      mul_one]
  -- h = p ++ [z]:
  · simp only [List.concat_eq_append]
    -- unsetting the MBOs keeps the queries.
    have hfst : (unsetMBOs (p ++ [z])).map Prod.fst = (p ++ [z]).map Prod.fst := by
      simp [unsetMBOs, Function.comp_def]
    -- Case on whether the queries of h are admitted.
    by_cases hadm : E ((p ++ [z]).map Prod.fst)
    -- Admitted. With xs the queries of h, and s_g, c_g the DDS and the condition of a game g:
    --   G(h unset) = Pr_G[g with MBO replies h unset]     (behavior_apply)
    --              = Pr_G[s_g replies h ∧ ¬ c_g(xs)]       (replies_withMBO_unset_iff)
    --              = goodProbability h
    --              = (1 - badProbability xs) · S h        (factor)
    --              = unsetProbability xs · S h            (unsetProbability_behavior)
    · rw [unsetProbability_behavior hG hE' hadm, ← factor, behavior_apply, goodProbability]
      -- Compare the events game by game.
      apply Distribution.mass_congr
      intro g
      -- Unsetting the MBOs tags each reply with MBO 0.
      have hsnd : (unsetMBOs (p ++ [z])).map Prod.snd =
          ((p ++ [z]).map Prod.snd).map (tagMBO false) := by
        simp [unsetMBOs, Function.comp_def]
      rw [hfst, hsnd]
      -- On nonempty queries, g with the MBO replies h unset iff s_g replies h and ¬ c_g(xs).
      exact DDG.replies_withMBO_unset_iff g.1 (by simp) _
    -- Not admitted: the last query is not admitted after `p`, so `S` gives h probability 0;
    · have hS : S (p ++ [z]) = 0 :=
        S.mass_eq_zero_of_not_admitted (by simpa using hadm) z.2
      -- so does the game.
      have hG0 : G.behavior hG (unsetMBOs (p ++ [z])) = 0 := by
        rw [unsetMBOs, List.map_append, List.map_singleton]
        exact (G.behavior hG).mass_eq_zero_of_not_admitted
          (by simpa [Function.comp_def] using hadm) _
      rw [hS, hG0, mul_zero]

end PDG

end SystemAlgebra

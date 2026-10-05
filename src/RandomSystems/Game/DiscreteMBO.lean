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

open Classical Probability

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
  rw [Part.eq_some_iff, Part.eq_some_iff, Part.mem_map_iff]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, rfl⟩
  · rintro ⟨ha, hc⟩
    exact ⟨forgetMBO v, ha, (eq_tagMBO_iff.mpr ⟨rfl, hc⟩).symm⟩

namespace DDG

/-- **A deterministic game with the MBO**: each reply of its DDS carries the condition on the
queries so far. -/
noncomputable def withMBO (g : DDG (Σ i, X i) (Σ i, Y i)) :
    DDS (Σ i, X i) (Σ i, withMBO Y i) :=
  ⟨fun h => (g.1.1 h).map (tagMBO (decide (g.2.1 h))), g.1.2.1,
    fun _ _ hp hn hd => g.1.2.2 hp hn hd⟩

/-- Forgetting the MBO gives the DDS of the game. -/
theorem relabel_withMBO (g : DDG (Σ i, X i) (Σ i, Y i)) :
    relabel (withMBO g).1 id forgetMBO = g.1.1 := by
  funext h
  simp only [relabel, List.map_id, withMBO, Part.map_map]
  exact Part.map_id' (fun _ => rfl) _

/-- The transcripts of a game with the MBO: the transcripts of its DDS, each reply with the
condition on the queries so far. -/
theorem replies_withMBO_iff (g : DDG (Σ i, X i) (Σ i, Y i)) (xs : List (Σ i, X i))
    (ys : List (Σ i, SystemAlgebra.withMBO Y i)) :
    Replies (withMBO g).1 xs ys ↔ Replies g.1.1 xs (ys.map forgetMBO) ∧
      ∀ k (hk : k < ys.length), ys[k].2.2 = decide (g.2.1 (xs.take (k + 1))) := by
  simp only [Replies, List.length_map, List.getElem_map, withMBO]
  constructor
  · rintro ⟨hl, h⟩
    exact ⟨⟨hl, fun k hk hk' => (map_tagMBO_eq_some_iff.mp (h k hk hk')).1⟩,
      fun k hk => (map_tagMBO_eq_some_iff.mp (h k (hl ▸ hk) hk)).2⟩
  · rintro ⟨⟨hl, h⟩, ht⟩
    exact ⟨hl, fun k hk hk' => map_tagMBO_eq_some_iff.mpr ⟨h k hk hk', ht k hk'⟩⟩

/-- Along a transcript of a game with the MBO, the MBO, once set, stays set. -/
theorem pairwise_withMBO {g : DDG (Σ i, X i) (Σ i, Y i)} {xs : List (Σ i, X i)}
    {ys : List (Σ i, SystemAlgebra.withMBO Y i)} (hr : Replies (withMBO g).1 xs ys) :
    (ys.map fun y => y.2.2).Pairwise (· ≤ ·) := by
  have ht := ((replies_withMBO_iff g xs ys).mp hr).2
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.length_map] at hi hj
  simp only [List.getElem_map, ht i hi, ht j hj]
  by_cases hb : g.2.1 (xs.take (i + 1))
  · have hb' : g.2.1 (xs.take (j + 1)) :=
      g.2.2 ((List.take_prefix_take_left (by omega) : xs.take (i + 1) <+: xs.take (j + 1))) hb
    simp [hb, hb']
  · simp [hb]

/-- On a nonempty transcript, the MBO is unset throughout exactly when the condition does not
hold on its queries. -/
theorem replies_withMBO_unset_iff (g : DDG (Σ i, X i) (Σ i, Y i)) {xs : List (Σ i, X i)}
    (hxs : xs ≠ []) (ys : List (Σ i, Y i)) :
    Replies (withMBO g).1 xs (ys.map (tagMBO false)) ↔ Replies g.1.1 xs ys ∧ ¬ g.2.1 xs := by
  rw [replies_withMBO_iff]
  simp only [List.map_map, List.length_map]
  have hf : forgetMBO ∘ tagMBO false = (id : (Σ i, Y i) → Σ i, Y i) := rfl
  rw [hf, List.map_id]
  refine and_congr_right fun hr => ?_
  have hl := hr.length
  constructor
  · intro ht hb
    have hk : xs.length - 1 < ys.length := by
      have := List.length_pos_iff.mpr hxs
      omega
    have := ht _ hk
    rw [Nat.sub_add_cancel (List.length_pos_iff.mpr hxs), List.take_length,
      List.getElem_map] at this
    simp [hb, tagMBO] at this
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
  Distribution.fTransform (fun g => ⟨(DDG.withMBO g.1).1, (DDG.withMBO g.1).2, fun h x hr => by
    have hd := g.2 (forgetMBOs h) x (by
      rw [map_fst_forgetMBOs, map_snd_forgetMBOs]
      exact ((DDG.replies_withMBO_iff g.1 _ _).mp hr).1)
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
  rw [behavior, PDS.behavior_mass, behaviorMass, withMBO, Distribution.mass_fTransform]

variable {G : PDG (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)} (hG : G.isProbDist)

/-- **The visible system of the game of a probabilistic discrete game** is the behavior of its
visible systems. -/
theorem visible_behavior :
    (G.behavior hG).visible = PDS.behavior G.underlying (underlying_probability hG) := by
  apply RandomSystem.ext
  intro h
  rw [RandomSystem.visible_apply, PDS.behavior_mass, behaviorMass, underlying,
    Distribution.mass_fTransform]
  have he : (fun k => G.behavior hG k) = fun k => ∑ g ∈ G.support,
      G g * if Replies (DDG.withMBO g.1).1 (k.map Prod.fst) (k.map Prod.snd) then 1 else 0 := by
    funext k
    rw [behavior_apply]
    simp only [Distribution.mass, Finsupp.sum, mul_boole]
  rw [show sumMBO (G.behavior hG) h = sumMBO (fun k => G.behavior hG k) h from rfl, he,
    sumMBO_sum]
  simp only [Distribution.mass, Finsupp.sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [sumMBO_const_mul, sumMBO_replies, DDG.relabel_withMBO, mul_boole]

/-- **The game of a probabilistic discrete game is a game**: its MBO, once set, stays set. -/
theorem monotoneMBO_behavior : (G.behavior hG).MonotoneMBO := by
  intro h hne
  rw [behavior_apply] at hne
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hr : Replies (DDG.withMBO g.1).1 (h.map Prod.fst) (h.map Prod.snd) := by
    by_contra hr
    simp [hr] at hg
  simpa only [List.map_map, Function.comp_def] using DDG.pairwise_withMBO hr

/-- The game replies at the queried interface when its visible systems do. -/
theorem repliesAtQueriedInterface_behavior
    (hU : (PDS.behavior G.underlying (underlying_probability hG)).RepliesAtQueriedInterface) :
    (G.behavior hG).RepliesAtQueriedInterface :=
  RandomSystem.RepliesAtQueriedInterface.of_visible ((visible_behavior hG).symm ▸ hU)

variable (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)

omit [Fintype I] [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] in
include hE' in
/-- On an admitted query sequence, a deterministic game with the MBO answers every query. -/
theorem exists_transcript_withMBO
    (g : {g : DDG (Σ i, X i) (Σ i, Y i) // HasDomain (Domain.ofInputs E m hE) g.1.1})
    {xs : List (Σ i, X i)} (hxs : E xs) :
    ∃ ys, Transcript (DDG.withMBO g.1).1 (fixedQueries xs) xs ys := by
  have reach : Reach (DDG.withMBO g.1).1 xs := fun p e hp hn =>
    (((hasDomain_ofInputs_iff hE' g.1.1.2).mp g.2) p).mpr (hE'.2 ⟨e, hp.symm⟩ hn hxs)
  exact (transcript_fixedQueries (s := (DDG.withMBO g.1).1) xs [] (List.append_nil xs).symm).mp
    reach

include hE' in
/-- **On an admitted query sequence, the MBO is unset with the probability that the condition
does not hold.** -/
theorem unsetProbability_behavior {xs : List (Σ i, X i)} (hxs : E xs) :
    (G.behavior hG).unsetProbability xs = 1 - G.badProbability xs := by
  have hne : xs ≠ [] := fun he => hE'.1 (he ▸ hxs)
  have hstop : ∀ ys : List (Σ i, SystemAlgebra.withMBO Y i), ys.length = xs.length →
      ¬ (fixedQueries xs ys).Dom := by
    intro ys hl
    simp [fixedQueries, hl]
  -- Every transcript of the fixed queries is complete.
  have hdone : (G.behavior hG).unsetProbability xs =
      ((G.behavior hG).sLaw (fixedQueries xs) xs.length).mass
        (fun h => ¬ (fixedQueries xs (h.map Prod.snd)).Dom ∧ ∀ z ∈ h, z.2.2.2 = false) := by
    apply Distribution.mass_congr_of_support
    intro h hh
    have hgood : Good (fixedQueries xs) xs.length h := by
      by_contra hn
      apply Finsupp.mem_support_iff.mp hh
      rw [RandomSystem.sLaw_apply]
      exact if_neg hn
    refine ⟨fun hu => ⟨?_, hu⟩, fun hu => hu.2⟩
    rcases hgood.2 with hl | ⟨-, hd⟩
    · exact hstop _ (by rw [List.length_map, hl])
    · exact hd
  have hcompl := Distribution.mass_add_compl G (fun g => g.1.2.1 xs)
  rw [hG.2] at hcompl
  rw [hdone, RandomSystem.sLaw_completed_eq_mass (G.behavior hG) G hG.1
    (fun g => (DDG.withMBO g.1).1) (behavior_apply G hG), badProbability,
    show 1 - G.mass (fun g => g.1.2.1 xs) = G.mass (fun g => ¬ g.1.2.1 xs) by linarith]
  apply Distribution.mass_congr
  intro g
  obtain ⟨ys, tr⟩ := exists_transcript_withMBO hE' g hxs
  have hl := tr.length_eq
  constructor
  · rintro ⟨h, tr', -, hd, hu⟩
    obtain ⟨-, hy⟩ := tr.eq_of_stopped tr' (hstop ys hl.symm) hd
    have hys : ys = ((h.map Prod.snd).map forgetMBO).map (tagMBO false) := by
      rw [hy, List.map_map]
      conv_lhs => rw [← List.map_id (h.map Prod.snd)]
      apply List.map_congr_left
      intro y hy'
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy'
      exact eq_tagMBO_iff.mpr ⟨rfl, hu z hz⟩
    rw [hys] at tr
    exact ((DDG.replies_withMBO_unset_iff g.1 hne _).mp tr.replies).2
  · intro hb
    refine ⟨xs.zip ys, ?_, ?_, ?_, ?_⟩
    · rwa [List.map_fst_zip (by omega), List.map_snd_zip (by omega)]
    · simp
    · rw [List.map_snd_zip (by omega)]
      exact hstop ys hl.symm
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
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  · rw [List.map_nil, RandomSystem.unsetProbability_nil]
    linarith [(hG.1.mass_nonneg _).trans (hbad [] (Or.inl rfl))]
  · simp only [List.concat_eq_append] at hh ⊢
    have hadm : E ((p ++ [z]).map Prod.fst) := by
      by_contra hd
      exact hh (S.mass_eq_zero_of_not_admitted (by simpa using hd) z.2)
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
  intro h
  rcases List.eq_nil_or_concat h with rfl | ⟨p, z, rfl⟩
  · simp only [unsetMBOs, List.map_nil, RandomSystem.mass_nil, RandomSystem.unsetProbability_nil,
      mul_one]
  · simp only [List.concat_eq_append]
    have hfst : (unsetMBOs (p ++ [z])).map Prod.fst = (p ++ [z]).map Prod.fst := by
      simp [unsetMBOs, Function.comp_def]
    by_cases hadm : E ((p ++ [z]).map Prod.fst)
    · rw [unsetProbability_behavior hG hE' hadm, ← factor, behavior_apply, goodProbability]
      apply Distribution.mass_congr
      intro g
      have hsnd : (unsetMBOs (p ++ [z])).map Prod.snd =
          ((p ++ [z]).map Prod.snd).map (tagMBO false) := by
        simp [unsetMBOs, Function.comp_def]
      rw [hfst, hsnd]
      exact DDG.replies_withMBO_unset_iff g.1 (by simp) _
    · have hS : S (p ++ [z]) = 0 :=
        S.mass_eq_zero_of_not_admitted (by simpa using hadm) z.2
      have hG0 : G.behavior hG (unsetMBOs (p ++ [z])) = 0 := by
        rw [unsetMBOs, List.map_append, List.map_singleton]
        exact (G.behavior hG).mass_eq_zero_of_not_admitted
          (by simpa [Function.comp_def] using hadm) _
      rw [hS, hG0, mul_zero]

end PDG

end SystemAlgebra

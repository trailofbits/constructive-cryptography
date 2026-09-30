import RandomSystems.Distance.Transcript
import RandomSystems.Converter.ConverterAttachment

/-!
# Decision probabilities

A deterministic distinguisher is compatible with a domain when, on every resource on the
domain, it queries only admitted inputs and replies along every possible transcript; with
its finite bound it then produces a decision. Its decision probability on a resource is the
probability of the decision `1` in the completed transcript law. An environment followed by
an event test decides `1` with the probability of the event, so decision gaps and the
statistical distance of transcript laws bound one another. On a presentation of a resource
by deterministic resources, the decision probability is the probability of deciding `1` on
a sample.

## Main definitions

* `Domain.Compatible`: environments compatible with every resource on a domain
* `Domain.DecisionCompatible`: deterministic distinguishers compatible with a domain
* `RandomSystem.decisionProbability`: the probability of the decision `1`
* `RandomSystem.transcriptDistance`: the largest statistical distance of completed
  transcript laws under compatible query-bounded environments

## Main results

* `RandomSystem.decisionProbability_envProbe`: an environment followed by an event test
  decides `1` with the probability of the event
* `RandomSystem.decisionProbability_gap_le`: decision gaps are at most the transcript
  distance
* `RandomSystem.decisionProbability_of_presents`: the decision probability on a
  presentation
* `Domain.decisionCompatible_iff_deterministic`: compatibility is checked on the
  deterministic resources of the domain
-/

namespace SystemAlgebra

open Classical Probability

theorem Cons.queries_eq {A B : Type} {e : List B →. A} {h : List (A × B)}
    (hc : Cons e h) : h.map Prod.fst = qsOf e (h.map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    obtain ⟨hc, hz⟩ := cons_snoc.mp hc
    simp only [List.map_append, List.map_singleton]
    rw [qsOf_snoc hz, ih hc]

theorem Cons.fits {I : Type} {X Y : I → Type}
    {e : List (Σ i, Y i) →. Σ i, X i}
    {h : List ((Σ i, X i) × (Σ i, Y i))} (hc : Cons e h)
    (hl : ∀ z ∈ h, z.2.1 = z.1.1) : EFits e (h.map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => exact EFits.nil
  | append_singleton h z ih =>
    obtain ⟨hc, hz⟩ := cons_snoc.mp hc
    simp only [List.map_append, List.map_singleton]
    exact (ih hc (fun a ha => hl a (by simp [ha]))).snoc hz (hl z (by simp))

/-- A probe is defined along precisely the environment's valid reply paths. -/
theorem envProbe_reach {I : Type} {X Y : I → Type}
    {E : DDE (Σ i, X i) (Σ i, Y i)}
    (A : List (Σ i, X i) × List (Σ i, Y i) → Prop)
    {ys : List (Σ i, Y i)} (hv : EFits E.1 ys) : Reach (envProbe E A) (dHist ys) := by
  induction ys using List.reverseRecOn with
  | nil =>
    change Reach (envProbe E A) ([] ++ [⟨.start, ()⟩])
    apply reach_snoc_iff.mpr
    refine ⟨reach_nil _, ?_⟩
    rw [show ([] ++ [⟨.start, ()⟩] : List (Σ p, dIn Y p)) = dHist [] from rfl,
      envProbe_dHist EFits.nil]
    simp only [envReply]
    split_ifs <;> exact Part.some_dom _
  | append_singleton ys y ih =>
    have he : dHist (ys ++ [y]) = dHist ys ++ [envIn y] := by simp [dHist]
    rw [he, reach_snoc_iff]
    refine ⟨ih hv.of_snoc.1, ?_⟩
    rw [← he, envProbe_dHist hv]
    simp only [envReply]
    split_ifs <;> exact Part.some_dom _

theorem envOf_trim_envProbe {I : Type} {X Y : I → Type}
    {E : DDE (Σ i, X i) (Σ i, Y i)}
    {A : List (Σ i, X i) × List (Σ i, Y i) → Prop}
    {ys} (hv : EFits E.1 ys) : envOf (trim (envProbe E A)) ys = E.1 ys := by
  change ((trim (envProbe E A)) (dHist ys)).bind _ = _
  rw [trim, if_pos (envProbe_reach A hv)]
  exact envOf_envProbe hv

namespace RandomSystem

variable {I : Type} {X Y : I → Type} [Fintype (Σ i, X i)] [Fintype (Σ i, Y i)]
  {D : Domain (Σ i, X i) (Σ i, Y i)}

theorem RepliesAtQueriedInterface.history
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) D} (hr : R.RepliesAtQueriedInterface)
    {h} (hm : R h ≠ 0) : ∀ z ∈ h, z.2.1 = z.1.1 := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    have hp : R h ≠ 0 := fun hz => hm (R.mass_eq_zero_of_prefix ⟨[z], rfl⟩ hz)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact ih hp w hw
    · obtain rfl := List.mem_singleton.mp hw
      exact Classical.byContradiction (fun hn => hm (hr h w.1 w.2 hn))

/-- Canonicalizing the probe leaves exactly the original query strategy on
all possible responding-resource transcripts. -/
theorem cons_trim_envProbe_iff
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) D} (hr : R.RepliesAtQueriedInterface)
    (E : DDE (Σ i, X i) (Σ i, Y i))
    (A : List (Σ i, X i) × List (Σ i, Y i) → Prop)
    {h} (hm : R h ≠ 0) :
    Cons (envOf (trim (envProbe E A))) h ↔ Cons E.1 h := by
  induction h using List.reverseRecOn with
  | nil => exact iff_of_true cons_nil cons_nil
  | append_singleton h z ih =>
    have hp : R h ≠ 0 := fun hz => hm (R.mass_eq_zero_of_prefix ⟨[z], rfl⟩ hz)
    rw [cons_snoc, cons_snoc, ih hp]
    exact and_congr_right fun hc => by
      rw [envOf_trim_envProbe (hc.fits (hr.history hp))]

theorem sLaw_trim_envProbe
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) D) (hr : R.RepliesAtQueriedInterface)
    (E : DDE (Σ i, X i) (Σ i, Y i))
    (A : List (Σ i, X i) × List (Σ i, Y i) → Prop) (n : ℕ) :
    R.sLaw (envOf (trim (envProbe E A))) n = R.sLaw E.1 n := by
  ext h
  rw [sLaw_apply, sLaw_apply]
  by_cases hm : R h = 0
  · simp [hm]
  · have hc := cons_trim_envProbe_iff hr E A hm
    by_cases hh : Cons E.1 h
    · simp only [Good, hc, hh, true_and, Done,
        envOf_trim_envProbe (hh.fits (hr.history hm))]
    · simp only [Good, hc, hh, false_and, if_false]

/-- A completed transcript leaves a query-bounded environment without a next query. -/
theorem sLaw_complete {E : DDE (Σ i, X i) (Σ i, Y i)} {n : ℕ} (hn : QueryBounded n E)
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) D) {h} (hh : h ∈ (R.sLaw E.1 n).support) :
    ¬ (E.1 (h.map Prod.snd)).Dom := by
  have hp := Finsupp.mem_support_iff.mp hh
  have hg : Good E.1 n h := by
    by_contra hg
    exact hp (by simp [sLaw_apply, hg])
  rcases hg.2 with he | ⟨_, hs⟩
  · intro hd
    have hb := hn _ hd
    simp only [List.length_map, he] at hb
    exact Nat.lt_irrefl n hb
  · exact hs

end RandomSystem

variable {I : Type} [Fintype I] {X Y : I → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]

namespace Domain

/-- An environment is compatible with a domain when it is compatible with every resource on
the domain. -/
def Compatible (𝒟 : Domain (Σ i, X i) (Σ i, Y i)) (E : DDE (Σ i, X i) (Σ i, Y i)) : Prop :=
  ∀ R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟, R.RepliesAtQueriedInterface → R.Compatible E.1

/-- A deterministic distinguisher is compatible with a domain when, on every resource on the
domain, it queries only admitted inputs and replies along every possible transcript.
Together with its finite bound this gives an actual decision. -/
def DecisionCompatible (𝒟 : Domain (Σ i, X i) (Σ i, Y i)) (D : DDD I X Y) : Prop :=
  ∀ R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟, R.RepliesAtQueriedInterface →
    ∀ h, Cons (envOf (trim D)) h → R h ≠ 0 →
      ((trim D) (dHist (h.map Prod.snd))).Dom ∧
        ∀ x, x ∈ envOf (trim D) (h.map Prod.snd) → 𝒟 h x

variable {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

theorem DecisionCompatible.environment {D : DDD I X Y}
    (hc : 𝒟.DecisionCompatible D) (hD : IsDDD D) : 𝒟.Compatible (ddeOf hD) :=
  fun R hR h x ht hp hx => (hc R hR h ht hp).2 x hx

/-- Every completed possible transcript ends in a defined decision. -/
theorem DecisionCompatible.producesDecision {D : DDD I X Y}
    (hc : 𝒟.DecisionCompatible D) (hD : IsDDD D) {R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) {h}
    (hh : h ∈ (R.sLaw (ddeOf hD).1 hD.2.1.choose).support) :
    ∃ b : Bool, ⟨.dec, b⟩ ∈ (trim D) (dHist (h.map Prod.snd)) := by
  have hstop := R.sLaw_complete (ddeOf_bounded hD) hh
  have hp : R h ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hh (by simp [RandomSystem.sLaw_apply, hz])
  have ht : Cons (envOf (trim D)) h := by
    by_contra hn
    exact Finsupp.mem_support_iff.mp hh
      (by simp [RandomSystem.sLaw_apply, Good, ddeOf, hn])
  obtain ⟨o, ho⟩ := Part.dom_iff_mem.mp (hc R hR h ht hp).1
  rcases o with ⟨_ | _ | i, v⟩
  · exact v.elim
  · exact ⟨v, ho⟩
  · exact False.elim (hstop (Part.dom_iff_mem.mpr ⟨⟨i, v⟩, mem_envOf.mpr ho⟩))

/-- An environment followed by an event test is compatible with the domain of the
environment. -/
theorem envProbe_decisionCompatible {E : DDE (Σ i, X i) (Σ i, Y i)} (hc : 𝒟.Compatible E)
    (T : List (Σ i, X i) × List (Σ i, Y i) → Prop) :
    𝒟.DecisionCompatible (envProbe E T) := by
  intro R hR h ht hp
  have he := (RandomSystem.cons_trim_envProbe_iff hR E T hp).mp ht
  have hv := he.fits (hR.history hp)
  constructor
  · rw [trim, if_pos (envProbe_reach T hv), envProbe_dHist hv]
    simp only [envReply]
    split_ifs <;> exact Part.some_dom _
  · intro x hx
    rw [envOf_trim_envProbe hv] at hx
    exact hc R hR h x he hp hx

end Domain

namespace RandomSystem

variable {𝒟 : Domain (Σ i, X i) (Σ i, Y i)}

/-- The transcript distance of two random systems on a domain: the largest statistical
distance of their completed-transcript laws under a query-bounded environment compatible
with the domain. -/
noncomputable def transcriptDistance (R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) :
    ENNReal :=
  ⨆ (E : DDE (Σ i, X i) (Σ i, Y i)) (n : ℕ) (_ : QueryBounded n E) (_ : 𝒟.Compatible E),
    ENNReal.ofReal (statDist (R.sLaw E.1 n) (S.sLaw E.1 n))

theorem statDist_le_transcriptDistance {E : DDE (Σ i, X i) (Σ i, Y i)} {n : ℕ}
    (hn : QueryBounded n E) (hc : 𝒟.Compatible E) (R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) :
    ENNReal.ofReal (statDist (R.sLaw E.1 n) (S.sLaw E.1 n)) ≤ R.transcriptDistance S :=
  le_iSup_of_le E (le_iSup_of_le n (le_iSup_of_le hn (le_iSup_of_le hc le_rfl)))

theorem transcriptDistance_le_one {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface) :
    R.transcriptDistance S ≤ 1 := by
  refine iSup_le fun E => iSup_le fun n => iSup_le fun _ => iSup_le fun hc => ?_
  apply ENNReal.ofReal_le_one.mpr
  have hr := R.sLaw_isProbDist (hc R hR) n
  have hs := S.sLaw_isProbDist (hc S hS) n
  exact (statDist_le_weight hr.1 hs.1).trans_eq hr.2

/-- The decision probability of a deterministic distinguisher on a random system: the
probability of the decision `1` in the completed transcript law. On a compatible
distinguisher the decision exists (`Domain.DecisionCompatible.producesDecision`). -/
noncomputable def decisionProbability (D : DDD I X Y) (hD : IsDDD D)
    (R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟) : ℝ :=
  (R.sLaw (ddeOf hD).1 hD.2.1.choose).mass
    fun h => ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd))

/-- An environment followed by an event test decides `1` with exactly that event's
probability on its completed transcript. -/
theorem decisionProbability_envProbe {E : DDE (Σ i, X i) (Σ i, Y i)} {n : ℕ}
    (hn : QueryBounded n E) (T : List (Σ i, X i) × List (Σ i, Y i) → Prop)
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟} (hR : R.RepliesAtQueriedInterface) :
    R.decisionProbability (envProbe E T) (envProbe_isDDD hn) =
      (R.sLaw E.1 n).mass (fun h => T (h.map Prod.fst, h.map Prod.snd)) := by
  let hD := envProbe_isDDD (A := T) hn
  change (R.sLaw (envOf (trim (envProbe E T))) hD.2.1.choose).mass _ = _
  rw [R.sLaw_trim_envProbe hR E T]
  have hb : ∀ h, Cons E.1 h → R h ≠ 0 → (E.1 (h.map Prod.snd)).Dom →
      h.length < hD.2.1.choose := by
    intro h ht hp hd
    have hv := ht.fits (hR.history hp)
    have hd' : ((ddeOf hD).1 (h.map Prod.snd)).Dom := by
      change (envOf (trim (envProbe E T)) (h.map Prod.snd)).Dom
      rwa [envOf_trim_envProbe hv]
    simpa only [List.length_map] using ddeOf_bounded hD _ hd'
  rw [R.sLaw_eq_of_query_bounds hb (fun h _ _ hd => by
    simpa only [List.length_map] using hn _ hd)]
  apply Distribution.mass_congr_of_support
  intro h hh
  have hp : R h ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hh (by simp [sLaw_apply, hz])
  have ht : Cons E.1 h := by
    by_contra hn'
    exact Finsupp.mem_support_iff.mp hh (by simp [sLaw_apply, Good, hn'])
  have hv := ht.fits (hR.history hp)
  have hstop := R.sLaw_complete hn hh
  rw [trim, if_pos (envProbe_reach T hv), envProbe_dHist hv, envReply, dif_neg hstop]
  simp only [Part.mem_some_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  rw [← ht.queries_eq]
  simp

/-- Decision gaps of a compatible distinguisher are at most the transcript distance. -/
theorem decisionProbability_gap_le {D : DDD I X Y} (hD : IsDDD D)
    (hc : 𝒟.DecisionCompatible D) {R S : RandomSystem (Σ i, X i) (Σ i, Y i) 𝒟}
    (hR : R.RepliesAtQueriedInterface) (hS : S.RepliesAtQueriedInterface) :
    |R.decisionProbability D hD - S.decisionProbability D hD| ≤
      (R.transcriptDistance S).toReal := by
  apply (ENNReal.ofReal_le_iff_le_toReal
    (ne_top_of_le_ne_top ENNReal.one_ne_top (transcriptDistance_le_one hR hS))).mp
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (statDist_le_transcriptDistance (ddeOf_bounded hD) (hc.environment hD) R S)
  exact abs_mass_sub_le_statDist
    ⟨_, R.sLaw_isProbDist (hc.environment hD R hR) _⟩
    ⟨_, S.sLaw_isProbDist (hc.environment hD S hS) _⟩ _

variable {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

/-- On a presentation by deterministic resources, the decision probability is the
probability of deciding `1` on a sample. -/
theorem decisionProbability_of_presents (D : DDD I X Y) (hD : IsDDD D)
    (P : Distribution.ProbDist {s : InterfaceSystem I X Y //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h})
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = R h) :
    R.decisionProbability D hD = P.1.mass (fun s => decOut true ∈ close D s.1 [startIn]) := by
  have stop {ys} (hy : (⟨.dec, true⟩ : Σ p, dOut X p) ∈ (trim D) (dHist ys)) :
      ¬ (envOf (trim D) ys).Dom := by
    rw [envOf, Part.eq_some_iff.mpr hy]
    simp [query]
  change (R.sLaw (envOf (trim D)) hD.2.1.choose).mass _ = _
  calc
    _ = (R.sLaw (envOf (trim D)) hD.2.1.choose).mass
        (fun h => ¬ (envOf (trim D) (h.map Prod.snd)).Dom ∧
          ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd))) :=
      Distribution.mass_congr _ (fun h => ⟨fun hy => ⟨stop hy, hy⟩, And.right⟩)
    _ = P.1.mass (fun s => ∃ h : List ((Σ i, X i) × (Σ i, Y i)),
        Transcript s.1 (envOf (trim D)) (h.map Prod.fst) (h.map Prod.snd) ∧
        h.length ≤ hD.2.1.choose ∧ ¬ (envOf (trim D) (h.map Prod.snd)).Dom ∧
          ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd))) :=
      sLaw_completed_eq_mass _ P.1 P.2.1 (fun s => s.1) (fun h => (hP h).symm) _ _ _
    _ = _ := by
      apply Distribution.mass_congr
      intro s
      rw [← close_trim_start D s.1, close_decision]
      constructor
      · rintro ⟨h, ht, _, _, hd⟩
        exact ⟨_, _, ht, hd⟩
      · rintro ⟨xs, ys, ht, hd⟩
        have hf : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [ht.length_eq])
        have hs : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [ht.length_eq])
        refine ⟨xs.zip ys, ?_, ?_, ?_, ?_⟩
        · simpa only [hf, hs] using ht
        · have hn := finite_trim hD.2.1.choose_spec _ hd.1
          simp only [dHist, List.length_cons, List.length_map] at hn
          have hl : (xs.zip ys).length = ys.length := by
            rw [List.length_zip, ht.length_eq, Nat.min_self]
          omega
        · simpa only [hs] using stop hd
        · simpa only [hs] using hd

end RandomSystem

namespace Domain

variable {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

/-- Compatibility with a domain of input histories is checked on its deterministic
resources: the distinguisher decides on each of them. -/
theorem decisionCompatible_iff_deterministic
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) {D : DDD I X Y} (hD : IsDDD D) :
    (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D ↔
      ∀ s : InterfaceSystem I X Y, IsDDS s → SystemAlgebra.RepliesAtQueriedInterface s →
        (∀ h, (s h).Dom ↔ E h) → (close D s [startIn]).Dom := by
  constructor
  · intro hc s hs hr he
    rw [← close_trim_start D s]
    apply (close_dom_iff_compatible (finite_trim hD.2.1.choose_spec)).mpr
    intro xs ys ht
    let Q : Distribution.ProbDist {s : InterfaceSystem I X Y //
        IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h} :=
      ⟨Finsupp.single ⟨s, hs, hr, he⟩ 1, Distribution.isProbDist_single _⟩
    let R : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE) :=
      RandomSystem.ofPDS Q.1 Q.2 (fun s _ _ _ _ => s.2.2.2 _)
    have hfst : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [ht.length_eq])
    have hsnd : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [ht.length_eq])
    have hm : R (xs.zip ys) =
        if Replies s ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) then 1 else 0 := by
      simp [R, Q, RandomSystem.ofPDS, behaviorMass, Distribution.mass, Finsupp.sum]
    have hp : R (xs.zip ys) ≠ 0 := by
      rw [hm, hfst, hsnd, if_pos ht.replies]
      exact one_ne_zero
    have hh := hc R (RandomSystem.ofPDS_repliesAtQueriedInterface Q) (xs.zip ys)
      (transcript_cons ht) hp
    simp only [Domain.ofInputs_apply, hfst, hsnd] at hh
    exact ⟨hh.1, fun x hx => (he _).mpr (hh.2 x hx)⟩
  · intro hc R hR h ht hp
    obtain ⟨s, ⟨hs, hr, he⟩, hsrep⟩ := R.2.isSubprobabilistic.exists_replies (n := m)
      (fun h hl => R.mass_eq_zero_of_bound_lt hl)
      (fun s => IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ E h)
      (fun _ hg => RandomSystem.isResource_realization hE' hR hg) hp
    have hd := hc s hs hr he
    rw [← close_trim_start D s] at hd
    have hcompat := (close_dom_iff_compatible (finite_trim hD.2.1.choose_spec)).mp hd
    obtain ⟨hdec, hquery⟩ := hcompat _ _ (transcript_of_cons ht hsrep)
    exact ⟨hdec, fun x hx => (he _).mp (hquery x hx)⟩

end Domain

end SystemAlgebra

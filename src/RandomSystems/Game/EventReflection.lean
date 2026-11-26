module

public import RandomSystems.Game.MBOAttachment

/-!
# Success reflected into a game's hidden event

`PDCBehavior.ReflectsMBO` says that a successful outside transcript, on every positive
completed interaction, has the inside MBO set. Internal calls made before the final outside
reply are part of that interaction.

`attach_liftMBO_unset_eq_zero_of_reflectsMBO` rules out success with the MBO unset.
`event_mass_le_winProbability_of_unset_eq_zero` bounds any such event by winning, using
the unset subdistribution and its missing mass. `winProbability_eq_mass_of_unset` gives
equality when the unset law is exactly a reference law restricted to the complementary event.
Both contracts need only the caller's completed histories. For concrete converters,
`reflectsMBO_of_unset_eq_zero` reduces reflection to an inside unset-mass calculation;
`liftMBO_ofDDC_ne_zero_iff` exposes the compiled converter’s execution.

```text
caller ── queries ──▶ converter α ── internal calls ──▶ game G
       ◀─ replies ──             ◀─ replies, MBO ────
       success                         MBO = true
```
-/

@[expose] public section

namespace SystemAlgebra

open Probability

section Decision

-- `I` indexes ports; `X i` and `Y i` are their query and reply alphabets.
variable {I : Type} [Fintype I] {X Y : I → Type}
  [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
  -- `E` is the admitted query domain, bounded by `m` queries.
  {E : List (Σ i, X i) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}

/-- If the unset law is the reference law off `event`, winning is its event mass. -/
theorem RandomSystem.winProbability_eq_mass_of_unset
    -- `G` carries the monotone bit; `R` supplies the reference transcript probabilities.
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    {R : RandomSystem (Σ i, X i) (Σ i, Y i) (Domain.ofInputs E m hE)}
    -- `hG` and `hR` preserve the queried port; `hm` keeps a reached bit set.
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    (hR : R.RepliesAtQueriedInterface)
    -- `hD` certifies that `D` stops; `hdc` keeps its queries in the shared domain.
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D)
    -- `event` is scored only on completed histories; `unset` identifies their good mass.
    (event : List ((Σ i, X i) × Σ i, Y i) → Prop) [DecidablePred event]
    (unset : ∀ h, Good (ddeOf hD).1 hD.2.1.choose h →
      G (unsetMBOs h) = if event h then 0 else R h) :
    G.winProbability D hD = (R.sLaw (ddeOf hD).1 hD.2.1.choose).mass event := by
  classical
  let μ := R.sLaw (ddeOf hD).1 hD.2.1.choose
  obtain ⟨ν, law, winning⟩ := G.exists_unset_winProbability hG hm D hD hdc
  -- On completed histories the unset law is the reference law restricted to no event.
  have same : ν = μ.restrict (fun h => ¬ event h) := by
    ext h
    rw [law, Distribution.restrict_apply]
    dsimp only [μ]
    rw [RandomSystem.sLaw_apply]
    by_cases hg : Good (ddeOf hD).1 hD.2.1.choose h
    · rw [ite_eq_left hg, ite_eq_left hg, unset h hg]
      by_cases he : event h <;>
        simp only [he, not_true_eq_false, not_false_eq_true, ite_true, ite_false]
    · simp only [hg, ite_false, ite_self]
  -- Winning is one minus the complementary mass of a normalized transcript law.
  rw [winning, same, Distribution.weight_restrict]
  have complement := Distribution.mass_add_compl μ event
  rw [(R.sLaw_isProbDist (hdc.environment hD _ hR) _).2] at complement
  linarith

/-- A transcript event with zero unset mass has probability at most winning:
`Pr[event on G.visible] ≤ Win(D,G)`. -/
theorem RandomSystem.event_mass_le_winProbability_of_unset_eq_zero
    -- `G` answers at the queried port and carries a monotone hidden bit.
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    -- `D` is a stopping caller compatible with the game's domain.
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D)
    -- `event` reads the visible transcript; `hzero` excludes it while the MBO is unset.
    (event : List ((Σ i, X i) × Σ i, Y i) → Prop)
    (hzero : ∀ h, Good (ddeOf hD).1 hD.2.1.choose h →
      event h → G (unsetMBOs h) = 0) :
    (G.visible.sLaw (ddeOf hD).1 hD.2.1.choose).mass event ≤ G.winProbability D hD := by
  classical
  obtain ⟨ν, hν, hwin⟩ := G.exists_unset_winProbability hG hm D hD hdc
  let μ := G.visible.sLaw (ddeOf hD).1 hD.2.1.choose
  -- Unset mass is part of visible mass, transcript by transcript.
  have hle : ∀ h, ν h ≤ μ h := by
    intro h
    rw [hν, RandomSystem.sLaw_apply]
    split_ifs
    · simpa only [forgetMBOs_unsetMBOs, ← RandomSystem.visible_apply] using
        le_sumMBO G.mass_nonneg (unsetMBOs h)
    · exact le_rfl
  -- The common unset part gives no mass to the event.
  have hz : ν.mass event = 0 := by
    unfold Distribution.mass Finsupp.sum
    apply Finset.sum_eq_zero
    intro h _
    dsimp only
    split_ifs with ha
    · rw [hν]
      split_ifs with hg
      · exact hzero h hg ha
      · rfl
    · rfl
  -- All event mass lies in the missing mass, which is exactly winning.
  have hb := Distribution.mass_sub_mass_le_of_le
    (G.visible.sLaw_isProbDist (hdc.environment hD _ hG.visible) _).2
    hle (fun _ => le_rfl) event
  simpa only [hz, sub_zero, ← hwin] using hb

/-- If every accepting completed transcript has zero unset mass, acceptance is bounded by
winning: `Pr[accept on G.visible] ≤ Win(D,G)`. -/
theorem RandomSystem.decisionProbability_le_winProbability_of_unset_eq_zero
    -- `G` answers at the queried port and carries a monotone hidden bit.
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    -- `D` is a stopping caller compatible with the game's domain.
    (D : DDD I X Y) (hD : IsDDD D)
    (hdc : (Domain.ofInputs E m hE : Domain (Σ i, X i) (Σ i, Y i)).DecisionCompatible D)
    -- `hzero` excludes acceptance before the hidden event on completed caller transcripts.
    (hzero : ∀ h, Good (ddeOf hD).1 hD.2.1.choose h →
      ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd)) → G (unsetMBOs h) = 0) :
    G.visible.decisionProbability D hD ≤ G.winProbability D hD := by
  simpa only [RandomSystem.decisionProbability] using
    RandomSystem.event_mass_le_winProbability_of_unset_eq_zero hG hm D hD hdc
      (fun h => (⟨.dec, true⟩ : Σ p, dOut X p) ∈ (trim D) (dHist (h.map Prod.snd))) hzero

/-- A positive transcript whose all-unset version has zero mass has reached the hidden event. -/
lemma RandomSystem.MonotoneMBO.finalMBO_eq_true_of_unset_eq_zero
    {G : RandomSystem (Σ i, X i) (Σ i, withMBO Y i) (Domain.ofInputs E m hE)}
    (hm : G.MonotoneMBO) {h} (hpos : G h ≠ 0)
    (hzero : G (unsetMBOs (forgetMBOs h)) = 0) : finalMBO h = true := by
  apply (finalMBO_eq_true_iff (hm h hpos)).mpr
  intro hall
  apply hpos
  have he : unsetMBOs (forgetMBOs h) = h :=
    ((eq_unsetMBOs_iff h (forgetMBOs h)).mpr ⟨rfl, hall⟩).symm
  rwa [he] at hzero

end Decision

section Attachment

-- `O` indexes outside ports with alphabets `U,V`; `J` indexes inside ports with `X,Y`.
variable {O J : Type} [Fintype O] [Fintype J] {U V : O → Type} {X Y : J → Type}
  [∀ o, Fintype (U o)] [∀ o, Fintype (V o)]
  [∀ j, Fintype (X j)] [∀ j, Fintype (Y j)]
  -- `E,F` are the inside and outside query domains, bounded by `m,n` respectively.
  {E : List (Σ j, X j) → Prop} {m : ℕ} {hE : ∀ h, E h → h.length ≤ m}
  {F : List (Σ o, U o) → Prop} {n : ℕ} {hF : ∀ h, F h → h.length ≤ n}

/-- Every positive completed interaction with outside `success` has its inside MBO set.
The lift records the hidden tags while `α` still sees only ordinary inside replies. -/
def PDCBehavior.ReflectsMBO
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    -- `success h` is the event on the visible outside transcript `h`.
    (success : List ((Σ o, U o) × Σ o, V o) → Prop) : Prop :=
  ∀ (h : List ((Σ o, U o) × Σ o, V o))
    -- `t` records all converter/game exchanges, including the final verification calls.
    (t : List (Two (Σ l, twoFam U (withMBO Y) l) (Σ j, X j) ×
      Two (Σ l, twoFam (withMBO V) X l) (Σ j, withMBO Y j))),
    FollowsStrategy (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) t →
    ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst) (t.map Prod.snd)).Dom →
    -- Positive joint mass enforces both components' domains and consistent wiring.
    RandomSystem.parallel (PDCBehavior.liftMBO α).1 G t ≠ 0 →
    (exposedReplies (resourceRoute (U := U)) (t.map Prod.snd)).map forgetMBO =
      h.map Prod.snd →
    success h → finalMBO (RandomSystem.parallelRight t) = true

/-- To establish reflection, exclude the all-unset version of each successful inside trace.
`hzero` receives positive masses for both component traces, with consistent wiring. -/
lemma PDCBehavior.reflectsMBO_of_unset_eq_zero
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hm : G.MonotoneMBO)
    {success : List ((Σ o, U o) × Σ o, V o) → Prop}
    -- `h` is the outside transcript; `t` contains the full converter/game interaction.
    (hzero : ∀ h t,
      FollowsStrategy (connectionQueries resourceRoute resourceInput (h.map Prod.fst)) t →
      ¬ (connectionQueries resourceRoute resourceInput (h.map Prod.fst)
        (t.map Prod.snd)).Dom →
      RandomSystem.parallelConsistent t →
      (PDCBehavior.liftMBO α).1 (RandomSystem.parallelLeft t) ≠ 0 →
      G (RandomSystem.parallelRight t) ≠ 0 →
      (exposedReplies (resourceRoute (U := U)) (t.map Prod.snd)).map forgetMBO =
        h.map Prod.snd →
      success h → G (unsetMBOs (forgetMBOs (RandomSystem.parallelRight t))) = 0) :
    α.ReflectsMBO G success := by
  intro h t hc hstop hpos hexp hs
  rw [RandomSystem.parallel_mass] at hpos
  split_ifs at hpos with hpar
  · obtain ⟨hα, hG⟩ := mul_ne_zero_iff.mp hpos
    exact hm.finalMBO_eq_true_of_unset_eq_zero hG (hzero h t hc hstop hpar hα hG hexp hs)
  · exact (hpos rfl).elim

open Classical in
/-- The lift of a deterministic converter has positive mass exactly on its tagged executions.
For compiled programs, use `TypedConverter.ofProgram_eq_ofDDC` first. -/
lemma PDCBehavior.liftMBO_ofDDC_ne_zero_iff
    -- `a` is the DDC certified by `ha`; `t` records its queries and tagged replies.
    (a : InsideOutsideSystem O J U V X Y) {b : ℕ} (ha : IsDDCFrom E F b a) (t) :
    (PDCBehavior.liftMBO (PDCBehavior.ofDDC a ha :
      PDCBehavior O J U V X Y E m hE F n hF)).1 t ≠ 0 ↔
      Replies (SystemAlgebra.liftMBO a) (t.map Prod.fst) (t.map Prod.snd) := by
  rw [PDCBehavior.liftMBO_apply, PDCBehavior.ofDDC_apply, replies_liftMBO_iff]
  split_ifs <;> simp_all

/-- Reflection excludes successful outside transcripts with every MBO unset. -/
lemma PDCBehavior.attach_liftMBO_unset_eq_zero_of_reflectsMBO
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    {success : List ((Σ o, U o) × Σ o, V o) → Prop}
    (hreflect : α.ReflectsMBO G success) {h} (hs : success h) :
    PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG (unsetMBOs h) = 0 := by
  by_contra hn
  -- A positive attached transcript has a positive completed joint interaction.
  obtain ⟨t, hc, _, hstop, hp, hexp⟩ :=
    RandomSystem.exists_completed_of_connectionLaw_ne_zero _ _ _ _ _ hn
  have hraw := hp
  rw [RandomSystem.parallel_mass] at hp
  split_ifs at hp with hpar
  · obtain ⟨hα, hinside⟩ := mul_ne_zero_iff.mp hp
    have htag : TaggedMBO (RandomSystem.parallelLeft t) := by
      by_contra ht
      exact hα (by rw [PDCBehavior.liftMBO_apply, ite_eq_right ht])
    -- Completion and the outside false tags force the entire inside MBO sequence to be false.
    have hu := parallelRight_eq_unsetMBOs_of_completed hc hpar hstop htag
      (fun v hv => by
        rw [hexp] at hv
        simp only [unsetMBOs, List.map_map, Function.comp_def, List.mem_map] at hv
        obtain ⟨z, _, rfl⟩ := hv
        rfl) (hm _ hinside)
    have hb := hreflect h t (by simpa only [unsetMBOs, List.map_map, Function.comp_def] using hc)
      (by simpa only [unsetMBOs, List.map_map, Function.comp_def] using hstop) hraw
      (by rw [hexp]; simp only [unsetMBOs, List.map_map, Function.comp_def, tagMBO,
        forgetMBO]) hs
    -- Reflection requires a true final bit on that same interaction, a contradiction.
    rw [hu] at hb
    have hall : ∀ z ∈ unsetMBOs (forgetMBOs (RandomSystem.parallelRight t)),
        z.2.2.2 = false := by
      intro z hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      rfl
    have hbits := hm _ hinside
    rw [hu] at hbits
    exact (finalMBO_eq_true_iff hbits).mp hb hall
  · exact hp rfl

/-- Under the completed-interaction contract, outside acceptance is bounded by winning
against the attached game. Absorption identifies this with winning against `G`. -/
theorem PDCBehavior.decisionProbability_attach_le_winProbability
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    -- `D` is the outside caller; its accepting completed interactions must set the inside MBO.
    (D : DDD O U V) (hD : IsDDD D)
    (hdc : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).DecisionCompatible D)
    (hreflect : α.ReflectsMBO G
      (fun h => Good (ddeOf hD).1 hD.2.1.choose h ∧
        ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd)))) :
    (PDCBehavior.attach hE' hF' α G.visible hG.visible).decisionProbability D hD ≤
      (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG).winProbability D hD := by
  rw [← RandomSystem.visible_attach_liftMBO hE' hF' α G hG]
  exact RandomSystem.decisionProbability_le_winProbability_of_unset_eq_zero
    (PDCBehavior.attach_repliesAtQueriedInterface hE' hF' _ G hG)
    (hm.attach_liftMBO hE' hF' α hG) D hD hdc
    (fun _ hg ha => α.attach_liftMBO_unset_eq_zero_of_reflectsMBO
      hE' hF' G hG hm hreflect ⟨hg, ha⟩)

/-- Every accepting legal completed run of randomized caller `P` sets the inside MBO.
The caller is sampled once; only callers in its support and transcripts following them count. -/
def Domain.Distinguisher.ReflectsMBO
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE)) : Prop :=
  ∀ D ∈ P.1.support, α.ReflectsMBO G
    (fun h => Good (ddeOf D.2.1).1 D.2.1.2.1.choose h ∧
      ⟨.dec, true⟩ ∈ (trim D.1) (dHist (h.map Prod.snd)))

/-- The same bound holds for randomized callers: average the completed-interaction contract
only over deterministic callers in `P`'s support. -/
theorem PDCBehavior.probability_attach_le_winProbability
    (hE' : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hF' : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (α : PDCBehavior O J U V X Y E m hE F n hF)
    (G : RandomSystem (Σ j, X j) (Σ j, withMBO Y j) (Domain.ofInputs E m hE))
    (hG : G.RepliesAtQueriedInterface) (hm : G.MonotoneMBO)
    -- `P` chooses a compatible stopping caller once, retaining its randomness throughout.
    (P : (Domain.ofInputs F n hF : Domain (Σ o, U o) (Σ o, V o)).Distinguisher)
    (hreflect : P.ReflectsMBO α G) :
    P.probability (PDCBehavior.attach hE' hF' α G.visible hG.visible) ≤
      P.winProbability (PDCBehavior.attach hE' hF' (PDCBehavior.liftMBO α) G hG) := by
  simp only [Domain.Distinguisher.probability, Domain.Distinguisher.winProbability, Finsupp.sum]
  exact Finset.sum_le_sum fun D hD => mul_le_mul_of_nonneg_left
    (α.decisionProbability_attach_le_winProbability hE' hF' G hG hm
      D.1 D.2.1 D.2.2 (hreflect D hD)) (P.2.1 D)

end Attachment

end SystemAlgebra

module

public import RandomSystems.Game.MBOAttachment

/-!
# Success reflected into a game's hidden event

`PDCBehavior.ReflectsMBO` says that a successful outside transcript, on every positive
completed interaction, has the inside MBO set. Internal calls made before the final outside
reply are part of that interaction.

`attach_liftMBO_unset_eq_zero_of_reflectsMBO` rules out success with the MBO unset.
`decisionProbability_le_winProbability_of_unset_eq_zero` then bounds success by winning,
using the existing unset subdistribution and its missing mass.

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
  -- The common unset part gives no mass to acceptance.
  have hz : ν.mass (fun h => ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd))) = 0 := by
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
  -- All acceptance lies in the missing mass, which is exactly winning.
  have hb := Distribution.mass_sub_mass_le_of_le
    (G.visible.sLaw_isProbDist (hdc.environment hD _ hG.visible) _).2
    hle (fun _ => le_rfl) (fun h => ⟨.dec, true⟩ ∈ (trim D) (dHist (h.map Prod.snd)))
  simpa only [RandomSystem.decisionProbability, hz, sub_zero, ← hwin] using hb

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

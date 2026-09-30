import RandomSystems.Cumulative.CumulativeObservation

/-!
# Mixtures and parallel composition

A finite mixture of random systems on one domain is a random system. Two random
systems run independently in parallel give a random system on the combined
alphabets, with product probabilities on the two component transcripts.

## Main definitions

* `RandomSystem.mix P R`: the mixture of the `R i` with `i ∼ P`
* `Domain.parallel D D'`: the domain of a parallel composition
* `RandomSystem.parallel R S`: independent parallel composition
* `PDS.parallel P Q`: independent sampling followed by deterministic parallel
  composition

## Main results

* `replies_pair_iff`: the transcripts of a deterministic pair are the interleaved
  component transcripts
* `parallel_mass_of_presentations`, `PDS.parallel_mass`: parallel composition of
  presentations presents the parallel composition
* `parallel_mix_right`: parallel composition distributes over mixtures
-/

namespace SystemAlgebra.RandomSystem

open Classical Probability

variable {A B C E ι : Type}

/-- Two-component alphabets of finite types are finite. -/
instance instFintypeOptF {Z W : Type} [Fintype Z] [Fintype W] (o : Option Unit) :
    Fintype (optF Z (fun _ : Unit => W) o) :=
  match o with
  | none => (inferInstance : Fintype Z)
  | some () => (inferInstance : Fintype W)

section Mix

variable [Fintype A] [Fintype B] {D : Domain A B}

/-- A finite probabilistic choice among behaviors on the same admitted domain. -/
noncomputable def mix (P : Distribution.ProbDist ι) (R : ι → RandomSystem A B D) :
    RandomSystem A B D :=
  ⟨fun h => ∑ i ∈ P.1.support, P.1 i * R i h, by
    refine ⟨?_, ?_, fun h x => ?_⟩
    · simpa only [(R _).mass_nil, mul_one, Distribution.weight, Finsupp.sum] using P.2.2
    · intro h
      exact Finset.sum_nonneg fun i _ => mul_nonneg (P.2.1 i) ((R i).mass_nonneg h)
    · refine ⟨∑ i ∈ P.1.support, P.1 i • (R i).extensionLaw h x, ?_, ?_⟩
      · intro y
        simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
          extensionLaw_apply]
      · rw [Distribution.weight_finset_sum]
        have hw (i : ι) : (P.1 i • (R i).extensionLaw h x).weight =
            P.1 i * ((R i).extensionLaw h x).weight := by
          unfold Distribution.weight
          rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
        simp only [hw, extensionLaw_weight]
        by_cases hd : D h x <;> simp only [hd, if_true, if_false, mul_zero, Finset.sum_const_zero]⟩

theorem mix_mass (P : Distribution.ProbDist ι) (R : ι → RandomSystem A B D)
    (h : List (A × B)) : mix P R h = ∑ i ∈ P.1.support, P.1 i * R i h := rfl

end Mix

/-- Project the exchanges belonging to the left component. -/
def parallelLeft (h : List ((Two A C) × (Two B E))) : List (A × B) :=
  h.filterMap fun z => match z with
    | (⟨none, x⟩, ⟨none, y⟩) => some (x, y)
    | _ => none

/-- Project the exchanges belonging to the right component. -/
def parallelRight (h : List ((Two A C) × (Two B E))) : List (C × E) :=
  h.filterMap fun z => match z with
    | (⟨some (), x⟩, ⟨some (), y⟩) => some (x, y)
    | _ => none

/-- An exchange is with one of the two independent components. -/
def parallelConsistent (h : List ((Two A C) × (Two B E))) : Prop :=
  ∀ z ∈ h, z.1.1 = z.2.1

theorem parallelConsistent_snoc {h : List ((Two A C) × (Two B E))} {z} :
    parallelConsistent (h ++ [z]) ↔ parallelConsistent h ∧ z.1.1 = z.2.1 := by
  simp [parallelConsistent, or_imp, forall_and]

/-- Parallel composition queries the selected component at its own history. -/
def parallelAdmits (D : List (A × B) → A → Prop) (D' : List (C × E) → C → Prop)
    (h : List ((Two A C) × (Two B E))) : Two A C → Prop
  | ⟨none, x⟩ => D (parallelLeft h) x
  | ⟨some (), x⟩ => D' (parallelRight h) x

/-- Consistent transcripts split into their two component transcripts. -/
theorem length_of_parallelConsistent {h : List ((Two A C) × (Two B E))}
    (hh : parallelConsistent h) :
    h.length = (parallelLeft h).length + (parallelRight h).length := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z (by simp)
    have ht : parallelConsistent h := fun a ha => hh a (by simp [ha])
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩ <;>
      simp_all [parallelLeft, parallelRight] <;> omega

/-- The domain of a parallel composition: a consistent transcript, the queried
component admitting the query, and the other component within its bound. -/
def _root_.SystemAlgebra.Domain.parallel (D : Domain A B) (D' : Domain C E) :
    Domain (Two A C) (Two B E) where
  admits h x := parallelConsistent h ∧ match x with
    | ⟨none, x⟩ => (parallelRight h).length ≤ D'.bound ∧ D (parallelLeft h) x
    | ⟨some (), x⟩ => (parallelLeft h).length ≤ D.bound ∧ D' (parallelRight h) x
  bound := D.bound + D'.bound
  length_lt h x hx := by
    rw [length_of_parallelConsistent hx.1]
    rcases x with ⟨_ | ⟨⟩, x⟩
    · have := D.length_lt _ _ hx.2.2
      have := hx.2.1
      omega
    · have := D'.length_lt _ _ hx.2.2
      have := hx.2.1
      omega

section Parallel

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] {D : Domain A B} {D' : Domain C E}

/-- Independent parallel composition, with its combined input/output alphabets. -/
noncomputable def parallel (R : RandomSystem A B D) (S : RandomSystem C E D') :
    RandomSystem (Two A C) (Two B E) (D.parallel D') :=
  ⟨fun h => if parallelConsistent h then R (parallelLeft h) * S (parallelRight h) else 0, by
    refine ⟨by simp [parallelConsistent, parallelLeft, parallelRight, R.mass_nil, S.mass_nil],
      ?_, fun h x => ?_⟩
    · intro h
      dsimp only
      split_ifs
      · exact mul_nonneg (R.mass_nonneg _) (S.mass_nonneg _)
      · exact le_rfl
    · by_cases hh : parallelConsistent h
      swap
      · refine ⟨0, fun y => ?_, ?_⟩
        · simp [parallelConsistent_snoc, hh]
        · simp [hh, Distribution.weight]
      rcases x with ⟨_ | ⟨⟨⟩⟩, x⟩
      · refine ⟨S (parallelRight h) • Distribution.fTransform (fun y : B => (⟨none, y⟩ : Two B E)) (R.extensionLaw (parallelLeft h) x),
          ?_, ?_⟩
        · intro y
          rcases y with ⟨_ | ⟨⟩, y⟩
          ·
            rw [Finsupp.smul_apply, smul_eq_mul,
              Distribution.fTransform_injective_apply _ _ (by intro a b h; simpa using h),
              extensionLaw_apply]
            simp [parallelConsistent_snoc, hh, parallelLeft, parallelRight,
              List.filterMap_append, mul_comm]
          ·
            rw [Finsupp.smul_apply, smul_eq_mul]
            have hz : Distribution.fTransform (fun y : B => (⟨none, y⟩ : Two B E)) (R.extensionLaw (parallelLeft h) x)
                (⟨some (), y⟩ : Two B E) = 0 :=
              Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨b, hb⟩; cases hb)
            simp [hz, parallelConsistent_snoc]
        · unfold Distribution.weight at ⊢
          rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
          change S (parallelRight h) *
            (Distribution.fTransform (fun y : B => (⟨none, y⟩ : Two B E)) (R.extensionLaw (parallelLeft h) x)).weight = _
          rw [Distribution.weight_fTransform, extensionLaw_weight]
          by_cases hb : (parallelRight h).length ≤ D'.bound
          · have hadm : (D.parallel D').admits h ⟨none, x⟩ ↔ D (parallelLeft h) x :=
              ⟨fun h' => h'.2.2, fun h' => ⟨hh, hb, h'⟩⟩
            by_cases hd : D (parallelLeft h) x
            · rw [if_pos hd, if_pos (hadm.mpr hd)]
              simp [hh, mul_comm]
            · rw [if_neg hd, if_neg (fun h' => hd (hadm.mp h'))]
              simp
          · rw [S.mass_eq_zero_of_bound_lt (not_le.mp hb), zero_mul,
              if_neg (fun h' => hb h'.2.1)]
      · refine ⟨R (parallelLeft h) • Distribution.fTransform (fun y : E => (⟨some (), y⟩ : Two B E)) (S.extensionLaw (parallelRight h) x),
          ?_, ?_⟩
        · intro y
          rcases y with ⟨_ | ⟨⟩, y⟩
          ·
            rw [Finsupp.smul_apply, smul_eq_mul]
            have hz : Distribution.fTransform (fun y : E => (⟨some (), y⟩ : Two B E)) (S.extensionLaw (parallelRight h) x)
                (⟨none, y⟩ : Two B E) = 0 :=
              Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨b, hb⟩; cases hb)
            simp [hz, parallelConsistent_snoc]
          ·
            rw [Finsupp.smul_apply, smul_eq_mul,
              Distribution.fTransform_injective_apply _ _ (by intro a b h; simpa using h),
              extensionLaw_apply]
            simp [parallelConsistent_snoc, hh, parallelLeft, parallelRight, List.filterMap_append]
        · unfold Distribution.weight at ⊢
          rw [Finsupp.sum_smul_index (fun _ => rfl), ← Finsupp.mul_sum]
          change R (parallelLeft h) *
            (Distribution.fTransform (fun y : E => (⟨some (), y⟩ : Two B E)) (S.extensionLaw (parallelRight h) x)).weight = _
          rw [Distribution.weight_fTransform, extensionLaw_weight]
          by_cases hb : (parallelLeft h).length ≤ D.bound
          · have hadm : (D.parallel D').admits h ⟨some (), x⟩ ↔ D' (parallelRight h) x :=
              ⟨fun h' => h'.2.2, fun h' => ⟨hh, hb, h'⟩⟩
            by_cases hd : D' (parallelRight h) x
            · rw [if_pos hd, if_pos (hadm.mpr hd)]
              simp [hh]
            · rw [if_neg hd, if_neg (fun h' => hd (hadm.mp h'))]
              simp
          · rw [R.mass_eq_zero_of_bound_lt (not_le.mp hb), zero_mul,
              if_neg (fun h' => hb h'.2.1)]⟩

theorem parallel_mass (R : RandomSystem A B D) (S : RandomSystem C E D')
    (h : List ((Two A C) × (Two B E))) :
    parallel R S h =
      if parallelConsistent h then R (parallelLeft h) * S (parallelRight h) else 0 := rfl

theorem parallel_mix_right (R : RandomSystem A B D) (P : Distribution.ProbDist ι)
    (S : ι → RandomSystem C E D') :
    parallel R (mix P S) = mix P (fun i => parallel R (S i)) := by
  apply RandomSystem.ext
  intro h
  simp only [parallel_mass, mix_mass]
  by_cases hc : parallelConsistent h
  · simp only [if_pos hc, Finset.mul_sum, mul_left_comm]
  · simp only [if_neg hc, mul_zero, Finset.sum_const_zero]

end Parallel

theorem parallelLeft_queries {h : List ((Two A C) × (Two B E))}
    (hh : parallelConsistent h) :
    (parallelLeft h).map Prod.fst = restrict none (h.map Prod.fst) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z (by simp)
    have ht : parallelConsistent h := fun a ha => hh a (by simp [ha])
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩ <;>
      simp_all [parallelLeft]

theorem parallelRight_queries {h : List ((Two A C) × (Two B E))}
    (hh : parallelConsistent h) :
    (parallelRight h).map Prod.fst = restrict (some ()) (h.map Prod.fst) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z (by simp)
    have ht : parallelConsistent h := fun a ha => hh a (by simp [ha])
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩ <;>
      simp_all [parallelRight]

/-- The existing deterministic parallel operation produces precisely the two
component transcripts, interleaved in the supplied order. No totality is needed. -/
theorem replies_pair_iff (s : System A B) (t : System C E)
    (h : List ((Two A C) × (Two B E))) :
    Replies (pair s t) (h.map Prod.fst) (h.map Prod.snd) ↔
      parallelConsistent h ∧
        Replies s ((parallelLeft h).map Prod.fst) ((parallelLeft h).map Prod.snd) ∧
        Replies t ((parallelRight h).map Prod.fst) ((parallelRight h).map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => simp [parallelConsistent, parallelLeft, parallelRight]
  | append_singleton h z ih =>
    simp only [List.map_append, List.map_cons, List.map_nil, replies_snoc, ih,
      parallelConsistent_snoc]
    by_cases hh : parallelConsistent h
    swap
    · simp [hh]
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩
    · rw [pair_left, ← parallelLeft_queries hh]
      simp only [hh, true_and, and_true, parallelLeft, parallelRight,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.map_append,
        List.map_cons, List.map_nil, List.append_nil, replies_snoc]
      simp only [Part.eq_some_iff, Part.mem_map_iff]
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, exists_eq_right]
      tauto
    · rw [pair_left]
      simp [Part.eq_some_iff, Part.mem_map_iff]
    · rw [pair_right]
      simp [Part.eq_some_iff, Part.mem_map_iff]
    · rw [pair_right, ← parallelRight_queries hh]
      simp only [hh, true_and, and_true, parallelLeft, parallelRight,
        List.filterMap_append, List.filterMap_cons, List.filterMap_nil, List.map_append,
        List.map_cons, List.map_nil, List.append_nil, replies_snoc]
      simp only [Part.eq_some_iff, Part.mem_map_iff]
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, exists_eq_right]
      tauto

section Presentations

variable [Fintype A] [Fintype B] [Fintype C] [Fintype E] {D : Domain A B} {D' : Domain C E}

/-- Product cumulative behavior preserves any finite presentations of its two
components, including presentations whose unreachable histories differ. -/
theorem parallel_mass_of_presentations {ι κ : Type}
    (R : RandomSystem A B D) (S : RandomSystem C E D')
    (P : Distribution ι) (Q : Distribution κ)
    (s : ι → System A B) (t : κ → System C E)
    (hR : ∀ h, R h = P.mass (fun i => Replies (s i) (h.map Prod.fst) (h.map Prod.snd)))
    (hS : ∀ h, S h = Q.mass (fun i => Replies (t i) (h.map Prod.fst) (h.map Prod.snd)))
    (h : List ((Two A C) × (Two B E))) :
    parallel R S h = (Distribution.prod P Q).mass (fun st =>
      Replies (pair (s st.1) (t st.2)) (h.map Prod.fst) (h.map Prod.snd)) := by
  rw [parallel_mass, Distribution.mass_congr (Distribution.prod P Q)
    (fun st => replies_pair_iff (s st.1) (t st.2) h)]
  by_cases hh : parallelConsistent h
  · simp only [hh, if_true, true_and, hR, hS]
    exact (Distribution.mass_prod_and P Q _ _).symm
  · simp only [hh, if_false, false_and]
    exact (Distribution.mass_eq_zero_of_forall_not _ (fun _ hf => hf)).symm

/-- Parallel cumulative behavior agrees with independent sampling followed by
the existing deterministic system operation. -/
theorem parallel_ofPDS_mass
    {p : System A B → Prop} {q : System C E → Prop}
    (P : Distribution {s : System A B // p s}) (Q : Distribution {s : System C E // q s})
    (hP : P.isProbDist) (hQ : Q.isProbDist)
    (hD : ∀ s ∈ P.support, ∀ h x, Replies s.1 (h.map Prod.fst) (h.map Prod.snd) →
      ((s.1 (h.map Prod.fst ++ [x])).Dom ↔ D h x))
    (hD' : ∀ t ∈ Q.support, ∀ h x, Replies t.1 (h.map Prod.fst) (h.map Prod.snd) →
      ((t.1 (h.map Prod.fst ++ [x])).Dom ↔ D' h x))
    (h : List ((Two A C) × (Two B E))) :
    parallel (ofPDS P hP hD) (ofPDS Q hQ hD') h =
      (Distribution.prod P Q).mass (fun st =>
        Replies (pair st.1.1 st.2.1) (h.map Prod.fst) (h.map Prod.snd)) := by
  exact parallel_mass_of_presentations _ _ P Q Subtype.val Subtype.val
    (fun _ => rfl) (fun _ => rfl) h

end Presentations

end SystemAlgebra.RandomSystem

namespace SystemAlgebra.PDS

open Classical Probability

variable {A B C E : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype E]
  {D : Domain A B} {D' : Domain C E}

omit [Fintype A] [Fintype B] [Fintype C] [Fintype E] in
/-- The reachable part of a pair of samples has the parallel domain. -/
theorem hasDomain_trim_pair {s : System A B} {t : System C E} (hs : HasDomain D s)
    (ht : HasDomain D' t) : HasDomain (D.parallel D') (trim (pair s t)) := by
  intro h x hr
  rw [replies_trim_iff, RandomSystem.replies_pair_iff] at hr
  obtain ⟨hh, hl, hr'⟩ := hr
  have hreach : Reach (pair s t) (h.map Prod.fst) := by
    have := (replies_trim_iff (pair s t) _ _).mpr
      ((RandomSystem.replies_pair_iff s t h).mpr ⟨hh, hl, hr'⟩)
    exact ((replies_trim_iff _ _ _).mp this).reach
  have hdom : ((trim (pair s t)) (h.map Prod.fst ++ [x])).Dom ↔
      ((pair s t) (h.map Prod.fst ++ [x])).Dom := by
    unfold trim
    rw [reach_snoc_iff]
    constructor
    · intro hd
      split_ifs at hd with hp
      · exact hd
      · exact hd.elim
    · intro hd
      rw [if_pos ⟨hreach, hd⟩]
      exact hd
  rw [hdom]
  change _ ↔ RandomSystem.parallelConsistent h ∧ _
  rcases x with ⟨_ | ⟨⟨⟩⟩, x⟩
  · rw [pair_left, ← RandomSystem.parallelLeft_queries hh]
    simp only [Part.map_Dom]
    rw [hs _ x hl]
    exact ⟨fun hd => ⟨hh, ht.length_le hr', hd⟩, fun hd => hd.2.2⟩
  · rw [pair_right, ← RandomSystem.parallelRight_queries hh]
    simp only [Part.map_Dom]
    rw [ht _ x hr']
    exact ⟨fun hd => ⟨hh, hs.length_le hl, hd⟩, fun hd => hd.2.2⟩

/-- Independent parallel sampling, using the existing system operation and its
reachable part. Trimming preserves every completed transcript. -/
noncomputable def parallel (P : PDS A B D) (Q : PDS C E D') : PDS (Two A C) (Two B E) (D.parallel D') :=
  Distribution.fTransform (fun st : {s : System A B // IsDDS s ∧ HasDomain D s} ×
      {s : System C E // IsDDS s ∧ HasDomain D' s} =>
    ⟨trim (pair st.1.1 st.2.1), SilentAtEmpty.isDDS_trim (parAll_silentAtEmpty _),
      hasDomain_trim_pair st.1.2.2 st.2.2.2⟩)
      (Distribution.prod P Q)

theorem parallel_isProbDist {P : PDS A B D} {Q : PDS C E D'}
    (hP : P.isProbDist) (hQ : Q.isProbDist) : (parallel P Q).isProbDist :=
  Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist P Q hP hQ)

theorem parallel_mass (P : PDS A B D) (Q : PDS C E D')
    (h : List ((Two A C) × (Two B E))) :
    behaviorMass (parallel P Q) (h.map Prod.fst) (h.map Prod.snd) =
      if RandomSystem.parallelConsistent h then
        behaviorMass P ((RandomSystem.parallelLeft h).map Prod.fst) ((RandomSystem.parallelLeft h).map Prod.snd) *
        behaviorMass Q ((RandomSystem.parallelRight h).map Prod.fst) ((RandomSystem.parallelRight h).map Prod.snd)
      else 0 := by
  rw [behaviorMass, parallel, Distribution.mass_fTransform]
  simp only [replies_trim_iff]
  rw [Distribution.mass_congr (Distribution.prod P Q)
    (fun st => RandomSystem.replies_pair_iff st.1.1 st.2.1 h)]
  by_cases hh : RandomSystem.parallelConsistent h
  · simp only [hh, if_true, true_and]
    exact Distribution.mass_prod_and P Q
      (fun s => Replies s.1 ((RandomSystem.parallelLeft h).map Prod.fst)
        ((RandomSystem.parallelLeft h).map Prod.snd))
      (fun t => Replies t.1 ((RandomSystem.parallelRight h).map Prod.fst)
        ((RandomSystem.parallelRight h).map Prod.snd))
  · simp only [hh, if_false, false_and]
    exact Distribution.mass_eq_zero_of_forall_not _ (fun _ hf => hf)

end SystemAlgebra.PDS

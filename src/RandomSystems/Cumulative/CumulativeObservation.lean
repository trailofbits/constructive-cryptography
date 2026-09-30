import RandomSystems.Cumulative.Cumulative

/-!
# Transcript laws

An environment `σ` chooses the next query from the replies so far. Interacting
with a random system for at most `n` rounds gives a distribution on transcripts;
when `σ` queries only within the domain, it is a probability distribution. Two random
systems on one domain are equal exactly when all compatible environments see the same
transcript laws; on a domain of input histories, fixed query sequences suffice.
Source: Lanzenberger–Maurer, Definitions 7 and 10, Lemma 5 (printed pp. 12–14).

## Main definitions

* `Cons σ h`, `Done σ n h`, `Good σ n h`: transcripts following `σ`, complete within
  `n` rounds
* `RandomSystem.sLaw R σ n`: the transcript law
* `RandomSystem.Compatible R σ`: `σ` queries only admitted inputs after possible
  transcripts
* `follow h`: the environment following the transcript `h`

## Main results

* `sLaw_isProbDist`: the transcript law of a compatible environment is a probability
  distribution
* `sLaw_completed_stable`, `sLaw_eq_of_query_bounds`: larger round bounds do not change
  completed transcripts
* `sLaw_completed_eq_mass`: on a finite presentation, completed transcript
  probabilities are sample masses
* `RandomSystem.eq_iff_sLaw`: equality is equality of transcript laws in all compatible
  environments (Definition 10)
* `RandomSystem.eq_iff_sLaw_fixedQueries`: on input domains, fixed query sequences
  suffice (Lemma 5)
-/

namespace SystemAlgebra

open Classical Probability

variable {A B : Type}
variable (σ : List B →. A)

/-- The queries of `h` follow `σ`. -/
def Cons (h : List (A × B)) : Prop :=
  ∀ i (hi : i < h.length), (h[i]).1 ∈ σ ((h.take i).map Prod.snd)

/-- `h` is complete for `σ` within `n` rounds. -/
def Done (n : ℕ) (h : List (A × B)) : Prop :=
  h.length = n ∨ (h.length < n ∧ ¬ (σ (h.map Prod.snd)).Dom)

/-- The transcripts of `σ` within `n` rounds. -/
def Good (n : ℕ) (h : List (A × B)) : Prop := Cons σ h ∧ Done σ n h

variable {σ}

theorem cons_nil : Cons σ ([] : List (A × B)) := fun i hi => absurd hi (by simp)

theorem cons_snoc {h : List (A × B)} {z : A × B} :
    Cons σ (h ++ [z]) ↔ Cons σ h ∧ z.1 ∈ σ (h.map Prod.snd) := by
  constructor
  · intro hc
    refine ⟨fun i hi => ?_, ?_⟩
    · have := hc i (by simp; omega)
      rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at this
    · have := hc h.length (by simp)
      rw [List.getElem_append_right (le_refl _), List.take_left' rfl] at this
      simpa using this
  · rintro ⟨hc, hz⟩ i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < h.length
    · rw [List.getElem_append_left hlt, List.take_append_of_le_length hlt.le]
      exact hc i hlt
    · have e : i = h.length := by omega
      subst e
      rw [List.take_left' rfl]
      simpa using hz

theorem Cons.of_prefix {h h' : List (A × B)} (hc : Cons σ h') (hp : h <+: h') : Cons σ h := by
  obtain ⟨e, rfl⟩ := hp
  intro i hi
  have := hc i (by simp; omega)
  rwa [List.getElem_append_left hi, List.take_append_of_le_length hi.le] at this

variable {s : System A B}

theorem transcript_cons {s : System A B} {xs ys}
    (tr : Transcript s σ xs ys) : Cons σ (xs.zip ys) := by
  induction tr with
  | nil => exact cons_nil
  | @snoc xs ys x y tr hx _ ih =>
    rw [List.zip_append (by simpa using tr.length_eq)]
    refine cons_snoc.mpr ⟨ih, ?_⟩
    rw [List.map_snd_zip (by rw [tr.length_eq])]
    exact hx

theorem transcript_of_cons {s : System A B} :
    ∀ {h : List (A × B)}, Cons σ h → Replies s (h.map Prod.fst) (h.map Prod.snd) →
      Transcript s σ (h.map Prod.fst) (h.map Prod.snd) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; exact Transcript.nil
  | append_singleton h z ih =>
    intro hc hr
    obtain ⟨hc', hz⟩ := cons_snoc.mp hc
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr', e⟩ := replies_snoc.mp hr
    exact Transcript.snoc (ih hc' hr') hz (by rw [e]; exact Part.mem_some _)

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}
variable (R : RandomSystem A B D) (σ : List B →. A)

/-- The transcripts of `σ` within `m` rounds with positive mass (a superset). -/
noncomputable def tSupp : ℕ → Finset (List (A × B))
  | 0 => {[]}
  | m + 1 => (tSupp m).biUnion fun h =>
      if hd : (σ (h.map Prod.snd)).Dom then
        (R.extensionLaw h ((σ (h.map Prod.snd)).get hd)).support.image
          fun y => h ++ [((σ (h.map Prod.snd)).get hd, y)]
      else {h}

variable {R σ}

theorem tSupp_good : ∀ {m h}, h ∈ tSupp R σ m → Good σ m h := by
  intro m
  induction m with
  | zero => intro h hh; simp [tSupp] at hh; subst hh; exact ⟨cons_nil, Or.inl rfl⟩
  | succ m ih =>
    intro h hh
    simp only [tSupp, Finset.mem_biUnion] at hh
    obtain ⟨h', hh', hm⟩ := hh
    obtain ⟨hc, hd'⟩ := ih hh'
    split_ifs at hm with hd
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hm
      have hl : h'.length = m := by
        rcases hd' with h | ⟨_, h⟩
        · exact h
        · exact absurd hd h
      exact ⟨cons_snoc.mpr ⟨hc, Part.get_mem hd⟩, Or.inl (by simp [hl])⟩
    · rw [Finset.mem_singleton] at hm
      subst hm
      refine ⟨hc, Or.inr ⟨?_, hd⟩⟩
      rcases hd' with h | ⟨h, _⟩ <;> omega

theorem mem_tSupp : ∀ {m h}, Good σ m h → R h ≠ 0 → h ∈ tSupp R σ m := by
  intro m
  induction m with
  | zero =>
    rintro h ⟨-, hd⟩ -
    have : h.length = 0 := by rcases hd with h | ⟨h, _⟩ <;> omega
    simp [tSupp, List.length_eq_zero_iff.mp this]
  | succ m ih =>
    rintro h ⟨hc, hd⟩ hm
    simp only [tSupp, Finset.mem_biUnion]
    rcases hd with hl | ⟨hl, hnd⟩
    · obtain ⟨h', z, rfl⟩ : ∃ h' z, h = h' ++ [z] := by
        rcases List.eq_nil_or_concat h with rfl | ⟨h', z, rfl⟩
        · simp at hl
        · exact ⟨h', z, List.concat_eq_append ..⟩
      obtain ⟨hc', hz⟩ := cons_snoc.mp hc
      have hl' : h'.length = m := by simpa using hl
      have hm' : R h' ≠ 0 := fun h0 => hm (mass_eq_zero_of_prefix R ⟨_, rfl⟩ h0)
      refine ⟨h', ih ⟨hc', Or.inl hl'⟩ hm', ?_⟩
      have hd : (σ (h'.map Prod.snd)).Dom := Part.dom_iff_mem.mpr ⟨_, hz⟩
      rw [dif_pos hd]
      have hx : (σ (h'.map Prod.snd)).get hd = z.1 := Part.get_eq_of_mem hz hd
      refine Finset.mem_image.mpr ⟨z.2, ?_, by rw [hx]⟩
      rw [Finsupp.mem_support_iff, hx, R.extensionLaw_apply]
      exact hm
    · refine ⟨h, ih ⟨hc, ?_⟩ hm, by rw [dif_neg hnd]; exact Finset.mem_singleton_self _⟩
      by_cases e : h.length = m
      · exact Or.inl e
      · exact Or.inr ⟨by omega, hnd⟩

variable (R σ)

/-- **The transcript law** of `R` with the strategy `σ` within `n` rounds. -/
noncomputable def sLaw (n : ℕ) : Distribution (List (A × B)) :=
  Finsupp.onFinset (tSupp R σ n) (fun h => if Good σ n h then R h else 0) fun h hh => by
    split_ifs at hh with hg
    · exact mem_tSupp hg hh
    · exact absurd rfl hh

variable {R σ}

theorem sLaw_apply (n : ℕ) (h : List (A × B)) :
    sLaw R σ n h = if Good σ n h then R h else 0 := Finsupp.onFinset_apply

theorem sLaw_nonNeg (n : ℕ) : (sLaw R σ n).NonNeg := fun h => by
  rw [sLaw_apply]; split_ifs
  · exact R.mass_nonneg _
  · exact le_rfl

/-- Compatibility says every query actually made after a possible transcript
is admitted. It neither totalizes the resource nor requires a decision output. -/
def Compatible (R : RandomSystem A B D) (σ : List B →. A) : Prop :=
  ∀ h x, Cons σ h → R h ≠ 0 → x ∈ σ (h.map Prod.snd) → D h x

theorem sum_extension (R : RandomSystem A B D) (h : List (A × B)) (x : A)
    (hd : D h x) : ∑ y ∈ (R.extensionLaw h x).support, R (h ++ [(x, y)]) = R h := by
  have hw := R.extensionLaw_weight h x
  rw [if_pos hd] at hw
  rw [← hw, Distribution.weight]
  unfold Finsupp.sum
  exact Finset.sum_congr rfl fun y _ => (R.extensionLaw_apply h x y).symm

theorem tSupp_possible : ∀ {m h}, h ∈ tSupp R σ m → R h ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro h hh
    have he : h = [] := by simpa [tSupp] using hh
    rw [he, R.mass_nil]
    exact one_ne_zero
  | succ m ih =>
    intro h hh
    simp only [tSupp, Finset.mem_biUnion] at hh
    obtain ⟨p, hp, hh⟩ := hh
    split_ifs at hh with hd
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hh
      simpa only [Finsupp.mem_support_iff, R.extensionLaw_apply] using hy
    · have he : h = p := Finset.mem_singleton.mp hh
      exact he ▸ ih hp

theorem sum_tSupp (hC : Compatible R σ) : ∀ m, ∑ h ∈ tSupp R σ m, (if Good σ m h then R h else 0) = 1 := by
  intro m
  induction m with
  | zero => simp [tSupp, Good, Done, cons_nil, R.mass_nil]
  | succ m ih =>
    rw [tSupp, Finset.sum_biUnion]
    · rw [← ih]
      refine Finset.sum_congr rfl fun h hh => ?_
      obtain ⟨hc, hd'⟩ := tSupp_good hh
      rw [if_pos ⟨hc, hd'⟩]
      split_ifs with hd
      · rw [Finset.sum_image (fun y _ y' _ e => by simpa using e)]
        rw [← sum_extension R h ((σ (h.map Prod.snd)).get hd)
          (hC h _ hc (tSupp_possible hh) (Part.get_mem hd))]
        refine Finset.sum_congr rfl fun y _ => ?_
        have hl : h.length = m := by
          rcases hd' with h | ⟨_, h⟩
          · exact h
          · exact absurd hd h
        rw [if_pos ⟨cons_snoc.mpr ⟨hc, Part.get_mem hd⟩, Or.inl (by simp [hl])⟩]
      · rw [Finset.sum_singleton,
          if_pos ⟨hc, Or.inr ⟨by rcases hd' with h | ⟨h, _⟩ <;> omega, hd⟩⟩]
    · intro h hh h' hh' hne
      simp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro g hg hg'
      obtain ⟨hc, hd⟩ := tSupp_good (m := m) hh
      obtain ⟨hc', hd'⟩ := tSupp_good (m := m) hh'
      split_ifs at hg hg' with e1 e2 e2
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
        exact hne (List.append_inj' e rfl).1.symm
      · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
        rw [Finset.mem_singleton] at hg'
        have hl : h.length = m := by rcases hd with h | ⟨_, h⟩; exact h; exact absurd e1 h
        have := congrArg List.length hg'
        rcases hd' with h | ⟨h, _⟩ <;> simp at this <;> omega
      · obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
        rw [Finset.mem_singleton] at hg
        have hl : h'.length = m := by rcases hd' with h | ⟨_, h⟩; exact h; exact absurd e2 h
        have := congrArg List.length (e.trans hg)
        rcases hd with h | ⟨h, _⟩ <;> simp at this <;> omega
      · rw [Finset.mem_singleton] at hg hg'
        exact hne (hg.symm.trans hg')

/-- **The transcript law is a probability distribution.** -/
theorem sLaw_isProbDist (hC : Compatible R σ) (n : ℕ) : (sLaw R σ n).isProbDist := by
  refine ⟨sLaw_nonNeg n, ?_⟩
  unfold Distribution.weight sLaw
  rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  exact sum_tSupp hC n

/-- Any two bounds beyond all possible queries give the same completed
transcript law. The bound is needed only on possible interaction histories. -/
theorem sLaw_eq_of_query_bounds {n m : ℕ}
    (hn : ∀ h, Cons σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < n)
    (hm : ∀ h, Cons σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < m) :
    R.sLaw σ n = R.sLaw σ m := by
  have good {k : ℕ}
      (hk : ∀ h, Cons σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < k)
      {h} (hc : Cons σ h) (hp : R h ≠ 0) :
      Good σ k h ↔ ¬ (σ (h.map Prod.snd)).Dom := by
    have hl : h.length ≤ k := by
      rcases List.eq_nil_or_concat h with rfl | ⟨pre, z, rfl⟩
      · simp
      · simp only [List.concat_eq_append] at hc hp ⊢
        have hpre : R pre ≠ 0 := fun hz => hp (R.mass_eq_zero_of_prefix ⟨[z], rfl⟩ hz)
        have hb := hk pre (cons_snoc.mp hc).1 hpre (cons_snoc.mp hc).2.1
        simp only [List.length_append, List.length_singleton]
        omega
    refine ⟨fun hg hd => ?_, fun hd => ⟨hc, ?_⟩⟩
    · rcases hg.2 with he | ⟨_, hs⟩
      · have := hk h hc hp hd
        omega
      · exact hs hd
    · by_cases he : h.length = k
      · exact Or.inl he
      · exact Or.inr ⟨by omega, hd⟩
  ext h
  rw [sLaw_apply, sLaw_apply]
  by_cases hp : R h = 0
  · simp [hp]
  · by_cases hc : Cons σ h
    · rw [good hn hc hp, good hm hc hp]
    · simp [Good, hc]

/-- Restricting to completed observations removes the artificial truncation
at the observation bound. -/
theorem sLaw_completed_apply (R : RandomSystem A B D) (σ : List B →. A)
    (n : ℕ) (h : List (A × B)) :
    ((R.sLaw σ n).restrict fun h => ¬ (σ (h.map Prod.snd)).Dom) h =
      if Cons σ h ∧ h.length ≤ n ∧ ¬ (σ (h.map Prod.snd)).Dom then R h else 0 := by
  classical
  rw [Distribution.restrict_apply, sLaw_apply]
  by_cases hd : (σ (h.map Prod.snd)).Dom
  · simp [hd]
  · have he : (h.length = n ∨ h.length < n) ↔ h.length ≤ n := by omega
    simp only [hd, not_false_eq_true, if_true, Good, Done, he, and_true]

/-- Once all possible completed transcripts fit, increasing the observation
bound changes no completed probability, even for partial resources. -/
theorem sLaw_completed_stable (R : RandomSystem A B D) (σ : List B →. A)
    {n m : ℕ} (hn : n ≤ m)
    (hb : ∀ h, Cons σ h → R h ≠ 0 → ¬ (σ (h.map Prod.snd)).Dom → h.length ≤ n) :
    (R.sLaw σ n).restrict (fun h => ¬ (σ (h.map Prod.snd)).Dom) =
      (R.sLaw σ m).restrict (fun h => ¬ (σ (h.map Prod.snd)).Dom) := by
  classical
  apply Finsupp.ext
  intro h
  rw [sLaw_completed_apply, sLaw_completed_apply]
  by_cases hp : R h = 0
  · simp [hp]
  · by_cases hc : Cons σ h
    · by_cases hd : (σ (h.map Prod.snd)).Dom
      · simp [hd]
      · simp [hc, hd, hb h hc hp hd, (hb h hc hp hd).trans hn]
    · simp [hc]

/-- For a finite presentation, the probability of a completed observation is
the mass of precisely those samples that produce that observation. Partiality
is retained: an unanswered query is not a completed transcript. -/
theorem sLaw_completed_eq_mass {ι : Type} (R : RandomSystem A B D)
    (P : Distribution ι) (hP : P.NonNeg) (systems : ι → System A B)
    (hR : ∀ h, R h = P.mass (fun s => Replies (systems s) (h.map Prod.fst) (h.map Prod.snd)))
    (σ : List B →. A) (n : ℕ) (E : List (A × B) → Prop) :
    (sLaw R σ n).mass
        (fun h => ¬ (σ (h.map Prod.snd)).Dom ∧ E h) =
      P.mass (fun s => ∃ h : List (A × B),
        Transcript (systems s) σ (h.map Prod.fst) (h.map Prod.snd) ∧
        h.length ≤ n ∧ ¬ (σ (h.map Prod.snd)).Dom ∧ E h) := by
  classical
  let T := tSupp R σ n
  let event := fun h : List (A × B) => ¬ (σ (h.map Prod.snd)).Dom ∧ E h
  have good (h) (hh : h ∈ T) := tSupp_good hh
  -- Sum transcript masses, then interchange the finite sums over transcripts and samples.
  calc
    _ = ∑ h ∈ T, ∑ s ∈ P.support,
        if event h ∧ Replies (systems s) (h.map Prod.fst) (h.map Prod.snd) then P s else 0 := by
      rw [Distribution.mass_eq_sum_of_support_subset (sLaw R σ n)
        (Finsupp.support_onFinset_subset ..) event, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro h hh
      rw [sLaw_apply, if_pos (good h hh)]
      rw [hR h]
      change (if event h then P.mass _ else 0) = _
      by_cases he : event h <;> simp [he, Distribution.mass, Finsupp.sum]
    _ = ∑ s ∈ P.support, ∑ h ∈ T,
        if event h ∧ Replies (systems s) (h.map Prod.fst) (h.map Prod.snd) then P s else 0 :=
      Finset.sum_comm
    _ = _ := by
      unfold Distribution.mass Finsupp.sum
      apply Finset.sum_congr rfl
      intro s hs
      -- A deterministic sample has at most one completed transcript.
      by_cases hex : ∃ h : List (A × B),
          Transcript (systems s) σ (h.map Prod.fst) (h.map Prod.snd) ∧
          h.length ≤ n ∧ ¬ (σ (h.map Prod.snd)).Dom ∧ E h
      · simp only [if_pos hex]
        obtain ⟨h, tr, hn, hd, he⟩ := hex
        have hc : Cons σ h := by
          have := transcript_cons tr
          have eh : h = (h.map Prod.fst).zip (h.map Prod.snd) := List.zip_of_prod rfl rfl
          exact eh ▸ this
        have hm : R h ≠ 0 := by
          rw [hR h]
          have hp := Distribution.apply_le_mass hP
            (P := fun t => Replies (systems t) (h.map Prod.fst) (h.map Prod.snd)) tr.replies
          exact ne_of_gt (lt_of_lt_of_le
            (lt_of_le_of_ne (hP s) (Ne.symm (Finsupp.mem_support_iff.mp hs))) hp)
        have ht : h ∈ T := mem_tSupp ⟨hc, by
          by_cases eq : h.length = n
          · exact Or.inl eq
          · exact Or.inr ⟨by omega, hd⟩⟩ hm
        rw [Finset.sum_eq_single_of_mem h ht, if_pos ⟨⟨hd, he⟩, tr.replies⟩]
        intro g hg hne
        apply if_neg
        rintro ⟨⟨hgd, _⟩, hgr⟩
        have tg := transcript_of_cons (good g hg).1 hgr
        obtain ⟨hx, hy⟩ := tg.eq_of_stopped tr hgd hd
        apply hne
        exact (List.zip_of_prod rfl rfl).trans
          ((congrArg₂ List.zip hx hy).trans (List.zip_of_prod rfl rfl).symm)
      · simp only [if_neg hex]
        apply Finset.sum_eq_zero
        intro h hh
        apply if_neg
        rintro ⟨⟨hd, he⟩, hr⟩
        obtain ⟨hc, hn⟩ := good h hh
        exact hex ⟨h, transcript_of_cons hc hr,
          by rcases hn with hn | ⟨hn, _⟩ <;> omega, hd, he⟩

end RandomSystem

/-! ## Equivalence by environments -/

section Follow

theorem cons_fixedQueries {xs : List A} {t : List (A × B)} (hc : Cons (fixedQueries xs) t) :
    t.length ≤ xs.length ∧ t.map Prod.fst = xs.take t.length := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t z ih =>
    obtain ⟨hc, hz⟩ := cons_snoc.mp hc
    obtain ⟨-, he⟩ := ih hc
    have hz' : xs[t.length]? = some z.1 := by simpa [fixedQueries] using hz
    have hlt : t.length < xs.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hz'
      cases hz'
    refine ⟨by simp; omega, ?_⟩
    rw [List.map_append, he, List.length_append, List.length_singleton, List.take_add_one, hz']
    rfl

/-- The environment following the transcript `h`: it submits the queries of `h` while the
replies agree with `h`, and stops as soon as they deviate. -/
noncomputable def follow (h : List (A × B)) : List B →. A := fun ys =>
  if ys = (h.take ys.length).map Prod.snd then fixedQueries (h.map Prod.fst) ys else Part.none

theorem mem_follow {h : List (A × B)} {ys : List B} {x : A} :
    x ∈ follow h ys ↔
      ys = (h.take ys.length).map Prod.snd ∧ x ∈ fixedQueries (h.map Prod.fst) ys := by
  unfold follow
  split_ifs with he
  · exact ⟨fun hx => ⟨he, hx⟩, fun hx => hx.2⟩
  · exact ⟨fun hx => absurd hx (Part.notMem_none _), fun hx => absurd hx.1 he⟩

theorem cons_follow_self (h : List (A × B)) : Cons (follow h) h := by
  intro i hi
  refine mem_follow.mpr ⟨by simp [Nat.min_eq_left hi.le], ?_⟩
  simp [fixedQueries, Nat.min_eq_left hi.le, hi]

/-- Before each of its queries, the environment following `h` has seen a prefix of `h`. -/
theorem follow_prefix {h t : List (A × B)} {x : A} (hc : Cons (follow h) t)
    (hx : x ∈ follow h (t.map Prod.snd)) :
    ∃ (i : ℕ) (hi : i < h.length), t = h.take i ∧ x = (h[i]).1 := by
  obtain ⟨hy, hq⟩ := mem_follow.mp hx
  obtain ⟨-, hf⟩ := cons_fixedQueries (fun i hi => (mem_follow.mp (hc i hi)).2)
  have hq' : (h.map Prod.fst)[t.length]? = some x := by simpa [fixedQueries] using hq
  have hlt : t.length < h.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by simp; omega)] at hq'
    cases hq'
  have hs : t.map Prod.snd = (h.take t.length).map Prod.snd := by simpa using hy
  have hf' : t.map Prod.fst = (h.take t.length).map Prod.fst := by rw [hf, List.map_take]
  refine ⟨t.length, hlt, ?_, ?_⟩
  · exact (List.zip_of_prod rfl rfl).trans
      ((congrArg₂ List.zip hf' hs).trans (List.zip_of_prod rfl rfl).symm)
  · simp [List.getElem?_eq_getElem hlt] at hq'
    exact hq'.symm

end Follow

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}

theorem compatible_follow (R : RandomSystem A B D) {h : List (A × B)}
    (hadm : ∀ i (hi : i < h.length), D (h.take i) (h[i]).1) : Compatible R (follow h) := by
  intro t x hc _ hx
  obtain ⟨i, hi, rfl, rfl⟩ := follow_prefix hc hx
  exact hadm i hi

theorem sLaw_follow (R : RandomSystem A B D) (h : List (A × B)) :
    sLaw R (follow h) h.length h = R h := by
  rw [sLaw_apply, if_pos ⟨cons_follow_self h, Or.inl rfl⟩]

theorem admitted_of_ne_zero {R S : RandomSystem A B D} {h : List (A × B)}
    (h0 : ¬ (R h = 0 ∧ S h = 0)) : ∀ i (hi : i < h.length), D (h.take i) (h[i]).1 := by
  intro i hi
  by_cases hr : R h = 0
  · exact (S.possible_prefix (fun hs => h0 ⟨hr, hs⟩) i hi).1
  · exact (R.possible_prefix hr i hi).1

/-- **Equivalence** (Lanzenberger–Maurer, Definition 10, printed p. 14): "Two (X, Y)-PDS S
and T are equivalent … if they have the same domain and tr(S, e) = tr(T, e) for all
compatible (Y, X)-DDE e." Two random systems on one domain are equal exactly when their
transcript laws agree for every compatible environment. -/
theorem eq_iff_sLaw {R S : RandomSystem A B D} :
    R = S ↔ ∀ σ, Compatible R σ → Compatible S σ → ∀ n, sLaw R σ n = sLaw S σ n := by
  refine ⟨fun he σ _ _ n => by subst he; rfl, fun he => ext fun h => ?_⟩
  by_cases h0 : R h = 0 ∧ S h = 0
  · rw [h0.1, h0.2]
  have hadm := admitted_of_ne_zero h0
  rw [← sLaw_follow R h, ← sLaw_follow S h,
    he (follow h) (R.compatible_follow hadm) (S.compatible_follow hadm)]

/-- **Lanzenberger–Maurer, Lemma 5** (printed p. 14): "For any two (X, Y)-PDS S and T with
the same domain we have S ≡ T if and only if tr(S, e) = tr(T, e) for all compatible
non-adaptive (Y, X)-DDE e." A non-adaptive environment submits a fixed query sequence
(footnote 10: "e(yⁱ) only depends on the length i of the sequence yⁱ"). On a domain of
input histories, fixed query sequences determine a random system. -/
theorem eq_iff_sLaw_fixedQueries {E : List A → Prop} {bound : ℕ}
    {hE : ∀ h, E h → h.length ≤ bound} {R S : RandomSystem A B (Domain.ofInputs E bound hE)} :
    R = S ↔ ∀ xs, Compatible R (fixedQueries xs) → Compatible S (fixedQueries xs) →
      ∀ n, sLaw R (fixedQueries xs) n = sLaw S (fixedQueries xs) n := by
  refine ⟨fun he xs _ _ n => by subst he; rfl, fun he => ext fun h => ?_⟩
  by_cases h0 : R h = 0 ∧ S h = 0
  · rw [h0.1, h0.2]
  have hadm := admitted_of_ne_zero h0
  have hcomp (T : RandomSystem A B (Domain.ofInputs E bound hE)) :
      Compatible T (fixedQueries (h.map Prod.fst)) := by
    intro t x hc _ hx
    obtain ⟨-, hf⟩ := cons_fixedQueries hc
    have hq : (h.map Prod.fst)[t.length]? = some x := by simpa [fixedQueries] using hx
    have hlt : t.length < h.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by simp; omega)] at hq
      cases hq
    simp [List.getElem?_eq_getElem hlt] at hq
    have := hadm t.length hlt
    simp only [Domain.ofInputs_apply] at this ⊢
    rw [hf, ← hq, ← List.map_take]
    exact this
  have hgood : Good (fixedQueries (h.map Prod.fst)) h.length h :=
    ⟨fun i hi => (mem_follow.mp (cons_follow_self h i hi)).2, Or.inl rfl⟩
  have e := congrArg (· h) (he _ (hcomp R) (hcomp S) h.length)
  simpa only [sLaw_apply, if_pos hgood] using e

end RandomSystem

end SystemAlgebra

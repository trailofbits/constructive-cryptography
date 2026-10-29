import RandomSystems.Cumulative.Cumulative
import RandomSystems.System.DDE

/-!
# Transcript laws

An environment `σ` chooses the next query from the replies so far. Interacting
with a random system for at most `n` rounds gives a distribution on transcripts;
when `σ` queries only within the domain, it is a probability distribution. Two random
systems on one domain are equal exactly when all compatible environments see the same
transcript laws; on a domain of input histories, fixed query sequences suffice.
Source: Lanzenberger–Maurer, Definitions 7 and 10, Lemma 5 (printed pp. 12–14).

## Main definitions

* `FollowsStrategy σ h`, `Done σ n h`, `Good σ n h`: transcripts following `σ`, complete within
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
* `sLaw_eq_domainBound`: a compatible `QueryBounded n E` is observed equally at `n` and at
  `D.bound`, since every possible query lies below the domain bound
* `FollowsStrategy.limitQueries_iff`, `Compatible.limitQueries`, `sLaw_limitQueries`: truncating
  a strategy `σ` at `n` keeps the transcripts of length `≤ n`, compatibility and the law at `n`
* `sLaw_completed_eq_mass`: on a finite presentation, completed transcript
  probabilities are sample masses
* `RandomSystem.eq_iff_sLaw`: equality is equality of transcript laws in all compatible
  environments (Definition 10)
* `RandomSystem.eq_iff_sLaw_fixedQueries`: on input domains, fixed query sequences
  suffice (Lemma 5)
-/

namespace SystemAlgebra

open Probability

variable {A B : Type}
variable (σ : List B →. A)

/-- Each query follows `σ`: for every prefix `pre ++ [(x,y)]` of `h`,
`x ∈ σ (pre.map Prod.snd)`. This is the environment equation of Lanzenberger–Maurer,
Definition 7, printed p. 12: “xᵢ = e(y₁, …, yᵢ₋₁)”. -/
def FollowsStrategy (h : List (A × B)) : Prop :=
  ∀ pre z, pre ++ [z] <+: h → z.1 ∈ σ (pre.map Prod.snd)

/-- `h` is complete for `σ` within `n` rounds. -/
def Done (n : ℕ) (h : List (A × B)) : Prop :=
  h.length = n ∨ (h.length < n ∧ ¬ (σ (h.map Prod.snd)).Dom)

/-- The transcripts of `σ` within `n` rounds. -/
def Good (n : ℕ) (h : List (A × B)) : Prop := FollowsStrategy σ h ∧ Done σ n h

variable {σ}

/-- The prefix rule is equivalently checked at every indexed exchange:
`h[i].1 ∈ σ ((h.take i).map Prod.snd)` for all `i < |h|`. -/
lemma FollowsStrategy.iff_getElem {h : List (A × B)} :
    FollowsStrategy σ h ↔ ∀ i (hi : i < h.length), h[i].1 ∈ σ ((h.take i).map Prod.snd) := by
  constructor
  -- Exchange `i` closes the prefix `h.take i ++ [h[i]]` of `h`.
  · intro hc i hi
    exact hc (h.take i) h[i]
      (by rw [← List.take_succ_eq_append_getElem hi]; exact List.take_prefix _ _)
  -- A prefix `pre ++ [z]` of `h` is exchange `|pre|`, preceded by `pre`.
  · intro hc pre z hp
    obtain ⟨tail, rfl⟩ := hp
    have hl : pre.length < ((pre ++ [z]) ++ tail).length := by
      simp only [List.length_append, List.length_singleton]
      omega
    have hx := hc pre.length hl
    simpa only [List.append_assoc, List.getElem_append_right (le_refl _), Nat.sub_self,
      List.cons_append, List.nil_append, List.getElem_cons_zero,
      List.take_append_of_le_length (le_refl _), List.take_length] using hx

/-- The empty transcript makes no query. -/
lemma FollowsStrategy.nil : FollowsStrategy σ [] := by
  intro pre z hp
  have := hp.length_le
  simp only [List.length_append, List.length_singleton, List.length_nil] at this
  omega

/-- Every prefix of a transcript follows the same strategy. -/
lemma FollowsStrategy.of_prefix {h h' : List (A × B)} (hc : FollowsStrategy σ h') (hp : h <+: h') :
    FollowsStrategy σ h := fun pre z hz => hc pre z (hz.trans hp)

/-- Appending an exchange preserves the strategy exactly when its query is the next query. -/
lemma FollowsStrategy.snoc_iff {h : List (A × B)} {z : A × B} :
    FollowsStrategy σ (h ++ [z]) ↔ FollowsStrategy σ h ∧ z.1 ∈ σ (h.map Prod.snd) := by
  constructor
  · intro hc
    exact ⟨FollowsStrategy.of_prefix hc (List.prefix_append _ _), hc h z List.prefix_rfl⟩
  · rintro ⟨hc, hz⟩ pre w hp
    -- A prefix of `h ++ [z]` is either all of it, checked by `hz`, or a prefix of `h`.
    rcases List.prefix_concat_iff.mp hp with he | hp
    · have hw : w = z := by
        simpa only [List.singleton_inj] using List.append_inj_right' he (by rfl)
      subst w
      have hpre := List.append_cancel_right he
      subst pre
      exact hz
    · exact hc pre w hp

variable {s : System A B}

/-- The exchanges of an interaction of `s` with `σ` follow `σ`. -/
lemma Transcript.followsStrategy {s : System A B} {xs ys}
    (tr : Transcript s σ xs ys) : FollowsStrategy σ (xs.zip ys) := by
  induction tr with
  | nil => exact FollowsStrategy.nil
  | @snoc xs ys x y tr hx _ ih =>
    rw [List.zip_append (by simpa using tr.length_eq)]
    refine FollowsStrategy.snoc_iff.mpr ⟨ih, ?_⟩
    rw [List.map_snd_zip (by rw [tr.length_eq])]
    exact hx

/-- Conversely, exchanges that follow `σ` and are replies of `s` form an interaction of `s`
with `σ`. -/
lemma FollowsStrategy.transcript {s : System A B} :
    ∀ {h : List (A × B)}, FollowsStrategy σ h → Replies s (h.map Prod.fst) (h.map Prod.snd) →
      Transcript s σ (h.map Prod.fst) (h.map Prod.snd) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; exact Transcript.nil
  | append_singleton h z ih =>
    intro hc hr
    obtain ⟨hc', hz⟩ := FollowsStrategy.snoc_iff.mp hc
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr', e⟩ := replies_snoc.mp hr
    exact Transcript.snoc (ih hc' hr') hz (by rw [e]; exact Part.mem_some _)

/-- Limiting queries preserves exactly the strategy transcripts of length at most `n`. -/
lemma FollowsStrategy.limitQueries_iff {σ : List B →. A} {n : ℕ} {h : List (A × B)} :
    FollowsStrategy (limitQueries σ n) h ↔ FollowsStrategy σ h ∧ h.length ≤ n := by
  constructor
  -- Each truncated query is a query of `σ`; the last one was asked after `|h| - 1 < n` replies.
  · intro hc
    refine ⟨fun pre z hp => (mem_limitQueries.mp (hc pre z hp)).2, ?_⟩
    rcases List.eq_nil_or_concat h with rfl | ⟨pre, z, rfl⟩
    · exact Nat.zero_le _
    · simp only [List.concat_eq_append] at hc ⊢
      have hl := (mem_limitQueries.mp (hc pre z List.prefix_rfl)).1
      simp only [List.length_map] at hl
      simp only [List.length_append, List.length_singleton]
      omega
  -- Each query of `σ` in `h` is asked after `|pre| < |h| ≤ n` replies, so it is kept.
  · rintro ⟨hc, hn⟩ pre z hp
    apply mem_limitQueries.mpr
    refine ⟨?_, hc pre z hp⟩
    have hl := hp.length_le
    simp only [List.length_append, List.length_singleton] at hl
    simp only [List.length_map]
    omega

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}
variable (R : RandomSystem A B D) (σ : List B →. A)

open Classical in
/-- The transcripts of `σ` within `m` rounds with positive mass (a superset). -/
noncomputable def tSupp : ℕ → Finset (List (A × B))
  | 0 => {[]}
  | m + 1 => (tSupp m).biUnion fun h =>
      if hd : (σ (h.map Prod.snd)).Dom then
        (R.extensionLaw h ((σ (h.map Prod.snd)).get hd)).support.image
          fun y => h ++ [((σ (h.map Prod.snd)).get hd, y)]
      else {h}

variable {R σ}

lemma tSupp_good : ∀ {m h}, h ∈ tSupp R σ m → Good σ m h := by
  classical
  intro m
  induction m with
  | zero =>
    intro h hh
    simp only [tSupp, Finset.mem_singleton] at hh
    subst hh
    exact ⟨FollowsStrategy.nil, Or.inl rfl⟩
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
      exact ⟨FollowsStrategy.snoc_iff.mpr ⟨hc, Part.get_mem hd⟩, Or.inl (by simp [hl])⟩
    · rw [Finset.mem_singleton] at hm
      subst hm
      refine ⟨hc, Or.inr ⟨?_, hd⟩⟩
      rcases hd' with h | ⟨h, _⟩ <;> omega

lemma mem_tSupp : ∀ {m h}, Good σ m h → R h ≠ 0 → h ∈ tSupp R σ m := by
  classical
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
      obtain ⟨hc', hz⟩ := FollowsStrategy.snoc_iff.mp hc
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

open Classical in
/-- **The transcript law** of `R` with the strategy `σ` within `n` rounds. -/
noncomputable def sLaw (n : ℕ) : Distribution (List (A × B)) :=
  Finsupp.onFinset (tSupp R σ n) (fun h => if Good σ n h then R h else 0) fun h hh => by
    split_ifs at hh with hg
    · exact mem_tSupp hg hh
    · exact absurd rfl hh

variable {R σ}

open Classical in
lemma sLaw_apply (n : ℕ) (h : List (A × B)) :
    sLaw R σ n h = if Good σ n h then R h else 0 := Finsupp.onFinset_apply

lemma sLaw_nonNeg (n : ℕ) : (sLaw R σ n).NonNeg := fun h => by
  rw [sLaw_apply]; split_ifs
  · exact R.mass_nonneg _
  · exact le_rfl

/-- Compatibility says every query actually made after a possible transcript
is admitted. It neither totalizes the resource nor requires a decision output. -/
def Compatible (R : RandomSystem A B D) (σ : List B →. A) : Prop :=
  ∀ h x, FollowsStrategy σ h → R h ≠ 0 → x ∈ σ (h.map Prod.snd) → D h x

/-- Stopping a compatible strategy after `n` queries cannot introduce an inadmissible query. -/
lemma Compatible.limitQueries {R : RandomSystem A B D} {σ : List B →. A}
    (hc : R.Compatible σ) (n : ℕ) : R.Compatible (limitQueries σ n) := by
  intro h x ht hp hx
  -- The truncated history and query are a history and query of `σ`.
  exact hc h x (FollowsStrategy.limitQueries_iff.mp ht).1 hp (mem_limitQueries.mp hx).2

lemma sum_extension (R : RandomSystem A B D) (h : List (A × B)) (x : A)
    (hd : D h x) : ∑ y ∈ (R.extensionLaw h x).support, R (h ++ [(x, y)]) = R h := by
  have hw := R.extensionLaw_weight h x
  rw [if_pos hd] at hw
  rw [← hw, Distribution.weight]
  unfold Finsupp.sum
  exact Finset.sum_congr rfl fun y _ => (R.extensionLaw_apply h x y).symm

lemma tSupp_possible : ∀ {m h}, h ∈ tSupp R σ m → R h ≠ 0 := by
  classical
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

open Classical in
/-- **One more round**: a sum over the transcripts of `σ` within `m + 1` rounds is the sum, over
the transcripts within `m` rounds, of the sum over their extensions by the possible replies to
the next query of `σ`, or of the transcript itself when `σ` has stopped. -/
lemma sum_tSupp_succ (f : List (A × B) → ℝ) (m : ℕ) :
    ∑ h ∈ tSupp R σ (m + 1), f h = ∑ h ∈ tSupp R σ m,
      if hd : (σ (h.map Prod.snd)).Dom then
        ∑ y ∈ (R.extensionLaw h ((σ (h.map Prod.snd)).get hd)).support,
          f (h ++ [((σ (h.map Prod.snd)).get hd, y)])
      else f h := by
  -- The transcripts within m + 1 rounds are the union, over the transcripts h within m rounds,
  -- of the extensions of h by one round, or of h itself; the union is disjoint.
  rw [tSupp, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hd
    -- Distinct replies give distinct extensions.
    · exact Finset.sum_image fun y _ y' _ e => by simpa using e
    · exact Finset.sum_singleton _ _
  -- Disjointness. A transcript within m rounds has at most m rounds, and exactly m when σ asks
  -- a further query; so an extension by one round has m + 1 rounds and a kept transcript at most
  -- m, and a transcript is determined by any extension of it by one round.
  · intro h hh h' hh' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro g hg hg'
    have hlen : ∀ p ∈ tSupp R σ m,
        p.length ≤ m ∧ ((σ (p.map Prod.snd)).Dom → p.length = m) := by
      intro p hp
      rcases (tSupp_good hp).2 with hl | ⟨hl, hs⟩
      · exact ⟨hl.le, fun _ => hl⟩
      · exact ⟨hl.le, fun hd => absurd hd hs⟩
    split_ifs at hg hg' with e1 e2 e2
    -- Both extended: the extensions agree, so do the transcripts.
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
      exact hne (List.append_inj' e rfl).1.symm
    -- One extended, one kept: m + 1 rounds against at most m.
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hg
      have hl := congrArg List.length (Finset.mem_singleton.mp hg')
      simp only [List.length_append, List.length_singleton] at hl
      have := (hlen h hh).2 e1
      have := (hlen h' hh').1
      omega
    · obtain ⟨y', -, e⟩ := Finset.mem_image.mp hg'
      have hl := congrArg List.length (e.trans (Finset.mem_singleton.mp hg))
      simp only [List.length_append, List.length_singleton] at hl
      have := (hlen h' hh').2 e2
      have := (hlen h hh).1
      omega
    -- Both kept: both are the transcript g.
    · exact hne ((Finset.mem_singleton.mp hg).symm.trans (Finset.mem_singleton.mp hg'))

open Classical in
lemma sum_tSupp (hC : Compatible R σ) :
    ∀ m, ∑ h ∈ tSupp R σ m, (if Good σ m h then R h else 0) = 1 := by
  intro m
  induction m with
  | zero => simp [tSupp, Good, Done, FollowsStrategy.nil, R.mass_nil]
  | succ m ih =>
    -- One more round: each transcript h within m rounds keeps its probability, spread over its
    -- extensions when σ asks a further query.
    rw [sum_tSupp_succ, ← ih]
    refine Finset.sum_congr rfl fun h hh => ?_
    obtain ⟨hc, hd'⟩ := tSupp_good hh
    rw [if_pos (show Good σ m h from ⟨hc, hd'⟩)]
    by_cases hd : (σ (h.map Prod.snd)).Dom
    -- σ asks x after h, admitted by compatibility: the possible replies to x weigh R h, and each
    -- extension of h has m + 1 rounds.
    · rw [dif_pos hd, ← sum_extension R h ((σ (h.map Prod.snd)).get hd)
        (hC h _ hc (tSupp_possible hh) (Part.get_mem hd))]
      have hl : h.length = m := by
        rcases hd' with hl | ⟨_, hs⟩
        · exact hl
        · exact absurd hd hs
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [if_pos ⟨FollowsStrategy.snoc_iff.mpr ⟨hc, Part.get_mem hd⟩, Or.inl (by simp [hl])⟩]
    -- σ has stopped: h is complete within m + 1 rounds too.
    · rw [dif_neg hd, if_pos ⟨hc, Or.inr ⟨by rcases hd' with hl | ⟨hl, _⟩ <;> omega, hd⟩⟩]

/-- **The transcript law is a probability distribution.** -/
lemma sLaw_isProbDist (hC : Compatible R σ) (n : ℕ) : (sLaw R σ n).isProbDist := by
  refine ⟨sLaw_nonNeg n, ?_⟩
  unfold Distribution.weight sLaw
  rw [Finsupp.onFinset_sum _ (fun _ => rfl)]
  exact sum_tSupp hC n

/-- Any two bounds beyond all possible queries give the same completed
transcript law. The bound is needed only on possible interaction histories. -/
lemma sLaw_eq_of_query_bounds {n m : ℕ}
    (hn : ∀ h, FollowsStrategy σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < n)
    (hm : ∀ h, FollowsStrategy σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < m) :
    R.sLaw σ n = R.sLaw σ m := by
  have good {k : ℕ}
      (hk : ∀ h, FollowsStrategy σ h → R h ≠ 0 → (σ (h.map Prod.snd)).Dom → h.length < k)
      {h} (hc : FollowsStrategy σ h) (hp : R h ≠ 0) :
      Good σ k h ↔ ¬ (σ (h.map Prod.snd)).Dom := by
    have hl : h.length ≤ k := by
      rcases List.eq_nil_or_concat h with rfl | ⟨pre, z, rfl⟩
      · simp
      · simp only [List.concat_eq_append] at hc hp ⊢
        have hpre : R pre ≠ 0 := fun hz => hp (R.mass_eq_zero_of_prefix ⟨[z], rfl⟩ hz)
        have hb := hk pre (FollowsStrategy.snoc_iff.mp hc).1 hpre
          (FollowsStrategy.snoc_iff.mp hc).2.1
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
  · by_cases hc : FollowsStrategy σ h
    · rw [good hn hc hp, good hm hc hp]
    · simp [Good, hc]

/-- For compatible `E` with `QueryBounded n E`, `sLaw R E n = sLaw R E D.bound`: both bounds lie
beyond every possible query, so `sLaw_eq_of_query_bounds` applies. -/
lemma sLaw_eq_domainBound (R : RandomSystem A B D) {E : DDE A B} {n : ℕ}
    (hn : QueryBounded n E) (hc : R.Compatible E.1) : R.sLaw E.1 n = R.sLaw E.1 D.bound := by
  apply R.sLaw_eq_of_query_bounds
  -- `E` queries only after fewer than `n` replies.
  · intro h _ _ hd
    simpa only [List.length_map] using hn _ hd
  -- A possible query is admitted by compatibility, and admitted histories are below `D.bound`.
  · intro h ht hp hd
    exact D.length_lt _ _ (hc h _ ht hp (Part.get_mem hd))

/-- The law observed through round `n` is unchanged by stopping the strategy at `n`:
`sLaw R (limitQueries σ n) n = sLaw R σ n`. No compatibility is needed. -/
lemma sLaw_limitQueries (R : RandomSystem A B D) (σ : List B →. A) (n : ℕ) :
    R.sLaw (limitQueries σ n) n = R.sLaw σ n := by
  ext h
  rw [RandomSystem.sLaw_apply, RandomSystem.sLaw_apply]
  -- Both laws weigh `R h`; the transcripts within `n` rounds coincide.
  have hg : Good (limitQueries σ n) n h ↔ Good σ n h := by
    rw [Good, Good, FollowsStrategy.limitQueries_iff]
    unfold Done limitQueries
    simp only [List.length_map]
    split_ifs with hn
    -- Below `n`, the truncated strategy queries exactly as `σ`.
    · exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hn.le⟩, h.2⟩⟩
    -- At `|h| ≥ n`, only `|h| = n` is complete for either strategy.
    · simp only [Part.not_none_dom, not_false_eq_true, and_true, hn, false_and, or_false]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.le⟩, h.2⟩⟩
  rw [hg]

open Classical in
/-- Restricting to completed observations removes the artificial truncation
at the observation bound. -/
lemma sLaw_completed_apply (R : RandomSystem A B D) (σ : List B →. A)
    (n : ℕ) (h : List (A × B)) :
    ((R.sLaw σ n).restrict fun h => ¬ (σ (h.map Prod.snd)).Dom) h =
      if FollowsStrategy σ h ∧ h.length ≤ n ∧ ¬ (σ (h.map Prod.snd)).Dom then R h else 0 := by
  classical
  rw [Distribution.restrict_apply, sLaw_apply]
  by_cases hd : (σ (h.map Prod.snd)).Dom
  · simp [hd]
  · have he : (h.length = n ∨ h.length < n) ↔ h.length ≤ n := by omega
    simp only [hd, not_false_eq_true, if_true, Good, Done, he, and_true]

/-- Once all possible completed transcripts fit, increasing the observation
bound changes no completed probability, even for partial resources. -/
lemma sLaw_completed_stable (R : RandomSystem A B D) (σ : List B →. A)
    {n m : ℕ} (hn : n ≤ m)
    (hb : ∀ h, FollowsStrategy σ h → R h ≠ 0 → ¬ (σ (h.map Prod.snd)).Dom → h.length ≤ n) :
    (R.sLaw σ n).restrict (fun h => ¬ (σ (h.map Prod.snd)).Dom) =
      (R.sLaw σ m).restrict (fun h => ¬ (σ (h.map Prod.snd)).Dom) := by
  classical
  apply Finsupp.ext
  intro h
  rw [sLaw_completed_apply, sLaw_completed_apply]
  by_cases hp : R h = 0
  · simp [hp]
  · by_cases hc : FollowsStrategy σ h
    · by_cases hd : (σ (h.map Prod.snd)).Dom
      · simp [hd]
      · simp [hc, hd, hb h hc hp hd, (hb h hc hp hd).trans hn]
    · simp [hc]

/-- For a finite presentation, the probability of a completed observation is
the mass of precisely those samples that produce that observation. Partiality
is retained: an unanswered query is not a completed transcript. -/
lemma sLaw_completed_eq_mass {ι : Type} (R : RandomSystem A B D)
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
        have hc : FollowsStrategy σ h := by
          have := Transcript.followsStrategy tr
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
        have tg := FollowsStrategy.transcript (good g hg).1 hgr
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
        exact hex ⟨h, FollowsStrategy.transcript hc hr,
          by rcases hn with hn | ⟨hn, _⟩ <;> omega, hd, he⟩

end RandomSystem

/-! ## Equivalence by environments -/

section Follow

lemma FollowsStrategy.fixedQueries {xs : List A} {t : List (A × B)}
    (hc : FollowsStrategy (fixedQueries xs) t) :
    t.length ≤ xs.length ∧ t.map Prod.fst = xs.take t.length := by
  induction t using List.reverseRecOn with
  | nil => simp
  | append_singleton t z ih =>
    obtain ⟨hc, hz⟩ := FollowsStrategy.snoc_iff.mp hc
    obtain ⟨-, he⟩ := ih hc
    have hz' : xs[t.length]? = some z.1 := by simpa [SystemAlgebra.fixedQueries] using hz
    have hlt : t.length < xs.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hz'
      cases hz'
    refine ⟨by simp; omega, ?_⟩
    rw [List.map_append, he, List.length_append, List.length_singleton, List.take_add_one, hz']
    rfl

open Classical in
/-- The environment following the transcript `h`: it submits the queries of `h` while the
replies agree with `h`, and stops as soon as they deviate. -/
noncomputable def follow (h : List (A × B)) : List B →. A := fun ys =>
  if ys = (h.take ys.length).map Prod.snd then fixedQueries (h.map Prod.fst) ys else Part.none

lemma mem_follow {h : List (A × B)} {ys : List B} {x : A} :
    x ∈ follow h ys ↔
      ys = (h.take ys.length).map Prod.snd ∧ x ∈ fixedQueries (h.map Prod.fst) ys := by
  unfold follow
  split_ifs with he
  · exact ⟨fun hx => ⟨he, hx⟩, fun hx => hx.2⟩
  · exact ⟨fun hx => absurd hx (Part.notMem_none _), fun hx => absurd hx.1 he⟩

lemma FollowsStrategy.follow_self (h : List (A × B)) : FollowsStrategy (follow h) h := by
  apply FollowsStrategy.iff_getElem.mpr
  intro i hi
  refine mem_follow.mpr ⟨by simp [Nat.min_eq_left hi.le], ?_⟩
  simp [SystemAlgebra.fixedQueries, Nat.min_eq_left hi.le, hi]

/-- Before each of its queries, the environment following `h` has seen a prefix of `h`. -/
lemma follow_prefix {h t : List (A × B)} {x : A} (hc : FollowsStrategy (follow h) t)
    (hx : x ∈ follow h (t.map Prod.snd)) :
    ∃ (i : ℕ) (hi : i < h.length), t = h.take i ∧ x = (h[i]).1 := by
  obtain ⟨hy, hq⟩ := mem_follow.mp hx
  obtain ⟨-, hf⟩ := FollowsStrategy.fixedQueries (fun pre z hp => (mem_follow.mp (hc pre z hp)).2)
  have hq' : (h.map Prod.fst)[t.length]? = some x := by simpa [SystemAlgebra.fixedQueries] using hq
  have hlt : t.length < h.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by simp; omega)] at hq'
    cases hq'
  have hs : t.map Prod.snd = (h.take t.length).map Prod.snd := by simpa using hy
  have hf' : t.map Prod.fst = (h.take t.length).map Prod.fst := by rw [hf, List.map_take]
  refine ⟨t.length, hlt, ?_, ?_⟩
  · exact (List.zip_of_prod rfl rfl).trans
      ((congrArg₂ List.zip hf' hs).trans (List.zip_of_prod rfl rfl).symm)
  · simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
      Option.some.injEq] at hq'
    exact hq'.symm

end Follow

namespace RandomSystem

variable [Fintype A] [Fintype B] {D : Domain A B}

lemma compatible_follow (R : RandomSystem A B D) {h : List (A × B)}
    (hadm : ∀ i (hi : i < h.length), D (h.take i) (h[i]).1) : Compatible R (follow h) := by
  intro t x hc _ hx
  obtain ⟨i, hi, rfl, rfl⟩ := follow_prefix hc hx
  exact hadm i hi

lemma sLaw_follow (R : RandomSystem A B D) (h : List (A × B)) :
    sLaw R (follow h) h.length h = R h := by
  rw [sLaw_apply, if_pos ⟨FollowsStrategy.follow_self h, Or.inl rfl⟩]

lemma admitted_of_ne_zero {R S : RandomSystem A B D} {h : List (A × B)}
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
    obtain ⟨-, hf⟩ := FollowsStrategy.fixedQueries hc
    have hq : (h.map Prod.fst)[t.length]? = some x := by simpa [SystemAlgebra.fixedQueries] using hx
    have hlt : t.length < h.length := by
      by_contra hn
      rw [List.getElem?_eq_none (by simp; omega)] at hq
      cases hq
    simp only [List.getElem?_map, List.getElem?_eq_getElem hlt, Option.map_some,
      Option.some.injEq] at hq
    have := hadm t.length hlt
    simp only [Domain.ofInputs_apply] at this ⊢
    rw [hf, ← hq, ← List.map_take]
    exact this
  have hgood : Good (fixedQueries (h.map Prod.fst)) h.length h :=
    ⟨fun pre z hp => (mem_follow.mp (FollowsStrategy.follow_self h pre z hp)).2, Or.inl rfl⟩
  have e := congrArg (· h) (he _ (hcomp R) (hcomp S) h.length)
  simpa only [sLaw_apply, if_pos hgood] using e

end RandomSystem

end SystemAlgebra

import RandomSystems.Cumulative.CumulativeOperations
import RandomSystems.Cumulative.Presentation

/-!
# Observing a connection

An environment observes the replies of a connection to a fixed input sequence by
following its internal exchanges. This characterizes the replies of deterministic
connections, and defines the law of the exposed replies of a connected random
system.

## Main definitions

* `exposedReplies`, `connectionQueries`: the replies a connection exposes, and the
  environment observing them
* `RandomSystem.connectionLaw`: the law of completed exposed replies

## Main results

* `replies_connection_iff`: completed transcripts characterize deterministic
  connections
* `connectionLaw_eq_mass`: on a presentation, connection probabilities are those of
  the deterministic connection
* `exists_parallel_connection_presentations`: a connection of two random systems is
  observed through independent presentations
-/

namespace SystemAlgebra

variable {A B X Y : Type}

/-- The replies exposed by a connection, in their original order. -/
def exposedReplies (route : Y → B ⊕ X) (ys : List Y) : List B :=
  ys.filterMap fun y => (route y).getLeft?

theorem exposedReplies_append (route : Y → B ⊕ X) (ys zs : List Y) :
    exposedReplies route (ys ++ zs) = exposedReplies route ys ++ exposedReplies route zs := by
  simp only [exposedReplies, List.filterMap_append]

/-- The environment that follows a connection while submitting `us` in order.
It stops exactly after receiving all the requested exposed replies. -/
def connectionQueries (route : Y → B ⊕ X) (inj : A → X) (us : List A) : List Y →. X :=
  fun ys => ⟨(exposedReplies route ys).length < us.length, fun hd =>
    match ys.getLast? with
    | none => inj us[(exposedReplies route ys).length]
    | some y => (route y).elim (fun _ => inj us[(exposedReplies route ys).length]) id⟩

theorem connectionQueries_dom (route : Y → B ⊕ X) (inj : A → X) (us : List A) (ys : List Y) :
    (connectionQueries route inj us ys).Dom ↔ (exposedReplies route ys).length < us.length := Iff.rfl

theorem connectionQueries_prefix (route : Y → B ⊕ X) (inj : A → X) (us : List A)
    (ys : List Y) (y : Y) (hd : (connectionQueries route inj us (ys ++ [y])).Dom) :
    (connectionQueries route inj us ys).Dom := by
  change (exposedReplies route ys).length < us.length
  change (exposedReplies route (ys ++ [y])).length < us.length at hd
  simp only [exposedReplies, List.filterMap_append, List.length_append] at hd ⊢
  omega

theorem connectionQueries_nil (route : Y → B ⊕ X) (inj : A → X) (us : List A) :
    connectionQueries route inj us [] = (us.head?.map inj : Part X) := by
  cases us with
  | nil => exact Part.ext fun _ => by simp [connectionQueries, exposedReplies]
  | cons a us => exact Part.ext fun _ => by simp [connectionQueries, exposedReplies, eq_comm]

theorem exposedReplies_snoc_in (route : Y → B ⊕ X) (ys : List Y) {y : Y} {x : X}
    (hy : route y = .inr x) : exposedReplies route (ys ++ [y]) = exposedReplies route ys := by
  simp [exposedReplies, List.filterMap_append, hy]

theorem exposedReplies_snoc_out (route : Y → B ⊕ X) (ys : List Y) {y : Y} {b : B}
    (hy : route y = .inl b) : exposedReplies route (ys ++ [y]) = exposedReplies route ys ++ [b] := by
  simp [exposedReplies, List.filterMap_append, hy]

theorem connectionQueries_snoc_in (route : Y → B ⊕ X) (inj : A → X) (us : List A)
    (ys : List Y) {y : Y} {x : X} (hy : route y = .inr x)
    (hd : (connectionQueries route inj us ys).Dom) :
    connectionQueries route inj us (ys ++ [y]) = Part.some x := by
  apply Part.eq_some_iff.mpr
  refine ⟨?_, ?_⟩
  · rw [connectionQueries_dom, exposedReplies_snoc_in route ys hy]
    exact hd
  · simp [connectionQueries, List.getLast?_append, hy]

theorem connectionQueries_snoc_out (route : Y → B ⊕ X) (inj : A → X) (us : List A)
    (ys : List Y) {y : Y} {b : B} (hy : route y = .inl b) :
    connectionQueries route inj us (ys ++ [y]) =
      ((us[(exposedReplies route ys).length + 1]?).map inj : Part X) := by
  apply Part.ext
  intro x
  by_cases hl : (exposedReplies route ys).length + 1 < us.length
  · simp [connectionQueries, exposedReplies_snoc_out route ys hy, List.getLast?_append,
      hy, hl, eq_comm]
  · simp [connectionQueries, exposedReplies_snoc_out route ys hy, List.getLast?_append,
      hy, hl]

/-- A routing environment never receives more exposed replies than requested. -/
theorem Cons.exposedReplies_length_le {route : Y → B ⊕ X} {inj : A → X}
    {us : List A} {h : List (X × Y)} (hc : Cons (connectionQueries route inj us) h) :
    (exposedReplies route (h.map Prod.snd)).length ≤ us.length := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
  · simp [exposedReplies]
  · rw [List.concat_eq_append] at hc ⊢
    have hd := Part.dom_iff_mem.mpr ⟨_, (cons_snoc.mp hc).2⟩
    change (exposedReplies route (h.map Prod.snd)).length < us.length at hd
    simp only [List.map_append, List.map_singleton]
    cases he : route z.2 with
    | inl b => rw [exposedReplies_snoc_out route _ he]; simpa using hd
    | inr x => rw [exposedReplies_snoc_in route _ he]; exact hd.le

/-- Observing one existing internal exchange extends the source transcript and
adds exactly its exposed reply. This applies to partial systems as well. -/
theorem exchange_transcript_connection {s : System X Y} {route : Y → B ⊕ X}
    (inj : A → X) (us : List A) {G o G'} (l : Exchange s route G o G') :
    ∀ H x ys b, G = H ++ [x] → o = some b →
      Transcript s (connectionQueries route inj us) H ys →
      x ∈ connectionQueries route inj us ys →
      ∃ ys', Transcript s (connectionQueries route inj us) G' ys' ∧
        exposedReplies route ys' = exposedReplies route ys ++ [b] ∧
        ∃ p y, ys' = p ++ [y] ∧ route y = .inl b := by
  induction l with
  | silent => intro H x ys b he hb; cases hb
  | out G y b' hy hy' =>
    intro H x ys b he hb hr hx
    cases hb
    subst G
    exact ⟨ys ++ [y], Transcript.snoc hr hx hy,
      exposedReplies_snoc_out route ys hy', ys, y, rfl, hy'⟩
  | feed G y x' o G' hy hy' l ih =>
    intro H x ys b he hb hr hx
    subst G
    have hr' := Transcript.snoc hr hx hy
    have hx' : x' ∈ connectionQueries route inj us (ys ++ [y]) := by
      rw [connectionQueries_snoc_in route inj us ys hy' (Part.dom_iff_mem.mpr ⟨x, hx⟩)]
      exact Part.mem_some _
    obtain ⟨zs, hzs, he, hl⟩ := ih (H ++ [x]) x' (ys ++ [y]) b rfl hb hr' hx'
    exact ⟨zs, hzs, by rwa [exposedReplies_snoc_in route ys hy'] at he, hl⟩

/-- The exposed prefixes of a routed transcript are replies of the existing
connection. The second clause extends the same internal history through the
pending exchange; no incompatible histories are combined. -/
theorem transcript_connection {s : System X Y} {route : Y → B ⊕ X}
    {inj : A → X} {us : List A} {xs : List X} {ys : List Y}
    (tr : Transcript s (connectionQueries route inj us) xs ys) :
    Replies (interconnect s route inj) (us.take (exposedReplies route ys).length)
      (exposedReplies route ys) ∧
      ∀ x, x ∈ connectionQueries route inj us ys → ∀ o H,
        Exchange s route (xs ++ [x]) o H →
          Induces s route inj (us.take ((exposedReplies route ys).length + 1)) o H := by
  induction tr with
  | nil =>
    refine ⟨by simp [exposedReplies], ?_⟩
    intro x hx o H l
    cases us with
    | nil => simp [connectionQueries, exposedReplies] at hx
    | cons a us =>
      have he : x = inj a := by simpa [connectionQueries_nil] using hx
      subst x
      simpa [exposedReplies] using Induces.snoc [] a none [] o H Induces.nil l
  | @snoc xs ys x y tr hx hy ih =>
    have hlt : (exposedReplies route ys).length < us.length := (Part.dom_iff_mem.mpr ⟨x, hx⟩)
    cases he : route y with
    | inl b =>
      have r := ih.2 x hx (some b) (xs ++ [x]) (Exchange.out _ y b hy he)
      rw [exposedReplies_snoc_out route ys he]
      simp only [List.length_append, List.length_singleton]
      have ht : us.take ((exposedReplies route ys).length + 1) =
          us.take (exposedReplies route ys).length ++ [us[(exposedReplies route ys).length]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt]; rfl
      refine ⟨?_, ?_⟩
      · rw [ht, replies_snoc]
        exact ⟨ih.1, Part.eq_some_iff.mpr (mem_interconnect.mpr ⟨xs ++ [x], ht ▸ r⟩)⟩
      · intro x' hx' o H l
        have hl : (exposedReplies route ys).length + 1 < us.length := by
          have hd := Part.dom_iff_mem.mpr ⟨x', hx'⟩
          rwa [connectionQueries_dom, exposedReplies_snoc_out route ys he,
            List.length_append, List.length_singleton] at hd
        have hv : x' = inj us[(exposedReplies route ys).length + 1] := by
          simpa [connectionQueries_snoc_out route inj us ys he,
            List.getElem?_eq_getElem hl] using hx'
        subst x'
        rw [List.take_add_one, List.getElem?_eq_getElem hl]
        exact Induces.snoc _ _ _ _ _ _ r l
    | inr z =>
      rw [exposedReplies_snoc_in route ys he]
      refine ⟨ih.1, ?_⟩
      intro x' hx' o H l
      have hv : x' = z := by
        simpa [connectionQueries_snoc_in route inj us ys he hlt] using hx'
      subst x'
      exact ih.2 x hx o H (Exchange.feed _ y z o H hy he l)

theorem replies_of_completed_connection {s : System X Y} {route : Y → B ⊕ X}
    {inj : A → X} {us : List A} {xs : List X} {ys : List Y}
    (tr : Transcript s (connectionQueries route inj us) xs ys)
    (hd : ¬ (connectionQueries route inj us ys).Dom) :
    Replies (interconnect s route inj) us (exposedReplies route ys) := by
  have hr := (transcript_connection tr).1
  rw [List.take_of_length_le (Nat.le_of_not_gt hd)] at hr
  exact hr

/-- Every completed connection prefix can be observed using the same source
history. The next external query is the next element of the supplied sequence. -/
theorem transcript_of_connection_replies {s : System X Y} {route : Y → B ⊕ X}
    {inj : A → X} {us u : List A} {v : List B}
    (hr : Replies (interconnect s route inj) u v) (hu : u <+: us) :
    ∃ H ys, Induces s route inj u v.getLast? H ∧
      Transcript s (connectionQueries route inj us) H ys ∧
      exposedReplies route ys = v ∧
      connectionQueries route inj us ys = (us[v.length]?.map inj : Part X) := by
  induction u using List.reverseRecOn generalizing v with
  | nil =>
    have he : v = [] := List.length_eq_zero_iff.mp hr.length
    subst v
    refine ⟨[], [], Induces.nil, Transcript.nil, rfl, ?_⟩
    rw [connectionQueries_nil]
    cases us <;> rfl
  | append_singleton u a ih =>
    have hv : v ≠ [] := by intro he; have hl := hr.length; simp [he] at hl
    obtain ⟨v, b, rfl⟩ := List.eq_nil_or_concat v |>.resolve_left hv
    rw [List.concat_eq_append] at hr ⊢
    obtain ⟨hr, hb⟩ := replies_snoc.mp hr
    obtain ⟨H, ys, r, tr, hv, hn⟩ := ih hr ((show u <+: u ++ [a] from ⟨[a], rfl⟩).trans hu)
    have hx : inj a ∈ connectionQueries route inj us ys := by
      rw [hn, hr.length]
      obtain ⟨e, he⟩ := hu
      simp [← he]
    obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.eq_some_iff.mp hb)
    obtain ⟨o, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
    have heH := (r₀.det r).2
    subst H₀
    obtain ⟨zs, hzs, he, p, y, hp, hy⟩ :=
      exchange_transcript_connection inj us l H (inj a) ys b rfl rfl tr hx
    have hev : exposedReplies route zs = v ++ [b] := by rwa [hv] at he
    refine ⟨H', zs, by simpa using r', hzs, hev, ?_⟩
    have hl : (exposedReplies route p).length + 1 = (v ++ [b]).length := by
      rw [hp, exposedReplies_snoc_out route p hy] at hev
      simpa using congrArg List.length hev
    rw [hp, connectionQueries_snoc_out route inj us p hy, hl]

/-- Completed transcripts characterize the replies of general system
connection, before any probabilistic lifting. -/
theorem replies_connection_iff {s : System X Y} {route : Y → B ⊕ X}
    {inj : A → X} (us : List A) (vs : List B) :
    Replies (interconnect s route inj) us vs ↔
      ∃ xs ys, Transcript s (connectionQueries route inj us) xs ys ∧
        exposedReplies route ys = vs ∧ ¬ (connectionQueries route inj us ys).Dom := by
  constructor
  · intro hr
    obtain ⟨H, ys, _, tr, he, hn⟩ := transcript_of_connection_replies hr (List.prefix_refl us)
    refine ⟨H, ys, tr, he, ?_⟩
    simp [hn, hr.length]
  · rintro ⟨xs, ys, tr, rfl, hd⟩
    exact replies_of_completed_connection tr hd

/-- A connection preserves inclusion of completed component behavior. Silent
exchanges are irrelevant here: every observed prefix has a completed reply. -/
theorem Replies.interconnect_mono {s t : System X Y}
    (hst : ∀ h y, y ∈ s h → y ∈ t h) {route : Y → B ⊕ X} {inj : A → X}
    {us vs} (hr : Replies (interconnect s route inj) us vs) :
    Replies (interconnect t route inj) us vs := by
  obtain ⟨xs, ys, tr, he, hd⟩ := (replies_connection_iff us vs).mp hr
  exact (replies_connection_iff us vs).mpr
    ⟨xs, ys, tr.of_replies (tr.replies.mono hst), he, hd⟩

/-- The bound on consecutive internal queries bounds the complete component
transcript of each exposed history, even for partial components. -/
theorem Transcript.connection_length_le
    {Xa Ya Xb Yb : Type} {a : System Xa Ya} {b : System Xb Yb} {P : Ya → Prop}
    {route : Two Ya Yb → B ⊕ Two Xa Xb} {inj : A → Two Xa Xb} {n : ℕ}
    (hc : CyclesThrough P route) (hb : ∀ h, (a h).Dom → run P a h ≤ n)
    {us xs ys} (tr : Transcript (pair a b) (connectionQueries route inj us) xs ys)
    (hd : ¬ (connectionQueries route inj us ys).Dom) :
    ys.length ≤ (2 * n + 2) * us.length := by
  have hr := replies_of_completed_connection tr hd
  obtain ⟨H, zs, hi, ht, _, hn⟩ :=
    transcript_of_connection_replies hr (List.prefix_refl us)
  have hstop : ¬ (connectionQueries route inj us zs).Dom := by
    simp [hn, hr.length]
  obtain ⟨rfl, rfl⟩ := tr.eq_of_stopped ht hd hstop
  rw [← ht.length_eq]
  exact hi.length_le_of_cycles hc hb

namespace RandomSystem

open Classical Probability

variable [Fintype X] [Fintype Y] {D : Domain X Y}

/-- The law of completed exposed replies within `n` internal exchanges.
Unfinished or undefined interactions contribute no completed reply. -/
noncomputable def connectionLaw (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n : ℕ) : Distribution (List B) :=
  Distribution.fTransform (fun h => exposedReplies route (h.map Prod.snd))
    ((R.sLaw (connectionQueries route inj us) n).restrict
      fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom)

theorem connectionLaw_nonneg (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n : ℕ) :
    (R.connectionLaw route inj us n).NonNeg :=
  ((sLaw_nonNeg n).restrict _).fTransform _

/-- Every completed internal transcript contributes its probability to its
exposed reply sequence. -/
theorem mass_le_connectionLaw (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n : ℕ) (h : List (X × Y))
    (hc : Cons (connectionQueries route inj us) h) (hn : h.length ≤ n)
    (hd : ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) :
    R h ≤ R.connectionLaw route inj us n (exposedReplies route (h.map Prod.snd)) := by
  unfold connectionLaw
  rw [Distribution.fTransform_apply_eq_mass]
  have hh : ((R.sLaw (connectionQueries route inj us) n).restrict
      (fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom)) h = R h := by
    rw [sLaw_completed_apply, if_pos ⟨hc, hn, hd⟩]
  rw [← hh]
  exact Distribution.apply_le_mass
    ((sLaw_nonNeg n).restrict _) rfl

/-- Connection preserves a finite probabilistic choice among behaviors on
the same admitted domain. -/
theorem connectionLaw_mix {ι : Type} (P : Distribution.ProbDist ι)
    (R : ι → RandomSystem X Y D) (route : Y → B ⊕ X) (inj : A → X)
    (us : List A) (n : ℕ) :
    (mix P R).connectionLaw route inj us n =
      ∑ i ∈ P.1.support, P.1 i • (R i).connectionLaw route inj us n := by
  have completed : ((mix P R).sLaw (connectionQueries route inj us) n).restrict
      (fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) =
      ∑ i ∈ P.1.support, P.1 i • ((R i).sLaw (connectionQueries route inj us) n).restrict
        (fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) := by
    apply Finsupp.ext
    intro h
    simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, sLaw_completed_apply]
    by_cases hd : Cons (connectionQueries route inj us) h ∧ h.length ≤ n ∧
        ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom
    · simp only [if_pos hd, mix_mass]
    · simp only [if_neg hd, mul_zero, Finset.sum_const_zero]
  unfold connectionLaw
  rw [completed, Distribution.fTransform_sum]
  simp only [Distribution.fTransform_smul]

/-- Every completed outcome contains exactly one reply to each exposed input. -/
theorem connectionLaw_length (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n : ℕ) {vs : List B}
    (hv : vs ∈ (R.connectionLaw route inj us n).support) : vs.length = us.length := by
  obtain ⟨h, hh, rfl⟩ := Distribution.mem_support_fTransform _ _ hv
  simp only [Distribution.restrict, Finsupp.support_filter, Finset.mem_filter] at hh
  have hg : Good (connectionQueries route inj us) n h :=
    tSupp_good ((Finsupp.support_onFinset_subset ..) hh.1)
  exact le_antisymm hg.1.exposedReplies_length_le (Nat.le_of_not_gt hh.2)

/-- Compatible, completed observations yield probability distributions. Both
hypotheses are explicit for partial resources. -/
theorem connectionLaw_isProbDist (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n : ℕ)
    (hc : Compatible R (connectionQueries route inj us))
    (hs : ∀ h, Cons (connectionQueries route inj us) h → R h ≠ 0 → h.length = n →
      ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) :
    (R.connectionLaw route inj us n).isProbDist := by
  have he : (R.sLaw (connectionQueries route inj us) n).restrict
      (fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) =
      R.sLaw (connectionQueries route inj us) n := by
    apply Finsupp.ext
    intro h
    rw [Distribution.restrict_apply]
    by_cases hm : R.sLaw (connectionQueries route inj us) n h = 0
    · simp [hm]
    · have hh := (Finsupp.support_onFinset_subset ..) (Finsupp.mem_support_iff.mpr hm)
      obtain ⟨hg, hd⟩ := tSupp_good hh
      have hstop : ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom := by
        rcases hd with hl | ⟨_, hd⟩
        · exact hs h hg (tSupp_possible hh) hl
        · exact hd
      exact if_pos hstop
  unfold connectionLaw
  rw [he]
  exact Distribution.fTransform_isProbDist _ (sLaw_isProbDist hc n)

/-- A sufficient internal bound is immaterial to the completed reply law. -/
theorem connectionLaw_stable (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) {n m : ℕ} (hn : n ≤ m)
    (hb : ∀ h, Cons (connectionQueries route inj us) h → R h ≠ 0 →
      ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom → h.length ≤ n) :
    R.connectionLaw route inj us n = R.connectionLaw route inj us m := by
  unfold connectionLaw
  rw [sLaw_completed_stable R _ hn hb]

/-- Any two sufficient bounds give the same completed law. -/
theorem connectionLaw_eq_of_bounds (R : RandomSystem X Y D) (route : Y → B ⊕ X)
    (inj : A → X) (us : List A) (n m : ℕ)
    (hn : ∀ h, Cons (connectionQueries route inj us) h → R h ≠ 0 →
      ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom → h.length ≤ n)
    (hm : ∀ h, Cons (connectionQueries route inj us) h → R h ≠ 0 →
      ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom → h.length ≤ m) :
    R.connectionLaw route inj us n = R.connectionLaw route inj us m := by
  rcases le_total n m with h | h
  · exact connectionLaw_stable R route inj us h hn
  · exact (connectionLaw_stable R route inj us h hm).symm

/-- On a finite presentation, completed connection probabilities agree with
the existing deterministic connection. The bound concerns the completed
internal transcripts, not the number of samples in the presentation. -/
theorem connectionLaw_eq_mass {ι : Type} (R : RandomSystem X Y D)
    (P : Distribution ι) (hP : P.NonNeg) (systems : ι → System X Y)
    (hR : ∀ h, R h = P.mass (fun s => Replies (systems s) (h.map Prod.fst) (h.map Prod.snd)))
    (route : Y → B ⊕ X) (inj : A → X) (us : List A) (n : ℕ)
    (hbound : ∀ s ∈ P.support, ∀ xs ys,
      Transcript (systems s) (connectionQueries route inj us) xs ys →
      ¬ (connectionQueries route inj us ys).Dom → ys.length ≤ n)
    (vs : List B) :
    connectionLaw R route inj us n vs =
      P.mass (fun s => Replies (interconnect (systems s) route inj) us vs) := by
  classical
  rw [connectionLaw, Distribution.fTransform_apply_eq_mass, Distribution.mass_restrict]
  have he := (sLaw R (connectionQueries route inj us) n).mass_congr
    (P := fun h => exposedReplies route (h.map Prod.snd) = vs ∧
      ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom)
    (Q := fun h => ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom ∧
      exposedReplies route (h.map Prod.snd) = vs) (fun _ => and_comm)
  rw [he, sLaw_completed_eq_mass R P hP systems hR]
  apply P.mass_congr_of_support
  intro s hs
  rw [replies_connection_iff]
  constructor
  · rintro ⟨h, tr, _, hd, hv⟩
    exact ⟨_, _, tr, hv, hd⟩
  · rintro ⟨xs, ys, tr, hv, hd⟩
    have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by rw [tr.length_eq])
    have hy : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by rw [tr.length_eq])
    refine ⟨xs.zip ys, ?_⟩
    rw [hx, hy]
    exact ⟨tr, by simpa only [List.length_zip, tr.length_eq, Nat.min_self]
      using hbound s hs xs ys tr hd, hd, hv⟩

/-- The connection of two independent random systems is observed through one pair of
independent finite presentations, whose samples have every property of the
realizations of possible choices. -/
theorem exists_parallel_connection_presentations
    {X' Y' : Type} [Fintype X'] [Fintype Y'] {D' : Domain X' Y'}
    (R : RandomSystem X Y D) (S : RandomSystem X' Y' D')
    (route : Two Y Y' → B ⊕ Two X X') (inj : A → Two X X') (bound : List A → ℕ)
    (p : System X Y → Prop) (q : System X' Y' → Prop)
    (hp : ∀ g, R.2.isSubprobabilistic.PossibleChoice g → p (realization g).1)
    (hq : ∀ g, S.2.isSubprobabilistic.PossibleChoice g → q (realization g).1)
    (hb : ∀ a b, p a → q b → ∀ us xs ys,
      Transcript (pair a b) (connectionQueries route inj us) xs ys →
      ¬ (connectionQueries route inj us ys).Dom → ys.length ≤ bound us) :
    ∃ P : Distribution.ProbDist {s : System X Y // p s},
      ∃ Q : Distribution.ProbDist {s : System X' Y' // q s}, ∀ us vs,
        (parallel R S).connectionLaw route inj us (bound us) vs =
          (Distribution.prod P.1 Q.1).mass
            (fun st => Replies (interconnect (pair st.1.1 st.2.1) route inj) us vs) := by
  obtain ⟨P, hP, -⟩ := R.2.isSubprobabilistic.exists_presentation (n := D.bound)
    (fun h hl => R.mass_eq_zero_of_bound_lt hl) p hp
  obtain ⟨Q, hQ, -⟩ := S.2.isSubprobabilistic.exists_presentation (n := D'.bound)
    (fun h hl => S.mass_eq_zero_of_bound_lt hl) q hq
  refine ⟨P, Q, fun us vs => ?_⟩
  apply connectionLaw_eq_mass _ (Distribution.prod P.1 Q.1)
    (P.2.1.prod Q.2.1) (fun st => pair st.1.1 st.2.1)
    (parallel_mass_of_presentations R S P.1 Q.1 Subtype.val Subtype.val
      (fun h => (hP h).symm) (fun h => (hQ h).symm))
  intro st _ xs ys tr hd
  exact hb st.1.1 st.2.1 st.1.2 st.2.2 us xs ys tr hd

/-- Deterministic component bounds bound every possible transcript of the
parallel system. -/
theorem parallel_connection_length_le
    {X' Y' : Type} [Fintype X'] [Fintype Y'] {D' : Domain X' Y'}
    (R : RandomSystem X Y D) (S : RandomSystem X' Y' D')
    (route : Two Y Y' → B ⊕ Two X X') (inj : A → Two X X')
    (p : System X Y → Prop) (q : System X' Y' → Prop)
    (hp : ∀ g, R.2.isSubprobabilistic.PossibleChoice g → p (realization g).1)
    (hq : ∀ g, S.2.isSubprobabilistic.PossibleChoice g → q (realization g).1)
    (bound : List A → ℕ)
    (hb : ∀ a b, p a → q b → ∀ us xs ys,
      Transcript (pair a b) (connectionQueries route inj us) xs ys →
      ¬ (connectionQueries route inj us ys).Dom → ys.length ≤ bound us)
    {us h} (hc : Cons (connectionQueries route inj us) h)
    (hm : parallel R S h ≠ 0)
    (hd : ¬ (connectionQueries route inj us (h.map Prod.snd)).Dom) :
    h.length ≤ bound us := by
  rw [parallel_mass] at hm
  split_ifs at hm with hpair
  swap
  · exact (hm rfl).elim
  obtain ⟨a, ha, hra⟩ := R.2.isSubprobabilistic.exists_replies
    (fun h hl => R.mass_eq_zero_of_bound_lt hl) p hp (mul_ne_zero_iff.mp hm).1
  obtain ⟨b, hb', hrb⟩ := S.2.isSubprobabilistic.exists_replies
    (fun h hl => S.mass_eq_zero_of_bound_lt hl) q hq (mul_ne_zero_iff.mp hm).2
  have hr := (replies_pair_iff a b h).mpr ⟨hpair, hra, hrb⟩
  simpa only [List.length_map] using
    hb a b ha hb' us _ _ (transcript_of_cons hc hr) hd

end RandomSystem

end SystemAlgebra

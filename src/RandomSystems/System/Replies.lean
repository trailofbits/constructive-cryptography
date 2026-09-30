import RandomSystems.System.Basic

/-!
# Replies of a deterministic system

A system `s` replies `ys` to the successive queries `xs` when each nonempty prefix of
`xs` receives the corresponding reply. For deterministic systems the completed replies
determine the system, and they are the transcripts of the environment that submits
`xs` in order.

## Main definitions

* `Replies s xs ys`: `s` replies `ys` to the successive queries `xs`

## Main results

* `replies_snoc`, `Replies.reach`, `Reach.exists_replies`: replies extend one query at a
  time, and exist exactly on the reached histories
* `replies_trim_iff`: trimming removes no completed replies
* `replies_congr_of_prefix`: replies to a history depend only on its prefixes
* `IsDDS.eq_of_replies_iff`: completed replies determine a deterministic system
* `transcript_fixedQueries_iff`: replies are the transcripts of fixed queries
* `Replies.suffix_le_run`, `Replies.exists_suffix_run`: consecutive replies with a
  property are counted by `run`
* `trim_dom_of_admission`: exact next-query admission determines a prefix-closed domain
-/

namespace SystemAlgebra

variable {A B : Type}

/-- `s` replies `ys` to the successive queries `xs`. -/
def Replies (s : System A B) (xs : List A) (ys : List B) : Prop :=
  ys.length = xs.length ∧
    ∀ k (hk : k < xs.length) (hk' : k < ys.length), s (xs.take (k + 1)) = Part.some ys[k]

@[simp] theorem replies_nil (s : System A B) : Replies s [] [] :=
  ⟨rfl, fun k hk => absurd hk (by simp)⟩

theorem replies_snoc {s : System A B} {xs : List A} {ys : List B} {x : A} {y : B} :
    Replies s (xs ++ [x]) (ys ++ [y]) ↔ Replies s xs ys ∧ s (xs ++ [x]) = Part.some y := by
  constructor
  · rintro ⟨hl, h⟩
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    refine ⟨⟨hl, fun k hk hk' => ?_⟩, ?_⟩
    · have := h k (by simp; omega) (by simp; omega)
      rwa [List.take_append_of_le_length (by omega), List.getElem_append_left hk'] at this
    · have := h xs.length (by simp) (by simp; omega)
      rw [List.take_of_length_le (by simp)] at this
      rw [List.getElem_append_right (by omega)] at this
      simpa [hl] using this
  · rintro ⟨⟨hl, h⟩, hx⟩
    refine ⟨by simp [hl], fun k hk hk' => ?_⟩
    simp only [List.length_append, List.length_singleton] at hk hk'
    by_cases hkl : k < xs.length
    · rw [List.take_append_of_le_length (by omega), List.getElem_append_left (by omega)]
      exact h k hkl (by omega)
    · have e : k = xs.length := by omega
      subst e
      rw [List.take_of_length_le (by simp), List.getElem_append_right (by omega)]
      simpa [hl] using hx

/-- Systems that agree on the prefixes of `xs` give the same replies to `xs`. -/
theorem replies_congr_of_prefix {s t : System A B} {xs : List A}
    (h : ∀ p, p <+: xs → s p = t p) (ys : List B) :
    Replies s xs ys ↔ Replies t xs ys := by
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨hl, fun k hk hk' => (h _ (List.take_prefix _ _)).symm.trans (hr k hk hk')⟩
  · rintro ⟨hl, hr⟩
    exact ⟨hl, fun k hk hk' => (h _ (List.take_prefix _ _)).trans (hr k hk hk')⟩

theorem Replies.length {s : System A B} {xs ys} (h : Replies s xs ys) : ys.length = xs.length := h.1

theorem Replies.dom {s : System A B} {xs ys} (h : Replies s xs ys) (hne : xs ≠ []) :
    (s xs).Dom := by
  obtain ⟨xs', x, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hne
  have hyn : ys ≠ [] := by intro he; have hl := h.length; simp [he] at hl
  obtain ⟨ys', y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hyn
  have he := (replies_snoc.mp (by simpa [List.concat_eq_append] using h)).2
  rw [List.concat_eq_append, he]
  trivial

/-- A completed transcript contains a reply at every nonempty input prefix. -/
theorem Replies.reach {s : System A B} {xs ys} (hr : Replies s xs ys) : Reach s xs := by
  induction xs using List.reverseRecOn generalizing ys with
  | nil => exact reach_nil s
  | append_singleton xs x ih =>
    have hyn : ys ≠ [] := by intro he; have hl := hr.length; simp [he] at hl
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hyn
    obtain ⟨hr, hy⟩ := replies_snoc.mp (by simpa only [List.concat_eq_append] using hr)
    exact reach_snoc_iff.mpr ⟨ih hr, by rw [hy]; trivial⟩

/-- Extending a partial function preserves all of its completed replies. -/
theorem Replies.mono {s t : System A B} (hst : ∀ h y, y ∈ s h → y ∈ t h)
    {xs ys} (hr : Replies s xs ys) : Replies t xs ys :=
  ⟨hr.length, fun i hi hj => Part.eq_some_iff.mpr
    (hst _ _ (Part.eq_some_iff.mp (hr.2 i hi hj)))⟩

/-- Two systems with the same domain, the first replying only as the second, have the same
transcripts. -/
theorem replies_iff_of_dom_iff {s t : System A B} (hd : ∀ h, (s h).Dom ↔ (t h).Dom)
    (hle : ∀ xs ys, Replies s xs ys → Replies t xs ys) (xs : List A) (ys : List B) :
    Replies s xs ys ↔ Replies t xs ys := by
  refine ⟨hle xs ys, fun hr => ?_⟩
  induction xs using List.reverseRecOn generalizing ys with
  | nil =>
    obtain rfl : ys = [] := List.eq_nil_of_length_eq_zero hr.length
    exact replies_nil s
  | append_singleton xs x ih =>
    rcases List.eq_nil_or_concat ys with rfl | ⟨ys, y, rfl⟩
    · exact absurd hr.length (by simp)
    rw [List.concat_eq_append] at hr ⊢
    obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
    obtain ⟨y', hy'⟩ := Part.dom_iff_mem.mp ((hd _).mpr (by rw [hy]; trivial))
    have hs := replies_snoc.mpr ⟨ih ys hr₀, Part.eq_some_iff.mpr hy'⟩
    obtain rfl : y' = y := Part.some_injective ((replies_snoc.mp (hle _ _ hs)).2.symm.trans hy)
    exact hs

/-- Every reachable input history has its uniquely determined list of replies. -/
theorem Reach.exists_replies {s : System A B} {xs : List A} (hr : Reach s xs) :
    ∃ ys, Replies s xs ys := by
  induction xs using List.reverseRecOn with
  | nil => exact ⟨[], replies_nil s⟩
  | append_singleton xs x ih =>
    obtain ⟨hp, hd⟩ := reach_snoc_iff.mp hr
    obtain ⟨ys, hy⟩ := ih hp
    obtain ⟨y, hy'⟩ := Part.dom_iff_mem.mp hd
    exact ⟨ys ++ [y], replies_snoc.mpr ⟨hy, Part.eq_some_iff.mpr hy'⟩⟩

/-- Trimming removes no completed transcript. -/
theorem replies_trim_iff (s : System A B) (xs : List A) (ys : List B) :
    Replies (trim s) xs ys ↔ Replies s xs ys := by
  constructor
  · rintro ⟨hl, hr⟩
    refine ⟨hl, fun i hi hj => ?_⟩
    have he := hr i hi hj
    unfold trim at he
    split_ifs at he with hp
    · exact he
    · simp at he
  · intro hr
    refine ⟨hr.length, fun i hi hj => ?_⟩
    have hp : Reach s (xs.take (i + 1)) := by
      intro p e he hn
      exact hr.reach p (e ++ xs.drop (i + 1)) (by rw [← List.append_assoc, ← he]; simp) hn
    rw [trim, if_pos hp]
    exact hr.2 i hi hj

/-- For DDSs, complete input/output behavior determines the partial function. -/
theorem IsDDS.eq_of_replies_iff {s t : System A B} (hs : IsDDS s) (ht : IsDDS t)
    (he : ∀ xs ys, Replies s xs ys ↔ Replies t xs ys) : s = t := by
  have step {s t : System A B} (hs : IsDDS s)
      (h : ∀ xs ys, Replies s xs ys → Replies t xs ys) (xs : List A) (y : B)
      (hy : y ∈ s xs) : y ∈ t xs := by
    have hn : xs ≠ [] := fun hnil => hs.1 (hnil ▸ hy.1)
    obtain ⟨ys, hr⟩ := ((hs.reach_iff hn).mpr hy.1).exists_replies
    obtain ⟨xs, x, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left hn
    have hyn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
    obtain ⟨ys, z, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hyn
    simp only [List.concat_eq_append] at hy hr ⊢
    have hy' := Part.eq_some_iff.mp (replies_snoc.mp hr).2
    obtain rfl := Part.mem_unique hy hy'
    exact Part.eq_some_iff.mp (replies_snoc.mp (h _ _ hr)).2
  exact system_ext (fun xs y => ⟨step hs (fun xs ys => (he xs ys).mp) xs y,
    step ht (fun xs ys => (he xs ys).mpr) xs y⟩)

section Transcripts

variable {A B : Type}

theorem Transcript.replies {s : System A B} {e xs ys} (tr : Transcript s e xs ys) :
    Replies s xs ys := by
  induction tr with
  | nil => exact replies_nil s
  | snoc tr hx hy ih => exact replies_snoc.mpr ⟨ih, Part.eq_some_iff.mpr hy⟩

theorem Transcript.of_replies {s t : System A B} {e xs ys} (tr : Transcript s e xs ys)
    (h : Replies t xs ys) : Transcript t e xs ys := by
  induction tr with
  | nil => exact Transcript.nil
  | snoc tr hx hy ih =>
    obtain ⟨h₁, h₂⟩ := replies_snoc.mp h
    exact Transcript.snoc (ih h₁) hx (Part.eq_some_iff.mp h₂)

theorem transcript_fixedQueries_of_replies {s : System A B} :
    ∀ {xs ys} (H : List A), xs <+: H → Replies s xs ys → Transcript s (fixedQueries H) xs ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro ys H _ h
    obtain rfl : ys = [] := List.length_eq_zero_iff.mp h.length
    exact Transcript.nil
  | append_singleton xs x ih =>
    intro ys H hp h
    obtain ⟨ys₀, y, rfl⟩ : ∃ ys₀ y, ys = ys₀ ++ [y] := by
      rcases List.eq_nil_or_concat ys with rfl | ⟨ys₀, y, rfl⟩
      · simpa using h.length
      · exact ⟨ys₀, y, List.concat_eq_append ..⟩
    obtain ⟨h₁, h₂⟩ := replies_snoc.mp h
    refine Transcript.snoc (ih H ((List.prefix_append _ _).trans hp) h₁) ?_ (Part.eq_some_iff.mp h₂)
    obtain ⟨e, rfl⟩ := hp
    simp [fixedQueries, h₁.length]

theorem transcript_fixedQueries_iff {s : System A B} {xs ys} :
    Transcript s (fixedQueries xs) xs ys ↔ Replies s xs ys :=
  ⟨Transcript.replies, transcript_fixedQueries_of_replies xs (List.prefix_refl xs)⟩

end Transcripts

theorem relabel_mono {A B A' B' : Type} {s t : System A B}
    (hst : ∀ h y, y ∈ s h → y ∈ t h) (f : A' → A) (g : B → B') :
    ∀ h y, y ∈ relabel s f g h → y ∈ relabel t f g h := by
  intro h y hy
  obtain ⟨v, hv, he⟩ := (Part.mem_map_iff _).mp hy
  exact (Part.mem_map_iff _).mpr ⟨v, hst _ _ hv, he⟩

/-- The transcripts of a relabeled system are the relabeled transcripts. -/
theorem replies_relabel_iff {A B A' B' : Type} (s : System A B)
    (i : A' ≃ A) (o : B ≃ B') (h : List (A' × B')) :
    Replies (relabel s i o) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies s ((h.map (i.prodCongr o.symm)).map Prod.fst)
        ((h.map (i.prodCongr o.symm)).map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton, Equiv.prodCongr_apply,
      replies_snoc, ih, relabel, Part.eq_some_iff, Part.mem_map_iff]
    have hi : (h.map Prod.fst).map i = (h.map (i.prodCongr o.symm)).map Prod.fst := by
      simp only [List.map_map]; rfl
    have ho (a : B) : o a = y ↔ a = o.symm y := o.eq_symm_apply.symm
    simp only [hi, Prod.map_apply, ho, exists_eq_right]
    rfl

/-- A suffix of replies in `P` is counted by the existing consecutive-reply count. -/
theorem Replies.suffix_le_run {s : System A B} (P : B → Prop)
    (h e : List (A × B))
    (hr : Replies s ((h ++ e).map Prod.fst) ((h ++ e).map Prod.snd))
    (he : ∀ z ∈ e, P z.2) : e.length ≤ run P s ((h ++ e).map Prod.fst) := by
  induction e using List.reverseRecOn with
  | nil => exact Nat.zero_le _
  | append_singleton e z ih =>
    have hr' : Replies s (((h ++ e).map Prod.fst) ++ [z.1])
        (((h ++ e).map Prod.snd) ++ [z.2]) := by simpa using hr
    obtain ⟨hp, hy⟩ := replies_snoc.mp hr'
    have hb := ih hp (fun w hw => he w (List.mem_append_left _ hw))
    have hz := he z (by simp)
    have hm : z.2 ∈ s ((h ++ e).map Prod.fst ++ [z.1]) := by rw [hy]; exact Part.mem_some _
    rw [← List.append_assoc, List.map_append, List.map_cons, List.map_nil,
      run_snoc, if_pos ⟨z.2, hm, hz⟩]
    simpa using Nat.succ_le_succ hb

/-- The consecutive-reply count is realized by an actual suffix of the transcript. -/
theorem Replies.exists_suffix_run {s : System A B} (P : B → Prop)
    (h : List (A × B)) (hr : Replies s (h.map Prod.fst) (h.map Prod.snd)) :
    ∃ p e, h = p ++ e ∧ (∀ z ∈ e, P z.2) ∧ run P s (h.map Prod.fst) = e.length := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨[], [], rfl, by simp, rfl⟩
  | append_singleton h z ih =>
    simp only [List.map_append, List.map_cons, List.map_nil] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hm : z.2 ∈ s (h.map Prod.fst ++ [z.1]) := by rw [hy]; exact Part.mem_some _
    rw [run_snoc]
    by_cases hz : P z.2
    · rw [if_pos ⟨z.2, hm, hz⟩]
      obtain ⟨p, e, he, hp, hn⟩ := ih hr
      refine ⟨p, e ++ [z], by rw [he]; simp, ?_, by simp [hn]⟩
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact hp w hw
      · simpa using (List.mem_singleton.mp hw ▸ hz)
    · rw [if_neg (by rintro ⟨y, hmem, hP⟩; exact hz (Part.mem_unique hmem hm ▸ hP))]
      exact ⟨h ++ [z], [], by simp, by simp, rfl⟩

/-- Exact next-query admission on produced histories determines the whole
prefix-closed domain after trimming. -/
theorem trim_dom_of_admission {A B : Type} {s : System A B} {E : List A → Prop}
    (hs₀ : SilentAtEmpty s)
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p)
    (hs : ∀ h x ys, Replies s h ys → ((s (h ++ [x])).Dom ↔ E (h ++ [x]))) :
    ∀ h, (trim s h).Dom ↔ E h := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    simp only [trim, reach_nil, if_true, hE.1, iff_false]
    exact hs₀
  | append_singleton h x ih =>
    constructor
    · intro hd
      have hr : Reach s (h ++ [x]) := by
        by_contra hr
        simp [trim, hr] at hd
      obtain ⟨ys, hy⟩ := (reach_snoc_iff.mp hr).1.exists_replies
      exact (hs h x ys hy).mp (reach_snoc_iff.mp hr).2
    · intro hd
      have hr : Reach s h := by
        by_cases hn : h = []
        · rw [hn]; exact reach_nil s
        · have ht := ih.mpr (hE.2 ⟨[x], rfl⟩ hn hd)
          by_contra hr
          simp [trim, hr] at ht
      obtain ⟨ys, hy⟩ := hr.exists_replies
      rw [trim_snoc_of_reach hr]
      exact (hs h x ys hy).mpr hd

end SystemAlgebra

import RandomSystems.Converter.ResourceAttachment

/-!
# Admissible histories in attachment

On a completed interaction every converter input is admitted by its preceding output.
Restricting a converter to its admissible histories therefore leaves its attachment
unchanged.

## Main results

* `resource_call_reply`: a completed call replies at its outside label and leaves the
  converter idle
* `replies_apply_canon`, `trim_apply_canon`: canonical restriction does not change an
  attachment
-/

namespace SystemAlgebra

open Classical

variable {O J : Type} {U V : O → Type} {X Y : J → Type}
  {α c : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y} {b : ℕ}

/-- A successful call returns at its outside label and leaves the converter idle. -/
theorem resource_call_reply (hα : IsDDC b α) (hR : RepliesAtQueriedInterface R)
    {G o' G'} (l : Exchange (pair α R) resourceRoute G o' G') :
    ∀ o, AlongCall (ι := id) α o G → ∀ w, o' = some w →
      w.1 = o ∧ AlongIdle (ι := id) α G' := by
  induction l with
  | silent G hd => intro o hG w hw; cases hw
  | out G y w hy hr =>
    intro o hG w' hw'
    cases hw'
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨(_ | ⟨⟩), i⟩, v⟩
      · cases hr
        have hi := hα.replies _ _ i hv rfl
        rw [hlo] at hi
        refine ⟨Option.some.inj hi.symm, ?_⟩
        refine ⟨by simpa using ha, fun _ => ?_, fun j => ?_⟩
        · simpa using Part.dom_iff_mem.mpr ⟨_, hv⟩
        · simp only [restrict_none_snoc_left, replyLabel_of_mem _ hv]
          intro he
          cases he
      · cases hr
    · rw [pair_right] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      cases hr
  | feed G y x' o' G'' hy hr l ih =>
    intro o hG w hw
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, ha, hq, hlo⟩
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨(_ | ⟨⟩), i⟩, v⟩
      · cases hr
      · cases hr
        apply ih o (Or.inr ⟨_, i, v, rfl, ?_, ?_, ?_⟩) w hw
        · simpa using ha
        · simpa using hv
        · simpa using hlo
    · rw [pair_right] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨i, v⟩
      have hi := hR _ _ _ hv
      change i = j at hi
      subst i
      cases hr
      apply ih o (Or.inl ⟨_, _, rfl, ?_, ?_⟩) w hw
      · rw [restrict_none_snoc_right]
        refine admissible_snoc.mpr ⟨ha, fun _ => Part.dom_iff_mem.mpr ⟨_, hq⟩, ?_⟩
        simp only [Admits, replyLabel_of_mem _ hq, admitAfter]
      · rw [restrict_none_snoc_right, lastOuter_snoc]
        simpa only [outerOf, Option.none_or] using hlo

/-- Canonicalization preserves a call, including a rejected resource query or a
converter that stops. -/
theorem resource_call_canon (hR : RepliesAtQueriedInterface R)
    {G o' G'} (l : Exchange (pair (canon c) R) resourceRoute G o' G') :
    ∀ o, AlongCall (ι := id) (canon c) o G →
      Exchange (pair c R) resourceRoute G o' G' := by
  induction l with
  | silent G hd =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · refine Exchange.silent _ ?_
      rw [pair_left, Part.map_Dom] at hd ⊢
      rwa [canon_of_admissible ((admissible_canon_iff _).mp ha)] at hd
    · exact Exchange.silent _ (by rw [pair_right] at hd ⊢; exact hd)
  | out G y w hy hr =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · refine Exchange.out _ y w ?_ hr
      rw [pair_left] at hy ⊢
      rwa [canon_of_admissible ((admissible_canon_iff _).mp ha)] at hy
    · exact Exchange.out _ y w (by rw [pair_right] at hy ⊢; exact hy) hr
  | feed G y x' o' G'' hy hr l ih =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, ha, hq, hlo⟩
    · have hy' := hy
      rw [pair_left, canon_of_admissible ((admissible_canon_iff _).mp ha)] at hy'
      rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨(_ | ⟨⟩), i⟩, v⟩
      · cases hr
      · cases hr
        refine Exchange.feed _ _ _ _ _ (by rw [pair_left]; exact hy') rfl
          (ih o (Or.inr ⟨_, i, v, rfl, ?_, ?_, ?_⟩))
        · simpa using ha
        · simpa using hv
        · simpa using hlo
    · have hy' := hy
      rw [pair_right] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨i, v⟩
      have hi := hR _ _ _ hv
      change i = j at hi
      subst i
      cases hr
      refine Exchange.feed _ ⟨some (), ⟨j, v⟩⟩ _ _ _
        (by rw [pair_right]; exact Part.mem_map _ hv) rfl
        (ih o (Or.inl ⟨_, _, rfl, ?_, ?_⟩))
      · rw [restrict_none_snoc_right]
        refine admissible_snoc.mpr ⟨ha, fun _ => Part.dom_iff_mem.mpr ⟨_, hq⟩, ?_⟩
        simp only [Admits, replyLabel_of_mem _ hq, admitAfter]
      · rw [restrict_none_snoc_right, lastOuter_snoc]
        simpa only [outerOf, Option.none_or] using hlo

/-- Every completed raw interaction also uses only legitimate converter histories. -/
theorem replies_apply_canon (hc : IsDDC b (canon c)) (hR : RepliesAtQueriedInterface R)
    (xs : List (Σ o, U o)) (ys : List (Σ o, V o)) :
    Replies (apply (canon c) R) xs ys ↔ Replies (apply c R) xs ys := by
  let F := interconnect (pair (canon c) R) resourceRoute resourceInput
  let T := interconnect (pair c R) resourceRoute resourceInput
  have completed : ∀ xs ys, Replies T xs ys →
      ∃ o H, Induces (pair (canon c) R) resourceRoute resourceInput xs o H ∧
        Induces (pair c R) resourceRoute resourceInput xs o H ∧
        AlongIdle (ι := id) (canon c) H ∧ Replies F xs ys := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil =>
      intro ys hy
      have he : ys = [] := List.length_eq_zero_iff.mp hy.length
      subst ys
      exact ⟨none, [], Induces.nil, Induces.nil,
        ⟨admissible_nil, fun hn => (hn rfl).elim, fun j => by
          change replyLabel (canon c) [] ≠ some ⟨some (), j⟩
          rw [replyLabel, dif_neg hc.dds.1]
          intro he; cases he⟩, replies_nil F⟩
    | append_singleton xs a ih =>
      intro ys hy
      have hn : ys ≠ [] := by intro he; have hl := hy.length; simp [he] at hl
      obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
      rw [List.concat_eq_append] at hy ⊢
      obtain ⟨hp, hy⟩ := replies_snoc.mp hy
      obtain ⟨o, H, hi, hi', hid, hr⟩ := ih ys hp
      obtain ⟨o', H', ht⟩ := hc.converges_resource R (xs ++ [a])
      obtain ⟨o₀, H₀, ht₀, lx⟩ := induces_snoc_iff.mp ht
      obtain ⟨rfl, rfl⟩ := hi.det ht₀
      rcases a with ⟨i, a⟩
      have hcall : AlongCall (ι := id) (canon c) i (H ++ [resourceInput ⟨i, a⟩]) := by
        refine Or.inl ⟨H, _, rfl, admissible_snoc.mpr
          ⟨hid.1, hid.2.1, (admitAfter_of_ne hid.2.2).mpr rfl⟩, ?_⟩
        rw [lastOuter_snoc]
        rfl
      have lx' := resource_call_canon hR lx i hcall
      have ht' := Induces.snoc _ _ _ _ _ _ hi' lx'
      obtain ⟨H'', hty⟩ := mem_interconnect.mp (Part.eq_some_iff.mp hy)
      obtain ⟨ho, _⟩ := ht'.det hty
      change o' = some y at ho
      subst o'
      refine ⟨some y, H', ht, ht', (resource_call_reply hc hR lx i hcall y rfl).2, ?_⟩
      exact replies_snoc.mpr ⟨hr, Part.eq_some_iff.mpr (mem_of_induces_some ht)⟩
  simp only [apply_eq]
  constructor
  · intro hr
    exact hr.interconnect_mono (pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => h))
  · intro hr
    obtain ⟨_, _, _, _, _, h⟩ := completed xs ys hr
    exact h

/-- Canonicalization does not change the partial DDS produced by attachment. -/
theorem trim_apply_canon (hc : IsDDC b (canon c)) (hR : RepliesAtQueriedInterface R) :
    trim (apply (canon c) R) = trim (apply c R) := by
  apply IsDDS.eq_of_replies_iff
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
    (SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq]))
  intro xs ys
  simp only [replies_trim_iff]
  exact replies_apply_canon hc hR xs ys

end SystemAlgebra

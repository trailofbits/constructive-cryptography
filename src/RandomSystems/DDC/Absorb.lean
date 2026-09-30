import RandomSystems.DDC.SingleAlphabet

/-!
# Absorbing a converter into a distinguisher

For a converter `α` attached along `ι` and a distinguisher `D`, the distinguisher
`D ⋄ α` runs `D` and `α` side by side and asks `R` what `α` would ask.

## Main definitions

* `absorbL D α`: the absorbed distinguisher `D ⋄ α`
* `outerCount`, `innerCount`: outside and inside inputs of a converter history

## Main results

* `close_attachL`, `decision_attachL`: `D ▹ (α^ι R) = (D ⋄ α) ▹ R` (law E1)
* `absorbL_isDDD`: `D ⋄ α` is a distinguisher, with bound `n (b + 1)`
* `IsDDC.count_le`: a converter's inside inputs are bounded by its outside inputs
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

variable {X Y K O J : Type}

section Absorb

variable (ι : J → K)

/-- The routing of `D ⋄ α` on `[D, α]`. -/
noncomputable def abRoute :
    Two (Σ p : DPort (Free (alongSet (O := O) ι)), dOut (fun _ => X) p)
        (Σ l : Two O J, twoFam (fun _ : O => Y) (fun _ : J => X) l) →
      (Σ p : DPort K, dOut (fun _ : K => X) p) ⊕
        Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
          (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l)
  | ⟨none, ⟨.start, e⟩⟩ => e.elim
  | ⟨none, ⟨.dec, b⟩⟩ => .inl ⟨.dec, b⟩
  | ⟨none, ⟨.res ⟨⟨none, ⟨none, o⟩⟩, _⟩, x⟩⟩ => .inr ⟨some (), ⟨⟨none, o⟩, x⟩⟩
  | ⟨none, ⟨.res ⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨none, ⟨.res ⟨⟨some (), k⟩, _⟩, x⟩⟩ => .inl ⟨.res k, x⟩
  | ⟨some (), ⟨⟨none, o⟩, y⟩⟩ =>
      .inr ⟨none, ⟨.res ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩, y⟩⟩
  | ⟨some (), ⟨⟨some (), j⟩, x⟩⟩ => .inl ⟨.res (ι j), x⟩

/-- External inputs of `D ⋄ α`: the trigger and replies at free labels go to `D`, replies
at `ι j` go to the inside label `j` of `α`. -/
noncomputable def abInj : (Σ p : DPort K, dIn (fun _ : K => Y) p) →
    Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
      (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l)
  | ⟨.start, u⟩ => ⟨none, ⟨.start, u⟩⟩
  | ⟨.dec, e⟩ => e.elim
  | ⟨.res k, y⟩ =>
      if h : k ∈ Set.range ι then ⟨some (), ⟨⟨some (), Classical.choose h⟩, y⟩⟩
      else ⟨none, ⟨.res ⟨⟨some (), k⟩, h⟩, y⟩⟩

/-- **Absorption** `D ⋄ α`: the distinguisher `D` of `α^ι R` with `α` absorbed. -/
noncomputable def absorbL (D : DDD (Free (alongSet (O := O) ι)) (fun _ => X) (fun _ => Y))
    (α : SingleAlphabetConverter X Y O J) : DDD K (fun _ => X) (fun _ => Y) :=
  interconnect (pair D α) (abRoute ι) (abInj ι)

/-- Every internal cycle of `D ⋄ α` passes through `D`: `α` answers `D` or leaves. -/
theorem abRoute_cyclesThrough : CyclesThrough (fun _ => True) (abRoute (X := X) (Y := Y) (O := O) ι) := by
  refine ⟨fun _ h => absurd trivial h, fun y _ => ?_, fun y => ?_⟩
  · rcases y with ⟨_ | _ | ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, v⟩
    · exact v.elim
    · exact Or.inl ⟨_, rfl⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · exact Or.inr ⟨_, rfl⟩
      · exact absurd (inside_mem_alongSet ι o) h
    · exact Or.inl ⟨_, rfl⟩
  · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩

/-- The trigger of `D ▹ (α^ι R)`, read as the trigger of `(D ⋄ α) ▹ R`. -/
def e1In : (Σ l : Free (closeSet (Free (alongSet (O := O) ι))),
      twoFam (dIn (fun _ => Y)) (fun _ => X) l.1) →
    Σ l : Free (closeSet K), twoFam (dIn (fun _ : K => Y)) (fun _ : K => X) l.1
  | ⟨⟨⟨none, .start⟩, _⟩, u⟩ => ⟨⟨⟨none, .start⟩, id⟩, u⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

/-- The decision of `(D ⋄ α) ▹ R`, read as a decision of `D ▹ (α^ι R)`. -/
def e1Out : (Σ l : Free (closeSet K), twoFam (dOut (fun _ : K => X)) (fun _ : K => Y) l.1) →
    Σ l : Free (closeSet (Free (alongSet (O := O) ι))),
      twoFam (dOut (fun _ => X)) (fun _ => Y) l.1
  | ⟨⟨⟨none, .start⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .dec⟩, _⟩, b⟩ => ⟨⟨⟨none, .dec⟩, id⟩, b⟩
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

variable {ι} {b : ℕ}

/-- **E1.** `D ▹ (α^ι R) = (D ⋄ α) ▹ R`, for a terminating distinguisher and a converter. -/
theorem close_attachL (D : DDD (Free (alongSet (O := O) ι)) (fun _ => X) (fun _ => Y))
    (α : SingleAlphabetConverter X Y O J) (R : SingleAlphabetSystem X Y K) (hD : Terminating D) (hα : IsResponsiveDDC b α) :
    close D (attachL ι α R) = relabel (close (absorbL ι D α) R) (e1In ι) (e1Out ι) := by
  rw [close_eq, close_eq]
  unfold absorbL attachL
  rw [pair_relabel_right, interconnect_relabel, attachAlong_eq,
    pair_interconnect_right D (hα.converges_along R), interconnect_interconnect, pair_assoc',
    interconnect_relabel,
    pair_interconnect_left (converges_pair_of_terminating (abRoute_cyclesThrough ι) hD),
    interconnect_interconnect, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | _ | ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, v⟩
      · exact v.elim
      · rfl
      · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
        · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
            connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
            closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting]
        · exact absurd (inside_mem_alongSet ι o) h
      · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
          connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
          closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting]
    · rcases o with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
          connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
          closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting]
      · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
          connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
          closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting, image_mem_alongSet]
    · rcases o with ⟨k, y⟩
      by_cases hk : k ∈ Set.range ι
      · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
          connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
          closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting, hk,
          (sys_mem_alongSet_iff (O := O) ι k).mpr hk, liftC]
      · simp [routeComp, routeRight, routeOpt, injOpt, twoMap, twoAssoc, twoAssoc', alongRoute,
          connectRoute_of_mem, connectRoute_of_not_mem, joinOut, splitIn, alongInj, connectInj,
          closeRoute, freeIn, freeOut, abRoute, abInj, e1Out, alongRouting, hk,
          sys_not_mem_alongSet (O := O) ι hk]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟨⟩⟩, z⟩, hz⟩, v⟩
    · rcases z with _ | _ | i
      · rfl
      · exact v.elim
      · exact absurd (res_mem_closeSet i) hz
    · exact absurd (sys_mem_closeSet z) hz

/-- The decision of `D ▹ (α^ι R)` is the decision of `(D ⋄ α) ▹ R`. -/
theorem decision_attachL (D : DDD (Free (alongSet (O := O) ι)) (fun _ => X) (fun _ => Y))
    (α : SingleAlphabetConverter X Y O J) (R : SingleAlphabetSystem X Y K) (hD : Terminating D) (hα : IsResponsiveDDC b α) (c : Bool) :
    decOut c ∈ close D (attachL ι α R) [startIn] ↔ decOut c ∈ close (absorbL ι D α) R [startIn] := by
  rw [close_attachL D α R hD hα]
  simp only [relabel, List.map_cons, List.map_nil]
  constructor
  · intro h
    obtain ⟨z, hz, e⟩ := Part.mem_map_iff _ |>.mp h
    obtain ⟨c', rfl⟩ := eq_decOut z
    obtain rfl : c' = c := by simpa [e1Out, decOut] using e
    exact hz
  · intro h
    exact Part.mem_map_iff _ |>.mpr ⟨_, h, rfl⟩

end Absorb

/-! ## A converter's inside inputs are bounded by its outside inputs -/

section Count

variable {U V : O → Type} {Xi Yi : J → Type}

/-- The number of outside inputs of a converter history. -/
def outerCount (h : List (Σ l, twoFam U Yi l)) : ℕ := h.countP (fun z => decide (z.1.1 = none))

/-- The number of inside inputs of a converter history. -/
def innerCount (h : List (Σ l, twoFam U Yi l)) : ℕ := h.countP (fun z => !decide (z.1.1 = none))

theorem outerCount_add_innerCount (h : List (Σ l, twoFam U Yi l)) :
    outerCount h + innerCount h = h.length := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    by_cases hz : z.1.1 = none <;>
      simp [outerCount, innerCount, List.countP_cons, hz] at ih ⊢ <;> omega

theorem outerCount_snoc (h : List (Σ l, twoFam U Yi l)) (z : Σ l, twoFam U Yi l) :
    outerCount (h ++ [z]) = outerCount h + if z.1.1 = none then 1 else 0 := by
  simp [outerCount, List.countP_append]

theorem innerCount_snoc (h : List (Σ l, twoFam U Yi l)) (z : Σ l, twoFam U Yi l) :
    innerCount (h ++ [z]) = innerCount h + if z.1.1 = none then 0 else 1 := by
  by_cases hz : z.1.1 = none <;> simp [innerCount, List.countP_append, hz]

variable {b : ℕ} {α : InsideOutsideSystem O J U V Xi Yi}

theorem replyLabel_nil_of_silentAtEmpty (hα : IsDDC b α) : replyLabel α [] = none := by
  have h := hα.dds.1
  simp only [SilentAtEmpty] at h
  simp [replyLabel, h]

/-- Inside inputs of an answered history: each outside call is followed by at most `b`
inside calls. The first component is the invariant while an inside call is open. -/
theorem IsDDC.count_le (hα : IsDDC b α) :
    ∀ h, (α h).Dom → ∀ y ∈ α h,
      (IsInside y → innerCount h + 1 + b ≤ b * outerCount h + insideRun α h) ∧
      (¬ IsInside y → innerCount h ≤ b * outerCount h) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro hd; exact absurd hd hα.dds.1
  | append_singleton h₀ z ih =>
    intro hd y hy
    have hadm := hα.admits h₀ z hd
    have hrun : insideRun α (h₀ ++ [z]) = if IsInside y then insideRun α h₀ + 1 else 0 := by
      rw [insideRun, run_snoc]
      by_cases hi : IsInside y
      · rw [if_pos ⟨y, hy, hi⟩, if_pos hi]; rfl
      · rw [if_neg (fun ⟨y', hy', hi'⟩ => hi (Part.mem_unique hy hy' ▸ hi')), if_neg hi]
    rw [outerCount_snoc, innerCount_snoc, hrun]
    rcases eq_or_ne h₀ [] with rfl | hne
    · have hz : z.1.1 = none := by
        simpa [Admits, replyLabel_nil_of_silentAtEmpty hα, admitAfter] using hadm
      simp only [outerCount, innerCount, List.countP_nil, hz, if_true, insideRun, run_nil]
      constructor
      · intro hi
        simp [hi]
        omega
      · intro hi
        simp [hi]
    · have hd₀ : (α h₀).Dom := hα.dds.2 ⟨[z], rfl⟩ hne hd
      have hy₀ := Part.get_mem hd₀
      have hb := hα.bound h₀ hd₀
      have hl := replyLabel_of_mem α hy₀
      obtain ⟨ih₁, ih₂⟩ := ih hd₀ _ hy₀
      generalize (α h₀).get hd₀ = y₀ at hy₀ hl ih₁ ih₂
      generalize insideRun α h₀ = r at hb ih₁ ih₂ ⊢
      generalize outerCount h₀ = m at ih₁ ih₂ ⊢
      generalize innerCount h₀ = c at ih₁ ih₂ ⊢
      rcases y₀ with ⟨⟨_ | ⟨⟨⟩⟩, l₀⟩, v₀⟩
      · have hz : z.1.1 = none := by simpa [Admits, hl, admitAfter] using hadm
        have ih₂ := ih₂ (by simp [IsInside])
        simp only [hz, if_true, if_false, Nat.mul_succ] at *
        constructor <;> intro hi <;> (try simp only [hi, if_true, if_false]) <;> omega
      · have hz : z.1 = ⟨some (), l₀⟩ := by simpa [Admits, hl, admitAfter] using hadm
        have ih₁ := ih₁ rfl
        simp only [hz, reduceCtorEq, if_false, if_true, Nat.add_zero] at *
        constructor <;> intro hi <;> (try simp only [hi, if_true, if_false]) <;> omega

theorem IsDDC.innerCount_le (hα : IsDDC b α) {h} (hd : (α h).Dom) :
    innerCount h ≤ b * outerCount h := by
  obtain ⟨h₁, h₂⟩ := hα.count_le h hd _ (Part.get_mem hd)
  by_cases hi : IsInside ((α h).get hd)
  · have := h₁ hi; have := hα.bound h hd; omega
  · exact h₂ hi

end Count

/-! ## `D ⋄ α` is a distinguisher -/

section Closure

variable {ι : J → K} {b : ℕ}
  {D : DDD (Free (alongSet (O := O) ι)) (fun _ => X) (fun _ => Y)} {α : SingleAlphabetConverter X Y O J}

variable (α) in
/-- `α` has no open inside call. -/
def AIdle (G : List (Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
    (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l))) : Prop :=
  ∀ j, replyLabel α (restrict (some ()) G) ≠ some ⟨some (), j⟩

variable (D) in
/-- `D` waits for `α` at an outside label. -/
def DWaits (G : List (Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
    (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l))) : Prop :=
  ∃ o h, replyLabel D (restrict none G) = some (.res ⟨⟨none, ⟨none, o⟩⟩, h⟩)

variable (D α) in
/-- Where the last reply `l` of `D ⋄ α` came from. -/
def ARel (l : DPort K) (G : List (Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
    (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l))) : Prop :=
  (l = .dec ∧ replyLabel D (restrict none G) = some .dec ∧ AIdle α G) ∨
  (∃ k h, l = .res k ∧ replyLabel D (restrict none G) = some (.res ⟨⟨some (), k⟩, h⟩) ∧ AIdle α G) ∨
  (∃ j, l = .res (ι j) ∧ replyLabel α (restrict (some ()) G) = some ⟨some (), j⟩ ∧ DWaits D G)

variable (α) in
/-- Outside calls of `α` are calls of `D`, and `α` answered its history. -/
def ACnt (G : List (Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
    (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l))) : Prop :=
  outerCount (restrict (some ()) G) ≤ (restrict none G).length ∧
    (restrict (some ()) G = [] ∨ (α (restrict (some ()) G)).Dom)

theorem ab_exchange {G o G'} (l : Exchange (pair D α) (abRoute ι) G o G') :
    ∀ out, o = some out →
      ((∃ G₁ x, G = G₁ ++ [⟨none, x⟩] ∧ Reach D (restrict none G₁) ∧ AIdle α G₁ ∧ ACnt α G₁) ∨
        (∃ G₁ x, G = G₁ ++ [⟨some (), x⟩] ∧ Reach D (restrict none G₁) ∧
          restrict none G₁ ≠ [] ∧ DWaits D G₁ ∧
          outerCount (restrict (some ()) G) ≤ (restrict none G₁).length ∧
          (restrict (some ()) G₁ = [] ∨ (α (restrict (some ()) G₁)).Dom))) →
      Reach D (restrict none G') ∧ restrict none G' ≠ [] ∧ ARel D α out.1 G' ∧ ACnt α G' := by
  induction l with
  | silent => intro out e; cases e
  | out G y c hy hr =>
    intro out e hm
    obtain rfl : c = out := Option.some_inj.mp e
    rcases hm with ⟨G₁, x, rfl, hDr, hid, hcnt⟩ | ⟨G₁, x, rfl, hDr, hne, hw, hc, hdα⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hr' := reach_snoc_iff.mpr ⟨hDr, Part.dom_iff_mem.mpr ⟨_, hy'⟩⟩
      have hl := replyLabel_of_mem D hy'
      have hcnt' : ACnt α (G₁ ++ [⟨none, x⟩]) := by
        simp only [ACnt, restrict_none_snoc_left, restrict_some_snoc_left, List.length_append,
          List.length_singleton]
        exact ⟨by have := hcnt.1; omega, hcnt.2⟩
      have hid' : AIdle α (G₁ ++ [⟨none, x⟩]) := by
        simpa only [AIdle, restrict_some_snoc_left] using hid
      rcases y' with ⟨_ | _ | ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, v⟩
      · exact v.elim
      · simp only [abRoute, Sum.inl.injEq] at hr
        subst hr
        exact ⟨by simpa using hr', by simp, Or.inl ⟨rfl, by simpa using hl, hid'⟩, hcnt'⟩
      · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
        · exact absurd hr (by simp [abRoute])
        · exact absurd (inside_mem_alongSet ι o) h
      · simp only [abRoute, Sum.inl.injEq] at hr
        subst hr
        exact ⟨by simpa using hr', by simp, Or.inr (Or.inl ⟨l, h, rfl, by simpa using hl, hid'⟩),
          hcnt'⟩
    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · exact absurd hr (by simp [abRoute])
      · simp only [abRoute, Sum.inl.injEq] at hr
        subst hr
        refine ⟨by simpa using hDr, by simpa using hne, Or.inr (Or.inr ⟨l, rfl, ?_, ?_⟩), ?_, ?_⟩
        · simpa only [restrict_some_snoc_right] using replyLabel_of_mem α hy'
        · simpa only [DWaits, restrict_none_snoc_right] using hw
        · simpa only [restrict_none_snoc_right] using hc
        · exact Or.inr (by simpa only [restrict_some_snoc_right] using Part.dom_iff_mem.mpr ⟨_, hy'⟩)
  | feed G y x' o G'' hy hr _ ih =>
    intro out e hm
    rcases hm with ⟨G₁, x, rfl, hDr, hid, hcnt⟩ | ⟨G₁, x, rfl, hDr, hne, hw, hc, hdα⟩
    · rw [pair_left] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hr' := reach_snoc_iff.mpr ⟨hDr, Part.dom_iff_mem.mpr ⟨_, hy'⟩⟩
      have hl := replyLabel_of_mem D hy'
      rcases y' with ⟨_ | _ | ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, v⟩
      · exact v.elim
      · exact absurd hr (by simp [abRoute])
      · rcases l with ⟨_ | ⟨⟨⟩⟩, o'⟩
        · simp only [abRoute, Sum.inr.injEq] at hr
          subst hr
          refine ih out e (Or.inr ⟨_, _, rfl, by simpa using hr', by simp, ⟨o', h, by simpa using hl⟩,
            ?_, ?_⟩)
          · simp only [restrict_some_snoc_right, restrict_some_snoc_left, restrict_none_snoc_left,
              outerCount_snoc, List.length_append, List.length_singleton, if_true]
            have := hcnt.1
            omega
          · simpa only [restrict_some_snoc_left] using hcnt.2
        · exact absurd (inside_mem_alongSet ι o') h
      · exact absurd hr (by simp [abRoute])
    · rw [pair_right] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp only [abRoute, Sum.inr.injEq] at hr
        subst hr
        refine ih out e (Or.inl ⟨_, _, rfl, by simpa using hDr, ?_, ?_⟩)
        · intro j hj
          rw [restrict_some_snoc_right, replyLabel_of_mem α hy'] at hj
          simp at hj
        · refine ⟨by simpa only [restrict_none_snoc_right] using hc, Or.inr ?_⟩
          simpa only [restrict_some_snoc_right] using Part.dom_iff_mem.mpr ⟨_, hy'⟩
      · exact absurd hr (by simp [abRoute])

variable (D α) in
/-- The invariant of `D ⋄ α` along an external history `u` and internal history `H`. -/
def AbInv (u : List (Σ p : DPort K, dIn (fun _ : K => Y) p))
    (H : List (Two (Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p)
      (Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l))) : Prop :=
  (∃ o, Induces (pair D α) (abRoute ι) (abInj ι) u o H) ∧ Reach D (restrict none H) ∧
  (u = [] ↔ restrict none H = []) ∧ (u = [] → H = []) ∧ ACnt α H ∧
  ∀ l, replyLabel (absorbL ι D α) u = some l → ARel D α l H

theorem ab_step (hD : IsDDD D) (hα : IsResponsiveDDC b α) {u H} (inv : AbInv D α u H)
    {z : Σ p : DPort K, dIn (fun _ : K => Y) p} (hr : Reach (absorbL ι D α) (u ++ [z])) :
    (u = [] ↔ z.1 = .start) ∧
      (∀ k, replyLabel (absorbL ι D α) u = some (.res k) → z.1 = .res k) ∧
      replyLabel (absorbL ι D α) u ≠ some .dec ∧ ∃ H', AbInv D α (u ++ [z]) H' := by
  obtain ⟨⟨o, rH⟩, hDr, hemp, hnil, hcnt, hlab⟩ := inv
  obtain ⟨hru, hd⟩ := reach_snoc_iff.mp hr
  have hout := Part.get_mem hd
  obtain ⟨H', r'⟩ := mem_interconnect.mp hout
  obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
  obtain ⟨-, e⟩ := rH.det r₀
  subst e
  have hstart := exchange_start_dom l _ rfl
  have hγu : u ≠ [] → ∃ lab, replyLabel (absorbL ι D α) u = some lab ∧ ARel D α lab H := by
    intro hne
    have hdu := hru u [] (by simp) hne
    exact ⟨_, replyLabel_of_mem _ (Part.get_mem hdu), hlab _ (replyLabel_of_mem _ (Part.get_mem hdu))⟩
  have hαnil : replyLabel α (restrict (some ()) ([] : List (Two (Σ p : DPort
      (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p) (Σ l : Two O J,
        twoFam (fun _ : O => X) (fun _ : J => Y) l)))) = none := by
    simpa using replyLabel_nil_of_silentAtEmpty hα.isDDC
  have hnew : ∀ H', Exchange (pair D α) (abRoute ι) (H ++ [abInj ι z])
      (some ((absorbL ι D α (u ++ [z])).get hd)) H' →
      (Reach D (restrict none H') ∧ restrict none H' ≠ [] ∧
        ARel D α ((absorbL ι D α (u ++ [z])).get hd).1 H' ∧ ACnt α H') →
      ∃ H', AbInv D α (u ++ [z]) H' := by
    intro H' l' ⟨h1, h2, h3, h4⟩
    refine ⟨H', ⟨_, induces_snoc_iff.mpr ⟨_, _, rH, l'⟩⟩, h1,
      ⟨fun e => absurd e (by simp), fun e => absurd e h2⟩, fun e => absurd e (by simp), h4,
      fun lab hl => ?_⟩
    rw [replyLabel_of_mem _ hout] at hl
    cases hl
    exact h3
  -- inputs for `D`
  have hDdir : ∀ x : Σ p : DPort (Free (alongSet (O := O) ι)), dIn (fun _ => Y) p,
      abInj (X := X) (O := O) ι z = ⟨none, x⟩ → (x.1 = .start ↔ z.1 = .start) →
      (∀ lab, x.1 = .res lab → ∃ k h, lab = ⟨⟨some (), k⟩, h⟩ ∧ z.1 = .res k) →
      (u = [] ↔ z.1 = .start) ∧
      (∀ k, replyLabel (absorbL ι D α) u = some (.res k) → z.1 = .res k) ∧
      replyLabel (absorbL ι D α) u ≠ some .dec ∧ ∃ H', AbInv D α (u ++ [z]) H' := by
    intro x hx hxs hxr
    rw [hx, pair_left] at hstart
    have hDr' : Reach D (restrict none H ++ [x]) := reach_snoc_iff.mpr ⟨hDr, by simpa using hstart⟩
    have htrig := hD.2.2.1 _ _ hDr'
    have hres := fun i => hD.2.2.2.1 _ _ i hDr'
    have hdec := hD.2.2.2.2 _ _ hDr'
    -- the label of the last reply of `D ⋄ α`
    have hcases : ∀ lab, replyLabel (absorbL ι D α) u = some lab →
        ∃ k, lab = .res k ∧ z.1 = .res k ∧ AIdle α H := by
      intro lab hl
      rcases hlab lab hl with ⟨rfl, hdD, -⟩ | ⟨k, h, rfl, hdD, hid⟩ | ⟨j, rfl, -, o, h, hdD⟩
      · exact absurd hdD hdec
      · obtain ⟨k', h', e, hz⟩ := hxr _ (hres _ hdD)
        obtain rfl : k = k' := by simpa using congrArg (fun p => p.1) e
        exact ⟨k, rfl, hz, hid⟩
      · obtain ⟨k', h', e, -⟩ := hxr _ (hres _ hdD)
        simp at e
    have hid : AIdle α H := by
      rcases eq_or_ne u [] with rfl | hne
      · rw [hnil rfl]; intro j hj; rw [hαnil] at hj; cases hj
      · obtain ⟨lab, hl, -⟩ := hγu hne
        obtain ⟨_, _, _, h⟩ := hcases lab hl
        exact h
    refine ⟨hemp.trans (htrig.trans hxs), fun k hk => ?_, fun hk => ?_, ?_⟩
    · obtain ⟨k', e, hz, -⟩ := hcases _ hk
      cases e
      exact hz
    · obtain ⟨k', e, -⟩ := hcases _ hk
      cases e
    · have l' := l
      rw [hx] at l'
      exact hnew _ l (ab_exchange l' _ rfl (Or.inl ⟨H, x, rfl, hDr, hid, hcnt⟩))
  rcases z with ⟨_ | _ | k, v⟩
  · exact hDdir ⟨.start, v⟩ rfl (by simp) (fun lab e => by cases e)
  · exact v.elim
  · by_cases hk : k ∈ Set.range ι
    swap
    · refine hDdir ⟨.res ⟨⟨some (), k⟩, hk⟩, v⟩ (by simp [abInj, hk]) (by simp) ?_
      intro lab e
      cases e
      exact ⟨k, hk, rfl, rfl⟩
    -- a reply to an inside call of `α`
    have hx : abInj (X := X) (O := O) ι ⟨.res k, v⟩ = ⟨some (), ⟨⟨some (), Classical.choose hk⟩, v⟩⟩ := by
      simp [abInj, hk]
    rw [hx, pair_right] at hstart
    have hadm := hα.admits _ _ (by simpa using hstart)
    obtain ⟨j, hj, rfl⟩ : ∃ j, replyLabel α (restrict (some ()) H) = some ⟨some (), j⟩ ∧
        Classical.choose hk = j := by
      rcases hl : replyLabel α (restrict (some ()) H) with _ | ⟨_ | ⟨⟨⟩⟩, j⟩
      · simp [Admits, hl, admitAfter] at hadm
      · simp [Admits, hl, admitAfter] at hadm
      · simp only [Admits, hl, admitAfter] at hadm
        exact ⟨j, rfl, by simpa using hadm⟩
    have hk' : ι (Classical.choose hk) = k := Classical.choose_spec hk
    have hne : u ≠ [] := by
      rintro rfl
      rw [hnil rfl, hαnil] at hj
      cases hj
    obtain ⟨lab, hl, hrel⟩ := hγu hne
    obtain ⟨j', rfl, hj', hw⟩ : ∃ j', lab = .res (ι j') ∧
        replyLabel α (restrict (some ()) H) = some ⟨some (), j'⟩ ∧ DWaits D H := by
      rcases hrel with ⟨-, -, hid⟩ | ⟨-, -, -, -, hid⟩ | h
      · exact absurd hj (hid _)
      · exact absurd hj (hid _)
      · exact h
    obtain rfl : j' = Classical.choose hk := by
      rw [hj] at hj'
      simpa using hj'.symm
    refine ⟨⟨fun e => absurd e hne, fun e => by cases e⟩, fun k₁ hk₁ => ?_, fun hk₁ => ?_, ?_⟩
    · rw [hl] at hk₁
      cases hk₁
      simp [hk']
    · rw [hl] at hk₁
      cases hk₁
    · have l' := l
      rw [hx] at l'
      refine hnew _ l (ab_exchange l' _ rfl (Or.inr ⟨H, _, rfl, hDr, (not_congr hemp).mp hne, hw,
        ?_, hcnt.2⟩))
      simp only [restrict_some_snoc_right, outerCount_snoc]
      simpa using hcnt.1

/-- **`D ⋄ α` is a distinguisher** (spec §5.6): with bound `(b + 2) n` for a distinguisher
with bound `n` and a converter with at most `b` consecutive inside calls. Neither the
converter nor the resource needs a finite lifetime. -/
theorem absorbL_inv (hD : IsDDD D) (hα : IsResponsiveDDC b α) :
    ∀ u, Reach (absorbL ι D α) u → ∃ H, AbInv D α u H := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], ⟨none, Induces.nil⟩, reach_nil D, by simp, fun _ => rfl, ⟨by simp [outerCount], Or.inl rfl⟩,
      fun l hl => ?_⟩
    simp [replyLabel, absorbL] at hl
  | append_singleton u z ih =>
    intro hr
    obtain ⟨H, hinv⟩ := ih (reach_snoc_iff.mp hr).1
    exact (ab_step hD hα hinv hr).2.2.2

/-- The explicit query bound of `D ⋄ α`: `(b + 2) n` for a bound `n` of `D`. -/
theorem absorbL_finite (hD : IsDDD D) (hα : IsResponsiveDDC b α) {nD : ℕ} (hnD : Finite nD D) :
    Finite ((b + 2) * nD) (trim (absorbL ι D α)) := by
  set γ := absorbL ι D α
  have inv := absorbL_inv hD hα
  intro u hd
  have hr : Reach γ u := by by_contra hr; simp [trim, hr] at hd
  obtain ⟨H, ⟨o, rH⟩, hDr, -, -, ⟨hc, hdα⟩, -⟩ := inv u hr
  have hlen := rH.length_le
  have hsplit := length_restrict_two H
  have hDn : (restrict none H).length ≤ nD := by
    rcases eq_or_ne (restrict none H) [] with he | hne
    · rw [he]; simp
    · exact hnD _ (hDr _ [] (by simp) hne)
  have hαn : (restrict (some ()) H).length ≤ (b + 1) * outerCount (restrict (some ()) H) := by
    rw [← outerCount_add_innerCount]
    rcases hdα with he | hdα
    · rw [he]; simp [outerCount, innerCount]
    · have := hα.isDDC.innerCount_le hdα
      rw [Nat.succ_mul]
      omega
  have h1 : (b + 1) * outerCount (restrict (some ()) H) ≤ (b + 1) * nD :=
    Nat.mul_le_mul_left _ (hc.trans hDn)
  have h2 : (b + 2) * nD = nD + (b + 1) * nD := by rw [Nat.succ_mul]; omega
  omega

theorem absorbL_isDDD (hD : IsDDD D) (hα : IsResponsiveDDC b α) :
    IsDDD (trim (absorbL ι D α)) := by
  set γ := absorbL ι D α
  have inv := absorbL_inv hD hα
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, trim, γ, absorbL]
  · obtain ⟨nD, hnD⟩ := hD.2.1
    exact ⟨_, absorbL_finite hD hα hnD⟩
  · intro h z hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    exact (ab_step hD hα hinv hr').1
  · intro h z i hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim γ (reach_snoc_iff.mp hr').1]
    exact (ab_step hD hα hinv hr').2.1 i
  · intro h z hr
    have hr' : Reach γ (h ++ [z]) := ((trim_behEq γ).1 _).mp hr
    obtain ⟨H, hinv⟩ := inv h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim γ (reach_snoc_iff.mp hr').1]
    exact (ab_step hD hα hinv hr').2.2.1

end Closure

end SystemAlgebra

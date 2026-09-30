import RandomSystems.Converter.ResourceAttachment
import RandomSystems.DDC.Absorb

/-!
# Absorbing a converter into a distinguisher

A distinguisher connected to all outside interfaces of a converter is again a
distinguisher: its trigger and decision remain exposed, and its interfaces become the
converter's inside interfaces. The connection is the same as in resource attachment, with
the same component histories.

## Main definitions

* `absorbAll D α`: the distinguisher `D` with the converter `α` absorbed

## Main results

* `close_apply`, `decision_apply`: closing the absorbed distinguisher with a resource is
  closing the distinguisher with the attached resource
* `absorbAll_finite`, `absorbAll_isDDD`: absorption keeps the distinguisher conditions
-/

namespace SystemAlgebra

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

def absorptionRoute : Two (Σ p, dOut U p) (Σ l, twoFam V X l) →
    (Σ p, dOut X p) ⊕ Two (Σ p, dIn V p) (Σ l, twoFam U Y l)
  | ⟨none, ⟨.start, e⟩⟩ => e.elim
  | ⟨none, ⟨.dec, b⟩⟩ => .inl ⟨.dec, b⟩
  | ⟨none, ⟨.res o, u⟩⟩ => .inr ⟨some (), ⟨⟨none, o⟩, u⟩⟩
  | ⟨some (), ⟨⟨none, o⟩, v⟩⟩ => .inr ⟨none, ⟨.res o, v⟩⟩
  | ⟨some (), ⟨⟨some (), j⟩, x⟩⟩ => .inl ⟨.res j, x⟩

def absorptionInput : (Σ p, dIn Y p) →
    Two (Σ p, dIn V p) (Σ l, twoFam U Y l)
  | ⟨.start, u⟩ => ⟨none, ⟨.start, u⟩⟩
  | ⟨.dec, e⟩ => e.elim
  | ⟨.res j, y⟩ => ⟨some (), ⟨⟨some (), j⟩, y⟩⟩

/-- Absorbing a converter leaves the trigger, bit, and inside interfaces. -/
noncomputable def absorbAll (D : DDD O U V) (α : InsideOutsideSystem O J U V X Y) : DDD J X Y :=
  interconnect (pair D α) absorptionRoute absorptionInput

theorem cyclesThrough_absorption :
    CyclesThrough (fun _ => True) (absorptionRoute (U := U) (V := V) (X := X) (Y := Y)) := by
  refine ⟨fun _ h => (h trivial).elim, ?_, ?_⟩
  · rintro ⟨_ | _ | o, v⟩ _
    · exact v.elim
    · exact Or.inl ⟨_, rfl⟩
    · exact Or.inr ⟨_, rfl⟩
  · rintro ⟨⟨_ | ⟨⟩, i⟩, v⟩
    · exact Or.inr ⟨_, rfl⟩
    · exact Or.inl ⟨_, rfl⟩

def absorptionCloseInput :
    (Σ l : Free (closeSet O), twoFam (dIn V) U l.1) →
    Σ l : Free (closeSet J), twoFam (dIn Y) X l.1
  | ⟨⟨⟨none, .start⟩, _⟩, u⟩ => ⟨⟨⟨none, .start⟩, start_not_mem_closeSet⟩, u⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => False.elim (h (res_mem_closeSet i))
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => False.elim (h (sys_mem_closeSet i))

def absorptionCloseOutput :
    (Σ l : Free (closeSet J), twoFam (dOut X) Y l.1) →
    Σ l : Free (closeSet O), twoFam (dOut U) V l.1
  | ⟨⟨⟨none, .start⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .dec⟩, _⟩, b⟩ => ⟨⟨⟨none, .dec⟩, dec_not_mem_closeSet⟩, b⟩
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => False.elim (h (res_mem_closeSet i))
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => False.elim (h (sys_mem_closeSet i))

/-- Closing after attachment is closing after absorption. The equation is
the same three-system connection with a different parenthesization. -/
theorem close_apply (D : DDD O U V) (α : InsideOutsideSystem O J U V X Y) (R : InterfaceSystem J X Y)
    (hD : Terminating D) {b : ℕ} (hα : IsDDC b α) :
    close D (apply α R) =
      relabel (close (absorbAll D α) R) absorptionCloseInput absorptionCloseOutput := by
  rw [close_eq, close_eq, apply_eq]
  unfold absorbAll
  rw [pair_interconnect_right D (hα.converges_resource R), interconnect_interconnect,
    pair_assoc', interconnect_relabel,
    pair_interconnect_left (converges_pair_of_terminating cyclesThrough_absorption hD),
    interconnect_interconnect, relabel_interconnect]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟩, y⟩
    · rcases y with ⟨_ | ⟨⟩, y⟩
      · rcases y with ⟨_ | _ | o, v⟩
        · exact v.elim
        · rfl
        · rfl
      · rcases y with ⟨⟨_ | ⟨⟩, i⟩, v⟩ <;> rfl
    · rcases y with ⟨j, y⟩; rfl
  · funext z
    rcases z with ⟨⟨⟨_ | ⟨⟩, l⟩, hl⟩, v⟩
    · rcases l with _ | _ | i
      · rfl
      · exact v.elim
      · exact False.elim (hl (res_mem_closeSet i))
    · exact False.elim (hl (sys_mem_closeSet l))

theorem decision_apply (D : DDD O U V) (α : InsideOutsideSystem O J U V X Y) (R : InterfaceSystem J X Y)
    (hD : Terminating D) {b : ℕ} (hα : IsDDC b α) (c : Bool) :
    decOut c ∈ close D (apply α R) [startIn] ↔
      decOut c ∈ close (absorbAll D α) R [startIn] := by
  rw [close_apply D α R hD hα]
  change _ ∈ (close (absorbAll D α) R [startIn]).map absorptionCloseOutput ↔ _
  constructor
  · intro h
    obtain ⟨z, hz, he⟩ := Part.mem_map_iff _ |>.mp h
    obtain ⟨c', rfl⟩ := eq_decOut z
    obtain rfl : c' = c := by simpa [absorptionCloseOutput, decOut] using he
    exact hz
  · intro h
    exact Part.mem_map_iff _ |>.mpr ⟨_, h, rfl⟩

section Preservation

variable {D : DDD O U V} {α : InsideOutsideSystem O J U V X Y} {b : ℕ}

/-- The converter is between outside calls. -/
def AbsorptionIdle (α : InsideOutsideSystem O J U V X Y)
    (H : List (Two (Σ p, dIn V p) (Σ l, twoFam U Y l))) : Prop :=
  ∀ j, replyLabel α (restrict (some ()) H) ≠ some ⟨some (), j⟩

/-- The distinguisher is waiting for an outside converter reply. -/
def AbsorptionWaits (D : DDD O U V)
    (H : List (Two (Σ p, dIn V p) (Σ l, twoFam U Y l))) : Prop :=
  ∃ o, replyLabel D (restrict none H) = some (.res o)

/-- The exposed output is either the decision or a pending inside query. -/
def AbsorptionReply (D : DDD O U V) (α : InsideOutsideSystem O J U V X Y) (l : DPort J)
    (H : List (Two (Σ p, dIn V p) (Σ l, twoFam U Y l))) : Prop :=
  (l = .dec ∧ replyLabel D (restrict none H) = some .dec ∧ AbsorptionIdle α H) ∨
  ∃ j, l = .res j ∧ replyLabel α (restrict (some ()) H) = some ⟨some (), j⟩ ∧
    AbsorptionWaits D H

/-- Each outside converter call was issued by the distinguisher. -/
def AbsorptionCount (α : InsideOutsideSystem O J U V X Y)
    (H : List (Two (Σ p, dIn V p) (Σ l, twoFam U Y l))) : Prop :=
  outerCount (restrict (some ()) H) ≤ (restrict none H).length ∧
    (restrict (some ()) H = [] ∨ (α (restrict (some ()) H)).Dom)

theorem absorption_exchange {G out G'} (l : Exchange (pair D α) absorptionRoute G out G') :
    ∀ y, out = some y →
      ((∃ H z, G = H ++ [⟨none, z⟩] ∧ Reach D (restrict none H) ∧
          AbsorptionIdle α H ∧ AbsorptionCount α H) ∨
        (∃ H z, G = H ++ [⟨some (), z⟩] ∧ Reach D (restrict none H) ∧
          restrict none H ≠ [] ∧ AbsorptionWaits D H ∧
          outerCount (restrict (some ()) G) ≤ (restrict none H).length ∧
          (restrict (some ()) H = [] ∨ (α (restrict (some ()) H)).Dom))) →
      Reach D (restrict none G') ∧ restrict none G' ≠ [] ∧
        AbsorptionReply D α y.1 G' ∧ AbsorptionCount α G' := by
  induction l with
  | silent => intro y he; cases he
  | out G z c hz hc =>
    intro y he hm
    obtain rfl : c = y := Option.some_inj.mp he
    rcases hm with ⟨H, x, rfl, hd, hi, hn⟩ | ⟨H, x, rfl, hd, hne, hw, hn, ha⟩
    · rw [pair_left] at hz
      obtain ⟨z', hz', rfl⟩ := Part.mem_map_iff _ |>.mp hz
      have hd' := reach_snoc_iff.mpr ⟨hd, hz'.1⟩
      have hl := replyLabel_of_mem D hz'
      rcases z' with ⟨_ | _ | o, v⟩
      · exact v.elim
      · simp only [absorptionRoute, Sum.inl.injEq] at hc
        subst hc
        refine ⟨by simpa using hd', by simp, Or.inl ⟨rfl, by simpa using hl, ?_⟩, ?_⟩
        · simpa only [AbsorptionIdle, restrict_some_snoc_left] using hi
        · simp only [AbsorptionCount, restrict_none_snoc_left, restrict_some_snoc_left,
            List.length_append, List.length_singleton]
          exact ⟨by have := hn.1; omega, hn.2⟩
      · simp [absorptionRoute] at hc
    · rw [pair_right] at hz
      obtain ⟨z', hz', rfl⟩ := Part.mem_map_iff _ |>.mp hz
      rcases z' with ⟨⟨_ | ⟨⟩, j⟩, v⟩
      · simp [absorptionRoute] at hc
      · simp only [absorptionRoute, Sum.inl.injEq] at hc
        subst hc
        refine ⟨by simpa using hd, by simpa using hne,
          Or.inr ⟨j, rfl, ?_, ?_⟩, ?_, ?_⟩
        · simpa only [restrict_some_snoc_right] using replyLabel_of_mem α hz'
        · simpa only [AbsorptionWaits, restrict_none_snoc_right] using hw
        · simpa only [restrict_none_snoc_right] using hn
        · exact Or.inr (by simpa only [restrict_some_snoc_right] using hz'.1)
  | feed G z x out G' hz hc _ ih =>
    intro y he hm
    rcases hm with ⟨H, w, rfl, hd, hi, hn⟩ | ⟨H, w, rfl, hd, hne, hw, hn, ha⟩
    · rw [pair_left] at hz
      obtain ⟨z', hz', rfl⟩ := Part.mem_map_iff _ |>.mp hz
      have hd' := reach_snoc_iff.mpr ⟨hd, hz'.1⟩
      have hl := replyLabel_of_mem D hz'
      rcases z' with ⟨_ | _ | o, v⟩
      · exact v.elim
      · simp [absorptionRoute] at hc
      · simp only [absorptionRoute, Sum.inr.injEq] at hc
        subst hc
        refine ih y he (Or.inr ⟨_, _, rfl, by simpa using hd', by simp,
          ⟨o, by simpa using hl⟩, ?_, ?_⟩)
        · simp only [restrict_some_snoc_right, restrict_some_snoc_left,
            restrict_none_snoc_left, outerCount_snoc, List.length_append,
            List.length_singleton, if_true]
          have := hn.1
          omega
        · simpa only [restrict_some_snoc_left] using hn.2
    · rw [pair_right] at hz
      obtain ⟨z', hz', rfl⟩ := Part.mem_map_iff _ |>.mp hz
      rcases z' with ⟨⟨_ | ⟨⟩, i⟩, v⟩
      · simp only [absorptionRoute, Sum.inr.injEq] at hc
        subst hc
        refine ih y he (Or.inl ⟨_, _, rfl, by simpa using hd, ?_, ?_⟩)
        · intro j hj
          rw [restrict_some_snoc_right, replyLabel_of_mem α hz'] at hj
          simp at hj
        · refine ⟨by simpa only [restrict_none_snoc_right] using hn, Or.inr ?_⟩
          simpa only [restrict_some_snoc_right] using hz'.1
      · simp [absorptionRoute] at hc

/-- The two retained histories and the currently exposed reply. -/
def AbsorptionHistory (D : DDD O U V) (α : InsideOutsideSystem O J U V X Y)
    (u : List (Σ p, dIn Y p))
    (H : List (Two (Σ p, dIn V p) (Σ l, twoFam U Y l))) : Prop :=
  (∃ o, Induces (pair D α) absorptionRoute absorptionInput u o H) ∧
    Reach D (restrict none H) ∧ (u = [] ↔ restrict none H = []) ∧
    (u = [] → H = []) ∧ AbsorptionCount α H ∧
    ∀ l, replyLabel (absorbAll D α) u = some l → AbsorptionReply D α l H

theorem absorption_history_snoc (hD : IsDDD D) (hα : IsDDC b α)
    {u H} (hh : AbsorptionHistory D α u H) {z : Σ p, dIn Y p}
    (hr : Reach (absorbAll D α) (u ++ [z])) :
    (u = [] ↔ z.1 = .start) ∧
      (∀ j, replyLabel (absorbAll D α) u = some (.res j) → z.1 = .res j) ∧
      replyLabel (absorbAll D α) u ≠ some .dec ∧
      ∃ H', AbsorptionHistory D α (u ++ [z]) H' := by
  obtain ⟨⟨o, rH⟩, hDr, hemp, hnil, hcnt, hlab⟩ := hh
  obtain ⟨hru, hd⟩ := reach_snoc_iff.mp hr
  have hout := Part.get_mem hd
  obtain ⟨H', r'⟩ := mem_interconnect.mp hout
  obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
  obtain ⟨_, he⟩ := rH.det r₀
  subst he
  have hstart := exchange_start_dom l _ rfl
  have hlast : u ≠ [] → ∃ lab, replyLabel (absorbAll D α) u = some lab ∧
      AbsorptionReply D α lab H := by
    intro hne
    have hdu := hru u [] (by simp) hne
    exact ⟨_, replyLabel_of_mem _ (Part.get_mem hdu),
      hlab _ (replyLabel_of_mem _ (Part.get_mem hdu))⟩
  have hnew : ∀ H', Exchange (pair D α) absorptionRoute (H ++ [absorptionInput z])
      (some ((absorbAll D α (u ++ [z])).get hd)) H' →
      (Reach D (restrict none H') ∧ restrict none H' ≠ [] ∧
        AbsorptionReply D α ((absorbAll D α (u ++ [z])).get hd).1 H' ∧
        AbsorptionCount α H') → ∃ H', AbsorptionHistory D α (u ++ [z]) H' := by
    intro H' hl ⟨hd', hn', ho', hc'⟩
    refine ⟨H', ⟨_, induces_snoc_iff.mpr ⟨_, _, rH, hl⟩⟩, hd',
      ⟨fun hn => by simp at hn, fun hn => (hn' hn).elim⟩,
      (fun hn => by simp at hn), hc', fun lab hlabel => ?_⟩
    rw [replyLabel_of_mem _ hout] at hlabel
    cases hlabel
    exact ho'
  rcases z with ⟨_ | _ | j, v⟩
  · rw [absorptionInput, pair_left] at hstart
    have hd' : Reach D (restrict none H ++ [⟨.start, v⟩]) :=
      reach_snoc_iff.mpr ⟨hDr, by simpa using hstart⟩
    have hu : u = [] := hemp.mpr ((hD.2.2.1 _ _ hd').mpr rfl)
    subst u
    have hH := hnil rfl
    subst H
    refine ⟨by simp, ?_, ?_, ?_⟩
    · intro k hk
      simp [replyLabel, absorbAll] at hk
    · simp [replyLabel, absorbAll]
    · apply hnew _ l
      exact absorption_exchange l _ rfl (Or.inl ⟨[], _, rfl, reach_nil D,
        by simpa [AbsorptionIdle] using (fun j => by
          rw [replyLabel_nil_of_silentAtEmpty hα]; simp : ∀ j, replyLabel α [] ≠ some ⟨some (), j⟩),
        ⟨by simp [outerCount], Or.inl rfl⟩⟩)
  · exact v.elim
  · rw [absorptionInput, pair_right] at hstart
    have hadm := hα.admits _ _ (by simpa using hstart)
    have hj : replyLabel α (restrict (some ()) H) = some ⟨some (), j⟩ := by
      rcases hl : replyLabel α (restrict (some ()) H) with _ | ⟨_ | ⟨⟩, k⟩
      · simp [Admits, hl, admitAfter] at hadm
      · simp [Admits, hl, admitAfter] at hadm
      · simp only [Admits, hl, admitAfter] at hadm
        simpa using congrArg some hadm.symm
    have hne : u ≠ [] := by
      rintro rfl
      rw [hnil rfl] at hj
      simp [replyLabel_nil_of_silentAtEmpty hα] at hj
    obtain ⟨lab, hl, hrel⟩ := hlast hne
    obtain ⟨k, rfl, hk, hw⟩ : ∃ k, lab = .res k ∧
        replyLabel α (restrict (some ()) H) = some ⟨some (), k⟩ ∧ AbsorptionWaits D H := by
      rcases hrel with ⟨_, _, hi⟩ | h
      · exact False.elim (hi j hj)
      · exact h
    obtain rfl : k = j := by rw [hj] at hk; simpa using hk.symm
    refine ⟨⟨fun he => (hne he).elim, fun he => by cases he⟩, ?_, ?_, ?_⟩
    · intro k hk
      rw [hl] at hk
      cases hk
      rfl
    · rw [hl]
      simp
    · apply hnew _ l
      apply absorption_exchange l _ rfl
      refine Or.inr ⟨H, _, rfl, hDr, (not_congr hemp).mp hne, hw, ?_, hcnt.2⟩
      simp only [absorptionInput, restrict_some_snoc_right, outerCount_snoc]
      simpa using hcnt.1

theorem absorbAll_history (hD : IsDDD D) (hα : IsDDC b α) :
    ∀ u, Reach (absorbAll D α) u → ∃ H, AbsorptionHistory D α u H := by
  intro u
  induction u using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨[], ⟨none, Induces.nil⟩, reach_nil D, by simp, fun _ => rfl,
      ⟨by simp [outerCount], Or.inl rfl⟩, fun lab hl => ?_⟩
    simp [replyLabel, absorbAll] at hl
  | append_singleton u z ih =>
    intro hr
    obtain ⟨H, hh⟩ := ih (reach_snoc_iff.mp hr).1
    exact (absorption_history_snoc hD hα hh hr).2.2.2

/-- A distinguisher with bound `n` absorbs a `b`-bounded converter with a
uniform bound `(b+2)*n`; neither the resource nor the converter has a finite lifetime. -/
theorem absorbAll_finite (hD : IsDDD D) (hα : IsDDC b α)
    {n : ℕ} (hn : Finite n D) : Finite ((b + 2) * n) (trim (absorbAll D α)) := by
  intro u hd
  have hr : Reach (absorbAll D α) u := by
    by_contra hr
    simp [trim, hr] at hd
  obtain ⟨H, ⟨o, rH⟩, hDr, _, _, ⟨hc, hdα⟩, _⟩ := absorbAll_history hD hα u hr
  have hlen := rH.length_le
  have hsplit := length_restrict_two H
  have hDn : (restrict none H).length ≤ n := by
    rcases eq_or_ne (restrict none H) [] with he | hne
    · rw [he]; simp
    · exact hn _ (hDr _ [] (by simp) hne)
  have hαn : (restrict (some ()) H).length ≤ (b + 1) * outerCount (restrict (some ()) H) := by
    rw [← outerCount_add_innerCount]
    rcases hdα with he | hdα
    · rw [he]; simp [outerCount, innerCount]
    · have := hα.innerCount_le hdα
      rw [Nat.succ_mul]
      omega
  have h1 := Nat.mul_le_mul_left (b + 1) (hc.trans hDn)
  have h2 : (b + 2) * n = n + (b + 1) * n := by rw [Nat.succ_mul]; omega
  omega

/-- Absorbing a heterogeneous converter preserves the distinguisher conditions. -/
theorem absorbAll_isDDD (hD : IsDDD D) (hα : IsDDC b α) :
    IsDDD (trim (absorbAll D α)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, trim, absorbAll]
  · obtain ⟨n, hn⟩ := hD.2.1
    exact ⟨_, absorbAll_finite hD hα hn⟩
  · intro h z hr
    have hr' := ((trim_behEq (absorbAll D α)).1 _).mp hr
    obtain ⟨H, hh⟩ := absorbAll_history hD hα h (reach_snoc_iff.mp hr').1
    exact (absorption_history_snoc hD hα hh hr').1
  · intro h z i hr
    have hr' := ((trim_behEq (absorbAll D α)).1 _).mp hr
    obtain ⟨H, hh⟩ := absorbAll_history hD hα h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim _ (reach_snoc_iff.mp hr').1]
    exact (absorption_history_snoc hD hα hh hr').2.1 i
  · intro h z hr
    have hr' := ((trim_behEq (absorbAll D α)).1 _).mp hr
    obtain ⟨H, hh⟩ := absorbAll_history hD hα h (reach_snoc_iff.mp hr').1
    rw [replyLabel_trim _ (reach_snoc_iff.mp hr').1]
    exact (absorption_history_snoc hD hα hh hr').2.2.1

end Preservation

end SystemAlgebra

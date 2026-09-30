import RandomSystems.DDC.SingleAlphabet

/-!
# Parallel converters and renaming converters

The parallel converter `α ⊗ β` runs `α` and `β` on disjoint interface
families; renaming changes the outside labels of a converter. Both are
converters, and their attachments are the attachments of their components.

## Main definitions

* `renameOut e α`: `α` with its outside labels renamed along `e`
* `tensorRaw α β`: the raw parallel converter `[α, β]`
* `tensorL α β`: the parallel converter `α ⊗ β`, the restriction of
  `[α, β]` to its admissible histories

## Main results

* `canon_isDDC`, `canon_isResponsiveDDC`: criteria for the restriction to
  admissible histories to be a converter
* `IsResponsiveDDC.renameOut`, `attachL_renameOut`: renaming preserves
  converters, and attaching a renamed converter is attaching and renaming
* `IsDDC.tensorL`, `IsResponsiveDDC.tensorL`: `α ⊗ β` is a converter, with
  bound `max b b'`
* `attachL_tensorL`: attaching `α ⊗ β` to a total resource is attaching `β`,
  then `α`
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

section Canon

variable {O J : Type} {U V : O → Type} {Xi Yi : J → Type} {b : ℕ} {c : InsideOutsideSystem O J U V Xi Yi}

theorem canon_dom_iff {h} : (canon c h).Dom ↔ Admissible c h ∧ (c h).Dom := by
  unfold canon
  by_cases ha : Admissible c h
  · simp [ha]
  · simp [ha]

theorem insideRun_canon : ∀ {h}, Admissible c h → insideRun (canon c) h = insideRun c h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton h z ih =>
    intro ha
    simp only [insideRun, run_snoc] at ih ⊢
    rw [ih ha.of_append, canon_of_admissible ha]

/-- **A criterion for partial converters.** Restricting a system to its admissible
histories gives a DDC when it is bounded and replies at the last outside label there. -/
theorem canon_isDDC (h0 : ¬ (c []).Dom)
    (hB : ∀ h, Admissible c h → (c h).Dom → insideRun c h ≤ b)
    (hRep : ∀ h y o, Admissible c h → y ∈ c h → y.1 = ⟨none, o⟩ → lastOuter h = some o) :
    IsDDC b (canon c) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · intro hd
    exact h0 (canon_dom_iff.mp hd).2
  · intro l₁ l₂ hp hne hd
    obtain ⟨ha, hd⟩ := canon_dom_iff.mp hd
    obtain ⟨e, rfl⟩ := hp
    refine canon_dom_iff.mpr ⟨ha.of_append, ?_⟩
    rcases e with _ | ⟨z, e⟩
    · simpa using hd
    · exact (ha l₁ z e rfl).1 hne
  · intro h z hd
    obtain ⟨ha, -⟩ := canon_dom_iff.mp hd
    obtain ⟨ha₀, -, hz⟩ := admissible_snoc.mp ha
    rwa [Admits, replyLabel_canon ha₀]
  · intro h hd
    obtain ⟨ha, hd⟩ := canon_dom_iff.mp hd
    rw [insideRun_canon ha]
    exact hB h ha hd
  · intro h y o hy e
    have hd : (canon c h).Dom := Part.dom_iff_mem.mpr ⟨y, hy⟩
    obtain ⟨ha, -⟩ := canon_dom_iff.mp hd
    rw [canon_of_admissible ha] at hy
    exact hRep h y o ha hy e

/-- **A criterion for converters**: responsiveness on admissible histories in addition. -/
theorem canon_isResponsiveDDC (h0 : ¬ (c []).Dom)
    (hR : ∀ h, Admissible c h → h ≠ [] → (c h).Dom)
    (hB : ∀ h, Admissible c h → (c h).Dom → insideRun c h ≤ b)
    (hRep : ∀ h y o, Admissible c h → y ∈ c h → y.1 = ⟨none, o⟩ → lastOuter h = some o) :
    IsResponsiveDDC b (canon c) := by
  refine isResponsiveDDC_iff.mpr ⟨canon_isDDC h0 hB hRep, fun h ha hne => ?_⟩
  have ha' := (admissible_canon_iff h).mp ha
  exact canon_dom_iff.mpr ⟨ha', hR h ha' hne⟩

end Canon

/-! ## Renaming the outside labels of a converter -/

section Rename

variable {X Y O O' J : Type} (e : O' ≃ O)

def renIn : (Σ l : Two O' J, twoFam (fun _ : O' => X) (fun _ : J => Y) l) →
    Σ l : Two O J, twoFam (fun _ : O => X) (fun _ : J => Y) l
  | ⟨⟨none, o⟩, x⟩ => ⟨⟨none, e o⟩, x⟩
  | ⟨⟨some (), j⟩, y⟩ => ⟨⟨some (), j⟩, y⟩

def renOut : (Σ l : Two O J, twoFam (fun _ : O => Y) (fun _ : J => X) l) →
    Σ l : Two O' J, twoFam (fun _ : O' => Y) (fun _ : J => X) l
  | ⟨⟨none, o⟩, y⟩ => ⟨⟨none, e.symm o⟩, y⟩
  | ⟨⟨some (), j⟩, x⟩ => ⟨⟨some (), j⟩, x⟩

/-- The label map of `renOut`. -/
def renLab : Two O J → Two O' J
  | ⟨none, o⟩ => ⟨none, e.symm o⟩
  | ⟨some (), j⟩ => ⟨some (), j⟩

/-- `α` with its outside labels renamed along `e`. -/
def renameOut (α : SingleAlphabetConverter X Y O J) : SingleAlphabetConverter X Y O' J := relabel α (renIn e) (renOut e)

variable {e}

theorem renOut_fst (y : Σ l : Two O J, twoFam (fun _ : O => Y) (fun _ : J => X) l) :
    (renOut e y).1 = renLab e y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

theorem isInside_renOut (y : Σ l : Two O J, twoFam (fun _ : O => Y) (fun _ : J => X) l) :
    IsInside (renOut e y) ↔ IsInside y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> simp [IsInside, renOut]

variable {α : SingleAlphabetConverter X Y O J}

theorem replyLabel_renameOut (h : List (Σ l : Two O' J, twoFam (fun _ : O' => X) (fun _ : J => Y) l)) :
    replyLabel (renameOut e α) h = (replyLabel α (h.map (renIn e))).map (renLab e) := by
  unfold replyLabel
  by_cases hd : (α (h.map (renIn e))).Dom
  · have hd' : (renameOut e α h).Dom := by simpa [renameOut, relabel] using hd
    rw [dif_pos hd, dif_pos hd']
    exact congrArg some (renOut_fst _)
  · have hd' : ¬ (renameOut e α h).Dom := by simpa [renameOut, relabel] using hd
    rw [dif_neg hd, dif_neg hd']
    rfl

theorem admits_renameOut (h) (z : Σ l : Two O' J, twoFam (fun _ : O' => X) (fun _ : J => Y) l) :
    Admits (renameOut e α) h z ↔ Admits α (h.map (renIn e)) (renIn e z) := by
  unfold Admits
  rw [replyLabel_renameOut]
  rcases replyLabel α (h.map (renIn e)) with _ | ⟨_ | ⟨⟨⟩⟩, l⟩ <;>
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, v⟩ <;> simp [admitAfter, renLab, renIn]

theorem admissible_renameOut : ∀ {h}, Admissible (renameOut e α) h ↔ Admissible α (h.map (renIn e)) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [admissible_snoc, List.map_append, List.map_singleton, admissible_snoc, ih, admits_renameOut]
    simp [renameOut, relabel]

theorem insideRun_renameOut : ∀ h, insideRun (renameOut e α) h = insideRun α (h.map (renIn e)) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    simp only [insideRun, run_snoc, List.map_append, List.map_singleton] at ih ⊢
    rw [ih]
    congr 1
    simp only [renameOut, relabel, Part.mem_map_iff, List.map_append, List.map_singleton]
    exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_renOut y).mp hi⟩,
      fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_renOut y).mpr hi⟩⟩

theorem lastOuter_renIn : ∀ h : List (Σ l : Two O' J, twoFam (fun _ : O' => X) (fun _ : J => Y) l),
    lastOuter (h.map (renIn e)) = (lastOuter h).map e := by
  intro h
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rw [List.map_append, List.map_singleton, lastOuter_snoc, lastOuter_snoc, ih]
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> simp [outerOf, renIn]

/-- **Renaming preserves converters.** -/
theorem IsResponsiveDDC.renameOut {b : ℕ} (hα : IsResponsiveDDC b α) : IsResponsiveDDC b (renameOut e α) := by
  refine ⟨⟨?_, ?_⟩, fun h z hd => ?_, fun h hd => ?_, fun h ha hne => ?_, fun h y o hy hl => ?_⟩
  · simpa [SilentAtEmpty, SystemAlgebra.renameOut, relabel] using hα.dds.1
  · intro l₁ l₂ hp hne hd
    have := hα.dds.2 (hp.map (renIn e)) (by simpa using hne)
      (by simpa [SystemAlgebra.renameOut, relabel] using hd)
    simpa [SystemAlgebra.renameOut, relabel] using this
  · rw [admits_renameOut]
    refine hα.admits _ _ ?_
    simpa [SystemAlgebra.renameOut, relabel] using hd
  · rw [insideRun_renameOut]
    exact hα.bound _ (by simpa [SystemAlgebra.renameOut, relabel] using hd)
  · have := hα.responsive _ (admissible_renameOut.mp ha) (by simpa using hne)
    simpa [SystemAlgebra.renameOut, relabel] using this
  · simp only [SystemAlgebra.renameOut, relabel, Part.mem_map_iff] at hy
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    rcases y₀ with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    · have e₁ : e.symm l = o := by
        simp only [renOut, Sigma.mk.inj_iff, heq_eq_eq, true_and] at hl
        exact hl
      have := hα.replies _ _ l hy₀ rfl
      rw [lastOuter_renIn] at this
      obtain ⟨o', ho', e'⟩ := Option.map_eq_some_iff.mp this
      rw [ho']
      simp only [Option.some.injEq]
      rw [← e₁, ← e']
      simp
    · simp [renOut] at hl

variable {K : Type} (e) (ι : J → K)

/-- The free labels of `(renameOut e α)^ι R` and of `α^ι R`. -/
def renFree : Free (alongSet (O := O') ι) ≃ Free (alongSet (O := O) ι) where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, e o⟩⟩, outside_not_mem_alongSet ι _⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet ι j) h
    | ⟨⟨some (), k⟩, h⟩ => ⟨⟨some (), k⟩, h⟩
  invFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, e.symm o⟩⟩, outside_not_mem_alongSet ι _⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet ι j) h
    | ⟨⟨some (), k⟩, h⟩ => ⟨⟨some (), k⟩, h⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · simp
      · exact absurd (inside_mem_alongSet ι o) h
    · rfl
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · simp
      · exact absurd (inside_mem_alongSet ι o) h
    · rfl

variable {e ι}

/-- **Attaching a renamed converter** is attaching the converter and renaming. -/
theorem attachL_renameOut (α : SingleAlphabetConverter X Y O J) (R : SingleAlphabetSystem X Y K) :
    attachL ι (renameOut e α) R = relabelL (renFree e ι).symm (attachL ι α R) := by
  unfold attachL attachAlong connect pairI renameOut relabelL
  simp only [pair_relabel_left, interconnect_relabel, relabel_interconnect, relabel_relabel]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
          Function.comp_def]
      · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
          Function.comp_def, liftC]
    · rcases o with ⟨k, y⟩
      by_cases hk : k ∈ Set.range ι
      · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
          Function.comp_def, liftC, connectRoute_of_mem, (sys_mem_alongSet_iff (O := O) ι k).mpr hk,
          (sys_mem_alongSet_iff (O := O') ι k).mpr hk, alongRouting]
      · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
          Function.comp_def, liftC, connectRoute_of_not_mem, sys_not_mem_alongSet (O := O) ι hk,
          sys_not_mem_alongSet (O := O') ι hk]
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
          Function.comp_def]
      · exact absurd (inside_mem_alongSet ι o) h
    · simp [twoMap, joinOut, splitIn, renOut, renIn, freeIn, freeOut, renFree, connectInj,
        Function.comp_def]

end Rename

/-! ## The parallel converter -/

section RunZero

variable {O J : Type} {U V : O → Type} {Xi Yi : J → Type}

theorem insideRun_eq_zero_of_outer {c : InsideOutsideSystem O J U V Xi Yi} {h} {o : O}
    (hl : replyLabel c h = some ⟨none, o⟩) : insideRun c h = 0 := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
  · rfl
  · rw [List.concat_eq_append] at hl ⊢
    rw [insideRun, run_snoc, if_neg]
    rintro ⟨y, hy, hi⟩
    rw [replyLabel_of_mem c hy] at hl
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
    · exact absurd hi (by simp [IsInside])
    · simp at hl

end RunZero

section Tensor

variable {O O' J J' : Type}
  {U V : O ⊕ O' → Type} {Xi Yi : J ⊕ J' → Type}

def tIn : (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l) →
    Two (Σ l : Two O J, twoFam (U ∘ Sum.inl) (Yi ∘ Sum.inl) l)
      (Σ l : Two O' J', twoFam (U ∘ Sum.inr) (Yi ∘ Sum.inr) l)
  | ⟨⟨none, .inl o⟩, x⟩ => ⟨none, ⟨⟨none, o⟩, x⟩⟩
  | ⟨⟨none, .inr o⟩, x⟩ => ⟨some (), ⟨⟨none, o⟩, x⟩⟩
  | ⟨⟨some (), .inl j⟩, y⟩ => ⟨none, ⟨⟨some (), j⟩, y⟩⟩
  | ⟨⟨some (), .inr j⟩, y⟩ => ⟨some (), ⟨⟨some (), j⟩, y⟩⟩

def tOut : Two (Σ l : Two O J, twoFam (V ∘ Sum.inl) (Xi ∘ Sum.inl) l)
      (Σ l : Two O' J', twoFam (V ∘ Sum.inr) (Xi ∘ Sum.inr) l) →
    Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam V Xi l
  | ⟨none, ⟨⟨none, o⟩, y⟩⟩ => ⟨⟨none, .inl o⟩, y⟩
  | ⟨none, ⟨⟨some (), j⟩, x⟩⟩ => ⟨⟨some (), .inl j⟩, x⟩
  | ⟨some (), ⟨⟨none, o⟩, y⟩⟩ => ⟨⟨none, .inr o⟩, y⟩
  | ⟨some (), ⟨⟨some (), j⟩, x⟩⟩ => ⟨⟨some (), .inr j⟩, x⟩

def lLab : Two O J → Two (O ⊕ O') (J ⊕ J')
  | ⟨none, o⟩ => ⟨none, .inl o⟩
  | ⟨some (), j⟩ => ⟨some (), .inl j⟩

def rLab : Two O' J' → Two (O ⊕ O') (J ⊕ J')
  | ⟨none, o⟩ => ⟨none, .inr o⟩
  | ⟨some (), j⟩ => ⟨some (), .inr j⟩

/-- `[α, β]` on the joint labels: the raw parallel converter. -/
noncomputable def tensorRaw (α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (Xi ∘ Sum.inl) (Yi ∘ Sum.inl)) (β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xi ∘ Sum.inr) (Yi ∘ Sum.inr)) : InsideOutsideSystem (O ⊕ O') (J ⊕ J') U V Xi Yi :=
  relabel (pair α β) tIn tOut

variable {α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (Xi ∘ Sum.inl) (Yi ∘ Sum.inl)} {β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xi ∘ Sum.inr) (Yi ∘ Sum.inr)}

noncomputable abbrev hA (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :=
  restrict none (h.map tIn)

noncomputable abbrev hB (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :=
  restrict (some ()) (h.map tIn)

theorem tOut_left_fst (y : Σ l : Two O J, twoFam (V ∘ Sum.inl) (Xi ∘ Sum.inl) l) :
    (tOut (V := V) (Xi := Xi) ⟨none, y⟩).1 = lLab y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

theorem tOut_right_fst (y : Σ l : Two O' J', twoFam (V ∘ Sum.inr) (Xi ∘ Sum.inr) l) :
    (tOut (V := V) (Xi := Xi) ⟨some (), y⟩).1 = rLab y.1 := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> rfl

theorem isInside_tOut_left (y : Σ l : Two O J, twoFam (V ∘ Sum.inl) (Xi ∘ Sum.inl) l) :
    IsInside (tOut (V := V) (Xi := Xi) ⟨none, y⟩) ↔ IsInside y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> simp [IsInside, tOut]

theorem isInside_tOut_right (y : Σ l : Two O' J', twoFam (V ∘ Sum.inr) (Xi ∘ Sum.inr) l) :
    IsInside (tOut (V := V) (Xi := Xi) ⟨some (), y⟩) ↔ IsInside y := by
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ <;> simp [IsInside, tOut]

variable {h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)}
  {z : Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l}

theorem tensorRaw_left {a} (hz : tIn z = ⟨none, a⟩) :
    tensorRaw α β (h ++ [z]) = (α (hA h ++ [a])).map (fun y => tOut ⟨none, y⟩) := by
  simp only [tensorRaw, relabel, List.map_append, List.map_singleton, hz, pair_left, Part.map_map]
  rfl

theorem tensorRaw_right {a} (hz : tIn z = ⟨some (), a⟩) :
    tensorRaw α β (h ++ [z]) = (β (hB h ++ [a])).map (fun y => tOut ⟨some (), y⟩) := by
  simp only [tensorRaw, relabel, List.map_append, List.map_singleton, hz, pair_right, Part.map_map]
  rfl

theorem hA_left {a} (hz : tIn z = ⟨none, a⟩) : hA (h ++ [z]) = hA h ++ [a] := by
  show restrict none ((h ++ [z]).map tIn) = restrict none (h.map tIn) ++ [a]
  rw [List.map_append, List.map_singleton, hz, restrict_none_snoc_left]

theorem hB_left {a} (hz : tIn z = ⟨none, a⟩) : hB (h ++ [z]) = hB h := by
  simp only [hB, List.map_append, List.map_singleton, hz]
  exact restrict_some_snoc_left _ _

theorem hA_right {a} (hz : tIn z = ⟨some (), a⟩) : hA (h ++ [z]) = hA h := by
  simp only [hA, List.map_append, List.map_singleton, hz]
  exact restrict_none_snoc_right _ _

theorem hB_right {a} (hz : tIn z = ⟨some (), a⟩) : hB (h ++ [z]) = hB h ++ [a] := by
  show restrict (some ()) ((h ++ [z]).map tIn) = restrict (some ()) (h.map tIn) ++ [a]
  rw [List.map_append, List.map_singleton, hz, restrict_some_snoc_right]

theorem replyLabel_tensorRaw_left {a} (hz : tIn z = ⟨none, a⟩) :
    replyLabel (tensorRaw α β) (h ++ [z]) = (replyLabel α (hA h ++ [a])).map lLab := by
  unfold replyLabel
  rw [tensorRaw_left hz]
  by_cases hd : (α (hA h ++ [a])).Dom
  · rw [dif_pos hd, dif_pos (by simpa using hd)]
    exact congrArg some (tOut_left_fst _)
  · rw [dif_neg hd, dif_neg (by simpa using hd)]
    rfl

theorem replyLabel_tensorRaw_right {a} (hz : tIn z = ⟨some (), a⟩) :
    replyLabel (tensorRaw α β) (h ++ [z]) = (replyLabel β (hB h ++ [a])).map rLab := by
  unfold replyLabel
  rw [tensorRaw_right hz]
  by_cases hd : (β (hB h ++ [a])).Dom
  · rw [dif_pos hd, dif_pos (by simpa using hd)]
    exact congrArg some (tOut_right_fst _)
  · rw [dif_neg hd, dif_neg (by simpa using hd)]
    rfl

theorem insideRun_tensorRaw_left {a} (hz : tIn z = ⟨none, a⟩) :
    insideRun (tensorRaw α β) (h ++ [z]) =
      if ∃ y ∈ α (hA h ++ [a]), IsInside y then insideRun (tensorRaw α β) h + 1 else 0 := by
  rw [insideRun, run_snoc, tensorRaw_left hz]
  congr 1
  simp only [Part.mem_map_iff]
  exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_tOut_left y).mp hi⟩,
    fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_tOut_left y).mpr hi⟩⟩

theorem insideRun_tensorRaw_right {a} (hz : tIn z = ⟨some (), a⟩) :
    insideRun (tensorRaw α β) (h ++ [z]) =
      if ∃ y ∈ β (hB h ++ [a]), IsInside y then insideRun (tensorRaw α β) h + 1 else 0 := by
  rw [insideRun, run_snoc, tensorRaw_right hz]
  congr 1
  simp only [Part.mem_map_iff]
  exact propext ⟨fun ⟨_, ⟨y, hy, rfl⟩, hi⟩ => ⟨y, hy, (isInside_tOut_right y).mp hi⟩,
    fun ⟨y, hy, hi⟩ => ⟨_, ⟨y, hy, rfl⟩, (isInside_tOut_right y).mpr hi⟩⟩

theorem insideRun_snoc_eq {O J : Type} {U V : O → Type} {Xi Yi : J → Type} (c : InsideOutsideSystem O J U V Xi Yi)
    (h : List (Σ l, twoFam U Yi l)) (a : Σ l, twoFam U Yi l) :
    insideRun c (h ++ [a]) = if ∃ y ∈ c (h ++ [a]), IsInside y then insideRun c h + 1 else 0 :=
  run_snoc _ _ _ _

theorem admitAfter_outer {P Q : Type} {r : Option (Two P Q)} {l : P}
    (h : admitAfter r ⟨none, l⟩) : ∀ j, r ≠ some ⟨some (), j⟩ := by
  rintro j rfl
  simp [admitAfter] at h

theorem admitAfter_inside {P Q : Type} {r : Option (Two P Q)} {j : Q}
    (h : admitAfter r ⟨some (), j⟩) : r = some ⟨some (), j⟩ := by
  rcases r with _ | ⟨_ | ⟨⟨⟩⟩, l⟩
  · simp [admitAfter] at h
  · simp [admitAfter] at h
  · simp only [admitAfter] at h
    rw [h]

theorem replyLabel_nil_conv {O J : Type} {U V : O → Type} {Xi Yi : J → Type} {b : ℕ}
    {c : InsideOutsideSystem O J U V Xi Yi} (hc : IsDDC b c) : replyLabel c [] = none := by
  have h := hc.dds.1
  simp only [SilentAtEmpty] at h
  simp [replyLabel, h]

theorem replyLabel_tensorRaw_nil : replyLabel (tensorRaw α β) [] = none := by
  simp [replyLabel, tensorRaw, relabel, pair, parAll]

variable (α β) in
def IdleA (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :
    Prop := ∀ j, replyLabel α (hA h) ≠ some ⟨some (), j⟩

variable (α β) in
def IdleB (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :
    Prop := ∀ j, replyLabel β (hB h) ≠ some ⟨some (), j⟩

variable (α β) in
/-- The state of `[α, β]` after `h`: both idle, or exactly one with an open inside call,
which is the last reply. -/
def TCase (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :
    Prop :=
  (∃ o, replyLabel (tensorRaw α β) h = some ⟨none, o⟩ ∧ lastOuter h = some o ∧ IdleA α (O' := O') (J' := J') h ∧
    IdleB β (O := O) (J := J) h) ∨
  (∃ j, replyLabel (tensorRaw α β) h = some ⟨some (), .inl j⟩ ∧
    replyLabel α (hA h) = some ⟨some (), j⟩ ∧ IdleB β (O := O) (J := J) h ∧
    lastOuter h = (lastOuter (hA h)).map .inl ∧ insideRun (tensorRaw α β) h ≤ insideRun α (hA h)) ∨
  (∃ j, replyLabel (tensorRaw α β) h = some ⟨some (), .inr j⟩ ∧
    replyLabel β (hB h) = some ⟨some (), j⟩ ∧ IdleA α (O' := O') (J' := J') h ∧
    lastOuter h = (lastOuter (hB h)).map .inr ∧ insideRun (tensorRaw α β) h ≤ insideRun β (hB h))

variable (α β) in
/-- The invariant of `[α, β]` on admissible histories. -/
def TInv (h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Yi l)) :
    Prop :=
  (h ≠ [] → (tensorRaw α β h).Dom) ∧ Admissible α (hA h) ∧ (hA h ≠ [] → (α (hA h)).Dom) ∧
    Admissible β (hB h) ∧ (hB h ≠ [] → (β (hB h)).Dom) ∧ (h ≠ [] → TCase α β h)

variable {bα bβ : ℕ}

theorem tpostA (hα : IsDDC bα α) {a} (hz : tIn z = ⟨none, a⟩)
    (haA : Admissible α (hA h)) (hdA : hA h ≠ [] → (α (hA h)).Dom)
    (haB : Admissible β (hB h)) (hdB : hB h ≠ [] → (β (hB h)).Dom)
    (hadm : Admits α (hA h) a) (hidB : IdleB β (O := O) (J := J) h)
    (hlo : lastOuter (h ++ [z]) = (lastOuter (hA h ++ [a])).map .inl)
    (hrun : insideRun (tensorRaw α β) h ≤ insideRun α (hA h))
    (hnext : Admissible α (hA h ++ [a]) → (α (hA h ++ [a])).Dom) : TInv α β (h ++ [z]) := by
  have haA' : Admissible α (hA h ++ [a]) := admissible_snoc.mpr ⟨haA, hdA, hadm⟩
  have hdA' : (α (hA h ++ [a])).Dom := hnext haA'
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdA'
  have hd' : (tensorRaw α β (h ++ [z])).Dom := by rw [tensorRaw_left hz]; exact hdA'
  have hl' : replyLabel (tensorRaw α β) (h ++ [z]) = some (lLab y.1) := by
    rw [replyLabel_tensorRaw_left hz, replyLabel_of_mem α hy]; rfl
  have hidB' : IdleB β (O := O) (J := J) (h ++ [z]) := by unfold IdleB; rw [hB_left hz]; exact hidB
  refine ⟨fun _ => hd', by rw [hA_left hz]; exact haA', fun _ => by rw [hA_left hz]; exact hdA',
    by rw [hB_left hz]; exact haB, by rw [hB_left hz]; exact hdB, fun _ => ?_⟩
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
  · refine Or.inl ⟨.inl l, hl', ?_, ?_, hidB'⟩
    · rw [hlo, hα.replies _ _ l hy rfl]; rfl
    · intro j hj
      rw [hA_left hz, replyLabel_of_mem α hy] at hj
      simp at hj
  · refine Or.inr (Or.inl ⟨l, hl', by rw [hA_left hz]; exact replyLabel_of_mem α hy, hidB',
      by rw [hA_left hz]; exact hlo, ?_⟩)
    rw [insideRun_tensorRaw_left hz, if_pos ⟨_, hy, rfl⟩, hA_left hz, insideRun_snoc_eq,
      if_pos ⟨_, hy, rfl⟩]
    omega

theorem tpostB (hβ : IsDDC bβ β) {a} (hz : tIn z = ⟨some (), a⟩)
    (haA : Admissible α (hA h)) (hdA : hA h ≠ [] → (α (hA h)).Dom)
    (haB : Admissible β (hB h)) (hdB : hB h ≠ [] → (β (hB h)).Dom)
    (hadm : Admits β (hB h) a) (hidA : IdleA α (O' := O') (J' := J') h)
    (hlo : lastOuter (h ++ [z]) = (lastOuter (hB h ++ [a])).map .inr)
    (hrun : insideRun (tensorRaw α β) h ≤ insideRun β (hB h))
    (hnext : Admissible β (hB h ++ [a]) → (β (hB h ++ [a])).Dom) : TInv α β (h ++ [z]) := by
  have haB' : Admissible β (hB h ++ [a]) := admissible_snoc.mpr ⟨haB, hdB, hadm⟩
  have hdB' : (β (hB h ++ [a])).Dom := hnext haB'
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hdB'
  have hd' : (tensorRaw α β (h ++ [z])).Dom := by rw [tensorRaw_right hz]; exact hdB'
  have hl' : replyLabel (tensorRaw α β) (h ++ [z]) = some (rLab y.1) := by
    rw [replyLabel_tensorRaw_right hz, replyLabel_of_mem β hy]; rfl
  have hidA' : IdleA α (O' := O') (J' := J') (h ++ [z]) := by unfold IdleA; rw [hA_right hz]; exact hidA
  refine ⟨fun _ => hd', by rw [hA_right hz]; exact haA, by rw [hA_right hz]; exact hdA,
    by rw [hB_right hz]; exact haB', fun _ => by rw [hB_right hz]; exact hdB', fun _ => ?_⟩
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
  · refine Or.inl ⟨.inr l, hl', ?_, hidA', ?_⟩
    · rw [hlo, hβ.replies _ _ l hy rfl]; rfl
    · intro j hj
      rw [hB_right hz, replyLabel_of_mem β hy] at hj
      simp at hj
  · refine Or.inr (Or.inr ⟨l, hl', by rw [hB_right hz]; exact replyLabel_of_mem β hy, hidA',
      by rw [hB_right hz]; exact hlo, ?_⟩)
    rw [insideRun_tensorRaw_right hz, if_pos ⟨_, hy, rfl⟩, hB_right hz, insideRun_snoc_eq,
      if_pos ⟨_, hy, rfl⟩]
    omega

/-- Before an outside input, both components are idle and no inside call is open. -/
theorem tensor_idle (hα : IsDDC bα α) (hβ : IsDDC bβ β) (inv : TInv α β h)
    (hn : ∀ j, replyLabel (tensorRaw α β) h ≠ some ⟨some (), j⟩) :
    IdleA α (O' := O') (J' := J') h ∧ IdleB β (O := O) (J := J) h ∧ insideRun (tensorRaw α β) h = 0 := by
  rcases eq_or_ne h [] with rfl | hne
  · refine ⟨fun j hj => ?_, fun j hj => ?_, rfl⟩
    · simp only [hA, List.map_nil, restrict_nil, replyLabel_nil_conv hα] at hj; cases hj
    · simp only [hB, List.map_nil, restrict_nil, replyLabel_nil_conv hβ] at hj; cases hj
  · rcases inv.2.2.2.2.2 hne with ⟨o, hl, -, hiA, hiB⟩ | ⟨j, hl, -⟩ | ⟨j, hl, -⟩
    · exact ⟨hiA, hiB, insideRun_eq_zero_of_outer hl⟩
    · exact absurd hl (hn _)
    · exact absurd hl (hn _)

theorem tensor_step (hα : IsDDC bα α) (hβ : IsDDC bβ β) (inv : TInv α β h)
    (hadm : Admits (tensorRaw α β) h z)
    (hnA : ∀ a, tIn z = ⟨none, a⟩ → Admissible α (hA h ++ [a]) → (α (hA h ++ [a])).Dom)
    (hnB : ∀ a, tIn z = ⟨some (), a⟩ → Admissible β (hB h ++ [a]) → (β (hB h ++ [a])).Dom) :
    TInv α β (h ++ [z]) := by
  obtain ⟨hd, haA, hdA, haB, hdB, hcase⟩ := inv
  have inv : TInv α β h := ⟨hd, haA, hdA, haB, hdB, hcase⟩
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, v⟩
  · -- outside input to `α`
    obtain ⟨hiA, hiB, hr0⟩ := tensor_idle hα hβ inv (admitAfter_outer hadm)
    refine tpostA hα rfl haA hdA haB hdB ?_ hiB ?_ (by rw [hr0]; exact Nat.zero_le _)
      (hnA _ rfl)
    · exact (admitAfter_of_ne hiA).mpr rfl
    · rw [lastOuter_snoc, lastOuter_snoc]; rfl
  · -- outside input to `β`
    obtain ⟨hiA, hiB, hr0⟩ := tensor_idle hα hβ inv (admitAfter_outer hadm)
    refine tpostB hβ rfl haA hdA haB hdB ?_ hiA ?_ (by rw [hr0]; exact Nat.zero_le _)
      (hnB _ rfl)
    · exact (admitAfter_of_ne hiB).mpr rfl
    · rw [lastOuter_snoc, lastOuter_snoc]; rfl
  · -- inside reply to `α`
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorRaw_nil] at hl; cases hl
    rcases hcase hne with ⟨o', hl', -⟩ | ⟨j, hl', hj, hiB, hlo, hrun⟩ | ⟨j, hl', -⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      obtain rfl : o = j := by simpa using hl'
      refine tpostA hα rfl haA hdA haB hdB ?_ hiB ?_ hrun (hnA _ rfl)
      · show admitAfter (replyLabel α (hA h)) ⟨some (), o⟩
        rw [hj]; rfl
      · rw [lastOuter_snoc, lastOuter_snoc]
        simpa [outerOf] using hlo
    · rw [hl] at hl'; simp at hl'
  · -- inside reply to `β`
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorRaw_nil] at hl; cases hl
    rcases hcase hne with ⟨o', hl', -⟩ | ⟨j, hl', -⟩ | ⟨j, hl', hj, hiA, hlo, hrun⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      obtain rfl : o = j := by simpa using hl'
      refine tpostB hβ rfl haA hdA haB hdB ?_ hiA ?_ hrun (hnB _ rfl)
      · show admitAfter (replyLabel β (hB h)) ⟨some (), o⟩
        rw [hj]; rfl
      · rw [lastOuter_snoc, lastOuter_snoc]
        simpa [outerOf] using hlo

theorem tInv_nil : TInv α β [] :=
  ⟨fun h => absurd rfl h, admissible_nil, fun h => (h rfl).elim, admissible_nil,
    fun h => (h rfl).elim, fun h => absurd rfl h⟩

/-- The invariant holds on every admissible history at which `[α, β]` is defined
on all nonempty prefixes. No component need answer every legal input. -/
theorem tensor_inv_partial (hα : IsDDC bα α) (hβ : IsDDC bβ β) :
    ∀ h, Admissible (tensorRaw α β) h → (h ≠ [] → (tensorRaw α β h).Dom) → TInv α β h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _ _; exact tInv_nil
  | append_singleton h z ih =>
    intro ha hd
    obtain ⟨ha₀, hd₀, hz⟩ := admissible_snoc.mp ha
    have hd' := hd (by simp)
    refine tensor_step hα hβ (ih ha₀ hd₀) hz (fun a e _ => ?_) (fun a e _ => ?_)
    · rw [tensorRaw_left e] at hd'; exact hd'
    · rw [tensorRaw_right e] at hd'; exact hd'

theorem tensor_inv (hα : IsResponsiveDDC bα α) (hβ : IsResponsiveDDC bβ β) :
    ∀ h, Admissible (tensorRaw α β) h → TInv α β h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; exact tInv_nil
  | append_singleton h z ih =>
    intro ha
    obtain ⟨ha₀, -, hz⟩ := admissible_snoc.mp ha
    exact tensor_step hα.isDDC hβ.isDDC (ih ha₀) hz
      (fun a _ ha => hα.responsive _ ha (by simp)) (fun a _ ha => hβ.responsive _ ha (by simp))

/-- **The parallel converter** `α ⊗ β`: `[α, β]` restricted to its admissible histories. -/
noncomputable def tensorL (α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (Xi ∘ Sum.inl) (Yi ∘ Sum.inl)) (β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xi ∘ Sum.inr) (Yi ∘ Sum.inr)) : InsideOutsideSystem (O ⊕ O') (J ⊕ J') U V Xi Yi :=
  canon (tensorRaw α β)

/-- **`α ⊗ β` is a partial converter**, with bound `max b b'`. -/
theorem IsDDC.tensorL (hα : IsDDC bα α) (hβ : IsDDC bβ β) :
    IsDDC (max bα bβ) (SystemAlgebra.tensorL α β) := by
  refine canon_isDDC ?_ ?_ ?_
  · simp [tensorRaw, relabel, pair, parAll]
  · intro h ha hd
    rcases eq_or_ne h [] with rfl | hne
    · exact Nat.zero_le _
    rcases (tensor_inv_partial hα hβ h ha (fun _ => hd)).2.2.2.2.2 hne with ⟨o, hl, -⟩ |
        ⟨j, -, hj, -, -, hrun⟩ | ⟨j, -, hj, -, -, hrun⟩
    · rw [insideRun_eq_zero_of_outer hl]; exact Nat.zero_le _
    · have hdA : (α (hA h)).Dom := by
        by_contra hn; simp [replyLabel, hn] at hj
      exact hrun.trans ((hα.bound _ hdA).trans (le_max_left _ _))
    · have hdB : (β (hB h)).Dom := by
        by_contra hn; simp [replyLabel, hn] at hj
      exact hrun.trans ((hβ.bound _ hdB).trans (le_max_right _ _))
  · intro h y o ha hy hl
    have hl' := replyLabel_of_mem _ hy
    rw [hl] at hl'
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorRaw_nil] at hl'; cases hl'
    rcases (tensor_inv_partial hα hβ h ha (fun _ => Part.dom_iff_mem.mpr ⟨y, hy⟩)).2.2.2.2.2 hne
      with ⟨o', hl'', hlo, -⟩ | ⟨j, hl'', -⟩ | ⟨j, hl'', -⟩
    · rw [hl'] at hl''
      obtain rfl : o = o' := by simpa using hl''
      exact hlo
    · rw [hl'] at hl''; simp at hl''
    · rw [hl'] at hl''; simp at hl''

/-- **`α ⊗ β` is a converter**, with bound `max b b'`. -/
theorem IsResponsiveDDC.tensorL (hα : IsResponsiveDDC bα α) (hβ : IsResponsiveDDC bβ β) :
    IsResponsiveDDC (max bα bβ) (SystemAlgebra.tensorL α β) := by
  refine isResponsiveDDC_iff.mpr ⟨hα.isDDC.tensorL hβ.isDDC, fun h ha hne => ?_⟩
  have ha' := (admissible_canon_iff h).mp ha
  exact canon_dom_iff.mpr ⟨ha', (tensor_inv hα hβ h ha').1 hne⟩

end Tensor

section TensorAttach

variable {X Y O O' J J' K : Type} {ι : J ⊕ J' → K}

theorem inl_not_mem_inr (hι : Function.Injective ι) (j : J) :
    (ι ∘ Sum.inl) j ∉ Set.range (ι ∘ Sum.inr) := by
  rintro ⟨j', e⟩
  exact Sum.inr_ne_inl (hι e)

variable (hι : Function.Injective ι)

/-- The free labels of `α^{ι₁} (β^{ι₂} R)` and of `(α ⊗ β)^ι R`. -/
def tensorEquiv :
    Free (alongSet (O := O) (liftAlong (O' := O') (ι ∘ Sum.inr) (ι ∘ Sum.inl) (inl_not_mem_inr hι))) ≃
      Free (alongSet (O := O ⊕ O') ι) where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, .inl o⟩⟩, outside_not_mem_alongSet ι _⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩ => ⟨⟨none, ⟨none, .inr o⟩⟩, outside_not_mem_alongSet ι _⟩
    | ⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h⟩⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), ⟨⟨some (), k⟩, h₁⟩⟩, h₂⟩ => ⟨⟨some (), k⟩, by
        rintro ⟨(j | j), rfl⟩
        · exact h₂ ⟨j, rfl⟩
        · exact h₁ ⟨j, rfl⟩⟩
  invFun
    | ⟨⟨none, ⟨none, .inl o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ _⟩
    | ⟨⟨none, ⟨none, .inr o⟩⟩, _⟩ => ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ _⟩⟩,
        outside_not_mem_alongSet_lift _ _ _ o _⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), k⟩, h⟩ => ⟨⟨some (), ⟨⟨some (), k⟩, fun ⟨j, e⟩ => h ⟨.inr j, e⟩⟩⟩, fun e => by
        obtain ⟨j, e⟩ := e
        exact h ⟨.inl j, by simpa [liftAlong] using congrArg (fun p => p.1) e⟩⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h'⟩
      · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
        · rfl
        · exact absurd (inside_mem_alongSet _ o) h'
      · rfl
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, l⟩
      · rcases l with o | o <;> rfl
      · exact absurd (inside_mem_alongSet _ l) h
    · rfl

theorem attachL_tensorRaw {bβ : ℕ} (α : SingleAlphabetConverter X Y O J) {β : SingleAlphabetConverter X Y O' J'} (hβ : IsResponsiveDDC bβ β)
    (R : SingleAlphabetSystem X Y K) :
    attachL ι (tensorRaw α β) R =
      relabelL (tensorEquiv hι)
        (attachL (liftAlong (ι ∘ Sum.inr) (ι ∘ Sum.inl) (inl_not_mem_inr hι)) α
          (attachL (ι ∘ Sum.inr) β R)) := by
  rw [attachL_lift _ (hι.comp Sum.inl_injective), relabelL, relabel_relabel]
  unfold attachL attachAlong connect pairI tensorRaw
  simp only [interconnect_relabel, pair_relabel_left, relabel_relabel]
  rw [pair_interconnect_right α (hβ.converges_along R), interconnect_interconnect, pair_assoc' α β R,
    interconnect_relabel, relabel_interconnect, relabel_interconnect]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | ⟨⟨⟩⟩, ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩⟩
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
    · rcases o with ⟨k, y⟩
      by_cases h₁ : k ∈ Set.range (ι ∘ Sum.inl)
      · obtain ⟨j, rfl⟩ := h₁
        have m₁ : (⟨some (), ι (.inl j)⟩ : Two (Two (O ⊕ O') (J ⊕ J')) K) ∈ alongSet ι :=
          image_mem_alongSet ι (.inl j)
        have m₂ : (⟨some (), ι (.inl j)⟩ : Two (Two O' J') K) ∉ alongSet (ι ∘ Sum.inr) :=
          sys_not_mem_alongSet _ (inl_not_mem_inr hι j)
        have m₃ : (⟨some (), ⟨⟨some (), ι (.inl j)⟩, m₂⟩⟩ : Two (Two O J) (Free (alongSet (O := O') (ι ∘ Sum.inr)))) ∈
            alongSet (liftAlong (ι ∘ Sum.inr) (ι ∘ Sum.inl) (inl_not_mem_inr hι)) := image_mem_alongSet _ j
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply, m₁, m₂, m₃]
        have e := liftC_alongRouting_lift (O := O) (U := fun _ : O => X) (V := fun _ : O => Y)
          (U' := fun _ : O' => X) (V' := fun _ : O' => Y) (X := fun _ : K => X) (Y := fun _ : K => Y)
          (ι ∘ Sum.inr) (hι.comp Sum.inl_injective) (inl_not_mem_inr hι) j
        simp only [Function.comp_apply] at e
        simp [e, splitIn, joinOut, twoAssoc', liftOut, tensorEquiv]
      · by_cases h₂ : k ∈ Set.range (ι ∘ Sum.inr)
        · obtain ⟨j, rfl⟩ := h₂
          have m₁ : (⟨some (), ι (.inr j)⟩ : Two (Two (O ⊕ O') (J ⊕ J')) K) ∈ alongSet ι :=
            image_mem_alongSet ι (.inr j)
          have m₂ : (⟨some (), ι (.inr j)⟩ : Two (Two O' J') K) ∈ alongSet (ι ∘ Sum.inr) :=
            image_mem_alongSet _ j
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply, m₁, m₂]
          have e := liftC_alongRouting_image (O := O') (U := fun _ : O' => X) (V := fun _ : O' => Y)
            (X := fun _ : K => X) (Y := fun _ : K => Y) (ι ∘ Sum.inr) (hι.comp Sum.inr_injective) j
          simp only [Function.comp_apply] at e
          simp [e, splitIn, joinOut, twoAssoc', twoAssoc, routeComp, routeRight, twoMap, liftOut, tensorEquiv]
        · have m₁ : (⟨some (), k⟩ : Two (Two (O ⊕ O') (J ⊕ J')) K) ∉ alongSet ι := by
            rintro ⟨(j | j), rfl⟩
            · exact h₁ ⟨j, rfl⟩
            · exact h₂ ⟨j, rfl⟩
          have m₂ : (⟨some (), k⟩ : Two (Two O' J') K) ∉ alongSet (ι ∘ Sum.inr) :=
            sys_not_mem_alongSet _ h₂
          have m₃ : ∀ h, (⟨some (), ⟨⟨some (), k⟩, h⟩⟩ : Two (Two O J) (Free (alongSet (O := O') (ι ∘ Sum.inr)))) ∉
              alongSet (liftAlong (ι ∘ Sum.inr) (ι ∘ Sum.inl) (inl_not_mem_inr hι)) := fun h e =>
            h₁ ((sys_mem_alongSet_lift_iff _ _ _ k h).1 e)
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply, m₁, m₂, m₃]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl⟩, v⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, l⟩
      · rcases l with o | o
        · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
        · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]
      · exact absurd (inside_mem_alongSet _ l) hl
    · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, outside_not_mem_alongSet, sys_mem_alongSet_lift_iff, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, liftC_alongRouting_inside, liftC_alongRouting_image _ hι, liftC_alongRouting_image _ (hι.comp Sum.inr_injective), liftC_alongRouting_lift _ (hι.comp Sum.inl_injective) (inl_not_mem_inr hι), tIn, tOut, liftIn, liftOut, tensorEquiv, freeIn, freeOut, splitIn, joinOut, twoAssoc, twoAssoc', connectInj, twoMap, routeComp, routeRight, alongRoute, alongInj, Function.comp_apply]

/-- **Attaching `α ⊗ β`** to a total resource is attaching `β`, then `α`. -/
theorem attachL_tensorL {bα bβ : ℕ} {α : SingleAlphabetConverter X Y O J} {β : SingleAlphabetConverter X Y O' J'} (hα : IsResponsiveDDC bα α)
    (hβ : IsResponsiveDDC bβ β) {R : SingleAlphabetSystem X Y K} (hR : TotalResource R) :
    attachL ι (tensorL α β) R =
      relabelL (tensorEquiv hι)
        (attachL (liftAlong (ι ∘ Sum.inr) (ι ∘ Sum.inl) (inl_not_mem_inr hι)) α
          (attachL (ι ∘ Sum.inr) β R)) := by
  rw [← attachL_tensorRaw hι α hβ R]
  unfold attachL tensorL
  rw [attachAlong_canon hι (IsResponsiveDDC.tensorL hα hβ) hR]

end TensorAttach

end SystemAlgebra

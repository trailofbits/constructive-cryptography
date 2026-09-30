import RandomSystems.DDC.Serial

/-!
# Single-alphabet systems and converters

Systems with one query alphabet and one reply alphabet at every label, as in
Jost, *On Generalizations of Composable Security*, Definitions 2.2.1–2.2.2.

## Main definitions

* `SingleAlphabetSystem X Y K`, `SingleAlphabetConverter X Y O J`
* `attachL ι α R`: attachment of a converter along the injection `ι`
* `relabelL τ R`: renaming labels along the equivalence `τ`
* `parL R S`, `dummyL`: parallel composition and the empty system

## Main results

* `attachL_relabelL`: attachment is natural in the labels
* `attachL_comp`, `attachL_idConverter`: attachment of a serial composition and
  of the identity
* `attachL_parL`, `parL_dummyL`: locality and the unit
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

variable (X Y : Type)

/-- A system on labels `K` with query alphabet `X` and reply alphabet `Y`. -/
abbrev SingleAlphabetSystem (K : Type) := InterfaceSystem K (fun _ : K => X) (fun _ : K => Y)

/-- A converter with outside labels `O` and inside labels `J`, alphabets `X`, `Y`. -/
abbrev SingleAlphabetConverter (O J : Type) :=
  InsideOutsideSystem O J (fun _ : O => X) (fun _ : O => Y) (fun _ : J => X) (fun _ : J => Y)

variable {X Y}

section Relabel

variable {K K' K'' : Type}

/-- Rename the labels of a system along `τ`. -/
def relabelL (τ : K ≃ K') (R : SingleAlphabetSystem X Y K) : SingleAlphabetSystem X Y K' :=
  relabel R (fun a => ⟨τ.symm a.1, a.2⟩) (fun b => ⟨τ b.1, b.2⟩)

@[simp] theorem relabelL_refl (R : SingleAlphabetSystem X Y K) : relabelL (Equiv.refl K) R = R := by
  exact relabel_id R

end Relabel

section Attach

variable {K O J : Type}

/-- Inputs of `α^ι R` at its free labels, read with the constant alphabet. -/
def freeIn (ι : J → K) : (Σ _ : Free (alongSet (O := O) ι), X) →
    Σ l : Free (alongSet (O := O) ι), twoFam (twoFam (fun _ : O => X) ((fun _ : K => Y) ∘ ι))
      (fun _ : K => X) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨⟨⟨some (), i⟩, h⟩, x⟩ => ⟨⟨⟨some (), i⟩, h⟩, x⟩

/-- Outputs of `α^ι R` at its free labels, read with the constant alphabet. -/
def freeOut (ι : J → K) : (Σ l : Free (alongSet (O := O) ι),
      twoFam (twoFam (fun _ : O => Y) ((fun _ : K => X) ∘ ι)) (fun _ : K => Y) l.1) →
    Σ _ : Free (alongSet (O := O) ι), Y
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨⟨⟨some (), i⟩, h⟩, y⟩ => ⟨⟨⟨some (), i⟩, h⟩, y⟩

/-- **Converter attachment** `α^ι R` (Jost p. 18): the inside label `j` of `α` is connected
to the interface `ι j` of `R`. The free labels are the outside labels of `α` and the
unconnected interfaces of `R`. -/
noncomputable def attachL (ι : J → K) (α : SingleAlphabetConverter X Y O J) (R : SingleAlphabetSystem X Y K) :
    SingleAlphabetSystem X Y (Free (alongSet (O := O) ι)) :=
  relabel (attachAlong ι α R) (freeIn ι) (freeOut ι)

variable {ι : J → K} {b : ℕ} {α : SingleAlphabetConverter X Y O J} {R : SingleAlphabetSystem X Y K}

theorem IsResponsiveDDC.totalResource_attachL (hι : Function.Injective ι) (hα : IsResponsiveDDC b α)
    (hR : TotalResource R) : TotalResource (attachL ι α R) := by
  have h := hα.totalResource_along hι hR
  refine ⟨fun u => ?_, fun u a y hy => ?_⟩
  · simp only [attachL, relabel, Part.map_Dom]
    rw [h.1]
    simp
  · simp only [attachL, relabel] at hy
    obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
    have hl := h.2 _ _ _ (by simpa using hy')
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl'⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rcases y' with ⟨⟨⟨_ | ⟨⟨⟩⟩, l'⟩, hl''⟩, v⟩
        · rcases l' with ⟨_ | ⟨⟨⟩⟩, o'⟩
          · simp [freeIn] at hl; subst hl; rfl
          · exact absurd (inside_mem_alongSet ι o') hl''
        · simp [freeIn] at hl
      · exact absurd (inside_mem_alongSet ι o) hl'
    · rcases y' with ⟨⟨⟨_ | ⟨⟨⟩⟩, l'⟩, hl''⟩, v⟩
      · simp [freeIn] at hl
      · simp [freeIn] at hl; subst hl; rfl

end Attach

section Naturality

variable {K K' O J : Type}

theorem not_mem_alongSet_comp {τ : K ≃ K'} {κ : J → K'} {i : K}
    (h : (⟨some (), i⟩ : Two (Two O J) K) ∉ alongSet (τ.symm ∘ κ)) :
    (⟨some (), τ i⟩ : Two (Two O J) K') ∉ alongSet κ := by
  rintro ⟨j, hj⟩
  exact h ⟨j, by simp [hj]⟩

theorem not_mem_alongSet_comp' {τ : K ≃ K'} {κ : J → K'} {i : K'}
    (h : (⟨some (), i⟩ : Two (Two O J) K') ∉ alongSet κ) :
    (⟨some (), τ.symm i⟩ : Two (Two O J) K) ∉ alongSet (τ.symm ∘ κ) := by
  rintro ⟨j, hj⟩
  exact h ⟨j, by simpa using congrArg τ hj⟩

/-- The free labels of `α^(τ⁻¹ ∘ κ) R` and of `α^κ (τ R)` correspond. -/
def freeEquivL (τ : K ≃ K') (κ : J → K') :
    Free (alongSet (O := O) (τ.symm ∘ κ)) ≃ Free (alongSet (O := O) κ) where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet κ o⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), i⟩, h⟩ => ⟨⟨some (), τ i⟩, not_mem_alongSet_comp h⟩
  invFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), i⟩, h⟩ => ⟨⟨some (), τ.symm i⟩, not_mem_alongSet_comp' h⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · simp
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · simp

/-- **Naturality of attachment**: attaching to a renamed resource is renaming the
attachment. -/
theorem attachL_relabelL (τ : K ≃ K') {κ : J → K'} (hκ : Function.Injective κ)
    (β : SingleAlphabetConverter X Y O J) (S : SingleAlphabetSystem X Y K) :
    attachL κ β (relabelL τ S) = relabelL (freeEquivL τ κ) (attachL (τ.symm ∘ κ) β S) := by
  have hκ' : Function.Injective (τ.symm ∘ κ) := τ.symm.injective.comp hκ
  unfold attachL relabelL attachAlong connect pairI
  rw [pair_relabel_right]
  simp only [interconnect_relabel, relabel_interconnect, relabel_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image κ hκ, liftC_alongRouting_image (τ.symm ∘ κ) hκ', freeOut, freeIn, freeEquivL, splitIn, joinOut, twoMap, connectInj]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image κ hκ, liftC_alongRouting_image (τ.symm ∘ κ) hκ', freeOut, freeIn, freeEquivL, splitIn, joinOut, twoMap, connectInj]
    · rcases y with ⟨i, w⟩
      by_cases hi : τ i ∈ Set.range κ
      · obtain ⟨j, hj⟩ := hi
        obtain rfl : i = τ.symm (κ j) := by rw [hj]; simp
        have h₁ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
          (X := fun _ : K => X) (Y := fun _ : K => Y) (τ.symm ∘ κ) hκ' j
        simp only [Function.comp_apply] at h₁
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image κ hκ, liftC_alongRouting_image (τ.symm ∘ κ) hκ', freeOut, freeIn, freeEquivL, splitIn, joinOut, twoMap, connectInj, h₁]
      · have hi' : τ.symm (τ i) ∉ Set.range (τ.symm ∘ κ) := by
          rintro ⟨j, hj⟩; exact hi ⟨j, by simpa using congrArg τ hj⟩
        simp only [Equiv.symm_apply_apply] at hi'
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image κ hκ, liftC_alongRouting_image (τ.symm ∘ κ) hκ', freeOut, freeIn, freeEquivL, splitIn, joinOut, twoMap, connectInj, hi, hi']
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image κ hκ, liftC_alongRouting_image (τ.symm ∘ κ) hκ', freeOut, freeIn, freeEquivL, splitIn, joinOut, twoMap, connectInj]

end Naturality

section Comp

variable {K O M J : Type} {ι : J → K}

/-- Inputs of `β^(α^ι R)` (outside labels of `α` connected) read with the constant alphabet. -/
def nestIn (ι : J → K) : (Σ _ : Free (alongSet (O := O) (outerOfAlong (M := M) ι)), X) →
    Σ l : Free (alongSet (O := O) (outerOfAlong (M := M) ι)),
      twoFam (twoFam (fun _ : O => X)
        ((fun l : Free (alongSet (O := M) ι) =>
          twoFam (twoFam (fun _ : M => Y) ((fun _ : K => X) ∘ ι)) (fun _ : K => Y) l.1) ∘
          outerOfAlong ι))
        (fun l : Free (alongSet (O := M) ι) =>
          twoFam (twoFam (fun _ : M => X) ((fun _ : K => Y) ∘ ι)) (fun _ : K => X) l.1) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩
  | ⟨⟨⟨none, ⟨some (), m⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ m) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, m⟩⟩, _⟩⟩, h⟩, _⟩ => absurd ⟨m, rfl⟩ h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h'⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet ι j) h'
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, x⟩ => ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, x⟩

/-- Outputs of `β^(α^ι R)` read with the constant alphabet. -/
def nestOut (ι : J → K) : (Σ l : Free (alongSet (O := O) (outerOfAlong (M := M) ι)),
      twoFam (twoFam (fun _ : O => Y)
        ((fun l : Free (alongSet (O := M) ι) =>
          twoFam (twoFam (fun _ : M => X) ((fun _ : K => Y) ∘ ι)) (fun _ : K => X) l.1) ∘
          outerOfAlong ι))
        (fun l : Free (alongSet (O := M) ι) =>
          twoFam (twoFam (fun _ : M => Y) ((fun _ : K => X) ∘ ι)) (fun _ : K => Y) l.1) l.1) →
    Σ _ : Free (alongSet (O := O) (outerOfAlong (M := M) ι)), Y
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩
  | ⟨⟨⟨none, ⟨some (), m⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ m) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, m⟩⟩, _⟩⟩, h⟩, _⟩ => absurd ⟨m, rfl⟩ h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h'⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet ι j) h'
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, y⟩ => ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, y⟩

/-- Attaching `β` to the outside of `α^ι R` is the nested attachment. -/
theorem attachL_outer (β : SingleAlphabetConverter X Y O M) (α : SingleAlphabetConverter X Y M J) (R : SingleAlphabetSystem X Y K) :
    attachL (outerOfAlong ι) β (attachL ι α R) =
      relabel (attachAlong (outerOfAlong ι) β (attachAlong ι α R)) (nestIn ι) (nestOut ι) := by
  unfold attachL attachAlong connect pairI
  rw [pair_relabel_right]
  simp only [interconnect_relabel, relabel_interconnect, relabel_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), freeOut, freeIn, nestOut, nestIn, splitIn, joinOut, twoMap, connectInj]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), freeOut, freeIn, nestOut, nestIn, splitIn, joinOut, twoMap, connectInj]
    · rcases y with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, w⟩
      · rcases l with ⟨_ | ⟨⟨⟩⟩, m⟩
        · obtain rfl : h = outside_not_mem_alongSet ι m := rfl
          have h₁ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := fun _ : Free (alongSet (O := M) ι) => X)
            (Y := fun _ : Free (alongSet (O := M) ι) => Y)
            (outerOfAlong (M := M) ι) (outerOfAlong_injective ι) m (image_mem_alongSet _ m) w
          have h₂ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := fun l : Free (alongSet (O := M) ι) =>
              twoFam (twoFam (fun _ : M => X) ((fun _ : K => Y) ∘ ι)) (fun _ : K => X) l.1)
            (Y := fun l : Free (alongSet (O := M) ι) =>
              twoFam (twoFam (fun _ : M => Y) ((fun _ : K => X) ∘ ι)) (fun _ : K => Y) l.1)
            (outerOfAlong (M := M) ι) (outerOfAlong_injective ι) m (image_mem_alongSet _ m) w
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), freeOut, freeIn, nestOut, nestIn, splitIn, joinOut, twoMap, connectInj, h₁]
          erw [h₂]
        · exact absurd (inside_mem_alongSet ι m) h
      · have hn := free_not_mem_outerOfAlong (O := O) (M := M) ι h
        simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, liftC_alongRouting_image (outerOfAlong (O := M) ι) (outerOfAlong_injective ι), freeOut, freeIn, nestOut, nestIn, splitIn, joinOut, twoMap, connectInj, hn]
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · exact absurd ⟨m, rfl⟩ h
        · exact absurd (inside_mem_alongSet ι m) h'
      · rfl

/-- The free labels of `β^(α^ι R)` and of `(β ⊙ α)^ι R` correspond. -/
def compEquiv (ι : J → K) :
    Free (alongSet (O := O) (outerOfAlong (M := M) ι)) ≃ Free (alongSet (O := O) ι) where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩
    | ⟨⟨none, ⟨some (), m⟩⟩, h⟩ => absurd (inside_mem_alongSet _ m) h
    | ⟨⟨some (), ⟨⟨none, ⟨none, m⟩⟩, _⟩⟩, h⟩ => absurd ⟨m, rfl⟩ h
    | ⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h'⟩⟩, _⟩ => absurd (inside_mem_alongSet ι j) h'
    | ⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, _⟩ => ⟨⟨some (), i⟩, h'⟩
  invFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet ι j) h
    | ⟨⟨some (), i⟩, h⟩ => ⟨⟨some (), ⟨⟨some (), i⟩, h⟩⟩, free_not_mem_outerOfAlong (O := O) (M := M) ι h⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · exact absurd ⟨m, rfl⟩ h
        · exact absurd (inside_mem_alongSet ι m) h'
      · rfl
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rfl

/-- **Serial attachment for converters** (MR16 §3.3, printed p. 7: “(β ◦ α)ⁱR = βⁱ(αⁱR)”):
attaching `trim (β ⊙ α)`, a converter by `IsResponsiveDDC.comp`, is attaching `α`, then `β`.
Derived from `attachAlong_comp`. -/
theorem attachL_comp (hι : Function.Injective ι) {bβ bα : ℕ} {β : SingleAlphabetConverter X Y O M}
    {α : SingleAlphabetConverter X Y M J} (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α) {R : SingleAlphabetSystem X Y K}
    (hR : TotalResource R) :
    attachL ι (trim (serialM β α)) R =
      relabelL (compEquiv ι) (attachL (outerOfAlong ι) β (attachL ι α R)) := by
  rw [attachL_outer, relabelL, relabel_relabel, attachL, attachAlong_comp hι hβ hα hR, relabel_relabel]
  congr 1
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rfl
  · funext b
    rcases b with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, y⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · exact absurd ⟨m, rfl⟩ h
        · exact absurd (inside_mem_alongSet ι m) h'
      · rfl

end Comp

section Identity

variable {K J : Type} {ι : J → K}

/-- The free labels of `𝟙^ι R` are the interfaces of `R`. -/
noncomputable def idEquivL (hι : Function.Injective ι) : Free (alongSet (O := J) ι) ≃ K where
  toFun
    | ⟨⟨none, ⟨none, j⟩⟩, _⟩ => ι j
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet ι j) h
    | ⟨⟨some (), i⟩, _⟩ => i
  invFun i := if h : i ∈ Set.range ι then ⟨⟨none, ⟨none, Classical.choose h⟩⟩,
      outside_not_mem_alongSet ι _⟩ else ⟨⟨some (), i⟩, sys_not_mem_alongSet ι h⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, j⟩
      · have hm : ι j ∈ Set.range ι := ⟨j, rfl⟩
        simp only [dif_pos hm]
        have := hι (Classical.choose_spec hm)
        simp only [Subtype.mk.injEq, Sigma.mk.injEq, heq_eq_eq, true_and]
        exact this
      · exact absurd (inside_mem_alongSet ι j) h
    · show (if h' : l ∈ Set.range ι then _ else _) = _
      rw [dif_neg (show l ∉ Set.range ι from h)]
  right_inv := by
    intro i
    by_cases h : i ∈ Set.range ι
    · simp only [dif_pos h]
      exact Classical.choose_spec h
    · simp only [dif_neg h]

/-- **Law I, identity converter** (MR16 §3.3; Jost p. 18, “id R = R”): attaching `𝟙` along
`ι` to a total resource gives back the resource, with its interfaces renamed by `ι`. -/
theorem attachL_idConverter (hι : Function.Injective ι) {R : SingleAlphabetSystem X Y K} (hR : TotalResource R) :
    relabelL (idEquivL hι) (attachL ι (idConverter J (fun _ : J => X) (fun _ : J => Y)) R) = R := by
  conv_rhs => rw [← attachAlong_idConverter hι hR]
  rw [attachL, relabelL, relabel_relabel]
  congr 1
  · funext a
    rcases a with ⟨i, x⟩
    by_cases h : i ∈ Set.range ι
    · simp only [Function.comp_apply]
      rw [idAlongIn_of_mem ι (a := ⟨i, x⟩) h]
      change freeIn ι ⟨(idEquivL hι).symm i, x⟩ = _
      simp only [idEquivL, Equiv.coe_fn_symm_mk, dif_pos h]
      rfl
    · simp only [Function.comp_apply]
      rw [idAlongIn_of_not_mem ι (a := ⟨i, x⟩) h]
      change freeIn ι ⟨(idEquivL hι).symm i, x⟩ = _
      simp only [idEquivL, Equiv.coe_fn_symm_mk, dif_neg h]
      rfl
  · funext b
    rcases b with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, y⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, j⟩
      · rfl
      · exact absurd (inside_mem_alongSet ι j) h
    · rfl

end Identity

section Lift

variable {K O J O' J' : Type} {ι : J → K} {κ : J' → K}

/-- Inputs of `α^ι (β^κ R)` (disjoint connections) read with the constant alphabet. -/
def liftIn (hd : ∀ j, ι j ∉ Set.range κ) :
    (Σ _ : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hd)), X) →
    Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hd)),
      twoFam (twoFam (fun _ : O => X) ((fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => Y) ((fun _ : K => X) ∘ κ)) (fun _ : K => Y) l.1) ∘ liftAlong κ ι hd)) (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => X) ((fun _ : K => Y) ∘ κ)) (fun _ : K => X) l.1) l.1
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, x⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, h'⟩⟩, h⟩, x⟩ => ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, h'⟩⟩, h⟩, x⟩
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h'⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet κ k) h'
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, x⟩ => ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, x⟩

/-- Outputs of `α^ι (β^κ R)` read with the constant alphabet. -/
def liftOut (hd : ∀ j, ι j ∉ Set.range κ) :
    (Σ l : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hd)),
      twoFam (twoFam (fun _ : O => Y) ((fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => X) ((fun _ : K => Y) ∘ κ)) (fun _ : K => X) l.1) ∘ liftAlong κ ι hd)) (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => Y) ((fun _ : K => X) ∘ κ)) (fun _ : K => Y) l.1) l.1) →
    Σ _ : Free (alongSet (O := O) (liftAlong (O' := O') κ ι hd)), Y
  | ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩ => ⟨⟨⟨none, ⟨none, o⟩⟩, h⟩, y⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet _ j) h
  | ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, h'⟩⟩, h⟩, y⟩ => ⟨⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, h'⟩⟩, h⟩, y⟩
  | ⟨⟨⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h'⟩⟩, _⟩, _⟩ => absurd (inside_mem_alongSet κ k) h'
  | ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, y⟩ => ⟨⟨⟨some (), ⟨⟨some (), i⟩, h'⟩⟩, h⟩, y⟩

theorem attachL_lift (hd : ∀ j, ι j ∉ Set.range κ) (hι : Function.Injective ι)
    (α : SingleAlphabetConverter X Y O J) (β : SingleAlphabetConverter X Y O' J') (R : SingleAlphabetSystem X Y K) :
    attachL (liftAlong κ ι hd) α (attachL κ β R) =
      relabel (attachAlong (liftAlong κ ι hd) α (attachAlong κ β R)) (liftIn hd) (liftOut hd) := by
  have hl := liftAlong_injective (O' := O') κ hι hd
  unfold attachL attachAlong connect pairI
  rw [pair_relabel_right]
  simp only [interconnect_relabel, relabel_interconnect, relabel_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, freeOut, freeIn, liftOut, liftIn, splitIn, joinOut, twoMap, connectInj]
      · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, freeOut, freeIn, liftOut, liftIn, splitIn, joinOut, twoMap, connectInj]
    · rcases y with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, w⟩
      · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
        · have hn := outside_not_mem_alongSet_lift (O := O) (J := J) κ ι hd o h
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, freeOut, freeIn, liftOut, liftIn, splitIn, joinOut, twoMap, connectInj, hn]
        · exact absurd (inside_mem_alongSet κ o) h
      · by_cases hi : l ∈ Set.range ι
        · obtain ⟨j, rfl⟩ := hi
          obtain rfl : h = hd j := rfl
          have h₁ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := fun _ : Free (alongSet (O := O') κ) => X) (Y := fun _ : Free (alongSet (O := O') κ) => Y)
            (liftAlong κ ι hd) hl j (image_mem_alongSet _ j) w
          have h₂ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => X) ((fun _ : K => Y) ∘ κ)) (fun _ : K => X) l.1)) (Y := (fun l : Free (alongSet (O := O') κ) => twoFam (twoFam (fun _ : O' => Y) ((fun _ : K => X) ∘ κ)) (fun _ : K => Y) l.1)) (liftAlong κ ι hd) hl j (image_mem_alongSet _ j) w
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, freeOut, freeIn, liftOut, liftIn, splitIn, joinOut, twoMap, connectInj, h₁]
          erw [h₂]
        · have hn := (sys_mem_alongSet_lift_iff (O := O) κ ι hd l h).not.mpr hi
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, outside_not_mem_alongSet_lift, inside_not_mem_alongSet_lift, freeOut, freeIn, liftOut, liftIn, splitIn, joinOut, twoMap, connectInj, hn]
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · rfl
        · exact absurd (inside_mem_alongSet κ m) h'
      · rfl

/-- The free labels of `β^(α^ι R)` and of `α^(β^κ R)` correspond. -/
def commEquiv (hι : ∀ j, ι j ∉ Set.range κ) (hκ : ∀ k, κ k ∉ Set.range ι) :
    Free (alongSet (O := O') (liftAlong (O' := O) ι κ hκ)) ≃
      Free (alongSet (O := O) (liftAlong (O' := O') κ ι hι)) where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet κ o⟩⟩,
        outside_not_mem_alongSet_lift κ ι hι o _⟩
    | ⟨⟨none, ⟨some (), k⟩⟩, h⟩ => absurd (inside_mem_alongSet _ k) h
    | ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩
    | ⟨⟨some (), ⟨⟨none, ⟨some (), j⟩⟩, h⟩⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
    | ⟨⟨some (), ⟨⟨some (), i⟩, h₁⟩⟩, h₂⟩ =>
        ⟨⟨some (), ⟨⟨some (), i⟩, fun h => h₂ ((sys_mem_alongSet_lift_iff ι κ hκ i h₁).2 h)⟩⟩,
          fun h => h₁ ((sys_mem_alongSet_lift_iff κ ι hι i _).1 h)⟩
  invFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩⟩,
        outside_not_mem_alongSet_lift ι κ hκ o _⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), ⟨⟨none, ⟨none, o⟩⟩, _⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩
    | ⟨⟨some (), ⟨⟨none, ⟨some (), k⟩⟩, h⟩⟩, _⟩ => absurd (inside_mem_alongSet κ k) h
    | ⟨⟨some (), ⟨⟨some (), i⟩, h₁⟩⟩, h₂⟩ =>
        ⟨⟨some (), ⟨⟨some (), i⟩, fun h => h₂ ((sys_mem_alongSet_lift_iff κ ι hι i h₁).2 h)⟩⟩,
          fun h => h₁ ((sys_mem_alongSet_lift_iff ι κ hκ i _).1 h)⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · rfl
        · exact absurd (inside_mem_alongSet ι m) h'
      · rfl
  right_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · rfl
        · exact absurd (inside_mem_alongSet κ m) h'
      · rfl

/-- **A2, independent attachment** (Jost Prop. 2.2.3, printed p. 18: “composition order
independence”): converters attached along disjoint injections commute. Derived from
`attachAlong_comm`. -/
theorem attachL_comm (hι : ∀ j, ι j ∉ Set.range κ) (hκ : ∀ k, κ k ∉ Set.range ι)
    (hιi : Function.Injective ι) (hκi : Function.Injective κ) {bα bβ : ℕ}
    {α : SingleAlphabetConverter X Y O J} {β : SingleAlphabetConverter X Y O' J'} (hα : IsResponsiveDDC bα α) (hβ : IsResponsiveDDC bβ β)
    (R : SingleAlphabetSystem X Y K) :
    attachL (liftAlong κ ι hι) α (attachL κ β R) =
      relabelL (commEquiv hι hκ) (attachL (liftAlong ι κ hκ) β (attachL ι α R)) := by
  rw [attachL_lift hι hιi, attachL_lift hκ hκi, relabelL, relabel_relabel,
    attachAlong_comm ι κ hι hκ hιi hκi α β R (hα.converges_along R) (hβ.converges_along R),
    relabel_relabel]
  congr 1
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · rfl
        · exact absurd (inside_mem_alongSet κ m) h'
      · rfl
  · funext b
    rcases b with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, y⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with ⟨⟨_ | ⟨⟨⟩⟩, l'⟩, h'⟩
      · rcases l' with ⟨_ | ⟨⟨⟩⟩, m⟩
        · rfl
        · exact absurd (inside_mem_alongSet ι m) h'
      · rfl

end Lift

section Parallel

variable {K K' O J : Type}

/-- Inputs of `[R, S]` on `K ⊕ K'`, read at the two components. -/
def parIn : (Σ _ : K ⊕ K', X) → Σ l : Two K K', twoFam (fun _ : K => X) (fun _ : K' => X) l
  | ⟨.inl k, x⟩ => ⟨⟨none, k⟩, x⟩
  | ⟨.inr k, x⟩ => ⟨⟨some (), k⟩, x⟩

/-- Outputs of `[R, S]`, read on `K ⊕ K'`. -/
def parOut : (Σ l : Two K K', twoFam (fun _ : K => Y) (fun _ : K' => Y) l) → Σ _ : K ⊕ K', Y
  | ⟨⟨none, k⟩, y⟩ => ⟨.inl k, y⟩
  | ⟨⟨some (), k⟩, y⟩ => ⟨.inr k, y⟩

/-- **Parallel composition** `[R, S]` (Jost p. 17): the interfaces of `R` and of `S`, side
by side. -/
noncomputable def parL (R : SingleAlphabetSystem X Y K) (S : SingleAlphabetSystem X Y K') : SingleAlphabetSystem X Y (K ⊕ K') :=
  relabel (pairI R S) parIn parOut

theorem inl_not_mem_alongSet {ι : J → K} {k : K} (h : (⟨some (), k⟩ : Two (Two O J) K) ∉ alongSet ι) :
    (⟨some (), Sum.inl k⟩ : Two (Two O J) (K ⊕ K')) ∉ alongSet (Sum.inl ∘ ι) := by
  rintro ⟨j, hj⟩
  exact h ⟨j, Sum.inl_injective hj⟩

theorem inr_not_mem_alongSet {ι : J → K} (k : K') :
    (⟨some (), Sum.inr k⟩ : Two (Two O J) (K ⊕ K')) ∉ alongSet (Sum.inl ∘ ι) := by
  rintro ⟨j, hj⟩
  cases hj

theorem not_mem_alongSet_of_inl {ι : J → K} {k : K}
    (h : (⟨some (), Sum.inl k⟩ : Two (Two O J) (K ⊕ K')) ∉ alongSet (Sum.inl ∘ ι)) :
    (⟨some (), k⟩ : Two (Two O J) K) ∉ alongSet ι := by
  rintro ⟨j, hj⟩
  exact h ⟨j, by simp [hj]⟩

/-- The free labels of `α^ι [R, S]` are those of `α^ι R` beside the interfaces of `S`. -/
def localEquiv (ι : J → K) :
    Free (alongSet (O := O) (Sum.inl ∘ ι : J → K ⊕ K')) ≃ Free (alongSet (O := O) ι) ⊕ K' where
  toFun
    | ⟨⟨none, ⟨none, o⟩⟩, _⟩ => .inl ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩
    | ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet _ j) h
    | ⟨⟨some (), .inl k⟩, h⟩ => .inl ⟨⟨some (), k⟩, not_mem_alongSet_of_inl h⟩
    | ⟨⟨some (), .inr k⟩, _⟩ => .inr k
  invFun
    | .inl ⟨⟨none, ⟨none, o⟩⟩, _⟩ => ⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet _ o⟩
    | .inl ⟨⟨none, ⟨some (), j⟩⟩, h⟩ => absurd (inside_mem_alongSet ι j) h
    | .inl ⟨⟨some (), k⟩, h⟩ => ⟨⟨some (), .inl k⟩, inl_not_mem_alongSet h⟩
    | .inr k => ⟨⟨some (), .inr k⟩, inr_not_mem_alongSet k⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with k | k <;> rfl
  right_inv := by
    rintro (⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩ | k)
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet ι o) h
    · rfl
    · rfl

/-- **Locality** (Jost Prop. 2.2.3, printed p. 18: “[π_P^γ R, S] = π_P^γ [R, S]”): attaching
a converter to `R` commutes with adjoining `S` in parallel. -/
theorem attachL_parL {ι : J → K} (hι : Function.Injective ι) {b : ℕ} {α : SingleAlphabetConverter X Y O J}
    (hα : IsResponsiveDDC b α) (R : SingleAlphabetSystem X Y K) (S : SingleAlphabetSystem X Y K') :
    attachL (Sum.inl ∘ ι) α (parL R S) = relabelL (localEquiv ι).symm (parL (attachL ι α R) S) := by
  have hαR := hα.converges_along (ι := ι) R
  unfold attachL parL attachAlong connect pairI relabelL
  simp only [relabel_relabel, pair_relabel_right, pair_relabel_left, interconnect_relabel]
  rw [pair_interconnect_left hαR, pair_assoc']
  simp only [relabel_relabel, interconnect_relabel, relabel_interconnect]
  have hι' : Function.Injective (Sum.inl ∘ ι : J → K ⊕ K') := Sum.inl_injective.comp hι
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
      · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩
        · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, freeOut, freeIn, parIn, parOut, localEquiv, splitIn, joinOut, twoMap, twoAssoc, twoAssoc', routeOpt, injOpt, alongRoute, alongInj, connectInj, inr_not_mem_alongSet]
        · simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, freeOut, freeIn, parIn, parOut, localEquiv, splitIn, joinOut, twoMap, twoAssoc, twoAssoc', routeOpt, injOpt, alongRoute, alongInj, connectInj, inr_not_mem_alongSet]
      · rcases y with ⟨k, w⟩
        by_cases hk : k ∈ Set.range ι
        · obtain ⟨j, rfl⟩ := hk
          have h₁ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := fun _ : K ⊕ K' => X) (Y := fun _ : K ⊕ K' => Y) (Sum.inl ∘ ι) hι' j
            (image_mem_alongSet _ j) w
          have h₂ := liftC_alongRouting_image (U := fun _ : O => X) (V := fun _ : O => Y)
            (X := fun _ : K => X) (Y := fun _ : K => Y) ι hι j (image_mem_alongSet _ j) w
          simp only [Function.comp_apply] at h₁
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, freeOut, freeIn, parIn, parOut, localEquiv, splitIn, joinOut, twoMap, twoAssoc, twoAssoc', routeOpt, injOpt, alongRoute, alongInj, connectInj, inr_not_mem_alongSet, h₁, h₂]
        · have hk' : (⟨some (), Sum.inl k⟩ : Two (Two O J) (K ⊕ K')) ∉ alongSet (Sum.inl ∘ ι) :=
            inl_not_mem_alongSet (sys_not_mem_alongSet ι hk)
          simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, freeOut, freeIn, parIn, parOut, localEquiv, splitIn, joinOut, twoMap, twoAssoc, twoAssoc', routeOpt, injOpt, alongRoute, alongInj, connectInj, inr_not_mem_alongSet, hk, hk']
    · rcases y with ⟨k, w⟩
      simp [connectRoute_of_mem, connectRoute_of_not_mem, inside_mem_alongSet, image_mem_alongSet, sys_mem_alongSet_iff, outside_not_mem_alongSet, liftC_alongRouting_inside, freeOut, freeIn, parIn, parOut, localEquiv, splitIn, joinOut, twoMap, twoAssoc, twoAssoc', routeOpt, injOpt, alongRoute, alongInj, connectInj, inr_not_mem_alongSet]
  · funext a
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, h⟩, x⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o⟩
      · rfl
      · exact absurd (inside_mem_alongSet _ o) h
    · rcases l with k | k <;> rfl

end Parallel

section Dummy

variable {K : Type}

/-- The dummy resource (Jost p. 17): no interfaces. -/
def dummyL : SingleAlphabetSystem X Y Empty := fun _ => Part.none

theorem restrict_none_map_parIn (h : List (Σ _ : K, X)) :
    restrict none ((h.map fun a => (⟨(Equiv.sumEmpty K Empty).symm a.1, a.2⟩ : Σ _ : K ⊕ Empty, X)).map
      (splitIn ∘ parIn)) = h := by
  induction h with
  | nil => rfl
  | cons a h ih =>
    simp only [List.map_cons, Function.comp_apply]
    rw [show splitIn (parIn (⟨(Equiv.sumEmpty K Empty).symm a.1, a.2⟩ : Σ _ : K ⊕ Empty, X)) =
      (⟨none, a⟩ : Two _ _) from rfl, restrict_two_none_cons_none, ih]

/-- **Right identity** (Jost p. 17: “[R, □] = R”). -/
theorem parL_dummyL {R : SingleAlphabetSystem X Y K} (hR : SilentAtEmpty R) :
    relabelL (Equiv.sumEmpty K Empty) (parL R dummyL) = R := by
  funext h
  simp only [relabelL, parL, pairI, relabel, List.map_map]
  rcases List.eq_nil_or_concat h with rfl | ⟨h', a, rfl⟩
  · simp only [List.map_nil]
    rw [Part.eq_none_iff'.mpr hR]
    simp [pair]
  · rw [List.concat_eq_append, List.map_append, List.map_singleton]
    rw [show (splitIn ∘ parIn ∘ fun a => (⟨(Equiv.sumEmpty K Empty).symm a.1, a.2⟩ :
        Σ _ : K ⊕ Empty, X)) a = (⟨none, a⟩ : Two _ _) from rfl, pair_left]
    have e : restrict none (h'.map (splitIn ∘ parIn ∘ fun a => (⟨(Equiv.sumEmpty K Empty).symm a.1,
        a.2⟩ : Σ _ : K ⊕ Empty, X))) = h' := by
      simpa [List.map_map, Function.comp_def] using restrict_none_map_parIn h'
    rw [e, Part.map_map, Part.map_map]
    conv_rhs => rw [← Part.map_id' (fun _ => rfl) (R (h' ++ [a]))]
    rfl

end Dummy

section ParNatural

variable {K K' K'' : Type}

end ParNatural

end SystemAlgebra

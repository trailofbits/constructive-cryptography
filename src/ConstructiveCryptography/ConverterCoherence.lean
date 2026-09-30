import ConstructiveCryptography.DDCCoherence
import ConstructiveCryptography.InterfaceTensorRename

/-!
# Naturality of the associator and the unitors

The associator and the unitors are natural for arbitrary converters. With presentations of the
converters, both sides are mixtures over the same samples; on each sample both sides are DDCs
with the same domains below one unrestricted regrouping, so they have the same transcripts.

## Main results

* `Interface.comp_associator`: naturality of the associator
* `Interface.comp_leftUnitor`, `Interface.comp_rightUnitor`: naturality of the unitors
-/

namespace SystemAlgebra.Interface

open Classical CategoryTheory Probability

variable {A B C D E F : Interface}
  {a : InsideOutsideSystem A.I D.I A.X A.Y D.X D.Y}
  {b : InsideOutsideSystem B.I E.I B.X B.Y E.X E.Y}
  {c : InsideOutsideSystem C.I F.I C.X C.Y F.X F.Y}

/-- On deterministic samples, the two sides of associator naturality have the same
transcripts. -/
theorem replies_associator_iff {ba bb bc : ℕ} (ha : IsDDCFrom D.domain A.domain ba a)
    (hb : IsDDCFrom E.domain B.domain bb b) (hc : IsDDCFrom F.domain C.domain bc c)
    {rD : InsideOutsideSystem ((D.I ⊕ E.I) ⊕ F.I) (D.I ⊕ (E.I ⊕ F.I))
      (tensor (tensor D E) F).X (tensor (tensor D E) F).Y
      (tensor D (tensor E F)).X (tensor D (tensor E F)).Y}
    {rA : InsideOutsideSystem ((A.I ⊕ B.I) ⊕ C.I) (A.I ⊕ (B.I ⊕ C.I))
      (tensor (tensor A B) C).X (tensor (tensor A B) C).Y
      (tensor A (tensor B C)).X (tensor A (tensor B C)).Y}
    (hrD : IsDDCFrom (tensor D (tensor E F)).domain (tensor (tensor D E) F).domain 1 rD)
    (hrA : IsDDCFrom (tensor A (tensor B C)).domain (tensor (tensor A B) C).domain 1 rA)
    (hD : ∀ h y, y ∈ rD h →
      y ∈ renameConverter (assocAlphabet D.X E.X F.X) (assocAlphabet D.Y E.Y F.Y).symm h)
    (hA : ∀ h y, y ∈ rA h →
      y ∈ renameConverter (assocAlphabet A.X B.X C.X) (assocAlphabet A.Y B.Y C.Y).symm h)
    (h : List ((Σ l, twoFam (tensor (tensor A B) C).X (tensor D (tensor E F)).Y l) ×
      (Σ l, twoFam (tensor (tensor A B) C).Y (tensor D (tensor E F)).X l))) :
    Replies (trim (serialM (SystemAlgebra.tensorL (SystemAlgebra.tensorL a b) c) rD))
        (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (trim (serialM rA (SystemAlgebra.tensorL a (SystemAlgebra.tensorL b c))))
        (h.map Prod.fst) (h.map Prod.snd) := by
  refine IsDDCFrom.replies_iff_of_le (IsDDCFrom.comp (bβ := max (max ba bb) bc) ?_ hrD)
    (IsDDCFrom.comp (bα := max ba (max bb bc)) hrA ?_)
    (W := trim (serialM (SystemAlgebra.tensorL (SystemAlgebra.tensorL a b) c)
      (renameConverter (assocAlphabet D.X E.X F.X) (assocAlphabet D.Y E.Y F.Y).symm))) ?_ ?_ h
  · apply IsDDCFrom.tensorL
    · apply IsDDCFrom.tensorL
      · exact ha
      · exact hb
    · exact hc
  · apply IsDDCFrom.tensorL
    · exact ha
    · apply IsDDCFrom.tensorL
      · exact hb
      · exact hc
  · intro xs ys hr
    exact (replies_trim_iff _ _ _).mpr
      (((replies_trim_iff _ _ _).mp hr).serialM_mono (fun _ _ hy => hy) hD)
  · intro xs ys hr
    rw [trim_serialM_associator_of_isDDC ha.isDDC hb.isDDC hc.isDDC]
    exact (replies_trim_iff _ _ _).mpr
      (((replies_trim_iff _ _ _).mp hr).serialM_mono hA (fun _ _ hy => hy))

/-- **The associator is natural.** -/
theorem comp_associator (α : A ⟶ D) (β : B ⟶ E) (γ : C ⟶ F) :
    parallelConverter (parallelConverter α β) γ ≫ (associator D E F).hom =
      (associator A B C).hom ≫ parallelConverter α (parallelConverter β γ) := by
  obtain ⟨rD, hrD, hD, hDle⟩ := exists_rename_eq_ofDDC (A := tensor (tensor D E) F)
    (B := tensor D (tensor E F)) _ _ _ (assocAlphabet_fst D.X E.X F.X)
    (assocAlphabet_fst D.Y E.Y F.Y) (parallelDomain_assoc D E F)
  obtain ⟨rA, hrA, hA, hAle⟩ := exists_rename_eq_ofDDC (A := tensor (tensor A B) C)
    (B := tensor A (tensor B C)) _ _ _ (assocAlphabet_fst A.X B.X C.X)
    (assocAlphabet_fst A.Y B.Y C.Y) (parallelDomain_assoc A B C)
  have hD' : (associator D E F).hom = PDCBehavior.ofDDC rD hrD := hD
  have hA' : (associator A B C).hom = PDCBehavior.ofDDC rA hrA := hA
  rw [hD', hA']
  obtain ⟨ba, P, hP⟩ := α.2
  obtain ⟨bb, Q, hQ⟩ := β.2
  obtain ⟨bc, R, hR⟩ := γ.2
  apply PDCBehavior.ext
  intro h
  change (PDCBehavior.comp _ _).1 h = (PDCBehavior.comp _ _).1 h
  have hAB := fun h => (PDCBehavior.tensor_presents α β P Q hP hQ h).symm
  have hBC := fun h => (PDCBehavior.tensor_presents β γ Q R hQ hR h).symm
  have hL := fun h => (PDCBehavior.tensor_presents (parallelConverter α β) γ _ R hAB hR h).symm
  have hR' := fun h => (PDCBehavior.tensor_presents α (parallelConverter β γ) P _ hP hBC h).symm
  rw [PDCBehavior.comp_ofDDC_presents (parallelConverter (parallelConverter α β) γ) _ hL hrD h,
    PDCBehavior.ofDDC_comp_presents hrA (parallelConverter α (parallelConverter β γ)) _ hR' h]
  simp only [tensorPDC, Distribution.mass_fTransform, Distribution.fTransform_prod_left,
    Distribution.fTransform_prod_right]
  rw [← Distribution.fTransform_assoc_prod P.1 Q.1 R.1, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro p
  exact replies_associator_iff p.1.2 p.2.1.2 p.2.2.2 hrD hrA hDle hAle h

/-- The identity on the unit interface is the forwarding converter. -/
theorem filter_unit :
    (DDC.filter (Y := unit.Y) (fun h => h = [] ∨ unit.domain h)
      (prefix_or_nil unit.nonempty_prefix.2)).1 = idConverter unit.I unit.X unit.Y := by
  funext h
  rcases h with _ | ⟨⟨⟨_ | ⟨⟩, e⟩, _⟩, _⟩
  · exact (Part.eq_none_iff'.mpr (DDC.isDDC_filter (Y := unit.Y) _ _).dds.1).trans
      (Part.eq_none_iff'.mpr (idConverter_isResponsiveDDC ..).dds.1).symm
  · exact e.elim
  · exact e.elim

/-- On deterministic samples, the two sides of left-unitor naturality have the same
transcripts. -/
theorem replies_leftUnitor_iff {ba : ℕ} (ha : IsDDCFrom D.domain A.domain ba a)
    {rD : InsideOutsideSystem (Empty ⊕ D.I) D.I (tensor unit D).X (tensor unit D).Y D.X D.Y}
    {rA : InsideOutsideSystem (Empty ⊕ A.I) A.I (tensor unit A).X (tensor unit A).Y A.X A.Y}
    (hrD : IsDDCFrom D.domain (tensor unit D).domain 1 rD)
    (hrA : IsDDCFrom A.domain (tensor unit A).domain 1 rA)
    (hD : ∀ h y, y ∈ rD h →
      y ∈ renameConverter (leftUnitAlphabet D.X) (leftUnitAlphabet D.Y).symm h)
    (hA : ∀ h y, y ∈ rA h →
      y ∈ renameConverter (leftUnitAlphabet A.X) (leftUnitAlphabet A.Y).symm h)
    (h : List ((Σ l, twoFam (tensor unit A).X D.Y l) × (Σ l, twoFam (tensor unit A).Y D.X l))) :
    Replies (trim (serialM (SystemAlgebra.tensorL
        (DDC.filter (Y := unit.Y) (fun h => h = [] ∨ unit.domain h)
          (prefix_or_nil unit.nonempty_prefix.2)).1 a) rD)) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (trim (serialM rA a)) (h.map Prod.fst) (h.map Prod.snd) := by
  refine IsDDCFrom.replies_iff_of_le (IsDDCFrom.comp (bβ := max 1 ba) ?_ hrD)
    (IsDDCFrom.comp hrA ha)
    (W := trim (serialM (SystemAlgebra.tensorL (idConverter unit.I unit.X unit.Y) a)
      (renameConverter (leftUnitAlphabet D.X) (leftUnitAlphabet D.Y).symm))) ?_ ?_ h
  · apply IsDDCFrom.tensorL
    · exact isDDCFrom_filter unit.nonempty_prefix
    · exact ha
  · intro xs ys hr
    refine (replies_trim_iff _ _ _).mpr (((replies_trim_iff _ _ _).mp hr).serialM_mono ?_ hD)
    rw [filter_unit]
    exact fun _ _ hy => hy
  · intro xs ys hr
    rw [trim_serialM_leftUnitor_of_isDDC ha.isDDC]
    exact (replies_trim_iff _ _ _).mpr
      (((replies_trim_iff _ _ _).mp hr).serialM_mono hA (fun _ _ hy => hy))

/-- On deterministic samples, the two sides of right-unitor naturality have the same
transcripts. -/
theorem replies_rightUnitor_iff {ba : ℕ} (ha : IsDDCFrom D.domain A.domain ba a)
    {rD : InsideOutsideSystem (D.I ⊕ Empty) D.I (tensor D unit).X (tensor D unit).Y D.X D.Y}
    {rA : InsideOutsideSystem (A.I ⊕ Empty) A.I (tensor A unit).X (tensor A unit).Y A.X A.Y}
    (hrD : IsDDCFrom D.domain (tensor D unit).domain 1 rD)
    (hrA : IsDDCFrom A.domain (tensor A unit).domain 1 rA)
    (hD : ∀ h y, y ∈ rD h →
      y ∈ renameConverter (rightUnitAlphabet D.X) (rightUnitAlphabet D.Y).symm h)
    (hA : ∀ h y, y ∈ rA h →
      y ∈ renameConverter (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y).symm h)
    (h : List ((Σ l, twoFam (tensor A unit).X D.Y l) × (Σ l, twoFam (tensor A unit).Y D.X l))) :
    Replies (trim (serialM (SystemAlgebra.tensorL a
        (DDC.filter (Y := unit.Y) (fun h => h = [] ∨ unit.domain h)
          (prefix_or_nil unit.nonempty_prefix.2)).1) rD)) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (trim (serialM rA a)) (h.map Prod.fst) (h.map Prod.snd) := by
  refine IsDDCFrom.replies_iff_of_le (IsDDCFrom.comp (bβ := max ba 1) ?_ hrD)
    (IsDDCFrom.comp hrA ha)
    (W := trim (serialM (SystemAlgebra.tensorL a (idConverter unit.I unit.X unit.Y))
      (renameConverter (rightUnitAlphabet D.X) (rightUnitAlphabet D.Y).symm))) ?_ ?_ h
  · apply IsDDCFrom.tensorL
    · exact ha
    · exact isDDCFrom_filter unit.nonempty_prefix
  · intro xs ys hr
    refine (replies_trim_iff _ _ _).mpr (((replies_trim_iff _ _ _).mp hr).serialM_mono ?_ hD)
    rw [filter_unit]
    exact fun _ _ hy => hy
  · intro xs ys hr
    rw [trim_serialM_rightUnitor_of_isDDC ha.isDDC]
    exact (replies_trim_iff _ _ _).mpr
      (((replies_trim_iff _ _ _).mp hr).serialM_mono hA (fun _ _ hy => hy))

/-- **The left unitor is natural.** -/
theorem comp_leftUnitor (α : A ⟶ D) :
    parallelConverter (𝟙 unit) α ≫ (leftUnitor D).hom = (leftUnitor A).hom ≫ α := by
  obtain ⟨rD, hrD, hD, hDle⟩ := exists_rename_eq_ofDDC (A := tensor unit D) (B := D) _ _ _
    (leftUnitAlphabet_fst D.X)
    (leftUnitAlphabet_fst D.Y) (parallelDomain_unit_left D)
  obtain ⟨rA, hrA, hA, hAle⟩ := exists_rename_eq_ofDDC (A := tensor unit A) (B := A) _ _ _
    (leftUnitAlphabet_fst A.X)
    (leftUnitAlphabet_fst A.Y) (parallelDomain_unit_left A)
  have hD' : (leftUnitor D).hom = PDCBehavior.ofDDC rD hrD := hD
  have hA' : (leftUnitor A).hom = PDCBehavior.ofDDC rA hrA := hA
  rw [hD', hA']
  obtain ⟨ba, P, hP⟩ := α.2
  apply PDCBehavior.ext
  intro h
  change (PDCBehavior.comp _ _).1 h = (PDCBehavior.comp _ _).1 h
  have hT := fun h => (PDCBehavior.tensor_presents (𝟙 unit) α
    ⟨Finsupp.single ⟨_, isDDCFrom_filter unit.nonempty_prefix⟩ 1, Distribution.isProbDist_single _⟩
    P (fun _ => rfl) hP h).symm
  rw [PDCBehavior.comp_ofDDC_presents (parallelConverter (𝟙 unit) α) _ hT hrD h,
    PDCBehavior.ofDDC_comp_presents hrA α P hP h]
  simp only [tensorPDC, Distribution.mass_fTransform, Distribution.prod_single_left]
  apply Distribution.mass_congr
  intro p
  exact replies_leftUnitor_iff p.2 hrD hrA hDle hAle h

/-- **The right unitor is natural.** -/
theorem comp_rightUnitor (α : A ⟶ D) :
    parallelConverter α (𝟙 unit) ≫ (rightUnitor D).hom = (rightUnitor A).hom ≫ α := by
  obtain ⟨rD, hrD, hD, hDle⟩ := exists_rename_eq_ofDDC (A := tensor D unit) (B := D) _ _ _
    (rightUnitAlphabet_fst D.X)
    (rightUnitAlphabet_fst D.Y) (parallelDomain_unit_right D)
  obtain ⟨rA, hrA, hA, hAle⟩ := exists_rename_eq_ofDDC (A := tensor A unit) (B := A) _ _ _
    (rightUnitAlphabet_fst A.X)
    (rightUnitAlphabet_fst A.Y) (parallelDomain_unit_right A)
  have hD' : (rightUnitor D).hom = PDCBehavior.ofDDC rD hrD := hD
  have hA' : (rightUnitor A).hom = PDCBehavior.ofDDC rA hrA := hA
  rw [hD', hA']
  obtain ⟨ba, P, hP⟩ := α.2
  apply PDCBehavior.ext
  intro h
  change (PDCBehavior.comp _ _).1 h = (PDCBehavior.comp _ _).1 h
  have hT := fun h => (PDCBehavior.tensor_presents α (𝟙 unit) P
    ⟨Finsupp.single ⟨_, isDDCFrom_filter unit.nonempty_prefix⟩ 1, Distribution.isProbDist_single _⟩
    hP (fun _ => rfl) h).symm
  rw [PDCBehavior.comp_ofDDC_presents (parallelConverter α (𝟙 unit)) _ hT hrD h,
    PDCBehavior.ofDDC_comp_presents hrA α P hP h]
  simp only [tensorPDC, Distribution.mass_fTransform, Distribution.prod_single_right]
  apply Distribution.mass_congr
  intro p
  exact replies_rightUnitor_iff p.2 hrD hrA hDle hAle h

end SystemAlgebra.Interface

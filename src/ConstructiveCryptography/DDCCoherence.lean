import RandomSystems.Converter.ConverterRelabel
import ConstructiveCryptography.InterfaceCoherence

/-!
# Regrouping parallel DDCs

The raw parallel wiring of DDCs on interface families is associative and unital up to the
regrouping of interface labels. Composing parallel DDCs with the regrouping equals
regrouping first, on every history: both sides are canonical restrictions of one
unrestricted wiring.

## Main results

* `Interface.tensorRaw_assoc`, `Interface.tensorRaw_unit_left`,
  `Interface.tensorRaw_unit_right`: regrouping the raw wiring changes only the labels
* `Interface.trim_serialM_leftUnitor_of_isDDC`, `Interface.trim_serialM_rightUnitor_of_isDDC`,
  `Interface.trim_serialM_associator_of_isDDC`: naturality of the unitors and the associator
  for DDCs
-/

namespace SystemAlgebra

open Classical

namespace Interface

variable {A B C D E F : Interface}
    {a : InsideOutsideSystem A.I D.I A.X A.Y D.X D.Y}
    {b : InsideOutsideSystem B.I E.I B.X B.Y E.X E.Y}
    {c : InsideOutsideSystem C.I F.I C.X C.Y F.X F.Y}

/-- Regrouping changes only the two ways to label the same three constituents. -/
theorem tensorRaw_assoc :
    relabel (tensorRaw (tensorRaw a b) c)
      (insideMap (assocAlphabet D.Y E.Y F.Y).symm)
      (insideMap (assocAlphabet D.X E.X F.X)) =
    relabel (tensorRaw a (tensorRaw b c))
      (outsideMap (assocAlphabet A.X B.X C.X))
      (outsideMap (assocAlphabet A.Y B.Y C.Y).symm) := by
  simp only [tensorRaw, pair_relabel_left, pair_relabel_right, relabel_relabel]
  rw [pair_assoc]
  simp only [relabel_relabel]
  congr 1
  · funext z
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩
    · rcases i with (i | j) | k <;> rfl
    · rcases i with i | j | k <;> rfl
  · funext z
    rcases z with ⟨(_ | ⟨⟨⟩⟩), z⟩
    · rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl
    · rcases z with ⟨(_ | ⟨⟨⟩⟩), ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩⟩ <;> rfl

theorem tensorRaw_unit_left (ha : SilentAtEmpty a) :
    relabel (tensorRaw (idConverter unit.I unit.X unit.Y) a)
      (insideMap (leftUnitAlphabet D.Y).symm) (insideMap (leftUnitAlphabet D.X)) =
      relabel a (outsideMap (leftUnitAlphabet A.X)) (outsideMap (leftUnitAlphabet A.Y).symm) := by
  rw [tensorRaw, relabel_relabel]
  have hi : tIn ∘ insideMap (leftUnitAlphabet D.Y).symm =
      fun z => (⟨some (), outsideMap (leftUnitAlphabet A.X) z⟩ :
        Two (Σ l, twoFam unit.X unit.Y l) (Σ l, twoFam A.X D.Y l)) := by
    funext z
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩
    · rcases i with e | i
      · exact e.elim
      · rfl
    · rfl
  rw [hi, relabel_pair_right_only _ _ ha]
  congr 1
  funext z
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl

theorem tensorRaw_unit_right (ha : SilentAtEmpty a) :
    relabel (tensorRaw a (idConverter unit.I unit.X unit.Y))
      (insideMap (rightUnitAlphabet D.Y).symm) (insideMap (rightUnitAlphabet D.X)) =
      relabel a (outsideMap (rightUnitAlphabet A.X)) (outsideMap (rightUnitAlphabet A.Y).symm) := by
  rw [tensorRaw, relabel_relabel]
  have hi : tIn ∘ insideMap (rightUnitAlphabet D.Y).symm =
      fun z => (⟨none, outsideMap (rightUnitAlphabet A.X) z⟩ :
        Two (Σ l, twoFam A.X D.Y l) (Σ l, twoFam unit.X unit.Y l)) := by
    funext z
    rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩
    · rcases i with i | e
      · rfl
      · exact e.elim
    · rfl
  rw [hi, relabel_pair_left_only _ _ ha]
  congr 1
  funext z
  rcases z with ⟨⟨(_ | ⟨⟨⟩⟩), i⟩, z⟩ <;> rfl

end Interface
namespace Interface

variable {A B C D E F : Interface}
    {a : InsideOutsideSystem A.I D.I A.X A.Y D.X D.Y}
    {b : InsideOutsideSystem B.I E.I B.X B.Y E.X E.Y}
    {c : InsideOutsideSystem C.I F.I C.X C.Y F.X F.Y}

theorem trim_serialM_leftUnitor_of_isDDC {ba : ℕ} (ha : IsDDC ba a) :
    trim (serialM (SystemAlgebra.tensorL (idConverter unit.I unit.X unit.Y) a)
      (renameConverter (leftUnitAlphabet D.X) (leftUnitAlphabet D.Y).symm)) =
    trim (serialM (renameConverter (leftUnitAlphabet A.X) (leftUnitAlphabet A.Y).symm) a) := by
  have hfA : ∀ u, (leftUnitAlphabet A.X u).1 = Equiv.emptySum Empty A.I u.1 := by
    rintro ⟨(e | i), x⟩; exact e.elim; rfl
  have hgA : ∀ v, ((leftUnitAlphabet A.Y).symm v).1 = (Equiv.emptySum Empty A.I).symm v.1 := by
    rintro ⟨i, y⟩; rfl
  have hfD : ∀ u, (leftUnitAlphabet D.X u).1 = Equiv.emptySum Empty D.I u.1 := by
    rintro ⟨(e | i), x⟩; exact e.elim; rfl
  have hgD : ∀ v, ((leftUnitAlphabet D.Y).symm v).1 = (Equiv.emptySum Empty D.I).symm v.1 := by
    rintro ⟨i, y⟩; rfl
  have hiA := (renameConverter_isResponsiveDDC _ _ _ hfA hgA).isDDC
  have hiD := (renameConverter_isResponsiveDDC _ _ _ hfD hgD).isDDC
  have ht : IsDDC (max 1 ba) (SystemAlgebra.tensorL (idConverter unit.I unit.X unit.Y) a :
      InsideOutsideSystem (Empty ⊕ A.I) (Empty ⊕ D.I) (Sum.rec unit.X A.X) (Sum.rec unit.Y A.Y)
        (Sum.rec unit.X D.X) (Sum.rec unit.Y D.Y)) := by
    apply IsDDC.tensorL
    · exact (idConverter_isResponsiveDDC ..).isDDC
    · exact ha
  apply (ht.comp hiD).eq_of_admitted_replies (hiA.comp ha)
  intro h hh
  rw [replies_trim_iff, replies_trim_iff, renameConverter_eq_canon _ _ _ hfD hgD,
    renameConverter_eq_canon _ _ _ hfA hgA]
  rw [renameConverter_eq_canon _ _ _ hfD hgD] at hiD
  rw [renameConverter_eq_canon _ _ _ hfA hgA] at hiA
  refine Iff.trans (replies_serialM_canon_iff (bβ := max 1 ba) ?_ hiD h hh) ?_
  · exact ht
  conv_rhs => rw [← ha.canon_eq]
  refine Iff.trans ?_ (replies_serialM_canon_iff (bα := ba) hiA ?_ h hh).symm
  · rw [serialM_forwardAll_relabel _ _ _ (tensorRaw_silentAtEmpty _ _), tensorRaw_unit_left ha.dds.1,
      serialM_relabel_forwardAll _ _ _ ha.dds.1]
  · rw [ha.canon_eq]; exact ha

theorem trim_serialM_rightUnitor_of_isDDC {ba : ℕ} (ha : IsDDC ba a) :
    trim (serialM (SystemAlgebra.tensorL a (idConverter unit.I unit.X unit.Y))
      (renameConverter (rightUnitAlphabet D.X) (rightUnitAlphabet D.Y).symm)) =
    trim (serialM (renameConverter (rightUnitAlphabet A.X) (rightUnitAlphabet A.Y).symm) a) := by
  have hfA : ∀ u, (rightUnitAlphabet A.X u).1 = Equiv.sumEmpty A.I Empty u.1 := by
    rintro ⟨(i | e), x⟩; rfl; exact e.elim
  have hgA : ∀ v, ((rightUnitAlphabet A.Y).symm v).1 = (Equiv.sumEmpty A.I Empty).symm v.1 := by
    rintro ⟨i, y⟩; rfl
  have hfD : ∀ u, (rightUnitAlphabet D.X u).1 = Equiv.sumEmpty D.I Empty u.1 := by
    rintro ⟨(i | e), x⟩; rfl; exact e.elim
  have hgD : ∀ v, ((rightUnitAlphabet D.Y).symm v).1 = (Equiv.sumEmpty D.I Empty).symm v.1 := by
    rintro ⟨i, y⟩; rfl
  have hiA := (renameConverter_isResponsiveDDC _ _ _ hfA hgA).isDDC
  have hiD := (renameConverter_isResponsiveDDC _ _ _ hfD hgD).isDDC
  have ht : IsDDC (max ba 1) (SystemAlgebra.tensorL a (idConverter unit.I unit.X unit.Y) :
      InsideOutsideSystem (A.I ⊕ Empty) (D.I ⊕ Empty) (Sum.rec A.X unit.X) (Sum.rec A.Y unit.Y)
        (Sum.rec D.X unit.X) (Sum.rec D.Y unit.Y)) := by
    apply IsDDC.tensorL
    · exact ha
    · exact (idConverter_isResponsiveDDC ..).isDDC
  apply (ht.comp hiD).eq_of_admitted_replies (hiA.comp ha)
  intro h hh
  rw [replies_trim_iff, replies_trim_iff, renameConverter_eq_canon _ _ _ hfD hgD,
    renameConverter_eq_canon _ _ _ hfA hgA]
  rw [renameConverter_eq_canon _ _ _ hfD hgD] at hiD
  rw [renameConverter_eq_canon _ _ _ hfA hgA] at hiA
  refine Iff.trans (replies_serialM_canon_iff (bβ := max ba 1) ?_ hiD h hh) ?_
  · exact ht
  conv_rhs => rw [← ha.canon_eq]
  refine Iff.trans ?_ (replies_serialM_canon_iff (bα := ba) hiA ?_ h hh).symm
  · rw [serialM_forwardAll_relabel _ _ _ (tensorRaw_silentAtEmpty _ _), tensorRaw_unit_right ha.dds.1,
      serialM_relabel_forwardAll _ _ _ ha.dds.1]
  · rw [ha.canon_eq]; exact ha

end Interface


namespace Interface

variable {A B C D E F : Interface}
    {a : InsideOutsideSystem A.I D.I A.X A.Y D.X D.Y}
    {b : InsideOutsideSystem B.I E.I B.X B.Y E.X E.Y}
    {c : InsideOutsideSystem C.I F.I C.X C.Y F.X F.Y}

/-- The associator is natural for partial converters. -/
theorem trim_serialM_associator_of_isDDC {ba bb bc : ℕ}
    (ha : IsDDC ba a) (hb : IsDDC bb b) (hc : IsDDC bc c) :
    trim (serialM (SystemAlgebra.tensorL (SystemAlgebra.tensorL a b) c)
      (renameConverter (assocAlphabet D.X E.X F.X) (assocAlphabet D.Y E.Y F.Y).symm)) =
    trim (serialM
      (renameConverter (assocAlphabet A.X B.X C.X) (assocAlphabet A.Y B.Y C.Y).symm)
      (SystemAlgebra.tensorL a (SystemAlgebra.tensorL b c))) := by
  have hfA : ∀ u, (assocAlphabet A.X B.X C.X u).1 = Equiv.sumAssoc A.I B.I C.I u.1 := by
    rintro ⟨((i | j) | k), x⟩ <;> rfl
  have hgA : ∀ v, ((assocAlphabet A.Y B.Y C.Y).symm v).1 =
      (Equiv.sumAssoc A.I B.I C.I).symm v.1 := by
    rintro ⟨(i | j | k), y⟩ <;> rfl
  have hfD : ∀ u, (assocAlphabet D.X E.X F.X u).1 = Equiv.sumAssoc D.I E.I F.I u.1 := by
    rintro ⟨((i | j) | k), x⟩ <;> rfl
  have hgD : ∀ v, ((assocAlphabet D.Y E.Y F.Y).symm v).1 =
      (Equiv.sumAssoc D.I E.I F.I).symm v.1 := by
    rintro ⟨(i | j | k), y⟩ <;> rfl
  have hiA := (renameConverter_isResponsiveDDC _ _ _ hfA hgA).isDDC
  have hiD := (renameConverter_isResponsiveDDC _ _ _ hfD hgD).isDDC
  refine IsDDC.eq_of_admitted_replies
    (IsDDC.comp (bβ := max (max ba bb) bc) ?_ hiD) (IsDDC.comp (bα := max ba (max bb bc)) hiA ?_)
    (fun h hh => ?_)
  · apply IsDDC.tensorL
    · apply IsDDC.tensorL
      · exact ha
      · exact hb
    · exact hc
  · apply IsDDC.tensorL
    · exact ha
    · apply IsDDC.tensorL
      · exact hb
      · exact hc
  rw [replies_trim_iff, replies_trim_iff, renameConverter_eq_canon _ _ _ hfD hgD,
    renameConverter_eq_canon _ _ _ hfA hgA]
  rw [renameConverter_eq_canon _ _ _ hfD hgD] at hiD
  rw [renameConverter_eq_canon _ _ _ hfA hgA] at hiA
  refine Iff.trans (replies_serialM_canon_iff (bβ := max (max ba bb) bc) ?_ hiD h hh) ?_
  · apply IsDDC.tensorL
    · apply IsDDC.tensorL
      · exact ha
      · exact hb
    · exact hc
  refine Iff.trans ?_ (replies_serialM_canon_iff (bβ := 1) (bα := max ba (max bb bc)) hiA ?_ h hh).symm
  swap
  · apply IsDDC.tensorL
    · exact ha
    · apply IsDDC.tensorL
      · exact hb
      · exact hc
  rw [serialM_forwardAll_relabel _ _ _ (tensorRaw_silentAtEmpty _ _),
    serialM_relabel_forwardAll _ _ _ (tensorRaw_silentAtEmpty _ _)]
  -- Both sides agree with the unrestricted regrouping on admitted inputs.
  refine Iff.trans (replies_relabel_congr_of_admitted (t := tensorRaw (tensorRaw a b) c)
    (insideEquiv (assocAlphabet D.Y E.Y F.Y).symm) (insideEquiv (assocAlphabet D.X E.X F.X))
    id (Equiv.sumAssoc D.I E.I F.I).symm (Equiv.injective _) ?_ ?_ ?_ h hh) ?_
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, z⟩
    · rfl
    · rcases i with i | j | k <;> rfl
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, z⟩
    · rfl
    · rcases i with i | j | k <;> rfl
  · intro h hh
    have := replies_tensorRaw_canon_iff (P := tensorRaw a b) (Q := c) (bP := max ba bb)
      (by apply IsDDC.tensorL; exact ha; exact hb) (hc.canon_eq.symm ▸ hc) h hh
    rwa [hc.canon_eq] at this
  refine Iff.trans ?_ (replies_relabel_congr_of_admitted (t := tensorRaw a (tensorRaw b c))
    (outsideEquiv (assocAlphabet A.X B.X C.X)) (outsideEquiv (assocAlphabet A.Y B.Y C.Y).symm)
    (Equiv.sumAssoc A.I B.I C.I) id Function.injective_id ?_ ?_ ?_ h hh).symm
  · exact iff_of_eq (congrArg (fun s => Replies s (h.map Prod.fst) (h.map Prod.snd))
      tensorRaw_assoc)
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, z⟩
    · rcases i with (i | j) | k <;> rfl
    · rfl
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, z⟩
    · rcases i with (i | j) | k <;> rfl
    · rfl
  · intro h hh
    have := replies_tensorRaw_canon_iff (P := a) (Q := tensorRaw b c) (bQ := max bb bc)
      (ha.canon_eq.symm ▸ ha) (by apply IsDDC.tensorL; exact hb; exact hc) h hh
    rwa [ha.canon_eq] at this

end Interface

end SystemAlgebra

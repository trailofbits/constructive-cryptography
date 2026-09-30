import RandomSystems.Converter.PDCBehavior
import RandomSystems.DDC.DDCParallelLaws
import RandomSystems.DDC.CanonWiring

/-!
# Parallel composition of DDCs and PDCs

Two DDCs on disjoint interfaces run side by side: each receives the inputs at its own
labels, and the joint history is legal exactly when both component histories are. The
parallel domain of two domains of input histories admits a nonempty history whose two
projections lie in their domains, or are empty. The parallel composition of a DDC from `E₁`
to `F₁` and a DDC from `E₂` to `F₂` is a DDC from `E₁ ∥ E₂` to `F₁ ∥ F₂`. The parallel
composition of two PDCs samples them independently (CR18, Definition 3.17); it satisfies
interchange with serial composition, and the parallel composition of identities is the
identity.

## Main definitions

* `sumAlphabet F`: messages of `Two` components as messages on the sum of their labels
* `parallelInputs E₁ E₂`: the parallel domain of two domains of input histories
* `tensorPDC`, `PDCBehavior.tensor`: the parallel composition of PDCs and of their behaviors

## Main results

* `replies_tensorRaw_iff`: parallel transcripts are pairs of component transcripts
* `IsDDCFrom.tensorL`: the parallel composition of DDCs from `E₁` to `F₁` and from `E₂` to
  `F₂` is a DDC from `E₁ ∥ E₂` to `F₁ ∥ F₂`
* `IsDDC.trim_serialM_tensorL`: interchange for DDCs
* `PDCBehavior.tensor_presents`: the parallel composition of presentations presents the
  parallel composition
* `PDCBehavior.tensor_id`, `PDCBehavior.comp_tensor`: identity and interchange
* `trim_apply_tensorL_pair`: parallel DDCs attached to parallel systems attach component by
  component
-/

namespace SystemAlgebra

open Classical

/-! ## Transcripts of parallel systems -/

/-- Messages of two components, as messages on the sum of their labels. -/
def sumAlphabet {I J : Type} (F : I ⊕ J → Type) :
    Two (Σ i, F (.inl i)) (Σ j, F (.inr j)) ≃ (Σ l, F l) where
  toFun
    | ⟨none, ⟨i, x⟩⟩ => ⟨.inl i, x⟩
    | ⟨some (), ⟨j, y⟩⟩ => ⟨.inr j, y⟩
  invFun
    | ⟨.inl i, x⟩ => ⟨none, ⟨i, x⟩⟩
    | ⟨.inr j, y⟩ => ⟨some (), ⟨j, y⟩⟩
  left_inv := by rintro ⟨(_ | ⟨⟩), ⟨i, x⟩⟩ <;> rfl
  right_inv := by rintro ⟨(i | j), x⟩ <;> rfl

/-- The parallel domain: a nonempty history whose two projections are empty or lie in the
component domains. -/
def parallelInputs {I J : Type} {F : I ⊕ J → Type} (E₁ : List (Σ i, F (.inl i)) → Prop)
    (E₂ : List (Σ j, F (.inr j)) → Prop) (h : List (Σ l, F l)) : Prop :=
  h ≠ [] ∧
    (restrict none (h.map (sumAlphabet F).symm) = [] ∨
      E₁ (restrict none (h.map (sumAlphabet F).symm))) ∧
    (restrict (some ()) (h.map (sumAlphabet F).symm) = [] ∨
      E₂ (restrict (some ()) (h.map (sumAlphabet F).symm)))

section Tensor

variable {O O' J J' : Type} {U V : O ⊕ O' → Type} {X Y : J ⊕ J' → Type}

/-- Joint converter inputs, split by component. -/
def tensorInputs : (Σ l, twoFam U Y l) ≃
    Two (Σ l, twoFam (U ∘ Sum.inl) (Y ∘ Sum.inl) l)
      (Σ l, twoFam (U ∘ Sum.inr) (Y ∘ Sum.inr) l) where
  toFun := tIn
  invFun := tOut
  left_inv := by rintro ⟨⟨(_ | ⟨⟩), (i | j)⟩, x⟩ <;> rfl
  right_inv := by rintro ⟨(_ | ⟨⟩), ⟨⟨(_ | ⟨⟩), i⟩, x⟩⟩ <;> rfl

/-- Joint converter outputs, from the components. -/
abbrev tensorOutputs := (tensorInputs (U := V) (Y := X)).symm

/-- Completed parallel histories are exactly pairs of completed component histories. -/
theorem replies_tensorRaw_iff
    (a : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl))
    (b : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr))
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    Replies (tensorRaw (U := U) (V := V) (Xi := X) (Yi := Y) a b)
        (h.map Prod.fst) (h.map Prod.snd) ↔
      RandomSystem.parallelConsistent (h.map (tensorInputs.prodCongr tensorOutputs.symm)) ∧
      Replies a ((RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd) ∧
      Replies b ((RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd) :=
  (replies_relabel_iff (pair a b) tensorInputs tensorOutputs h).trans
    (RandomSystem.replies_pair_iff a b _)

/-! ## Projections of joint histories -/

theorem outsideInputs_left (xs : List (Σ l, twoFam U Y l)) :
    restrict none ((outsideInputs xs).map (sumAlphabet U).symm) =
      outsideInputs (restrict none (xs.map tIn)) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [outsideInputs_append, List.map_append, restrict_append, ih]
    congr 1
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, u⟩ <;>
      simp [outsideInputs, splitIn, sumAlphabet, tIn, restrict_cons_self, restrict_cons_ne]

theorem outsideInputs_right (xs : List (Σ l, twoFam U Y l)) :
    restrict (some ()) ((outsideInputs xs).map (sumAlphabet U).symm) =
      outsideInputs (restrict (some ()) (xs.map tIn)) := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih =>
    simp only [outsideInputs_append, List.map_append, restrict_append, ih]
    congr 1
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, u⟩ <;>
      simp [outsideInputs, splitIn, sumAlphabet, tIn, restrict_cons_self, restrict_cons_ne]

theorem insideQueries_left (ys : List (Σ l, twoFam V X l)) :
    restrict none ((insideQueries ys).map (sumAlphabet X).symm) =
      insideQueries (restrict none (ys.map tensorOutputs.symm)) := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    simp only [insideQueries_append, List.map_append, restrict_append, ih]
    congr 1
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, u⟩ <;>
      simp [insideQueries, splitIn, sumAlphabet, tensorInputs, tIn, restrict_cons_self,
        restrict_cons_ne]

theorem insideQueries_right (ys : List (Σ l, twoFam V X l)) :
    restrict (some ()) ((insideQueries ys).map (sumAlphabet X).symm) =
      insideQueries (restrict (some ()) (ys.map tensorOutputs.symm)) := by
  induction ys using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    simp only [insideQueries_append, List.map_append, restrict_append, ih]
    congr 1
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, u⟩ <;>
      simp [insideQueries, splitIn, sumAlphabet, tensorInputs, tIn, restrict_cons_self,
        restrict_cons_ne]

end Tensor

/-! ## Parallel composition of DDCs from `E` to `F` -/

section TensorDomain

variable {O O' J J' : Type} {U V : O ⊕ O' → Type} {X Y : J ⊕ J' → Type}
  {α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl)}
  {β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)}
  {bα bβ : ℕ}

theorem parallelLeft_snd {A B C E : Type} {h : List ((Two A C) × (Two B E))}
    (hh : RandomSystem.parallelConsistent h) :
    (RandomSystem.parallelLeft h).map Prod.snd = restrict none (h.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z (by simp)
    have ht : RandomSystem.parallelConsistent h := fun a ha => hh a (by simp [ha])
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩ <;>
      simp_all [RandomSystem.parallelLeft]

theorem parallelRight_snd {A B C E : Type} {h : List ((Two A C) × (Two B E))}
    (hh : RandomSystem.parallelConsistent h) :
    (RandomSystem.parallelRight h).map Prod.snd = restrict (some ()) (h.map Prod.snd) := by
  induction h with
  | nil => rfl
  | cons z h ih =>
    have hz := hh z (by simp)
    have ht : RandomSystem.parallelConsistent h := fun a ha => hh a (by simp [ha])
    rcases z with ⟨⟨_ | ⟨⟩, x⟩, ⟨_ | ⟨⟩, y⟩⟩ <;>
      simp_all [RandomSystem.parallelRight]

/-- The component answering the next input is admitting it. -/
theorem tensor_admits_left (hα : IsDDC bα α) (hβ : IsDDC bβ β)
    {h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Y l)}
    {z : Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Y l} {a}
    (inv : TInv α β h) (hadm : Admits (tensorRaw α β) h z) (hz : tIn z = ⟨none, a⟩) :
    Admits α (hA h) a := by
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, v⟩
  · cases hz
    exact (admitAfter_of_ne (tensor_idle hα hβ inv (admitAfter_outer hadm)).1).mpr rfl
  · cases hz
  · cases hz
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorRaw_nil] at hl; cases hl
    rcases inv.2.2.2.2.2 hne with ⟨o', hl', -⟩ | ⟨j, hl', hj, -⟩ | ⟨j, hl', -⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      obtain rfl : o = j := by simpa using hl'
      show admitAfter (replyLabel α (hA h)) ⟨some (), o⟩
      rw [hj]; rfl
    · rw [hl] at hl'; simp at hl'
  · cases hz

theorem tensor_admits_right (hα : IsDDC bα α) (hβ : IsDDC bβ β)
    {h : List (Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Y l)}
    {z : Σ l : Two (O ⊕ O') (J ⊕ J'), twoFam U Y l} {a}
    (inv : TInv α β h) (hadm : Admits (tensorRaw α β) h z) (hz : tIn z = ⟨some (), a⟩) :
    Admits β (hB h) a := by
  unfold Admits at hadm
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, (o | o)⟩, v⟩
  · cases hz
  · cases hz
    exact (admitAfter_of_ne (tensor_idle hα hβ inv (admitAfter_outer hadm)).2.1).mpr rfl
  · cases hz
  · cases hz
    have hl := admitAfter_inside hadm
    have hne : h ≠ [] := by rintro rfl; rw [replyLabel_tensorRaw_nil] at hl; cases hl
    rcases inv.2.2.2.2.2 hne with ⟨o', hl', -⟩ | ⟨j, hl', -⟩ | ⟨j, hl', hj, -⟩
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'; simp at hl'
    · rw [hl] at hl'
      obtain rfl : o = j := by simpa using hl'
      show admitAfter (replyLabel β (hB h)) ⟨some (), o⟩
      rw [hj]; rfl

theorem tensorRaw_silentAtEmpty (α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl))
    (β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)) :
    SilentAtEmpty (tensorRaw α β) := by
  simp [SilentAtEmpty, tensorRaw, relabel, pair, parAll]

/-- A canonical converter answers the next input of an admitted transcript exactly when the
input is admitted and the converter answers it. -/
theorem canon_snoc_dom_iff {O J : Type} {U V : O → Type} {X Y : J → Type}
    {c : InsideOutsideSystem O J U V X Y} (hc : SilentAtEmpty c)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))} (ha : Admitted converterAdmits h)
    (hr : Replies c (h.map Prod.fst) (h.map Prod.snd)) (x : Σ l, twoFam U Y l) :
    (canon c (h.map Prod.fst ++ [x])).Dom ↔ converterAdmits h x ∧ (c (h.map Prod.fst ++ [x])).Dom := by
  have hx : Admissible c (h.map Prod.fst ++ [x]) ↔ converterAdmits h x := by
    rw [admissible_snoc]
    simp only [Admits, hr.replyLabel hc, converterAdmits]
    exact ⟨fun h => h.2.2, fun hx => ⟨(hr.admissible_iff_admitted hc).mpr ha, hr.dom, hx⟩⟩
  unfold canon
  by_cases hd : Admissible c (h.map Prod.fst ++ [x])
  · rw [if_pos hd]
    exact ⟨fun h => ⟨hx.mp hd, h⟩, fun h => h.2⟩
  · rw [if_neg hd]
    exact ⟨fun h => absurd h Part.not_none_dom, fun h => absurd (hx.mpr h.1) hd⟩

/-- The components of a joint transcript of `α ⊗ β`. -/
theorem replies_tensorL_split
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (SystemAlgebra.tensorL α β) (h.map Prod.fst) (h.map Prod.snd)) :
    Admitted converterAdmits h ∧
      Replies (tensorRaw α β) (h.map Prod.fst) (h.map Prod.snd) ∧
      Replies α ((RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd) ∧
      Replies β ((RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst)
        ((RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd) ∧
      (RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst = hA (h.map Prod.fst) ∧
      (RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.fst = hB (h.map Prod.fst) ∧
      (RandomSystem.parallelLeft (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd = restrict none ((h.map Prod.snd).map tensorOutputs.symm) ∧
      (RandomSystem.parallelRight (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map
          Prod.snd = restrict (some ()) ((h.map Prod.snd).map tensorOutputs.symm) := by
  obtain ⟨hadm, hrr⟩ := (replies_canon_iff _ (tensorRaw_silentAtEmpty α β) h).mp hr
  obtain ⟨hc, hra, hrb⟩ := (replies_tensorRaw_iff α β h).mp hrr
  have hfst : (h.map (tensorInputs.prodCongr tensorOutputs.symm)).map Prod.fst =
      (h.map Prod.fst).map tIn := by
    simp only [List.map_map]; rfl
  have hsnd : (h.map (tensorInputs.prodCongr tensorOutputs.symm)).map Prod.snd =
      (h.map Prod.snd).map tensorOutputs.symm := by
    simp only [List.map_map]; rfl
  refine ⟨hadm, hrr, hra, hrb, ?_, ?_, ?_, ?_⟩
  · rw [RandomSystem.parallelLeft_queries hc, hfst]
  · rw [RandomSystem.parallelRight_queries hc, hfst]
  · rw [parallelLeft_snd hc, hsnd]
  · rw [parallelRight_snd hc, hsnd]

/-- **The parallel composition of DDCs from `E₁` to `F₁` and from `E₂` to `F₂` is a DDC
from `E₁ ∥ E₂` to `F₁ ∥ F₂`**, with the larger of the two inside-query bounds. -/
theorem IsDDCFrom.tensorL {E₁ : List (Σ j, (X ∘ Sum.inl) j) → Prop}
    {E₂ : List (Σ j, (X ∘ Sum.inr) j) → Prop} {F₁ : List (Σ o, (U ∘ Sum.inl) o) → Prop}
    {F₂ : List (Σ o, (U ∘ Sum.inr) o) → Prop}
    (hα : IsDDCFrom E₁ F₁ bα α) (hβ : IsDDCFrom E₂ F₂ bβ β) :
    IsDDCFrom (parallelInputs (F := X) E₁ E₂) (parallelInputs (F := U) F₁ F₂) (max bα bβ)
      (SystemAlgebra.tensorL α β) := by
  have hraw := tensorRaw_silentAtEmpty α β
  have queries : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (SystemAlgebra.tensorL α β) (h.map Prod.fst) (h.map Prod.snd) →
        insideQueries (h.map Prod.snd) = [] ∨
          parallelInputs (F := X) E₁ E₂ (insideQueries (h.map Prod.snd)) := by
    intro h hr
    obtain ⟨-, -, hra, hrb, -, -, hsa, hsb⟩ := replies_tensorL_split hr
    by_cases hq : insideQueries (h.map Prod.snd) = []
    · exact Or.inl hq
    · refine Or.inr ⟨hq, ?_, ?_⟩
      · rw [insideQueries_left, ← hsa]
        exact hα.queries _ hra
      · rw [insideQueries_right, ← hsb]
        exact hβ.queries _ hrb
  refine ⟨hα.isDDC.tensorL hβ.isDDC, fun h x hr => ?_, queries⟩
  obtain ⟨hadm, hrr, hra, hrb, hfa, hfb, -, -⟩ := replies_tensorL_split hr
  have inv := tensor_inv_partial hα.isDDC hβ.isDDC (h.map Prod.fst)
    ((hrr.admissible_iff_admitted hraw).mpr hadm) (fun hne => hrr.dom hne)
  have hjoint : converterAdmits h x → Admits (tensorRaw α β) (h.map Prod.fst) x := by
    intro hx
    simpa only [Admits, hrr.replyLabel hraw, converterAdmits] using hx
  change (canon (tensorRaw α β) (h.map Prod.fst ++ [x])).Dom ↔ _
  rw [canon_snoc_dom_iff hraw hadm hrr x]
  have hE := queries h hr
  have hne := fun hx => outsideInputs_ne_nil (x := x) hadm hx
  rcases e : tIn x with ⟨_ | ⟨⟨⟩⟩, a⟩
  · -- the input goes to `α`
    rw [tensorRaw_left e, Part.map_Dom]
    have hlF : restrict none ((outsideInputs (h.map Prod.fst ++ [x])).map (sumAlphabet U).symm) =
        outsideInputs ((RandomSystem.parallelLeft
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map Prod.fst ++ [a]) := by
      rw [outsideInputs_left, List.map_append, List.map_singleton, e, restrict_none_snoc_left,
        hfa]
    have hrF : restrict (some ()) ((outsideInputs (h.map Prod.fst ++ [x])).map (sumAlphabet U).symm) =
        outsideInputs ((RandomSystem.parallelRight
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map Prod.fst) := by
      rw [outsideInputs_right, List.map_append, List.map_singleton, e, restrict_some_snoc_left,
        hfb]
    rw [← hfa]
    constructor
    · rintro ⟨hx, hd⟩
      have hz := (hα.answers _ a hra).mp hd
      refine ⟨hadm, hx, ⟨hne hx, ?_, ?_⟩, hE⟩
      · rw [hlF]; exact Or.inr hz.2.2.1
      · rw [hrF]; exact hβ.outsideInputs_mem hrb
    · rintro ⟨-, hx, ⟨-, hF₁, -⟩, -⟩
      refine ⟨hx, (hα.answers _ a hra).mpr ?_⟩
      have hax : converterAdmits (RandomSystem.parallelLeft
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))) a := by
        have := tensor_admits_left hα.isDDC hβ.isDDC inv (hjoint hx) e
        rwa [Admits, ← hfa, hra.replyLabel hα.isDDC.dds.1] at this
      have hadmα := hα.isDDC.admitted_of_replies hra
      refine ⟨hadmα, hax, ?_, hα.queries _ hra⟩
      rw [hlF] at hF₁
      exact hF₁.resolve_left (outsideInputs_ne_nil hadmα hax)
  · -- the input goes to `β`
    rw [tensorRaw_right e, Part.map_Dom]
    have hlF : restrict none ((outsideInputs (h.map Prod.fst ++ [x])).map (sumAlphabet U).symm) =
        outsideInputs ((RandomSystem.parallelLeft
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map Prod.fst) := by
      rw [outsideInputs_left, List.map_append, List.map_singleton, e, restrict_none_snoc_right,
        hfa]
    have hrF : restrict (some ()) ((outsideInputs (h.map Prod.fst ++ [x])).map (sumAlphabet U).symm) =
        outsideInputs ((RandomSystem.parallelRight
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))).map Prod.fst ++ [a]) := by
      rw [outsideInputs_right, List.map_append, List.map_singleton, e, restrict_some_snoc_right,
        hfb]
    rw [← hfb]
    constructor
    · rintro ⟨hx, hd⟩
      have hz := (hβ.answers _ a hrb).mp hd
      refine ⟨hadm, hx, ⟨hne hx, ?_, ?_⟩, hE⟩
      · rw [hlF]; exact hα.outsideInputs_mem hra
      · rw [hrF]; exact Or.inr hz.2.2.1
    · rintro ⟨-, hx, ⟨-, -, hF₂⟩, -⟩
      refine ⟨hx, (hβ.answers _ a hrb).mpr ?_⟩
      have hax : converterAdmits (RandomSystem.parallelRight
          (h.map (tensorInputs.prodCongr tensorOutputs.symm))) a := by
        have := tensor_admits_right hα.isDDC hβ.isDDC inv (hjoint hx) e
        rwa [Admits, ← hfb, hrb.replyLabel hβ.isDDC.dds.1] at this
      have hadmβ := hβ.isDDC.admitted_of_replies hrb
      refine ⟨hadmβ, hax, ?_, hβ.queries _ hrb⟩
      rw [hrF] at hF₂
      exact hF₂.resolve_left (outsideInputs_ne_nil hadmβ hax)

theorem parallelInputs_length_le {I J : Type} {F : I ⊕ J → Type}
    {E₁ : List (Σ i, F (.inl i)) → Prop} {E₂ : List (Σ j, F (.inr j)) → Prop} {m₁ m₂ : ℕ}
    (hE₁ : ∀ h, E₁ h → h.length ≤ m₁) (hE₂ : ∀ h, E₂ h → h.length ≤ m₂) (h : List (Σ l, F l))
    (hh : parallelInputs E₁ E₂ h) : h.length ≤ m₁ + m₂ := by
  have hl := length_restrict_two (h.map (sumAlphabet F).symm)
  rw [List.length_map] at hl
  have h₁ : (restrict none (h.map (sumAlphabet F).symm)).length ≤ m₁ := by
    rcases hh.2.1 with he | he
    · rw [he]; exact Nat.zero_le _
    · exact hE₁ _ he
  have h₂ : (restrict (some ()) (h.map (sumAlphabet F).symm)).length ≤ m₂ := by
    rcases hh.2.2 with he | he
    · rw [he]; exact Nat.zero_le _
    · exact hE₂ _ he
  omega

/-- Two domains that contain every nonempty history of at most `k` queries contain it in
parallel. -/
theorem parallelInputs_of_length_le {I J : Type} {F : I ⊕ J → Type}
    {E₁ : List (Σ i, F (.inl i)) → Prop} {E₂ : List (Σ j, F (.inr j)) → Prop} {k : ℕ}
    (h₁ : ∀ xs, xs ≠ [] → xs.length ≤ k → E₁ xs)
    (h₂ : ∀ xs, xs ≠ [] → xs.length ≤ k → E₂ xs) :
    ∀ xs, xs ≠ [] → xs.length ≤ k → parallelInputs E₁ E₂ xs := by
  intro xs hne hl
  have hr := length_restrict_two (xs.map (sumAlphabet F).symm)
  rw [List.length_map] at hr
  refine ⟨hne, ?_, ?_⟩
  · by_cases he : restrict none (xs.map (sumAlphabet F).symm) = []
    · exact Or.inl he
    · exact Or.inr (h₁ _ he (by omega))
  · by_cases he : restrict (some ()) (xs.map (sumAlphabet F).symm) = []
    · exact Or.inl he
    · exact Or.inr (h₂ _ he (by omega))

/-- The queries at a left label of a parallel history are those of its left projection. -/
theorem restrict_restrict_sumAlphabet {I J : Type} {F : I ⊕ J → Type} (i : I)
    (ys : List (Σ l, F l)) :
    restrict i (restrict none (ys.map (sumAlphabet F).symm)) = restrict (Sum.inl i) ys := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨(i' | j), x⟩
    · change restrict i (restrict none ((⟨none, ⟨i', x⟩⟩ : Two _ _) ::
        ys.map (sumAlphabet F).symm)) = restrict (Sum.inl i) (⟨Sum.inl i', x⟩ :: ys)
      rw [restrict_two_none_cons_none]
      by_cases hi : i' = i
      · subst hi
        rw [restrict_cons_self, restrict_cons_self, ih]
      · rw [restrict_cons_ne hi, restrict_cons_ne (by simpa using hi), ih]
    · change restrict i (restrict none ((⟨some (), ⟨j, x⟩⟩ : Two _ _) ::
        ys.map (sumAlphabet F).symm)) = restrict (Sum.inl i) (⟨Sum.inr j, x⟩ :: ys)
      rw [restrict_cons_ne (by simp), restrict_cons_ne (by simp), ih]

theorem parallelInputs_nonempty_prefix {I J : Type} {F : I ⊕ J → Type}
    {E₁ : List (Σ i, F (.inl i)) → Prop} {E₂ : List (Σ j, F (.inr j)) → Prop}
    (hE₁ : ∀ {p h}, p <+: h → p ≠ [] → E₁ h → E₁ p) (hE₂ : ∀ {p h}, p <+: h → p ≠ [] → E₂ h → E₂ p) :
    ¬ parallelInputs E₁ E₂ [] ∧
      ∀ {p h}, p <+: h → p ≠ [] → parallelInputs E₁ E₂ h → parallelInputs E₁ E₂ p := by
  refine ⟨fun h => h.1 rfl, fun {p h} hp hn hd => ⟨hn, ?_, ?_⟩⟩
  · have hpre := restrict_prefix none (hp.map (sumAlphabet F).symm)
    by_cases he : restrict none (p.map (sumAlphabet F).symm) = []
    · exact Or.inl he
    · exact Or.inr (hE₁ hpre he
        (hd.2.1.resolve_left (fun hz => he (List.eq_nil_of_prefix_nil (hz ▸ hpre)))))
  · have hpre := restrict_prefix (some ()) (hp.map (sumAlphabet F).symm)
    by_cases he : restrict (some ()) (p.map (sumAlphabet F).symm) = []
    · exact Or.inl he
    · exact Or.inr (hE₂ hpre he
        (hd.2.2.resolve_left (fun hz => he (List.eq_nil_of_prefix_nil (hz ▸ hpre)))))

end TensorDomain

/-! ## Parallel and serial wiring -/

theorem tensorRaw_mono {O O' J J' : Type} {U V : O ⊕ O' → Type} {X Y : J ⊕ J' → Type}
    {a a' : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {b b' : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    (ha : ∀ h y, y ∈ a h → y ∈ a' h) (hb : ∀ h y, y ∈ b h → y ∈ b' h) :
    ∀ h y, y ∈ tensorRaw a b h → y ∈ tensorRaw a' b' h :=
  relabel_mono (pair_mono ha hb) _ _

theorem Replies.serialM_mono {O M J : Type} {U V : O → Type}
    {Xm Ym : M → Type} {X Y : J → Type}
    {a a' : InsideOutsideSystem O M U V Xm Ym} {b b' : InsideOutsideSystem M J Xm Ym X Y}
    (ha : ∀ h y, y ∈ a h → y ∈ a' h) (hb : ∀ h y, y ∈ b h → y ∈ b' h)
    {xs ys} (hr : Replies (serialM a b) xs ys) : Replies (serialM a' b') xs ys :=
  hr.interconnect_mono (pair_mono ha hb)

section TensorWiring

variable {O O' J J' : Type} {U V : O ⊕ O' → Type} {Xi Yi : J ⊕ J' → Type}

/-- Parallel wiring respects equality of completed component histories. -/
theorem replies_tensorRaw_congr
    {a a' : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (Xi ∘ Sum.inl) (Yi ∘ Sum.inl)}
    {b b' : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xi ∘ Sum.inr) (Yi ∘ Sum.inr)}
    (ha : ∀ xs ys, Replies a xs ys ↔ Replies a' xs ys)
    (hb : ∀ xs ys, Replies b xs ys ↔ Replies b' xs ys)
    (h : List ((Σ l, twoFam U Yi l) × (Σ l, twoFam V Xi l))) :
    Replies (tensorRaw (U := U) (V := V) (Xi := Xi) (Yi := Yi) a b)
        (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies (tensorRaw (U := U) (V := V) (Xi := Xi) (Yi := Yi) a' b')
        (h.map Prod.fst) (h.map Prod.snd) := by
  rw [replies_tensorRaw_iff, replies_tensorRaw_iff, ha, hb]

/-- **Canonical restriction commutes with parallel wiring** on admitted histories. -/
theorem replies_tensorRaw_canon_iff {bP bQ : ℕ}
    {P : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (Xi ∘ Sum.inl) (Yi ∘ Sum.inl)}
    {Q : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xi ∘ Sum.inr) (Yi ∘ Sum.inr)}
    (hP : IsDDC bP (canon P)) (hQ : IsDDC bQ (canon Q)) :
    ∀ h : List ((Σ l, twoFam U Yi l) × (Σ l, twoFam V Xi l)), Admitted converterAdmits h →
      (Replies (tensorRaw (U := U) (V := V) (Xi := Xi) (Yi := Yi) (canon P) (canon Q))
          (h.map Prod.fst) (h.map Prod.snd) ↔
        Replies (tensorRaw (U := U) (V := V) (Xi := Xi) (Yi := Yi) P Q)
          (h.map Prod.fst) (h.map Prod.snd)) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro _; simp [Replies]
  | append_singleton h z ih =>
    intro hh
    obtain ⟨hh₀, hz⟩ := admitted_snoc.mp hh
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton]
    constructor
    · intro hr
      exact hr.mono (tensorRaw_mono (fun _ _ h => canon_mem h) (fun _ _ h => canon_mem h))
    · intro hr
      obtain ⟨hr₀, hy⟩ := replies_snoc.mp hr
      have hc₀ := (ih hh₀).mpr hr₀
      have hreact := tensorRaw_silentAtEmpty (U := U) (V := V) (X := Xi) (Y := Yi) (canon P) (canon Q)
      have ha : Admissible (tensorRaw (canon P) (canon Q)) (h.map Prod.fst) :=
        (hc₀.admissible_iff_admitted hreact).mpr hh₀
      have inv := tensor_inv_partial hP hQ _ ha (fun hne => hc₀.dom hne)
      have hadm : Admits (tensorRaw (canon P) (canon Q)) (h.map Prod.fst) x := by
        rw [Admits, hc₀.replyLabel_eq hreact, List.getLast?_map]
        simpa [converterAdmits, Option.map_map, Function.comp_def] using hz
      have hraw := Part.eq_some_iff.mp hy
      have inv' := tensor_step hP hQ inv hadm
        (fun a e ha' => by
          rw [canon_of_admissible ((admissible_canon_iff _).mp ha')]
          rw [tensorRaw_left e] at hraw
          exact (Part.mem_map_iff _).mp hraw |>.elim fun v hv => Part.dom_iff_mem.mpr ⟨v, hv.1⟩)
        (fun a e ha' => by
          rw [canon_of_admissible ((admissible_canon_iff _).mp ha')]
          rw [tensorRaw_right e] at hraw
          exact (Part.mem_map_iff _).mp hraw |>.elim fun v hv => Part.dom_iff_mem.mpr ⟨v, hv.1⟩)
      refine replies_snoc.mpr ⟨hc₀, ?_⟩
      rcases e : tIn x with ⟨_ | ⟨⟩, a⟩
      · have hA' := inv'.2.1
        rw [hA_left e] at hA'
        rw [tensorRaw_left e, canon_of_admissible ((admissible_canon_iff _).mp hA'),
          ← tensorRaw_left (β := Q) e]
        exact hy
      · have hB' := inv'.2.2.2.1
        rw [hB_right e] at hB'
        rw [tensorRaw_right e, canon_of_admissible ((admissible_canon_iff _).mp hB'),
          ← tensorRaw_right (α := P) e]
        exact hy

end TensorWiring

section Interchange

variable {O O' M M' J J' : Type} {U V : O ⊕ O' → Type}
    {Xm Ym : M ⊕ M' → Type} {X Y : J ⊕ J' → Type}
    {a : InsideOutsideSystem O M (U ∘ Sum.inl) (V ∘ Sum.inl) (Xm ∘ Sum.inl) (Ym ∘ Sum.inl)}
    {b : InsideOutsideSystem O' M' (U ∘ Sum.inr) (V ∘ Sum.inr) (Xm ∘ Sum.inr) (Ym ∘ Sum.inr)}
    {c : InsideOutsideSystem M J (Xm ∘ Sum.inl) (Ym ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {d : InsideOutsideSystem M' J' (Xm ∘ Sum.inr) (Ym ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    {ba bb bc bd : ℕ}

/-- Serial and parallel composition of partial converters satisfy interchange. -/
theorem IsDDC.trim_serialM_tensorL (ha : IsDDC ba a) (hb : IsDDC bb b)
    (hc : IsDDC bc c) (hd : IsDDC bd d) :
    trim (serialM (SystemAlgebra.tensorL a b) (SystemAlgebra.tensorL c d)) =
      SystemAlgebra.tensorL (trim (serialM a c)) (trim (serialM b d)) := by
  apply ((ha.tensorL hb).comp (hc.tensorL hd)).eq_of_admitted_replies
    ((ha.comp hc).tensorL (hb.comp hd))
  intro h hh
  rw [replies_trim_iff]
  refine (replies_serialM_canon_iff (β := tensorRaw a b) (α := tensorRaw c d)
    (ha.tensorL hb) (hc.tensorL hd) h hh).trans ?_
  rw [serialM_tensorRaw ha hb]
  refine Iff.trans ?_ (replies_canon_iff _ (tensorRaw_silentAtEmpty _ _) h).symm
  rw [replies_tensorRaw_congr (fun xs ys => (replies_trim_iff (serialM a c) xs ys).symm)
    (fun xs ys => (replies_trim_iff (serialM b d) xs ys).symm) h]
  exact ⟨fun hr => ⟨hh, hr⟩, fun hr => hr.2⟩

end Interchange

/-! ## Parallel composition of PDCs -/

instance instFintypeSumRec {I J : Type} (F : I → Type) (G : J → Type) [∀ i, Fintype (F i)]
    [∀ j, Fintype (G j)] : ∀ l : I ⊕ J, Fintype (Sum.rec F G l)
  | .inl i => (inferInstance : Fintype (F i))
  | .inr j => (inferInstance : Fintype (G j))

section PDCTensor

open Probability

variable {O O' J J' : Type} [Fintype O] [Fintype O'] [Fintype J] [Fintype J']
  {U₁ V₁ : O → Type} {U₂ V₂ : O' → Type} {X₁ Y₁ : J → Type} {X₂ Y₂ : J' → Type}
  [∀ o, Fintype (U₁ o)] [∀ o, Fintype (V₁ o)] [∀ o, Fintype (U₂ o)] [∀ o, Fintype (V₂ o)]
  [∀ j, Fintype (X₁ j)] [∀ j, Fintype (Y₁ j)] [∀ j, Fintype (X₂ j)] [∀ j, Fintype (Y₂ j)]
  {E₁ : List (Σ j, X₁ j) → Prop} {m₁ : ℕ} {hE₁ : ∀ h, E₁ h → h.length ≤ m₁}
  {E₂ : List (Σ j, X₂ j) → Prop} {m₂ : ℕ} {hE₂ : ∀ h, E₂ h → h.length ≤ m₂}
  {F₁ : List (Σ o, U₁ o) → Prop} {n₁ : ℕ} {hF₁ : ∀ h, F₁ h → h.length ≤ n₁}
  {F₂ : List (Σ o, U₂ o) → Prop} {n₂ : ℕ} {hF₂ : ∀ h, F₂ h → h.length ≤ n₂}

/-- The parallel composition of two PDCs: independent samples, side by side (CR18,
Definition 3.17). -/
noncomputable def tensorPDC {bα bβ : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U₁ V₁ X₁ Y₁ // IsDDCFrom E₁ F₁ bα a})
    (Q : Distribution.ProbDist {b : InsideOutsideSystem O' J' U₂ V₂ X₂ Y₂ // IsDDCFrom E₂ F₂ bβ b}) :
    Distribution.ProbDist {c : InsideOutsideSystem (O ⊕ O') (J ⊕ J') (Sum.rec U₁ U₂)
        (Sum.rec V₁ V₂) (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂) //
      IsDDCFrom (parallelInputs (F := Sum.rec X₁ X₂) E₁ E₂)
        (parallelInputs (F := Sum.rec U₁ U₂) F₁ F₂) (max bα bβ) c} :=
  ⟨Distribution.fTransform (fun st => ⟨tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂)
      (Xi := Sum.rec X₁ X₂) (Yi := Sum.rec Y₁ Y₂) st.1.1 st.2.1,
      IsDDCFrom.tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂) (X := Sum.rec X₁ X₂)
        (Y := Sum.rec Y₁ Y₂) st.1.2 st.2.2⟩)
    (Distribution.prod P.1 Q.1),
    Distribution.fTransform_isProbDist _ (Distribution.prod_isProbDist P.1 Q.1 P.2 Q.2)⟩

/-- On admitted joint transcripts, the parallel composition of presentations has the product
of the component behaviors. -/
theorem behaviorMass_tensorPDC {bα bβ : ℕ}
    {R : RandomSystem (Σ l, twoFam U₁ Y₁ l) (Σ l, twoFam V₁ X₁ l)
      (Domain.converter E₁ m₁ hE₁ F₁ n₁ hF₁)}
    {S : RandomSystem (Σ l, twoFam U₂ Y₂ l) (Σ l, twoFam V₂ X₂ l)
      (Domain.converter E₂ m₂ hE₂ F₂ n₂ hF₂)}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U₁ V₁ X₁ Y₁ // IsDDCFrom E₁ F₁ bα a})
    (Q : Distribution.ProbDist {b : InsideOutsideSystem O' J' U₂ V₂ X₂ Y₂ // IsDDCFrom E₂ F₂ bβ b})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = R h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = S h)
    (h : List ((Σ l, twoFam (Sum.rec U₁ U₂) (Sum.rec Y₁ Y₂) l) ×
      (Σ l, twoFam (Sum.rec V₁ V₂) (Sum.rec X₁ X₂) l))) :
    behaviorMass (tensorPDC P Q).1 (h.map Prod.fst) (h.map Prod.snd) =
      if Admitted converterAdmits h then
        RandomSystem.parallel R S (h.map (tensorInputs.prodCongr tensorOutputs.symm))
      else 0 := by
  simp only [tensorPDC, behaviorMass, Distribution.mass_fTransform]
  rw [RandomSystem.parallel_mass_of_presentations R S P.1 Q.1 Subtype.val Subtype.val
    (fun h => (hP h).symm) (fun h => (hQ h).symm)]
  have key (a : InsideOutsideSystem O J U₁ V₁ X₁ Y₁) (b : InsideOutsideSystem O' J' U₂ V₂ X₂ Y₂) :
      Replies (tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂) (Xi := Sum.rec X₁ X₂)
          (Yi := Sum.rec Y₁ Y₂) a b) (h.map Prod.fst) (h.map Prod.snd) ↔
        Admitted converterAdmits h ∧
          Replies (pair a b) ((h.map (tensorInputs.prodCongr tensorOutputs.symm)).map Prod.fst)
            ((h.map (tensorInputs.prodCongr tensorOutputs.symm)).map Prod.snd) := by
    rw [show tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂) (Xi := Sum.rec X₁ X₂)
        (Yi := Sum.rec Y₁ Y₂) a b = canon (tensorRaw (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂)
          (Xi := Sum.rec X₁ X₂) (Yi := Sum.rec Y₁ Y₂) a b) from rfl,
      replies_canon_iff _ (tensorRaw_silentAtEmpty (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂)
        (X := Sum.rec X₁ X₂) (Y := Sum.rec Y₁ Y₂) a b) h]
    refine and_congr Iff.rfl ?_
    exact replies_relabel_iff _ (tensorInputs (U := Sum.rec U₁ U₂) (Y := Sum.rec Y₁ Y₂))
      (tensorOutputs (V := Sum.rec V₁ V₂) (X := Sum.rec X₁ X₂)) h
  refine (Distribution.mass_congr (Distribution.prod P.1 Q.1)
    (fun st => key st.1.1 st.2.1)).trans ?_
  by_cases hh : Admitted converterAdmits h
  · simp only [hh, if_true, true_and]
    rfl
  · simp only [hh, if_false, false_and]
    exact Distribution.mass_eq_zero_of_forall_not _ (fun _ hf => hf)

namespace PDCBehavior

/-- **Parallel composition** (CR18, Definition 3.17): the two PDCs are sampled independently
and run side by side on disjoint interfaces. -/
noncomputable def tensor (α : PDCBehavior O J U₁ V₁ X₁ Y₁ E₁ m₁ hE₁ F₁ n₁ hF₁)
    (β : PDCBehavior O' J' U₂ V₂ X₂ Y₂ E₂ m₂ hE₂ F₂ n₂ hF₂) :
    PDCBehavior (O ⊕ O') (J ⊕ J') (Sum.rec U₁ U₂) (Sum.rec V₁ V₂) (Sum.rec X₁ X₂)
      (Sum.rec Y₁ Y₂) (parallelInputs (F := Sum.rec X₁ X₂) E₁ E₂) (m₁ + m₂)
      (parallelInputs_length_le hE₁ hE₂) (parallelInputs (F := Sum.rec U₁ U₂) F₁ F₂) (n₁ + n₂)
      (parallelInputs_length_le hF₁ hF₂) :=
  ofPDC (tensorPDC α.2.choose_spec.choose β.2.choose_spec.choose)

/-- **The parallel composition of presentations presents the parallel composition.** -/
theorem tensor_presents (α : PDCBehavior O J U₁ V₁ X₁ Y₁ E₁ m₁ hE₁ F₁ n₁ hF₁)
    (β : PDCBehavior O' J' U₂ V₂ X₂ Y₂ E₂ m₂ hE₂ F₂ n₂ hF₂) {bα bβ : ℕ}
    (P : Distribution.ProbDist {a : InsideOutsideSystem O J U₁ V₁ X₁ Y₁ // IsDDCFrom E₁ F₁ bα a})
    (Q : Distribution.ProbDist {b : InsideOutsideSystem O' J' U₂ V₂ X₂ Y₂ // IsDDCFrom E₂ F₂ bβ b})
    (hP : ∀ h, behaviorMass P.1 (h.map Prod.fst) (h.map Prod.snd) = α.1 h)
    (hQ : ∀ h, behaviorMass Q.1 (h.map Prod.fst) (h.map Prod.snd) = β.1 h)
    (h : List ((Σ l, twoFam (Sum.rec U₁ U₂) (Sum.rec Y₁ Y₂) l) ×
      (Σ l, twoFam (Sum.rec V₁ V₂) (Sum.rec X₁ X₂) l))) :
    (tensor α β).1 h = behaviorMass (tensorPDC P Q).1 (h.map Prod.fst) (h.map Prod.snd) := by
  change behaviorMass (tensorPDC _ _).1 _ _ = _
  rw [behaviorMass_tensorPDC _ _ α.2.choose_spec.choose_spec β.2.choose_spec.choose_spec,
    behaviorMass_tensorPDC P Q hP hQ]

/-- The parallel composition of two DDCs as behaviors is the behavior of their parallel
composition. -/
theorem tensor_ofDDC {a : InsideOutsideSystem O J U₁ V₁ X₁ Y₁}
    {c : InsideOutsideSystem O' J' U₂ V₂ X₂ Y₂} {bα bβ : ℕ}
    (ha : IsDDCFrom E₁ F₁ bα a) (hc : IsDDCFrom E₂ F₂ bβ c) :
    tensor (ofDDC a ha : PDCBehavior O J U₁ V₁ X₁ Y₁ E₁ m₁ hE₁ F₁ n₁ hF₁)
      (ofDDC c hc : PDCBehavior O' J' U₂ V₂ X₂ Y₂ E₂ m₂ hE₂ F₂ n₂ hF₂) =
      ofDDC (tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂) (Xi := Sum.rec X₁ X₂)
        (Yi := Sum.rec Y₁ Y₂) a c)
        (IsDDCFrom.tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂) (X := Sum.rec X₁ X₂)
          (Y := Sum.rec Y₁ Y₂) ha hc) := by
  apply ext
  intro h
  rw [tensor_presents _ _ ⟨Finsupp.single ⟨a, ha⟩ 1, Distribution.isProbDist_single _⟩
    ⟨Finsupp.single ⟨c, hc⟩ 1, Distribution.isProbDist_single _⟩ (fun _ => rfl) (fun _ => rfl)]
  change _ = behaviorMass (Finsupp.single _ 1) _ _
  simp only [tensorPDC, behaviorMass, Distribution.mass_fTransform, Distribution.prod_single_left,
    Distribution.mass_single]

end PDCBehavior

end PDCTensor

section TensorIdentity

open Probability

variable {J J' : Type} [Fintype J] [Fintype J'] {X₁ Y₁ : J → Type} {X₂ Y₂ : J' → Type}
  [∀ j, Fintype (X₁ j)] [∀ j, Fintype (Y₁ j)] [∀ j, Fintype (X₂ j)] [∀ j, Fintype (Y₂ j)]
  {E₁ : List (Σ j, X₁ j) → Prop} {m₁ : ℕ} {hE₁ : ∀ h, E₁ h → h.length ≤ m₁}
  {E₂ : List (Σ j, X₂ j) → Prop} {m₂ : ℕ} {hE₂ : ∀ h, E₂ h → h.length ≤ m₂}

/-- **The parallel composition of the identities** from `E₁` to `E₁` and from `E₂` to `E₂` is the
identity from `E₁ ∥ E₂` to `E₁ ∥ E₂`. -/
theorem PDCBehavior.tensor_id (hE₁' : ¬ E₁ [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E₁ h → E₁ p)
    (hE₂' : ¬ E₂ [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E₂ h → E₂ p) :
    PDCBehavior.tensor (PDCBehavior.id (Y := Y₁) (m := m₁) (hE := hE₁) hE₁')
      (PDCBehavior.id (Y := Y₂) (m := m₂) (hE := hE₂) hE₂') =
      PDCBehavior.id (parallelInputs_nonempty_prefix (F := Sum.rec X₁ X₂) hE₁'.2 hE₂'.2) := by
  have hle {K : Type} {A B : K → Type} (D : List (Σ k, A k) → Prop)
      (hD : ∀ {p h}, p <+: h → D h → D p) :
      ∀ h y, y ∈ (DDC.filter (Y := B) D hD).1 h → y ∈ forwardAll K A B h :=
    fun h y hy => canon_mem ((filterDom_mem_iff _ _ h y).mp hy).2
  rw [PDCBehavior.id, PDCBehavior.id, PDCBehavior.tensor_ofDDC, PDCBehavior.id]
  refine PDCBehavior.ofDDC_eq_of_le _ _
    (W := forwardAll (J ⊕ J') (Sum.rec X₁ X₂) (Sum.rec Y₁ Y₂)) ?_ ?_
  · intro xs ys hr
    rw [← tensorRaw_forwardAll]
    exact hr.mono fun h y hy => tensorRaw_mono (hle _ (prefix_or_nil hE₁'.2))
      (hle _ (prefix_or_nil hE₂'.2)) h y (canon_mem hy)
  · intro xs ys hr
    exact hr.mono (hle _ (prefix_or_nil (parallelInputs_nonempty_prefix hE₁'.2 hE₂'.2).2))

end TensorIdentity

section Interchange

open Probability

variable {O O' M M' J J' : Type} [Fintype O] [Fintype O'] [Fintype M] [Fintype M'] [Fintype J]
  [Fintype J'] {U₁ V₁ : O → Type} {U₂ V₂ : O' → Type} {Xm₁ Ym₁ : M → Type}
  {Xm₂ Ym₂ : M' → Type} {X₁ Y₁ : J → Type} {X₂ Y₂ : J' → Type}
  [∀ o, Fintype (U₁ o)] [∀ o, Fintype (V₁ o)] [∀ o, Fintype (U₂ o)] [∀ o, Fintype (V₂ o)]
  [∀ k, Fintype (Xm₁ k)] [∀ k, Fintype (Ym₁ k)] [∀ k, Fintype (Xm₂ k)] [∀ k, Fintype (Ym₂ k)]
  [∀ j, Fintype (X₁ j)] [∀ j, Fintype (Y₁ j)] [∀ j, Fintype (X₂ j)] [∀ j, Fintype (Y₂ j)]
  {E₁ : List (Σ j, X₁ j) → Prop} {m₁ : ℕ} {hE₁ : ∀ h, E₁ h → h.length ≤ m₁}
  {E₂ : List (Σ j, X₂ j) → Prop} {m₂ : ℕ} {hE₂ : ∀ h, E₂ h → h.length ≤ m₂}
  {F₁ : List (Σ k, Xm₁ k) → Prop} {n₁ : ℕ} {hF₁ : ∀ h, F₁ h → h.length ≤ n₁}
  {F₂ : List (Σ k, Xm₂ k) → Prop} {n₂ : ℕ} {hF₂ : ∀ h, F₂ h → h.length ≤ n₂}
  {G₁ : List (Σ o, U₁ o) → Prop} {q₁ : ℕ} {hG₁ : ∀ h, G₁ h → h.length ≤ q₁}
  {G₂ : List (Σ o, U₂ o) → Prop} {q₂ : ℕ} {hG₂ : ∀ h, G₂ h → h.length ≤ q₂}

/-- **Interchange**: serial composition of parallel compositions is parallel composition of
serial compositions. -/
theorem PDCBehavior.comp_tensor (α : PDCBehavior O M U₁ V₁ Xm₁ Ym₁ F₁ n₁ hF₁ G₁ q₁ hG₁)
    (β : PDCBehavior O' M' U₂ V₂ Xm₂ Ym₂ F₂ n₂ hF₂ G₂ q₂ hG₂)
    (γ : PDCBehavior M J Xm₁ Ym₁ X₁ Y₁ E₁ m₁ hE₁ F₁ n₁ hF₁)
    (δ : PDCBehavior M' J' Xm₂ Ym₂ X₂ Y₂ E₂ m₂ hE₂ F₂ n₂ hF₂) :
    PDCBehavior.comp (PDCBehavior.tensor α β) (PDCBehavior.tensor γ δ) =
      PDCBehavior.tensor (PDCBehavior.comp α γ) (PDCBehavior.comp β δ) := by
  obtain ⟨ba, P, hP⟩ := α.2
  obtain ⟨bb, Q, hQ⟩ := β.2
  obtain ⟨bc, R, hR⟩ := γ.2
  obtain ⟨bd, S, hS⟩ := δ.2
  apply PDCBehavior.ext
  intro h
  rw [PDCBehavior.comp_presents _ _ (tensorPDC P Q) (tensorPDC R S)
      (fun h => (PDCBehavior.tensor_presents α β P Q hP hQ h).symm)
      (fun h => (PDCBehavior.tensor_presents γ δ R S hR hS h).symm),
    PDCBehavior.tensor_presents _ _ (compPDC P R) (compPDC Q S)
      (fun h => (PDCBehavior.comp_presents α γ P R hP hR h).symm)
      (fun h => (PDCBehavior.comp_presents β δ Q S hQ hS h).symm),
    behaviorMass_compPDC]
  simp only [tensorPDC, compPDC, behaviorMass, Distribution.fTransform_prod_left,
    Distribution.fTransform_prod_right, Distribution.mass_fTransform]
  rw [← Distribution.independent_product_middle P.1 Q.1 R.1 S.1, Distribution.mass_fTransform]
  apply Distribution.mass_congr
  intro abcd
  simp only [Prod.map_fst, Prod.map_snd, id_eq]
  exact iff_of_eq (congrArg (fun t => Replies t (h.map Prod.fst) (h.map Prod.snd))
    (IsDDC.trim_serialM_tensorL (U := Sum.rec U₁ U₂) (V := Sum.rec V₁ V₂)
      (Xm := Sum.rec Xm₁ Xm₂) (Ym := Sum.rec Ym₁ Ym₂) (X := Sum.rec X₁ X₂) (Y := Sum.rec Y₁ Y₂)
      abcd.1.1.2.isDDC abcd.1.2.2.isDDC abcd.2.1.2.isDDC abcd.2.2.2.isDDC))

end Interchange

/-! ## Attachment to parallel systems -/



/-- Trimming either constituent preserves the completed parallel behavior. -/
theorem trim_pair_trim {A B C D : Type} (s : System A B) (t : System C D) :
    trim (pair (trim s) (trim t)) = trim (pair s t) := by
  apply EqOnReachable.trim_eq
  · exact EqOnReachable.parAll (fun k => by cases k <;> exact trim_behEq _)
  · exact Part.not_none_dom
  · exact Part.not_none_dom

theorem RepliesAtQueriedInterface.trim {I : Type} {X Y : I → Type} {R : InterfaceSystem I X Y}
    (hR : RepliesAtQueriedInterface R) : RepliesAtQueriedInterface (SystemAlgebra.trim R) := by
  intro h x y hy
  unfold SystemAlgebra.trim at hy
  split_ifs at hy with hr
  · exact hR h x y hy
  · exact (Part.not_none_dom hy.1).elim

/-- The component tag and its original interface label both accompany the reply. -/
theorem RepliesAtQueriedInterface.parallel {I J : Type} {X Y : I ⊕ J → Type}
    {R : InterfaceSystem I (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {S : InterfaceSystem J (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    (hR : RepliesAtQueriedInterface R) (hS : RepliesAtQueriedInterface S) :
    RepliesAtQueriedInterface (SystemAlgebra.relabel (pair R S) (sumAlphabet X).symm (sumAlphabet Y)) := by
  intro h x y hy
  obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
  simp only [List.map_append, List.map_singleton] at hv
  rcases x with ⟨(i | j), x⟩
  · change v ∈ pair R S (h.map (sumAlphabet X).symm ++ [⟨none, ⟨i, x⟩⟩]) at hv
    rw [pair_left] at hv
    obtain ⟨z, hz, he⟩ := (Part.mem_map_iff _).mp hv
    subst v
    exact congrArg Sum.inl (hR (restrict none (h.map (sumAlphabet X).symm)) ⟨i, x⟩ z hz)
  · change v ∈ pair R S (h.map (sumAlphabet X).symm ++ [⟨some (), ⟨j, x⟩⟩]) at hv
    rw [pair_right] at hv
    obtain ⟨z, hz, he⟩ := (Part.mem_map_iff _).mp hv
    subst v
    exact congrArg Sum.inr (hS (restrict (some ()) (h.map (sumAlphabet X).symm)) ⟨j, x⟩ z hz)

section Tensor

variable {O O' J J' : Type} {U V : O ⊕ O' → Type} {X Y : J ⊕ J' → Type}
    {α : InsideOutsideSystem O J (U ∘ Sum.inl) (V ∘ Sum.inl) (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {β : InsideOutsideSystem O' J' (U ∘ Sum.inr) (V ∘ Sum.inr) (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    {ba bb : ℕ}

/-- Each converter interacts only with its own component. -/
theorem apply_tensorRaw_pair (ha : IsDDC ba α) (hb : IsDDC bb β)
    (R : InterfaceSystem J (X ∘ Sum.inl) (Y ∘ Sum.inl))
    (S : InterfaceSystem J' (X ∘ Sum.inr) (Y ∘ Sum.inr)) :
    apply (tensorRaw α β) (relabel (pair R S) (sumAlphabet X).symm (sumAlphabet Y)) =
      relabel (pair (apply α R) (apply β S)) (sumAlphabet U).symm (sumAlphabet V) := by
  simp only [apply_eq, tensorRaw, pair_relabel, interconnect_relabel]
  rw [pair_interconnect_left (ha.converges_resource R),
    pair_interconnect_right (pair α R) (hb.converges_resource S),
    interconnect_interconnect, relabel_interconnect,
    pair_middle α β R S, interconnect_relabel]
  congr 1
  · funext z
    rcases z with ⟨(_ | ⟨⟩), ⟨(_ | ⟨⟩), z⟩⟩
    · rcases z with ⟨⟨(_ | ⟨⟩), i⟩, z⟩ <;> rfl
    · rcases z with ⟨i, z⟩; rfl
    · rcases z with ⟨⟨(_ | ⟨⟩), i⟩, z⟩ <;> rfl
    · rcases z with ⟨i, z⟩; rfl
  · funext z
    rcases z with ⟨(i | j), z⟩ <;> rfl

/-- The canonical tensor has the same completed partial behavior. -/
theorem trim_apply_tensorL_pair (ha : IsDDC ba α) (hb : IsDDC bb β)
    {R : InterfaceSystem J (X ∘ Sum.inl) (Y ∘ Sum.inl)}
    {S : InterfaceSystem J' (X ∘ Sum.inr) (Y ∘ Sum.inr)}
    (hR : RepliesAtQueriedInterface R) (hS : RepliesAtQueriedInterface S) :
    trim (apply (tensorL α β)
      (relabel (trim (pair R S)) (sumAlphabet X).symm (sumAlphabet Y))) =
    relabel (trim (pair (trim (apply α R)) (trim (apply β S))))
      (sumAlphabet U).symm (sumAlphabet V) := by
  have he := (EqOnReachable.rfl' (tensorL α β)).apply
    ((trim_behEq (pair R S)).relabel (sumAlphabet X).symm (sumAlphabet Y))
  have ht := he.trim_eq (by simp [SilentAtEmpty, apply_eq]) (by simp [SilentAtEmpty, apply_eq])
  rw [ht, tensorL, trim_apply_canon (ha.tensorL hb) (hR.parallel hS),
    apply_tensorRaw_pair ha hb, trim_relabel, trim_pair_trim]

end Tensor

end SystemAlgebra

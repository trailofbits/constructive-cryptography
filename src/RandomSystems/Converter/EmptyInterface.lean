import RandomSystems.Converter.ConverterDomain

/-!
# Converters with an empty interface

A deterministic system is a DDC with no inside interface: `resourceDDC s` reads its inputs
as outside queries and makes no inside calls. When `s` answers exactly on the histories of
`F`, it is a DDC from the empty domain to `F`. Dually, the DDC with no outside interface
never replies; it is a DDC from any domain to the empty domain.

## Main definitions

* `resourceDDC s`: `s` as a DDC with no inside interface
* `resourcePDC Q`: the DDC readings of a PDS of deterministic systems
* `discardSystem J X Y`: the DDC with no outside interface

## Main results

* `apply_resourceDDC`: attaching `resourceDDC s` to a system on the empty interface gives `s`
* `resourceDDC_isDDCFrom`, `discardSystem_isDDCFrom`: their domains
-/

namespace SystemAlgebra

open Classical Probability

variable {O : Type} {U V : O → Type}

/-! ## A deterministic system as a DDC with no inside interface -/

/-- With no inside labels, the converter's inputs are the system's inputs. -/
def outsideInput (U : O → Type) :
    (Σ l : Two O Empty, twoFam U (Empty.elim : Empty → Type) l) ≃ Σ o, U o where
  toFun
    | ⟨⟨none, o⟩, u⟩ => ⟨o, u⟩
    | ⟨⟨some (), e⟩, _⟩ => e.elim
  invFun z := ⟨⟨none, z.1⟩, z.2⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩
    · rfl
    · exact o.elim
  right_inv _ := rfl

/-- With no inside labels, the converter's outputs are the system's outputs. -/
def outsideOutput (V : O → Type) :
    (Σ l : Two O Empty, twoFam V (Empty.elim : Empty → Type) l) ≃ Σ o, V o where
  toFun
    | ⟨⟨none, o⟩, v⟩ => ⟨o, v⟩
    | ⟨⟨some (), e⟩, _⟩ => e.elim
  invFun z := ⟨⟨none, z.1⟩, z.2⟩
  left_inv := by
    rintro ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
    · rfl
    · exact o.elim
  right_inv _ := rfl

/-- A deterministic system read as a converter with no inside interface. -/
def resourceDDC (s : InterfaceSystem O U V) :
    InsideOutsideSystem O Empty U V Empty.elim Empty.elim :=
  relabel s (outsideInput U) (outsideOutput V).symm

theorem not_isInside_unit (y : Σ l : Two O Empty, twoFam V (Empty.elim : Empty → Type) l) :
    ¬ IsInside y := by
  intro hy
  rcases y with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, _⟩
  · simp [IsInside] at hy
  · exact j.elim

theorem resourceDDC_isDDC {s : InterfaceSystem O U V} (hs : IsDDS s)
    (hr : RepliesAtQueriedInterface s) : IsDDC 0 (resourceDDC s) where
  dds := ⟨by simpa [SilentAtEmpty, resourceDDC, relabel] using hs.1,
    fun l₁ l₂ hp hne hd => by
      simp only [resourceDDC, relabel, Part.map_Dom] at hd ⊢
      exact hs.2 (hp.map _) (by simpa using hne) hd⟩
  admits h z _ := by
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · exact (admitAfter_of_ne (fun j => j.elim)).mpr rfl
    · exact i.elim
  bound h _ := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
    · simp [insideRun]
    · rw [List.concat_eq_append, insideRun, run_snoc,
        if_neg (fun ⟨y, _, hy⟩ => not_isInside_unit y hy)]
  replies h y o hy hl := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
    · exact absurd (Part.dom_iff_mem.mpr ⟨y, hy⟩)
        (by simpa [resourceDDC, relabel, SilentAtEmpty] using hs.1)
    rw [List.concat_eq_append] at hy ⊢
    obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · have hl' := hr (h.map (outsideInput U)) ((outsideInput U) ⟨⟨none, i⟩, x⟩) y'
        (by simpa only [List.map_append, List.map_singleton] using hy')
      have ho : y'.1 = o := eq_of_heq ((Sigma.mk.inj_iff.mp hl).2)
      rw [lastOuter_snoc]
      simp only [outerOf, Option.some_or]
      rw [← ho, hl']
      rfl
    · exact i.elim

/-- Attaching a system with no inside interface reads the system itself. -/
theorem apply_resourceDDC (s : InterfaceSystem O U V) (hs : SilentAtEmpty s)
    (t : InterfaceSystem Empty Empty.elim Empty.elim) :
    apply (resourceDDC s) t = s := by
  let g : Two (Σ l : Two O Empty, twoFam V (Empty.elim : Empty → Type) l)
      (Σ j, (Empty.elim : Empty → Type) j) → Σ o, V o
    | ⟨none, ⟨⟨none, o⟩, v⟩⟩ => ⟨o, v⟩
    | ⟨none, ⟨⟨some (), j⟩, _⟩⟩ => j.elim
    | ⟨some (), ⟨j, _⟩⟩ => j.elim
  rw [apply_eq, interconnect_no_feedback (g := g) (by simp [SilentAtEmpty, pair]) (by
    rintro ⟨_ | ⟨⟨⟩⟩, ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩⟩ <;> first | rfl | exact o.elim)]
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, u, rfl⟩
  · have h1 : SilentAtEmpty (pair (resourceDDC s) t) := by simp [SilentAtEmpty, pair]
    simp only [relabel, List.map_nil]
    rw [Part.eq_none_iff'.mpr h1, Part.eq_none_iff'.mpr hs, Part.map_none]
  · rw [List.concat_eq_append]
    simp only [relabel, List.map_append, List.map_singleton, resourceInput]
    rw [pair_left]
    have hr : restrict none (h.map (resourceInput (X := (Empty.elim : Empty → Type))
        (Y := (Empty.elim : Empty → Type)))) = h.map (outsideInput U).symm := by
      induction h with
      | nil => rfl
      | cons u h ih => simp only [List.map_cons, resourceInput, restrict_none_cons_none, ih]; rfl
    rw [hr]
    simp only [resourceDDC, relabel, Part.map_map, List.map_append, List.map_map,
      List.map_singleton]
    have hi : (outsideInput U) ∘ (outsideInput U).symm = id := by
      funext z; exact (outsideInput U).apply_symm_apply z
    rw [hi, List.map_id]
    exact Part.map_id' (fun _ => rfl) _

/-- With no inside labels, the outside inputs are all inputs. -/
theorem outsideInputs_unit (xs : List (Σ l : Two O Empty, twoFam U (Empty.elim : Empty → Type) l)) :
    outsideInputs xs = xs.map (outsideInput U) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
    · rw [← List.singleton_append, outsideInputs_append, outsideInputs_outside, ih]
      rfl
    · exact i.elim

/-- With no inside labels, there are no inside queries. -/
theorem insideQueries_unit (ys : List (Σ l : Two O Empty, twoFam V (Empty.elim : Empty → Type) l)) :
    insideQueries ys = [] := by
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    rcases y with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · rw [← List.singleton_append, insideQueries_append, insideQueries_outside, ih]
      rfl
    · exact i.elim

/-- With no inside labels, every outside query is admitted after every transcript. -/
theorem converterAdmits_unit
    (h : List ((Σ l : Two O Empty, twoFam U (Empty.elim : Empty → Type) l) ×
      (Σ l : Two O Empty, twoFam V (Empty.elim : Empty → Type) l)))
    (x : Σ l : Two O Empty, twoFam U (Empty.elim : Empty → Type) l) :
    converterAdmits h x := by
  rcases x with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, x⟩
  · refine (admitAfter_of_ne fun j => ?_).mpr rfl
    exact j.elim
  · exact i.elim

/-- The DDC reading of a deterministic system that answers exactly on `F` is a DDC from the
empty domain to `F`. -/
theorem resourceDDC_isDDCFrom {F : List (Σ o, U o) → Prop} {s : InterfaceSystem O U V}
    (hs : IsDDS s) (hr : RepliesAtQueriedInterface s) (hd : ∀ h, (s h).Dom ↔ F h) :
    IsDDCFrom (fun _ => False) F 0 (resourceDDC s) where
  isDDC := resourceDDC_isDDC hs hr
  answers h x _ := by
    change (s ((h.map Prod.fst ++ [x]).map (outsideInput U))).Dom ↔ _
    rw [hd]
    unfold converterDomain
    rw [outsideInputs_unit, insideQueries_unit]
    exact ⟨fun hx => ⟨fun p z _ _ => converterAdmits_unit p z.1, converterAdmits_unit h x, hx,
      Or.inl rfl⟩, fun hx => hx.2.2.1⟩
  queries h _ := Or.inl (insideQueries_unit _)

/-- The DDC readings of a PDS of deterministic systems that answer exactly on `F`. -/
noncomputable def resourcePDC {F : List (Σ o, U o) → Prop}
    (Q : Distribution.ProbDist {s : InterfaceSystem O U V //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ F h}) :
    Distribution.ProbDist {a : InsideOutsideSystem O Empty U V Empty.elim Empty.elim //
      IsDDCFrom (fun _ => False) F 0 a} :=
  ⟨Distribution.fTransform (fun s => ⟨resourceDDC s.1,
      resourceDDC_isDDCFrom s.2.1 s.2.2.1 s.2.2.2⟩) Q.1,
    Distribution.fTransform_isProbDist _ Q.2⟩

/-! ## The DDC with no outside interface -/

/-- With no outside interface there are no invocations and no inside queries. -/
def discardSystem (J : Type) (X Y : J → Type) :
    InsideOutsideSystem Empty J Empty.elim Empty.elim X Y :=
  fun _ => Part.none

theorem discardSystem_isDDC (J : Type) (X Y : J → Type) : IsDDC 0 (discardSystem J X Y) where
  dds := ⟨Part.not_none_dom, fun _ _ _ _ hd => (Part.not_none_dom hd).elim⟩
  admits _ _ hd := (Part.not_none_dom hd).elim
  bound _ hd := (Part.not_none_dom hd).elim
  replies _ _ _ hy := (Part.notMem_none _ hy).elim

theorem discardSystem_isDDCFrom {J : Type} {X Y : J → Type} (E : List (Σ j, X j) → Prop) :
    IsDDCFrom E (fun _ => False) 0 (discardSystem J X Y) where
  isDDC := discardSystem_isDDC J X Y
  answers h x _ := by
    refine iff_of_false Part.not_none_dom fun hd => ?_
    exact hd.2.2.1
  queries h hr := by
    rcases List.eq_nil_or_concat h with rfl | ⟨h, z, rfl⟩
    · exact Or.inl rfl
    · simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hr
      exact absurd (replies_snoc.mp hr).2 (Part.some_ne_none _).symm

end SystemAlgebra

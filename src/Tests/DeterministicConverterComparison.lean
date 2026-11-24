module

public import RandomSystems.Typed.Parallel
public import ConstructiveCryptography.Notation

/-!
# Tests for deterministic converter comparison and closure

* Two history functions differing on unreachable histories have equal reachable DDCs and define
  one typed converter (`IsDDCFrom.eq_of_next_eq`, `TypedConverter.ofDDC_eq_of_next_eq`), even
  under distinct certified internal-query bounds.
* `TypedConverter.ofDDC_eq_iff_replies` and `TypedConverter.ofDDC_eq_iff` characterize equality
  of deterministic typed converters.
* `(ofDDC α ⊗ₘ ofDDC γ) ≫ ofDDC β`, `(ofDDC α ≫ ofDDC β) ⊗ₘ ofDDC γ`, identities, and parallel
  compositions with identities each reduce to a single `TypedConverter.ofDDC`.
* `cc_normalize` interacts cleanly with deterministic converters under `⊗ₘ`, `≫`, `𝟙`, `•`, `∥`.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.DeterministicConverterComparison

open CategoryTheory CategoryTheory.MonoidalCategory
open SystemAlgebra
open scoped SystemAlgebra

/-- A one-port Boolean interface with a 1-query budget. -/
abbrev BoolPort : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 1

/-- Raw history function that echoes outside queries directly and returns `fallback` on
unreachable histories ending in an inside reply. -/
def echoWithFallback (fallback : Bool) :
    InsideOutsideSystem Unit Unit (fun _ => Bool) (fun _ => Bool)
      (fun _ => Bool) (fun _ => Bool) := fun h =>
  match h.getLast? with
  | some ⟨⟨none, ()⟩, b⟩ => Part.some ⟨⟨none, ()⟩, b⟩
  | some ⟨⟨some (), ()⟩, _⟩ => Part.some ⟨⟨none, ()⟩, fallback⟩
  | none => Part.none

/-- `echoWithFallback false` and `echoWithFallback true` differ on an unreachable inside reply. -/
lemma echoWithFallback_ne : echoWithFallback false ≠ echoWithFallback true := by
  intro h
  have h1 := congrFun h [⟨⟨some (), ()⟩, false⟩]
  simp [echoWithFallback] at h1

lemma echoWithFallback_snoc_outer (fallback : Bool)
    (h : List (Σ l, twoFam (fun _ : Unit => Bool) (fun _ : Unit => Bool) l)) (b : Bool) :
    echoWithFallback fallback (h ++ [⟨⟨none, ()⟩, b⟩]) = Part.some ⟨⟨none, ()⟩, b⟩ := by
  simp [echoWithFallback]

lemma echoWithFallback_dom (fallback : Bool)
    {h : List (Σ l, twoFam (fun _ : Unit => Bool) (fun _ : Unit => Bool) l)} (hne : h ≠ []) :
    (echoWithFallback fallback h).Dom := by
  obtain ⟨h₀, z, rfl⟩ := (List.eq_nil_or_concat h).resolve_left hne
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨⟩⟩, b⟩ <;> simp [echoWithFallback]

lemma echoWithFallback_not_inside (fallback : Bool)
    {h : List (Σ l, twoFam (fun _ : Unit => Bool) (fun _ : Unit => Bool) l)}
    {y : Σ l, twoFam (fun _ : Unit => Bool) (fun _ : Unit => Bool) l}
    (hy : y ∈ echoWithFallback fallback h) : y.1 = ⟨none, ()⟩ := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
  · simp [echoWithFallback] at hy
  · rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨⟩⟩, b⟩ <;>
      · simp only [echoWithFallback, List.concat_eq_append, List.getLast?_append,
          List.getLast?_singleton, Option.some_or, Part.mem_some_iff] at hy
        subst hy; rfl

lemma echoWithFallback_canon_isResponsiveDDC (fallback : Bool) (b : ℕ) :
    IsResponsiveDDC b (canon (echoWithFallback fallback)) := by
  -- Canonicalization removes unreachable inputs; the remaining converter echoes every request.
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, canon, echoWithFallback]
  · intro l₁ l₂ hp hne hd
    have ha₂ : Admissible (echoWithFallback fallback) l₂ := by
      by_contra hc; simp [canon, hc] at hd
    obtain ⟨e, rfl⟩ := hp
    rw [canon_of_admissible ha₂.of_append]
    exact echoWithFallback_dom fallback hne
  · intro h z hd
    have ha : Admissible (echoWithFallback fallback) (h ++ [z]) := by
      by_contra hc; simp [canon, hc] at hd
    obtain ⟨hh, -, hz⟩ := admissible_snoc.mp ha
    simpa [Admits, replyLabel_canon hh] using hz
  -- Every output is outside, so the inside-query run has length zero.
  · intro h hd
    rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
    · simp [insideRun]
    · rw [List.concat_eq_append, insideRun, run_snoc]
      have hnot : ¬ ∃ w ∈ canon (echoWithFallback fallback) (h₀ ++ [z]), IsInside w := by
        rintro ⟨w, hw, hwi⟩
        have hl := echoWithFallback_not_inside fallback (canon_mem hw)
        simp [IsInside, hl] at hwi
      simp [hnot]
  · intro h ha hne
    rw [admissible_canon_iff] at ha
    rw [canon_of_admissible ha]
    exact echoWithFallback_dom fallback hne
  -- An admitted inside reply would require an inside query, which echo never emits.
  · intro h y o hy hyo
    have ha : Admissible (echoWithFallback fallback) h := by
      by_contra hc; simp [canon, hc] at hy
    rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
    · simp [canon, echoWithFallback] at hy
    · rw [List.concat_eq_append] at ha hy ⊢
      obtain ⟨hh, -, hz⟩ := admissible_snoc.mp ha
      rcases z with ⟨⟨_ | ⟨⟨⟩⟩, ⟨⟩⟩, v⟩
      · simp [lastOuter_snoc, outerOf]
      · exfalso
        rcases List.eq_nil_or_concat h₀ with rfl | ⟨h₁, z₁, rfl⟩
        · simp [Admits, replyLabel, echoWithFallback, admitAfter] at hz
        · obtain ⟨w, hw⟩ :=
            Part.dom_iff_mem.mp (echoWithFallback_dom fallback (h := h₁.concat z₁) (by simp))
          have hrl := replyLabel_of_mem _ hw
          have hl := echoWithFallback_not_inside fallback hw
          rw [Admits, hrl, hl] at hz
          simp [admitAfter] at hz

/-- Reachable part of `echoWithFallback fallback` restricted to `BoolPort`. -/
noncomputable def reachableEcho (fallback : Bool) :
    InsideOutsideSystem BoolPort.I BoolPort.I BoolPort.X BoolPort.Y BoolPort.X BoolPort.Y :=
  filterDom (fun xs => outsideInputs xs = [] ∨ BoolPort.domain (outsideInputs xs))
    (canon (echoWithFallback fallback))

lemma reachableEcho_isDDCFrom (fallback : Bool) (b : ℕ) :
    IsDDCFrom BoolPort.domain BoolPort.domain b (reachableEcho fallback) := by
  refine (echoWithFallback_canon_isResponsiveDDC fallback b).isDDCFrom_filterDom
    BoolPort.nonempty_prefix.2 fun h hr => Or.inl ?_
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr', hy⟩ := replies_snoc.mp hr
    have hmem : y ∈ echoWithFallback fallback (h.map Prod.fst ++ [x]) :=
      canon_mem ((filterDom_mem_iff _ _ _ _).mp (Part.eq_some_iff.mp hy)).2
    have hl := echoWithFallback_not_inside fallback hmem
    rcases y with ⟨⟨l, j⟩, v⟩
    have hln : l = none := congrArg Sigma.fst hl
    subst hln
    rw [insideQueries_append, ih hr']
    simp [insideQueries, splitIn]

/-- The two differing history functions yield equal reachable DDCs and one typed converter,
even with distinct certified internal-query bounds `0` and `1`. -/
lemma reachableEcho_converter_eq :
    TypedConverter.ofDDC (reachableEcho false) (reachableEcho_isDDCFrom false 0) =
      TypedConverter.ofDDC (reachableEcho true) (reachableEcho_isDDCFrom true 1) := by
  apply TypedConverter.ofDDC_eq_of_next_eq
  intro t x hr0 hr1 hx
  have houter : x.1.1 = none := by
    have hct := hx.2.1
    rcases List.eq_nil_or_concat t with rfl | ⟨t₀, ⟨x₀, y₀⟩, rfl⟩
    · simpa [converterAdmits, admitAfter] using hct
    · simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hr0
      have hy0 := (replies_snoc.mp hr0).2
      have hmem : y₀ ∈ echoWithFallback false (t₀.map Prod.fst ++ [x₀]) :=
        canon_mem ((filterDom_mem_iff _ _ _ _).mp (Part.eq_some_iff.mp hy0)).2
      have hl := echoWithFallback_not_inside false hmem
      simpa [converterAdmits, hl, admitAfter] using hct
  have hd0 := ((reachableEcho_isDDCFrom false 0).answers t x hr0).mpr hx
  have hd1 := ((reachableEcho_isDDCFrom true 1).answers t x hr1).mpr hx
  obtain ⟨y0, hy0⟩ := Part.dom_iff_mem.mp hd0
  obtain ⟨y1, hy1⟩ := Part.dom_iff_mem.mp hd1
  have hm0 : y0 ∈ echoWithFallback false (t.map Prod.fst ++ [x]) :=
    canon_mem ((filterDom_mem_iff _ _ _ _).mp hy0).2
  have hm1 : y1 ∈ echoWithFallback true (t.map Prod.fst ++ [x]) :=
    canon_mem ((filterDom_mem_iff _ _ _ _).mp hy1).2
  rcases x with ⟨⟨_ | ⟨⟨⟩⟩, ⟨⟩⟩, v⟩
  · rw [echoWithFallback_snoc_outer] at hm0 hm1
    rw [Part.eq_some_iff.mpr hy0, Part.eq_some_iff.mpr hy1,
      Part.mem_some_iff.mp hm0, Part.mem_some_iff.mp hm1]
  · simp at houter

/-- By the converse `TypedConverter.ofDDC_eq_iff`, the reachable DDCs themselves are equal. -/
example : reachableEcho false = reachableEcho true :=
  (TypedConverter.ofDDC_eq_iff (reachableEcho_isDDCFrom false 0)
    (reachableEcho_isDDCFrom true 1)).mp reachableEcho_converter_eq

/-- `(ofDDC α ⊗ₘ ofDDC γ) ≫ ofDDC β` as a single `TypedConverter.ofDDC`. -/
example {A B C D E : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {γ : InsideOutsideSystem C.I D.I C.X C.Y D.X D.Y}
    {β : InsideOutsideSystem (B ⊗ D).I E.I (B ⊗ D).X (B ⊗ D).Y E.X E.Y}
    {bα bγ bβ : ℕ}
    (hα : IsDDCFrom B.domain A.domain bα α) (hγ : IsDDCFrom D.domain C.domain bγ γ)
    (hβ : IsDDCFrom E.domain (B ⊗ D).domain bβ β) :
    ((TypedConverter.ofDDC α hα : A ⟶ B) ⊗ₘ (TypedConverter.ofDDC γ hγ : C ⟶ D)) ≫
        (TypedConverter.ofDDC β hβ : (B ⊗ D) ⟶ E) =
      TypedConverter.ofDDC
        (trim (serialM
          (tensorL (U := (A ⊗ C).X) (V := (A ⊗ C).Y) (Xi := (B ⊗ D).X) (Yi := (B ⊗ D).Y) α γ) β))
        ((IsDDCFrom.tensorL (U := (A ⊗ C).X) (V := (A ⊗ C).Y)
          (X := (B ⊗ D).X) (Y := (B ⊗ D).Y) hα hγ).comp hβ) := by
  change TypedConverter.comp
    (TypedConverter.parallel (TypedConverter.ofDDC α hα) (TypedConverter.ofDDC γ hγ))
    (TypedConverter.ofDDC β hβ) = _
  rw [TypedConverter.parallel_ofDDC]
  exact (TypedConverter.ofDDC_eq_comp _ hβ _ rfl).symm

/-- `(ofDDC α ≫ ofDDC β) ⊗ₘ ofDDC γ` as a single `TypedConverter.ofDDC`. -/
example {A B C D E : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {β : InsideOutsideSystem B.I C.I B.X B.Y C.X C.Y}
    {γ : InsideOutsideSystem D.I E.I D.X D.Y E.X E.Y}
    {bα bβ bγ : ℕ}
    (hα : IsDDCFrom B.domain A.domain bα α) (hβ : IsDDCFrom C.domain B.domain bβ β)
    (hγ : IsDDCFrom E.domain D.domain bγ γ) :
    ((TypedConverter.ofDDC α hα : A ⟶ B) ≫ (TypedConverter.ofDDC β hβ : B ⟶ C)) ⊗ₘ
        (TypedConverter.ofDDC γ hγ : D ⟶ E) =
      TypedConverter.ofDDC
        (tensorL (U := (A ⊗ D).X) (V := (A ⊗ D).Y) (Xi := (C ⊗ E).X) (Yi := (C ⊗ E).Y)
          (trim (serialM α β)) γ)
        (IsDDCFrom.tensorL (U := (A ⊗ D).X) (V := (A ⊗ D).Y)
          (X := (C ⊗ E).X) (Y := (C ⊗ E).Y) (hα.comp hβ) hγ) := by
  change TypedConverter.parallel
    (TypedConverter.comp (TypedConverter.ofDDC α hα) (TypedConverter.ofDDC β hβ))
    (TypedConverter.ofDDC γ hγ) = _
  rw [← TypedConverter.ofDDC_eq_comp hα hβ (hα.comp hβ) rfl, TypedConverter.parallel_ofDDC]

/-- Parallel composition with identities reduces to a single `TypedConverter.ofDDC` on either
side, and `cc_normalize` distributes them over parallel systems. -/
example {A B C : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y} {bα : ℕ}
    (hα : IsDDCFrom B.domain A.domain bα α)
    (R : TypedSystem B) (S : TypedSystem C) :
    ((TypedConverter.ofDDC α hα : A ⟶ B) ⊗ₘ 𝟙 C) • (R ∥ S) =
      (TypedConverter.ofDDC α hα • R) ∥ S := by
  cc_normalize

/-- `TypedConverter.parallel_ofDDC_id` and `TypedConverter.parallel_id_ofDDC` present whiskered
deterministic converters as single `ofDDC`s. -/
example {A B C : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y} {bα : ℕ}
    (hα : IsDDCFrom B.domain A.domain bα α) :
    ∃ γ, ∃ b, ∃ hγ : IsDDCFrom (B ⊗ C).domain (A ⊗ C).domain b γ,
      ((TypedConverter.ofDDC α hα : A ⟶ B) ⊗ₘ 𝟙 C) = TypedConverter.ofDDC γ hγ :=
  ⟨_, _, _, TypedConverter.parallel_ofDDC_id hα⟩

example {A B C : Interface}
    {γ : InsideOutsideSystem B.I C.I B.X B.Y C.X C.Y} {bγ : ℕ}
    (hγ : IsDDCFrom C.domain B.domain bγ γ) :
    ∃ δ, ∃ b, ∃ hδ : IsDDCFrom (A ⊗ C).domain (A ⊗ B).domain b δ,
      (𝟙 A ⊗ₘ (TypedConverter.ofDDC γ hγ : B ⟶ C)) = TypedConverter.ofDDC δ hδ :=
  ⟨_, _, _, TypedConverter.parallel_id_ofDDC hγ⟩

#print axioms IsDDCFrom.replies_iff_of_next_eq
#print axioms IsDDCFrom.eq_of_next_eq
#print axioms PDCBehavior.ofDDC_eq_of_next_eq
#print axioms PDCBehavior.ofDDC_eq_iff_replies
#print axioms PDCBehavior.ofDDC_eq_iff
#print axioms TypedConverter.ofDDC_eq_of_next_eq
#print axioms TypedConverter.ofDDC_eq_iff_replies
#print axioms TypedConverter.ofDDC_eq_iff
#print axioms TypedConverter.parallel_ofDDC
#print axioms TypedConverter.id_eq_ofDDC_filter
#print axioms TypedConverter.parallel_ofDDC_id
#print axioms TypedConverter.parallel_id_ofDDC

end Tests.DeterministicConverterComparison

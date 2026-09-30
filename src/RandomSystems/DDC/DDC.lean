import RandomSystems.System.Observation

/-!
# Deterministic discrete converters

A deterministic discrete converter (DDC) is a system with outside and inside
interfaces that is silent before its first input, answers only admissible
histories, makes a bounded number of consecutive inside queries, and replies
outside at the label of the last outside input. A responsive converter also
answers every admissible history. Sources: CR18 Definition 3.8, printed p. 61;
Lanzenberger–Maurer Definition 5, printed p. 11; Jost Definition 2.2.2,
printed pp. 17–18.

## Main definitions

* `Admissible α h`: every input of `h` follows a defined reply and is admitted
  there
* `IsDDC b α`, `DDC O J U V X Y`: converters with at most `b` consecutive
  inside queries
* `IsResponsiveDDC b α`: responsive converters
* `canon c`: the restriction of `c` to its admissible histories
* `idConverter J X Y`: the identity converter
* `TotalResource R`: a resource answering exactly the nonempty histories, at
  the interface queried (Jost Definition 2.2.1)
* `AgreesAlong b b' H`: agreement of a component on the queries it receives
  along `H`

## Main results

* `IsResponsiveDDC.converges_along`: attaching a converter converges, for
  every resource
* `IsResponsiveDDC.totalResource_along`: a converter attached to a total
  resource gives a total resource
* `attachAlong_canon`: restriction to admissible histories does not change an
  attachment
* `idConverter_isResponsiveDDC`, `attachAlong_idConverter`: the identity
  converter and the identity law
* `pair_congr_right`, `Exchange.congr_right`, `Induces.congr_right`: an
  attachment depends only on the replies to the queries made
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

/-! ## Converters (Jost Def. 2.2.2) -/

section ConverterClass

variable {O J : Type}

/-- A message at an inside label. -/
def IsInside {F : Two O J → Type} (y : Σ l, F l) : Prop := y.1.1 = some ()

/-- The labels admitted after a reply at `r`: the inside label just queried, or any
outside label. -/
def admitAfter : Option (Two O J) → Two O J → Prop
  | some ⟨some (), j⟩, l => l = ⟨some (), j⟩
  | _, l => l.1 = none

theorem admitAfter_of_ne {r : Option (Two O J)} (hr : ∀ j, r ≠ some ⟨some (), j⟩) {l : Two O J} :
    admitAfter r l ↔ l.1 = none := by
  rcases r with _ | ⟨_ | ⟨⟨⟩⟩, j⟩
  · rfl
  · rfl
  · exact absurd rfl (hr j)

/-- The label of an outside message. -/
def outerOf {F : Two O J → Type} : (Σ l, F l) → Option O
  | ⟨⟨none, o⟩, _⟩ => some o
  | ⟨⟨some (), _⟩, _⟩ => none

/-- The label of the last outside input. -/
def lastOuter {F : Two O J → Type} (h : List (Σ l, F l)) : Option O :=
  h.reverse.findSome? outerOf

theorem lastOuter_snoc {F : Two O J → Type} (h : List (Σ l, F l)) (z : Σ l, F l) :
    lastOuter (h ++ [z]) = (outerOf z).or (lastOuter h) := by
  simp only [lastOuter, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append, List.findSome?_cons]
  cases outerOf z <;> rfl

variable {U V : O → Type} {Xi Yi : J → Type}

/-- The input `z` is admitted after `h`. -/
def Admits (α : InsideOutsideSystem O J U V Xi Yi) (h : List (Σ l, twoFam U Yi l)) (z : Σ l, twoFam U Yi l) :
    Prop := admitAfter (replyLabel α h) z.1

/-- Admissible histories: every input arrives after a defined reply, where it is admitted
(Jost Def. 2.2.2, printed pp. 17–18). -/
def Admissible (α : InsideOutsideSystem O J U V Xi Yi) (h : List (Σ l, twoFam U Yi l)) : Prop :=
  ∀ h' z e, h = h' ++ z :: e → (h' ≠ [] → (α h').Dom) ∧ Admits α h' z

variable {α : InsideOutsideSystem O J U V Xi Yi}

@[simp] theorem admissible_nil : Admissible α [] := by
  intro h' z e he
  simp at he

theorem admissible_snoc {h : List (Σ l, twoFam U Yi l)} {z : Σ l, twoFam U Yi l} :
    Admissible α (h ++ [z]) ↔ Admissible α h ∧ (h ≠ [] → (α h).Dom) ∧ Admits α h z := by
  constructor
  · intro ha
    refine ⟨fun h' z' e he => ha h' z' (e ++ [z]) (by rw [he]; simp), ha h z [] rfl⟩
  · rintro ⟨ha, hd, hz⟩ h' z' e he
    rcases List.eq_nil_or_concat e with rfl | ⟨e', w, rfl⟩
    · have he' : h ++ [z] = h' ++ [z'] := by simpa using he
      obtain ⟨rfl, e2⟩ := List.append_inj' he' rfl
      obtain rfl : z = z' := by simpa using e2
      exact ⟨hd, hz⟩
    · rw [List.concat_eq_append] at he
      have he' : h ++ [z] = (h' ++ z' :: e') ++ [w] := by rw [he]; simp
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      exact ha h' z' e' rfl

theorem Admissible.of_append {h e : List (Σ l, twoFam U Yi l)} (ha : Admissible α (h ++ e)) :
    Admissible α h :=
  fun h' z e' he => ha h' z (e' ++ e) (by rw [he]; simp)

/-- Consecutive replies at inside labels at the end of `h`. -/
noncomputable def insideRun (α : InsideOutsideSystem O J U V Xi Yi) (h : List (Σ l, twoFam U Yi l)) : ℕ :=
  run IsInside α h

/-- The converter conditions without an obligation to answer every legal input. -/
structure IsDDC (b : ℕ) (α : InsideOutsideSystem O J U V Xi Yi) : Prop where
  dds : IsDDS α
  admits : ∀ h z, (α (h ++ [z])).Dom → Admits α h z
  bound : ∀ h, (α h).Dom → insideRun α h ≤ b
  replies : ∀ h y (o : O), y ∈ α h → y.1 = ⟨none, o⟩ → lastOuter h = some o

/-- A DDC is the existing interface system satisfying the converter conditions. -/
abbrev DDC (O J : Type) (U V : O → Type) (X Y : J → Type) :=
  {α : InsideOutsideSystem O J U V X Y // ∃ b, IsDDC b α}

/-- An additional guarantee: every legal nonempty input history receives a reply. -/
def Responsive (α : InsideOutsideSystem O J U V Xi Yi) : Prop :=
  ∀ h, Admissible α h → h ≠ [] → (α h).Dom

theorem IsDDC.mono {b c : ℕ} (hα : IsDDC b α) (hbc : b ≤ c) : IsDDC c α :=
  { hα with bound := fun h hd => (hα.bound h hd).trans hbc }

/-- **Responsive converter** (Jost Def. 2.2.2, printed pp. 17–18): a deterministic system that
* is silent before the first input and has a prefix-closed domain;
* answers exactly the admissible histories: the first input and every input after an
  outside reply are outside, and the input after a query at inside label `j` is the reply
  at `j`;
* makes at most `b` consecutive inside queries;
* replies outside at the label of the last outside input. -/
structure IsResponsiveDDC (b : ℕ) (α : InsideOutsideSystem O J U V Xi Yi) : Prop where
  dds : IsDDS α
  admits : ∀ h z, (α (h ++ [z])).Dom → Admits α h z
  bound : ∀ h, (α h).Dom → insideRun α h ≤ b
  responsive : Responsive α
  replies : ∀ h y (o : O), y ∈ α h → y.1 = ⟨none, o⟩ → lastOuter h = some o

theorem IsResponsiveDDC.isDDC {b : ℕ} (hα : IsResponsiveDDC b α) : IsDDC b α :=
  ⟨hα.dds, hα.admits, hα.bound, hα.replies⟩

/-- The responsive specialization adds exactly its reply obligation. -/
theorem isResponsiveDDC_iff {b : ℕ} :
    IsResponsiveDDC b α ↔ IsDDC b α ∧ Responsive α :=
  ⟨fun h => ⟨h.isDDC, h.responsive⟩,
    fun ⟨h, hr⟩ => ⟨h.dds, h.admits, h.bound, hr, h.replies⟩⟩

theorem IsResponsiveDDC.mono {b b' : ℕ} (hα : IsResponsiveDDC b α) (hb : b ≤ b') :
    IsResponsiveDDC b' α :=
  { hα with bound := fun h hd => (hα.bound h hd).trans hb }

theorem IsResponsiveDDC.admissible {b : ℕ} (hα : IsResponsiveDDC b α) {h : List (Σ l, twoFam U Yi l)}
    (hd : (α h).Dom) : Admissible α h := by
  intro h' z e he
  subst he
  have hz : (α (h' ++ [z])).Dom :=
    hα.dds.2 ⟨e, by simp⟩ (by simp) hd
  refine ⟨fun hne => hα.dds.2 ⟨z :: e, rfl⟩ hne hd, hα.admits h' z hz⟩

/-- A converter answers exactly the nonempty admissible histories. -/
theorem IsResponsiveDDC.dom_iff {b : ℕ} (hα : IsResponsiveDDC b α) (h : List (Σ l, twoFam U Yi l)) :
    (α h).Dom ↔ h ≠ [] ∧ Admissible α h :=
  ⟨fun hd => ⟨by rintro rfl; exact hα.dds.1 hd, hα.admissible hd⟩,
    fun ⟨hne, ha⟩ => hα.responsive h ha hne⟩

end ConverterClass

/-! ## Restriction to admissible histories and the identity converter -/

section Identity

variable {O J : Type} {U V : O → Type} {Xi Yi : J → Type}

/-- The restriction of `c` to its admissible histories. -/
noncomputable def canon (c : InsideOutsideSystem O J U V Xi Yi) : InsideOutsideSystem O J U V Xi Yi := fun h =>
  if Admissible c h then c h else Part.none

theorem canon_of_admissible {c : InsideOutsideSystem O J U V Xi Yi} {h} (ha : Admissible c h) :
    canon c h = c h := if_pos ha

theorem replyLabel_canon {c : InsideOutsideSystem O J U V Xi Yi} {h} (ha : Admissible c h) :
    replyLabel (canon c) h = replyLabel c h := by
  simp [replyLabel, canon_of_admissible ha]

theorem admissible_canon_iff {c : InsideOutsideSystem O J U V Xi Yi} (h : List (Σ l, twoFam U Yi l)) :
    Admissible (canon c) h ↔ Admissible c h := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rw [admissible_snoc, admissible_snoc]
    constructor
    · rintro ⟨ha, hd, hz⟩
      have ha' := ih.mp ha
      refine ⟨ha', fun hne => by simpa [canon_of_admissible ha'] using hd hne, ?_⟩
      simpa [Admits, replyLabel_canon ha'] using hz
    · rintro ⟨ha, hd, hz⟩
      refine ⟨ih.mpr ha, fun hne => by simpa [canon_of_admissible ha] using hd hne, ?_⟩
      simpa [Admits, replyLabel_canon ha] using hz

variable (J : Type) (X Y : J → Type)

/-- Forwarding between outside label `j` and inside label `j`, on all histories. -/
def forwardAll : InsideOutsideSystem J J X Y X Y := fun h =>
  match h.getLast? with
  | none => Part.none
  | some ⟨⟨none, j⟩, x⟩ => Part.some ⟨⟨some (), j⟩, x⟩
  | some ⟨⟨some (), j⟩, y⟩ => Part.some ⟨⟨none, j⟩, y⟩

/-- **The identity converter** `𝟙` (spec §5.4): forwarding on admissible histories. -/
noncomputable def idConverter : InsideOutsideSystem J J X Y X Y := canon (forwardAll J X Y)

variable {J X Y}

theorem forwardAll_snoc_outer (h : List (Σ l, twoFam X Y l)) (j : J) (x : X j) :
    forwardAll J X Y (h ++ [⟨⟨none, j⟩, x⟩]) = Part.some ⟨⟨some (), j⟩, x⟩ := by
  simp [forwardAll]

theorem forwardAll_snoc_inner (h : List (Σ l, twoFam X Y l)) (j : J) (y : Y j) :
    forwardAll J X Y (h ++ [⟨⟨some (), j⟩, y⟩]) = Part.some ⟨⟨none, j⟩, y⟩ := by
  simp [forwardAll]

theorem forwardAll_dom {h : List (Σ l, twoFam X Y l)} (hne : h ≠ []) :
    (forwardAll J X Y h).Dom := by
  obtain ⟨h₀, z, rfl⟩ := List.eq_nil_or_concat h |>.resolve_left hne
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
  · simp [List.concat_eq_append, forwardAll_snoc_outer]
  · simp [List.concat_eq_append, forwardAll_snoc_inner]

theorem replyLabel_forwardAll_outer (h : List (Σ l, twoFam X Y l)) (j : J) (x : X j) :
    replyLabel (forwardAll J X Y) (h ++ [⟨⟨none, j⟩, x⟩]) = some ⟨some (), j⟩ := by
  simp [replyLabel, forwardAll_snoc_outer]

theorem replyLabel_forwardAll_inner (h : List (Σ l, twoFam X Y l)) (j : J) (y : Y j) :
    replyLabel (forwardAll J X Y) (h ++ [⟨⟨some (), j⟩, y⟩]) = some ⟨none, j⟩ := by
  simp [replyLabel, forwardAll_snoc_inner]

/-- On an admissible history, an inside input at `j` follows an outside input at `j`. -/
theorem forwardAll_inner_prev {h : List (Σ l, twoFam X Y l)} {j : J} {y : Y j}
    (ha : Admissible (forwardAll J X Y) (h ++ [⟨⟨some (), j⟩, y⟩])) :
    ∃ h₀ x, h = h₀ ++ [⟨⟨none, j⟩, x⟩] := by
  obtain ⟨-, -, hz⟩ := admissible_snoc.mp ha
  rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
  · simp [Admits, replyLabel, forwardAll, admitAfter] at hz
  rw [List.concat_eq_append] at hz ⊢
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j'⟩, v⟩
  · rw [Admits, replyLabel_forwardAll_outer] at hz
    simp only [admitAfter, Sigma.mk.injEq, heq_eq_eq, true_and] at hz
    subst hz
    exact ⟨h₀, v, rfl⟩
  · rw [Admits, replyLabel_forwardAll_inner] at hz
    simp [admitAfter] at hz

theorem idConverter_isResponsiveDDC : IsResponsiveDDC 1 (idConverter J X Y) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, idConverter, canon, forwardAll]
  · intro l₁ l₂ hp hne hd
    obtain ⟨ha, -⟩ : Admissible (forwardAll J X Y) l₂ ∧ True := by
      by_contra hc
      simp only [and_true] at hc
      simp [idConverter, canon, hc] at hd
    obtain ⟨e, rfl⟩ := hp
    have ha₁ := ha.of_append
    rw [idConverter, canon_of_admissible ha₁]
    exact forwardAll_dom hne
  · intro h z hd
    have ha : Admissible (forwardAll J X Y) (h ++ [z]) := by
      by_contra hc; simp [idConverter, canon, hc] at hd
    have hh := (admissible_snoc.mp ha).1
    have := (admissible_snoc.mp ha).2.2
    simpa [Admits, idConverter, replyLabel_canon hh] using this
  · intro h hd
    induction h using List.reverseRecOn with
    | nil => simp [insideRun]
    | append_singleton h z _ =>
      have ha : Admissible (forwardAll J X Y) (h ++ [z]) := by
        by_contra hc; simp [idConverter, canon, hc] at hd
      rw [insideRun, run_snoc]
      split_ifs with hin
      · obtain ⟨w, hw, hwi⟩ := hin
        rw [idConverter, canon_of_admissible ha] at hw
        -- an inside reply answers an outside input, so the previous reply was outside
        rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
        · rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z₀, rfl⟩
          · simp [insideRun]
          simp only [List.concat_eq_append] at *
          obtain ⟨hh, -, hz⟩ := admissible_snoc.mp ha
          have hnot : ¬ ∃ w ∈ idConverter J X Y (h₀ ++ [z₀]), IsInside w := by
            rintro ⟨w', hw', hwi'⟩
            rw [idConverter, canon_of_admissible hh] at hw'
            have hr := replyLabel_of_mem _ hw'
            rw [Admits, hr] at hz
            rcases w' with ⟨⟨_ | ⟨⟨⟩⟩, j'⟩, v'⟩
            · simp [IsInside] at hwi'
            · simp [admitAfter] at hz
          simp [run_snoc, hnot]
        · rw [forwardAll_snoc_inner] at hw
          obtain rfl := Part.mem_some_iff.mp hw
          simp [IsInside] at hwi
      · exact Nat.zero_le _
  · intro h ha hne
    rw [idConverter, admissible_canon_iff] at ha
    rw [idConverter, canon_of_admissible ha]
    exact forwardAll_dom hne
  · intro h y o hy hyo
    have ha : Admissible (forwardAll J X Y) h := by
      by_contra hc; simp [idConverter, canon, hc] at hy
    rw [idConverter, canon_of_admissible ha] at hy
    rcases List.eq_nil_or_concat h with rfl | ⟨h₀, z, rfl⟩
    · simp [forwardAll] at hy
    rw [List.concat_eq_append] at ha hy ⊢
    rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
    · rw [forwardAll_snoc_outer] at hy
      obtain rfl := Part.mem_some_iff.mp hy
      simp at hyo
    · rw [forwardAll_snoc_inner] at hy
      obtain rfl := Part.mem_some_iff.mp hy
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hyo
      subst hyo
      obtain ⟨h₁, x, rfl⟩ := forwardAll_inner_prev ha
      rw [lastOuter_snoc, lastOuter_snoc]
      simp [outerOf]

end Identity

/-! ## Attachments of converters converge -/

section AlongConverge

variable {I O J : Type} {X Y : I → Type} {U V : O → Type}

/-- Every internal cycle of `α^ι R` passes through `α`, continuing only after an inside query. -/
theorem cyclesThrough_along (ι : J → I) :
    CyclesThrough (IsInside (F := twoFam V (X ∘ ι))) (alongRoute (U := U) (Y := Y) ι) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, l⟩, v⟩ hy
    · refine ⟨⟨⟨⟨none, ⟨none, l⟩⟩, outside_not_mem_alongSet ι l⟩, v⟩, ?_⟩
      simp only [alongRoute]
      rw [show (joinOut ⟨none, ⟨⟨none, l⟩, v⟩⟩ : Σ p : Two (Two O J) I, _) = ⟨⟨none, ⟨none, l⟩⟩, v⟩
        from rfl, connectRoute_of_not_mem _ (outside_not_mem_alongSet ι l)]
      rfl
    · exact absurd rfl hy
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩ hy
    · exact absurd hy (by simp [IsInside])
    · refine Or.inr ⟨⟨ι j, x⟩, ?_⟩
      simp only [alongRoute]
      rw [show (joinOut ⟨none, ⟨⟨some (), j⟩, x⟩⟩ : Σ p : Two (Two O J) I, _) =
        ⟨⟨none, ⟨some (), j⟩⟩, x⟩ from rfl, connectRoute_of_mem _ (inside_mem_alongSet ι j)]
      rfl
  · rintro ⟨i, w⟩
    by_cases hi : (⟨some (), i⟩ : Two (Two O J) I) ∈ alongSet ι
    · refine Or.inr ⟨⟨⟨some (), Classical.choose hi⟩,
        cast (congrArg Y (Classical.choose_spec hi).symm) w⟩, ?_⟩
      simp only [alongRoute]
      rw [show (joinOut ⟨some (), ⟨i, w⟩⟩ : Σ p : Two (Two O J) I, _) = ⟨⟨some (), i⟩, w⟩
        from rfl, connectRoute_of_mem _ hi]
      rfl
    · refine Or.inl ⟨⟨⟨⟨some (), i⟩, hi⟩, w⟩, ?_⟩
      simp only [alongRoute]
      rw [show (joinOut ⟨some (), ⟨i, w⟩⟩ : Σ p : Two (Two O J) I, _) = ⟨⟨some (), i⟩, w⟩
        from rfl, connectRoute_of_not_mem _ hi]
      rfl

/-- **Attaching a converter converges**, whatever the resource. -/
theorem IsResponsiveDDC.converges_along {b : ℕ} {ι : J → I} {α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)}
    (hα : IsResponsiveDDC b α) (R : InterfaceSystem I X Y) :
    Converges (pair α R) (alongRoute ι) (alongInj ι) :=
  converges_pair (cyclesThrough_along ι) hα.bound

end AlongConverge

/-! ## Attaching a converter to a total resource -/

section AlongTotal

variable {I O J : Type} {X Y : I → Type} {U V : O → Type}

/-- A total resource (Jost Def. 2.2.1, printed p. 16): it answers exactly the nonempty
histories, at the interface queried. -/
def TotalResource (R : InterfaceSystem I X Y) : Prop := (∀ h, (R h).Dom ↔ h ≠ []) ∧ RepliesAtQueriedInterface R

theorem TotalResource.isDDS {R : InterfaceSystem I X Y} (hR : TotalResource R) : IsDDS R :=
  ⟨fun hd => (hR.1 []).mp hd rfl, fun l₁ _ _ hne _ => (hR.1 l₁).mpr hne⟩

variable (ι : J → I)

theorem alongRoute_outer (o : O) (v : V o) :
    alongRoute (X := X) (U := U) (Y := Y) ι ⟨none, ⟨⟨none, o⟩, v⟩⟩ =
      .inl ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩, v⟩ := by
  show Sum.map id splitIn (connectRoute (alongSet ι) (alongRouting ι) ⟨⟨none, ⟨none, o⟩⟩, v⟩) = _
  rw [connectRoute_of_not_mem _ (outside_not_mem_alongSet ι o)]
  rfl

theorem alongRoute_inside (j : J) (x : X (ι j)) :
    alongRoute (U := U) (V := V) (Y := Y) ι ⟨none, ⟨⟨some (), j⟩, x⟩⟩ = .inr ⟨some (), ⟨ι j, x⟩⟩ := by
  show Sum.map id splitIn (connectRoute (alongSet ι) (alongRouting ι) ⟨⟨none, ⟨some (), j⟩⟩, x⟩) = _
  rw [connectRoute_of_mem _ (inside_mem_alongSet ι j)]
  rfl

theorem alongRoute_image (hι : Function.Injective ι) (j : J) (y : Y (ι j)) :
    alongRoute (X := X) (U := U) (V := V) ι ⟨some (), ⟨ι j, y⟩⟩ = .inr ⟨none, ⟨⟨some (), j⟩, y⟩⟩ := by
  simp only [alongRoute]
  rw [show (joinOut ⟨some (), ⟨ι j, y⟩⟩ : Σ p : Two (Two O J) I, _) = ⟨⟨some (), ι j⟩, y⟩
    from rfl, connectRoute_of_mem _ (image_mem_alongSet ι j), liftC_alongRouting_image ι hι j]
  rfl

theorem alongRoute_free {i : I} (hi : i ∉ Set.range ι) (y : Y i) :
    alongRoute (X := X) (U := U) (V := V) ι ⟨some (), ⟨i, y⟩⟩ =
      .inl ⟨⟨⟨some (), i⟩, sys_not_mem_alongSet ι hi⟩, y⟩ := by
  simp only [alongRoute]
  rw [show (joinOut ⟨some (), ⟨i, y⟩⟩ : Σ p : Two (Two O J) I, _) = ⟨⟨some (), i⟩, y⟩
    from rfl, connectRoute_of_not_mem _ (sys_not_mem_alongSet ι hi)]
  rfl

variable {ι} {b : ℕ} {α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)} {R : InterfaceSystem I X Y}

/-- Between two calls, `α` waits for an outside input. -/
def AlongIdle (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι))
    (H : List (Two (Σ l, twoFam U (Y ∘ ι) l) (Σ i, X i))) : Prop :=
  Admissible α (restrict none H) ∧ (restrict none H ≠ [] → (α (restrict none H)).Dom) ∧
    ∀ j, replyLabel α (restrict none H) ≠ some ⟨some (), j⟩

/-- A call from outside label `o`: `α` is about to reply, or `R` is about to answer an inside
query of `α` at `j`. -/
def AlongCall (α : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)) (o : O)
    (G : List (Two (Σ l, twoFam U (Y ∘ ι) l) (Σ i, X i))) : Prop :=
  (∃ G₁ z, G = G₁ ++ [⟨none, z⟩] ∧ Admissible α (restrict none G₁ ++ [z]) ∧
      lastOuter (restrict none G₁ ++ [z]) = some o) ∨
  (∃ G₁ j x, G = G₁ ++ [⟨some (), ⟨ι j, x⟩⟩] ∧ Admissible α (restrict none G₁) ∧
      (⟨⟨some (), j⟩, x⟩ : Σ l, twoFam V (X ∘ ι) l) ∈ α (restrict none G₁) ∧
      lastOuter (restrict none G₁) = some o)

theorem along_call (hι : Function.Injective ι) (hα : IsResponsiveDDC b α) (hR : TotalResource R)
    {G o' G'} (l : Exchange (pair α R) (alongRoute ι) G o' G') :
    ∀ o, AlongCall α o G → ∃ v, o' = some ⟨⟨⟨none, ⟨none, o⟩⟩, outside_not_mem_alongSet ι o⟩, v⟩ ∧
      AlongIdle α G' := by
  induction l with
  | silent G hd =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · rw [pair_left] at hd
      exact absurd (Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (Part.get_mem
        (hα.responsive _ ha (by simp)))⟩) hd
    · rw [pair_right] at hd
      exact absurd (Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (Part.get_mem
        ((hR.1 _).mpr (by simp)))⟩) hd
  | out G y c hy hr =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · rw [pair_left] at hy
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases w with ⟨⟨_ | ⟨⟨⟩⟩, o''⟩, v⟩
      · have := hα.replies _ _ o'' hw rfl
        rw [hlo] at this
        obtain rfl := Option.some_inj.mp this.symm
        rw [alongRoute_outer] at hr
        refine ⟨v, (Sum.inl.inj hr).symm ▸ rfl, ?_⟩
        refine ⟨by simpa using ha, fun _ => by simpa using Part.dom_iff_mem.mpr ⟨_, hw⟩, fun j => ?_⟩
        simp [replyLabel_of_mem _ hw]
      · rw [alongRoute_inside] at hr; cases hr
    · rw [pair_right] at hy
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hl := hR.2 _ _ _ hw
      rcases w with ⟨i, w⟩
      simp only at hl
      subst hl
      rw [alongRoute_image ι hι] at hr; cases hr
  | feed G y x' o' G'' hy hr _ ih =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, ha, hq, hlo⟩
    · rw [pair_left] at hy
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases w with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
      · rw [alongRoute_outer] at hr; cases hr
      · rw [alongRoute_inside] at hr
        cases hr
        refine ih o (Or.inr ⟨_, j, v, rfl, ?_, ?_, ?_⟩)
        · simpa using ha
        · simpa using hw
        · simpa using hlo
    · rw [pair_right] at hy
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hl := hR.2 _ _ _ hw
      rcases w with ⟨i, w⟩
      simp only at hl
      subst hl
      rw [alongRoute_image ι hι] at hr
      cases hr
      refine ih o (Or.inl ⟨_, _, rfl, ?_, ?_⟩)
      · rw [restrict_none_snoc_right]
        refine admissible_snoc.mpr ⟨ha, fun _ => Part.dom_iff_mem.mpr ⟨_, hq⟩, ?_⟩
        simp [Admits, replyLabel_of_mem _ hq, admitAfter]
      · rw [restrict_none_snoc_right, lastOuter_snoc]
        simpa [outerOf] using hlo

/-- Every external history leaves `α` idle, and each reply comes at the queried interface. -/
theorem along_induces (hι : Function.Injective ι) (hα : IsResponsiveDDC b α) (hR : TotalResource R)
    {u o H} (r : Induces (pair α R) (alongRoute ι) (alongInj ι) u o H) :
    AlongIdle α H ∧ ∀ u' a, u = u' ++ [a] → ∃ c, o = some c ∧ c.1 = a.1 := by
  induction r with
  | nil => exact ⟨⟨admissible_nil, fun h => absurd rfl h, fun j => by
      rw [restrict_nil, replyLabel, dif_neg hα.dds.1]; simp⟩, fun u' a e => by simp at e⟩
  | snoc u a o₀ H o H' _ lx ih =>
    obtain ⟨⟨ha, hd, hi⟩, -⟩ := ih
    suffices hfin : AlongIdle α H' ∧ ∃ c, o = some c ∧ c.1 = a.1 by
      refine ⟨hfin.1, fun u' a' e => ?_⟩
      obtain ⟨-, e'⟩ := List.append_inj' e rfl
      obtain rfl : a = a' := by simpa using e'
      exact hfin.2
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl⟩, v⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o'⟩
      · have h₁ : Admissible α (restrict none H ++ [⟨⟨none, o'⟩, v⟩]) :=
          admissible_snoc.mpr ⟨ha, hd, (admitAfter_of_ne hi).mpr rfl⟩
        have h₂ : lastOuter (restrict none H ++ [⟨⟨none, o'⟩, v⟩]) = some o' := by
          rw [lastOuter_snoc]; rfl
        obtain ⟨v', rfl, hid⟩ := along_call hι hα hR lx o' (Or.inl ⟨H, _, rfl, h₁, h₂⟩)
        exact ⟨hid, _, rfl, rfl⟩
      · exact absurd (inside_mem_alongSet ι o') hl
    · -- a query at a free interface of `R`
      have hi' : l ∉ Set.range ι := hl
      have hpr : pair α R (H ++ [⟨some (), ⟨l, v⟩⟩]) =
          (R (restrict (some ()) H ++ [⟨l, v⟩])).map (Sigma.mk (some ())) := pair_right _ _ _ _
      have hdR := (hR.1 (restrict (some ()) H ++ [⟨l, v⟩])).mpr (by simp)
      have hw := Part.get_mem hdR
      have hlab := hR.2 _ _ _ hw
      set w := (R (restrict (some ()) H ++ [⟨l, v⟩])).get hdR
      rcases w with ⟨i, w⟩
      simp only at hlab
      subst hlab
      have l' : Exchange (pair α R) (alongRoute ι) (H ++ [⟨some (), ⟨i, v⟩⟩])
          (some ⟨⟨⟨some (), i⟩, sys_not_mem_alongSet ι hi'⟩, w⟩) (H ++ [⟨some (), ⟨i, v⟩⟩]) :=
        Exchange.out _ ⟨some (), ⟨i, w⟩⟩ _ (by rw [hpr]; exact Part.mem_map _ hw)
          (alongRoute_free ι hi' w)
      obtain ⟨rfl, rfl⟩ := lx.det l'
      refine ⟨⟨by simpa using ha, by simpa using hd, by simpa using hi⟩, _, rfl, rfl⟩

/-- **A converter on a total resource gives a total resource** (Jost p. 18): the attachment
answers every nonempty history, at the interface queried. -/
theorem IsResponsiveDDC.totalResource_along (hι : Function.Injective ι) (hα : IsResponsiveDDC b α)
    (hR : TotalResource R) : TotalResource (attachAlong ι α R) := by
  rw [attachAlong_eq]
  refine ⟨fun u => ⟨fun hd => ?_, fun hne => ?_⟩, fun h a c hc => ?_⟩
  · rintro rfl
    exact not_dom_of_induces_none Induces.nil hd
  · obtain ⟨o, H, r⟩ := hα.converges_along R u
    obtain ⟨u', a, rfl⟩ := List.eq_nil_or_concat u |>.resolve_left hne
    obtain ⟨c, rfl, -⟩ := (along_induces hι hα hR r).2 u' a (by simp)
    exact Part.dom_iff_mem.mpr ⟨c, mem_of_induces_some r⟩
  · obtain ⟨H, r⟩ := mem_interconnect.mp hc
    obtain ⟨c', e, hc'⟩ := (along_induces hι hα hR r).2 h a rfl
    cases e
    exact hc'

end AlongTotal

/-! ## Restriction to admissible histories does not change an attachment -/

section AlongCanon

variable {I O J : Type} {X Y : I → Type} {U V : O → Type} {ι : J → I} {b : ℕ}
  {c : InsideOutsideSystem O J U V (X ∘ ι) (Y ∘ ι)} {R : InterfaceSystem I X Y}

theorem along_call_canon (hι : Function.Injective ι) (hc : IsResponsiveDDC b (canon c))
    (hR : TotalResource R) {G o' G'} (l : Exchange (pair (canon c) R) (alongRoute ι) G o' G') :
    ∀ o, AlongCall (canon c) o G → Exchange (pair c R) (alongRoute ι) G o' G' := by
  induction l with
  | silent G hd =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · rw [pair_left] at hd
      exact absurd (Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (Part.get_mem
        (hc.responsive _ ha (by simp)))⟩) hd
    · rw [pair_right] at hd
      exact absurd (Part.dom_iff_mem.mpr ⟨_, Part.mem_map _ (Part.get_mem
        ((hR.1 _).mpr (by simp)))⟩) hd
  | out G y c' hy hr =>
    intro o hG
    rcases hG with ⟨G₁, z, rfl, ha, -⟩ | ⟨G₁, j, x, rfl, -, -, -⟩
    · refine Exchange.out _ y c' ?_ hr
      rw [pair_left] at hy ⊢
      rwa [canon_of_admissible ((admissible_canon_iff _).mp ha)] at hy
    · refine Exchange.out _ y c' ?_ hr
      rw [pair_right] at hy ⊢
      exact hy
  | feed G y x' o' G'' hy hr l ih =>
    intro o hG
    have hcall := hG
    rcases hG with ⟨G₁, z, rfl, ha, hlo⟩ | ⟨G₁, j, x, rfl, ha, hq, hlo⟩
    · have hy' := hy
      rw [pair_left, canon_of_admissible ((admissible_canon_iff _).mp ha)] at hy'
      rw [pair_left] at hy
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases w with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
      · rw [alongRoute_outer] at hr; cases hr
      · rw [alongRoute_inside] at hr
        cases hr
        refine Exchange.feed _ _ _ _ _ (by rw [pair_left]; exact hy') (alongRoute_inside ι j v)
          (ih o (Or.inr ⟨_, j, v, rfl, ?_, ?_, ?_⟩))
        · simpa using ha
        · simpa using hw
        · simpa using hlo
    · have hy' := hy
      rw [pair_right] at hy hy'
      obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hl := hR.2 _ _ _ hw
      rcases w with ⟨i, w⟩
      simp only at hl
      subst hl
      rw [alongRoute_image ι hι] at hr
      cases hr
      refine Exchange.feed _ _ _ _ _ (by rw [pair_right]; exact hy') (alongRoute_image ι hι j w)
        (ih o (Or.inl ⟨_, _, rfl, ?_, ?_⟩))
      · rw [restrict_none_snoc_right]
        refine admissible_snoc.mpr ⟨ha, fun _ => Part.dom_iff_mem.mpr ⟨_, hq⟩, ?_⟩
        simp [Admits, replyLabel_of_mem _ hq, admitAfter]
      · rw [restrict_none_snoc_right, lastOuter_snoc]
        simpa [outerOf] using hlo

theorem along_induces_canon (hι : Function.Injective ι) (hc : IsResponsiveDDC b (canon c))
    (hR : TotalResource R) {u o H}
    (r : Induces (pair (canon c) R) (alongRoute ι) (alongInj ι) u o H) :
    Induces (pair c R) (alongRoute ι) (alongInj ι) u o H := by
  induction r with
  | nil => exact Induces.nil
  | snoc u a o₀ H o H' r₀ lx ih =>
    obtain ⟨⟨ha, hd, hi⟩, -⟩ := along_induces hι hc hR r₀
    refine Induces.snoc _ _ _ _ _ _ ih ?_
    rcases a with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl⟩, v⟩
    · rcases l with ⟨_ | ⟨⟨⟩⟩, o'⟩
      · have h₁ : Admissible (canon c) (restrict none H ++ [⟨⟨none, o'⟩, v⟩]) :=
          admissible_snoc.mpr ⟨ha, hd, (admitAfter_of_ne hi).mpr rfl⟩
        have h₂ : lastOuter (restrict none H ++ [⟨⟨none, o'⟩, v⟩]) = some o' := by
          simp [lastOuter_snoc, outerOf]
        exact along_call_canon hι hc hR lx o' (Or.inl ⟨H, _, rfl, h₁, h₂⟩)
      · exact absurd (inside_mem_alongSet ι o') hl
    · change Exchange (pair (canon c) R) (alongRoute ι) (H ++ [⟨some (), ⟨l, v⟩⟩]) o H' at lx
      show Exchange (pair c R) (alongRoute ι) (H ++ [⟨some (), ⟨l, v⟩⟩]) o H'
      cases lx with
      | silent _ hd' => exact Exchange.silent _ (by rw [pair_right] at hd' ⊢; exact hd')
      | out _ y c' hy hr => exact Exchange.out _ y c' (by rw [pair_right] at hy ⊢; exact hy) hr
      | feed _ y x' o' G'' hy hr l =>
        exfalso
        rw [pair_right] at hy
        obtain ⟨w, hw, rfl⟩ := Part.mem_map_iff _ |>.mp hy
        have hlab := hR.2 _ _ _ hw
        rcases w with ⟨i, w⟩
        simp only at hlab
        subst hlab
        rw [alongRoute_free ι hl] at hr
        cases hr

/-- Restricting a converter to its admissible histories does not change its attachment to a
total resource. -/
theorem attachAlong_canon (hι : Function.Injective ι) (hc : IsResponsiveDDC b (canon c))
    (hR : TotalResource R) : attachAlong ι (canon c) R = attachAlong ι c R := by
  rw [attachAlong_eq, attachAlong_eq]
  apply system_ext
  intro u w
  rw [mem_interconnect, mem_interconnect]
  constructor
  · rintro ⟨H, r⟩
    exact ⟨H, along_induces_canon hι hc hR r⟩
  · rintro ⟨H, r⟩
    obtain ⟨o, H', r'⟩ := hc.converges_along R u
    obtain ⟨e, rfl⟩ := (along_induces_canon hι hc hR r').det r
    subst e
    exact ⟨_, r'⟩

end AlongCanon

/-! ## The identity law -/

section AlongIdentity

variable {I J X Y : Type} (ι : J → I)

/-- Inputs of `R`, read as inputs of `𝟙^ι R`: interfaces in the image of `ι` become outside
labels of `𝟙`. -/
noncomputable def idAlongIn : (Σ _ : I, X) →
    Σ l : Free (alongSet (O := J) ι), twoFam (twoFam (fun _ : J => X) (fun _ : J => Y))
      (fun _ : I => X) l.1 := fun a =>
  if h : a.1 ∈ Set.range ι then ⟨⟨⟨none, ⟨none, Classical.choose h⟩⟩, outside_not_mem_alongSet ι _⟩, a.2⟩
  else ⟨⟨⟨some (), a.1⟩, sys_not_mem_alongSet ι h⟩, a.2⟩

theorem idAlongIn_of_mem {a : Σ _ : I, X} (h : a.1 ∈ Set.range ι) :
    idAlongIn (Y := Y) ι a =
      ⟨⟨⟨none, ⟨none, Classical.choose h⟩⟩, outside_not_mem_alongSet ι _⟩, a.2⟩ := dif_pos h

theorem idAlongIn_of_not_mem {a : Σ _ : I, X} (h : a.1 ∉ Set.range ι) :
    idAlongIn (Y := Y) ι a = ⟨⟨⟨some (), a.1⟩, sys_not_mem_alongSet ι h⟩, a.2⟩ := dif_neg h

/-- Outputs of `𝟙^ι R`, read as outputs of `R`. -/
def idAlongOut : (Σ l : Free (alongSet (O := J) ι), twoFam (twoFam (fun _ : J => Y)
      (fun _ : J => X)) (fun _ : I => Y) l.1) → Σ _ : I, Y
  | ⟨⟨⟨none, ⟨none, j⟩⟩, _⟩, y⟩ => ⟨ι j, y⟩
  | ⟨⟨⟨none, ⟨some (), j⟩⟩, h⟩, _⟩ => absurd (inside_mem_alongSet ι j) h
  | ⟨⟨⟨some (), i⟩, _⟩, y⟩ => ⟨i, y⟩

theorem forwardAll_forwarder :
    Forwarder (forwardAll J (fun _ : J => X) (fun _ : J => Y)) fun
      | ⟨⟨none, j⟩, x⟩ => ⟨⟨some (), j⟩, x⟩
      | ⟨⟨some (), j⟩, y⟩ => ⟨⟨none, j⟩, y⟩ := by
  refine ⟨by simp [SilentAtEmpty, forwardAll], fun h z => ?_⟩
  rcases z with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
  · exact forwardAll_snoc_outer h j v
  · exact forwardAll_snoc_inner h j v

variable {ι}

/-- Forwarding along `ι` is transparent. -/
theorem attachAlong_forwardAll (hι : Function.Injective ι) (R : InterfaceSystem I (fun _ => X) (fun _ => Y))
    (hR : SilentAtEmpty R) :
    relabel (attachAlong ι (forwardAll J (fun _ : J => X) (fun _ : J => Y)) R) (idAlongIn ι)
      (idAlongOut ι) = R := by
  unfold attachAlong connect pairI
  rw [relabel_interconnect, interconnect_relabel, pair_swap, interconnect_relabel,
    interconnect_forwarder hR forwardAll_forwarder (f := id) (g := id), relabel_id]
  constructor
  · rintro ⟨i, x⟩
    by_cases h : i ∈ Set.range ι
    · right
      obtain ⟨j, hj⟩ := h
      refine ⟨⟨⟨none, Classical.choose (⟨j, hj⟩ : i ∈ Set.range ι)⟩, x⟩, ?_, ?_⟩
      · simp only [Function.comp_apply]
        rw [idAlongIn_of_mem ι (a := ⟨i, x⟩) ⟨j, hj⟩]
        rfl
      · have hc := Classical.choose_spec (⟨j, hj⟩ : i ∈ Set.range ι)
        simp only [Function.comp_apply, twoSwap, joinOut]
        rw [connectRoute_of_mem _ (inside_mem_alongSet ι _)]
        simp only [Sum.map_inr, liftC_alongRouting_inside, splitIn, twoSwap, id]
        rw [hc]
    · left
      simp only [Function.comp_apply]
      rw [idAlongIn_of_not_mem ι (a := ⟨i, x⟩) h]
      rfl
  · rintro ⟨i, y⟩
    by_cases h : i ∈ Set.range ι
    · right
      obtain ⟨j, rfl⟩ := h
      refine ⟨⟨⟨some (), j⟩, y⟩, ?_, ?_⟩
      · simp only [Function.comp_apply, twoSwap, joinOut]
        rw [connectRoute_of_mem _ (image_mem_alongSet ι j), liftC_alongRouting_image ι hι j]
        rfl
      · simp only [Function.comp_apply, twoSwap, joinOut]
        rw [connectRoute_of_not_mem _ (outside_not_mem_alongSet ι j)]
        rfl
    · left
      simp only [Function.comp_apply, twoSwap, joinOut]
      rw [connectRoute_of_not_mem _ (sys_not_mem_alongSet ι h)]
      rfl

/-- **Law I, identity converter.** Attaching `𝟙` along `ι` to a total resource gives back
the resource, after naming the outside labels of `𝟙` by `ι`. -/
theorem attachAlong_idConverter (hι : Function.Injective ι) {R : InterfaceSystem I (fun _ => X) (fun _ => Y)}
    (hR : TotalResource R) :
    relabel (attachAlong ι (idConverter J (fun _ : J => X) (fun _ : J => Y)) R) (idAlongIn ι)
      (idAlongOut ι) = R := by
  rw [idConverter, attachAlong_canon (c := forwardAll J (fun _ : J => X) (fun _ : J => Y)) hι
    (idConverter_isResponsiveDDC (J := J) (X := fun _ => X) (Y := fun _ => Y)) hR]
  exact attachAlong_forwardAll hι R hR.isDDS.1

end AlongIdentity

/-! ## An attachment depends only on the queried replies of the second component -/

section PairCongr

variable {Xa Ya Xb Yb A B : Type} {a : System Xa Ya} {b b' : System Xb Yb}
  {route : Two Ya Yb → B ⊕ Two Xa Xb} {inj : A → Two Xa Xb}

/-- The second component agrees on every query it receives along `H`. -/
def AgreesAlong (b b' : System Xb Yb) (H : List (Two Xa Xb)) : Prop :=
  ∀ G₀ x, G₀ ++ [⟨some (), x⟩] <+: H →
    b (restrict (some ()) G₀ ++ [x]) = b' (restrict (some ()) G₀ ++ [x])

theorem AgreesAlong.mono {H H'} (h : AgreesAlong (Xa := Xa) b b' H') (hp : H <+: H') :
    AgreesAlong (Xa := Xa) b b' H :=
  fun G₀ x hG => h G₀ x (hG.trans hp)

theorem pair_congr_right {G : List (Two Xa Xb)} (h : AgreesAlong (Xa := Xa) b b' G) :
    pair a b G = pair a b' G := by
  rcases List.eq_nil_or_concat G with rfl | ⟨G₀, g, rfl⟩
  · simp [pair]
  rw [List.concat_eq_append] at h ⊢
  rcases g with ⟨_ | ⟨⟨⟩⟩, g⟩
  · rw [pair_left, pair_left]
  · rw [pair_right, pair_right, h G₀ g (List.prefix_refl _)]

theorem Exchange.congr_right {G o G'} (l : Exchange (pair a b) route G o G')
    (h : AgreesAlong (Xa := Xa) b b' G') : Exchange (pair a b') route G o G' := by
  induction l with
  | silent G hd => exact Exchange.silent _ (by rwa [← pair_congr_right h])
  | out G y c hy hr => exact Exchange.out _ y c (by rwa [← pair_congr_right h]) hr
  | feed G y x o G'' hy hr l ih =>
    obtain ⟨e, he⟩ := l.extends
    refine Exchange.feed _ y x _ _ ?_ hr (ih h)
    rw [← pair_congr_right (h.mono ⟨x :: e, by rw [he]; simp⟩)]
    exact hy

theorem Induces.congr_right {u o H} (r : Induces (pair a b) route inj u o H)
    (h : AgreesAlong (Xa := Xa) b b' H) : Induces (pair a b') route inj u o H := by
  induction r with
  | nil => exact Induces.nil
  | snoc u x o₀ H₀ o H' r₀ l ih =>
    obtain ⟨e, he⟩ := l.extends
    exact Induces.snoc _ _ _ _ _ _ (ih (h.mono ⟨inj x :: e, by rw [he]; simp⟩))
      (l.congr_right h)

theorem restrict_prefix {K : Type} {F : K → Type} (k : K) {G H : List (Σ k, F k)} (h : G <+: H) :
    restrict k G <+: restrict k H := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨restrict k e, by rw [restrict_append]⟩

end PairCongr

end SystemAlgebra

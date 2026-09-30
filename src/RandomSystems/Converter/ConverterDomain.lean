import RandomSystems.Converter.ResourceCanon
import RandomSystems.Converter.FilterAttachment
import RandomSystems.Converter.PartialIdentity

/-!
# Converter domains

The converter domain from the inside domain `E` to the outside domain `F` admits,
after a transcript on the converter alphabets, the inputs legal for the phase whose
outside queries lie in `F` and whose inside replies answer queries in `E`. On finite
domains its transcripts are bounded. A DDC from `E` to `F` answers exactly these inputs
and queries only in `E`; attached to a resource with domain `E` it gives a resource with
domain `F`.
Sources: CR18, Definitions 3.8–3.9 (printed pp. 61–62); Lanzenberger–Maurer,
Definitions 5 and 8 (printed pp. 11, 13).

## Main definitions

* `converterAdmits`, `Admitted`: admission of inputs on the converter alphabets after
  the previous output
* `insideQueries`: the inside queries among outputs on the converter alphabets
* `converterDomain E F`, `Domain.converter`: the converter domain from `E` to `F`
* `IsDDCFrom E F b a`: a DDC from `E` to `F` with bound `b`

## Main results

* `length_lt_of_converterDomain`: admitted transcripts are bounded
* `IsDDC.eq_of_admitted_replies`: a DDC is determined by its transcripts on admitted inputs
* `IsDDCFrom.mapsDomain`: a DDC from `E` to `F` maps resources with domain `E`
  to resources with domain `F`
* `IsDDCFrom.replies_iff_of_le`: two DDCs from `E` to `F` below one system have the same
  transcripts
-/

namespace SystemAlgebra

open Classical

variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-! ## Admission along DDC transcripts -/

/-- Admitted inputs depend only on the previous output interface. -/
def converterAdmits
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
    (x : Σ l, twoFam U Y l) : Prop :=
  admitAfter (h.getLast?.map fun z => z.2.1) x.1

/-- Every query in the transcript is admitted after its preceding exchanges. -/
def Admitted {A B : Type} (D : List (A × B) → A → Prop) (h : List (A × B)) : Prop :=
  ∀ p z t, h = p ++ z :: t → D p z.1

@[simp] theorem admitted_nil {A B : Type} (D : List (A × B) → A → Prop) : Admitted D [] := by
  intro p z t he
  simp at he

theorem admitted_snoc {A B : Type} {D : List (A × B) → A → Prop} {h z} :
    Admitted D (h ++ [z]) ↔ Admitted D h ∧ D h z.1 := by
  constructor
  · intro ha
    exact ⟨fun p w t he => ha p w (t ++ [z]) (by rw [he]; simp), ha h z [] rfl⟩
  · rintro ⟨ha, hz⟩ p w t he
    rcases List.eq_nil_or_concat t with rfl | ⟨t, v, rfl⟩
    · have he' : h ++ [z] = p ++ [w] := he
      obtain ⟨rfl, hw⟩ := List.append_inj' he' rfl
      obtain rfl : z = w := by simpa using hw
      exact hz
    · rw [List.concat_eq_append] at he
      have he' : h ++ [z] = (p ++ w :: t) ++ [v] := by rw [he]; simp
      obtain ⟨rfl, -⟩ := List.append_inj' he' rfl
      exact ha p w t rfl

/-- **Restriction to a smaller domain**: a random system on `D`, set to zero on the histories
not admitted by `D' ⊆ D`, is a random system on `D'`. -/
theorem IsRandomSystem.restrict {A B : Type} {D D' : List (A × B) → A → Prop}
    {p : List (A × B) → ℝ} (hp : IsRandomSystem D p) (hD : ∀ h x, D' h x → D h x) :
    IsRandomSystem D' (fun h => if Admitted D' h then p h else 0) := by
  refine ⟨by simp [hp.1], fun h => ?_, fun h x => ?_⟩
  · dsimp only
    split_ifs
    exacts [hp.2.1 h, le_rfl]
  obtain ⟨μ, hμ, hw⟩ := hp.2.2 h x
  by_cases hadm : Admitted D' h ∧ D' h x
  · refine ⟨μ, fun y => ?_, ?_⟩
    · dsimp only
      rw [hμ, if_pos (admitted_snoc.mpr hadm)]
    · dsimp only
      rw [hw, if_pos (hD h x hadm.2), if_pos hadm.2, if_pos hadm.1]
  · refine ⟨0, fun y => ?_, ?_⟩
    · dsimp only
      rw [if_neg (fun ha => hadm (admitted_snoc.mp ha))]
      rfl
    · dsimp only
      by_cases hx : D' h x
      · rw [if_pos hx, if_neg (fun ha => hadm ⟨ha, hx⟩)]
        rfl
      · rw [if_neg hx]
        rfl

/-- A completed deterministic transcript fixes the preceding reply label. -/
theorem Replies.replyLabel {α : InsideOutsideSystem O J U V X Y} (hα : SilentAtEmpty α)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies α (h.map Prod.fst) (h.map Prod.snd)) :
    replyLabel α (h.map Prod.fst) = h.getLast?.map (fun z => z.2.1) := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨x, y⟩, rfl⟩
  · simp only [List.map_nil, List.getLast?_nil, Option.map_none]
    exact dif_neg hα
  · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil] at hr ⊢
    have hy := (replies_snoc.mp hr).2
    rw [replyLabel_of_mem α (by rw [hy]; exact Part.mem_some _)]
    simp

theorem Replies.admissible_iff_admitted {c : InsideOutsideSystem O J U V X Y} (hc : SilentAtEmpty c)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies c (h.map Prod.fst) (h.map Prod.snd)) :
    Admissible c (h.map Prod.fst) ↔ Admitted converterAdmits h := by
  revert hr
  induction h using List.reverseRecOn with
  | nil => intro _; simp
  | append_singleton h z ih =>
    intro hr
    simp only [List.map_append, List.map_singleton, replies_snoc] at hr
    have hd : h.map Prod.fst ≠ [] → (c (h.map Prod.fst)).Dom := hr.1.dom
    rw [List.map_append, List.map_singleton, admissible_snoc, admitted_snoc, ih hr.1]
    simp only [Admits, hr.1.replyLabel hc, converterAdmits]
    exact ⟨fun ⟨ha, _, hz⟩ => ⟨ha, hz⟩, fun ⟨ha, hz⟩ => ⟨ha, hd, hz⟩⟩

theorem replies_canon_iff (c : InsideOutsideSystem O J U V X Y) (hc : SilentAtEmpty c)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) :
    Replies (canon c) (h.map Prod.fst) (h.map Prod.snd) ↔
      Admitted converterAdmits h ∧ Replies c (h.map Prod.fst) (h.map Prod.snd) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton, replies_snoc, ih, admitted_snoc]
    by_cases hr : Replies c (h.map Prod.fst) (h.map Prod.snd)
    swap
    · tauto
    have ha := hr.admissible_iff_admitted hc
    have hd : h.map Prod.fst ≠ [] → (c (h.map Prod.fst)).Dom := hr.dom
    have hx : Admissible c (h.map Prod.fst ++ [x]) ↔
        Admitted converterAdmits h ∧ converterAdmits h x := by
      rw [admissible_snoc, ha]
      simp only [Admits, hr.replyLabel hc, converterAdmits]
      exact ⟨fun ⟨ha, _, hz⟩ => ⟨ha, hz⟩, fun ⟨ha, hz⟩ => ⟨ha, hd, hz⟩⟩
    by_cases had : Admitted converterAdmits h ∧ converterAdmits h x
    · rw [canon_of_admissible (hx.mpr had)]
      tauto
    · have hn : ¬ Admissible c (h.map Prod.fst ++ [x]) := fun hh => had (hx.mp hh)
      simp only [canon, hn, if_false, Part.none_ne_some]
      tauto

/-- Defined histories of a partial DDC are admissible. -/
theorem IsDDC.admissible {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α)
    {h : List (Σ l, twoFam U Y l)} (hd : (α h).Dom) : Admissible α h := by
  intro h' z e he
  subst he
  have hz : (α (h' ++ [z])).Dom := hα.dds.2 ⟨e, by simp⟩ (by simp) hd
  exact ⟨fun hne => hα.dds.2 ⟨z :: e, rfl⟩ hne hd, hα.admits h' z hz⟩

/-- Completed histories of a partial DDC are admitted. -/
theorem IsDDC.admitted_of_replies {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies α (h.map Prod.fst) (h.map Prod.snd)) : Admitted converterAdmits h := by
  by_cases hn : h.map Prod.fst = []
  · obtain rfl : h = [] := List.map_eq_nil_iff.mp hn
    exact admitted_nil _
  · exact (hr.admissible_iff_admitted hα.dds.1).mp (hα.admissible (hr.dom hn))

/-- A partial converter is its own canonical restriction. -/
theorem IsDDC.canon_eq {b : ℕ} {α : InsideOutsideSystem O J U V X Y} (hα : IsDDC b α) : canon α = α := by
  funext h
  by_cases hd : (α h).Dom
  · exact canon_of_admissible (hα.admissible hd)
  · unfold canon
    split_ifs
    · rfl
    · exact (Part.eq_none_iff'.mpr hd).symm

/-- Partial converters with the same completed histories on admitted inputs are equal. -/
theorem IsDDC.eq_of_admitted_replies {bα bβ : ℕ} {α β : InsideOutsideSystem O J U V X Y}
    (hα : IsDDC bα α) (hβ : IsDDC bβ β)
    (he : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)), Admitted converterAdmits h →
      (Replies α (h.map Prod.fst) (h.map Prod.snd) ↔
        Replies β (h.map Prod.fst) (h.map Prod.snd))) : α = β := by
  apply IsDDS.eq_of_replies_iff hα.dds hβ.dds
  intro xs ys
  by_cases hl : ys.length = xs.length
  · have hx : (xs.zip ys).map Prod.fst = xs := List.map_fst_zip (by omega)
    have hy : (xs.zip ys).map Prod.snd = ys := List.map_snd_zip (by omega)
    constructor
    · intro hr
      have hr' : Replies α ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) := by
        rw [hx, hy]; exact hr
      have := (he _ (hα.admitted_of_replies hr')).mp hr'
      rwa [hx, hy] at this
    · intro hr
      have hr' : Replies β ((xs.zip ys).map Prod.fst) ((xs.zip ys).map Prod.snd) := by
        rw [hx, hy]; exact hr
      have := (he _ (hβ.admitted_of_replies hr')).mpr hr'
      rwa [hx, hy] at this
  · exact ⟨fun hr => absurd hr.length hl, fun hr => absurd hr.length hl⟩

/-! ## The converter domain -/

/-- The inside queries among outputs on the converter alphabets. -/
noncomputable def insideQueries (ys : List (Σ l, twoFam V X l)) : List (Σ j, X j) :=
  restrict (some ()) (ys.map splitIn)

theorem insideQueries_append (ys zs : List (Σ l, twoFam V X l)) :
    insideQueries (ys ++ zs) = insideQueries ys ++ insideQueries zs := by
  simp only [insideQueries, List.map_append, restrict_append]

@[simp] theorem insideQueries_outside (o : O) (v : V o) :
    insideQueries [(⟨⟨none, o⟩, v⟩ : Σ l, twoFam V X l)] = [] := by
  simp [insideQueries, splitIn]

@[simp] theorem insideQueries_inside (j : J) (x : X j) :
    insideQueries [(⟨⟨some (), j⟩, x⟩ : Σ l, twoFam V X l)] = [⟨j, x⟩] := by
  simp [insideQueries, splitIn]

@[simp] theorem outsideInputs_outside (o : O) (u : U o) :
    outsideInputs [(⟨⟨none, o⟩, u⟩ : Σ l, twoFam U Y l)] = [⟨o, u⟩] := by
  simp [outsideInputs, splitIn]

@[simp] theorem outsideInputs_inside (j : J) (y : Y j) :
    outsideInputs [(⟨⟨some (), j⟩, y⟩ : Σ l, twoFam U Y l)] = [] := by
  simp [outsideInputs, splitIn]

/-- The inputs admitted from the inside domain `E` to the outside
domain `F`: legal for the phase, with outside queries in `F` and inside queries
so far in `E`. -/
def converterDomain (E : List (Σ j, X j) → Prop) (F : List (Σ o, U o) → Prop)
    (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) (x : Σ l, twoFam U Y l) : Prop :=
  Admitted converterAdmits h ∧ converterAdmits h x ∧
    F (outsideInputs (h.map Prod.fst ++ [x])) ∧
    (insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd)))

/-- An input on the converter alphabets is an outside query or an inside reply. -/
theorem length_eq_outsideInputs_add (xs : List (Σ l, twoFam U Y l)) :
    xs.length = (outsideInputs xs).length + (restrict (some ()) (xs.map splitIn)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨⟨_ | ⟨⟩, o⟩, u⟩ <;>
      simp [outsideInputs, splitIn, restrict_cons_self, restrict_cons_ne, ih] <;> omega

/-- Each inside reply follows an inside query. -/
theorem insideReplies_length_le {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    {x : Σ l, twoFam U Y l} (ha : Admitted converterAdmits h) (hx : converterAdmits h x) :
    (restrict (some ()) ((h.map Prod.fst ++ [x]).map splitIn)).length ≤
      (insideQueries (h.map Prod.snd)).length := by
  induction h using List.reverseRecOn generalizing x with
  | nil =>
    rcases x with ⟨⟨_ | ⟨⟩, o⟩, u⟩
    · simp [splitIn]
    · simp [converterAdmits, admitAfter] at hx
  | append_singleton h z ih =>
    obtain ⟨ha, hz⟩ := admitted_snoc.mp ha
    have ih := ih ha hz
    rcases z with ⟨x', y'⟩
    simp only [converterAdmits, List.getLast?_append, List.getLast?_singleton,
      Option.some_or, Option.map_some] at hx
    simp only [List.map_append, List.map_singleton, List.append_assoc, restrict_append,
      insideQueries_append, List.length_append] at ih ⊢
    rcases y' with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩ <;> rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o'⟩, u⟩
    · simp [splitIn] at ih ⊢; omega
    · simp [admitAfter] at hx
    · simp [admitAfter] at hx
    · simp [splitIn] at ih ⊢; omega

/-- Admitted transcripts are bounded by the two domain bounds. -/
theorem length_lt_of_converterDomain {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    {m n : ℕ} (hE : ∀ h, E h → h.length ≤ m) (hF : ∀ h, F h → h.length ≤ n)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))} {x : Σ l, twoFam U Y l}
    (hx : converterDomain E F h x) : h.length < n + m := by
  obtain ⟨ha, hx', hFx, hEx⟩ := hx
  have hl := length_eq_outsideInputs_add (h.map Prod.fst ++ [x])
  have hr := insideReplies_length_le ha hx'
  have hn := hF _ hFx
  have hm : (insideQueries (h.map Prod.snd)).length ≤ m := by
    rcases hEx with he | he
    · simp [he]
    · exact hE _ he
  simp only [List.length_append, List.length_map, List.length_singleton] at hl
  omega

/-- The converter domain from `E` (bound `m`) to `F` (bound `n`). -/
def Domain.converter (E : List (Σ j, X j) → Prop) (m : ℕ) (hE : ∀ h, E h → h.length ≤ m)
    (F : List (Σ o, U o) → Prop) (n : ℕ) (hF : ∀ h, F h → h.length ≤ n) :
    Domain (Σ l, twoFam U Y l) (Σ l, twoFam V X l) where
  admits := converterDomain E F
  bound := n + m
  length_lt _ _ hx := length_lt_of_converterDomain hE hF hx

/-! ## DDCs from `E` to `F` -/

/-- A DDC converting systems with domain `E` into systems with domain `F`: it
answers exactly the converter domain and queries only in `E`. -/
structure IsDDCFrom (E : List (Σ j, X j) → Prop) (F : List (Σ o, U o) → Prop) (b : ℕ)
    (a : InsideOutsideSystem O J U V X Y) : Prop where
  isDDC : IsDDC b a
  answers : ∀ (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) (x : Σ l, twoFam U Y l),
    Replies a (h.map Prod.fst) (h.map Prod.snd) →
      ((a (h.map Prod.fst ++ [x])).Dom ↔ converterDomain E F h x)
  queries : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
    Replies a (h.map Prod.fst) (h.map Prod.snd) →
      insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd))

/-- Along a transcript of a DDC from `E` to `F`, the outside queries are in `F`. -/
theorem IsDDCFrom.outsideInputs_mem {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    {b : ℕ} {a : InsideOutsideSystem O J U V X Y} (ha : IsDDCFrom E F b a)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies a (h.map Prod.fst) (h.map Prod.snd)) :
    outsideInputs (h.map Prod.fst) = [] ∨ F (outsideInputs (h.map Prod.fst)) := by
  rcases List.eq_nil_or_concat h with rfl | ⟨h, ⟨x, y⟩, rfl⟩
  · exact Or.inl rfl
  · simp only [List.concat_eq_append, List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    exact Or.inr ((ha.answers h x hr).mp (by rw [hy]; trivial)).2.2.1

/-! ## The identity -/

section Identity

/-- The first input of a legal history is an outside query. -/
theorem outsideInputs_ne_nil {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    {x : Σ l, twoFam U Y l} (ha : Admitted converterAdmits h) (hx : converterAdmits h x) :
    outsideInputs (h.map Prod.fst ++ [x]) ≠ [] := by
  rcases h with _ | ⟨⟨x₀, y₀⟩, t⟩
  · rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩
    · simp
    · simp [converterAdmits, admitAfter] at hx
  · have h₀ : converterAdmits [] x₀ := ha [] (x₀, y₀) t rfl
    rcases x₀ with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩
    · simp [outsideInputs, splitIn]
    · simp [converterAdmits, admitAfter] at h₀

/-- Along a transcript of the identity, the inside queries are the outside queries. -/
theorem insideQueries_eq_of_replies_id {h : List ((Σ l, twoFam X Y l) × (Σ l, twoFam Y X l))}
    (hr : Replies (idConverter J X Y) (h.map Prod.fst) (h.map Prod.snd)) :
    insideQueries (h.map Prod.snd) = outsideInputs (h.map Prod.fst) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h z ih =>
    rcases z with ⟨x, y⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hr, hy⟩ := replies_snoc.mp hr
    have hy' := canon_mem (Part.eq_some_iff.mp hy)
    rw [insideQueries_append, outsideInputs_append, ih hr]
    rcases x with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, v⟩
    · rw [forwardAll_snoc_outer] at hy'
      obtain rfl := Part.mem_some_iff.mp hy'
      simp
    · rw [forwardAll_snoc_inner] at hy'
      obtain rfl := Part.mem_some_iff.mp hy'
      simp

theorem prefix_or_nil {A : Type} {E : List A → Prop}
    (hE : ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    ∀ {p h : List A}, p <+: h → (h = [] ∨ E h) → (p = [] ∨ E p) := by
  intro p h hp hh
  by_cases hn : p = []
  · exact Or.inl hn
  · rcases hh with rfl | hh
    · exact Or.inl (List.prefix_nil.mp hp)
    · exact Or.inr (hE hp hn hh)

theorem DDC.isDDC_filter (D : List (Σ j, X j) → Prop) (hD : ∀ {p h}, p <+: h → D h → D p) :
    IsDDC 1 (DDC.filter (Y := Y) D hD).1 :=
  (idConverter_isResponsiveDDC (J := J) (X := X) (Y := Y)).isDDC.filterDom _
    (fun {p h} hp _ hd => hD (by
      obtain ⟨e, rfl⟩ := hp
      exact ⟨outsideInputs e, (outsideInputs_append p e).symm⟩) hd)

/-- **A responsive DDC restricted to an outside domain `F`** is a DDC from `E` to `F` when the
inside queries of its transcripts stay in `E`. -/
theorem IsResponsiveDDC.isDDCFrom_filterDom {E : List (Σ j, X j) → Prop}
    {F : List (Σ o, U o) → Prop} {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α) (hF : ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (hq : ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (filterDom (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs)) α)
        (h.map Prod.fst) (h.map Prod.snd) →
      insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd))) :
    IsDDCFrom E F b (filterDom (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs)) α) := by
  have hD : ∀ {p h : List (Σ l, twoFam U Y l)}, p <+: h → p ≠ [] →
      (outsideInputs h = [] ∨ F (outsideInputs h)) →
      (outsideInputs p = [] ∨ F (outsideInputs p)) := fun {p h} hp _ hd =>
    prefix_or_nil hF (by
      obtain ⟨e, rfl⟩ := hp
      exact ⟨outsideInputs e, (outsideInputs_append p e).symm⟩) hd
  have hf : IsDDC b (filterDom (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs)) α) :=
    hα.isDDC.filterDom _ hD
  have hsub : ∀ h y, y ∈ filterDom (fun xs => outsideInputs xs = [] ∨ F (outsideInputs xs)) α h →
      y ∈ α h := fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
  refine ⟨hf, fun h x hr => ?_, hq⟩
  have hri := hr.mono hsub
  have hadm := hf.admitted_of_replies hr
  rw [filterDom_dom, hα.dom_iff, admissible_snoc, hri.admissible_iff_admitted hα.dds.1]
  simp only [Admits, hri.replyLabel hα.dds.1]
  constructor
  · rintro ⟨hFx, -, -, -, hx⟩
    exact ⟨hadm, hx, hFx.resolve_left (outsideInputs_ne_nil hadm hx), hq h hr⟩
  · rintro ⟨-, hx, hFx, -⟩
    exact ⟨Or.inr hFx, by simp, hadm, fun hn => hri.dom hn, hx⟩

/-- **The identity from `E` to `E`** is the filter forwarding the outside queries in `E`
(CR18, §3.4.3, printed p. 62). -/
theorem isDDCFrom_filter {E : List (Σ j, X j) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) :
    IsDDCFrom E E 1 (DDC.filter (Y := Y) (fun h => h = [] ∨ E h) (prefix_or_nil hE.2)).1 :=
  (idConverter_isResponsiveDDC (J := J) (X := X) (Y := Y)).isDDCFrom_filterDom hE.2
    fun h hr => by
      have hri := hr.mono fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
      rw [insideQueries_eq_of_replies_id hri]
      by_cases hn : h.map Prod.fst = []
      · exact Or.inl (by rw [hn]; rfl)
      · exact ((filterDom_dom _ _ _).mp (hr.dom hn)).1

/-- A DDC from `E` to `F` is a DDC from any larger inside domain `E'` to `F`. -/
theorem IsDDCFrom.inside_mono {E E' : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    {b : ℕ} {a : InsideOutsideSystem O J U V X Y} (ha : IsDDCFrom E F b a)
    (hE : ∀ h, E h → E' h) : IsDDCFrom E' F b a where
  isDDC := ha.isDDC
  answers h x hr := by
    rw [ha.answers h x hr]
    exact ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄.imp_right (hE _)⟩,
      fun ⟨h₁, h₂, h₃, _⟩ => ⟨h₁, h₂, h₃, ha.queries h hr⟩⟩
  queries h hr := (ha.queries h hr).imp_right (hE _)

/-- Attaching the identity from `E` to `E` leaves a resource with domain `E` unchanged. -/
theorem trim_apply_filter_of_dom {E : List (Σ j, X j) → Prop}
    (hE : ¬ E [] ∧ ∀ {p h}, p <+: h → p ≠ [] → E h → E p) {R : InterfaceSystem J X Y}
    (hR : IsDDS R) (hr : RepliesAtQueriedInterface R) (hRE : ∀ h, (R h).Dom ↔ E h) :
    trim (apply (DDC.filter (Y := Y) (fun h => h = [] ∨ E h) (prefix_or_nil hE.2)).1 R) = R := by
  rw [trim_apply_filter _ _ hR hr]
  funext h
  by_cases hd : h = [] ∨ E h
  · simp [filterDom, hd]
  · rw [filterDom, if_neg hd]
    exact (Part.eq_none_iff'.mpr fun hd' => hd (Or.inr ((hRE h).mp hd'))).symm

end Identity

/-! ## Attachment to a resource -/

section Attachment

variable {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop} {b : ℕ}
  {a : InsideOutsideSystem O J U V X Y} {R : InterfaceSystem J X Y}

/-- Between calls: the DDC's history is one of its transcripts with no open
inside query, and the resource has received exactly its inside queries. -/
def AttachIdle (a : InsideOutsideSystem O J U V X Y)
    (H : List (Two (Σ l, twoFam U Y l) (Σ j, X j))) : Prop :=
  ∃ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
    restrict none H = h.map Prod.fst ∧ Replies a (h.map Prod.fst) (h.map Prod.snd) ∧
    restrict (some ()) H = insideQueries (h.map Prod.snd) ∧ ∀ z ∈ h.getLast?, ¬ IsInside z.2

/-- During a call at the outside label `o`: the DDC is about to answer an
admitted input, or the resource is about to answer the DDC's last query. -/
def AttachCall (E : List (Σ j, X j) → Prop) (F : List (Σ o, U o) → Prop)
    (a : InsideOutsideSystem O J U V X Y) (o : O)
    (G : List (Two (Σ l, twoFam U Y l) (Σ j, X j))) : Prop :=
  (∃ (G₁ : List (Two (Σ l, twoFam U Y l) (Σ j, X j)))
      (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) (z : Σ l, twoFam U Y l),
      G = G₁ ++ [⟨none, z⟩] ∧ restrict none G₁ = h.map Prod.fst ∧
      Replies a (h.map Prod.fst) (h.map Prod.snd) ∧
      restrict (some ()) G₁ = insideQueries (h.map Prod.snd) ∧
      converterDomain E F h z ∧ lastOuter (h.map Prod.fst ++ [z]) = some o) ∨
  (∃ (G₁ : List (Two (Σ l, twoFam U Y l) (Σ j, X j)))
      (h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))) (j : J) (x : X j),
      G = G₁ ++ [⟨some (), ⟨j, x⟩⟩] ∧ restrict none G₁ = h.map Prod.fst ∧
      Replies a (h.map Prod.fst) (h.map Prod.snd) ∧
      h.getLast?.map Prod.snd = some ⟨⟨some (), j⟩, x⟩ ∧
      restrict (some ()) G₁ ++ [⟨j, x⟩] = insideQueries (h.map Prod.snd) ∧
      F (outsideInputs (h.map Prod.fst)) ∧ lastOuter (h.map Prod.fst) = some o)

/-- A call answers at its outside label and leaves the DDC idle: every
admitted input is answered, and every query is in `E`, where the resource answers. -/
theorem IsDDCFrom.attach_call (ha : IsDDCFrom E F b a) (hR : RepliesAtQueriedInterface R)
    (hRE : ∀ h, (R h).Dom ↔ E h) {G o' G'}
    (l : Exchange (pair a R) resourceRoute G o' G') :
    ∀ o, AttachCall E F a o G → ∃ w : Σ o, V o, o' = some w ∧ w.1 = o ∧ AttachIdle a G' := by
  induction l with
  | silent G hd =>
    intro o hG
    rcases hG with ⟨G₁, h, z, rfl, hH, hr, -, hz, -⟩ | ⟨G₁, h, j, x, rfl, -, hr, -, hq, -, -⟩
    · rw [pair_left, Part.map_Dom, hH] at hd
      exact (hd ((ha.answers h z hr).mpr hz)).elim
    · rw [pair_right, Part.map_Dom, hq] at hd
      refine (hd ((hRE _).mpr ?_)).elim
      rcases ha.queries h hr with he | he
      · rw [← hq] at he
        simp at he
      · exact he
  | out G y w hy hr =>
    intro o hG
    rcases hG with ⟨G₁, h, z, rfl, hH, hr', hQ, -, hlo⟩ | ⟨G₁, h, j, x, rfl, -, -, -, -, -, -⟩
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, v⟩
      · cases hr
        have hi := ha.isDDC.replies _ _ i hv rfl
        rw [hH, hlo] at hi
        refine ⟨_, rfl, Option.some.inj hi.symm, h ++ [(z, ⟨⟨none, i⟩, v⟩)], ?_, ?_, ?_, ?_⟩
        · simp [hH]
        · rw [hH] at hv
          simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hr', Part.eq_some_iff.mpr hv⟩
        · simp [hQ, insideQueries_append]
        · simp [IsInside]
      · cases hr
    · rw [pair_right] at hy
      obtain ⟨v, -, rfl⟩ := (Part.mem_map_iff _).mp hy
      cases hr
  | feed G y x' o' G'' hy hr l ih =>
    intro o hG
    rcases hG with ⟨G₁, h, z, rfl, hH, hr', hQ, hz, hlo⟩ |
        ⟨G₁, h, j, x, rfl, hH, hr', hlast, hQ, hF, hlo⟩
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, q⟩
      · cases hr
      · cases hr
        rw [hH] at hv
        refine ih o (Or.inr ⟨_, h ++ [(z, ⟨⟨some (), j⟩, q⟩)], j, q, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩)
        · simp [hH]
        · simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hr', Part.eq_some_iff.mpr hv⟩
        · simp
        · simp [hQ, insideQueries_append]
        · simpa only [List.map_append, List.map_singleton] using hz.2.2.1
        · simpa only [List.map_append, List.map_singleton] using hlo
    · rw [pair_right] at hy
      obtain ⟨r, hrv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases r with ⟨i, w⟩
      have hi : i = j := hR _ _ _ hrv
      subst hi
      cases hr
      have hlab : h.getLast?.map (fun z => z.2.1) = some ⟨some (), i⟩ := by
        rw [show (fun z : (Σ l, twoFam U Y l) × (Σ l, twoFam V X l) => z.2.1) =
          (fun y => y.1) ∘ Prod.snd from rfl, ← Option.map_map, hlast]
        rfl
      refine ih o (Or.inl ⟨_, h, ⟨⟨some (), i⟩, w⟩, rfl, ?_, hr', ?_, ?_, ?_⟩)
      · rw [restrict_none_snoc_right, hH]
      · rw [restrict_some_snoc_right, hQ]
      · refine ⟨ha.isDDC.admitted_of_replies hr', ?_, ?_, ha.queries h hr'⟩
        · simp [converterAdmits, hlab, admitAfter]
        · simpa [outsideInputs_append] using hF
      · simpa [lastOuter_snoc, outerOf] using hlo

/-- The next outside query after a completed history: answered exactly when it is
in `F`, at its own label. -/
theorem IsDDCFrom.attach_next (ha : IsDDCFrom E F b a) (hR : RepliesAtQueriedInterface R)
    (hRE : ∀ h, (R h).Dom ↔ E h) {xs : List (Σ o, U o)} {o₀ H}
    (r : Induces (pair a R) resourceRoute resourceInput xs o₀ H) (hi : AttachIdle a H)
    (x : Σ o, U o) {o' H'} (lx : Exchange (pair a R) resourceRoute (H ++ [resourceInput x]) o' H')
    (hc : F (xs ++ [x]) ∨ o' ≠ none) :
    ∃ w : Σ o, V o, o' = some w ∧ w.1 = x.1 ∧ AttachIdle a H' ∧ F (xs ++ [x]) := by
  obtain ⟨h, hH, hr, hQ, hlast⟩ := hi
  let z : Σ l, twoFam U Y l := ⟨⟨none, x.1⟩, x.2⟩
  have hout : outsideInputs (h.map Prod.fst ++ [z]) = xs ++ [x] := by
    rw [outsideInputs_append, ← hH, r.outsideInputs_resource, outsideInputs_outside]
  have hz : converterDomain E F h z := by
    rcases hc with hF | hn
    · refine ⟨ha.isDDC.admitted_of_replies hr, ?_, hout ▸ hF, ha.queries h hr⟩
      refine (admitAfter_of_ne fun j hj => ?_).mpr rfl
      obtain ⟨p, hp, hpj⟩ := Option.map_eq_some_iff.mp hj
      exact hlast p hp (by simp [IsInside, hpj])
    · apply (ha.answers h z hr).mp
      by_contra hd
      apply hn
      apply exchange_silent_of_not_dom lx
      rw [resourceInput, pair_left, Part.map_Dom, hH]
      exact hd
  obtain ⟨w, hw, hw1, hi'⟩ := ha.attach_call hR hRE lx x.1
    (Or.inl ⟨H, h, z, rfl, hH, hr, hQ, hz, by simp [lastOuter_snoc, outerOf, z]⟩)
  exact ⟨w, hw, hw1, hi', hout ▸ hz.2.2.1⟩

/-- Every completed history of the attachment leaves the DDC idle. -/
theorem IsDDCFrom.attach_idle (ha : IsDDCFrom E F b a) (hR : RepliesAtQueriedInterface R)
    (hRE : ∀ h, (R h).Dom ↔ E h) :
    ∀ xs ys, Replies (apply a R) xs ys →
      ∃ H, Induces (pair a R) resourceRoute resourceInput xs ys.getLast? H ∧ AttachIdle a H := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
    intro ys hy
    obtain rfl : ys = [] := List.length_eq_zero_iff.mp hy.length
    exact ⟨[], Induces.nil, [], rfl, replies_nil _, rfl, by simp⟩
  | append_singleton xs x ih =>
    intro ys hy
    have hn : ys ≠ [] := by intro he; have hl := hy.length; simp [he] at hl
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
    rw [List.concat_eq_append] at hy ⊢
    obtain ⟨hp, hy⟩ := replies_snoc.mp hy
    obtain ⟨H, r, hi⟩ := ih ys hp
    rw [apply_eq] at hy
    obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.eq_some_iff.mp hy)
    obtain ⟨o₀, H₀, r₀, lx⟩ := induces_snoc_iff.mp r'
    obtain ⟨-, rfl⟩ := r.det r₀
    obtain ⟨w, hw, -, hi', -⟩ := ha.attach_next hR hRE r hi x lx (Or.inr (by simp))
    exact ⟨H', by simpa using r', hi'⟩

/-- **A DDC from `E` to `F` maps resources with domain `E` to resources with domain
`F`**, replying at the queried interface. -/
theorem IsDDCFrom.mapsDomain (ha : IsDDCFrom E F b a)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p) : MapsDomain E F a := by
  intro R _ hR hRE
  have next : ∀ xs ys x, Replies (apply a R) xs ys →
      ((apply a R (xs ++ [x])).Dom ↔ F (xs ++ [x])) ∧
        ∀ y ∈ apply a R (xs ++ [x]), y.1 = x.1 := by
    intro xs ys x hr
    obtain ⟨H, r, hi⟩ := ha.attach_idle hR hRE xs ys hr
    obtain ⟨o', H', r'⟩ := ha.isDDC.converges_resource R (xs ++ [x])
    obtain ⟨o₀, H₀, r₀, lx⟩ := induces_snoc_iff.mp r'
    obtain ⟨-, rfl⟩ := r.det r₀
    have hs := ha.attach_next hR hRE r hi x lx
    rw [apply_eq]
    refine ⟨⟨fun hd => ?_, fun hFx => ?_⟩, fun y hy => ?_⟩
    · refine (hs (Or.inr ?_)).choose_spec.2.2.2
      rintro rfl
      exact not_dom_of_induces_none r' hd
    · obtain ⟨w, rfl, -, -, -⟩ := hs (Or.inl hFx)
      exact Part.dom_iff_mem.mpr ⟨w, mem_of_induces_some r'⟩
    · obtain ⟨H'', r''⟩ := mem_interconnect.mp hy
      obtain ⟨rfl, -⟩ := r'.det r''
      obtain ⟨w, hw, hw1, -⟩ := hs (Or.inr (by simp))
      cases hw
      exact hw1
  refine ⟨fun xs x y hy => ?_, trim_dom_of_admission (by simp [SilentAtEmpty, apply_eq]) hF
    (fun xs x ys hr => (next xs ys x hr).1)⟩
  have hreach := reach_of_trim hy.1
  obtain ⟨ys, hr⟩ := (reach_snoc_iff.mp hreach).1.exists_replies
  exact (next xs ys x hr).2 y (by simpa only [trim, if_pos hreach] using hy)

end Attachment

/-! ## Serial composition -/

section Serial

variable {M : Type} {Xm Ym : M → Type} {E : List (Σ j, X j) → Prop}
  {F : List (Σ m, Xm m) → Prop} {G : List (Σ o, U o) → Prop} {bβ bα : ℕ}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}

/-- The components behind a composite step. `β` has received the outside queries `P`, `α`
has received `β`'s inside queries, and `α`'s inside queries are `Q`. Either the three are
idle, or the composite's last output `o` is an inside query of `α`, made during a call of
`β` at `α`'s last outside label. -/
def SerialAfter (G : List (Σ o, U o) → Prop) (β : InsideOutsideSystem O M U V Xm Ym)
    (α : InsideOutsideSystem M J Xm Ym X Y) (P : List (Σ o, U o)) (Q : List (Σ j, X j))
    (o : Option (Σ l : Two O J, twoFam V X l))
    (K : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  ∃ (hb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)))
    (ha : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l))),
    restrict none K = hb.map Prod.fst ∧ Replies β (hb.map Prod.fst) (hb.map Prod.snd) ∧
    restrict (some ()) K = ha.map Prod.fst ∧ Replies α (ha.map Prod.fst) (ha.map Prod.snd) ∧
    outsideInputs (hb.map Prod.fst) = P ∧
    outsideInputs (ha.map Prod.fst) = insideQueries (hb.map Prod.snd) ∧
    insideQueries (ha.map Prod.snd) = Q ∧
    (((∀ y ∈ o, ¬ IsInside y) ∧ (∀ z ∈ hb.getLast?, ¬ IsInside z.2) ∧
        (∀ z ∈ ha.getLast?, ¬ IsInside z.2)) ∨
      ∃ (j : J) (x : X j) (m : M) (q : Xm m), o = some ⟨⟨some (), j⟩, x⟩ ∧
        ha.getLast?.map Prod.snd = some ⟨⟨some (), j⟩, x⟩ ∧
        hb.getLast?.map Prod.snd = some ⟨⟨some (), m⟩, q⟩ ∧
        lastOuter (ha.map Prod.fst) = some m ∧ G P)

/-- During a composite call with outside queries `P` and inside queries `Q`: `β` is about to
answer an input of its domain, or `α` is about to answer an input of its domain during a call
of `β` at its last outside label. -/
def SerialCall (E : List (Σ j, X j) → Prop) (F : List (Σ m, Xm m) → Prop)
    (G : List (Σ o, U o) → Prop) (β : InsideOutsideSystem O M U V Xm Ym)
    (α : InsideOutsideSystem M J Xm Ym X Y) (P : List (Σ o, U o)) (Q : List (Σ j, X j))
    (K : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l))) : Prop :=
  (∃ (K₁ : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l)))
      (hb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)))
      (ha : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l))) (z : Σ l, twoFam U Ym l),
      K = K₁ ++ [⟨none, z⟩] ∧
      restrict none K₁ = hb.map Prod.fst ∧ Replies β (hb.map Prod.fst) (hb.map Prod.snd) ∧
      restrict (some ()) K₁ = ha.map Prod.fst ∧ Replies α (ha.map Prod.fst) (ha.map Prod.snd) ∧
      converterDomain F G hb z ∧ outsideInputs (hb.map Prod.fst ++ [z]) = P ∧
      outsideInputs (ha.map Prod.fst) = insideQueries (hb.map Prod.snd) ∧
      insideQueries (ha.map Prod.snd) = Q ∧ ∀ w ∈ ha.getLast?, ¬ IsInside w.2) ∨
  (∃ (K₁ : List (Two (Σ l, twoFam U Ym l) (Σ l, twoFam Xm Y l)))
      (hb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)))
      (ha : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l))) (z : Σ l, twoFam Xm Y l)
      (m : M) (q : Xm m),
      K = K₁ ++ [⟨some (), z⟩] ∧
      restrict none K₁ = hb.map Prod.fst ∧ Replies β (hb.map Prod.fst) (hb.map Prod.snd) ∧
      restrict (some ()) K₁ = ha.map Prod.fst ∧ Replies α (ha.map Prod.fst) (ha.map Prod.snd) ∧
      converterDomain E F ha z ∧ hb.getLast?.map Prod.snd = some ⟨⟨some (), m⟩, q⟩ ∧
      lastOuter (ha.map Prod.fst ++ [z]) = some m ∧ outsideInputs (hb.map Prod.fst) = P ∧
      outsideInputs (ha.map Prod.fst ++ [z]) = insideQueries (hb.map Prod.snd) ∧
      insideQueries (ha.map Prod.snd) = Q)

theorem getLast?_label {A K : Type} {F : K → Type}
    {h : List (A × (Σ l, F l))} {y : Σ l, F l} (hy : h.getLast?.map Prod.snd = some y) :
    h.getLast?.map (fun z => z.2.1) = some y.1 := by
  rw [show (fun z : A × (Σ l, F l) => z.2.1) = (fun y => y.1) ∘ Prod.snd from rfl,
    ← Option.map_map, hy]
  rfl

theorem getLast?_snd {A B : Type} {h : List (A × B)} {p : A × B} (hp : p ∈ h.getLast?) :
    p.2 ∈ (h.map Prod.snd).getLast? := by
  rw [List.getLast?_map, Option.mem_def.mp hp]
  rfl

theorem converterAdmits_of_idle {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hl : ∀ z ∈ h.getLast?, ¬ IsInside z.2) (x : Σ l, twoFam U Y l) :
    converterAdmits h x ↔ x.1.1 = none :=
  admitAfter_of_ne fun j hj => by
    obtain ⟨p, hp, hpj⟩ := Option.map_eq_some_iff.mp hj
    exact hl p hp (by simp [IsInside, hpj])

theorem converterAdmits_of_query {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    {j : J} {x : X j} (hl : h.getLast?.map Prod.snd = some ⟨⟨some (), j⟩, x⟩)
    (z : Σ l, twoFam U Y l) : converterAdmits h z ↔ z.1 = ⟨some (), j⟩ := by
  rw [converterAdmits, getLast?_label hl]
  rfl

/-- A call of the composite ends with an exposed output: every input reaching a component
lies in its domain. -/
theorem IsDDCFrom.serial_call (hβ : IsDDCFrom F G bβ β) (hα : IsDDCFrom E F bα α)
    {P : List (Σ o, U o)} {Q : List (Σ j, X j)} (hP : G P) {K o' K'}
    (l : Exchange (pair β α) serialRouteM K o' K') :
    SerialCall E F G β α P Q K →
      ∃ w, o' = some w ∧ SerialAfter G β α P (Q ++ insideQueries [w]) (some w) K' := by
  induction l with
  | silent K hd =>
    rintro (⟨K₁, hb, ha, z, rfl, hKb, hrb, -, -, hz, -⟩ |
      ⟨K₁, hb, ha, z, m, q, rfl, -, -, hKa, hra, hz, -⟩)
    · rw [pair_left, Part.map_Dom, hKb] at hd
      exact (hd ((hβ.answers hb z hrb).mpr hz)).elim
    · rw [pair_right, Part.map_Dom, hKa] at hd
      exact (hd ((hα.answers ha z hra).mpr hz)).elim
  | out K y w hy hr =>
    rintro (⟨K₁, hb, ha, z, rfl, hKb, hrb, hKa, hra, -, hPz, hR2, hQ, hia⟩ |
      ⟨K₁, hb, ha, z, m, q, rfl, hKb, hrb, hKa, hra, -, hlb, hlo, hPb, hR2, hQ⟩)
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · cases hr
        rw [hKb] at hv
        refine ⟨_, rfl, hb ++ [(z, ⟨⟨none, o⟩, v⟩)], ha, ?_, ?_, ?_, hra, ?_, ?_, ?_,
          Or.inl ⟨?_, ?_, hia⟩⟩
        · simp [hKb]
        · simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hrb, Part.eq_some_iff.mpr hv⟩
        · simp [hKa]
        · simpa only [List.map_append, List.map_singleton] using hPz
        · simp [hR2, insideQueries_append]
        · simp [hQ]
        · simp [IsInside]
        · simp [IsInside]
      · cases hr
    · rw [pair_right] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, j⟩, x⟩
      · cases hr
      · cases hr
        rw [hKa] at hv
        refine ⟨_, rfl, hb, ha ++ [(z, ⟨⟨some (), j⟩, x⟩)], ?_, hrb, ?_, ?_, hPb, ?_, ?_,
          Or.inr ⟨j, x, m, q, rfl, by simp, hlb, ?_, hP⟩⟩
        · simp [hKb]
        · simp [hKa]
        · simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hra, Part.eq_some_iff.mpr hv⟩
        · simpa only [List.map_append, List.map_singleton] using hR2
        · simp [hQ, insideQueries_append]
        · simpa only [List.map_append, List.map_singleton] using hlo
  | feed K y x' o' K'' hy hr l ih =>
    rintro (⟨K₁, hb, ha, z, rfl, hKb, hrb, hKa, hra, hz, hPz, hR2, hQ, hia⟩ |
      ⟨K₁, hb, ha, z, m, q, rfl, hKb, hrb, hKa, hra, hz, hlb, hlo, hPb, hR2, hQ⟩)
    · rw [pair_left] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, v⟩
      · cases hr
      · cases hr
        rw [hKb] at hv
        let y : Σ l, twoFam V Xm l := ⟨⟨some (), o⟩, v⟩
        have hrb' : Replies β ((hb ++ [(z, y)]).map Prod.fst) ((hb ++ [(z, y)]).map Prod.snd) := by
          simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hrb, Part.eq_some_iff.mpr hv⟩
        have hFq : F (insideQueries ((hb ++ [(z, y)]).map Prod.snd)) := by
          rcases hβ.queries _ hrb' with he | he
          · simp [insideQueries_append, y] at he
          · exact he
        refine ih (Or.inr ⟨_, hb ++ [(z, y)], ha, ⟨⟨none, o⟩, v⟩, o, v, rfl,
          ?_, hrb', ?_, hra, ⟨hα.isDDC.admitted_of_replies hra, ?_, ?_, hα.queries ha hra⟩,
          by simp [y], by simp [lastOuter_snoc, outerOf], ?_, ?_, hQ⟩)
        · simp [hKb]
        · simp [hKa]
        · exact (converterAdmits_of_idle hia _).mpr rfl
        · rw [outsideInputs_append, hR2, outsideInputs_outside]
          simpa [insideQueries_append, y] using hFq
        · simpa only [List.map_append, List.map_singleton] using hPz
        · simp [outsideInputs_append, hR2, insideQueries_append, y]
    · rw [pair_right] at hy
      obtain ⟨v, hv, rfl⟩ := (Part.mem_map_iff _).mp hy
      rcases v with ⟨⟨_ | ⟨⟨⟩⟩, m'⟩, v⟩
      · cases hr
        rw [hKa] at hv
        have hm := hα.isDDC.replies _ _ m' hv rfl
        rw [hlo] at hm
        obtain rfl : m' = m := (Option.some.inj hm).symm
        refine ih (Or.inl ⟨_, hb, ha ++ [(z, ⟨⟨none, m'⟩, v⟩)], ⟨⟨some (), m'⟩, v⟩, rfl,
          ?_, hrb, ?_, ?_, ⟨hβ.isDDC.admitted_of_replies hrb, ?_, ?_, hβ.queries hb hrb⟩,
          ?_, ?_, ?_, by simp [IsInside]⟩)
        · simp [hKb]
        · simp [hKa]
        · simpa only [List.map_append, List.map_singleton] using
            replies_snoc.mpr ⟨hra, Part.eq_some_iff.mpr hv⟩
        · exact (converterAdmits_of_query hlb _).mpr rfl
        · simpa [outsideInputs_append, hPb] using hP
        · simp [outsideInputs_append, hPb]
        · simpa only [List.map_append, List.map_singleton] using hR2
        · simp [hQ, insideQueries_append]
      · cases hr

/-- The composite's next input: in its domain exactly when the composite answers it, and then
the components are again behind a composite step. -/
theorem IsDDCFrom.serial_next (hβ : IsDDCFrom F G bβ β) (hα : IsDDCFrom E F bα α)
    {h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))} {K}
    (hr : Replies (serialM β α) (h.map Prod.fst) (h.map Prod.snd))
    (hs : SerialAfter G β α (outsideInputs (h.map Prod.fst)) (insideQueries (h.map Prod.snd))
      (h.map Prod.snd).getLast? K)
    (x : Σ l, twoFam U Y l) {o' K'}
    (lx : Exchange (pair β α) serialRouteM (K ++ [serialInjM x]) o' K')
    (hc : converterDomain E G h x ∨ o' ≠ none) :
    converterDomain E G h x ∧ ∃ w, o' = some w ∧
      SerialAfter G β α (outsideInputs (h.map Prod.fst ++ [x]))
        (insideQueries (h.map Prod.snd ++ [w])) (some w) K' := by
  obtain ⟨hb, ha, hKb, hrb, hKa, hra, hPb, hR2, hQ, hst⟩ := hs
  have hγ := hβ.isDDC.comp hα.isDDC
  have hrγ : Replies (trim (serialM β α)) (h.map Prod.fst) (h.map Prod.snd) :=
    (replies_trim_iff _ _ _).mpr hr
  have hE : insideQueries (h.map Prod.snd) = [] ∨ E (insideQueries (h.map Prod.snd)) := by
    rw [← hQ]; exact hα.queries ha hra
  -- the composite's phase is read off its last output
  have hidle : (∀ y ∈ (h.map Prod.snd).getLast?, ¬ IsInside y) →
      ∀ z ∈ h.getLast?, ¬ IsInside z.2 := fun hi z hz => hi z.2 (getLast?_snd hz)
  have hwait : ∀ {j : J} {x : X j}, (h.map Prod.snd).getLast? = some ⟨⟨some (), j⟩, x⟩ →
      h.getLast?.map Prod.snd = some ⟨⟨some (), j⟩, x⟩ := fun hl => by
    rwa [List.getLast?_map] at hl
  simp only [insideQueries_append]
  rcases x with ⟨⟨_ | ⟨⟨⟩⟩, o⟩, u⟩
  · -- an outside query goes to `β`, which must be idle
    have hPx : outsideInputs (hb.map Prod.fst ++ [⟨⟨none, o⟩, u⟩]) =
        outsideInputs (h.map Prod.fst ++ [⟨⟨none, o⟩, u⟩]) := by
      simp [outsideInputs_append, hPb]
    have hst' : (∀ y ∈ (h.map Prod.snd).getLast?, ¬ IsInside y) ∧
        (∀ z ∈ hb.getLast?, ¬ IsInside z.2) ∧ (∀ z ∈ ha.getLast?, ¬ IsInside z.2) := by
      rcases hst with hi | ⟨j, x, m, q, hl, -, hlb, -⟩
      · exact hi
      · exfalso
        rcases hc with hc | hn
        · have ha' := hc.2.1
          rw [converterAdmits_of_query (hwait hl)] at ha'
          cases ha'
        · apply hn
          apply exchange_silent_of_not_dom lx
          rw [serialInjM, pair_left, Part.map_Dom, hKb]
          intro hd
          have ha' := ((hβ.answers hb _ hrb).mp hd).2.1
          rw [converterAdmits_of_query hlb] at ha'
          cases ha'
    obtain ⟨hl, hlb, hla⟩ := hst'
    have hz : converterDomain F G hb ⟨⟨none, o⟩, u⟩ := by
      rcases hc with hc | hn
      · exact ⟨hβ.isDDC.admitted_of_replies hrb, (converterAdmits_of_idle hlb _).mpr rfl,
          hPx ▸ hc.2.2.1, hβ.queries hb hrb⟩
      · apply (hβ.answers hb _ hrb).mp
        by_contra hd
        apply hn
        apply exchange_silent_of_not_dom lx
        rw [serialInjM, pair_left, Part.map_Dom, hKb]
        exact hd
    have hc' : converterDomain E G h ⟨⟨none, o⟩, u⟩ :=
      ⟨hγ.admitted_of_replies hrγ, (converterAdmits_of_idle (hidle hl) _).mpr rfl,
        hPx ▸ hz.2.2.1, hE⟩
    exact ⟨hc', hβ.serial_call hα hc'.2.2.1 lx
      (Or.inl ⟨K, hb, ha, _, rfl, hKb, hrb, hKa, hra, hz, hPx, hR2, hQ, hla⟩)⟩
  · -- an inside reply goes to `α`, which must wait for it
    have hPx : outsideInputs (h.map Prod.fst ++ [⟨⟨some (), o⟩, u⟩]) =
        outsideInputs (h.map Prod.fst) := by
      simp [outsideInputs_append]
    have key : ∃ (x : X o) (m : M) (q : Xm m),
        ha.getLast?.map Prod.snd = some ⟨⟨some (), o⟩, x⟩ ∧
        (h.map Prod.snd).getLast? = some ⟨⟨some (), o⟩, x⟩ ∧
        hb.getLast?.map Prod.snd = some ⟨⟨some (), m⟩, q⟩ ∧
        lastOuter (ha.map Prod.fst) = some m ∧ G (outsideInputs (h.map Prod.fst)) := by
      rcases hst with ⟨hi, -, hia⟩ | ⟨j, x, m, q, hl, hla, hlb, hlo, hG⟩
      · exfalso
        rcases hc with hc | hn
        · have ha' := hc.2.1
          rw [converterAdmits_of_idle (hidle hi)] at ha'
          cases ha'
        · apply hn
          apply exchange_silent_of_not_dom lx
          rw [serialInjM, pair_right, Part.map_Dom, hKa]
          intro hd
          have ha' := ((hα.answers ha _ hra).mp hd).2.1
          rw [converterAdmits_of_idle hia] at ha'
          cases ha'
      · have hj : j = o := by
          rcases hc with hc | hn
          · have ha' := hc.2.1
            rw [converterAdmits_of_query (hwait hl)] at ha'
            cases ha'
            rfl
          · by_contra hne
            apply hn
            apply exchange_silent_of_not_dom lx
            rw [serialInjM, pair_right, Part.map_Dom, hKa]
            intro hd
            have ha' := ((hα.answers ha _ hra).mp hd).2.1
            rw [converterAdmits_of_query hla] at ha'
            cases ha'
            exact hne rfl
        subst hj
        exact ⟨x, m, q, hla, hl, hlb, hlo, hG⟩
    obtain ⟨x, m, q, hla, hl, hlb, hlo, hG⟩ := key
    have hF : F (insideQueries (hb.map Prod.snd)) := by
      rcases hβ.queries hb hrb with he | he
      · exfalso
        obtain ⟨hb, z, rfl⟩ := List.eq_nil_or_concat hb |>.resolve_left (by
          rintro rfl; simp at hlb)
        simp only [List.concat_eq_append, List.getLast?_append, List.getLast?_singleton,
          Option.some_or, Option.map_some, Option.some.injEq] at hlb
        simp [insideQueries_append, hlb] at he
      · exact he
    have hz : converterDomain E F ha ⟨⟨some (), o⟩, u⟩ :=
      ⟨hα.isDDC.admitted_of_replies hra, (converterAdmits_of_query hla _).mpr rfl,
        by simpa [outsideInputs_append, hR2] using hF, hα.queries ha hra⟩
    have hc' : converterDomain E G h ⟨⟨some (), o⟩, u⟩ :=
      ⟨hγ.admitted_of_replies hrγ, (converterAdmits_of_query (hwait hl) _).mpr rfl, hPx ▸ hG, hE⟩
    refine ⟨hc', ?_⟩
    rw [hPx]
    exact hβ.serial_call hα hG lx (Or.inr ⟨K, hb, ha, _, m, q, rfl, hKb, hrb, hKa, hra, hz, hlb,
      by simpa [lastOuter_snoc, outerOf] using hlo, hPb, by simpa [outsideInputs_append] using hR2,
      hQ⟩)

/-- Every completed history of the composite has its components behind it. -/
theorem IsDDCFrom.serial_idle (hβ : IsDDCFrom F G bβ β) (hα : IsDDCFrom E F bα α) :
    ∀ h : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)),
      Replies (serialM β α) (h.map Prod.fst) (h.map Prod.snd) →
      ∃ K, Induces (pair β α) serialRouteM serialInjM (h.map Prod.fst)
          (h.map Prod.snd).getLast? K ∧
        SerialAfter G β α (outsideInputs (h.map Prod.fst)) (insideQueries (h.map Prod.snd))
          (h.map Prod.snd).getLast? K := by
  intro h
  induction h using List.reverseRecOn with
  | nil =>
    intro _
    exact ⟨[], Induces.nil, [], [], rfl, replies_nil _, rfl, replies_nil _, rfl, rfl, rfl,
      Or.inl ⟨by simp, by simp, by simp⟩⟩
  | append_singleton h z ih =>
    intro hr
    rcases z with ⟨x, w⟩
    simp only [List.map_append, List.map_singleton] at hr ⊢
    obtain ⟨hp, hw⟩ := replies_snoc.mp hr
    obtain ⟨K, r, hs⟩ := ih hp
    obtain ⟨K', r'⟩ := mem_interconnect.mp (Part.eq_some_iff.mp hw)
    obtain ⟨o₀, K₀, r₀, lx⟩ := induces_snoc_iff.mp r'
    obtain ⟨-, rfl⟩ := r.det r₀
    obtain ⟨-, w', hw', hs'⟩ := hβ.serial_next hα hp hs x lx (Or.inr (by simp))
    cases hw'
    exact ⟨K', by simpa using r', by simpa using hs'⟩

/-- **Serial composition of DDCs from `E` to `F` and from `F` to `G` is a DDC from `E`
to `G`**, with the product of the inside-query bounds. -/
theorem IsDDCFrom.comp (hβ : IsDDCFrom F G bβ β) (hα : IsDDCFrom E F bα α) :
    IsDDCFrom E G (bα * bβ) (trim (serialM β α)) := by
  refine ⟨hβ.isDDC.comp hα.isDDC, fun h x hr => ?_, fun h hr => ?_⟩
  · rw [replies_trim_iff] at hr
    rw [trim_snoc_of_reach hr.reach]
    obtain ⟨K, r, hs⟩ := hβ.serial_idle hα h hr
    obtain ⟨o', K', r'⟩ := hβ.isDDC.converges_serial α (h.map Prod.fst ++ [x])
    obtain ⟨o₀, K₀, r₀, lx⟩ := induces_snoc_iff.mp r'
    obtain ⟨-, rfl⟩ := r.det r₀
    have hn := hβ.serial_next hα hr hs x lx
    constructor
    · intro hd
      refine (hn (Or.inr ?_)).1
      rintro rfl
      exact not_dom_of_induces_none r' hd
    · intro hc
      obtain ⟨-, w, rfl, -⟩ := hn (Or.inl hc)
      exact Part.dom_iff_mem.mpr ⟨w, mem_of_induces_some r'⟩
  · rw [replies_trim_iff] at hr
    obtain ⟨K, -, hb, ha, -, -, -, hra, -, -, hQ, -⟩ := hβ.serial_idle hα h hr
    rw [← hQ]
    exact hα.queries ha hra

/-- **Two DDCs from `E` to `F` whose transcripts are transcripts of one system have the same
transcripts.** -/
theorem IsDDCFrom.replies_iff_of_le {γ s W : InsideOutsideSystem O M U V Xm Ym} {c b : ℕ}
    (hγ : IsDDCFrom F G c γ) (hs : IsDDCFrom F G b s)
    (hγW : ∀ xs ys, Replies γ xs ys → Replies W xs ys)
    (hsW : ∀ xs ys, Replies s xs ys → Replies W xs ys)
    (h : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l))) :
    Replies γ (h.map Prod.fst) (h.map Prod.snd) ↔ Replies s (h.map Prod.fst) (h.map Prod.snd) := by
  have key : ∀ {γ s : InsideOutsideSystem O M U V Xm Ym} {c b : ℕ}, IsDDCFrom F G c γ →
      IsDDCFrom F G b s → (∀ xs ys, Replies γ xs ys → Replies W xs ys) →
      (∀ xs ys, Replies s xs ys → Replies W xs ys) →
      ∀ h : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)),
        Replies s (h.map Prod.fst) (h.map Prod.snd) → Replies γ (h.map Prod.fst) (h.map Prod.snd) := by
    intro γ s c b hγ hs hγW hsW h hr
    induction h using List.reverseRecOn with
    | nil => exact replies_nil _
    | append_singleton h z ih =>
      rcases z with ⟨x, y⟩
      simp only [List.map_append, List.map_singleton] at hr ⊢
      obtain ⟨hrs, hy⟩ := replies_snoc.mp hr
      have hrγ := ih hrs
      have hd := (hγ.answers h x hrγ).mpr ((hs.answers h x hrs).mp (by rw [hy]; trivial))
      obtain ⟨y', hy'⟩ := Part.dom_iff_mem.mp hd
      have hr' := replies_snoc.mpr ⟨hrγ, Part.eq_some_iff.mpr hy'⟩
      obtain rfl : y' = y := Part.mem_unique
        (Part.eq_some_iff.mp (replies_snoc.mp (hγW _ _ hr')).2)
        (Part.eq_some_iff.mp (replies_snoc.mp (hsW _ _ hr)).2)
      exact hr'
  exact ⟨key hs hγ hsW hγW h, key hγ hs hγW hsW h⟩

/-- Composing with the identity on the inside changes no transcript. -/
theorem IsDDCFrom.replies_serialM_filter (hβ : IsDDCFrom F G bβ β)
    (hF : ¬ F [] ∧ ∀ {p h}, p <+: h → p ≠ [] → F h → F p)
    (h : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l))) :
    Replies (trim (serialM β (DDC.filter (Y := Ym) (fun h => h = [] ∨ F h)
        (prefix_or_nil hF.2)).1)) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies β (h.map Prod.fst) (h.map Prod.snd) := by
  refine (hβ.comp (isDDCFrom_filter hF)).replies_iff_of_le hβ (fun xs ys hr => ?_)
    (fun _ _ hr => hr) h
  rw [replies_trim_iff] at hr
  unfold serialM at hr
  have hsub : ∀ h y, y ∈ (DDC.filter (Y := Ym) (fun h => h = [] ∨ F h)
      (prefix_or_nil hF.2)).1 h → y ∈ idConverter M Xm Ym h :=
    fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
  have hm := hr.interconnect_mono (pair_mono (fun _ _ hy => hy) hsub)
  rw [← IsDDC.trim_serialM_id hβ.isDDC, replies_trim_iff]
  exact hm

/-- Composing with the identity on the outside changes no transcript. -/
theorem IsDDCFrom.replies_filter_serialM (hβ : IsDDCFrom F G bβ β)
    (hG : ¬ G [] ∧ ∀ {p h}, p <+: h → p ≠ [] → G h → G p)
    (h : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l))) :
    Replies (trim (serialM (DDC.filter (Y := V) (fun h => h = [] ∨ G h)
        (prefix_or_nil hG.2)).1 β)) (h.map Prod.fst) (h.map Prod.snd) ↔
      Replies β (h.map Prod.fst) (h.map Prod.snd) := by
  refine ((isDDCFrom_filter hG).comp hβ).replies_iff_of_le hβ (fun xs ys hr => ?_)
    (fun _ _ hr => hr) h
  rw [replies_trim_iff] at hr
  unfold serialM at hr
  have hsub : ∀ h y, y ∈ (DDC.filter (Y := V) (fun h => h = [] ∨ G h)
      (prefix_or_nil hG.2)).1 h → y ∈ idConverter O U V h :=
    fun h y hy => ((filterDom_mem_iff _ _ h y).mp hy).2
  have hm := hr.interconnect_mono (pair_mono hsub (fun _ _ hy => hy))
  rw [← IsDDC.trim_id_serialM hβ.isDDC, replies_trim_iff]
  exact hm

end Serial

end SystemAlgebra

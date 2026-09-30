import RandomSystems.Converter.Identity

/-!
# Attaching a converter to a resource

A converter is attached to a resource by connecting all of its inside interfaces to
the resource; its outside interfaces remain exposed. Attachment converges for DDCs,
attaching a serial composition attaches the inner converter first, and the identity
leaves a resource unchanged. A converter maps the domain `E` to the domain `F` when
its attachment to every resource with domain `E` has domain `F`. Source: CR18,
Definition 3.9 (printed p. 62).

## Main definitions

* `apply α R`, `DDC.attach`: attachment
* `MapsDomain E F α`: attachment maps resources with domain `E` to resources with
  domain `F`

## Main results

* `IsDDC.converges_resource`: attaching a DDC converges
* `IsDDC.trim_apply_serialM`: serial attachment
* `trim_apply_id`: the identity leaves a resource unchanged
* `MapsDomain.comp`, `MapsDomain.admits`: domain maps compose, and give the exact
  next-query admission
-/

namespace SystemAlgebra

open Classical

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}

def resourceRoute : Two (Σ l, twoFam V X l) (Σ j, Y j) →
    (Σ o, V o) ⊕ Two (Σ l, twoFam U Y l) (Σ j, X j)
  | ⟨none, ⟨⟨none, o⟩, v⟩⟩ => .inl ⟨o, v⟩
  | ⟨none, ⟨⟨some (), j⟩, x⟩⟩ => .inr ⟨some (), ⟨j, x⟩⟩
  | ⟨some (), ⟨j, y⟩⟩ => .inr ⟨none, ⟨⟨some (), j⟩, y⟩⟩

def resourceInput (u : Σ o, U o) : Two (Σ l, twoFam U Y l) (Σ j, X j) :=
  ⟨none, ⟨⟨none, u.1⟩, u.2⟩⟩

def allOutsideInput (u : Σ o, U o) :
    Σ l : Free (alongSet (O := O) (id : J → J)), twoFam (twoFam U (Y ∘ id)) X l.1 :=
  ⟨⟨⟨none, ⟨none, u.1⟩⟩, outside_not_mem_alongSet id u.1⟩, u.2⟩

def allOutsideOutput :
    (Σ l : Free (alongSet (O := O) (id : J → J)), twoFam (twoFam V (X ∘ id)) Y l.1) → Σ o, V o
  | ⟨⟨⟨none, ⟨none, o⟩⟩, _⟩, v⟩ => ⟨o, v⟩
  | ⟨⟨⟨none, ⟨some (), _⟩⟩, h⟩, _⟩ => False.elim (h trivial)
  | ⟨⟨⟨some (), j⟩, h⟩, _⟩ => False.elim (h ⟨j, rfl⟩)

/-- The system obtained by attaching all the converter's inside interfaces. -/
noncomputable def apply (α : InsideOutsideSystem O J U V X Y) (R : InterfaceSystem J X Y) : InterfaceSystem O U V :=
  relabel (attachAlong id α R) allOutsideInput allOutsideOutput

theorem apply_eq (α : InsideOutsideSystem O J U V X Y) (R : InterfaceSystem J X Y) :
    apply α R = interconnect (pair α R) resourceRoute resourceInput := by
  rw [apply, attachAlong_eq, relabel_interconnect]
  congr 1
  funext y
  rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
  · rcases y with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩
    · rw [alongRoute_outer]; rfl
    · rw [alongRoute_inside]; rfl
  · rcases y with ⟨j, y⟩
    exact congrArg (Sum.map allOutsideOutput id)
      (alongRoute_image (U := U) (V := V) id Function.injective_id j y)

theorem cyclesThrough_resource :
    CyclesThrough (IsInside (F := twoFam V X)) (resourceRoute (U := U) (Y := Y)) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩ hy
    · exact ⟨_, rfl⟩
    · exact absurd rfl hy
  · rintro ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩ hy
    · exact absurd hy (by simp [IsInside])
    · exact Or.inr ⟨_, rfl⟩
  · rintro ⟨j, y⟩
    exact Or.inr ⟨_, rfl⟩

theorem IsDDC.converges_resource {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsDDC b α) (R : InterfaceSystem J X Y) :
    Converges (pair α R) resourceRoute resourceInput :=
  converges_pair cyclesThrough_resource hα.bound

theorem IsResponsiveDDC.converges_resource {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α) (R : InterfaceSystem J X Y) :
    Converges (pair α R) resourceRoute resourceInput :=
  hα.isDDC.converges_resource R

/-- Regrouping connects the same three histories, including undefined behavior. -/
theorem IsDDC.apply_serialM {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsDDC bβ β) (hα : IsDDC bα α)
    (R : InterfaceSystem J X Y) : apply (serialM β α) R = apply β (apply α R) := by
  simp only [apply_eq, serialM]
  rw [pair_interconnect_left (hβ.converges_serial α), interconnect_interconnect,
    pair_interconnect_right β (hα.converges_resource R), interconnect_interconnect,
    pair_assoc', interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩
    · rcases y with ⟨_ | ⟨⟨⟩⟩, y⟩ <;>
        rcases y with ⟨⟨_ | ⟨⟨⟩⟩, i⟩, y⟩ <;> rfl
    · rcases y with ⟨j, y⟩; rfl

theorem apply_serialM {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α)
    (R : InterfaceSystem J X Y) : apply (serialM β α) R = apply β (apply α R) :=
  IsDDC.apply_serialM hβ.isDDC hα.isDDC R

theorem EqOnReachable.apply {α α' : InsideOutsideSystem O J U V X Y} {R R' : InterfaceSystem J X Y}
    (hα : α ≈ₛ α') (hR : R ≈ₛ R') : apply α R ≈ₛ apply α' R' := by
  rw [apply_eq, apply_eq]
  apply EqOnReachable.interconnect
  exact EqOnReachable.parAll (fun i => by cases i with
    | none => exact hα
    | some _ => exact hR)

/-- The serial resource equation on canonical partial systems. -/
theorem IsDDC.trim_apply_serialM {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsDDC bβ β) (hα : IsDDC bα α)
    (R : InterfaceSystem J X Y) :
    trim (apply (trim (serialM β α)) R) =
      trim (apply β (trim (apply α R))) := by
  have hl := (trim_behEq (serialM β α)).apply (EqOnReachable.rfl' R)
  have hr := (EqOnReachable.rfl' β).apply (trim_behEq (apply α R))
  rw [IsDDC.apply_serialM hβ hα R] at hl
  exact (hl.trans hr.symm).trim_eq
    (by simp [SilentAtEmpty, apply_eq]) (by simp [SilentAtEmpty, apply_eq])

theorem trim_apply_serialM {bβ bα : ℕ} {β : InsideOutsideSystem O M U V Xm Ym}
    {α : InsideOutsideSystem M J Xm Ym X Y} (hβ : IsResponsiveDDC bβ β) (hα : IsResponsiveDDC bα α)
    (R : InterfaceSystem J X Y) :
    trim (apply (trim (serialM β α)) R) =
      trim (apply β (trim (apply α R))) :=
  IsDDC.trim_apply_serialM hβ.isDDC hα.isDDC R

namespace DDC

/-- Attach the existing systems and keep their completed input histories.
The result is a DDS even when either component can stop. -/
noncomputable def attach (α : DDC O J U V X Y)
    (R : DDS (Σ j, X j) (Σ j, Y j)) : DDS (Σ o, U o) (Σ o, V o) :=
  ⟨trim (apply α.1 R.1),
    SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq])⟩

/-- Serial attachment on partial DDSs is the general system regrouping equation. -/
theorem comp_attach (β : DDC O M U V Xm Ym) (α : DDC M J Xm Ym X Y)
    (R : DDS (Σ j, X j) (Σ j, Y j)) :
    attach (comp β α) R = attach β (attach α R) := by
  apply Subtype.ext
  obtain ⟨bβ, hβ⟩ := β.2
  obtain ⟨bα, hα⟩ := α.2
  exact IsDDC.trim_apply_serialM hβ hα R.1

end DDC

/-- One identity exchange forwards the query and reply at the same interface. -/
theorem idConverter_call {h : List (Σ l, twoFam X Y l)}
    (hi : Idle (idConverter J X Y) h) (j : J) (x : X j) (y : Y j) :
    idConverter J X Y (h ++ [⟨⟨none, j⟩, x⟩]) = Part.some ⟨⟨some (), j⟩, x⟩ ∧
    idConverter J X Y (h ++ [⟨⟨none, j⟩, x⟩, ⟨⟨some (), j⟩, y⟩]) =
      Part.some ⟨⟨none, j⟩, y⟩ ∧
    Idle (idConverter J X Y) (h ++ [⟨⟨none, j⟩, x⟩, ⟨⟨some (), j⟩, y⟩]) := by
  have ha : Admissible (idConverter J X Y) (h ++ [⟨⟨none, j⟩, x⟩]) :=
    admissible_snoc.mpr ⟨hi.1, hi.2.1, (admitAfter_of_ne hi.2.2).mpr rfl⟩
  have hx : idConverter J X Y (h ++ [⟨⟨none, j⟩, x⟩]) =
      Part.some ⟨⟨some (), j⟩, x⟩ := by
    rw [idConverter, canon_of_admissible ((admissible_canon_iff _).mp ha)]
    exact forwardAll_snoc_outer h j x
  have ha' : Admissible (idConverter J X Y)
      ((h ++ [⟨⟨none, j⟩, x⟩]) ++ [⟨⟨some (), j⟩, y⟩]) := by
    apply admissible_snoc.mpr
    refine ⟨ha, fun _ => by rw [hx]; trivial, ?_⟩
    simp [Admits, replyLabel_of_mem _ (Part.eq_some_iff.mp hx), admitAfter]
  have hy : idConverter J X Y ((h ++ [⟨⟨none, j⟩, x⟩]) ++ [⟨⟨some (), j⟩, y⟩]) =
      Part.some ⟨⟨none, j⟩, y⟩ := by
    rw [idConverter, canon_of_admissible ((admissible_canon_iff _).mp ha')]
    exact forwardAll_snoc_inner _ j y
  refine ⟨hx, by simpa only [List.append_assoc, List.singleton_append] using hy, ?_⟩
  have hif : Idle (idConverter J X Y)
      ((h ++ [⟨⟨none, j⟩, x⟩]) ++ [⟨⟨some (), j⟩, y⟩]) :=
    ⟨ha', fun _ => by rw [hy]; trivial,
      fun k => by rw [replyLabel_of_mem _ (Part.eq_some_iff.mp hy)]; simp⟩
  simpa only [List.append_assoc, List.singleton_append] using hif

/-- Every completed resource history is forwarded by the canonical identity. -/
theorem replies_apply_id {R : InterfaceSystem J X Y} (hR : RepliesAtQueriedInterface R)
    {xs ys} (hr : Replies R xs ys) : Replies (apply (idConverter J X Y) R) xs ys := by
  have key : ∀ xs ys, Replies R xs ys → ∃ o H,
      Induces (pair (idConverter J X Y) R) resourceRoute resourceInput xs o H ∧
      restrict (some ()) H = xs ∧ Idle (idConverter J X Y) (restrict none H) ∧
      (∀ y, ys.getLast? = some y → o = some y) := by
    intro xs
    induction xs using List.reverseRecOn with
    | nil =>
      intro ys hr
      have hy : ys = [] := List.length_eq_zero_iff.mp hr.length
      subst ys
      exact ⟨none, [], Induces.nil, rfl, ⟨admissible_nil, by simp,
        fun j => by simp [replyLabel, idConverter, canon, forwardAll]⟩,
        by simp⟩
    | append_singleton xs a ih =>
      intro ys hr
      have hn : ys ≠ [] := by intro hz; simpa [hz] using hr.length
      obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left hn
      rw [List.concat_eq_append] at hr ⊢
      obtain ⟨hp, hy⟩ := replies_snoc.mp hr
      obtain ⟨o, H, hi, hH, hid, _⟩ := ih ys hp
      rcases a with ⟨j, x⟩
      rcases y with ⟨j', y⟩
      have hj : j' = j := hR xs ⟨j, x⟩ ⟨j', y⟩ (Part.eq_some_iff.mp hy)
      subst j'
      obtain ⟨hx, hy', hid'⟩ := idConverter_call hid j x y
      let H₁ := H ++ [resourceInput (Y := Y) ⟨j, x⟩]
      let H₂ := H₁ ++ [⟨some (), ⟨j, x⟩⟩]
      let H₃ := H₂ ++ [⟨none, ⟨⟨some (), j⟩, y⟩⟩]
      have hq : (⟨none, ⟨⟨some (), j⟩, x⟩⟩ : Two _ (Σ j, Y j)) ∈
          pair (idConverter J X Y) R H₁ := by
        dsimp only [H₁]
        rw [resourceInput, pair_left, hx]
        exact Part.mem_map _ (Part.mem_some _)
      have ha : (⟨some (), ⟨j, y⟩⟩ : Two (Σ l, twoFam Y X l) _) ∈
          pair (idConverter J X Y) R H₂ := by
        dsimp only [H₂]
        rw [pair_right]
        simp only [H₁, resourceInput, restrict_some_snoc_left, hH, hy]
        exact Part.mem_map _ (Part.mem_some _)
      have hv : (⟨none, ⟨⟨none, j⟩, y⟩⟩ : Two _ (Σ j, Y j)) ∈
          pair (idConverter J X Y) R H₃ := by
        dsimp only [H₃]
        rw [pair_left]
        simp only [H₂, H₁, resourceInput, restrict_none_snoc_right, restrict_none_snoc_left]
        rw [List.append_assoc, List.singleton_append, hy']
        exact Part.mem_map _ (Part.mem_some _)
      refine ⟨some ⟨j, y⟩, H₃, Induces.snoc _ _ _ _ _ _ hi
        (Exchange.feed _ _ _ _ _ hq rfl (Exchange.feed _ _ _ _ _ ha rfl
          (Exchange.out _ _ _ hv rfl))), ?_, ?_, ?_⟩
      · simp [H₃, H₂, H₁, resourceInput, hH]
      · simpa [H₃, H₂, H₁, resourceInput, List.append_assoc] using hid'
      · intro z hz
        simpa using hz
  rw [apply_eq]
  refine ⟨hr.length, fun k hk hj => ?_⟩
  have hp : Replies R (xs.take (k + 1)) (ys.take (k + 1)) := by
    refine ⟨by simp [hr.length], fun i hi hi' => ?_⟩
    simp only [List.length_take] at hi hi'
    have hik : i + 1 ≤ k + 1 := by omega
    simpa only [List.take_take, Nat.min_eq_left hik, List.getElem_take] using
      hr.2 i (by omega) (by omega)
  obtain ⟨o, H, hi, _, _, ho⟩ := key _ _ hp
  have hl : (ys.take (k + 1)).getLast? = some ys[k] := by
    have he : ys.take (k + 1) = ys.take k ++ [ys[k]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
    rw [he, List.getLast?_append]
    rfl
  rw [ho _ hl] at hi
  exact Part.eq_some_iff.mpr (mem_interconnect.mpr ⟨H, hi⟩)

theorem apply_forwardAll {R : InterfaceSystem J X Y} (hR : SilentAtEmpty R) :
    apply (forwardAll J X Y) R = R := by
  rw [apply_eq, pair_swap, interconnect_relabel,
    interconnect_forwarder hR forwardAll_heterogeneous (f := id) (g := id), relabel_id]
  constructor
  · rintro ⟨j, x⟩; exact Or.inr ⟨_, rfl, rfl⟩
  · rintro ⟨j, y⟩; exact Or.inr ⟨_, rfl, rfl⟩

/-- Identity on a partial responding DDS, with its domain unchanged. -/
theorem trim_apply_id {R : InterfaceSystem J X Y} (hR : IsDDS R) (hresp : RepliesAtQueriedInterface R) :
    trim (apply (idConverter J X Y) R) = R := by
  apply IsDDS.eq_of_replies_iff
    (SilentAtEmpty.isDDS_trim (s := apply (idConverter J X Y) R)
      (by simp [SilentAtEmpty, apply_eq])) hR
  intro xs ys
  rw [replies_trim_iff]
  constructor
  · intro hr
    rw [apply_eq] at hr
    have ht := hr.interconnect_mono (pair_mono (fun _ _ h => canon_mem h) (fun _ _ h => h))
    change Replies (interconnect (pair (forwardAll J X Y) R) resourceRoute resourceInput) xs ys at ht
    rwa [← apply_eq, apply_forwardAll hR.1] at ht
  · exact replies_apply_id hresp

/-- A converter acts between the stated resource domains when its attachment
preserves exactly that domain and the responding interface. This restricts the
arrows, not the behavior of any attached system. -/
def MapsDomain (E : List (Σ j, X j) → Prop) (F : List (Σ o, U o) → Prop)
    (α : InsideOutsideSystem O J U V X Y) : Prop :=
  ∀ R : InterfaceSystem J X Y, IsDDS R → RepliesAtQueriedInterface R → (∀ h, (R h).Dom ↔ E h) →
    RepliesAtQueriedInterface (trim (apply α R)) ∧ ∀ h, (trim (apply α R) h).Dom ↔ F h

/-- Identity acts on every partial resource domain. -/
theorem idConverter_mapsDomain (E : List (Σ j, X j) → Prop) :
    MapsDomain E E (idConverter J X Y) := by
  intro R hR hresp hE
  rw [trim_apply_id hR hresp]
  exact ⟨hresp, hE⟩

/-- Domain preservation composes because attachment itself satisfies the
serial equation. The intermediate system is the actual canonical attachment. -/
theorem MapsDomain.comp
    {E : List (Σ j, X j) → Prop} {F : List (Σ m, Xm m) → Prop}
    {G : List (Σ o, U o) → Prop} {bβ bα : ℕ}
    {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
    (hβ : IsDDC bβ β) (hα : IsDDC bα α)
    (hβD : MapsDomain F G β) (hαD : MapsDomain E F α) :
    MapsDomain E G (trim (serialM β α)) := by
  intro R hR hresp hE
  obtain ⟨hSresp, hF⟩ := hαD R hR hresp hE
  have hS : IsDDS (trim (apply α R)) :=
    SilentAtEmpty.isDDS_trim (by simp [SilentAtEmpty, apply_eq])
  simpa only [IsDDC.trim_apply_serialM hβ hα R] using
    hβD (trim (apply α R)) hS hSresp hF

/-- Domain preservation gives the exact next-query condition required by the
cumulative connection constructor. -/
theorem MapsDomain.admits {E : List (Σ j, X j) → Prop}
    {F : List (Σ o, U o) → Prop} {α : InsideOutsideSystem O J U V X Y}
    (hα : MapsDomain E F α) {R : InterfaceSystem J X Y}
    (hR : IsDDS R) (hresp : RepliesAtQueriedInterface R) (hE : ∀ h, (R h).Dom ↔ E h)
    (h : List ((Σ o, U o) × (Σ o, V o))) (x : Σ o, U o)
    (hr : Replies (apply α R) (h.map Prod.fst) (h.map Prod.snd)) :
    (apply α R (h.map Prod.fst ++ [x])).Dom ↔ F (h.map Prod.fst ++ [x]) := by
  rw [← trim_snoc_of_reach hr.reach]
  exact (hα R hR hresp hE).2 _

/-- The left component is read only at prefixes of its own retained history. -/
theorem pair_eq_on_prefixes_left {A B C D : Type} {s t : System A B} (R : System C D)
    {H : List (Two A C)} (he : ∀ p, p <+: restrict none H → s p = t p) :
    ∀ G, G <+: H → pair s R G = pair t R G := by
  intro G hG
  rcases List.eq_nil_or_concat G with rfl | ⟨G, ⟨_ | ⟨⟨⟩⟩, x⟩, rfl⟩
  · rfl
  · simp only [List.concat_eq_append] at hG ⊢
    have hp := restrict_prefix none hG
    simp only [restrict_none_snoc_left] at hp
    rw [pair_left, pair_left, he _ hp]
  · simp only [List.concat_eq_append, pair_right]

/-- Domain preservation depends only on finite converter behavior. This is
the closure principle used when lifting to fresh converters. -/
theorem IsResponsiveDDC.mapsDomain_of_replies {E : List (Σ j, X j) → Prop}
    {F : List (Σ o, U o) → Prop} {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    (hα : IsResponsiveDDC b α)
    (ha : ∀ xs ys, Replies α xs ys → ∃ (c : ℕ) (β : InsideOutsideSystem O J U V X Y),
      IsResponsiveDDC c β ∧ MapsDomain E F β ∧ Replies β xs ys) :
    MapsDomain E F α := by
  intro R hR hresp hE
  have local_eq (h : List (Σ o, U o)) : ∃ β : InsideOutsideSystem O J U V X Y,
      MapsDomain E F β ∧ trim (apply α R) h = trim (apply β R) h := by
    obtain ⟨o, H, hr⟩ := hα.converges_resource R h
    obtain ⟨xs, ys, _, ht, he⟩ := hα.exists_prefix_test (restrict none H)
    obtain ⟨c, β, hβ, hβD, hb⟩ := ha xs ys ht
    refine ⟨β, hβD, ?_⟩
    simp only [apply_eq]
    exact trim_eq_of_prefix_eq
      (hr.interconnect_eq_on_prefixes (pair_eq_on_prefixes_left R (he hβ hb)))
  constructor
  · intro h x y hy
    obtain ⟨β, hβ, he⟩ := local_eq (h ++ [x])
    rw [he] at hy
    exact (hβ R hR hresp hE).1 h x y hy
  · intro h
    obtain ⟨β, hβ, he⟩ := local_eq h
    rw [he]
    exact (hβ R hR hresp hE).2 h

end SystemAlgebra

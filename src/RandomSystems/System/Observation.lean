import RandomSystems.System.InterfaceSystem

/-!
# Decisions of distinguishers

The decision of a distinguisher `D` closed with a system `R`, `D ▹ R`, is read off
the transcripts of `R` with `D`.

## Main definitions

* `envOf D`: the queries of a distinguisher as an environment
* `Compatible D R`: `D` asks only what `R` answers
* `RepliesAtQueriedInterface R`: `R` replies at the label it was queried at
* `probe h P`: the distinguisher that asks the queries `h` and tests the replies
* `swapper`, `mute`: two systems that no distinguisher tells apart

## Main results

* `close_decision`: the decision is determined by the transcript
* `close_dom_iff_compatible`: for finite `D`, the decision is defined iff `D` is
  compatible with `R`
* `behEq_iff_decision`, `behEq_iff_transcript_DDD`: on systems replying at the
  queried label, `≈` is equality of all decisions and of all transcripts
* `dde_blind_beyond_resources`: without that condition, distinguishers observe
  less than `≈`
-/

set_option linter.unusedSimpArgs false

namespace SystemAlgebra

open Classical

section Decision

variable {I : Type} {X Y : I → Type}

/-- A reply of the system, read as an input of the environment. -/
def envIn (y : Σ i, Y i) : Σ p, dIn Y p := ⟨.res y.1, y.2⟩

theorem envIn_injective : Function.Injective (envIn (Y := Y)) := by
  rintro ⟨i, y⟩ ⟨i', y'⟩ h
  simp only [envIn, Sigma.mk.injEq, DPort.res.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

/-- The history of the environment after the replies `ys`. -/
def dHist (ys : List (Σ i, Y i)) : List (Σ p, dIn Y p) := ⟨.start, ()⟩ :: ys.map envIn

/-- An output of the environment, read as a query to the system. -/
def query : (Σ p, dOut X p) → Option (Σ i, X i)
  | ⟨.res i, x⟩ => some ⟨i, x⟩
  | _ => none

/-- The environment `D` as a query function `Y* ⇀ X` on the system's side. -/
noncomputable def envOf (D : DDD I X Y) : List (Σ i, Y i) →. Σ i, X i :=
  fun ys => (D (dHist ys)).bind fun o => (query o : Part _)

theorem mem_envOf {D : DDD I X Y} {ys x} : x ∈ envOf D ys ↔ ⟨.res x.1, x.2⟩ ∈ D (dHist ys) := by
  constructor
  · intro h
    obtain ⟨o, ho, hq⟩ := Part.mem_bind_iff.mp h
    rcases o with ⟨_ | _ | i, v⟩
    · exact v.elim
    · simp [query] at hq
    · simp only [query] at hq
      obtain ⟨_, rfl⟩ := hq
      exact ho
  · intro h
    exact Part.mem_bind_iff.mpr ⟨_, h, by simp [query]⟩

/-- The routing of `D ▹ R` on `[D, R]`. -/
def closeRoute : Two (Σ p, dOut X p) (Σ i, Y i) →
    (Σ l : Free (closeSet I), twoFam (dOut X) Y l.1) ⊕ Two (Σ p, dIn Y p) (Σ i, X i)
  | ⟨none, ⟨.start, e⟩⟩ => e.elim
  | ⟨none, ⟨.dec, b⟩⟩ => .inl ⟨⟨⟨none, .dec⟩, dec_not_mem_closeSet⟩, b⟩
  | ⟨none, ⟨.res i, x⟩⟩ => .inr ⟨some (), ⟨i, x⟩⟩
  | ⟨some (), ⟨i, y⟩⟩ => .inr ⟨none, ⟨.res i, y⟩⟩

/-- External inputs of `D ▹ R` go to `D`. -/
def closeInj : (Σ l : Free (closeSet I), twoFam (dIn Y) X l.1) → Two (Σ p, dIn Y p) (Σ i, X i)
  | ⟨⟨⟨none, .start⟩, _⟩, u⟩ => ⟨none, ⟨.start, u⟩⟩
  | ⟨⟨⟨none, .dec⟩, _⟩, e⟩ => e.elim
  | ⟨⟨⟨none, .res i⟩, h⟩, _⟩ => absurd (res_mem_closeSet i) h
  | ⟨⟨⟨some (), i⟩, h⟩, _⟩ => absurd (sys_mem_closeSet i) h

theorem close_eq (D : DDD I X Y) (R : InterfaceSystem I X Y) :
    close D R = interconnect (pair D R) closeRoute closeInj := by
  unfold close connect pairI
  rw [interconnect_relabel]
  congr 1
  · funext o
    rcases o with ⟨_ | ⟨⟨⟩⟩, o⟩
    · rcases o with ⟨_ | _ | i, v⟩
      · exact v.elim
      · simp [connectRoute_of_not_mem, dec_not_mem_closeSet, joinOut, closeRoute]
      · simp [connectRoute_of_mem, res_mem_closeSet, liftC_closeRouting_res, joinOut, splitIn,
          closeRoute]
    · rcases o with ⟨i, y⟩
      simp [connectRoute_of_mem, sys_mem_closeSet, liftC_closeRouting_sys, joinOut, splitIn,
        closeRoute]
  · funext l
    rcases l with ⟨⟨⟨_ | ⟨⟨⟩⟩, z⟩, hz⟩, v⟩
    · rcases z with _ | _ | i
      · rfl
      · exact v.elim
      · exact absurd (res_mem_closeSet i) hz
    · exact absurd (sys_mem_closeSet z) hz

/-- The trigger. -/
def startIn : Σ l : Free (closeSet I), twoFam (dIn Y) X l.1 :=
  ⟨⟨⟨none, .start⟩, start_not_mem_closeSet⟩, ()⟩

/-- The decision `b`, as an output of `D ▹ R`. -/
def decOut (b : Bool) : Σ l : Free (closeSet I), twoFam (dOut X) Y l.1 :=
  ⟨⟨⟨none, .dec⟩, dec_not_mem_closeSet⟩, b⟩

/-- Every output of `D ▹ R` is a decision. -/
theorem eq_decOut (z : Σ l : Free (closeSet I), twoFam (dOut X) Y l.1) : ∃ b, z = decOut b := by
  rcases z with ⟨⟨⟨_ | ⟨⟨⟩⟩, l⟩, hl⟩, v⟩
  · rcases l with _ | _ | i
    · exact v.elim
    · exact ⟨v, rfl⟩
    · exact absurd (res_mem_closeSet i) hl
  · exact absurd (sys_mem_closeSet l) hl

theorem decOut_injective : Function.Injective (decOut (X := X) (Y := Y)) := by
  intro b b' h
  simpa [decOut] using h

/-! ### The internal history of `[D, R]` along a transcript -/

/-- Queries `xs` and replies `ys`, interleaved as inputs of `[D, R]`. -/
def inter : List (Σ i, X i) → List (Σ i, Y i) → List (Two (Σ p, dIn Y p) (Σ i, X i))
  | x :: xs, y :: ys => ⟨some (), x⟩ :: ⟨none, envIn y⟩ :: inter xs ys
  | _, _ => []

/-- The internal history of `D ▹ R` after the trigger, the queries `xs` and the replies `ys`. -/
def hist (xs : List (Σ i, X i)) (ys : List (Σ i, Y i)) : List (Two (Σ p, dIn Y p) (Σ i, X i)) :=
  ⟨none, ⟨.start, ()⟩⟩ :: inter xs ys

theorem inter_snoc {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)} (hl : xs.length = ys.length)
    (x : Σ i, X i) (y : Σ i, Y i) :
    inter (xs ++ [x]) (ys ++ [y]) = inter xs ys ++ [⟨some (), x⟩, ⟨none, envIn y⟩] := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => simp at hl
  | cons x' xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y' ys => simp [inter, ih (by simpa using hl)]

theorem hist_snoc {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)} (hl : xs.length = ys.length)
    (x : Σ i, X i) (y : Σ i, Y i) :
    hist (xs ++ [x]) (ys ++ [y]) = hist xs ys ++ [⟨some (), x⟩] ++ [⟨none, envIn y⟩] := by
  simp [hist, inter_snoc hl]

theorem restrict_none_inter {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)}
    (hl : xs.length = ys.length) : restrict none (inter xs ys) = ys.map envIn := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons => simp at hl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      rw [inter, restrict_cons_ne (k := (none : Option Unit)) (k' := some ()) (by simp),
        restrict_cons_self, ih (by simpa using hl)]
      rfl

theorem restrict_some_inter {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)}
    (hl : xs.length = ys.length) : restrict (some ()) (inter xs ys) = xs := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
    cases ys with
    | nil => simp at hl
    | cons y ys =>
      rw [inter, restrict_cons_self, restrict_cons_ne (k := some ()) (k' := (none : Option Unit)) (by simp),
        ih (by simpa using hl)]

theorem restrict_none_hist {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)}
    (hl : xs.length = ys.length) : restrict none (hist xs ys) = dHist ys := by
  simp [hist, dHist, restrict_none_inter hl]

theorem restrict_some_hist {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)}
    (hl : xs.length = ys.length) : restrict (some ()) (hist xs ys) = xs := by
  simp [hist, restrict_some_inter hl]

theorem hist_last {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)} (hl : xs.length = ys.length) :
    ∃ G a, hist xs ys = G ++ [⟨none, a⟩] := by
  rcases List.eq_nil_or_concat xs with rfl | ⟨xs', x, rfl⟩
  · cases ys with
    | nil => exact ⟨[], _, rfl⟩
    | cons => simp at hl
  · rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
    · simp at hl
    · rw [List.concat_eq_append, List.concat_eq_append]
      exact ⟨_, _, hist_snoc (by simpa using hl) x y⟩

variable {D : DDD I X Y} {R : InterfaceSystem I X Y}

theorem pair_hist {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)} (hl : xs.length = ys.length) :
    pair D R (hist xs ys) = (D (dHist ys)).map (Sigma.mk none) := by
  obtain ⟨G, a, e⟩ := hist_last hl
  have hr := restrict_none_hist (Y := Y) hl
  rw [e] at hr ⊢
  rw [pair_left]
  simp only [restrict_append, restrict_two_none_cons_none, restrict_nil] at hr
  rw [hr]

theorem pair_hist_query {xs : List (Σ i, X i)} {ys : List (Σ i, Y i)}
    (hl : xs.length = ys.length) (x : Σ i, X i) :
    pair D R (hist xs ys ++ [⟨some (), x⟩]) = (R (xs ++ [x])).map (Sigma.mk (some ())) := by
  rw [pair_right, restrict_some_hist hl]

/-! ### The decision is read off the transcript -/

/-- Along an exchange of `D ▹ R` that starts on a transcript, a decision is a decision
of `D` at the end of a longer transcript. -/
theorem close_exchange {G o G'} (l : Exchange (pair D R) closeRoute G o G') :
    ∀ b, o = some (decOut b) → ∀ xs ys, Transcript R (envOf D) xs ys →
      (G = hist xs ys ∨ ∃ x, x ∈ envOf D ys ∧ G = hist xs ys ++ [⟨some (), x⟩]) →
      ∃ xs' ys', Transcript R (envOf D) xs' ys' ∧ ⟨.dec, b⟩ ∈ D (dHist ys') := by
  induction l with
  | silent => intro b e; cases e
  | out G y c hy hr =>
    intro b e xs ys tr hG
    obtain rfl : c = decOut b := Option.some_inj.mp e
    have hl := tr.length_eq
    rcases hG with rfl | ⟨x, -, rfl⟩
    · rw [pair_hist hl] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨_ | _ | i, v⟩
      · exact v.elim
      · simp only [closeRoute, Sum.inl.injEq] at hr
        obtain rfl := decOut_injective hr
        exact ⟨xs, ys, tr, hy'⟩
      · simp [closeRoute] at hr
    · rw [pair_hist_query hl] at hy
      obtain ⟨y', -, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      simp [closeRoute] at hr
  | feed G y x o G'' hy hr _ ih =>
    intro b e xs ys tr hG
    have hl := tr.length_eq
    rcases hG with rfl | ⟨x₀, hx₀, rfl⟩
    · rw [pair_hist hl] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      rcases y' with ⟨_ | _ | i, v⟩
      · exact v.elim
      · simp [closeRoute] at hr
      · simp only [closeRoute, Sum.inr.injEq] at hr
        subst hr
        exact ih b e xs ys tr (Or.inr ⟨⟨i, v⟩, mem_envOf.mpr hy', rfl⟩)
    · rw [pair_hist_query hl] at hy
      obtain ⟨y', hy', rfl⟩ := Part.mem_map_iff _ |>.mp hy
      simp only [closeRoute, Sum.inr.injEq] at hr
      subst hr
      refine ih b e _ _ (Transcript.snoc tr hx₀ hy') (Or.inl ?_)
      rw [hist_snoc hl]
      rfl

/-- An exchange from a later point of a transcript is an exchange from its start. -/
theorem exchange_of_transcript {xs ys} (tr : Transcript R (envOf D) xs ys) :
    ∀ {o G'}, Exchange (pair D R) closeRoute (hist xs ys) o G' →
      Exchange (pair D R) closeRoute (hist [] []) o G' := by
  induction tr with
  | nil => exact id
  | @snoc xs ys x y tr hx hy ih =>
    intro o G' l
    have hl := tr.length_eq
    rw [hist_snoc hl] at l
    apply ih
    refine Exchange.feed _ ⟨none, ⟨.res x.1, x.2⟩⟩ ⟨some (), x⟩ _ _ ?_ rfl ?_
    · rw [pair_hist hl]; exact Part.mem_map _ (mem_envOf.mp hx)
    · refine Exchange.feed _ ⟨some (), y⟩ ⟨none, envIn y⟩ _ _ ?_ rfl l
      rw [pair_hist_query hl]; exact Part.mem_map _ hy

theorem induces_start {o H} :
    Induces (pair D R) closeRoute closeInj [startIn] o H ↔
      Exchange (pair D R) closeRoute (hist [] []) o H := by
  rw [show ([startIn] : List (Σ l : Free (closeSet I), twoFam (dIn Y) X l.1)) = [] ++ [startIn]
    from rfl, induces_snoc_iff]
  constructor
  · rintro ⟨_, H₀, r, l⟩
    obtain ⟨-, rfl⟩ := induces_nil_iff.mp r
    exact l
  · intro l
    exact ⟨none, [], Induces.nil, l⟩

/-- **The decision of `D ▹ R`** is the decision of `D` at the end of a transcript of `R`
with `D`. -/
theorem close_decision (b : Bool) :
    decOut b ∈ close D R [startIn] ↔
      ∃ xs ys, Transcript R (envOf D) xs ys ∧ ⟨.dec, b⟩ ∈ D (dHist ys) := by
  rw [close_eq, mem_interconnect]
  constructor
  · rintro ⟨H, r⟩
    exact close_exchange (induces_start.mp r) b rfl [] [] Transcript.nil (Or.inl rfl)
  · rintro ⟨xs, ys, tr, hd⟩
    refine ⟨_, induces_start.mpr (exchange_of_transcript tr (Exchange.out _ ⟨none, ⟨.dec, b⟩⟩ _ ?_ rfl))⟩
    rw [pair_hist tr.length_eq]
    exact Part.mem_map _ hd

/-- The decision depends only on the transcripts. -/
theorem close_start_eq {S : InterfaceSystem I X Y}
    (h : ∀ xs ys, Transcript R (envOf D) xs ys ↔ Transcript S (envOf D) xs ys) :
    close D R [startIn] = close D S [startIn] := by
  apply Part.ext
  intro z
  obtain ⟨b, rfl⟩ := eq_decOut z
  rw [close_decision, close_decision]
  exact exists_congr fun xs => exists_congr fun ys => and_congr_left' (h xs ys)

/-! ### Defined iff compatible -/

/-- `D` is compatible with `R` (LanMau20 Def. 7): along every transcript, `D` replies,
and `R` answers every query of `D`. -/
def Compatible (D : DDD I X Y) (R : InterfaceSystem I X Y) : Prop :=
  ∀ xs ys, Transcript R (envOf D) xs ys →
    (D (dHist ys)).Dom ∧ ∀ x, x ∈ envOf D ys → (R (xs ++ [x])).Dom

/-- From every point of a transcript, the exchange of a defined decision goes on. -/
theorem exchange_along {xs ys} (tr : Transcript R (envOf D) xs ys) :
    ∀ {c G'}, Exchange (pair D R) closeRoute (hist [] []) (some c) G' →
      ∃ c' G'', Exchange (pair D R) closeRoute (hist xs ys) (some c') G'' := by
  induction tr with
  | nil => exact fun l => ⟨_, _, l⟩
  | @snoc xs ys x y tr hx hy ih =>
    intro c G' l
    obtain ⟨c', G'', l'⟩ := ih l
    have hl := tr.length_eq
    have hDx : (⟨none, ⟨.res x.1, x.2⟩⟩ : Two (Σ p, dOut X p) (Σ i, Y i)) ∈
        pair D R (hist xs ys) := by
      rw [pair_hist hl]; exact Part.mem_map _ (mem_envOf.mp hx)
    have hRy : (⟨some (), y⟩ : Two (Σ p, dOut X p) (Σ i, Y i)) ∈
        pair D R (hist xs ys ++ [⟨some (), x⟩]) := by
      rw [pair_hist_query hl]; exact Part.mem_map _ hy
    rw [hist_snoc hl]
    cases l' with
    | out _ y' _ hy' hr' =>
      obtain rfl := Part.mem_unique hy' hDx
      simp [closeRoute] at hr'
    | feed _ y' x' _ _ hy' hr' l₂ =>
      obtain rfl := Part.mem_unique hy' hDx
      simp only [closeRoute, Sum.inr.injEq] at hr'
      subst hr'
      cases l₂ with
      | out _ y'' _ hy'' hr'' =>
        obtain rfl := Part.mem_unique hy'' hRy
        simp [closeRoute] at hr''
      | feed _ y'' x'' _ _ hy'' hr'' l₃ =>
        obtain rfl := Part.mem_unique hy'' hRy
        simp only [closeRoute, Sum.inr.injEq] at hr''
        subst hr''
        exact ⟨_, _, l₃⟩

/-- **The decision is defined iff the environment is compatible with the system**
(spec §5.6), for a finite environment. -/
theorem close_dom_iff_compatible {n : ℕ} (hD : Finite n D) :
    (close D R [startIn]).Dom ↔ Compatible D R := by
  rw [close_eq]
  constructor
  · intro hd xs ys tr
    obtain ⟨H, r⟩ := mem_interconnect.mp (Part.get_mem hd)
    obtain ⟨c, G, l⟩ := exchange_along tr (induces_start.mp r)
    have hl := tr.length_eq
    have hdom := exchange_start_dom l _ rfl
    rw [pair_hist hl] at hdom
    refine ⟨hdom, fun x hx => ?_⟩
    have hDx : (⟨none, ⟨.res x.1, x.2⟩⟩ : Two (Σ p, dOut X p) (Σ i, Y i)) ∈
        pair D R (hist xs ys) := by
      rw [pair_hist hl]; exact Part.mem_map _ (mem_envOf.mp hx)
    cases l with
    | out _ y' _ hy' hr' =>
      obtain rfl := Part.mem_unique hy' hDx
      simp [closeRoute] at hr'
    | feed _ y' x' _ _ hy' hr' l₂ =>
      obtain rfl := Part.mem_unique hy' hDx
      simp only [closeRoute, Sum.inr.injEq] at hr'
      subst hr'
      have := exchange_start_dom l₂ _ rfl
      rw [pair_hist_query hl] at this
      exact this
  · intro hc
    have key : ∀ m xs ys, Transcript R (envOf D) xs ys → n - ys.length ≤ m →
        ∃ c G', Exchange (pair D R) closeRoute (hist xs ys) (some c) G' := by
      intro m
      induction m with
      | zero =>
        intro xs ys tr hm
        have := hD _ (hc xs ys tr).1
        simp [dHist] at this
        omega
      | succ m ih =>
        intro xs ys tr hm
        have hl := tr.length_eq
        obtain ⟨hdD, hdR⟩ := hc xs ys tr
        have hmem := Part.get_mem hdD
        generalize (D (dHist ys)).get hdD = o at hmem
        have hpo : (⟨none, o⟩ : Two (Σ p, dOut X p) (Σ i, Y i)) ∈ pair D R (hist xs ys) := by
          rw [pair_hist hl]; exact Part.mem_map _ hmem
        rcases o with ⟨_ | _ | i, v⟩
        · exact v.elim
        · exact ⟨_, _, Exchange.out _ _ _ hpo rfl⟩
        · have hx : (⟨i, v⟩ : Σ i, X i) ∈ envOf D ys := mem_envOf.mpr hmem
          have hdx := hdR _ hx
          have hy := Part.get_mem hdx
          generalize (R (xs ++ [⟨i, v⟩])).get hdx = y at hy
          have hbound := hD _ (hc _ _ (Transcript.snoc tr hx hy)).1
          obtain ⟨c, G', l⟩ := ih _ _ (Transcript.snoc tr hx hy) (by simp; omega)
          rw [hist_snoc hl] at l
          refine ⟨c, G', Exchange.feed _ _ ⟨some (), ⟨i, v⟩⟩ _ _ hpo rfl ?_⟩
          refine Exchange.feed _ ⟨some (), y⟩ ⟨none, envIn y⟩ _ _ ?_ rfl l
          rw [pair_hist_query hl]; exact Part.mem_map _ hy
    obtain ⟨c, G', l⟩ := key n [] [] Transcript.nil (by simp)
    exact Part.dom_iff_mem.mpr ⟨c, mem_interconnect.mpr ⟨G', induces_start.mpr l⟩⟩

end Decision

/-! ## Resources: `≈` is observed by DDDs (spec §1.4) -/

section Resource

variable {I : Type} {X Y : I → Type}

/-- A resource replies at the interface it was queried at. -/
def RepliesAtQueriedInterface (R : InterfaceSystem I X Y) : Prop := ∀ h a y, y ∈ R (h ++ [a]) → y.1 = a.1

/-- A change of interface vocabulary preserves responding interfaces. -/
theorem RepliesAtQueriedInterface.relabel {J : Type} {U V : J → Type} {R : InterfaceSystem I X Y} (hr : RepliesAtQueriedInterface R)
    (f : (Σ j, U j) → (Σ i, X i)) (g : (Σ i, Y i) → (Σ j, V j))
    (hl : ∀ x y, y.1 = (f x).1 → (g y).1 = x.1) : RepliesAtQueriedInterface (relabel R f g) := by
  intro h x y hy
  obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).mp hy
  have hz' : z ∈ R (h.map f ++ [f x]) := by
    simpa only [List.map_append, List.map_singleton] using hz
  exact hl x z (hr (h.map f) (f x) z hz')

/-- Replies `ys` whose labels are those of the first queries of `h`. -/
def Fits (h : List (Σ i, X i)) (ys : List (Σ i, Y i)) : Prop :=
  ys.length ≤ h.length ∧ ys.map Sigma.fst = (h.take ys.length).map Sigma.fst

/-- The next output of the probe after the replies `ys`. -/
def probeReply (h : List (Σ i, X i)) (P : List (Σ i, Y i) → Bool) (ys : List (Σ i, Y i)) :
    Part (Σ p, dOut X p) :=
  match h[ys.length]? with
  | some q => Part.some ⟨.res q.1, q.2⟩
  | none => Part.some ⟨.dec, P ys⟩

/-- The probe: it queries `h` in order and decides `P` of the replies. It is silent on
replies at the wrong interface. -/
noncomputable def probe (h : List (Σ i, X i)) (P : List (Σ i, Y i) → Bool) : DDD I X Y
  | ⟨.start, _⟩ :: ws =>
    if hv : ∃ ys, ws = ys.map envIn ∧ Fits h ys then probeReply h P (Classical.choose hv)
    else Part.none
  | _ => Part.none

variable {h : List (Σ i, X i)} {P : List (Σ i, Y i) → Bool}

theorem probe_dHist {ys : List (Σ i, Y i)} (hv : Fits h ys) :
    probe h P (dHist ys) = probeReply h P ys := by
  have hex : ∃ ys', ys.map envIn = ys'.map envIn ∧ Fits h ys' := ⟨ys, rfl, hv⟩
  simp only [probe, dHist, dif_pos hex]
  have e : Classical.choose hex = ys :=
    (List.map_injective_iff.mpr envIn_injective (Classical.choose_spec hex).1).symm
  rw [e]

theorem probe_dom {w} (hd : (probe (Y := Y) h P w).Dom) : ∃ ys, w = dHist ys ∧ Fits h ys := by
  match w, hd with
  | ⟨.start, ()⟩ :: ws, hd =>
    simp only [probe] at hd
    split_ifs at hd with hv
    · exact ⟨Classical.choose hv, by rw [dHist, ← (Classical.choose_spec hv).1],
        (Classical.choose_spec hv).2⟩
    · exact hd.elim
  | [], hd => exact hd.elim
  | ⟨.dec, e⟩ :: _, _ => exact e.elim
  | ⟨.res _, _⟩ :: _, hd => exact hd.elim

theorem Fits.of_snoc {ys : List (Σ i, Y i)} {y} (hv : Fits h (ys ++ [y])) :
    Fits h ys ∧ ∃ q, h[ys.length]? = some q ∧ y.1 = q.1 := by
  obtain ⟨hle, hm⟩ := hv
  simp only [List.length_append, List.length_singleton] at hle hm
  have hlt : ys.length < h.length := by omega
  rw [List.take_add_one, List.getElem?_eq_getElem hlt] at hm
  simp only [List.map_append, List.map_cons, List.map_nil, Option.toList_some] at hm
  obtain ⟨h1, h2⟩ := List.append_inj' hm (by simp)
  simp only [List.cons.injEq, and_true] at h2
  exact ⟨⟨by omega, h1⟩, _, List.getElem?_eq_getElem hlt, h2⟩

theorem Fits.snoc {ys : List (Σ i, Y i)} (hv : Fits h ys) {q} (hq : h[ys.length]? = some q)
    {y : Σ i, Y i} (hy : y.1 = q.1) : Fits h (ys ++ [y]) := by
  obtain ⟨hle, hm⟩ := hv
  have hlt : ys.length < h.length := (List.getElem?_eq_some_iff.mp hq).1
  obtain rfl : h[ys.length] = q := (List.getElem?_eq_some_iff.mp hq).2
  refine ⟨by simp; omega, ?_⟩
  rw [List.length_append, List.length_singleton, List.take_add_one, List.getElem?_eq_getElem hlt]
  simp only [List.map_append, List.map_cons, List.map_nil, Option.toList_some, hm, hy]

theorem dHist_snoc_inv {w : List (Σ p, dIn Y p)} {z} {ys' : List (Σ i, Y i)}
    (e : w ++ [z] = dHist ys') :
    (w = [] ∧ z = ⟨.start, ()⟩) ∨ ∃ ys y, ys' = ys ++ [y] ∧ w = dHist ys ∧ z = envIn y := by
  rcases List.eq_nil_or_concat ys' with rfl | ⟨ys, y, rfl⟩
  · left
    have : w ++ [z] = [] ++ [⟨.start, ()⟩] := e
    obtain ⟨h1, h2⟩ := List.append_inj' this rfl
    exact ⟨h1, by simpa using h2⟩
  · right
    have : w ++ [z] = dHist ys ++ [envIn y] := by simpa [dHist] using e
    obtain ⟨h1, h2⟩ := List.append_inj' this rfl
    exact ⟨ys, y, List.concat_eq_append .., h1, by simpa using h2⟩

theorem dHist_ne_nil (ys : List (Σ i, Y i)) : dHist ys ≠ [] := by simp [dHist]

/-- The probe is a DDD. -/
theorem probe_finite : Finite (h.length + 1) (probe (Y := Y) h P) := by
  intro w hd
  obtain ⟨ys, rfl, hv⟩ := probe_dom hd
  simp [dHist]; exact hv.1

theorem probe_isDDD : IsDDD (probe (Y := Y) h P) := by
  refine ⟨?_, ⟨h.length + 1, probe_finite⟩, ?_, ?_, ?_⟩
  · simp [SilentAtEmpty, probe]
  · intro w z hr
    obtain ⟨ys', e, -⟩ := probe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp
    · simp [dHist_ne_nil, envIn]
  · intro w z i hr hl
    obtain ⟨ys', e, hv'⟩ := probe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp [replyLabel, probe] at hl
    · obtain ⟨hv, q, hq, hyq⟩ := hv'.of_snoc
      rw [replyLabel, probe_dHist hv] at hl
      simp only [probeReply, hq, Part.some_dom, dite_true, Part.get_some, Option.some.injEq,
        DPort.res.injEq] at hl
      simp [envIn, hyq, hl]
  · intro w z hr hl
    obtain ⟨ys', e, hv'⟩ := probe_dom (reach_snoc_iff.mp hr).2
    rcases dHist_snoc_inv e with ⟨rfl, rfl⟩ | ⟨ys, y, rfl, rfl, rfl⟩
    · simp [replyLabel, probe] at hl
    · obtain ⟨hv, q, hq, -⟩ := hv'.of_snoc
      rw [replyLabel, probe_dHist hv] at hl
      simp [probeReply, hq] at hl

theorem fixedQueries_take {R : InterfaceSystem I X Y} {H : List (Σ i, X i)} {xs ys}
    (tr : Transcript R (fixedQueries H) xs ys) : xs = H.take xs.length := by
  induction tr with
  | nil => simp
  | @snoc xs ys x y tr hx _ ih =>
    have hl := tr.length_eq
    simp only [fixedQueries, Part.mem_ofOption, Option.mem_def] at hx
    rw [List.length_append, List.length_singleton, List.take_add_one, hl, hx, ← hl, ← ih]
    rfl

theorem probe_transcript_fixed {R : InterfaceSystem I X Y} (hR : RepliesAtQueriedInterface R) {xs ys}
    (tr : Transcript R (envOf (probe h P)) xs ys) : Transcript R (fixedQueries h) xs ys ∧ Fits h ys := by
  induction tr with
  | nil => exact ⟨Transcript.nil, by simp [Fits]⟩
  | @snoc xs ys x y tr hx hy ih =>
    obtain ⟨tr', hv⟩ := ih
    rw [mem_envOf, probe_dHist hv] at hx
    simp only [probeReply] at hx
    split at hx
    · next q hq =>
      simp only [Part.mem_some_iff, Sigma.mk.injEq, DPort.res.injEq] at hx
      obtain ⟨e1, e2⟩ := hx
      have hxq : x = q := by
        rcases x with ⟨i, v⟩; rcases q with ⟨i', v'⟩
        simp only at e1 e2; subst e1; cases e2; rfl
      subst hxq
      refine ⟨Transcript.snoc tr' (by simp [fixedQueries, hq]) hy, ?_⟩
      exact hv.snoc hq (hR _ _ _ hy)
    · simp at hx

theorem fixed_probe_transcript {R : InterfaceSystem I X Y} (hR : RepliesAtQueriedInterface R) {xs ys}
    (tr : Transcript R (fixedQueries h) xs ys) :
    Transcript R (envOf (probe h P)) xs ys ∧ Fits h ys := by
  induction tr with
  | nil => exact ⟨Transcript.nil, by simp [Fits]⟩
  | @snoc xs ys x y tr hx hy ih =>
    obtain ⟨tr', hv⟩ := ih
    simp only [fixedQueries, Part.mem_ofOption, Option.mem_def] at hx
    refine ⟨Transcript.snoc tr' ?_ hy, hv.snoc hx (hR _ _ _ hy)⟩
    rw [mem_envOf, probe_dHist hv]
    simp [probeReply, hx]

/-- The decisions of the probe on a resource: it decides `P` of the replies to `h`,
exactly when `h` is answered. -/
theorem probe_decision {R : InterfaceSystem I X Y} (hR : RepliesAtQueriedInterface R) (b : Bool) :
    decOut b ∈ close (probe h P) R [startIn] ↔
      ∃ ys, Transcript R (fixedQueries h) h ys ∧ b = P ys := by
  rw [close_decision]
  constructor
  · rintro ⟨xs, ys, tr, hd⟩
    obtain ⟨tr', hv⟩ := probe_transcript_fixed hR tr
    rw [probe_dHist hv] at hd
    simp only [probeReply] at hd
    split at hd
    · simp at hd
    · next hq =>
      simp only [Part.mem_some_iff, Sigma.mk.injEq, heq_eq_eq, true_and] at hd
      have hlen : ys.length = h.length := le_antisymm hv.1 (List.getElem?_eq_none_iff.mp hq)
      have hxs : xs = h := by
        rw [fixedQueries_take tr', tr'.length_eq, hlen, List.take_length]
      subst hxs
      exact ⟨ys, tr', hd⟩
  · rintro ⟨ys, tr, rfl⟩
    obtain ⟨tr', hv⟩ := fixed_probe_transcript hR tr
    refine ⟨h, ys, tr', ?_⟩
    have hq : h[ys.length]? = none := by
      rw [← tr.length_eq]; simp
    rw [probe_dHist hv]
    simp [probeReply, hq]

variable {R S : InterfaceSystem I X Y}

/-- **For resources, behavioural equality is equality of the decisions of every DDD**
(spec §1.4, LanMau20 Def. 7). -/
theorem behEq_iff_decision (hR : RepliesAtQueriedInterface R) (hS : RepliesAtQueriedInterface S) :
    R ≈ₛ S ↔ ∀ D : DDD I X Y, IsDDD D → close D R [startIn] = close D S [startIn] := by
  constructor
  · intro hRS D _
    exact close_start_eq ((behEq_iff_transcript.mp hRS) (envOf D))
  · intro hdec
    have hreach : ∀ h, Reach R h ↔ Reach S h := by
      intro h
      rw [transcript_fixedQueries (H := h) h [] (by simp),
        transcript_fixedQueries (H := h) h [] (by simp)]
      have e₁ := probe_decision (h := h) (P := fun _ => true) hR true
      have e₂ := probe_decision (h := h) (P := fun _ => true) hS true
      rw [hdec _ probe_isDDD] at e₁
      simpa using e₁.symm.trans e₂
    refine ⟨hreach, fun h hr hne => ?_⟩
    obtain ⟨ysR, trR⟩ := (transcript_fixedQueries (H := h) h [] (by simp)).mp hr
    have e₁ := probe_decision (h := h) (P := fun ys => decide (ys = ysR)) hR true
    have e₂ := probe_decision (h := h) (P := fun ys => decide (ys = ysR)) hS true
    rw [hdec _ probe_isDDD] at e₁
    obtain ⟨ys, trS, hys⟩ := e₂.mp (e₁.mpr ⟨ysR, trR, by simp⟩)
    obtain rfl : ys = ysR := by simpa using hys.symm
    rcases List.eq_nil_or_concat h with rfl | ⟨h₀, x, rfl⟩
    · exact (hne rfl).elim
    rw [List.concat_eq_append] at trR trS ⊢
    obtain ⟨ys₀, y, rfl, -, -, hyR⟩ := trR.snoc_inv
    obtain ⟨ys₀', y', e, -, -, hyS⟩ := trS.snoc_inv
    obtain ⟨-, e'⟩ := List.append_inj' e rfl
    simp only [List.cons.injEq, and_true] at e'
    subst e'
    rw [Part.eq_some_iff.mpr hyR, Part.eq_some_iff.mpr hyS]

/-- **For resources, behavioural equality is equality of the transcripts with every DDD**
(spec §1.4). -/
theorem behEq_iff_transcript_DDD (hR : RepliesAtQueriedInterface R) (hS : RepliesAtQueriedInterface S) :
    R ≈ₛ S ↔ ∀ D : DDD I X Y, IsDDD D →
      ∀ xs ys, Transcript R (envOf D) xs ys ↔ Transcript S (envOf D) xs ys := by
  constructor
  · exact fun hRS D _ => (behEq_iff_transcript.mp hRS) (envOf D)
  · exact fun h => (behEq_iff_decision hR hS).mpr fun D hD => close_start_eq (h D hD)

end Resource

/-! ## Beyond resources, DDDs observe less than `≈` (spec §1.4) -/

section Blind

/-- Answers the first query at the other interface, then stays silent. -/
def swapper : InterfaceSystem Bool (fun _ => Unit) (fun _ => Unit)
  | [⟨i, ()⟩] => Part.some ⟨!i, ()⟩
  | _ => Part.none

/-- Never answers. -/
def mute : InterfaceSystem Bool (fun _ => Unit) (fun _ => Unit) := fun _ => Part.none

theorem swapper_transcript {e xs ys} (tr : Transcript swapper e xs ys) :
    ys = [] ∨ ∃ x y, xs = [x] ∧ ys = [y] ∧ x ∈ e [] ∧ y ∈ swapper [x] := by
  cases tr with
  | nil => exact Or.inl rfl
  | @snoc xs ys x y tr hx hy =>
    right
    rcases xs with _ | ⟨x₀, xs⟩
    · have : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using tr.length_eq.symm)
      subst this
      exact ⟨x, y, rfl, rfl, hx, hy⟩
    · exfalso
      rcases x₀ with ⟨i, ⟨⟩⟩
      simp [swapper] at hy

theorem mute_transcript {e xs ys} (tr : Transcript mute e xs ys) : ys = [] := by
  cases tr with
  | nil => rfl
  | snoc _ _ hy => simp [mute] at hy

/-- **DDDs do not see replies at another interface**: `swapper` and `mute` are not
behaviourally equal, but every DDD decides the same with both. -/
theorem dde_blind_beyond_resources :
    ¬ swapper ≈ₛ mute ∧
      ∀ D : DDD Bool (fun _ => Unit) (fun _ => Unit), IsDDD D →
        close D swapper [startIn] = close D mute [startIn] := by
  refine ⟨fun h => ?_, fun D hD => ?_⟩
  · have hr : Reach swapper [⟨true, ()⟩] := by
      rw [show ([⟨true, ()⟩] : List (Σ _ : Bool, Unit)) = [] ++ [⟨true, ()⟩] from rfl,
        reach_snoc_iff]
      exact ⟨reach_nil _, by simp [swapper]⟩
    have := reach_snoc_iff.mp (show Reach mute ([] ++ [⟨true, ()⟩]) from (h.1 _).mp hr)
    simp [mute] at this
  · apply Part.ext
    intro z
    obtain ⟨b, rfl⟩ := eq_decOut z
    rw [close_decision, close_decision]
    constructor
    · rintro ⟨xs, ys, tr, hd⟩
      rcases swapper_transcript tr with rfl | ⟨x, y, rfl, rfl, hx, hy⟩
      · exact ⟨[], [], Transcript.nil, hd⟩
      · exfalso
        rcases x with ⟨i, ⟨⟩⟩
        simp only [swapper, Part.mem_some_iff] at hy
        subst hy
        have hq := mem_envOf.mp hx
        have hr : Reach D ([⟨.start, ()⟩] ++ [envIn (⟨!i, ()⟩ : Σ _ : Bool, Unit)]) := by
          refine reach_snoc_iff.mpr ⟨?_, Part.dom_iff_mem.mpr ⟨_, hd⟩⟩
          rw [show ([⟨.start, ()⟩] : List (Σ p, dIn (fun _ : Bool => Unit) p)) = [] ++ [⟨.start, ()⟩]
            from rfl, reach_snoc_iff]
          exact ⟨reach_nil _, Part.dom_iff_mem.mpr ⟨_, hq⟩⟩
        have := hD.2.2.2.1 _ _ i hr (replyLabel_of_mem D hq)
        cases i <;> simp [envIn] at this
    · rintro ⟨xs, ys, tr, hd⟩
      obtain rfl := mute_transcript tr
      exact ⟨[], [], Transcript.nil, hd⟩

end Blind

end SystemAlgebra

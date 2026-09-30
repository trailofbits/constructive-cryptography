import Mathlib.Data.PFun
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Option

/-!
# Systems and their wiring

A system `System A B` is a partial function `List A →. B` from input histories to
the next output; it is a deterministic discrete system (`IsDDS`) when it is silent
before the first input and its domain is closed under nonempty prefixes. Source:
Lanzenberger–Maurer, *Coupling of Random Systems*, Definition 5.

## Main definitions

* `System`, `IsDDS`, `DDS`, `SilentAtEmpty`, `PrefixClosed`, `Finite`, `Terminating`
* `Reach`, `trim`, `EqOnReachable` (`≈`): reachable histories and equality on them
* `relabel s f g`: renaming the input and output alphabets
* `interconnect s route inj`: feeding outputs back as inputs along a routing
  table, with the relations `Exchange` and `Induces` and the condition `Converges`
* `parAll`, `pair`: parallel composition of a family and of two systems

## Main results

* `interconnect_interconnect`: two nested wirings are one wiring
* `interconnect_relabel`, `relabel_interconnect`: relabeling commutes with wiring
* `parAll_interconnect`: locality of parallel composition under wiring
* `parAll_reindex`, `parAll_flatten`, `parAll_relabel`
* `Finite.terminating`, `Terminating.parAll`, `Terminating.interconnect`,
  `Terminating.relabel`
* `converges_pair`, `converges_pair_of_terminating`, `interconnect_no_feedback`
* `trim_behEq`, `trim_prefix_closed`, `IsDDS.trim_eq`
-/

namespace SystemAlgebra

open Classical

/-- A discrete system (LanMau20 Def. 5, printed p. 11): a partial function on histories. -/
abbrev System (A B : Type) := List A →. B

variable {A B C D E X Y M N : Type}

/-! ## Relabeling -/

/-- Rename inputs and outputs. -/
def relabel (s : System X Y) (f : A → X) (g : Y → B) : System A B :=
  fun h => (s (h.map f)).map g

theorem relabel_relabel (s : System X Y) (f : A → X) (g : Y → B)
    (f' : C → A) (g' : B → D) :
    relabel (relabel s f g) f' g' = relabel s (f ∘ f') (g' ∘ g) := by
  funext h
  simp [relabel, List.map_map, Part.map_map]

theorem relabel_id (s : System X Y) : relabel s id id = s := by
  funext h
  simp [relabel]
  exact Part.map_id' (fun _ => rfl) _

/-- Two systems are equal once their replies have the same members. -/
theorem system_ext {s t : System A B} (h : ∀ u b, b ∈ s u ↔ b ∈ t u) : s = t := by
  funext u
  exact Part.ext (h u)

/-! ## Predicates on the carrier (spec §1) -/

/-- A reactive system never speaks before it has received an input. -/
def SilentAtEmpty (s : System X Y) : Prop := ¬ (s []).Dom

/-- The domain is closed under nonempty prefixes. -/
def PrefixClosed (s : System X Y) : Prop :=
  ∀ ⦃l₁ l₂ : List X⦄, l₁ <+: l₂ → l₁ ≠ [] → (s l₂).Dom → (s l₁).Dom

/-- A deterministic discrete system (LanMau20 Def. 5, printed p. 11): silent before
the first input, with a prefix-closed domain. -/
def IsDDS (s : System X Y) : Prop := SilentAtEmpty s ∧ PrefixClosed s

/-- Deterministic discrete systems. -/
abbrev DDS (X Y : Type) := {s : System X Y // IsDDS s}

/-- Silent on all histories longer than `n`. -/
def Finite (n : ℕ) (s : System X Y) : Prop := ∀ h, (s h).Dom → h.length ≤ n

/-- Every defined reply strictly decreases a natural-number measure. -/
def Terminating (s : System X Y) : Prop :=
  ∃ μ : List X → ℕ, ∀ h x, (s (h ++ [x])).Dom → μ (h ++ [x]) < μ h

/-- T0. -/
theorem Finite.terminating {n : ℕ} {s : System X Y} (hs : Finite n s) : Terminating s :=
  ⟨fun h => n - h.length, fun h x hd => by
    have := hs _ hd
    simp at this ⊢
    omega⟩

/-- T3. -/
theorem Terminating.relabel {s : System X Y} (hs : Terminating s) (f : A → X) (g : Y → B) :
    Terminating (SystemAlgebra.relabel s f g) := by
  obtain ⟨μ, hμ⟩ := hs
  exact ⟨fun h => μ (h.map f), fun h x hd => by simpa using hμ (h.map f) (f x) (by simpa [SystemAlgebra.relabel] using hd)⟩

/-- Histories all of whose nonempty prefixes are answered. -/
def Reach (s : System X Y) (h : List X) : Prop :=
  ∀ h' e, h = h' ++ e → h' ≠ [] → (s h').Dom

/-- The reachable part of a system. -/
noncomputable def trim (s : System X Y) : System X Y :=
  fun h => if Reach s h then s h else Part.none

theorem trim_eq_of_prefix_eq {s t : System X Y} {h : List X}
    (he : ∀ p, p <+: h → s p = t p) : trim s h = trim t h := by
  have hr : Reach s h ↔ Reach t h := by
    constructor <;> intro hp p e hh hn
    · rw [← he p ⟨e, hh.symm⟩]; exact hp p e hh hn
    · rw [he p ⟨e, hh.symm⟩]; exact hp p e hh hn
  simp only [trim, hr, he h (List.prefix_refl h)]

/-- Behavioural equality: same reachable histories, same replies there. -/
def EqOnReachable (s t : System X Y) : Prop :=
  (∀ h, Reach s h ↔ Reach t h) ∧ ∀ h, Reach s h → h ≠ [] → s h = t h

infix:50 " ≈ₛ " => EqOnReachable

/-! ## Wiring by a routing table -/

section Wire

variable (s : System X Y) (route : Y → B ⊕ X) (inj : A → X)

/-- The internal exchange from the internal history `h`: evaluate `s`,
feed internal outputs back, stop at an exposed output or at silence. -/
inductive Exchange : List X → Option B → List X → Prop
  | silent (h) : ¬ (s h).Dom → Exchange h none h
  | out (h) (y : Y) (b : B) : y ∈ s h → route y = Sum.inl b → Exchange h (some b) h
  | feed (h) (y : Y) (x : X) (o h') : y ∈ s h → route y = Sum.inr x →
      Exchange (h ++ [x]) o h' → Exchange h o h'

/-- An external history induces the last exposed reply and the internal history
reached afterwards. No exchange happens at the empty history (spec §4). -/
inductive Induces : List A → Option B → List X → Prop
  | nil : Induces [] none []
  | snoc (u a o₀ H o H') : Induces u o₀ H → Exchange s route (H ++ [inj a]) o H' →
      Induces (u ++ [a]) o H'

variable {s route inj}

theorem Exchange.det {h o₁ H₁ o₂ H₂} (l₁ : Exchange s route h o₁ H₁) (l₂ : Exchange s route h o₂ H₂) :
    o₁ = o₂ ∧ H₁ = H₂ := by
  induction l₁ generalizing o₂ H₂ with
  | silent h hd =>
    cases l₂ with
    | silent => exact ⟨rfl, rfl⟩
    | out _ y _ hy => exact (hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
    | feed _ y _ _ _ hy => exact (hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
  | out h y b hy hr =>
    cases l₂ with
    | silent _ hd => exact (hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
    | out _ y' b' hy' hr' =>
      have := Part.mem_unique hy hy'
      subst this
      rw [hr] at hr'
      cases hr'
      exact ⟨rfl, rfl⟩
    | feed _ y' x' _ _ hy' hr' =>
      have := Part.mem_unique hy hy'
      subst this
      rw [hr] at hr'
      cases hr'
  | feed h y x o h' hy hr _ ih =>
    cases l₂ with
    | silent _ hd => exact (hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
    | out _ y' b' hy' hr' =>
      have := Part.mem_unique hy hy'
      subst this
      rw [hr] at hr'
      cases hr'
    | feed _ y' x' _ _ hy' hr' l =>
      have := Part.mem_unique hy hy'
      subst this
      rw [hr] at hr'
      cases hr'
      exact ih l

theorem Induces.inv {u o H} (r : Induces s route inj u o H) :
    (u = [] ∧ o = none ∧ H = []) ∨
      ∃ u' a o₀ H₀, u = u' ++ [a] ∧ Induces s route inj u' o₀ H₀ ∧
        Exchange s route (H₀ ++ [inj a]) o H := by
  cases r with
  | nil => exact Or.inl ⟨rfl, rfl, rfl⟩
  | snoc u' a o₀ H₀ _ _ r l => exact Or.inr ⟨u', a, o₀, H₀, rfl, r, l⟩

theorem induces_nil_iff {o H} : Induces s route inj [] o H ↔ o = none ∧ H = [] := by
  constructor
  · intro r
    rcases r.inv with ⟨-, h⟩ | ⟨u', a, _, _, hu, _, _⟩
    · exact h
    · simp at hu
  · rintro ⟨rfl, rfl⟩; exact Induces.nil

theorem induces_snoc_iff {u a o H'} :
    Induces s route inj (u ++ [a]) o H' ↔
      ∃ o₀ H, Induces s route inj u o₀ H ∧ Exchange s route (H ++ [inj a]) o H' := by
  constructor
  · intro r
    rcases r.inv with ⟨hu, -⟩ | ⟨u', a', o₀, H, hu, r, l⟩
    · simp at hu
    · obtain ⟨rfl, h2⟩ := List.append_inj' hu rfl
      cases h2
      exact ⟨o₀, H, r, l⟩
  · rintro ⟨o₀, H, r, l⟩
    exact Induces.snoc _ _ _ _ _ _ r l

theorem Induces.det {u o₁ H₁ o₂ H₂} (r₁ : Induces s route inj u o₁ H₁)
    (r₂ : Induces s route inj u o₂ H₂) : o₁ = o₂ ∧ H₁ = H₂ := by
  induction r₁ generalizing o₂ H₂ with
  | nil => obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r₂; exact ⟨rfl, rfl⟩
  | snoc u a o₀ H o H' r l ih =>
    obtain ⟨_, K, r', l'⟩ := induces_snoc_iff.mp r₂
    obtain ⟨-, rfl⟩ := ih r'
    exact l.det l'

variable (s route inj)

/-- The wired system: its reply is the last exposed reply induced by the external history. -/
noncomputable def interconnect : System A B := fun u =>
  ⟨∃ b H, Induces s route inj u (some b) H, fun h => Classical.choose h⟩

variable {s route inj}

theorem mem_interconnect {u b} : b ∈ interconnect s route inj u ↔ ∃ H, Induces s route inj u (some b) H := by
  constructor
  · rintro ⟨h, rfl⟩
    exact Classical.choose_spec h
  · rintro ⟨H, r⟩
    refine ⟨⟨b, H, r⟩, ?_⟩
    obtain ⟨H', r'⟩ := Classical.choose_spec (⟨b, H, r⟩ : ∃ b H, Induces s route inj u (some b) H)
    exact Option.some_inj.mp (r'.det r).1

end Wire

section Basic

variable {s : System X Y} {route : Y → B ⊕ X} {inj : A → X}

theorem Exchange.extends {h o h'} (l : Exchange s route h o h') : ∃ e, h' = h ++ e := by
  induction l with
  | silent => exact ⟨[], by simp⟩
  | out => exact ⟨[], by simp⟩
  | feed h y x o h' _ _ _ ih =>
    obtain ⟨e, rfl⟩ := ih
    exact ⟨x :: e, by simp⟩

theorem Induces.prefix {u e o H} (r : Induces s route inj (u ++ e) o H) :
    ∃ o' H', Induces s route inj u o' H' := by
  induction e using List.reverseRecOn generalizing o H with
  | nil => exact ⟨o, H, by simpa using r⟩
  | append_singleton e a ih =>
    rw [← List.append_assoc] at r
    obtain ⟨o₀, H₀, r₀, -⟩ := induces_snoc_iff.mp r
    exact ih r₀

theorem mem_of_induces_some {u b H} (r : Induces s route inj u (some b) H) :
    b ∈ interconnect s route inj u := mem_interconnect.mpr ⟨H, r⟩

theorem not_dom_of_induces_none {u H} (r : Induces s route inj u none H) :
    ¬ (interconnect s route inj u).Dom := by
  intro d
  obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.get_mem d)
  cases (r.det r').1

theorem interconnect_eq_some {u b H} (r : Induces s route inj u (some b) H) :
    interconnect s route inj u = Part.some b :=
  Part.eq_some_iff.mpr (mem_of_induces_some r)

theorem interconnect_eq_none {u H} (r : Induces s route inj u none H) :
    interconnect s route inj u = Part.none :=
  Part.eq_none_iff'.mpr (not_dom_of_induces_none r)

/-- An exchange uses only the system values on its actual input prefixes. -/
theorem Exchange.congr_of_prefix_eq {t : System X Y} {G o H}
    (l : Exchange s route G o H) (he : ∀ p, p <+: H → s p = t p) :
    Exchange t route G o H := by
  induction l with
  | silent G hd => exact Exchange.silent G (by rwa [← he G (List.prefix_refl G)])
  | out G y b hy hr =>
    exact Exchange.out G y b (by rwa [← he G (List.prefix_refl G)]) hr
  | feed G y x o H hy hr l ih =>
    obtain ⟨e, hH⟩ := l.extends
    exact Exchange.feed G y x o H (by rwa [← he G ⟨x :: e, by rw [hH]; simp⟩])
      hr (ih he)

theorem Induces.congr_of_prefix_eq {t : System X Y} {u o H}
    (r : Induces s route inj u o H) (he : ∀ p, p <+: H → s p = t p) :
    Induces t route inj u o H := by
  induction r with
  | nil => exact Induces.nil
  | snoc u x o₀ H₀ o H r l ih =>
    obtain ⟨e, hH⟩ := l.extends
    have hp : H₀ <+: H := ⟨inj x :: e, by rw [hH]; simp⟩
    exact Induces.snoc _ _ _ _ _ _ (ih (fun p h => he p (h.trans hp)))
      (l.congr_of_prefix_eq he)

/-- Prefixes of the exposed history keep prefixes of the same component history. -/
theorem Induces.prefix_history {u e o H} (r : Induces s route inj (u ++ e) o H) :
    ∃ o' H', Induces s route inj u o' H' ∧ H' <+: H := by
  induction e using List.reverseRecOn generalizing o H with
  | nil => exact ⟨o, H, by simpa using r, List.prefix_refl H⟩
  | append_singleton e a ih =>
    rw [← List.append_assoc] at r
    obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r
    obtain ⟨o', H', r', hp⟩ := ih r₀
    obtain ⟨e', he'⟩ := l.extends
    exact ⟨o', H', r', hp.trans ⟨inj a :: e', by rw [he']; simp⟩⟩

/-- Finite component agreement determines every observed prefix, including silence. -/
theorem Induces.interconnect_eq_on_prefixes {t : System X Y} {u o H}
    (r : Induces s route inj u o H) (he : ∀ p, p <+: H → s p = t p) :
    ∀ p, p <+: u → interconnect s route inj p = interconnect t route inj p := by
  rintro p ⟨e, rfl⟩
  obtain ⟨o', H', r', hp⟩ := r.prefix_history
  have rt := r'.congr_of_prefix_eq (fun q hq => he q (hq.trans hp))
  cases o' with
  | none => rw [interconnect_eq_none r', interconnect_eq_none rt]
  | some y => rw [interconnect_eq_some r', interconnect_eq_some rt]

/-- No internal exchange diverges: every external history induces an internal history. -/
def Converges (s : System X Y) (route : Y → B ⊕ X) (inj : A → X) : Prop :=
  ∀ u, ∃ o H, Induces s route inj u o H

/-- If every internal exchange stops, the wiring converges. -/
theorem converges_of_exchanges (h : ∀ H, ∃ o H', Exchange s route H o H') :
    ∀ u, ∃ o H, Induces s route inj u o H := by
  intro u
  induction u using List.reverseRecOn with
  | nil => exact ⟨none, [], Induces.nil⟩
  | append_singleton u a ih =>
    obtain ⟨o₀, H₀, r⟩ := ih
    obtain ⟨o, H, l⟩ := h (H₀ ++ [inj a])
    exact ⟨o, H, Induces.snoc _ _ _ _ _ _ r l⟩

end Basic

/-! ## Two nested wirings are one wiring -/

section Vanishing

variable (s : System X Y) (r₁ : Y → M ⊕ X) (i₁ : N → X)
  (r₂ : M → B ⊕ N) (i₂ : A → N)

/-- The routing table obtained by closing first `r₁`, then `r₂`. -/
def routeComp : Y → B ⊕ X := fun y =>
  match r₁ y with
  | Sum.inr x => Sum.inr x
  | Sum.inl m =>
    match r₂ m with
    | Sum.inl b => Sum.inl b
    | Sum.inr n => Sum.inr (i₁ n)

variable {s r₁ i₁ r₂ i₂}

local notation "F" => interconnect s r₁ i₁
local notation "RJ" => routeComp r₁ i₁ r₂

/-- What the joint exchange does after the inner exchange has stopped. -/
def Cont (o₁ : Option M) (T : List X) (o : Option B) (T' : List X) : Prop :=
  match o₁ with
  | none => o = none ∧ T' = T
  | some m =>
    (∃ b, r₂ m = Sum.inl b ∧ o = some b ∧ T' = T) ∨
      (∃ n, r₂ m = Sum.inr n ∧ Exchange s RJ (T ++ [i₁ n]) o T')

theorem joint_of_inner {T₀ o₁ T₁ o T'} (l : Exchange s r₁ T₀ o₁ T₁)
    (c : Cont (s := s) (r₁ := r₁) (i₁ := i₁) (r₂ := r₂) o₁ T₁ o T') : Exchange s RJ T₀ o T' := by
  induction l with
  | silent h hd =>
    obtain ⟨rfl, rfl⟩ := c
    exact Exchange.silent _ hd
  | out h y m hy hr =>
    rcases c with ⟨b, hb, rfl, rfl⟩ | ⟨n, hn, l'⟩
    · exact Exchange.out _ y b hy (by simp [routeComp, hr, hb])
    · exact Exchange.feed _ y _ _ _ hy (by simp [routeComp, hr, hn]) l'
  | feed h y x _ _ hy hr _ ih =>
    exact Exchange.feed _ y x _ _ hy (by simp [routeComp, hr]) (ih c)

/-- The internal history induced by `K` continues as the inner exchange from `T₀`. -/
def Pending (K : List N) (T₀ : List X) : Prop :=
  ∀ o₂ T₂, Induces s r₁ i₁ K o₂ T₂ ↔ Exchange s r₁ T₀ o₂ T₂

theorem pending_snoc {K o T n} (r : Induces s r₁ i₁ K o T) :
    Pending (s := s) (r₁ := r₁) (i₁ := i₁) (K ++ [n]) (T ++ [i₁ n]) := by
  intro o₂ T₂
  rw [induces_snoc_iff]
  constructor
  · rintro ⟨o', T', r', l⟩
    obtain ⟨-, rfl⟩ := r.det r'
    exact l
  · intro l
    exact ⟨o, T, r, l⟩

theorem pending_feed {K T₀ y x} (p : Pending (s := s) (r₁ := r₁) (i₁ := i₁) K T₀)
    (hy : y ∈ s T₀) (hr : r₁ y = Sum.inr x) :
    Pending (s := s) (r₁ := r₁) (i₁ := i₁) K (T₀ ++ [x]) := by
  intro o₂ T₂
  rw [p]
  constructor
  · intro l
    cases l with
    | silent _ hd => exact (hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
    | out _ y' _ hy' hr' =>
      rw [Part.mem_unique hy hy', hr'] at hr; cases hr
    | feed _ y' x' _ _ hy' hr' l =>
      rw [Part.mem_unique hy hy', hr'] at hr; cases hr; exact l
  · exact Exchange.feed _ y x _ _ hy hr

theorem outer_of_joint {T₀ o T'} (l : Exchange s RJ T₀ o T') :
    ∀ K, Pending (s := s) (r₁ := r₁) (i₁ := i₁) K T₀ →
      ∃ K', Exchange F r₂ K o K' ∧ ∃ o₁, Induces s r₁ i₁ K' o₁ T' := by
  induction l with
  | silent h hd =>
    intro K p
    have r := (p none h).mpr (Exchange.silent _ hd)
    exact ⟨K, Exchange.silent _ (not_dom_of_induces_none r), none, r⟩
  | out h y b hy hr =>
    intro K p
    unfold routeComp at hr
    split at hr
    · cases hr
    · rename_i m hm
      split at hr
      · cases hr
        have r := (p (some m) h).mpr (Exchange.out _ y m hy hm)
        exact ⟨K, Exchange.out _ m b (mem_of_induces_some r) ‹_›, some m, r⟩
      · cases hr
  | feed h y x o h' hy hr _ ih =>
    intro K p
    unfold routeComp at hr
    split at hr
    · rename_i x' hx
      cases hr
      exact ih K (pending_feed p hy hx)
    · rename_i m hm
      split at hr
      · cases hr
      · rename_i n hn
        cases hr
        have r := (p (some m) h).mpr (Exchange.out _ y m hy hm)
        obtain ⟨K', l', rest⟩ := ih (K ++ [n]) (pending_snoc r)
        exact ⟨K', Exchange.feed _ m n _ _ (mem_of_induces_some r) hn l', rest⟩

theorem joint_of_outer {K o K'} (l : Exchange F r₂ K o K') :
    ∀ T₀, Pending (s := s) (r₁ := r₁) (i₁ := i₁) K T₀ →
      ∀ o₁ T', Induces s r₁ i₁ K' o₁ T' → Exchange s RJ T₀ o T' := by
  induction l with
  | silent K hd =>
    intro T₀ p o₁ T' r
    cases o₁ with
    | none => exact joint_of_inner ((p _ _).mp r) ⟨rfl, rfl⟩
    | some m => exact (hd (Part.dom_iff_mem.mpr ⟨_, mem_of_induces_some r⟩)).elim
  | out K m b hm hb =>
    intro T₀ p o₁ T' r
    obtain ⟨T₁, r₁'⟩ := mem_interconnect.mp hm
    obtain ⟨rfl, rfl⟩ := r₁'.det r
    exact joint_of_inner ((p _ _).mp r₁') (Or.inl ⟨b, hb, rfl, rfl⟩)
  | feed K m n o K' hm hn _ ih =>
    intro T₀ p o₁ T' r
    obtain ⟨T₁, r₁'⟩ := mem_interconnect.mp hm
    exact joint_of_inner ((p _ _).mp r₁')
      (Or.inr ⟨n, hn, ih _ (pending_snoc r₁') o₁ T' r⟩)

theorem induces_joint_iff {u o T} :
    Induces s RJ (i₁ ∘ i₂) u o T ↔
      ∃ K, Induces F r₂ i₂ u o K ∧ ∃ o₁, Induces s r₁ i₁ K o₁ T := by
  induction u using List.reverseRecOn generalizing o T with
  | nil =>
    rw [induces_nil_iff]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨[], Induces.nil, none, Induces.nil⟩
    · rintro ⟨K, r, o₁, r'⟩
      obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
      obtain ⟨-, rfl⟩ := induces_nil_iff.mp r'
      exact ⟨rfl, rfl⟩
  | append_singleton u a ih =>
    rw [induces_snoc_iff]
    constructor
    · rintro ⟨o₀, T₀, r₀, l⟩
      obtain ⟨K, rK, o₁, rT⟩ := ih.mp r₀
      obtain ⟨K', l', rest⟩ := outer_of_joint l _ (pending_snoc (n := i₂ a) rT)
      exact ⟨K', induces_snoc_iff.mpr ⟨o₀, K, rK, l'⟩, rest⟩
    · rintro ⟨K', r, o₁, r'⟩
      obtain ⟨o₀, K, rK, l⟩ := induces_snoc_iff.mp r
      obtain ⟨e, rfl⟩ := l.extends
      obtain ⟨o₂, T₀, rT⟩ := Induces.prefix (e := [i₂ a] ++ e) (by simpa using r')
      exact ⟨o₀, T₀, ih.mpr ⟨K, rK, o₂, rT⟩,
        joint_of_outer l _ (pending_snoc rT) o₁ T r'⟩

/-- **Vanishing.** Closing `r₁` and then `r₂` is the same as closing the
composed routing table at once. No hypothesis is needed. -/
theorem interconnect_interconnect :
    interconnect (interconnect s r₁ i₁) r₂ i₂ = interconnect s (routeComp r₁ i₁ r₂) (i₁ ∘ i₂) := by
  apply system_ext
  intro u b
  rw [mem_interconnect, mem_interconnect]
  constructor
  · rintro ⟨K, r⟩
    have hK : ∃ o₁ T, Induces s r₁ i₁ K o₁ T := by
      have hd : ∀ {K₀ K'}, Exchange F r₂ K₀ (some b) K' → (F K').Dom := by
        intro K₀ K' l
        generalize hb : (some b : Option B) = ob at l
        induction l with
        | silent => cases hb
        | out _ m _ hm _ => exact Part.dom_iff_mem.mpr ⟨m, hm⟩
        | feed _ _ _ _ _ _ _ _ ih => exact ih hb
      have hdK : (F K).Dom := by
        induction u using List.reverseRecOn with
        | nil => cases (induces_nil_iff.mp r).1
        | append_singleton u a _ =>
          obtain ⟨_, _, _, l⟩ := induces_snoc_iff.mp r
          exact hd l
      obtain ⟨T, rT⟩ := mem_interconnect.mp (Part.get_mem hdK)
      exact ⟨_, T, rT⟩
    obtain ⟨o₁, T, rT⟩ := hK
    exact ⟨T, induces_joint_iff.mpr ⟨K, r, o₁, rT⟩⟩
  · rintro ⟨T, r⟩
    obtain ⟨K, rK, -⟩ := induces_joint_iff.mp r
    exact ⟨K, rK⟩

end Vanishing

/-! ## Relabeling and wiring -/

section Naturality

variable (s : System X Y) (route : Y → B ⊕ X) (inj : A → X)

/-- Relabeling the exposed side of a wired system relabels its routing table. -/
theorem relabel_interconnect {A' B' : Type} (f : A' → A) (g : B → B') :
    relabel (interconnect s route inj) f g = interconnect s (fun y => (route y).map g id) (inj ∘ f) := by
  have hl : ∀ {h o h'}, Exchange s route h o h' →
      Exchange s (fun y => (route y).map g id) h (o.map g) h' := by
    intro h o h' l
    induction l with
    | silent h hd => exact Exchange.silent _ hd
    | out h y b hy hr => exact Exchange.out _ y (g b) hy (by simp [hr])
    | feed h y x _ _ hy hr _ ih => exact Exchange.feed _ y x _ _ hy (by simp [hr]) ih
  have hr : ∀ {u o H}, Induces s route inj (u.map f) o H →
      Induces s (fun y => (route y).map g id) (inj ∘ f) u (o.map g) H := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro o H r
      obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
      exact Induces.nil
    | append_singleton u a ih =>
      intro o H r
      rw [List.map_append, List.map_singleton] at r
      obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r
      exact Induces.snoc _ _ _ _ _ _ (ih r₀) (hl l)
  -- every induced history of the relabeled table comes from one of the original table
  have hl' : ∀ {h o' h'}, Exchange s (fun y => (route y).map g id) h o' h' →
      ∃ o, Exchange s route h o h' ∧ o' = o.map g := by
    intro h o' h' l
    induction l with
    | silent h hd => exact ⟨none, Exchange.silent _ hd, rfl⟩
    | out h y b hy hr =>
      cases e : route y with
      | inl b₀ => rw [e] at hr; cases hr; exact ⟨some b₀, Exchange.out _ y b₀ hy e, rfl⟩
      | inr x => rw [e] at hr; cases hr
    | feed h y x _ _ hy hr _ ih =>
      obtain ⟨o, l, rfl⟩ := ih
      cases e : route y with
      | inl b₀ => rw [e] at hr; cases hr
      | inr x₀ => rw [e] at hr; cases hr; exact ⟨o, Exchange.feed _ y x₀ _ _ hy e l, rfl⟩
  have hr' : ∀ {u o' H}, Induces s (fun y => (route y).map g id) (inj ∘ f) u o' H →
      ∃ o, Induces s route inj (u.map f) o H ∧ o' = o.map g := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro o' H r
      obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
      exact ⟨none, Induces.nil, rfl⟩
    | append_singleton u a ih =>
      intro o' H r
      obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r
      obtain ⟨o₁, r₁, -⟩ := ih r₀
      obtain ⟨o, l', e⟩ := hl' l
      refine ⟨o, ?_, e⟩
      rw [List.map_append, List.map_singleton]
      exact Induces.snoc _ _ _ _ _ _ r₁ l'
  apply system_ext
  intro u b'
  simp only [relabel, Part.mem_map_iff, mem_interconnect]
  constructor
  · rintro ⟨b, ⟨H, r⟩, rfl⟩
    exact ⟨H, hr r⟩
  · rintro ⟨H, r⟩
    obtain ⟨o, r', e⟩ := hr' r
    cases o with
    | none => cases e
    | some b => cases e; exact ⟨b, ⟨H, r'⟩, rfl⟩

/-- An induced history of a relabeled system maps to one of the system itself. -/
theorem induces_relabel {X' Y' : Type} {s : System X Y} {f : X' → X} {g : Y → Y'}
    {route : Y' → B ⊕ X'} {inj : A → X'} {u o H}
    (r : Induces (relabel s f g) route inj u o H) :
    Induces s (fun y => (route (g y)).map id f) (f ∘ inj) u o (H.map f) := by
  have hl : ∀ {h o h'}, Exchange (relabel s f g) route h o h' →
      Exchange s (fun y => (route (g y)).map id f) (h.map f) o (h'.map f) := by
    intro h o h' l
    induction l with
    | silent h hd => exact Exchange.silent _ (by simpa [relabel] using hd)
    | out h y b hy hr =>
      obtain ⟨y₀, hy₀, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      exact Exchange.out _ y₀ b hy₀ (by simp [hr])
    | feed h y x _ _ hy hr _ ih =>
      obtain ⟨y₀, hy₀, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      exact Exchange.feed _ y₀ (f x) _ _ hy₀ (by simp [hr]) (by simpa using ih)
  induction u using List.reverseRecOn generalizing o H with
  | nil =>
    obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
    exact Induces.nil
  | append_singleton u a ih =>
    obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r
    exact Induces.snoc _ _ _ _ _ _ (ih r₀) (by simpa using hl l)

theorem Converges.relabel {X' Y' : Type} {s : System X Y} {f : X' → X} {g : Y → Y'}
    {route : Y' → B ⊕ X'} {inj : A → X'} (hc : Converges (SystemAlgebra.relabel s f g) route inj) :
    Converges s (fun y => (route (g y)).map id f) (f ∘ inj) := fun u => by
  obtain ⟨o, H, r⟩ := hc u
  exact ⟨o, _, induces_relabel r⟩

/-- Relabeling the inside of a wired system is absorbed by the routing table. -/
theorem interconnect_relabel {X' Y' : Type} (s : System X Y) (f : X' → X) (g : Y → Y')
    (route : Y' → B ⊕ X') (inj : A → X') :
    interconnect (relabel s f g) route inj =
      interconnect s (fun y => (route (g y)).map id f) (f ∘ inj) := by
  have hl : ∀ {h o h'}, Exchange (relabel s f g) route h o h' →
      Exchange s (fun y => (route (g y)).map id f) (h.map f) o (h'.map f) := by
    intro h o h' l
    induction l with
    | silent h hd => exact Exchange.silent _ (by simpa [relabel] using hd)
    | out h y b hy hr =>
      obtain ⟨y₀, hy₀, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      exact Exchange.out _ y₀ b hy₀ (by simp [hr])
    | feed h y x _ _ hy hr _ ih =>
      obtain ⟨y₀, hy₀, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      exact Exchange.feed _ y₀ (f x) _ _ hy₀ (by simp [hr]) (by simpa using ih)
  have hr : ∀ {u o H}, Induces (relabel s f g) route inj u o H →
      Induces s (fun y => (route (g y)).map id f) (f ∘ inj) u o (H.map f) := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro o H r
      obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
      exact Induces.nil
    | append_singleton u a ih =>
      intro o H r
      obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r
      exact Induces.snoc _ _ _ _ _ _ (ih r₀) (by simpa using hl l)
  have hl' : ∀ {T o T'}, Exchange s (fun y => (route (g y)).map id f) T o T' →
      ∀ h, T = h.map f → ∃ h', T' = h'.map f ∧ Exchange (relabel s f g) route h o h' := by
    intro T o T' l
    induction l with
    | silent T hd =>
      rintro h rfl
      exact ⟨h, rfl, Exchange.silent _ (by simpa [relabel] using hd)⟩
    | out T y b hy hr =>
      rintro h rfl
      refine ⟨h, rfl, Exchange.out _ (g y) b (Part.mem_map_iff _ |>.mpr ⟨y, hy, rfl⟩) ?_⟩
      cases e : route (g y) with
      | inl b₀ => rw [e] at hr; cases hr; rfl
      | inr x => rw [e] at hr; cases hr
    | feed T y x _ _ hy hr _ ih =>
      rintro h rfl
      cases e : route (g y) with
      | inl b₀ => rw [e] at hr; cases hr
      | inr x₀ =>
        rw [e] at hr; cases hr
        obtain ⟨h', rfl, l⟩ := ih (h ++ [x₀]) (by simp)
        exact ⟨h', rfl, Exchange.feed _ (g y) x₀ _ _
          (Part.mem_map_iff _ |>.mpr ⟨y, hy, rfl⟩) e l⟩
  have hr' : ∀ {u o T}, Induces s (fun y => (route (g y)).map id f) (f ∘ inj) u o T →
      ∃ H, T = H.map f ∧ Induces (relabel s f g) route inj u o H := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      intro o T r
      obtain ⟨rfl, rfl⟩ := induces_nil_iff.mp r
      exact ⟨[], rfl, Induces.nil⟩
    | append_singleton u a ih =>
      intro o T r
      obtain ⟨o₀, T₀, r₀, l⟩ := induces_snoc_iff.mp r
      obtain ⟨H₀, rfl, r₁⟩ := ih r₀
      obtain ⟨H, rfl, l'⟩ := hl' l (H₀ ++ [inj a]) (by simp)
      exact ⟨H, rfl, Induces.snoc _ _ _ _ _ _ r₁ l'⟩
  apply system_ext
  intro u b
  rw [mem_interconnect, mem_interconnect]
  constructor
  · rintro ⟨H, r⟩; exact ⟨_, hr r⟩
  · rintro ⟨T, r⟩
    obtain ⟨H, -, r'⟩ := hr' r
    exact ⟨H, r'⟩

end Naturality

/-! ## Wiring without feedback -/

section NoFeedback

variable {s : System X Y} {route : Y → B ⊕ X} {inj : A → X} {g : Y → B}

/-- A routing that feeds nothing back: the wiring is a relabeling. -/
theorem interconnect_no_feedback (hs : SilentAtEmpty s) (hr : ∀ y, route y = .inl (g y)) :
    interconnect s route inj = relabel s inj g := by
  have ex : ∀ H, ∃ o, Exchange s route H o H := by
    intro H
    by_cases hd : (s H).Dom
    · exact ⟨_, Exchange.out H _ _ (Part.get_mem hd) (hr _)⟩
    · exact ⟨none, Exchange.silent H hd⟩
  have ind : ∀ u, ∃ o, Induces s route inj u o (u.map inj) := by
    intro u
    induction u using List.reverseRecOn with
    | nil => exact ⟨none, Induces.nil⟩
    | append_singleton u a ih =>
      obtain ⟨o, r⟩ := ih
      obtain ⟨o', l⟩ := ex (u.map inj ++ [inj a])
      exact ⟨o', by simpa using Induces.snoc _ _ _ _ _ _ r l⟩
  funext u
  apply Part.ext
  intro b
  rw [mem_interconnect]
  rcases List.eq_nil_or_concat u with rfl | ⟨u, a, rfl⟩
  · simp only [relabel, List.map_nil]
    constructor
    · rintro ⟨H, r⟩; cases (induces_nil_iff.mp r).1
    · intro hb
      obtain ⟨y, hy, -⟩ := Part.mem_map_iff _ |>.mp hb
      exact (hs (Part.dom_iff_mem.mpr ⟨y, hy⟩)).elim
  · rw [List.concat_eq_append]
    simp only [relabel, List.map_append, List.map_singleton]
    obtain ⟨o₀, r₀⟩ := ind u
    constructor
    · rintro ⟨H, r⟩
      obtain ⟨o₁, H₀, r₁, l⟩ := induces_snoc_iff.mp r
      obtain ⟨-, rfl⟩ := r₁.det r₀
      cases l with
      | out _ y _ hy hb => rw [hr] at hb; cases hb; exact Part.mem_map _ hy
      | feed _ y _ _ _ _ hb _ => rw [hr] at hb; cases hb
    · intro hb
      obtain ⟨y, hy, rfl⟩ := Part.mem_map_iff _ |>.mp hb
      exact ⟨_, Induces.snoc _ _ _ _ _ _ r₀ (Exchange.out _ y _ hy (hr y))⟩

end NoFeedback

/-! ## A sufficient condition for convergence -/

section Termination

variable {s : System X Y} {route : Y → B ⊕ X}

/-- Exchanges stop when every continued feedback step decreases a measure. -/
theorem exchanges_of_measure (μ : List X → ℕ)
    (hμ : ∀ H y x, y ∈ s H → route y = Sum.inr x → (s (H ++ [x])).Dom → μ (H ++ [x]) < μ H)
    (H : List X) : ∃ o H', Exchange s route H o H' := by
  induction h : μ H using Nat.strong_induction_on generalizing H with
  | _ n ih =>
    by_cases hd : (s H).Dom
    · obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
      cases e : route y with
      | inl b => exact ⟨_, _, Exchange.out _ y b hy e⟩
      | inr x =>
        by_cases hd' : (s (H ++ [x])).Dom
        · obtain ⟨o, H', l⟩ := ih _ (h ▸ hμ H y x hy e hd') (H ++ [x]) rfl
          exact ⟨o, H', Exchange.feed _ y x _ _ hy e l⟩
        · exact ⟨none, _, Exchange.feed _ y x _ _ hy e (Exchange.silent _ hd')⟩
    · exact ⟨none, H, Exchange.silent _ hd⟩

/-- T2 (first half): the internal exchanges of a terminating system stop. -/
theorem Terminating.converges {s : System X Y} (hs : Terminating s) (route : Y → B ⊕ X)
    (inj : A → X) : Converges s route inj := by
  obtain ⟨μ, hμ⟩ := hs
  exact converges_of_exchanges (exchanges_of_measure μ (fun H y x _ _ hd => hμ H x hd))

end Termination

/-! ## n-ary parallel composition (spec §3) -/

section Par

variable {K : Type} {A B : K → Type}

/-- The inputs of `h` addressed to component `k`, with the tags removed. -/
noncomputable def restrict (k : K) : List (Σ k, A k) → List (A k)
  | [] => []
  | x :: h => if e : x.1 = k then (e ▸ x.2) :: restrict k h else restrict k h

@[simp] theorem restrict_nil (k : K) : restrict k ([] : List (Σ k, A k)) = [] := rfl

@[simp] theorem restrict_cons_self (k : K) (a : A k) (h : List (Σ k, A k)) :
    restrict k (⟨k, a⟩ :: h) = a :: restrict k h := by
  simp [restrict]

@[simp] theorem restrict_cons_ne {k k' : K} (hk : k' ≠ k) (a : A k') (h : List (Σ k, A k)) :
    restrict k (⟨k', a⟩ :: h) = restrict k h := by
  simp [restrict, hk]

@[simp] theorem restrict_append (k : K) (h h' : List (Σ k, A k)) :
    restrict k (h ++ h') = restrict k h ++ restrict k h' := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨k', a⟩ := x
    by_cases hk : k' = k
    · subst hk; simp [ih]
    · simp [hk, ih]

theorem length_restrict_le (k : K) (h : List (Σ k, A k)) : (restrict k h).length ≤ h.length := by
  induction h with
  | nil => simp
  | cons x h ih =>
    obtain ⟨k', a⟩ := x
    by_cases hk : k' = k
    · subst hk; simpa using ih
    · simpa [hk] using ih.trans (Nat.le_succ _)

theorem length_restrict_singleton (k : K) (x : Σ k, A k) :
    (restrict k [x]).length = if x.1 = k then 1 else 0 := by
  obtain ⟨k', a⟩ := x
  by_cases hk : k' = k
  · subst hk; simp
  · simp [hk]

/-- A history has as many inputs as its components together. -/
theorem length_eq_sum_restrict [Fintype K] (h : List (Σ k, A k)) :
    h.length = ∑ k, (restrict k h).length := by
  classical
  induction h with
  | nil => simp
  | cons x h ih =>
    obtain ⟨k', a⟩ := x
    have step : ∀ k, (restrict k (⟨k', a⟩ :: h)).length =
        (restrict k h).length + if k' = k then 1 else 0 := by
      intro k
      by_cases hk : k' = k
      · subst hk; simp
      · simp [hk]
    rw [List.length_cons, ih, Finset.sum_congr rfl fun k _ => step k, Finset.sum_add_distrib,
      Finset.sum_eq_single k' (fun k _ hk => if_neg (Ne.symm hk)) (by simp), if_pos rfl]

/-- Parallel composition: an input `⟨k, a⟩` is answered by component `k` on
its own restricted history. Undefined on the empty history. -/
noncomputable def parAll (s : ∀ k, System (A k) (B k)) : System (Σ k, A k) (Σ k, B k) :=
  fun h =>
    match h.getLast? with
    | none => Part.none
    | some x => (s x.1 (restrict x.1 h)).map (Sigma.mk x.1)

variable (s : ∀ k, System (A k) (B k))

@[simp] theorem parAll_nil : parAll s [] = Part.none := rfl

theorem parAll_snoc (h : List (Σ k, A k)) (k : K) (a : A k) :
    parAll s (h ++ [⟨k, a⟩]) = (s k (restrict k h ++ [a])).map (Sigma.mk k) := by
  simp [parAll]

theorem parAll_silentAtEmpty : SilentAtEmpty (parAll s) := by
  simp [SilentAtEmpty]

/-- Reverse induction on histories, split by the component of the last input. -/
theorem parAll_ext {S : System (Σ k, A k) (Σ k, B k)} {T : System (Σ k, A k) (Σ k, B k)}
    (h0 : S [] = T []) (h1 : ∀ h k a, S (h ++ [⟨k, a⟩]) = T (h ++ [⟨k, a⟩])) : S = T := by
  funext h
  induction h using List.reverseRecOn with
  | nil => exact h0
  | append_singleton h x _ => exact h1 h x.1 x.2

/-- P3: relabeling distributes over parallel composition. -/
theorem parAll_relabel {A' B' : K → Type} (f : ∀ k, A' k → A k) (g : ∀ k, B k → B' k) :
    parAll (fun k => relabel (s k) (f k) (g k)) =
      relabel (parAll s) (Sigma.map id f) (Sigma.map id g) := by
  have hr : ∀ (k : K) (h : List (Σ k, A' k)),
      restrict k (h.map (Sigma.map id f)) = (restrict k h).map (f k) := by
    intro k h
    induction h with
    | nil => rfl
    | cons x h ih =>
      obtain ⟨k', a⟩ := x
      by_cases hk : k' = k
      · subst hk; simp [Sigma.map, ih]
      · simp [Sigma.map, hk, ih]
  apply parAll_ext
  · simp [relabel]
  · intro h k a
    simp [relabel, parAll_snoc, hr, Part.map_map, Sigma.map, Function.comp_def]

/-- Flatten a doubly tagged message. -/
def flatMsg {L : K → Type} {A : ∀ k, L k → Type} (x : Σ k, Σ l, A k l) :
    Σ p : Σ k, L k, A p.1 p.2 := ⟨⟨x.1, x.2.1⟩, x.2.2⟩

/-- Nest a message tagged by a pair. -/
def nestMsg {L : K → Type} {A : ∀ k, L k → Type} (y : Σ p : Σ k, L k, A p.1 p.2) :
    Σ k, Σ l, A k l := ⟨y.1.1, ⟨y.1.2, y.2⟩⟩

/-- P2: flattening a parallel composition of parallel compositions. -/
theorem parAll_flatten {L : K → Type} {A B : ∀ k, L k → Type}
    (s : ∀ k l, System (A k l) (B k l)) :
    parAll (fun k => parAll (s k)) =
      relabel (parAll fun p : Σ k, L k => s p.1 p.2) flatMsg nestMsg := by
  have hr : ∀ (k : K) (l : L k) (h : List (Σ k, Σ l, A k l)),
      restrict l (restrict k h) = restrict (⟨k, l⟩ : Σ k, L k) (h.map flatMsg) := by
    intro k l h
    induction h with
    | nil => rfl
    | cons x h ih =>
      obtain ⟨k', l', a⟩ := x
      by_cases hk : k' = k
      · subst hk
        by_cases hl : l' = l
        · subst hl; simp [flatMsg, ih]
        · have : (⟨k', l'⟩ : Σ k, L k) ≠ ⟨k', l⟩ := by simpa using hl
          simp [flatMsg, hl, this, ih]
      · have : (⟨k', l'⟩ : Σ k, L k) ≠ ⟨k, l⟩ := by
          intro e; exact hk (congrArg Sigma.fst e)
        simp [flatMsg, hk, this, ih]
  apply parAll_ext
  · simp [relabel]
  · intro h k x
    obtain ⟨l, a⟩ := x
    simp only [relabel, List.map_append, List.map_singleton, parAll_snoc, Part.map_map]
    rw [show flatMsg (⟨k, ⟨l, a⟩⟩ : Σ k, Σ l, A k l) = ⟨⟨k, l⟩, a⟩ from rfl, parAll_snoc, ← hr]
    rw [Part.map_map]
    rfl

/-- P1: reindexing a parallel composition along a bijection of indices. -/
theorem parAll_reindex {K' : Type} (τ : K' ≃ K) :
    parAll (fun k' => s (τ k')) =
      relabel (parAll s) (Equiv.sigmaCongrLeft τ (β := A))
        (Equiv.sigmaCongrLeft τ (β := B)).symm := by
  have hr : ∀ (k' : K') (h : List (Σ k', A (τ k'))),
      restrict (τ k') (h.map (Equiv.sigmaCongrLeft τ (β := A))) = restrict k' h := by
    intro k' h
    induction h with
    | nil => rfl
    | cons x h ih =>
      obtain ⟨k'', a⟩ := x
      rw [List.map_cons, show (Equiv.sigmaCongrLeft τ (β := A)) ⟨k'', a⟩ = ⟨τ k'', a⟩ from rfl]
      by_cases hk : k'' = k'
      · subst hk; rw [restrict_cons_self, restrict_cons_self, ih]
      · have : τ k'' ≠ τ k' := fun e => hk (τ.injective e)
        rw [restrict_cons_ne this, restrict_cons_ne hk, ih]
  apply parAll_ext
  · simp [relabel]
  · intro h k' a
    have e : (Equiv.sigmaCongrLeft τ (β := A)) ⟨k', a⟩ = ⟨τ k', a⟩ := rfl
    simp only [relabel, List.map_append, List.map_singleton, e, parAll_snoc, hr, Part.map_map]
    congr 1
    funext b
    apply (Equiv.sigmaCongrLeft τ (β := B)).injective
    simp

end Par

/-! ## Locality (spec §6, C3) -/

section Locality

variable {K : Type} {A B : K → Type} {A₀ B₀ : Type}

/-- A family with one distinguished component `none`. -/
abbrev optF (Z : Type) (F : K → Type) : Option K → Type
  | none => Z
  | some k => F k

/-- A family of systems with one distinguished component `none`. -/
def optS {Z W : Type} (s₀ : System Z W) (t : ∀ k, System (A k) (B k)) :
    ∀ o, System (optF Z A o) (optF W B o)
  | none => s₀
  | some k => t k

@[simp] theorem restrict_none_cons_none {Z : Type} (z : Z) (h : List (Σ o, optF Z A o)) :
    restrict (A := optF Z A) none (⟨none, z⟩ :: h) = z :: restrict none h :=
  restrict_cons_self (A := optF Z A) none z h

@[simp] theorem restrict_some_cons_none {Z : Type} (k : K) (z : Z) (h : List (Σ o, optF Z A o)) :
    restrict (A := optF Z A) (some k) (⟨none, z⟩ :: h) = restrict (some k) h :=
  restrict_cons_ne (A := optF Z A) (k := some k) (k' := none) (by simp) z h

@[simp] theorem restrict_none_cons_some {Z : Type} (k : K) (a : A k) (h : List (Σ o, optF Z A o)) :
    restrict (A := optF Z A) none (⟨some k, a⟩ :: h) = restrict none h :=
  restrict_cons_ne (A := optF Z A) (k := none) (k' := some k) (by simp) a h

@[simp] theorem restrict_some_cons_some {Z : Type} (k : K) (a : A k) (h : List (Σ o, optF Z A o)) :
    restrict (A := optF Z A) (some k) (⟨some k, a⟩ :: h) = a :: restrict (some k) h :=
  restrict_cons_self (A := optF Z A) (some k) a h

@[simp] theorem restrict_some_cons_some_ne {Z : Type} {k k' : K} (hk : k' ≠ k) (a : A k')
    (h : List (Σ o, optF Z A o)) :
    restrict (A := optF Z A) (some k) (⟨some k', a⟩ :: h) = restrict (some k) h :=
  restrict_cons_ne (A := optF Z A) (k := some k) (k' := some k') (by simpa using hk) a h

variable (route : Y → B₀ ⊕ X) (inj : A₀ → X)

/-- Wire component `none` by `route`; expose every other component. -/
def routeOpt : (Σ o, optF Y B o) → (Σ o, optF B₀ B o) ⊕ (Σ o, optF X A o)
  | ⟨none, y⟩ => (route y).elim (fun b => .inl ⟨none, b⟩) (fun x => .inr ⟨none, x⟩)
  | ⟨some k, b⟩ => .inl ⟨some k, b⟩

/-- External inputs of component `none` enter through `inj`. -/
def injOpt : (Σ o, optF A₀ A o) → Σ o, optF X A o
  | ⟨none, a⟩ => ⟨none, inj a⟩
  | ⟨some k, a⟩ => ⟨some k, a⟩

variable {route inj} {s₀ : System X Y} {t : ∀ k, System (A k) (B k)}

theorem parAll_opt_none (H₁ : List (Σ o, optF X A o)) (x : X) :
    parAll (optS s₀ t) (H₁ ++ [⟨none, x⟩]) =
      (s₀ (restrict none (H₁ ++ [⟨none, x⟩]))).map (Sigma.mk none) := by
  have e := parAll_snoc (optS s₀ t) H₁ none x
  rw [e]
  simp only [restrict_append, restrict_none_cons_none, restrict_nil]
  rfl

theorem exchange_none {T₀ o T'} (l : Exchange s₀ route T₀ o T') :
    ∀ (H₁ : List (Σ o, optF X A o)) (x : X), restrict none (H₁ ++ [⟨none, x⟩]) = T₀ →
      ∃ H', Exchange (parAll (optS s₀ t)) (routeOpt route) (H₁ ++ [⟨none, x⟩])
          (o.map (Sigma.mk none)) H' ∧
        restrict none H' = T' ∧
        ∀ k, restrict (some k) H' = restrict (some k) (H₁ ++ [⟨none, x⟩]) := by
  induction l with
  | silent T hd =>
    rintro H₁ x rfl
    exact ⟨_, Exchange.silent _ (by rw [parAll_opt_none]; exact hd), rfl, fun _ => rfl⟩
  | out T y b hy hr =>
    rintro H₁ x rfl
    refine ⟨_, Exchange.out _ ⟨none, y⟩ _ ?_ (by simp only [routeOpt]; rw [hr]; rfl), rfl, fun _ => rfl⟩
    rw [parAll_opt_none]; exact Part.mem_map _ hy
  | feed T y x' o T' hy hr _ ih =>
    rintro H₁ x rfl
    obtain ⟨H', l, h1, h2⟩ := ih (H₁ ++ [⟨none, x⟩]) x' (by simp)
    refine ⟨H', Exchange.feed _ ⟨none, y⟩ ⟨none, x'⟩ _ _ ?_ (by simp only [routeOpt]; rw [hr]; rfl) l, h1,
      fun k => by rw [h2]; simp⟩
    rw [parAll_opt_none]; exact Part.mem_map _ hy

theorem exchange_some (H : List (Σ o, optF X A o)) (k : K) (a : A k) :
    ∃ o, Exchange (parAll (optS s₀ t)) (routeOpt route) (H ++ [⟨some k, a⟩]) o
        (H ++ [⟨some k, a⟩]) ∧
      ∀ c, c ∈ (t k (restrict (some k) H ++ [a])).map (Sigma.mk (some k)) ↔ o = some c := by
  have hpar : parAll (optS s₀ t) (H ++ [⟨some k, a⟩]) =
      (t k (restrict (some k) H ++ [a])).map (Sigma.mk (some k)) := parAll_snoc _ _ _ _
  by_cases hd : (t k (restrict (some k) H ++ [a])).Dom
  · obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hd
    refine ⟨some ⟨some k, b⟩, Exchange.out _ ⟨some k, b⟩ _ (by rw [hpar]; exact Part.mem_map _ hb) rfl,
      fun c => ?_⟩
    rw [Part.mem_map_iff]
    constructor
    · rintro ⟨b', hb', rfl⟩; rw [Part.mem_unique hb hb']
    · intro e; cases e; exact ⟨b, hb, rfl⟩
  · refine ⟨none, Exchange.silent _ (by rw [hpar]; exact hd), fun c => ?_⟩
    simp only [reduceCtorEq, iff_false, Part.mem_map_iff, not_exists, not_and]
    exact fun b hb _ => hd (Part.dom_iff_mem.mpr ⟨b, hb⟩)

/-- **C3, locality.** Wiring one component of a parallel composition before or
after composing gives the same system, if the wiring of that component converges. -/
theorem parAll_interconnect (hc : Converges s₀ route inj) :
    parAll (optS (interconnect s₀ route inj) t) = interconnect (parAll (optS s₀ t)) (routeOpt route) (injOpt inj) := by
  have hconv := hc
  have key : ∀ u : List (Σ o, optF A₀ A o), ∃ o H,
      Induces (parAll (optS s₀ t)) (routeOpt route) (injOpt inj) u o H ∧
      (∃ o₀, Induces s₀ route inj (restrict none u) o₀ (restrict none H)) ∧
      (∀ k, restrict (some k) H = restrict (some k) u) ∧
      ∀ c, c ∈ parAll (optS (interconnect s₀ route inj) t) u ↔ o = some c := by
    intro u
    induction u using List.reverseRecOn with
    | nil => exact ⟨none, [], Induces.nil, ⟨none, Induces.nil⟩, fun _ => rfl, by simp⟩
    | append_singleton u x ih =>
      obtain ⟨o, H, r, ⟨o₀, rs⟩, hrt, -⟩ := ih
      obtain ⟨ox, a⟩ := x
      cases ox with
      | none =>
        obtain ⟨o₁, T', rs'⟩ := hconv (restrict none u ++ [a])
        obtain ⟨o₂, T₂, rs₂, ls⟩ := induces_snoc_iff.mp rs'
        obtain ⟨-, rfl⟩ := rs.det rs₂
        obtain ⟨H', l, h1, h2⟩ := exchange_none (t := t) ls H (inj a) (by simp)
        refine ⟨_, H', Induces.snoc _ _ _ _ _ _ r l, ⟨o₁, ?_⟩, fun k => by rw [h2]; simp [hrt], ?_⟩
        · rw [h1]; simpa using rs'
        · intro c
          rw [parAll_snoc, Part.mem_map_iff]
          constructor
          · rintro ⟨b, hb, rfl⟩
            obtain ⟨H'', r'⟩ := mem_interconnect.mp hb
            rw [(rs'.det r').1]; rfl
          · intro e
            cases o₁ with
            | none => cases e
            | some b => cases e; exact ⟨b, mem_of_induces_some rs', rfl⟩
      | some k =>
        obtain ⟨o', l, ho⟩ := exchange_some (s₀ := s₀) (t := t) (route := route) H k a
        refine ⟨o', _, Induces.snoc _ _ _ _ _ _ r l, ⟨o₀, by simpa using rs⟩,
          fun k' => ?_, fun c => ?_⟩
        · simp only [restrict_append, hrt]
          by_cases e : k = k'
          · subst e; simp
          · simp [e]
        · have := ho c
          rw [hrt k] at this
          rw [parAll_snoc]
          exact this
  apply system_ext
  intro u c
  obtain ⟨o, H, r, -, -, ho⟩ := key u
  rw [ho, mem_interconnect]
  constructor
  · rintro rfl; exact ⟨H, r⟩
  · rintro ⟨H', r'⟩; exact (r.det r').1

end Locality

/-! ## Termination is preserved (spec §1.3, T1 and T2) -/

section TermClosure

/-- T1: a finite parallel composition of terminating systems terminates. -/
theorem Terminating.parAll {K : Type} [Fintype K] {A B : K → Type}
    {s : ∀ k, System (A k) (B k)} (hs : ∀ k, Terminating (s k)) :
    Terminating (SystemAlgebra.parAll s) := by
  choose μ hμ using hs
  refine ⟨fun h => ∑ k, μ k (restrict k h), fun h x hd => ?_⟩
  obtain ⟨k, a⟩ := x
  rw [parAll_snoc] at hd
  apply Finset.sum_lt_sum
  · intro k' _
    by_cases e : k = k'
    · subst e
      exact le_of_lt (by simpa using hμ k (restrict k h) a hd)
    · simp [restrict_append, restrict_cons_ne e]
  · exact ⟨k, Finset.mem_univ _, by simpa using hμ k (restrict k h) a hd⟩

theorem exchange_some_measure {s : System X Y} {route : Y → B ⊕ X} (μ : List X → ℕ)
    (hμ : ∀ h x, (s (h ++ [x])).Dom → μ (h ++ [x]) < μ h) {h o h'}
    (l : Exchange s route h o h') : ∀ b, o = some b → (s h).Dom ∧ μ h' ≤ μ h := by
  induction l with
  | silent => intro b e; cases e
  | out h y _ hy _ => intro _ _; exact ⟨Part.dom_iff_mem.mpr ⟨y, hy⟩, le_rfl⟩
  | feed h y x o h' hy _ _ ih =>
    intro b e
    obtain ⟨hd, hle⟩ := ih b e
    exact ⟨Part.dom_iff_mem.mpr ⟨y, hy⟩, le_trans hle (le_of_lt (hμ h x hd))⟩

/-- T2: wiring a terminating system gives a terminating system. -/
theorem Terminating.interconnect {s : System X Y} (hs : Terminating s) (route : Y → B ⊕ X)
    (inj : A → X) : Terminating (SystemAlgebra.interconnect s route inj) := by
  have hconv := hs.converges route inj
  obtain ⟨μ, hμ⟩ := hs
  choose o H hr using hconv
  refine ⟨fun u => μ (H u), fun u a hd => ?_⟩
  obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.get_mem hd)
  obtain ⟨-, rfl⟩ := (hr (u ++ [a])).det r'
  obtain ⟨o₀, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
  obtain ⟨-, rfl⟩ := (hr u).det r₀
  obtain ⟨hd', hle⟩ := exchange_some_measure μ hμ l _ rfl
  exact lt_of_le_of_lt hle (hμ _ _ hd')

end TermClosure

/-! ## Two components (spec §3, "Two components") -/

section Pair

variable {A₁ B₁ A₂ B₂ A₃ B₃ : Type}

/-- Alphabet of a two-component composite: `none` left, `some ()` right. -/
abbrev Two (Z W : Type) : Type := Σ o, optF Z (fun _ : Unit => W) o

/-- The two-component parallel composition `[a, b]`. -/
noncomputable def pair (a : System A₁ B₁) (b : System A₂ B₂) : System (Two A₁ A₂) (Two B₁ B₂) :=
  parAll (optS a (fun _ : Unit => b))

@[simp] theorem restrict_two_none_cons_none (z : A₁) (h : List (Two A₁ A₂)) :
    restrict none (⟨none, z⟩ :: h) = z :: restrict none h :=
  restrict_none_cons_none z h

theorem length_restrict_two (G : List (Two A₁ A₂)) :
    (restrict none G).length + (restrict (some ()) G).length = G.length := by
  induction G with
  | nil => rfl
  | cons g G ih =>
    rcases g with ⟨_ | ⟨⟨⟩⟩, g⟩
    · simp only [restrict_two_none_cons_none, restrict_cons_ne (show (none : Option Unit) ≠ some () by simp),
        List.length_cons]
      omega
    · simp only [restrict_cons_self, restrict_cons_ne (show some () ≠ (none : Option Unit) by simp),
        List.length_cons]
      omega

theorem pair_left (a : System A₁ B₁) (b : System A₂ B₂) (h : List (Two A₁ A₂)) (x : A₁) :
    pair a b (h ++ [⟨none, x⟩]) = (a (restrict none h ++ [x])).map (Sigma.mk none) :=
  parAll_snoc _ h none x

theorem pair_right (a : System A₁ B₁) (b : System A₂ B₂) (h : List (Two A₁ A₂)) (x : A₂) :
    pair a b (h ++ [⟨some (), x⟩]) = (b (restrict (some ()) h ++ [x])).map (Sigma.mk (some ())) :=
  parAll_snoc _ h (some ()) x

/-- Map each side of a two-component message. -/
def twoMap {Z Z' W W' : Type} (f : Z → Z') (g : W → W') : Two Z W → Two Z' W'
  | ⟨none, z⟩ => ⟨none, f z⟩
  | ⟨some (), w⟩ => ⟨some (), g w⟩

/-- Swap the two sides of a message. -/
def twoSwap {Z W : Type} : Two Z W → Two W Z
  | ⟨none, z⟩ => ⟨some (), z⟩
  | ⟨some (), w⟩ => ⟨none, w⟩

/-- Regroup `[[·,·],·]` messages as `[·,[·,·]]` messages. -/
def twoAssoc {Z W V : Type} : Two (Two Z W) V → Two Z (Two W V)
  | ⟨none, ⟨none, z⟩⟩ => ⟨none, z⟩
  | ⟨none, ⟨some (), w⟩⟩ => ⟨some (), ⟨none, w⟩⟩
  | ⟨some (), v⟩ => ⟨some (), ⟨some (), v⟩⟩

/-- Regroup `[·,[·,·]]` messages as `[[·,·],·]` messages. -/
def twoAssoc' {Z W V : Type} : Two Z (Two W V) → Two (Two Z W) V
  | ⟨none, z⟩ => ⟨none, ⟨none, z⟩⟩
  | ⟨some (), ⟨none, w⟩⟩ => ⟨none, ⟨some (), w⟩⟩
  | ⟨some (), ⟨some (), v⟩⟩ => ⟨some (), v⟩

theorem restrict_twoMap_none {Z Z' W W' : Type} (f : Z → Z') (g : W → W') (h : List (Two Z W)) :
    restrict none (h.map (twoMap f g)) = (restrict none h).map f := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> simp [twoMap, ih]

theorem restrict_twoMap_some {Z Z' W W' : Type} (f : Z → Z') (g : W → W') (h : List (Two Z W)) :
    restrict (some ()) (h.map (twoMap f g)) = (restrict (some ()) h).map g := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> simp [twoMap, ih]

/-- Relabeling each component of a pair. -/
theorem pair_relabel {A₁' B₁' A₂' B₂' : Type} (a : System A₁ B₁) (b : System A₂ B₂)
    (f : A₁' → A₁) (g : B₁ → B₁') (f' : A₂' → A₂) (g' : B₂ → B₂') :
    pair (relabel a f g) (relabel b f' g') = relabel (pair a b) (twoMap f f') (twoMap g g') := by
  apply parAll_ext
  · simp [relabel, pair]
  · intro h o x
    rcases o with _ | ⟨⟩
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoMap f f' ⟨none, x⟩ = ⟨none, f x⟩ from rfl]
      simp only [pair] at *
      rw [parAll_snoc, parAll_snoc]
      simp [optS, relabel, restrict_twoMap_none, Part.map_map, twoMap, Function.comp_def]
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoMap f f' ⟨some (), x⟩ = ⟨some (), f' x⟩ from rfl]
      simp only [pair] at *
      rw [parAll_snoc, parAll_snoc]
      simp [optS, relabel, restrict_twoMap_some, Part.map_map, twoMap, Function.comp_def]

theorem restrict_twoSwap_none {Z W : Type} (h : List (Two Z W)) :
    restrict none (h.map twoSwap) = restrict (some ()) h := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> simp [twoSwap, ih]

theorem restrict_twoSwap_some {Z W : Type} (h : List (Two Z W)) :
    restrict (some ()) (h.map twoSwap) = restrict none h := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> simp [twoSwap, ih]

/-- Swapping the two components of a pair. -/
theorem pair_swap (a : System A₁ B₁) (b : System A₂ B₂) :
    pair b a = relabel (pair a b) twoSwap twoSwap := by
  apply parAll_ext
  · simp [relabel, pair]
  · intro h o x
    rcases o with _ | ⟨⟩
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoSwap (⟨none, x⟩ : Two A₂ A₁) = ⟨some (), x⟩ from rfl]
      simp only [pair] at *
      rw [parAll_snoc, parAll_snoc]
      simp [optS, restrict_twoSwap_some, Part.map_map, twoSwap, Function.comp_def]
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoSwap (⟨some (), x⟩ : Two A₂ A₁) = ⟨none, x⟩ from rfl]
      simp only [pair] at *
      rw [parAll_snoc, parAll_snoc]
      simp [optS, restrict_twoSwap_none, Part.map_map, twoSwap, Function.comp_def]

theorem restrict_twoAssoc_a {Z W V : Type} (h : List (Two (Two Z W) V)) :
    restrict none (h.map twoAssoc) = restrict none (restrict none h) := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [rcases x with ⟨_ | ⟨⟩, x⟩; skip] <;> simp [twoAssoc, ih]

theorem restrict_twoAssoc_b {Z W V : Type} (h : List (Two (Two Z W) V)) :
    restrict none (restrict (some ()) (h.map twoAssoc)) = restrict (some ()) (restrict none h) := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [rcases x with ⟨_ | ⟨⟩, x⟩; skip] <;> simp [twoAssoc, ih]

theorem restrict_twoAssoc_c {Z W V : Type} (h : List (Two (Two Z W) V)) :
    restrict (some ()) (restrict (some ()) (h.map twoAssoc)) = restrict (some ()) h := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [rcases x with ⟨_ | ⟨⟩, x⟩; skip] <;> simp [twoAssoc, ih]

/-- Associativity of pairs. -/
theorem pair_assoc (a : System A₁ B₁) (b : System A₂ B₂) (c : System A₃ B₃) :
    pair (pair a b) c = relabel (pair a (pair b c)) twoAssoc twoAssoc' := by
  apply parAll_ext
  · simp [relabel, pair]
  · intro h o x
    simp only [pair] at *
    rcases o with _ | ⟨⟩
    · rcases x with ⟨_ | ⟨⟩, x⟩
      · simp only [relabel, List.map_append, List.map_singleton]
        rw [show twoAssoc (⟨none, ⟨none, x⟩⟩ : Two (Two A₁ A₂) A₃) = ⟨none, x⟩ from rfl,
          parAll_snoc, parAll_snoc]
        simp [optS, parAll_snoc, restrict_twoAssoc_a, Part.map_map, twoAssoc', Function.comp_def]
      · simp only [relabel, List.map_append, List.map_singleton]
        rw [show twoAssoc (⟨none, ⟨some (), x⟩⟩ : Two (Two A₁ A₂) A₃) = ⟨some (), ⟨none, x⟩⟩ from rfl,
          parAll_snoc, parAll_snoc]
        simp [optS, parAll_snoc, restrict_twoAssoc_b, Part.map_map, twoAssoc', Function.comp_def]
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoAssoc (⟨some (), x⟩ : Two (Two A₁ A₂) A₃) = ⟨some (), ⟨some (), x⟩⟩ from rfl,
        parAll_snoc]
      simp [optS, parAll_snoc, restrict_twoAssoc_c, Part.map_map, twoAssoc', Function.comp_def]

theorem Terminating.pair {a : System A₁ B₁} {b : System A₂ B₂} (ha : Terminating a)
    (hb : Terminating b) : Terminating (SystemAlgebra.pair a b) :=
  Terminating.parAll (fun o => by cases o <;> assumption)

theorem pair_relabel_left {A₁' B₁' : Type} (a : System A₁ B₁) (b : System A₂ B₂)
    (f : A₁' → A₁) (g : B₁ → B₁') :
    pair (relabel a f g) b = relabel (pair a b) (twoMap f id) (twoMap g id) := by
  have := pair_relabel a b f g id id
  rwa [relabel_id] at this

theorem pair_relabel_right {A₂' B₂' : Type} (a : System A₁ B₁) (b : System A₂ B₂)
    (f : A₂' → A₂) (g : B₂ → B₂') :
    pair a (relabel b f g) = relabel (pair a b) (twoMap id f) (twoMap id g) := by
  have := pair_relabel a b id id f g
  rwa [relabel_id] at this

/-- Associativity of pairs, read from right to left. -/
theorem pair_assoc' (a : System A₁ B₁) (b : System A₂ B₂) (c : System A₃ B₃) :
    pair a (pair b c) = relabel (pair (pair a b) c) twoAssoc' twoAssoc := by
  rw [pair_assoc, relabel_relabel]
  have e1 : (twoAssoc ∘ twoAssoc' : Two A₁ (Two A₂ A₃) → _) = id := by
    funext z; rcases z with ⟨_ | ⟨⟩, z⟩ <;> [skip; rcases z with ⟨_ | ⟨⟩, z⟩] <;> rfl
  have e2 : (twoAssoc ∘ twoAssoc' : Two B₁ (Two B₂ B₃) → _) = id := by
    funext z; rcases z with ⟨_ | ⟨⟩, z⟩ <;> [skip; rcases z with ⟨_ | ⟨⟩, z⟩] <;> rfl
  rw [e1, e2, relabel_id]

/-- Exchange the first two of three components of a message. -/
def twoLComm {Z W V : Type} : Two Z (Two W V) → Two W (Two Z V)
  | ⟨none, z⟩ => ⟨some (), ⟨none, z⟩⟩
  | ⟨some (), ⟨none, w⟩⟩ => ⟨none, w⟩
  | ⟨some (), ⟨some (), v⟩⟩ => ⟨some (), ⟨some (), v⟩⟩

theorem restrict_twoLComm_a {Z W V : Type} (h : List (Two Z (Two W V))) :
    restrict none (restrict (some ()) (h.map twoLComm)) = restrict none h := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [skip; rcases x with ⟨_ | ⟨⟩, x⟩] <;> simp [twoLComm, ih]

theorem restrict_twoLComm_b {Z W V : Type} (h : List (Two Z (Two W V))) :
    restrict none (h.map twoLComm) = restrict none (restrict (some ()) h) := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [skip; rcases x with ⟨_ | ⟨⟩, x⟩] <;> simp [twoLComm, ih]

theorem restrict_twoLComm_c {Z W V : Type} (h : List (Two Z (Two W V))) :
    restrict (some ()) (restrict (some ()) (h.map twoLComm)) = restrict (some ()) (restrict (some ()) h) := by
  induction h with
  | nil => rfl
  | cons x h ih => rcases x with ⟨_ | ⟨⟩, x⟩ <;> [skip; rcases x with ⟨_ | ⟨⟩, x⟩] <;> simp [twoLComm, ih]

/-- Exchanging the first two of three components. -/
theorem pair_left_comm (a : System A₁ B₁) (b : System A₂ B₂) (c : System A₃ B₃) :
    pair b (pair a c) = relabel (pair a (pair b c)) twoLComm twoLComm := by
  apply parAll_ext
  · simp [relabel, pair]
  · intro h o x
    simp only [pair] at *
    rcases o with _ | ⟨⟨⟩⟩
    · simp only [relabel, List.map_append, List.map_singleton]
      rw [show twoLComm (⟨none, x⟩ : Two A₂ (Two A₁ A₃)) = ⟨some (), ⟨none, x⟩⟩ from rfl,
        parAll_snoc]
      simp [optS, parAll_snoc, restrict_twoLComm_a, Part.map_map, twoLComm, Function.comp_def]
    · rcases x with ⟨_ | ⟨⟩, x⟩
      · simp only [relabel, List.map_append, List.map_singleton]
        rw [show twoLComm (⟨some (), ⟨none, x⟩⟩ : Two A₂ (Two A₁ A₃)) = ⟨none, x⟩ from rfl,
          parAll_snoc, parAll_snoc]
        simp [optS, parAll_snoc, restrict_twoLComm_b, Part.map_map, twoLComm, Function.comp_def]
      · simp only [relabel, List.map_append, List.map_singleton]
        rw [show twoLComm (⟨some (), ⟨some (), x⟩⟩ : Two A₂ (Two A₁ A₃)) = ⟨some (), ⟨some (), x⟩⟩ from rfl,
          parAll_snoc, parAll_snoc]
        simp [optS, parAll_snoc, restrict_twoLComm_c, Part.map_map, twoLComm, Function.comp_def]

/-- Locality on the left component of a pair. -/
theorem pair_interconnect_left {X Y B₀ A₀ : Type} {a : System X Y}
    {route : Y → B₀ ⊕ X} {inj : A₀ → X} (ha : Converges a route inj) (b : System A₂ B₂) :
    pair (interconnect a route inj) b =
      interconnect (pair a b) (routeOpt (B := fun _ : Unit => B₂) route) (injOpt (A := fun _ : Unit => A₂) inj) :=
  parAll_interconnect ha

/-- The routing table that wires the right component of a pair. -/
def routeRight {Y X B₀ : Type} (route : Y → B₀ ⊕ X) : Two B₁ Y → Two B₁ B₀ ⊕ Two A₁ X
  | ⟨none, b⟩ => .inl ⟨none, b⟩
  | ⟨some (), y⟩ => (route y).elim (fun b => .inl ⟨some (), b⟩) (fun x => .inr ⟨some (), x⟩)

/-- Locality on the right component of a pair. -/
theorem pair_interconnect_right {X Y B₀ A₀ : Type} (a : System A₁ B₁) {b : System X Y}
    {route : Y → B₀ ⊕ X} {inj : A₀ → X} (hb : Converges b route inj) :
    pair a (interconnect b route inj) = interconnect (pair a b) (routeRight route) (twoMap id inj) := by
  rw [pair_swap, pair_interconnect_left hb, relabel_interconnect, pair_swap, interconnect_relabel]
  congr 1
  · funext y
    rcases y with ⟨_ | ⟨⟩, y⟩
    · rfl
    · simp only [routeRight, twoSwap, routeOpt]
      cases route y <;> rfl
  · funext x
    rcases x with ⟨_ | ⟨⟩, x⟩ <;> rfl

/-- Exchange the middle components of a pair of pairs. -/
def twoMiddle {A B C D : Type} : Two (Two A B) (Two C D) → Two (Two A C) (Two B D)
  | ⟨none, ⟨none, a⟩⟩ => ⟨none, ⟨none, a⟩⟩
  | ⟨none, ⟨some (), b⟩⟩ => ⟨some (), ⟨none, b⟩⟩
  | ⟨some (), ⟨none, c⟩⟩ => ⟨none, ⟨some (), c⟩⟩
  | ⟨some (), ⟨some (), d⟩⟩ => ⟨some (), ⟨some (), d⟩⟩

theorem pair_middle {A B C D W X Y Z : Type}
    (a : System A W) (b : System B X) (c : System C Y) (d : System D Z) :
    pair (pair a b) (pair c d) =
      relabel (pair (pair a c) (pair b d)) twoMiddle twoMiddle := by
  rw [pair_assoc a b (pair c d), pair_left_comm c b d,
    pair_relabel_right, relabel_relabel, pair_assoc a c (pair b d), relabel_relabel]
  congr 1 <;> funext z
  · rcases z with ⟨(_ | ⟨⟩), ⟨(_ | ⟨⟩), z⟩⟩ <;> rfl
  · rcases z with ⟨(_ | ⟨⟩), z⟩
    · rfl
    · rcases z with ⟨(_ | ⟨⟩), z⟩
      · rfl
      · rcases z with ⟨(_ | ⟨⟩), z⟩ <;> rfl

end Pair

/-! ## A forwarder in the interconnect is transparent (for spec §6, I) -/

section Forwarder

variable {C D' : Type} {s : System X Y} {c : System C D'} {φ : C → D'}
  {R : Two Y D' → B ⊕ Two X C} {inj : A → Two X C} {f : A → X} {g : Y → B}

/-- A reactive, memoryless forwarder: it answers every input `x` with `φ x`. -/
def Forwarder (c : System C D') (φ : C → D') : Prop :=
  SilentAtEmpty c ∧ ∀ h x, c (h ++ [x]) = Part.some (φ x)

/-- The routing conditions under which the forwarder is transparent: an
external input reaches `s` directly or through one hop of the forwarder, and
every output of `s` leaves directly or through one hop of the forwarder. -/
def Transparent (R : Two Y D' → B ⊕ Two X C) (inj : A → Two X C) (φ : C → D')
    (f : A → X) (g : Y → B) : Prop :=
  (∀ a, inj a = ⟨none, f a⟩ ∨ ∃ x, inj a = ⟨some (), x⟩ ∧
      R ⟨some (), φ x⟩ = .inr ⟨none, f a⟩) ∧
  (∀ y, R ⟨none, y⟩ = .inl (g y) ∨
    ∃ x, R ⟨none, y⟩ = .inr ⟨some (), x⟩ ∧ R ⟨some (), φ x⟩ = .inl (g y))

theorem exchange_forward (hc : Forwarder c φ) (hT : Transparent R inj φ f g)
    (H₁ : List (Two X C)) (x : X) :
    ∃ o H', Exchange (pair s c) R (H₁ ++ [⟨none, x⟩]) o H' ∧
      restrict none H' = restrict none (H₁ ++ [⟨none, x⟩]) ∧
      ∀ b, b ∈ (s (restrict none (H₁ ++ [⟨none, x⟩]))).map g ↔ o = some b := by
  have hp : pair s c (H₁ ++ [⟨none, x⟩]) = (s (restrict none (H₁ ++ [⟨none, x⟩]))).map (Sigma.mk none) := by
    rw [pair_left]; simp
  by_cases hd : (s (restrict none (H₁ ++ [⟨none, x⟩]))).Dom
  · obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hd
    have hy' : (⟨none, y⟩ : Two Y D') ∈ pair s c (H₁ ++ [⟨none, x⟩]) := by
      rw [hp]; exact Part.mem_map _ hy
    have hb : ∀ b, b ∈ (s (restrict none (H₁ ++ [⟨none, x⟩]))).map g ↔ some (g y) = some b := by
      intro b
      rw [Part.mem_map_iff]
      constructor
      · rintro ⟨y', hy'', rfl⟩; rw [Part.mem_unique hy hy'']
      · intro e; cases e; exact ⟨y, hy, rfl⟩
    rcases hT.2 y with e | ⟨x', e, e'⟩
    · exact ⟨_, _, Exchange.out _ _ _ hy' e, rfl, hb⟩
    · refine ⟨_, H₁ ++ [⟨none, x⟩] ++ [⟨some (), x'⟩],
        Exchange.feed _ _ _ _ _ hy' e (Exchange.out _ ⟨some (), φ x'⟩ _ ?_ e'), by simp, hb⟩
      rw [pair_right, hc.2]
      exact Part.mem_map _ (Part.mem_some _)
  · refine ⟨none, _, Exchange.silent _ (by rw [hp]; exact hd), rfl, fun b => ?_⟩
    simp only [reduceCtorEq, iff_false, Part.mem_map_iff, not_exists, not_and]
    exact fun y hy _ => hd (Part.dom_iff_mem.mpr ⟨y, hy⟩)

theorem exchange_input (hc : Forwarder c φ) (hT : Transparent R inj φ f g)
    (H : List (Two X C)) (a : A) :
    ∃ o H', Exchange (pair s c) R (H ++ [inj a]) o H' ∧
      restrict none H' = restrict none H ++ [f a] ∧
      ∀ b, b ∈ (s (restrict none H ++ [f a])).map g ↔ o = some b := by
  rcases hT.1 a with e | ⟨x, e, e'⟩
  · rw [e]
    obtain ⟨o, H', l, h1, h2⟩ := exchange_forward (s := s) hc hT H (f a)
    exact ⟨o, H', l, by simpa using h1, by simpa using h2⟩
  · obtain ⟨o, H', l, h1, h2⟩ := exchange_forward (s := s) hc hT (H ++ [⟨some (), x⟩]) (f a)
    refine ⟨o, H', ?_, by simpa using h1, by simpa using h2⟩
    rw [e]
    refine Exchange.feed _ ⟨some (), φ x⟩ ⟨none, f a⟩ _ _ ?_ e' l
    rw [pair_right, hc.2]
    exact Part.mem_map _ (Part.mem_some _)

/-- A forwarder wired to a reactive `s` is transparent. -/
theorem interconnect_forwarder (hs : SilentAtEmpty s) (hc : Forwarder c φ) (hT : Transparent R inj φ f g) :
    interconnect (pair s c) R inj = relabel s f g := by
  have key : ∀ u, ∃ o H, Induces (pair s c) R inj u o H ∧ restrict none H = u.map f ∧
      ∀ b, b ∈ relabel s f g u ↔ o = some b := by
    intro u
    induction u using List.reverseRecOn with
    | nil =>
      refine ⟨none, [], Induces.nil, rfl, fun b => ?_⟩
      simp only [relabel, List.map_nil, reduceCtorEq, iff_false, Part.mem_map_iff, not_exists,
        not_and]
      exact fun y hy _ => hs (Part.dom_iff_mem.mpr ⟨y, hy⟩)
    | append_singleton u a ih =>
      obtain ⟨o₀, H, r, hH, -⟩ := ih
      obtain ⟨o, H', l, h1, h2⟩ := exchange_input (s := s) hc hT H a
      refine ⟨o, H', Induces.snoc _ _ _ _ _ _ r l, by simp [h1, hH], fun b => ?_⟩
      rw [← h2, hH]
      simp [relabel]
  apply system_ext
  intro u b
  obtain ⟨o, H, r, -, ho⟩ := key u
  rw [ho, mem_interconnect]
  constructor
  · rintro ⟨H', r'⟩; exact (r.det r').1
  · rintro rfl; exact ⟨H, r⟩

end Forwarder

/-! ## Behavioural equality (spec §1.4, R1–R2, B) -/

section Behaviour

variable {s t : System X Y}

@[simp] theorem reach_nil (s : System X Y) : Reach s [] := by
  intro h' e he hne
  exact (hne (List.append_eq_nil_iff.mp he.symm).1).elim

theorem reach_snoc_iff {h : List X} {x : X} :
    Reach s (h ++ [x]) ↔ Reach s h ∧ (s (h ++ [x])).Dom := by
  constructor
  · intro hr
    refine ⟨fun h' e he hne => hr h' (e ++ [x]) (by rw [he, List.append_assoc]) hne, ?_⟩
    exact hr (h ++ [x]) [] (by simp) (by simp)
  · rintro ⟨hr, hd⟩ h' e he hne
    induction e using List.reverseRecOn with
    | nil => simp at he; rw [← he]; exact hd
    | append_singleton e z _ =>
      rw [← List.append_assoc] at he
      obtain ⟨rfl, -⟩ := List.append_inj' he rfl
      exact hr h' e rfl hne

/-- For a DDS, a nonempty history is reachable exactly when it is in the domain.
Prefix closure, rather than total responsiveness, supplies all earlier replies. -/
theorem IsDDS.reach_iff (hs : IsDDS s) {h : List X} (hne : h ≠ []) :
    Reach s h ↔ (s h).Dom :=
  ⟨fun hr => hr h [] (by simp) hne,
    fun hd p e he hp => hs.2 ⟨e, he.symm⟩ hp hd⟩

/-- On DDSs, behavioral equality is equality of the partial history functions.
This includes both the domain and every defined reply. -/
theorem EqOnReachable.eq_of_isDDS (hst : s ≈ₛ t) (hs : IsDDS s) (ht : IsDDS t) : s = t := by
  apply system_ext
  intro h y
  by_cases hn : h = []
  · subst h
    exact ⟨fun hy => (hs.1 hy.1).elim, fun hy => (ht.1 hy.1).elim⟩
  · constructor
    · intro hy
      rw [← hst.2 h ((hs.reach_iff hn).mpr hy.1) hn]
      exact hy
    · intro hy
      rw [hst.2 h ((hst.1 h).mpr ((ht.reach_iff hn).mpr hy.1)) hn]
      exact hy

/-- R1: trimming does not change the behaviour. -/
theorem trim_behEq (s : System X Y) : trim s ≈ₛ s := by
  have hreach : ∀ h, Reach (trim s) h ↔ Reach s h := by
    intro h
    induction h using List.reverseRecOn with
    | nil => simp
    | append_singleton h x ih =>
      rw [reach_snoc_iff, reach_snoc_iff, ih]
      constructor
      · rintro ⟨hr, hd⟩
        refine ⟨hr, ?_⟩
        by_cases hx : Reach s (h ++ [x])
        · exact (reach_snoc_iff.mp hx).2
        · simp [trim, hx] at hd
      · rintro ⟨hr, hd⟩
        refine ⟨hr, ?_⟩
        have : Reach s (h ++ [x]) := reach_snoc_iff.mpr ⟨hr, hd⟩
        simpa [trim, this] using hd
  refine ⟨hreach, fun h hr _ => ?_⟩
  simp [trim, (hreach h).mp hr]

/-- After a reachable history, trimming preserves the next partial reply,
including undefinedness. -/
theorem trim_snoc_of_reach {h : List X} (hr : Reach s h) (x : X) :
    trim s (h ++ [x]) = s (h ++ [x]) := by
  by_cases hd : (s (h ++ [x])).Dom
  · exact if_pos (reach_snoc_iff.mpr ⟨hr, hd⟩)
  · rw [trim, if_neg (fun ht => hd (reach_snoc_iff.mp ht).2), Part.eq_none_iff'.mpr hd]

/-- R1: a trimmed system has a prefix-closed domain. -/
theorem trim_prefix_closed (s : System X Y) {h e : List X} (hd : (trim s (h ++ e)).Dom)
    (hne : h ≠ []) : (trim s h).Dom := by
  by_cases hr : Reach s (h ++ e)
  · have := hr h e rfl hne
    have hr' : Reach s h := fun h' e' he' hne' => hr h' (e' ++ e) (by rw [he', List.append_assoc]) hne'
    simpa [trim, hr'] using this
  · simp [trim, hr] at hd

/-- Restricting to reachable histories preserves a reactive system's silence at `[]`. -/
theorem SilentAtEmpty.isDDS_trim (hs : SilentAtEmpty s) : IsDDS (trim s) := by
  refine ⟨by simpa [SilentAtEmpty, trim] using hs, ?_⟩
  rintro h k ⟨e, rfl⟩ hn hd
  exact trim_prefix_closed s hd hn

/-- A DDS already has exactly its reachable nonempty histories. -/
theorem IsDDS.trim_eq (hs : IsDDS s) : trim s = s :=
  (trim_behEq s).eq_of_isDDS hs.1.isDDS_trim hs

/-- B for relabeling. -/
theorem EqOnReachable.relabel (hst : s ≈ₛ t) (f : A → X) (g : Y → B) :
    SystemAlgebra.relabel s f g ≈ₛ SystemAlgebra.relabel t f g := by
  have hr : ∀ (u : System X Y) h, Reach (SystemAlgebra.relabel u f g) h ↔ Reach u (h.map f) := by
    intro u h
    induction h using List.reverseRecOn with
    | nil => simp
    | append_singleton h x ih =>
      rw [reach_snoc_iff, List.map_append, List.map_singleton, reach_snoc_iff, ih]
      simp [SystemAlgebra.relabel]
  refine ⟨fun h => by rw [hr, hr]; exact hst.1 _, fun h hh hne => ?_⟩
  simp only [SystemAlgebra.relabel]
  rw [hst.2 _ ((hr s h).mp hh) (by simpa using hne)]

/-- Trimming commutes with a change of the input and output vocabulary. -/
theorem trim_relabel {A B X Y : Type} (s : System X Y) (f : A → X) (g : Y → B) :
    trim (relabel s f g) = relabel (trim s) f g := by
  funext h
  have hr : Reach (relabel s f g) h ↔ Reach s (h.map f) := by
    induction h using List.reverseRecOn with
    | nil => simp only [List.map_nil, reach_nil]
    | append_singleton h x ih =>
      rw [List.map_append, List.map_singleton, reach_snoc_iff, reach_snoc_iff, ih]
      simp only [relabel, List.map_append, List.map_singleton, Part.map_Dom]
  simp only [trim, relabel, hr]
  split_ifs
  · rfl
  · exact Part.map_none _ |>.symm

end Behaviour

section BehaviourPar

variable {K : Type} {A B : K → Type} {s t : ∀ k, System (A k) (B k)}

theorem reach_restrict {h : List (Σ k, A k)} (hr : Reach (parAll s) h) (k : K) :
    Reach (s k) (restrict k h) := by
  induction h using List.reverseRecOn with
  | nil => simp
  | append_singleton h x ih =>
    obtain ⟨hr0, hd⟩ := reach_snoc_iff.mp hr
    obtain ⟨k', a⟩ := x
    by_cases e : k' = k
    · subst e
      rw [parAll_snoc] at hd
      rw [restrict_append, restrict_cons_self, restrict_nil]
      exact reach_snoc_iff.mpr ⟨ih hr0, hd⟩
    · rw [restrict_append, restrict_cons_ne e, restrict_nil, List.append_nil]
      exact ih hr0

/-- A parallel transcript is reachable exactly when all its component
projections are reachable. -/
theorem reach_parAll_iff (h : List (Σ k, A k)) :
    Reach (parAll s) h ↔ ∀ k, Reach (s k) (restrict k h) := by
  refine ⟨fun hr k => reach_restrict hr k, ?_⟩
  intro hr p e he hn
  obtain ⟨p, ⟨k, a⟩, rfl⟩ := List.eq_nil_or_concat p |>.resolve_left hn
  rw [List.concat_eq_append, parAll_snoc]
  exact hr k (restrict k p ++ [a]) (restrict k e)
    (by rw [he]; simp [List.concat_eq_append]) (by simp)

/-- The reachable parallel composition of DDSs has exactly the intersection
of their projected domains, with the empty input history excluded. -/
theorem trim_parAll_dom (hs : ∀ k, IsDDS (s k)) (h : List (Σ k, A k)) :
    (trim (parAll s) h).Dom ↔ h ≠ [] ∧
      ∀ k, restrict k h = [] ∨ (s k (restrict k h)).Dom := by
  have hr : Reach (parAll s) h ↔ ∀ k, restrict k h = [] ∨ (s k (restrict k h)).Dom := by
    rw [reach_parAll_iff]
    apply forall_congr'
    intro k
    by_cases he : restrict k h = []
    · simp [he]
    · simp only [he, false_or]
      exact (hs k).reach_iff he
  constructor
  · intro hd
    have hreach : Reach (parAll s) h := by
      by_contra hn
      simp [trim, hn] at hd
    refine ⟨?_, hr.mp hreach⟩
    rintro rfl
    simp [trim, parAll] at hd
  · rintro ⟨hn, hh⟩
    have hreach := hr.mpr hh
    rw [trim, if_pos hreach]
    exact hreach h [] (by simp) hn

/-- B for parallel composition. -/
theorem EqOnReachable.parAll (hst : ∀ k, s k ≈ₛ t k) :
    SystemAlgebra.parAll s ≈ₛ SystemAlgebra.parAll t := by
  have hdom : ∀ h k a, Reach (SystemAlgebra.parAll s) h →
      ((s k (restrict k h ++ [a])).Dom ↔ (t k (restrict k h ++ [a])).Dom) := by
    intro h k a hr
    have h1 := reach_restrict hr k
    have h2 : Reach (t k) (restrict k h) := ((hst k).1 _).mp h1
    have := (hst k).1 (restrict k h ++ [a])
    rw [reach_snoc_iff, reach_snoc_iff] at this
    exact ⟨fun hd => (this.mp ⟨h1, hd⟩).2, fun hd => (this.mpr ⟨h2, hd⟩).2⟩
  have hreach : ∀ h, Reach (SystemAlgebra.parAll s) h ↔ Reach (SystemAlgebra.parAll t) h := by
    intro h
    induction h using List.reverseRecOn with
    | nil => simp
    | append_singleton h x ih =>
      obtain ⟨k, a⟩ := x
      rw [reach_snoc_iff, reach_snoc_iff, parAll_snoc, parAll_snoc]
      constructor
      · rintro ⟨hr, hd⟩; exact ⟨ih.mp hr, (hdom h k a hr).mp hd⟩
      · rintro ⟨hr, hd⟩; exact ⟨ih.mpr hr, (hdom h k a (ih.mpr hr)).mpr hd⟩
  refine ⟨hreach, fun h hr hne => ?_⟩
  induction h using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton h x _ =>
    obtain ⟨k, a⟩ := x
    obtain ⟨hr', hd⟩ := reach_snoc_iff.mp hr
    rw [parAll_snoc] at hd ⊢
    rw [parAll_snoc]
    have h1 : Reach (s k) (restrict k h ++ [a]) :=
      reach_snoc_iff.mpr ⟨reach_restrict hr' k, hd⟩
    rw [(hst k).2 _ h1 (by simp)]

/-- R2: the trimmed parallel composition of finite systems is finite. -/
theorem finite_trim_parAll [Fintype K] {n : K → ℕ} (hs : ∀ k, Finite (n k) (s k)) :
    Finite (∑ k, n k) (trim (SystemAlgebra.parAll s)) := by
  intro h hd
  have hr : Reach (SystemAlgebra.parAll s) h := by
    by_contra hr; simp [trim, hr] at hd
  have hlen : ∀ h : List (Σ k, A k), h.length = ∑ k, (restrict k h).length := by
    intro h
    induction h with
    | nil => simp
    | cons x h ih =>
      obtain ⟨k', a⟩ := x
      have : ∀ k, (restrict k (⟨k', a⟩ :: h)).length =
          (restrict k h).length + if k = k' then 1 else 0 := by
        intro k
        by_cases e : k' = k
        · subst e; simp
        · simp [restrict_cons_ne e, Ne.symm e]
      simp only [List.length_cons, this, Finset.sum_add_distrib, ih]
      simp
      rw [Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (fun h => absurd (Finset.mem_univ _) h)]
      simp
  rw [hlen]
  apply Finset.sum_le_sum
  intro k _
  have hk := reach_restrict hr k
  cases e : restrict k h using List.reverseRecOn with
  | nil => simp
  | append_singleton r a =>
    rw [e] at hk
    exact hs k _ (reach_snoc_iff.mp hk).2

end BehaviourPar

section BehaviourWire

variable {s t : System X Y} {route : Y → B ⊕ X} {inj : A → X}

theorem exchange_of_behEq (hst : s ≈ₛ t) {h₀ o h'} (l : Exchange s route h₀ o h') :
    ∀ h x, h₀ = h ++ [x] → Reach s h → Exchange t route h₀ o h' := by
  induction l with
  | silent g hd =>
    rintro h x rfl hr
    refine Exchange.silent _ fun hd' => hd ?_
    have ht : Reach t h := (hst.1 h).mp hr
    exact (reach_snoc_iff.mp ((hst.1 _).mpr (reach_snoc_iff.mpr ⟨ht, hd'⟩))).2
  | out g y b hy hb =>
    rintro h x rfl hr
    have hrx : Reach s (h ++ [x]) := reach_snoc_iff.mpr ⟨hr, Part.dom_iff_mem.mpr ⟨y, hy⟩⟩
    exact Exchange.out _ y b (by rw [← hst.2 _ hrx (by simp)]; exact hy) hb
  | feed g y x' o g' hy hb _ ih =>
    rintro h x rfl hr
    have hrx : Reach s (h ++ [x]) := reach_snoc_iff.mpr ⟨hr, Part.dom_iff_mem.mpr ⟨y, hy⟩⟩
    exact Exchange.feed _ y x' _ _ (by rw [← hst.2 _ hrx (by simp)]; exact hy) hb
      (ih (h ++ [x]) x' rfl hrx)

theorem reach_of_exchange_some {h x b h'} (l : Exchange s route (h ++ [x]) (some b) h')
    (hr : Reach s h) : Reach s h' := by
  generalize e : h ++ [x] = g at l
  generalize eb : some b = ob at l
  induction l generalizing h x with
  | silent => cases eb
  | out g y _ hy _ => subst e; exact reach_snoc_iff.mpr ⟨hr, Part.dom_iff_mem.mpr ⟨y, hy⟩⟩
  | feed g y x' _ _ hy _ _ ih =>
    subst e
    exact ih (reach_snoc_iff.mpr ⟨hr, Part.dom_iff_mem.mpr ⟨y, hy⟩⟩) rfl eb

/-- B for connection: behavioural equality is preserved by wiring, with no hypothesis. -/
theorem EqOnReachable.interconnect (hst : s ≈ₛ t) (route : Y → B ⊕ X) (inj : A → X) :
    SystemAlgebra.interconnect s route inj ≈ₛ SystemAlgebra.interconnect t route inj := by
  have hts : t ≈ₛ s := ⟨fun h => (hst.1 h).symm, fun h hr hne => (hst.2 h ((hst.1 h).mpr hr) hne).symm⟩
  -- replies after a reachable internal history agree
  have step : ∀ {u a H b}, Induces s route inj u none H ∨ (∃ o, Induces s route inj u o H) →
      Reach s H → Induces t route inj u none H ∨ (∃ o, Induces t route inj u o H) →
      (b ∈ SystemAlgebra.interconnect s route inj (u ++ [a]) ↔ b ∈ SystemAlgebra.interconnect t route inj (u ++ [a])) := by
    intro u a H b hs hr ht
    obtain ⟨os, rs⟩ : ∃ o, Induces s route inj u o H := by
      rcases hs with h | h; exact ⟨_, h⟩; exact h
    obtain ⟨ot, rt⟩ : ∃ o, Induces t route inj u o H := by
      rcases ht with h | h; exact ⟨_, h⟩; exact h
    have hrt : Reach t H := (hst.1 H).mp hr
    rw [mem_interconnect, mem_interconnect]
    constructor
    · rintro ⟨H', r'⟩
      obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
      obtain ⟨-, rfl⟩ := rs.det r₀
      exact ⟨H', induces_snoc_iff.mpr ⟨_, _, rt, exchange_of_behEq hst l _ _ rfl hr⟩⟩
    · rintro ⟨H', r'⟩
      obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
      obtain ⟨-, rfl⟩ := rt.det r₀
      exact ⟨H', induces_snoc_iff.mpr ⟨_, _, rs, exchange_of_behEq hts l _ _ rfl hrt⟩⟩
  have key : ∀ u, (Reach (SystemAlgebra.interconnect s route inj) u ↔ Reach (SystemAlgebra.interconnect t route inj) u) ∧
      (Reach (SystemAlgebra.interconnect s route inj) u →
        ∃ o H, Induces s route inj u o H ∧ Induces t route inj u o H ∧ Reach s H) := by
    intro u
    induction u using List.reverseRecOn with
    | nil => exact ⟨by simp, fun _ => ⟨none, [], Induces.nil, Induces.nil, reach_nil s⟩⟩
    | append_singleton u a ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hdom : Reach (SystemAlgebra.interconnect s route inj) u →
          ((SystemAlgebra.interconnect s route inj (u ++ [a])).Dom ↔
            (SystemAlgebra.interconnect t route inj (u ++ [a])).Dom) := by
        intro hr
        obtain ⟨o, H, rs, rt, hH⟩ := ih2 hr
        constructor
        · intro d
          exact Part.dom_iff_mem.mpr ⟨_, (step (Or.inr ⟨o, rs⟩) hH (Or.inr ⟨o, rt⟩)).mp (Part.get_mem d)⟩
        · intro d
          exact Part.dom_iff_mem.mpr ⟨_, (step (Or.inr ⟨o, rs⟩) hH (Or.inr ⟨o, rt⟩)).mpr (Part.get_mem d)⟩
      refine ⟨?_, ?_⟩
      · rw [reach_snoc_iff, reach_snoc_iff]
        constructor
        · rintro ⟨hr, hd⟩; exact ⟨ih1.mp hr, (hdom hr).mp hd⟩
        · rintro ⟨hr, hd⟩; exact ⟨ih1.mpr hr, (hdom (ih1.mpr hr)).mpr hd⟩
      · intro hr
        obtain ⟨hr0, hd⟩ := reach_snoc_iff.mp hr
        obtain ⟨o, H, rs, rt, hH⟩ := ih2 hr0
        obtain ⟨H', r'⟩ := mem_interconnect.mp (Part.get_mem hd)
        obtain ⟨_, H₀, r₀, l⟩ := induces_snoc_iff.mp r'
        obtain ⟨-, rfl⟩ := rs.det r₀
        refine ⟨_, H', r', induces_snoc_iff.mpr ⟨_, _, rt, exchange_of_behEq hst l _ _ rfl hH⟩, ?_⟩
        exact reach_of_exchange_some l hH
  refine ⟨fun u => (key u).1, fun u hr hne => ?_⟩
  induction u using List.reverseRecOn with
  | nil => exact (hne rfl).elim
  | append_singleton u a _ =>
    obtain ⟨hr0, -⟩ := reach_snoc_iff.mp hr
    obtain ⟨o, H, rs, rt, hH⟩ := (key u).2 hr0
    exact Part.ext fun b => step (Or.inr ⟨o, rs⟩) hH (Or.inr ⟨o, rt⟩)

theorem exchange_some_dom {h o h'} (l : Exchange s route h o h') : ∀ b, o = some b → (s h').Dom := by
  induction l with
  | silent => intro b e; cases e
  | out h y _ hy _ => intro _ _; exact Part.dom_iff_mem.mpr ⟨y, hy⟩
  | feed _ _ _ _ _ _ _ _ ih => exact ih

theorem Induces.length_le {u o H} (r : Induces s route inj u o H) : u.length ≤ H.length := by
  induction r with
  | nil => simp
  | snoc u a o₀ H o H' _ l ih =>
    obtain ⟨e, rfl⟩ := l.extends
    simp
    omega

theorem exchange_start_dom {h o h'} (l : Exchange s route h o h') : ∀ b, o = some b → (s h).Dom := by
  cases l with
  | silent => intro b e; cases e
  | out _ y _ hy _ => intro _ _; exact Part.dom_iff_mem.mpr ⟨y, hy⟩
  | feed _ y _ _ _ hy _ _ => intro _ _; exact Part.dom_iff_mem.mpr ⟨y, hy⟩

@[simp] theorem interconnect_nil : SystemAlgebra.interconnect s route inj [] = Part.none := interconnect_eq_none Induces.nil

theorem EqOnReachable.symm {t : System X Y} (hst : s ≈ₛ t) : t ≈ₛ s :=
  ⟨fun h => (hst.1 h).symm, fun h hr hne => (hst.2 h ((hst.1 h).mpr hr) hne).symm⟩

theorem EqOnReachable.trans {t u : System X Y} (hst : s ≈ₛ t) (htu : t ≈ₛ u) : s ≈ₛ u :=
  ⟨fun h => (hst.1 h).trans (htu.1 h),
    fun h hr hn => (hst.2 h hr hn).trans (htu.2 h ((hst.1 h).mp hr) hn)⟩

theorem EqOnReachable.trim_eq {t : System X Y} (hst : s ≈ₛ t) (hs : SilentAtEmpty s) (ht : SilentAtEmpty t) :
    trim s = trim t :=
  ((trim_behEq s).trans (hst.trans (trim_behEq t).symm)).eq_of_isDDS
    hs.isDDS_trim ht.isDDS_trim

/-- R3: connecting a finite system gives a finite system. -/
theorem Finite.interconnect {n : ℕ} (hs : Finite n s) : Finite n (SystemAlgebra.interconnect s route inj) := by
  intro u hd
  obtain ⟨H, r⟩ := mem_interconnect.mp (Part.get_mem hd)
  refine le_trans r.length_le (hs H ?_)
  induction u using List.reverseRecOn with
  | nil => cases (induces_nil_iff.mp r).1
  | append_singleton u a _ =>
    obtain ⟨_, _, _, l⟩ := induces_snoc_iff.mp r
    exact exchange_some_dom l _ rfl

end BehaviourWire

/-! ## Behavioural equality is transcript equality (spec §1.4) -/

section Transcript

/-- The transcripts of `s` with the environment `e : B* ⇀ A` (LanMau20 Def. 7):
`x_k = e(y_1 … y_{k-1})` and `y_k = s(x_1 … x_k)`. -/
inductive Transcript (s : System A B) (e : List B →. A) : List A → List B → Prop
  | nil : Transcript s e [] []
  | snoc {xs ys x y} : Transcript s e xs ys → x ∈ e ys → y ∈ s (xs ++ [x]) →
      Transcript s e (xs ++ [x]) (ys ++ [y])

variable {s t : System A B}

theorem Transcript.length_eq {e xs ys} (tr : Transcript s e xs ys) : xs.length = ys.length := by
  induction tr with
  | nil => rfl
  | snoc _ _ _ ih => simp [ih]

theorem Transcript.reach {e xs ys} (tr : Transcript s e xs ys) : Reach s xs := by
  induction tr with
  | nil => exact reach_nil s
  | snoc _ _ hy ih => exact reach_snoc_iff.mpr ⟨ih, Part.dom_iff_mem.mpr ⟨_, hy⟩⟩

theorem Transcript.snoc_inv {e xs ys' x} (tr : Transcript s e (xs ++ [x]) ys') :
    ∃ ys y, ys' = ys ++ [y] ∧ Transcript s e xs ys ∧ x ∈ e ys ∧ y ∈ s (xs ++ [x]) := by
  generalize hx : xs ++ [x] = xs' at tr
  cases tr with
  | nil => simp at hx
  | snoc tr hx' hy =>
    obtain ⟨rfl, rfl⟩ := List.append_inj' hx rfl |>.imp id (fun h => by simpa using h.symm)
    exact ⟨_, _, rfl, tr, hx', hy⟩

theorem Transcript.take {e xs ys} (tr : Transcript s e xs ys) (n : ℕ) :
    Transcript s e (xs.take n) (ys.take n) := by
  induction tr with
  | nil => simp only [List.take_nil]; exact Transcript.nil
  | @snoc xs ys x y tr hx hy ih =>
    by_cases hn : n ≤ xs.length
    · rw [List.take_append_of_le_length hn,
        List.take_append_of_le_length (tr.length_eq ▸ hn)]
      exact ih
    · rw [List.take_of_length_le (by simp; omega),
        List.take_of_length_le (by have hl := tr.length_eq; simp; omega)]
      exact Transcript.snoc tr hx hy

/-- At each length, two deterministic systems have only one interaction
transcript. -/
theorem Transcript.eq_of_length_eq {e xs ys xs' ys'} (tr : Transcript s e xs ys)
    (tr' : Transcript s e xs' ys') (hl : xs.length = xs'.length) : xs = xs' ∧ ys = ys' := by
  induction tr generalizing xs' ys' with
  | nil =>
    have hx : xs' = [] := List.length_eq_zero_iff.mp hl.symm
    have hy : ys' = [] := List.length_eq_zero_iff.mp (tr'.length_eq.symm.trans hl.symm)
    exact ⟨hx.symm, hy.symm⟩
  | snoc tr hx hy ih =>
    cases tr' with
    | nil => simp at hl
    | snoc tr' hx' hy' =>
      obtain ⟨rfl, rfl⟩ := ih tr' (by simpa using hl)
      obtain rfl := Part.mem_unique hx hx'
      obtain rfl := Part.mem_unique hy hy'
      exact ⟨rfl, rfl⟩

theorem Transcript.length_le_of_stopped {e xs ys xs' ys'} (tr : Transcript s e xs ys)
    (hd : ¬ (e ys).Dom) (tr' : Transcript s e xs' ys') : xs'.length ≤ xs.length := by
  by_contra hn
  have hl : xs.length < xs'.length := Nat.lt_of_not_ge hn
  have htake := tr'.take (xs.length + 1)
  rw [List.take_add_one, List.getElem?_eq_getElem hl] at htake
  obtain ⟨zs, z, _, hp, hx, _⟩ := Transcript.snoc_inv htake
  obtain ⟨_, he⟩ := tr.eq_of_length_eq hp (by simp; omega)
  exact hd (he ▸ Part.dom_iff_mem.mpr ⟨_, hx⟩)

/-- Completed transcripts are unique, including for partial systems. -/
theorem Transcript.eq_of_stopped {e xs ys xs' ys'} (tr : Transcript s e xs ys)
    (tr' : Transcript s e xs' ys') (hd : ¬ (e ys).Dom) (hd' : ¬ (e ys').Dom) :
    xs = xs' ∧ ys = ys' :=
  tr.eq_of_length_eq tr' (le_antisymm (tr'.length_le_of_stopped hd' tr)
    (tr.length_le_of_stopped hd tr'))

/-- The environment that issues the queries `H` in order, ignoring the replies. -/
def fixedQueries (H : List A) : List B →. A := fun ys => (H[ys.length]? : Part A)

theorem transcript_fixedQueries {H : List A} :
    ∀ h e', H = h ++ e' → (Reach s h ↔ ∃ ys, Transcript s (fixedQueries H) h ys) := by
  intro h
  induction h using List.reverseRecOn with
  | nil => intro e' _; exact ⟨fun _ => ⟨[], Transcript.nil⟩, fun _ => reach_nil s⟩
  | append_singleton h x ih =>
    intro e' hH
    have ih' := ih (x :: e') (by simp [hH])
    constructor
    · intro hr
      obtain ⟨hr₀, hd⟩ := reach_snoc_iff.mp hr
      obtain ⟨ys, tr⟩ := ih'.mp hr₀
      refine ⟨ys ++ [(s (h ++ [x])).get hd], Transcript.snoc tr ?_ (Part.get_mem hd)⟩
      simp [fixedQueries, ← tr.length_eq, hH]
    · rintro ⟨ys', tr⟩
      exact tr.reach

/-- Behavioural equality is equality of the transcripts with every environment. -/
theorem behEq_iff_transcript :
    s ≈ₛ t ↔ ∀ e xs ys, Transcript s e xs ys ↔ Transcript t e xs ys := by
  constructor
  · intro hst
    have one : ∀ {s t : System A B}, s ≈ₛ t → ∀ {e xs ys}, Transcript s e xs ys → Transcript t e xs ys := by
      intro s t hst e xs ys tr
      induction tr with
      | nil => exact Transcript.nil
      | snoc tr hx hy ih =>
        have hr : Reach s (_ ++ [_]) := reach_snoc_iff.mpr ⟨tr.reach, Part.dom_iff_mem.mpr ⟨_, hy⟩⟩
        exact Transcript.snoc ih hx (by rw [← hst.2 _ hr (by simp)]; exact hy)
    have hts : t ≈ₛ s :=
      ⟨fun h => (hst.1 h).symm, fun h hr hne => (hst.2 h ((hst.1 h).mpr hr) hne).symm⟩
    exact fun e xs ys => ⟨one hst, one hts⟩
  · intro htr
    have hreach : ∀ h, Reach s h ↔ Reach t h := by
      intro h
      rw [transcript_fixedQueries (H := h) h [] (by simp),
        transcript_fixedQueries (H := h) h [] (by simp)]
      exact exists_congr fun ys => htr _ h ys
    refine ⟨hreach, fun h hr hne => ?_⟩
    apply Part.ext
    intro y
    induction h using List.reverseRecOn with
    | nil => exact (hne rfl).elim
    | append_singleton h x _ =>
      obtain ⟨hr₀, _⟩ := reach_snoc_iff.mp hr
      obtain ⟨ys, tr⟩ := (transcript_fixedQueries (s := s) h [x] rfl).mp hr₀
      have hx : x ∈ fixedQueries (h ++ [x]) ys := by
        simp [fixedQueries, ← tr.length_eq]
      constructor
      · intro hy
        obtain ⟨ys', y', e₁, -, -, hy'⟩ := ((htr _ _ _).mp (Transcript.snoc tr hx hy)).snoc_inv
        obtain ⟨-, e₂⟩ := List.append_inj' e₁ rfl
        simp only [List.cons.injEq, and_true] at e₂
        exact e₂ ▸ hy'
      · intro hy
        have trt := (htr _ h ys).mp tr
        obtain ⟨ys', y', e₁, -, -, hy'⟩ := ((htr _ _ _).mpr (Transcript.snoc trt hx hy)).snoc_inv
        obtain ⟨-, e₂⟩ := List.append_inj' e₁ rfl
        simp only [List.cons.injEq, and_true] at e₂
        exact e₂ ▸ hy'

end Transcript

/-! ## Convergence of two-component wirings -/

section Run

variable {X Y : Type}

/-- The number of consecutive replies in `P` at the end of a reversed history. -/
noncomputable def runRev (P : Y → Prop) (s : System X Y) : List X → ℕ
  | [] => 0
  | x :: r => if ∃ y ∈ s (r.reverse ++ [x]), P y then runRev P s r + 1 else 0

/-- The number of consecutive replies in `P` at the end of `h`. -/
noncomputable def run (P : Y → Prop) (s : System X Y) (h : List X) : ℕ :=
  runRev P s h.reverse

@[simp] theorem run_nil (P : Y → Prop) (s : System X Y) : run P s [] = 0 := rfl

theorem run_snoc (P : Y → Prop) (s : System X Y) (h : List X) (x : X) :
    run P s (h ++ [x]) = if ∃ y ∈ s (h ++ [x]), P y then run P s h + 1 else 0 := by
  simp [run, runRev]

end Run

section Converge

variable {Xa Ya Xb Yb A B : Type} {a : System Xa Ya} {b : System Xb Yb} {P : Ya → Prop}
  {route : Two Ya Yb → B ⊕ Two Xa Xb} {inj : A → Two Xa Xb} {n : ℕ}

/-- Every internal cycle of `[a, b]` passes through `a`: a reply of `a` outside `P`
leaves, a reply of `a` in `P` leaves or goes to `b`, and a reply of `b` leaves or goes
to `a`. -/
structure CyclesThrough (P : Ya → Prop) (route : Two Ya Yb → B ⊕ Two Xa Xb) : Prop where
  left_out : ∀ y, ¬ P y → ∃ c, route ⟨none, y⟩ = .inl c
  left_in : ∀ y, P y → (∃ c, route ⟨none, y⟩ = .inl c) ∨ ∃ x, route ⟨none, y⟩ = .inr ⟨some (), x⟩
  right : ∀ y, (∃ c, route ⟨some (), y⟩ = .inl c) ∨ ∃ x, route ⟨some (), y⟩ = .inr ⟨none, x⟩

theorem restrict_none_snoc_left (G : List (Two Xa Xb)) (z : Xa) :
    restrict none (G ++ [⟨none, z⟩]) = restrict none G ++ [z] := by simp

theorem restrict_some_snoc_left (G : List (Two Xa Xb)) (z : Xa) :
    restrict (some ()) (G ++ [⟨none, z⟩]) = restrict (some ()) G := by
  rw [restrict_append, restrict_cons_ne (by simp)]; simp

theorem restrict_none_snoc_right (G : List (Two Xa Xb)) (x : Xb) :
    restrict none (G ++ [⟨some (), x⟩]) = restrict none G := by
  rw [restrict_append, restrict_cons_ne (by simp)]; simp

theorem restrict_some_snoc_right (G : List (Two Xa Xb)) (x : Xb) :
    restrict (some ()) (G ++ [⟨some (), x⟩]) = restrict (some ()) G ++ [x] := by simp

section Measure

variable (hc : CyclesThrough P route) (ν : List Xa → ℕ)
  (hν : ∀ h x w, w ∈ a (h ++ [x]) → P w → ν (h ++ [x]) < ν h)
include hc hν

/-- From a turn of `a`, the exchange stops. -/
theorem exchange_left_turn :
    ∀ m (G : List (Two Xa Xb)) (z : Xa), ν (restrict none G ++ [z]) = m →
      ∃ o G', Exchange (pair a b) route (G ++ [⟨none, z⟩]) o G' := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro G z hm
  have hpl : pair a b (G ++ [⟨none, z⟩]) = (a (restrict none G ++ [z])).map (Sigma.mk none) :=
    pair_left a b G z
  by_cases hd : (a (restrict none G ++ [z])).Dom
  swap
  · exact ⟨none, _, Exchange.silent _ (by rw [hpl]; exact hd)⟩
  have hy := Part.get_mem hd
  set y := (a (restrict none G ++ [z])).get hd
  have hpy : (⟨none, y⟩ : Two Ya Yb) ∈ pair a b (G ++ [⟨none, z⟩]) := by
    rw [hpl]; exact Part.mem_map _ hy
  by_cases hP : P y
  swap
  · obtain ⟨c, e⟩ := hc.left_out y hP
    exact ⟨_, _, Exchange.out _ _ c hpy e⟩
  rcases hc.left_in y hP with ⟨c, e⟩ | ⟨x, e⟩
  · exact ⟨_, _, Exchange.out _ _ c hpy e⟩
  -- the query `x` goes to `b`
  have hpr : pair a b (G ++ [⟨none, z⟩] ++ [⟨some (), x⟩]) =
      (b (restrict (some ()) G ++ [x])).map (Sigma.mk (some ())) := by
    rw [pair_right, restrict_some_snoc_left]
  by_cases hdb : (b (restrict (some ()) G ++ [x])).Dom
  swap
  · exact ⟨none, _, Exchange.feed _ _ _ _ _ hpy e (Exchange.silent _ (by rw [hpr]; exact hdb))⟩
  have hy' := Part.get_mem hdb
  set y' := (b (restrict (some ()) G ++ [x])).get hdb
  have hpy' : (⟨some (), y'⟩ : Two Ya Yb) ∈ pair a b (G ++ [⟨none, z⟩] ++ [⟨some (), x⟩]) := by
    rw [hpr]; exact Part.mem_map _ hy'
  rcases hc.right y' with ⟨c, e'⟩ | ⟨z', e'⟩
  · exact ⟨_, _, Exchange.feed _ _ _ _ _ hpy e (Exchange.out _ _ c hpy' e')⟩
  -- the reply `z'` goes back to `a`
  have hres : restrict none (G ++ [⟨none, z⟩] ++ [⟨some (), x⟩]) = restrict none G ++ [z] := by
    rw [restrict_none_snoc_right, restrict_none_snoc_left]
  suffices hnext : ∃ o G', Exchange (pair a b) route
      (G ++ [⟨none, z⟩] ++ [⟨some (), x⟩] ++ [⟨none, z'⟩]) o G' by
    obtain ⟨o, G', l⟩ := hnext
    exact ⟨o, G', Exchange.feed _ _ _ _ _ hpy e (Exchange.feed _ _ _ _ _ hpy' e' l)⟩
  by_cases hP' : ∃ w ∈ a (restrict none G ++ [z] ++ [z']), P w
  · -- a further reply in `P`: the measure decreases
    obtain ⟨w, hw, hPw⟩ := hP'
    refine ih _ ?_ _ _ rfl
    rw [hres, ← hm]
    exact hν _ _ w hw hPw
  · -- a reply outside `P` leaves, or `a` is silent
    have hpl' : pair a b (G ++ [⟨none, z⟩] ++ [⟨some (), x⟩] ++ [⟨none, z'⟩]) =
        (a (restrict none G ++ [z] ++ [z'])).map (Sigma.mk none) := by
      rw [pair_left, hres]
    by_cases hd' : (a (restrict none G ++ [z] ++ [z'])).Dom
    · have hw := Part.get_mem hd'
      obtain ⟨c, e''⟩ := hc.left_out _ (fun hw' => hP' ⟨_, hw, hw'⟩)
      exact ⟨_, _, Exchange.out _ _ c (by rw [hpl']; exact Part.mem_map _ hw) e''⟩
    · exact ⟨none, _, Exchange.silent _ (by rw [hpl']; exact hd')⟩

/-- Every exchange of `[a, b]` stops. -/
theorem exchange_pair (G : List (Two Xa Xb)) : ∃ o G', Exchange (pair a b) route G o G' := by
  rcases List.eq_nil_or_concat G with rfl | ⟨G₀, g, rfl⟩
  · exact ⟨none, [], Exchange.silent _ (by simp [pair])⟩
  rw [List.concat_eq_append]
  rcases g with ⟨_ | ⟨⟨⟩⟩, g⟩
  · exact exchange_left_turn hc ν hν _ G₀ g rfl
  · have hpr : pair a b (G₀ ++ [⟨some (), g⟩]) =
        (b (restrict (some ()) G₀ ++ [g])).map (Sigma.mk (some ())) := pair_right a b G₀ g
    by_cases hdb : (b (restrict (some ()) G₀ ++ [g])).Dom
    swap
    · exact ⟨none, _, Exchange.silent _ (by rw [hpr]; exact hdb)⟩
    have hy' := Part.get_mem hdb
    have hpy' : (⟨some (), (b (restrict (some ()) G₀ ++ [g])).get hdb⟩ : Two Ya Yb) ∈
        pair a b (G₀ ++ [⟨some (), g⟩]) := by rw [hpr]; exact Part.mem_map _ hy'
    rcases hc.right ((b (restrict (some ()) G₀ ++ [g])).get hdb) with ⟨c, e'⟩ | ⟨z', e'⟩
    · exact ⟨_, _, Exchange.out _ _ c hpy' e'⟩
    · obtain ⟨o, G', l⟩ := exchange_left_turn hc ν hν _ (G₀ ++ [⟨some (), g⟩]) z' rfl
      exact ⟨o, G', Exchange.feed _ _ _ _ _ hpy' e' l⟩

/-- If every internal cycle passes through `a`, and a measure on `a`'s histories drops at
each reply of `a` that continues a cycle, the wiring of `[a, b]` converges, whatever `b` is. -/
theorem converges_pair_of_measure : Converges (pair a b) route inj :=
  converges_of_exchanges (exchange_pair hc ν hν)

end Measure

/-- **Convergence of an attachment.** If every internal cycle passes through `a`, and `a`
has at most `n` consecutive replies that continue a cycle, the wiring of `[a, b]` converges,
whatever `b` is. -/
theorem converges_pair (hc : CyclesThrough P route) (hb : ∀ h, (a h).Dom → run P a h ≤ n) :
    Converges (pair a b) route inj := by
  refine converges_pair_of_measure hc (fun h => n - run P a h) (fun h x w hw hP => ?_)
  have hle := hb _ (Part.dom_iff_mem.mpr ⟨w, hw⟩)
  rw [run_snoc, if_pos ⟨w, hw, hP⟩] at hle ⊢
  omega

/-- Each internal cycle consumes one of the remaining consecutive queries of
`a`. A turn of `b` adds at most one reply before control returns to `a`. -/
theorem Exchange.length_le_of_cycles (hc : CyclesThrough P route)
    (hb : ∀ h, (a h).Dom → run P a h ≤ n) {G o H}
    (l : Exchange (pair a b) route G o H) :
    ∀ G₀ x, G = G₀ ++ [x] →
      H.length ≤ G₀.length + 2 * (n - run P a (restrict none G₀)) +
        (if x.1 = none then 1 else 2) := by
  induction l with
  | silent G hd =>
    intro G₀ x he
    subst G
    simp only [List.length_append, List.length_singleton]
    split_ifs <;> omega
  | out G y w hy hr =>
    intro G₀ x he
    subst G
    simp only [List.length_append, List.length_singleton]
    split_ifs <;> omega
  | feed G y z o H hy hr l ih =>
    intro G₀ x he
    subst G
    rcases x with ⟨_ | ⟨⟨⟩⟩, x⟩
    · rw [pair_left] at hy
      obtain ⟨y, hySource, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      have hP : P y := by
        by_contra hn
        obtain ⟨w, hw⟩ := hc.left_out y hn
        rw [hr] at hw
        cases hw
      obtain ⟨w, hw⟩ | ⟨z', hz⟩ := hc.left_in y hP
      · rw [hr] at hw; cases hw
      · have ez : z = ⟨some (), z'⟩ := Sum.inr.inj (hr.symm.trans hz)
        subst z
        have hrun : run P a (restrict none G₀ ++ [x]) =
            run P a (restrict none G₀) + 1 := by
          rw [run_snoc, if_pos ⟨y, hySource, hP⟩]
        have hn := hb _ hySource.1
        rw [hrun] at hn
        have hi := ih (G₀ ++ [⟨none, x⟩]) ⟨some (), z'⟩ rfl
        simp only [restrict_none_snoc_left, hrun, List.length_append,
          List.length_singleton, reduceCtorEq, if_false, if_true] at hi ⊢
        omega
    · rw [pair_right] at hy
      obtain ⟨y, hy, rfl⟩ := Part.mem_map_iff _ |>.mp hy
      obtain ⟨w, hw⟩ | ⟨z', hz⟩ := hc.right y
      · rw [hr] at hw; cases hw
      · have ez : z = ⟨none, z'⟩ := Sum.inr.inj (hr.symm.trans hz)
        subst z
        have hi := ih (G₀ ++ [⟨some (), x⟩]) ⟨none, z'⟩ rfl
        simp only [restrict_none_snoc_right, List.length_append,
          List.length_singleton, reduceCtorEq, if_false, if_true] at hi ⊢
        omega

/-- A finite exposed history needs at most `2n + 2` component replies per
input. This concerns interaction length, independently of sample support. -/
theorem Induces.length_le_of_cycles (hc : CyclesThrough P route)
    (hb : ∀ h, (a h).Dom → run P a h ≤ n) {us o H}
    (r : Induces (pair a b) route inj us o H) :
    H.length ≤ (2 * n + 2) * us.length := by
  induction r with
  | nil => simp
  | snoc us u o G o' H r l ih =>
    have hl := l.length_le_of_cycles hc hb G (inj u) rfl
    have hn : n - run P a (restrict none G) ≤ n := Nat.sub_le _ _
    simp only [List.length_append, List.length_singleton, Nat.mul_add, Nat.mul_one]
    split_ifs at hl <;> omega

/-- **Convergence against a terminating system.** If every internal cycle passes through a
terminating `a`, the wiring of `[a, b]` converges, whatever `b` is. -/
theorem converges_pair_of_terminating (hc : CyclesThrough P route) (ha : Terminating a) :
    Converges (pair a b) route inj := by
  obtain ⟨μ, hμ⟩ := ha
  exact converges_pair_of_measure hc μ (fun h x w hw _ => hμ h x (Part.dom_iff_mem.mpr ⟨w, hw⟩))

end Converge

/-- If every input addresses the right constituent, only its history is used. -/
theorem relabel_pair_right_only {A B C D E F : Type} (s : System A B) (t : System C D)
    (ht : SilentAtEmpty t) (f : E → C) (g : Two B D → F) :
    relabel (pair s t) (fun x => ⟨some (), f x⟩) g =
      relabel t f (fun y => g ⟨some (), y⟩) := by
  have hm (h : List E) :
      restrict (some ()) (h.map (fun x => (⟨some (), f x⟩ : Two A C))) = h.map f := by
    induction h with
    | nil => rfl
    | cons x h ih => simp only [List.map_cons, restrict_cons_self, ih]
  funext h
  rcases List.eq_nil_or_concat h with rfl | ⟨h, x, rfl⟩
  · simp only [relabel, List.map_nil, pair, parAll_nil, Part.eq_none_iff'.mpr ht, Part.map_none]
  · simp only [relabel, List.concat_eq_append, List.map_append, List.map_singleton,
      pair_right, hm, Part.map_map, Function.comp_def]

theorem relabel_pair_left_only {A B C D E F : Type} (s : System A B) (t : System C D)
    (hs : SilentAtEmpty s) (f : E → A) (g : Two B D → F) :
    relabel (pair s t) (fun x => ⟨none, f x⟩) g =
      relabel s f (fun y => g ⟨none, y⟩) := by
  rw [pair_swap, relabel_relabel]
  exact relabel_pair_right_only t s hs f (g ∘ twoSwap)

end SystemAlgebra

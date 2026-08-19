/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ProbabilisticSystem
import AbstractCryptography.Specification.Interfaces

/-!
# Attachment at an interface, and the axiom it discharges

The middle layer at interface set `P` over alphabets `(X, Y)`: resources are
`PDS (P × X) Y` — the interface address is input data — and a converter is
attached at one interface by CR18 Definition 3.13 (`Converter.General.attachAt`),
lifted to laws by pushforward.

`Σ` is the free monoid of Jost's *converter-connection pairs* `(i, α)`; each
letter acts by attachment at its interface.  `pairwiseOrderInvariant_attach`
discharges the one axiom the abstract layer asks of an attachment family
(LiuZhang fn. 1, Jost Prop 2.2.3): attachments at distinct interfaces commute
in their action.  It is the lift of the deterministic `attachAt_comm`, so
`AbstractCryptography.attachedWithin`/`orderInvariant_attachedWithin` and the
blocking relaxations apply to this carrier with no further proof.
-/

namespace RandomSystems

open Probability (Distribution)

universe u v z

variable {P : Type u} [DecidableEq P] {X : Type z} {Y : Type v}

namespace Converter

/-- CR18 Definition 3.13, lifted to laws: the pushforward along `attachAt`. -/
noncomputable def General.attachAtLaw (i : P) (α : DDC X Y X Y) :
    PDS (P × X) Y → PDS (P × X) Y :=
  Distribution.fTransform (General.attachAt i α)

/-- Order invariance survives the lift to laws. -/
theorem General.attachAtLaw_comm (i : P) (α : DDC X Y X Y) (j : P)
    (β : DDC X Y X Y) (hij : i ≠ j) (S : PDS (P × X) Y) :
    General.attachAtLaw i α (General.attachAtLaw j β S) =
      General.attachAtLaw j β (General.attachAtLaw i α S) := by
  unfold General.attachAtLaw
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  exact congrArg (fun f => Distribution.fTransform f S)
    (funext fun s => General.attachAt_comm i α j β s hij)

/-- The middle layer's `Σ`: words of converter-connection pairs, each letter
acting by attachment at its interface. -/
noncomputable def connectionAct :
    FreeMonoid (P × DDC X Y X Y) →* Function.End (PDS (P × X) Y) :=
  FreeMonoid.lift fun c =>
    (General.attachAtLaw c.1 c.2 : Function.End (PDS (P × X) Y))

noncomputable instance instMulActionConnection :
    MulAction (FreeMonoid (P × DDC X Y X Y)) (PDS (P × X) Y) :=
  MulAction.compHom _ connectionAct

@[simp] theorem connection_smul_letter (c : P × DDC X Y X Y)
    (S : PDS (P × X) Y) :
    (FreeMonoid.of c : FreeMonoid (P × DDC X Y X Y)) • S =
      General.attachAtLaw c.1 c.2 S := by
  show connectionAct (FreeMonoid.of c) S = _
  simp [connectionAct]

/-- Attachment at one interface — the family the abstract layer indexes. -/
noncomputable def attachFamily : P → DDC X Y X Y → FreeMonoid (P × DDC X Y X Y) :=
  fun i α => FreeMonoid.of (i, α)

/-- **The axiom, discharged** (LiuZhang fn. 1, Jost Prop 2.2.3): CR18
Definition 3.13 attachment is pairwise order-invariant on laws. -/
theorem pairwiseOrderInvariant_attach :
    AbstractCryptography.PairwiseOrderInvariant (PDS (P × X) Y)
      (attachFamily (P := P) (X := X) (Y := Y)) := by
  intro i j hij α β S
  simp only [attachFamily, connection_smul_letter]
  exact General.attachAtLaw_comm i α j β hij S

/-- Receipt: any corruption split yields the attachment pair the blocking
relaxations (`AbstractCryptography.Specification.Outbound`) consume. -/
example {Z₁ Z₂ : Set P} (h : Disjoint Z₁ Z₂) :
    AbstractCryptography.OrderInvariant (PDS (P × X) Y)
      (AbstractCryptography.attachedWithin (attachFamily (X := X) (Y := Y)) Z₁).subtype
      (AbstractCryptography.attachedWithin (attachFamily (X := X) (Y := Y)) Z₂).subtype :=
  AbstractCryptography.orderInvariant_attachedWithin _
    pairwiseOrderInvariant_attach h

/-! ## The identity converter (MauRen16 §3.3's `id ∈ Σ`)

The monoid identity is the empty word (`one_smul`); this is the neutral
*letter*: the converter that forwards the outer query inside and the inner
answer outside, silent past a `⊥`.  `attachAt_id` shows it idle at every
interface. -/

/-- A converter history that never contains the completion symbol `⊥`. -/
def BotFree (c : List (DDC.CIn X Y)) : Prop :=
  ∀ lab : InLabel, (Sum.inr (lab, (none : Option Y)) : DDC.CIn X Y) ∉ c

theorem BotFree.nil : BotFree ([] : List (DDC.CIn X Y)) := fun _ h => by cases h

theorem BotFree.append_inl {c : List (DDC.CIn X Y)} (h : BotFree c)
    (lab : InLabel) (x : X) : BotFree (c ++ [Sum.inl (lab, x)]) := by
  intro lab' hmem
  rcases List.mem_append.mp hmem with hc | hc
  · exact h lab' hc
  · simp at hc

theorem BotFree.append_some {c : List (DDC.CIn X Y)} (h : BotFree c)
    (lab : InLabel) (y : Y) : BotFree (c ++ [Sum.inr (lab, some y)]) := by
  intro lab' hmem
  rcases List.mem_append.mp hmem with hc | hc
  · exact h lab' hc
  · simp at hc

theorem not_botFree_append_none (c : List (DDC.CIn X Y)) (lab : InLabel) :
    ¬ BotFree (c ++ [Sum.inr (lab, (none : Option Y))]) := fun h =>
  h lab (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))

open Classical in
/-- MauRen16 §3.3's identity converter: forward the outer query inside,
forward the inner answer outside; silent past a `⊥`. -/
noncomputable def idDDC : DDC X Y X Y :=
  ⟨fun c =>
    if BotFree c then
      match c.getLast? with
      | some (Sum.inl (_, x)) => Part.some (Sum.inr (InLabel.inside, x))
      | some (Sum.inr (_, some y)) => Part.some (Sum.inl (InLabel.outside, y))
      | _ => Part.none
    else Part.none,
   by
    constructor
    · intro h
      rw [PFun.mem_dom] at h
      obtain ⟨v, hv⟩ := h
      simp only [if_pos (BotFree.nil (X := X) (Y := Y)), List.getLast?_nil] at hv
      exact Part.notMem_none v hv
    · intro l₁ l₂ hpre hne hdom
      rw [PFun.mem_dom] at hdom ⊢
      obtain ⟨v, hv⟩ := hdom
      by_cases hbf₂ : BotFree l₂
      · have hbf₁ : BotFree l₁ := fun lab hmem => hbf₂ lab (hpre.subset hmem)
        cases hlast : l₁.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp hlast) hne
        | some e =>
          have hmem : e ∈ l₁ := by
            have hg := List.getLast?_eq_some_getLast (l := l₁) hne
            have he : e = l₁.getLast hne :=
              Option.some.inj (hlast.symm.trans hg)
            exact he ▸ List.getLast_mem hne
          rcases e with ⟨lab, x⟩ | ⟨lab, o⟩
          · exact ⟨Sum.inr (InLabel.inside, x), by
              simp only [eq_true hbf₁, if_true, hlast, Part.mem_some_iff]⟩
          · rcases o with - | y
            · exact absurd hmem (hbf₁ lab)
            · exact ⟨Sum.inl (InLabel.outside, y), by
                simp only [eq_true hbf₁, if_true, hlast, Part.mem_some_iff]⟩
      · rw [if_neg hbf₂] at hv
        exact absurd hv (Part.notMem_none v)⟩

theorem mem_idDDC_query {c : List (DDC.CIn X Y)} (hbf : BotFree c)
    (lab : InLabel) (x : X) :
    (Sum.inr (InLabel.inside, x) : DDC.COut Y X) ∈
      (idDDC (X := X) (Y := Y)).1 (c ++ [Sum.inl (lab, x)]) := by
  simp only [idDDC, if_pos (hbf.append_inl lab x), List.getLast?_concat]
  exact Part.mem_some_iff.mpr rfl

theorem mem_idDDC_answer {c : List (DDC.CIn X Y)} (hbf : BotFree c)
    (lab : InLabel) (y : Y) :
    (Sum.inl (InLabel.outside, y) : DDC.COut Y X) ∈
      (idDDC (X := X) (Y := Y)).1 (c ++ [Sum.inr (lab, some y)]) := by
  simp only [idDDC, if_pos (hbf.append_some lab y), List.getLast?_concat]
  exact Part.mem_some_iff.mpr rfl

theorem idDDC_bot (c : List (DDC.CIn X Y)) (lab : InLabel) :
    (idDDC (X := X) (Y := Y)).1
      (c ++ [Sum.inr (lab, (none : Option Y))]) = Part.none := by
  simp [idDDC, if_neg (not_botFree_append_none c lab)]

namespace General

/-- A stalled converter stalls the whole `i`-round. -/
theorem attachResolve_none (i : P) (α : DDC X Y X Y)
    (s : System.Resource P X Y)
    {st : List (DDC.CIn X Y) × List (P × X)} (h : α.1 st.1 = Part.none) :
    attachResolve i α s st = Part.none := by
  rw [Part.eq_none_iff]
  intro b hb
  rw [attachResolve, PFun.mem_fix_iff] at hb
  have hstep : attachStep i α s st = Part.none := by
    simp [attachStep, h]
  rcases hb with hb | ⟨a', ha', -⟩
  · rw [hstep] at hb
    exact Part.notMem_none _ hb
  · rw [hstep] at ha'
    exact Part.notMem_none _ ha'

/-! ### The resource replayed alone

`replay s rs l` collects the outputs of `s` at each successive extension of
`rs` by an entry of `l` — the pass-through reference the identity attachment
is compared against. -/

/-- The outputs of `s` along `l`, continuing the history `rs`. -/
noncomputable def replay (s : System.Resource P X Y) :
    List (P × X) → List (P × X) →. List Y
  | _, [] => Part.some []
  | rs, e :: rest =>
      (s.1 (rs ++ [e])).bind fun y =>
        (replay s (rs ++ [e]) rest).map fun ys => y :: ys

theorem replay_length {s : System.Resource P X Y} :
    ∀ {l rs : List (P × X)} {ys : List Y},
      ys ∈ replay s rs l → ys.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro rs ys h
      simp only [replay, Part.mem_some_iff] at h
      simp [h]
  | cons e rest ih =>
      intro rs ys h
      simp only [replay, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨y, -, ys', hys', rfl⟩ := h
      simp [ih hys']

/-- The last collected output is the resource's output at the full history. -/
theorem mem_of_replay_getLast {s : System.Resource P X Y} :
    ∀ {l rs : List (P × X)} {ys : List Y} {y : Y},
      ys ∈ replay s rs l → ys.getLast? = some y → y ∈ s.1 (rs ++ l) := by
  intro l
  induction l with
  | nil =>
      intro rs ys y h hlast
      simp only [replay, Part.mem_some_iff] at h
      subst h
      simp at hlast
  | cons e rest ih =>
      intro rs ys y h hlast
      simp only [replay, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨y₀, hy₀, ys', hys', rfl⟩ := h
      cases rest with
      | nil =>
          simp only [replay, Part.mem_some_iff] at hys'
          subst hys'
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst hlast
          simpa using hy₀
      | cons e' rest' =>
          cases ys' with
          | nil =>
              have := replay_length hys'
              simp at this
          | cons y₁ ys'' =>
              rw [List.getLast?_cons_cons] at hlast
              have := ih hys' hlast
              simpa [List.append_assoc] using this

/-- Conversely, a defined output at the full history yields a replay run
ending in it. -/
theorem exists_replay_of_mem {s : System.Resource P X Y} :
    ∀ {l rs : List (P × X)} {y : Y},
      y ∈ s.1 (rs ++ l) → l ≠ [] →
      ∃ ys ∈ replay s rs l, ys.getLast? = some y := by
  intro l
  induction l with
  | nil => intro rs y _ h; exact absurd rfl h
  | cons e rest ih =>
      intro rs y hy _
      have hdom : rs ++ e :: rest ∈ System.dom s := (PFun.mem_dom _ _).mpr ⟨y, hy⟩
      cases rest with
      | nil =>
          refine ⟨[y], ?_, by simp⟩
          simp only [replay, Part.mem_bind_iff, Part.mem_map_iff]
          exact ⟨y, hy, [], Part.mem_some_iff.mpr rfl, rfl⟩
      | cons e' rest' =>
          have h1 : rs ++ [e] ∈ System.dom s := by
            refine System.prefix_closed s ?_ (by simp) hdom
            exact ⟨e' :: rest', by simp⟩
          have hy' : y ∈ s.1 ((rs ++ [e]) ++ e' :: rest') := by
            simpa [List.append_assoc] using hy
          obtain ⟨ys', hys', hlast⟩ := ih hy' (by simp)
          have hy₀ : System.output s (rs ++ [e]) h1 ∈ s.1 (rs ++ [e]) :=
            Part.get_mem h1
          cases ys' with
          | nil =>
              have := replay_length hys'
              simp at this
          | cons y₁ ys'' =>
              refine ⟨System.output s (rs ++ [e]) h1 :: y₁ :: ys'', ?_, ?_⟩
              · exact Part.mem_bind_iff.mpr
                  ⟨_, hy₀, Part.mem_map _ hys'⟩
              · rw [List.getLast?_cons_cons]
                exact hlast

/-! ### The identity attachment is idle -/

/-- Forward direction: whatever the identity attachment's drive produces, the
resource alone produces — with the whole history kept and the converter
history `⊥`-free. -/
theorem attachDrive_idDDC_forward {i : P} {s : System.Resource P X Y} :
    ∀ {l : List (P × X)} {c : List (DDC.CIn X Y)} {rs : List (P × X)}
      {r : List Y × (List (DDC.CIn X Y) × List (P × X))},
      BotFree c → (rs ∈ System.dom s ∨ rs = []) →
      r ∈ attachDrive i idDDC s (c, rs) l →
      r.1 ∈ replay s rs l ∧ r.2.2 = rs ++ l ∧ BotFree r.2.1 := by
  intro l
  induction l with
  | nil =>
      intro c rs r hbf hk h
      simp only [attachDrive, Part.mem_some_iff] at h
      subst h
      refine ⟨?_, by simp, hbf⟩
      simp only [replay]
      exact Part.mem_some_iff.mpr rfl
  | cons e rest ih =>
      intro c rs r hbf hk h
      simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨r₁, hr₁, rr, hrr, hreq⟩ := h
      subst hreq
      by_cases he : e.1 = i
      · simp only [attachEntryStep, if_pos he] at hr₁
        have hq := mem_idDDC_query hbf InLabel.outside e.2
        rw [attachResolve_in i idDDC s hq] at hr₁
        by_cases hd : rs ++ [(i, e.2)] ∈ System.dom s
        · have hans := System.output_fullyDefined_append_of_mem s rs (i, e.2) hk hd
          simp only [hans] at hr₁
          set y₀ := System.output s (rs ++ [(i, e.2)]) hd with hy₀def
          set c₁ := (c ++ [Sum.inl (InLabel.outside, e.2)]) ++
            [Sum.inr (InLabel.inside, some y₀)] with hc₁def
          have hbf₁ : BotFree c₁ :=
            (hbf.append_inl InLabel.outside e.2).append_some InLabel.inside y₀
          have hout := attachResolve_out i idDDC s
            (mem_idDDC_answer (hbf.append_inl InLabel.outside e.2)
              InLabel.inside y₀) (rs := rs ++ [(i, e.2)])
          have hr₁eq : r₁ = (y₀, (c₁, rs ++ [(i, e.2)])) :=
            Part.mem_unique hr₁ hout
          subst hr₁eq
          obtain ⟨h1, h2, h3⟩ := ih hbf₁ (Or.inl hd) hrr
          have he' : (i, e.2) = e := by rw [← he]
          refine ⟨?_, ?_, h3⟩
          · refine Part.mem_bind_iff.mpr ⟨y₀, ?_, ?_⟩
            · rw [← he']
              exact Part.get_mem hd
            · rw [← he']
              exact Part.mem_map _ h1
          · rw [h2, ← he']
            simp
        · have hans : System.output (System.fullyDefined s) (rs ++ [(i, e.2)])
                (by rw [System.dom_fullyDefined]; simp) = none := by
              cases hout : System.output (System.fullyDefined s)
                  (rs ++ [(i, e.2)]) (by rw [System.dom_fullyDefined]; simp) with
              | some y' =>
                  obtain ⟨hnext, -⟩ :=
                    System.mem_of_output_fullyDefined_append_eq_some s rs
                      (i, e.2) hk hout
                  exact absurd hnext hd
              | none => rfl
          simp only [hans] at hr₁
          rw [attachResolve_none i idDDC s
            (idDDC_bot (c ++ [Sum.inl (InLabel.outside, e.2)]) InLabel.inside)]
            at hr₁
          exact absurd hr₁ (Part.notMem_none _)
      · simp only [attachEntryStep, if_neg he, Part.mem_map_iff] at hr₁
        obtain ⟨y₀, hy₀, hr₁eq⟩ := hr₁
        subst hr₁eq
        obtain ⟨h1, h2, h3⟩ :=
          ih hbf (Or.inl ((PFun.mem_dom _ _).mpr ⟨y₀, hy₀⟩)) hrr
        refine ⟨Part.mem_bind_iff.mpr ⟨y₀, hy₀, Part.mem_map _ h1⟩, ?_, h3⟩
        rw [h2]
        simp

/-- Backward direction: whatever the resource alone produces, the identity
attachment's drive produces. -/
theorem attachDrive_idDDC_exists {i : P} {s : System.Resource P X Y} :
    ∀ {l : List (P × X)} {c : List (DDC.CIn X Y)} {rs : List (P × X)}
      {ys : List Y},
      BotFree c → (rs ∈ System.dom s ∨ rs = []) →
      ys ∈ replay s rs l →
      ∃ c', (ys, (c', rs ++ l)) ∈ attachDrive i idDDC s (c, rs) l := by
  intro l
  induction l with
  | nil =>
      intro c rs ys hbf hk h
      simp only [replay, Part.mem_some_iff] at h
      subst h
      refine ⟨c, ?_⟩
      simp only [attachDrive, List.append_nil]
      exact Part.mem_some_iff.mpr rfl
  | cons e rest ih =>
      intro c rs ys hbf hk h
      simp only [replay, Part.mem_bind_iff, Part.mem_map_iff] at h
      obtain ⟨y₀, hy₀, ys₁, hys₁, hyseq⟩ := h
      subst hyseq
      have hd' : rs ++ [e] ∈ System.dom s := (PFun.mem_dom _ _).mpr ⟨y₀, hy₀⟩
      by_cases he : e.1 = i
      · have he' : (i, e.2) = e := by rw [← he]
        have hd : rs ++ [(i, e.2)] ∈ System.dom s := by rw [he']; exact hd'
        have hy₀' : y₀ ∈ s.1 (rs ++ [(i, e.2)]) := by rw [he']; exact hy₀
        have hyget : System.output s (rs ++ [(i, e.2)]) hd = y₀ :=
          Part.get_eq_of_mem hy₀' hd
        have hans : System.output (System.fullyDefined s) (rs ++ [(i, e.2)])
            (by rw [System.dom_fullyDefined]; simp) = some y₀ :=
          (System.output_fullyDefined_append_of_mem s rs (i, e.2) hk hd).trans
            (congrArg some hyget)
        set c₁ := (c ++ [Sum.inl (InLabel.outside, e.2)]) ++
          [Sum.inr (InLabel.inside, some y₀)] with hc₁def
        have hbf₁ : BotFree c₁ :=
          (hbf.append_inl InLabel.outside e.2).append_some InLabel.inside y₀
        have hys₁' : ys₁ ∈ replay s (rs ++ [(i, e.2)]) rest := by
          rw [he']; exact hys₁
        obtain ⟨c', hdrive⟩ := ih hbf₁ (Or.inl hd) hys₁'
        refine ⟨c', ?_⟩
        simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff]
        refine ⟨(y₀, (c₁, rs ++ [(i, e.2)])), ?_, (ys₁, (c', rs ++ e :: rest)),
          ?_, rfl⟩
        · simp only [attachEntryStep, if_pos he]
          rw [attachResolve_in i idDDC s (mem_idDDC_query hbf InLabel.outside e.2)]
          simp only [hans]
          exact attachResolve_out i idDDC s
            (mem_idDDC_answer (hbf.append_inl InLabel.outside e.2)
              InLabel.inside y₀)
        · have harr : (rs ++ [(i, e.2)]) ++ rest = rs ++ e :: rest := by
            rw [he']; simp
          rw [← harr]
          exact hdrive
      · obtain ⟨c', hdrive⟩ := ih hbf (Or.inl hd') hys₁
        refine ⟨c', ?_⟩
        simp only [attachDrive, Part.mem_bind_iff, Part.mem_map_iff]
        refine ⟨(y₀, (c, rs ++ [e])), ?_, (ys₁, (c', rs ++ e :: rest)), ?_, rfl⟩
        · simp only [attachEntryStep, if_neg he]
          exact Part.mem_map _ hy₀
        · have harr : (rs ++ [e]) ++ rest = rs ++ e :: rest := by simp
          rw [← harr]
          exact hdrive

/-- **The identity attachment is idle** (MauRen16 §3.3: `id` "simply stands
for using the resource as is"). -/
theorem attachAt_idDDC (i : P) (s : System.Resource P X Y) :
    attachAt i (idDDC (X := X) (Y := Y)) s = s := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    simp only [attachAt] at hy
    simp only [attachRaw, Part.mem_bind_iff] at hy
    obtain ⟨r, hr, hy⟩ := hy
    obtain ⟨h1, -, -⟩ :=
      attachDrive_idDDC_forward BotFree.nil (Or.inr rfl) hr
    cases hlast : r.1.getLast? with
    | none =>
        rw [hlast] at hy
        exact absurd hy (Part.notMem_none _)
    | some y' =>
        rw [hlast] at hy
        have : y = y' := Part.mem_some_iff.mp hy
        subst this
        simpa using mem_of_replay_getLast h1 hlast
  · intro hy
    have hne : l ≠ [] := by
      rintro rfl
      exact System.empty_not_mem s ((PFun.mem_dom _ _).mpr ⟨y, hy⟩)
    obtain ⟨ys, hys, hlast⟩ :=
      exists_replay_of_mem (l := l) (rs := []) (by simpa using hy) hne
    obtain ⟨c', hdrive⟩ :=
      attachDrive_idDDC_exists (i := i) BotFree.nil (Or.inr rfl) hys
    simp only [attachAt]
    simp only [attachRaw, Part.mem_bind_iff]
    refine ⟨(ys, (c', [] ++ l)), by simpa using hdrive, ?_⟩
    rw [hlast]
    exact Part.mem_some_iff.mpr rfl

/-- The identity attachment is idle on laws. -/
theorem attachAtLaw_idDDC (i : P) :
    General.attachAtLaw i (idDDC (X := X) (Y := Y)) = id := by
  funext S
  unfold General.attachAtLaw
  rw [show General.attachAt i (idDDC (X := X) (Y := Y)) = id from
    funext (attachAt_idDDC i)]
  exact Distribution.fTransform_id S

end General

/-- MauRen16 §3.3's `id ∈ Σ`, as a letter: attaching the identity converter
at any interface leaves the law unchanged. -/
theorem attachFamily_idDDC_smul (i : P) (S : PDS (P × X) Y) :
    (attachFamily i (idDDC (X := X) (Y := Y))) • S = S := by
  rw [attachFamily, connection_smul_letter]
  simp [General.attachAtLaw_idDDC]

/-! ## The blocking converter (MR16 §3.4's `⊣`)

The nowhere-defined converter: attached at `i` it stalls every `i`-query, so
"the resource `R⊣` only has a left interface" is literal — the applied
resource is `s` restricted to `i`-free histories.  Blocking absorbs any
converter previously attached at the same interface, which makes every
resource of this carrier right-outbound: the model is query-driven, so a
converter behind a blocked interface is never activated. -/

/-- MR16 §3.4's `⊣`: the nowhere-defined converter. -/
def blkDDC : DDC X Y X Y :=
  ⟨fun _ => Part.none, ⟨fun h => h.elim, fun _ _ hdom => hdom.elim⟩⟩

@[simp] theorem blkDDC_apply (c : List (DDC.CIn X Y)) :
    (blkDDC (X := X) (Y := Y)).1 c = Part.none := rfl

namespace General

/-- On an `i`-free history, any attachment at `i` drives as the resource
alone, converter history untouched. -/
theorem attachDrive_of_no_query {i : P} (β : DDC X Y X Y)
    (s : System.Resource P X Y) :
    ∀ {l : List (P × X)} {c : List (DDC.CIn X Y)} {rs : List (P × X)},
      (∀ e ∈ l, e.1 ≠ i) →
      attachDrive i β s (c, rs) l =
        (replay s rs l).map fun ys => (ys, (c, rs ++ l)) := by
  intro l
  induction l with
  | nil =>
      intro c rs _
      simp [attachDrive, replay, Part.map_some]
  | cons e rest ih =>
      intro c rs hfree
      have he : e.1 ≠ i := hfree e (List.mem_cons_self ..)
      have hrest : ∀ e' ∈ rest, e'.1 ≠ i := fun e' h' =>
        hfree e' (List.mem_cons_of_mem _ h')
      simp only [attachDrive, attachEntryStep, if_neg he, replay,
        ih hrest, Part.bind_map, Part.map_bind, Part.map_map, Function.comp_def]
      simp [List.append_assoc]

/-- A history that queries a blocked interface drives to nothing. -/
theorem attachDrive_blkDDC_none {i : P} (s : System.Resource P X Y) :
    ∀ {l : List (P × X)} {c : List (DDC.CIn X Y)} {rs : List (P × X)},
      (∃ e ∈ l, e.1 = i) →
      attachDrive i (blkDDC (X := X) (Y := Y)) s (c, rs) l = Part.none := by
  intro l
  induction l with
  | nil => intro _ _ h; obtain ⟨e, he, -⟩ := h; cases he
  | cons e rest ih =>
      intro c rs h
      by_cases he : e.1 = i
      · rw [Part.eq_none_iff]
        intro b hb
        simp only [attachDrive, Part.mem_bind_iff] at hb
        obtain ⟨r₁, hr₁, -⟩ := hb
        simp only [attachEntryStep, if_pos he] at hr₁
        rw [attachResolve_none i blkDDC s rfl] at hr₁
        exact Part.notMem_none _ hr₁
      · obtain ⟨e', he', hi⟩ := h
        rcases List.mem_cons.mp he' with rfl | he'rest
        · exact absurd hi he
        rw [Part.eq_none_iff]
        intro b hb
        simp only [attachDrive, Part.mem_bind_iff] at hb
        obtain ⟨r₁, -, hb⟩ := hb
        rw [ih ⟨e', he'rest, hi⟩] at hb
        simp at hb

/-- **Blocking restricts the domain** (MR16 §3.4: "the resource `R⊣` only
has a left interface"): attaching `⊣` at `i` is exactly the restriction of
`s` to `i`-free histories. -/
theorem attachAt_blkDDC (i : P) (s : System.Resource P X Y) :
    attachAt i (blkDDC (X := X) (Y := Y)) s =
      System.filterDom (fun l : List (P × X) => ∀ e ∈ l, e.1 ≠ i)
        (fun _ _ hpre h e' he' => h e' (hpre.subset he')) s := by
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · intro hy
    simp only [attachAt] at hy
    simp only [attachRaw, Part.mem_bind_iff] at hy
    obtain ⟨r, hr, hy⟩ := hy
    by_cases hfree : ∀ e ∈ l, e.1 ≠ i
    · rw [attachDrive_of_no_query blkDDC s hfree] at hr
      obtain ⟨ys, hys, hreq⟩ := (Part.mem_map_iff _).mp hr
      subst hreq
      cases hlast : ys.getLast? with
      | none =>
          rw [hlast] at hy
          exact absurd hy (Part.notMem_none _)
      | some y' =>
          rw [hlast] at hy
          have : y = y' := Part.mem_some_iff.mp hy
          subst this
          have hmem : y ∈ s.1 ([] ++ l) := mem_of_replay_getLast hys hlast
          obtain ⟨hd, hv⟩ := (show y ∈ s.1 l by simpa using hmem)
          exact ⟨⟨hd, hfree⟩, hv⟩
    · push_neg at hfree
      obtain ⟨e, he, hi⟩ := hfree
      rw [attachDrive_blkDDC_none s ⟨e, he, hi⟩] at hr
      exact absurd hr (Part.notMem_none _)
  · intro hy
    obtain ⟨⟨hdom, hfree⟩, hval⟩ := hy
    have hyS : y ∈ s.1 l := ⟨hdom, hval⟩
    have hne : l ≠ [] := by
      rintro rfl
      exact System.empty_not_mem s hdom
    obtain ⟨ys, hys, hlast⟩ :=
      exists_replay_of_mem (l := l) (rs := []) (by simpa using hyS) hne
    simp only [attachAt]
    simp only [attachRaw, Part.mem_bind_iff]
    refine ⟨(ys, ([], [] ++ l)), ?_, ?_⟩
    · rw [attachDrive_of_no_query blkDDC s hfree]
      exact Part.mem_map _ hys
    · rw [hlast]
      exact Part.mem_some_iff.mpr rfl

/-- Any attachment is transparent on histories that never query its
interface. -/
theorem attachAt_transparent {i : P} (β : DDC X Y X Y)
    (s : System.Resource P X Y) {l : List (P × X)}
    (hfree : ∀ e ∈ l, e.1 ≠ i) :
    (attachAt i β s).1 l = s.1 l := by
  apply Part.ext
  intro y
  constructor
  · intro hy
    simp only [attachAt] at hy
    simp only [attachRaw, Part.mem_bind_iff] at hy
    obtain ⟨r, hr, hy⟩ := hy
    rw [attachDrive_of_no_query β s hfree] at hr
    obtain ⟨ys, hys, hreq⟩ := (Part.mem_map_iff _).mp hr
    subst hreq
    cases hlast : ys.getLast? with
    | none =>
        rw [hlast] at hy
        exact absurd hy (Part.notMem_none _)
    | some y' =>
        rw [hlast] at hy
        have : y = y' := Part.mem_some_iff.mp hy
        subst this
        simpa using mem_of_replay_getLast hys hlast
  · intro hy
    have hne : l ≠ [] := by
      rintro rfl
      exact System.empty_not_mem s ((PFun.mem_dom _ _).mpr ⟨y, hy⟩)
    obtain ⟨ys, hys, hlast⟩ :=
      exists_replay_of_mem (l := l) (rs := []) (by simpa using hy) hne
    simp only [attachAt]
    simp only [attachRaw, Part.mem_bind_iff]
    refine ⟨(ys, ([], [] ++ l)), ?_, ?_⟩
    · rw [attachDrive_of_no_query β s hfree]
      exact Part.mem_map _ hys
    · rw [hlast]
      exact Part.mem_some_iff.mpr rfl

/-- **Blocking absorbs any converter at the same interface**: `Rβ⊣ = R⊣`.
The model is query-driven, so a converter behind a blocked interface is
never activated. -/
theorem attachAt_blkDDC_absorb (i : P) (β : DDC X Y X Y)
    (s : System.Resource P X Y) :
    attachAt i (blkDDC (X := X) (Y := Y)) (attachAt i β s) =
      attachAt i (blkDDC (X := X) (Y := Y)) s := by
  rw [attachAt_blkDDC, attachAt_blkDDC]
  apply Subtype.ext
  funext l
  apply Part.ext
  intro y
  constructor
  · rintro ⟨⟨hdom, hfree⟩, hval⟩
    have hmem : y ∈ s.1 l := by
      rw [← attachAt_transparent β s hfree]
      exact ⟨hdom, hval⟩
    obtain ⟨hd', hv'⟩ := hmem
    exact ⟨⟨hd', hfree⟩, hv'⟩
  · rintro ⟨⟨hdom, hfree⟩, hval⟩
    have hmem : y ∈ (attachAt i β s).1 l := by
      rw [attachAt_transparent β s hfree]
      exact ⟨hdom, hval⟩
    obtain ⟨hd', hv'⟩ := hmem
    exact ⟨⟨hd', hfree⟩, hv'⟩

/-- Absorption on laws. -/
theorem attachAtLaw_blkDDC_absorb (i : P) (β : DDC X Y X Y)
    (S : PDS (P × X) Y) :
    attachAtLaw i (blkDDC (X := X) (Y := Y)) (attachAtLaw i β S) =
      attachAtLaw i (blkDDC (X := X) (Y := Y)) S := by
  unfold attachAtLaw
  rw [Distribution.fTransform_fTransform]
  exact congrArg (fun f => Distribution.fTransform f S)
    (funext fun s => attachAt_blkDDC_absorb i β s)

end General

/-- `⊣` attached at `i` is a converter attached within `{i}`. -/
theorem blkDDC_mem_attachedWithin (i : P) :
    attachFamily i (blkDDC (X := X) (Y := Y)) ∈
      AbstractCryptography.attachedWithin
        (attachFamily (P := P) (X := X) (Y := Y)) {i} :=
  AbstractCryptography.mem_attachedWithin_of_attach _ (Set.mem_singleton i) _

set_option maxHeartbeats 1000000 in
/-- **Every resource of this carrier is right-outbound** with respect to
single-interface blocking: the model is query-driven, so any word of
converters behind a blocked interface is never activated.  (MR16 §3.4 keeps
right-outboundness as a property because the abstract layer must also serve
carriers with spontaneous outputs; on this carrier it is a theorem.) -/
theorem rightOutbound_attach (i : P) (S : PDS (P × X) Y) :
    AbstractCryptography.RightOutbound
      ((AbstractCryptography.attachedWithin
        (attachFamily (P := P) (X := X) (Y := Y)) {i}).subtype)
      ⟨attachFamily i blkDDC, blkDDC_mem_attachedWithin i⟩ S := by
  have key : ∀ b ∈ AbstractCryptography.attachedWithin
      (attachFamily (P := P) (X := X) (Y := Y)) {i},
      ∀ T : PDS (P × X) Y,
        (attachFamily i (blkDDC (X := X) (Y := Y))) • b • T =
          (attachFamily i (blkDDC (X := X) (Y := Y))) • T := by
    intro b hb
    induction hb using Submonoid.closure_induction with
    | mem x hx =>
        intro T
        simp only [Set.mem_iUnion] at hx
        obtain ⟨i', hi', α, rfl⟩ := hx
        obtain rfl : i = i' := hi'.symm
        simp only [attachFamily, connection_smul_letter]
        exact General.attachAtLaw_blkDDC_absorb i α T
    | one => intro T; rw [one_smul]
    | mul x y hx hy ihx ihy =>
        intro T
        rw [mul_smul, ihx (y • T), ihy T]
  intro β
  exact key β.1 β.2 S

end Converter

end RandomSystems

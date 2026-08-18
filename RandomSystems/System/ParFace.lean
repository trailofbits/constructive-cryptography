/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.StarFullyDefined
import RandomSystems.System.ParFrame
import AbstractCryptography.Specification.Parallel
import AbstractCryptography.Specification.ConstructorClass
import AbstractCryptography.Metric.Epsilon

/-!
# MauRen16 §2.1's parallel composition at `Φ`, addressed by the left face

`RandomSystems.par` takes the splitting `c : Set Uni` as an argument, so it is
a *family* of binary operations and not the `Par Φ` of
`AbstractCryptography.Refinement.Basic`.  This file elects the splitting from
the left argument itself,

  `parF L M := RandomSystems.par (RandomSystems.support L) L M`,

registers `instance : Par Phi`, and proves the facts that make the election
canonical rather than arbitrary.

## The face

The addressing set is the resource's own **interface set**
`RandomSystems.support R = ⋃ S ∈ R.support, System.support S`
(`Phi.lean:351`) — MauRen16's "face" of a resource.  It is *adopted*, not
re-declared: the definition already existed in the tree and was unreferenced.
Its typed analogue `PDS.faceT` is new (there was none), and is what lets the
face of an *included* typed resource be computed.

## Why the election is canonical

`par_eq_parF_of_separating` says: **every** splitting that puts `L`'s face on
its own side and keeps `M`'s face off it computes the same system.  So on the
separated regime — the regime in which MauRen16 §2.1 writes `[𝓡₁, 𝓡₂]` at all
— the choice of `c` carries no information, and `parF` is not a choice.  The
general statement is the two-splitting form `System.par_eq_of_separating`; the
Φ-level election is the instance at `c' := RandomSystems.support L`.

## Addressing is value-level

Self-composition — `n` copies of one resource in one tuple — is obtained by
`PDS.copy`, which moves each copy into its own **value-level** fiber
`{p : ι × X | p.1 = k}` of a single typed alphabet.  Type-level tags were
refuted (they need type-constructor injectivity, which is neither provable nor
refutable); the only injectivity spent here is `System.encode_injective` at one
type, which is a theorem.

## The regime is a hypothesis, always

`parF` is a total operation but is parallel composition only on separated
faces: `parF_absorb` shows that a right argument whose face already fits inside
the left one is never asked anything and is forgotten down to its total mass.
Every law below therefore carries its separation hypothesis explicitly, and the
user surface (`PDS.copy` / `PDS.tuple`) is built so that the hypothesis is
discharged by construction.

## The converter side

`instParConverterMonoidAt` is MauRen11 §6.2's `α∣β` at the metric-facing `Σ`,
with the fn.-23 ruling recorded at the instance, and the framing law relating
the two `Par`s — `(α∣β)ⁱ(𝓡‖𝓢) = αⁱ𝓡 ‖ βⁱ𝓢` — is `smul_parF`, read at `parF`
through canonicity from the carrier theorem in `ParFrame.lean`.  Both abstract
classes that would carry those equations *unconditionally* (`SMulParClass`,
`IsNonexpandingPar`) are uninstantiable here; the M5 header says why, the
conditional theorems replace them, and `constructs_epsilonRelaxation_parF` is
the JM20 Corollary 1 endpoint assembled from the two of them.

## The admitted constructor set `Γ` (matrix row 2)

The last section of the file instantiates
`AbstractCryptography.Constructible` — MauRen16 §2.1's `∃ γ ∈ Γ : ℛ —γ→ 𝒮`,
the possibility side of `↛` — at this carrier, in the two readings the paper
actually uses.  It is a *reading* of the endpoints above and below, not new
mathematics: every proof is one application of an abstract combinator to an
existing carrier theorem.  See the section header for which class plays `Γ` in
which reading and why.
-/

namespace Probability.Distribution

/-- The support of a pushforward along an **injective** map is the image of the
support.  Without injectivity only `⊆` holds: the carrier is signed, and
cancellation inside a fiber can kill an image atom
(`exists_mem_support_of_mem_support_fTransform`'s own docstring).

Stated here because `RandomSystems.System.ParFace` is its only consumer, in the
same way the leg-(b) DDC-general bridges live in `AttachEngineFully.lean`. -/
theorem support_fTransform_of_injective {A B : Type*} [DecidableEq B] (f : A → B)
    (hf : Function.Injective f) (X : Distribution A) :
    (Distribution.fTransform f X).support = X.support.image f := by
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Distribution.mem_support_fTransform f X hb
    exact Finset.mem_image_of_mem f ha
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine Finsupp.mem_support_iff.mpr ?_
    rw [Distribution.fTransform_injective_apply X f hf a]
    exact Finsupp.mem_support_iff.mp ha

end Probability.Distribution

namespace RandomSystems

open Probability (Distribution)

universe u v

noncomputable section

open Classical

/-! ## M1 — the typed face and the face of an included typed resource -/

namespace System

variable {X Y : Type u}

/-- The support of an included deterministic system is the **image** of its
support.  `support_ofTyped` gives only the containment in the type-tag cylinder
`{q | q.1 = X}`; this is the sharp form the face equation needs. -/
theorem support_ofTyped_eq (S : DDS X Y) :
    System.support (System.ofTyped S) = System.encode X '' System.support S := by
  ext q
  constructor
  · rintro ⟨l, hl, hq⟩
    have hraw : (ofTypedRaw S l).Dom := hl.2 l (List.prefix_refl _) hl.1
    obtain ⟨hdec, -⟩ := hraw
    set lx := (decodeList X l).get hdec with hlx
    have heq : l = lx.map (System.encode X) :=
      decodeList_mem_eq (Part.get_mem hdec)
    have hne : lx ≠ [] := by
      intro h
      rw [h, List.map_nil] at heq
      exact hl.1 heq
    have hdom : lx ∈ dom S := (mem_dom_ofTyped_encode hne).mp (by rw [← heq]; exact hl)
    rw [heq] at hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact ⟨x, ⟨lx, hdom, hx⟩, rfl⟩
  · rintro ⟨x, ⟨lx, hlx, hx⟩, rfl⟩
    have hne : lx ≠ [] := by
      intro h; rw [h] at hx; exact absurd hx List.not_mem_nil
    exact ⟨lx.map (System.encode X), (mem_dom_ofTyped_encode hne).mpr hlx,
      List.mem_map_of_mem hx⟩

/-- **Inclusion into `Uni` is injective.**  Needed to turn the support of the
pushforward `PDS.ofTyped` into the *image* of the support: the law carrier is
signed, so without injectivity only `⊆` is available, and the face equation is
an equation. -/
theorem ofTyped_injective :
    Function.Injective (System.ofTyped (X := X) (Y := Y)) := by
  intro S T h
  apply Subtype.ext
  funext lx
  rcases eq_or_ne lx [] with rfl | hne
  · refine Part.ext' ?_ (fun h₁ _ => absurd h₁ (System.empty_not_mem S))
    exact ⟨fun hh => absurd hh (System.empty_not_mem S),
           fun hh => absurd hh (System.empty_not_mem T)⟩
  · have hiff : lx ∈ dom S ↔ lx ∈ dom T := by
      constructor
      · intro hS
        exact (mem_dom_ofTyped_encode (S := T) hne).mp
          (h ▸ (mem_dom_ofTyped_encode hne).mpr hS)
      · intro hT
        exact (mem_dom_ofTyped_encode (S := S) hne).mp
          (h ▸ (mem_dom_ofTyped_encode hne).mpr hT)
    refine Part.ext' hiff (fun hS hT => ?_)
    have hA : lx.map (System.encode X) ∈ dom (System.ofTyped S) :=
      (mem_dom_ofTyped_encode hne).mpr hS
    have hB : lx.map (System.encode X) ∈ dom (System.ofTyped T) :=
      (mem_dom_ofTyped_encode hne).mpr hT
    have hmemS : System.encode Y (output S lx hS) ∈
        (System.ofTyped S).1 (lx.map (System.encode X)) :=
      ⟨hA, output_ofTyped_encode hS hA⟩
    have hmemT : System.encode Y (output T lx hT) ∈
        (System.ofTyped T).1 (lx.map (System.encode X)) :=
      ⟨hB, output_ofTyped_encode hT hB⟩
    rw [h] at hmemS
    exact System.encode_injective Y (Part.mem_unique hmemS hmemT)

end System

namespace PDS

variable {X : Type u} {Y : Type v}

/-- **The typed face** (coinage, flagged): the interface set of a typed
resource — the union of its behaviours' supports.  This is
`RandomSystems.support` one carrier down; the tree had the `Φ`-level union
(`Phi.lean:351`) and no typed analogue, and the face of an included typed
resource cannot even be *stated* without it. -/
def faceT (R : PDS X Y) : Set X :=
  ⋃ S ∈ R.support, System.support S

theorem subset_faceT {R : PDS X Y} {S : System.DDS X Y} (hS : S ∈ R.support) :
    System.support S ⊆ faceT R :=
  fun _ hq => Set.mem_iUnion₂.mpr ⟨S, hS, hq⟩

end PDS

/-- A behaviour's support sits inside the resource's face — the `Φ`-level
companion of `PDS.subset_faceT`, and the only way `RandomSystems.support` is
ever entered. -/
theorem subset_support_of_mem_support {L : Phi.{u}}
    {S : System.DDS Uni.{u} Uni.{u}} (hS : S ∈ (L : PDS Uni.{u} Uni.{u}).support) :
    System.support S ⊆ RandomSystems.support L :=
  fun _ hq => Set.mem_iUnion₂.mpr ⟨S, hS, hq⟩

/-- **M1 — the face of an included typed resource.**  Including a typed
resource into `Φ` moves its face along `encode` and nothing else.

Both injectivities are spent here: `System.ofTyped_injective` at the law level
(the signed carrier), and `System.support_ofTyped_eq` at the deterministic
level. -/
theorem faceT_ofTyped {X Y : Type u} (R : PDS X Y) :
    RandomSystems.support (RandomSystems.ofTyped R) = System.encode X '' PDS.faceT R := by
  show (⋃ S ∈ (Distribution.fTransform
      (System.ofTyped (X := X) (Y := Y)) R).support, System.support S) = _
  rw [Distribution.support_fTransform_of_injective _ System.ofTyped_injective R]
  ext q
  simp only [Set.mem_iUnion, Finset.mem_image, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨S, ⟨T, hT, rfl⟩, hq⟩
    rw [System.support_ofTyped_eq] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨x, Set.mem_iUnion₂.mpr ⟨T, hT, hx⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨T, hT, hxT⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨System.ofTyped T, ⟨T, hT, rfl⟩,
      by rw [System.support_ofTyped_eq]; exact ⟨x, hxT, rfl⟩⟩

/-! ## M2 — canonicity of the splitting, at the deterministic core

The load-bearing claim of the design: on the separated regime the splitting is
not a choice.  Everything rests on one receipt — an accepted history of a
parallel composition mentions no query outside the two components' supports —
so the two splittings refuse everywhere they disagree. -/

namespace System

variable {X : Type u} {Y : Type v}

/-- **The refusal receipt.**  Every query in an accepted history of a parallel
composition lies in one of the two components' supports.

This is what makes the face determine dispatch.  `System.support S` is *derived
from* `dom S` (`{q | ∃ l ∈ dom S, q ∈ l}`), and `mem_dom_par` requires each
component's whole sub-history to lie in that component's domain; so a query
belonging to neither support could not appear in an accepted history at all. -/
theorem mem_support_of_mem_dom_par (c : Set X) (R S : DDS X Y) {l : List X}
    (hl : l ∈ dom (System.par c R S)) {q : X} (hq : q ∈ l) :
    q ∈ System.support R ∪ System.support S := by
  obtain ⟨-, hR, hS⟩ := (mem_dom_par c R S l).mp hl
  by_cases hc : q ∈ c
  · refine Or.inl ?_
    have hmem : q ∈ historyAt c l := (mem_historyAt c l q).mpr ⟨hq, hc⟩
    rcases hR with hemp | hdom
    · rw [hemp] at hmem; exact absurd hmem List.not_mem_nil
    · exact ⟨historyAt c l, hdom, hmem⟩
  · refine Or.inr ?_
    have hmem : q ∈ historyAt cᶜ l := (mem_historyAt cᶜ l q).mpr ⟨hq, hc⟩
    rcases hS with hemp | hdom
    · rw [hemp] at hmem; exact absurd hmem List.not_mem_nil
    · exact ⟨historyAt cᶜ l, hdom, hmem⟩

/-- Two separating splittings assign the same owner to every query either
component can be asked. -/
theorem mem_iff_of_separating {c c' : Set X} {R S : DDS X Y}
    (hR : System.support R ⊆ c ∩ c')
    (hS : Disjoint (System.support S) (c ∪ c'))
    {q : X} (hq : q ∈ System.support R ∪ System.support S) :
    (q ∈ c ↔ q ∈ c') := by
  rcases hq with h | h
  · exact iff_of_true (hR h).1 (hR h).2
  · have : q ∉ c ∪ c' := fun hmem => (Set.disjoint_left.mp hS h) hmem
    exact iff_of_false (fun hc => this (Or.inl hc)) (fun hc => this (Or.inr hc))

/-- Sub-histories agree once every entry has the same owner. -/
theorem historyAt_congr {c c' : Set X} {l : List X}
    (h : ∀ q ∈ l, (q ∈ c ↔ q ∈ c')) : historyAt c l = historyAt c' l := by
  refine List.filter_congr ?_
  intro q hq
  simp only [decide_eq_decide]
  exact h q hq

/-- Separating splittings accept the same histories. -/
theorem mem_dom_par_iff_of_separating {c c' : Set X} {R S : DDS X Y}
    (hR : System.support R ⊆ c ∩ c')
    (hS : Disjoint (System.support S) (c ∪ c')) (l : List X) :
    l ∈ dom (System.par c R S) ↔ l ∈ dom (System.par c' R S) := by
  have key : ∀ (d d' : Set X), System.support R ⊆ d ∩ d' →
      Disjoint (System.support S) (d ∪ d') →
      l ∈ dom (System.par d R S) → l ∈ dom (System.par d' R S) := by
    intro d d' hRd hSd hmem
    have hown : ∀ q ∈ l, (q ∈ d ↔ q ∈ d') := fun q hq =>
      mem_iff_of_separating hRd hSd (mem_support_of_mem_dom_par d R S hmem hq)
    have h1 : historyAt d l = historyAt d' l := historyAt_congr hown
    have h2 : historyAt dᶜ l = historyAt d'ᶜ l :=
      historyAt_congr (fun q hq => by
        simp only [Set.mem_compl_iff]
        exact not_congr (hown q hq))
    obtain ⟨hne, hL, hRt⟩ := (mem_dom_par d R S l).mp hmem
    exact (mem_dom_par d' R S l).mpr ⟨hne, h1 ▸ hL, h2 ▸ hRt⟩
  constructor
  · exact key c c' hR hS
  · refine key c' c ?_ ?_
    · exact fun q hq => ⟨(hR hq).2, (hR hq).1⟩
    · rw [Set.union_comm]; exact hS

/-- **Canonicity, general two-splitting form.**  Two splittings that separate
`R` from `S` compose them into the *same* system.

The Φ-level election needs this general form, not merely the instance at
`c' := System.support R`: at Φ the canonical splitting is the union over *all*
of the left law's atoms, which for an individual atom is strictly larger than
that atom's own support. -/
theorem par_eq_of_separating {c c' : Set X} (R S : DDS X Y)
    (hR : System.support R ⊆ c ∩ c')
    (hS : Disjoint (System.support S) (c ∪ c')) :
    System.par c R S = System.par c' R S := by
  have hdom := mem_dom_par_iff_of_separating hR hS
  apply Subtype.ext
  funext l
  refine Part.ext' (hdom l) fun h₁ h₂ => ?_
  show output (System.par c R S) l h₁ = output (System.par c' R S) l h₂
  obtain ⟨L, e, rfl⟩ : ∃ L e, l = L ++ [e] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, e, rfl⟩
    · exact absurd rfl ((mem_dom_par c R S []).mp h₁).1
    · exact ⟨L, e, List.concat_eq_append⟩
  have hown : ∀ q ∈ L ++ [e], (q ∈ c ↔ q ∈ c') := fun q hq =>
    mem_iff_of_separating hR hS (mem_support_of_mem_dom_par c R S h₁ hq)
  have hownL : ∀ q ∈ L, (q ∈ c ↔ q ∈ c') := fun q hq =>
    hown q (List.mem_append_left _ hq)
  have hL : historyAt c L = historyAt c' L := historyAt_congr hownL
  have hLc : historyAt cᶜ L = historyAt c'ᶜ L :=
    historyAt_congr (fun q hq => by
      simp only [Set.mem_compl_iff]; exact not_congr (hownL q hq))
  have hOwnE : (e ∈ c ↔ e ∈ c') := hown e (by simp)
  by_cases he : e ∈ c
  · have he' : e ∈ c' := hOwnE.mp he
    have hd : historyAt c L ++ [e] ∈ dom R :=
      mem_dom_left_of_mem_dom_par c R S L e he h₁
    have hd' : historyAt c' L ++ [e] ∈ dom R :=
      mem_dom_left_of_mem_dom_par c' R S L e he' h₂
    rw [output_par_mem c R S L e he h₁ hd, output_par_mem c' R S L e he' h₂ hd']
    exact output_congr R (by rw [hL]) hd hd'
  · have he' : e ∉ c' := fun hc => he (hOwnE.mpr hc)
    have hd : historyAt cᶜ L ++ [e] ∈ dom S :=
      mem_dom_right_of_mem_dom_par c R S L e he h₁
    have hd' : historyAt c'ᶜ L ++ [e] ∈ dom S :=
      mem_dom_right_of_mem_dom_par c' R S L e he' h₂
    rw [output_par_not_mem c R S L e he h₁ hd,
      output_par_not_mem c' R S L e he' h₂ hd']
    exact output_congr S (by rw [hLc]) hd hd'

/-! ### The other extreme: a right component with nowhere to answer -/

theorem historyAt_eq_self {c : Set X} {l : List X} (h : ∀ q ∈ l, q ∈ c) :
    historyAt c l = l :=
  List.filter_eq_self.mpr fun q hq => by simpa using h q hq

theorem historyAt_compl_eq_nil {c : Set X} {l : List X} (h : ∀ q ∈ l, q ∈ c) :
    historyAt cᶜ l = [] :=
  List.filter_eq_nil_iff.mpr fun q hq => by simpa using h q hq

/-- **The absorption, at the deterministic core.**  If the *right* component's
whole support sits inside the splitting, it never receives a legal query and
the composition is the left component alone.

This is not a defect: it is what electing a splitting that already covers both
components means.  It is the reason every law below carries a separation
hypothesis. -/
theorem par_eq_left_of_support_subset {c : Set X} (R S : DDS X Y)
    (hR : System.support R ⊆ c) (hS : System.support S ⊆ c) :
    System.par c R S = R := by
  have hall : ∀ {l : List X}, l ∈ dom R → ∀ q ∈ l, q ∈ c :=
    fun {l} hl q hq => hR ⟨l, hl, hq⟩
  have hcompl : ∀ {l : List X}, (historyAt cᶜ l = [] ∨ historyAt cᶜ l ∈ dom S) →
      historyAt cᶜ l = [] := by
    intro l h
    rcases h with h | h
    · exact h
    · by_contra hne
      obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hne
      exact ((mem_historyAt cᶜ l q).mp hq).2 (hS ⟨_, h, hq⟩)
  have hdom : ∀ l : List X, l ∈ dom (System.par c R S) ↔ l ∈ dom R := by
    intro l
    rw [mem_dom_par]
    constructor
    · rintro ⟨hne, hL, hR'⟩
      have hemp := hcompl hR'
      have hself : historyAt c l = l := by
        refine historyAt_eq_self fun q hq => ?_
        by_contra hc
        have : q ∈ historyAt cᶜ l := (mem_historyAt cᶜ l q).mpr ⟨hq, hc⟩
        rw [hemp] at this
        exact absurd this List.not_mem_nil
      rcases hL with h | h
      · exact absurd (hself ▸ h) hne
      · rwa [hself] at h
    · intro hl
      exact ⟨fun h => System.empty_not_mem R (h ▸ hl),
        Or.inr (by rw [historyAt_eq_self (hall hl)]; exact hl),
        Or.inl (historyAt_compl_eq_nil (hall hl))⟩
  apply Subtype.ext
  funext l
  refine Part.ext' (hdom l) fun h₁ h₂ => ?_
  show output (System.par c R S) l h₁ = output R l h₂
  obtain ⟨L, e, rfl⟩ : ∃ L e, l = L ++ [e] := by
    rcases List.eq_nil_or_concat l with rfl | ⟨L, e, rfl⟩
    · exact absurd h₂ (System.empty_not_mem R)
    · exact ⟨L, e, List.concat_eq_append⟩
  have hallL : ∀ q ∈ L, q ∈ c := fun q hq => hall h₂ q (List.mem_append_left _ hq)
  have he : e ∈ c := hall h₂ e (by simp)
  have hd : historyAt c L ++ [e] ∈ dom R := by
    rw [historyAt_eq_self hallL]; exact h₂
  rw [output_par_mem c R S L e he h₁ hd]
  exact output_congr R (by rw [historyAt_eq_self hallL]) hd h₂

end System

/-! ## M2 — `parF`, the `Par Φ` instance, and its laws -/

/-- **MauRen16 §2.1's parallel composition at `Φ`** (coinage, flagged): the
splitting is read off the left argument's own face.

`RandomSystems.par` is a family indexed by a splitting `c : Set Uni`, and
`AbstractCryptography.Par` is a bare binary operation; `parF` closes the gap by
electing `c := RandomSystems.support L`.  By `par_eq_parF_of_separating` the
election is canonical wherever the two arguments are separated — which is the
only regime in which the paper writes `[𝓡₁, 𝓡₂]` at all. -/
def parF (L M : Phi.{u}) : Phi.{u} :=
  RandomSystems.par (RandomSystems.support L) L M

/-- **The `Par Φ` instance** — the object matrix rows 4 and 6 have been
missing.  Every `∥` written at `Phi` from here on is `parF`.

Read `parF_absorb` before using it bare: the operation is total, but it is
parallel composition only on separated faces. -/
instance instParPhi : AbstractCryptography.Par Phi.{u} := ⟨parF⟩

theorem par_eq_parF (L M : Phi.{u}) : AbstractCryptography.Par.par L M = parF L M := rfl

/-- **Φ-level canonicity, two-splitting form.**  The atoms of `L` and `M` are
separated by both splittings, so the two pushforwards agree atom by atom. -/
theorem phi_par_eq_of_separating {c c' : Set Uni.{u}} (L M : Phi.{u})
    (hL : RandomSystems.support L ⊆ c ∩ c')
    (hM : Disjoint (RandomSystems.support M) (c ∪ c')) :
    RandomSystems.par c L M = RandomSystems.par c' L M := by
  show Distribution.fTransform _ (Distribution.prod L M) =
    Distribution.fTransform _ (Distribution.prod L M)
  refine Distribution.fTransform_congr _ fun p hp => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Distribution.support_prod_subset L M hp)
  exact System.par_eq_of_separating p.1 p.2
    (fun q hq => hL (subset_support_of_mem_support h1 hq))
    (Set.disjoint_left.mpr fun q hq =>
      Set.disjoint_left.mp hM (subset_support_of_mem_support h2 hq))

/-- **M2 — canonicity.**  *Every* splitting that puts `L`'s face on its own
side and keeps `M`'s face off it computes `parF L M`.  So on the separated
regime the election of `RandomSystems.support L` carries no information. -/
theorem par_eq_parF_of_separating {c : Set Uni.{u}} (L M : Phi.{u})
    (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    RandomSystems.par c L M = parF L M := by
  refine phi_par_eq_of_separating L M (Set.subset_inter hL (subset_refl _)) ?_
  rwa [Set.union_eq_self_of_subset_right hL]

/-! ### The face of a composite — the bookkeeping every nested statement needs -/

/-- The Φ-level mirror of `System.support_par`, sharp form. -/
theorem support_par_subset (c : Set Uni.{u}) (L M : Phi.{u}) :
    RandomSystems.support (RandomSystems.par c L M) ⊆
      (RandomSystems.support L ∩ c) ∪ (RandomSystems.support M ∩ cᶜ) := by
  intro q hq
  obtain ⟨S, hS, hqS⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨p, hp, rfl⟩ := Distribution.mem_support_fTransform _ _ hS
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Distribution.support_prod_subset L M hp)
  rcases System.support_par c p.1 p.2 hqS with ⟨hq1, hc⟩ | ⟨hq2, hc⟩
  · exact Or.inl ⟨subset_support_of_mem_support h1 hq1, hc⟩
  · exact Or.inr ⟨subset_support_of_mem_support h2 hq2, hc⟩

/-- **The nesting receipt.**  The containment is all the laws need; the reverse
inclusion is not free on the signed carrier and nothing here asks for it. -/
theorem support_parF_subset (L M : Phi.{u}) :
    RandomSystems.support (parF L M) ⊆
      RandomSystems.support L ∪ RandomSystems.support M := by
  intro q hq
  rcases support_par_subset (RandomSystems.support L) L M hq with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

/-- Disjointness lifts through a composite — the fold step. -/
theorem disjoint_support_parF {N L M : Phi.{u}}
    (hL : Disjoint (RandomSystems.support N) (RandomSystems.support L))
    (hM : Disjoint (RandomSystems.support N) (RandomSystems.support M)) :
    Disjoint (RandomSystems.support N) (RandomSystems.support (parF L M)) :=
  Set.disjoint_of_subset_right (support_parF_subset L M)
    (Set.disjoint_union_right.mpr ⟨hL, hM⟩)

/-! ### Commutativity and associativity, on separated faces -/

/-- **`parF` commutes on disjoint faces.**

`RandomSystems.par_comm` alone does *not* give this: it swaps the splitting to
the complement `cᶜ`, and `(support M)ᶜ` is not `support L`.  Canonicity is what
closes the last step, and it is indispensable. -/
theorem parF_comm {L M : Phi.{u}}
    (h : Disjoint (RandomSystems.support L) (RandomSystems.support M)) :
    parF L M = parF M L := by
  have h1 : parF M L = RandomSystems.par (RandomSystems.support M)ᶜ L M :=
    RandomSystems.par_comm (RandomSystems.support M) M L
  rw [h1]
  refine (par_eq_parF_of_separating L M ?_ ?_).symm
  · exact fun q hq => Set.disjoint_left.mp h hq
  · exact disjoint_compl_right

/-- **`parF` associates** — and it needs strictly less than pairwise disjoint
faces.  Nothing at all is required of `support L` against `support M`: only the
*rightmost* component's face must miss both of the others.

`RandomSystems.par_assoc` is unconditional and already merges the two
splittings as `support L ∪ support M`; the only gap left is between that union
and the composite's own face, which canonicity closes from
`support_parF_subset`. -/
theorem parF_assoc {L M N : Phi.{u}}
    (hNL : Disjoint (RandomSystems.support N) (RandomSystems.support L))
    (hNM : Disjoint (RandomSystems.support N) (RandomSystems.support M)) :
    parF L (parF M N) = parF (parF L M) N := by
  have hstep : RandomSystems.par (RandomSystems.support L) L
        (RandomSystems.par (RandomSystems.support M) M N) =
      RandomSystems.par (RandomSystems.support L ∪ RandomSystems.support M)
        (RandomSystems.par (RandomSystems.support L) L M) N :=
    RandomSystems.par_assoc (RandomSystems.support L) (RandomSystems.support M) L M N
  show RandomSystems.par (RandomSystems.support L) L (parF M N) = _
  rw [show parF M N = RandomSystems.par (RandomSystems.support M) M N from rfl, hstep]
  exact phi_par_eq_of_separating (parF L M) N
    (Set.subset_inter (support_parF_subset L M) (subset_refl _))
    (Set.disjoint_union_right.mpr
      ⟨Set.disjoint_union_right.mpr ⟨hNL, hNM⟩, disjoint_support_parF hNL hNM⟩)

/-! ### Off the separated regime: what `parF` is instead -/

/-- **`parF` absorbs its right argument whenever that argument's face already
fits inside the left one**: the right component never receives a legal query
and is forgotten down to its total mass.

The scalar is spelled through `ofPhi` because `Phi` is a `def`, so the `ℝ`
action lives on `PDS Uni Uni` and instance search does not see it at `Phi`.

This is a *documented theorem*, not a fork: it is unreachable from the
copy-based user surface of M3, where distinct copies live in distinct
value-level fibres and the hypothesis is false by `face_copy_disjoint`.  It is
recorded here because the `Par` instance is total and every abstract consumer
writes `∥` with no side condition. -/
theorem parF_absorb {L M : Phi.{u}}
    (h : RandomSystems.support M ⊆ RandomSystems.support L) :
    ofPhi (parF L M) = (ofPhi M).weight • ofPhi L := by
  show Distribution.fTransform _ (Distribution.prod (ofPhi L) (ofPhi M)) =
    (Distribution.weight (ofPhi M)) • (ofPhi L)
  rw [← Distribution.fTransform_fst_prod (ofPhi L) (ofPhi M)]
  refine Distribution.fTransform_congr _ fun p hp => ?_
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp (Distribution.support_prod_subset L M hp)
  exact System.par_eq_left_of_support_subset p.1 p.2
    (subset_support_of_mem_support h1)
    (fun q hq => h (subset_support_of_mem_support h2 hq))

/-- The sharpest reading of `parF_absorb`: a probability law composed with
itself is itself.  "Two copies of a resource" is exactly what `PDS.copy` is
for. -/
theorem parF_self {L : Phi.{u}} (h : (ofPhi L).weight = 1) : parF L L = L := by
  show ofPhi (parF L L) = ofPhi L
  rw [parF_absorb (subset_refl _), h, one_smul]

/-! ## M3 — the user surface: copies, the unit, and the tuple

`parF_self` says the operation cannot see two occurrences of one resource.  The
fix is not a guard on `parF` but a construction: put each occurrence in its own
**value-level fibre** of a single typed alphabet, so that distinct copies are
distinct queries and the separation hypotheses of M2 are discharged by
`face_copy_disjoint` rather than assumed.

Addressing is value-level by ruling: type-level tags need type-constructor
injectivity, which is neither provable nor refutable.  The only injectivity
spent below is `System.encode_injective` at the single type `ι × X`. -/

namespace System

variable {ι X : Type u} {Y : Type v}

/-- **The `k`-th copy of a deterministic system** (coinage, flagged): relabel
its queries into the fibre `ι × X` and silence every query outside fibre `k`.

Both halves already exist — `relabel` and `blockSet` (`Relabel.lean:48,141`) —
so this is a composite, not new machinery. -/
def copy (k : ι) (S : DDS X Y) : DDS (ι × X) Y :=
  blockSet {p : ι × X | p.1 ≠ k} (relabel Prod.snd id S)

/-- **Every copy lives in its own fibre.** -/
theorem support_copy (k : ι) (S : DDS X Y) :
    System.support (copy k S) ⊆ {p : ι × X | p.1 = k} := by
  rintro q ⟨l, hl, hq⟩
  have := (mem_dom_blockSet _ _ l).mp hl |>.2 q hq
  simpa using this

/-- Distinct copies are separated already at the deterministic core. -/
theorem support_copy_disjoint {k l : ι} (hkl : k ≠ l) (S T : DDS X Y) :
    Disjoint (System.support (copy k S)) (System.support (copy l T)) :=
  Set.disjoint_left.mpr fun _ hq hq' =>
    hkl ((support_copy k S hq).symm.trans (support_copy l T hq'))

/-- **The unit law at the deterministic core.**  A component whose face already
fits inside the splitting is unchanged by composing the nowhere-defined system
onto the complement. -/
theorem par_emptySystem {c : Set X} (R : DDS X Y) (hR : System.support R ⊆ c) :
    System.par c R (System.emptySystem : DDS X Y) = R := by
  refine par_eq_left_of_support_subset R System.emptySystem hR ?_
  rintro q ⟨l, hl, -⟩
  rw [System.dom_emptySystem] at hl
  exact absurd hl (Set.notMem_empty l)

end System

namespace PDS

variable {ι X : Type u} {Y : Type v}

/-- **The `k`-th copy of a typed resource.**  `n` definedness-disjoint copies
of one resource inside ONE typed alphabet, addressed by the value-level fibre
index. -/
def copy (k : ι) (R : PDS X Y) : PDS (ι × X) Y :=
  Distribution.fTransform (System.copy k) R

/-- The law-level `copy` is the tree's existing block-of-a-relabelling, so
nothing new is needed at this level either.  `PDS.blockLaw Z` is
`System.block Z` pushed forward and `System.block Z = blockSet {p | p.1 ∈ Z}`,
so `blockLaw {k}ᶜ` *is* `blockSet {p | p.1 ≠ k}`. -/
theorem copy_eq_blockLaw_relabelLaw (k : ι) (R : PDS X Y) :
    copy k R = blockLaw ({k}ᶜ : Set ι) (relabelLaw Prod.snd id R) := by
  rw [blockLaw, relabelLaw, Distribution.fTransform_fTransform]
  rfl

/-- The typed face of a copy is inside its fibre. -/
theorem faceT_copy (k : ι) (R : PDS X Y) :
    faceT (copy k R) ⊆ {p : ι × X | p.1 = k} := by
  intro q hq
  obtain ⟨S, hS, hqS⟩ := Set.mem_iUnion₂.mp hq
  obtain ⟨T, -, rfl⟩ := Distribution.mem_support_fTransform _ _ hS
  exact System.support_copy k T hqS

end PDS

/-- **M3 — distinct copies have disjoint faces at `Φ`.**  This is what makes
the tuple surface discharge M2's separation hypotheses by construction instead
of assuming them, and it is the reason `parF_absorb` is unreachable from the
surface.

The only injectivity spent is `System.encode_injective` at the single type
`ι × X` — value level, which is a theorem; no type-constructor injectivity is
involved. -/
theorem face_copy_disjoint {ι X Y : Type u} {k l : ι} (hkl : k ≠ l)
    (R S : PDS X Y) :
    Disjoint (RandomSystems.support (RandomSystems.ofTyped (PDS.copy k R)))
      (RandomSystems.support (RandomSystems.ofTyped (PDS.copy l S))) := by
  rw [faceT_ofTyped, faceT_ofTyped]
  refine Set.disjoint_left.mpr ?_
  rintro q ⟨a, ha, rfl⟩ ⟨b, hb, hba⟩
  have hab : b = a := System.encode_injective (ι × X) hba
  subst hab
  exact hkl ((PDS.faceT_copy k R ha).symm.trans (PDS.faceT_copy l S hb))

/-! ### The fold's unit

The registry names the tuple as a `parF`-fold and names no unit.  The obvious
candidate `0 : Phi` is the zero *measure* and annihilates — `prod L 0 = 0`, so a
`0`-based fold would send every tuple to `0`.  The unit is the Dirac law at the
nowhere-defined system: weight one, empty face.  It is a **right** unit only,
so the fold is a `foldr`. -/

/-- **The unit of the `parF`-fold** (coinage, flagged): the Dirac law at the
nowhere-defined system. -/
def parUnit : Phi.{u} := PDS.ofDDS (System.emptySystem : System.DDS Uni.{u} Uni.{u})

@[simp] theorem support_parUnit : RandomSystems.support (parUnit.{u}) = ∅ := by
  show (⋃ S ∈ (Finsupp.single (System.emptySystem : System.DDS Uni.{u} Uni.{u})
    (1:ℝ)).support, System.support S) = ∅
  rw [Finsupp.support_single_ne_zero _ one_ne_zero]
  ext q
  simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false,
    Finset.mem_singleton, exists_prop, not_exists]
  rintro S ⟨rfl, ⟨l, hl, -⟩⟩
  rw [System.dom_emptySystem] at hl
  exact hl

/-- The independent product against a Dirac law is a pushforward. -/
theorem PDS.prod_ofDDS_right {A : Type*} {X : Type u} {Y : Type v}
    (L : Distribution A) (t : System.DDS X Y) :
    Distribution.prod L (PDS.ofDDS t) =
      Distribution.fTransform (fun a => (a, t)) L := by
  rw [Distribution.prod_eq_sum_right]
  show ∑ b ∈ (Finsupp.single t (1:ℝ)).support,
    (Finsupp.single t (1:ℝ)) b • Distribution.fTransform (fun a => (a, b)) L = _
  rw [Finsupp.support_single_ne_zero _ (one_ne_zero (α := ℝ))]
  simp

/-- **The fold's right unit.** -/
@[simp] theorem parF_parUnit (L : Phi.{u}) : parF L parUnit.{u} = L := by
  show Distribution.fTransform _
    (Distribution.prod L (PDS.ofDDS System.emptySystem)) = L
  rw [PDS.prod_ofDDS_right, Distribution.fTransform_fTransform]
  refine Eq.trans (Distribution.fTransform_congr (g := id) L
    (fun S hS => System.par_emptySystem S (subset_support_of_mem_support hS)))
    (Distribution.fTransform_id L)

/-- The unit is **right** only.  On the left its face is empty, so the
splitting is `∅`: the left component is never asked anything and the result is
`par ∅ parUnit M`, not `M`.  This is why the fold below is a `foldr`. -/
theorem parF_parUnit_left (M : Phi.{u}) :
    parF parUnit.{u} M = RandomSystems.par (∅ : Set Uni.{u}) parUnit M := by
  show RandomSystems.par (RandomSystems.support parUnit.{u}) parUnit M = _
  rw [support_parUnit]

/-! ### The tuple -/

/-- **MauRen16 §2.1's `[𝓡₁, …, 𝓡ₙ]`** (coinage, flagged): the `parF`-fold.

The fold is a `foldr` with `parUnit` on the right, because the unit is a right
unit only (`parF_parUnit_left`).  The bracketing is therefore
`𝓡₁ ∥ (𝓡₂ ∥ (… ∥ parUnit))`; on separated leaves `parF_assoc` re-brackets it
freely. -/
def parTuple : List Phi.{u} → Phi.{u}
  | [] => parUnit
  | L :: t => parF L (parTuple t)

@[simp] theorem parTuple_nil : parTuple ([] : List Phi.{u}) = parUnit := rfl

@[simp] theorem parTuple_cons (L : Phi.{u}) (t : List Phi.{u}) :
    parTuple (L :: t) = parF L (parTuple t) := rfl

@[simp] theorem parTuple_singleton (L : Phi.{u}) : parTuple [L] = L :=
  parF_parUnit L

/-- **The fold's face is inside the union of the leaves' faces** — the
bookkeeping every nested statement needs. -/
theorem support_parTuple_subset : ∀ Ls : List Phi.{u},
    RandomSystems.support (parTuple Ls) ⊆ ⋃ L ∈ Ls, RandomSystems.support L := by
  intro Ls
  induction Ls with
  | nil => simp
  | cons L t ih =>
      intro q hq
      rcases support_parF_subset L (parTuple t) hq with h | h
      · exact Set.mem_iUnion₂.mpr ⟨L, List.mem_cons_self, h⟩
      · obtain ⟨M, hM, hqM⟩ := Set.mem_iUnion₂.mp (ih h)
        exact Set.mem_iUnion₂.mpr ⟨M, List.mem_cons_of_mem _ hM, hqM⟩

namespace PDS

/-- **The tuple of typed resources at a list of fibre indices**: include each
resource as its own copy, then fold.  Distinct indices give separated leaves by
`face_copy_disjoint`, so this surface never meets `parF_absorb`. -/
def tupleOn {ι X Y : Type u} (ks : List ι) (R : ι → PDS X Y) : Phi.{u} :=
  parTuple (ks.map fun k => RandomSystems.ofTyped (copy k (R k)))

/-- **The tuple of a finite family of typed resources.**  The fold order is
`Finset.univ.toList`'s; it is a choice, and it is the only choice this
definition makes — on separated leaves `parF_comm`/`parF_assoc` say the order
does not matter, but the *statement* that it does not is a `List.Perm`
induction that nothing here needs. -/
def tuple {ι X Y : Type u} [Fintype ι] (R : (k : ι) → PDS X Y) : Phi.{u} :=
  tupleOn (Finset.univ : Finset ι).toList R

theorem tuple_eq_tupleOn {ι X Y : Type u} [Fintype ι] (R : (k : ι) → PDS X Y) :
    tuple R = tupleOn (Finset.univ : Finset ι).toList R := rfl

/-- The tuple's face is inside the union of the copies' faces. -/
theorem support_tupleOn_subset {ι X Y : Type u} (ks : List ι) (R : ι → PDS X Y) :
    RandomSystems.support (tupleOn ks R) ⊆
      ⋃ k ∈ ks, System.encode (ι × X) '' faceT (copy k (R k)) := by
  intro q hq
  obtain ⟨L, hL, hqL⟩ := Set.mem_iUnion₂.mp (support_parTuple_subset _ hq)
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hL
  exact Set.mem_iUnion₂.mpr ⟨k, hk, by rwa [faceT_ofTyped] at hqL⟩

/-- **The binary `∥`-surface for typed resources**: the tuple at two fibre
indices.  The index type is `ULift (Fin 2)` so that the surface is available at
every universe, and the list is explicit so that the surface is *provably* the
`parF` of the two copies (`parTyped_eq_parF`). -/
def parTyped {X Y : Type u} (R S : PDS X Y) : Phi.{u} :=
  tupleOn (ι := ULift.{u} (Fin 2)) [⟨0⟩, ⟨1⟩] (fun k => ![R, S] k.down)

theorem parTyped_eq_parF {X Y : Type u} (R S : PDS X Y) :
    parTyped R S =
      parF (RandomSystems.ofTyped (copy (⟨0⟩ : ULift.{u} (Fin 2)) R))
        (RandomSystems.ofTyped (copy (⟨1⟩ : ULift.{u} (Fin 2)) S)) := by
  show parF _ (parTuple [RandomSystems.ofTyped (copy (⟨1⟩ : ULift.{u} (Fin 2)) S)]) = _
  rw [parTuple_singleton]
  rfl

/-- **The payoff.**  The two slots of the binary surface commute — the
hypothesis of `parF_comm` is discharged by `face_copy_disjoint`, not assumed.
This is the sense in which the copies mechanism, and not a guard on `parF`,
answers `parF_self`. -/
theorem parF_copy_comm {ι X Y : Type u} {k l : ι} (hkl : k ≠ l) (R S : PDS X Y) :
    parF (RandomSystems.ofTyped (copy k R)) (RandomSystems.ofTyped (copy l S)) =
      parF (RandomSystems.ofTyped (copy l S)) (RandomSystems.ofTyped (copy k R)) :=
  parF_comm (face_copy_disjoint hkl R S)

end PDS

/-! ## M4 — the metric, and the abstract consumers

**The slot terminology, pinned.**  As in `Absorb.lean`'s
`parLeft`/`parRight_mem_nonexpandingConverters`, `left`/`right` names the
position of the **fixed frame**, not of the varying argument.  The two slots
are *not* symmetric here, and the asymmetry is the whole content:

| the frame `T` sits | as a map | its splitting | verdict |
|---|---|---|---|
| on the LEFT | `M ↦ parF T M` | `support T`, **fixed** | unconditional in the varying argument |
| on the RIGHT | `L ↦ parF L T` | `support L`, **moves with the argument** | needs a common separating splitting for the two points compared |

A statement drafted from "the left argument is the conditional one" puts the
disjointness hypotheses on the wrong argument.  The conditional slot is the
frame-on-the-right one, because that is the one whose *splitting* moves. -/

section Metric

open scoped ENNReal

open AbstractCryptography (Specification Relaxation)

open scoped AbstractCryptography

/-- **The frame on the LEFT costs nothing new.**  `parF T ·` is
`par (support T) T ·`, a fixed-splitting map, so this is
`parLeft_mem_nonexpandingConverters` verbatim — unconditional in the varying
argument. -/
theorem parF_left_mem_nonexpandingConverters {T : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1) :
    (fun M => parF T M) ∈ nonexpandingConverters.{u} :=
  parLeft_mem_nonexpandingConverters (c := RandomSystems.support T) h0 h1

theorem edist_parF_left_le {T : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1) (L M : Phi.{u}) :
    edist (parF T L) (parF T M) ≤ edist L M :=
  edist_apply_le_of_mem_nonexpandingConverters
    (parF_left_mem_nonexpandingConverters h0 h1) L M

/-- **The frame on the RIGHT, repaired by canonicity.**  `parF · T` is not a
fixed-splitting map: its splitting moves with the argument, so no fixed-`c`
receipt applies to it directly.  On a pair `L, M` whose faces both sit inside
one `c` that misses `support T`, canonicity rewrites both sides to `par c · T`
and `parRight_mem_nonexpandingConverters` applies.

The price is a **common** separating splitting for the two points compared —
in practice the interface set both resources live at. -/
theorem advFullyDefined_parF_right_le {c : Set Uni.{u}} {T : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : RandomSystems.support M ⊆ c)
    (hT : Disjoint (RandomSystems.support T) c) :
    PDS.advFullyDefined (parF L T) (parF M T) ≤ PDS.advFullyDefined L M := by
  rw [← par_eq_parF_of_separating L T hL hT, ← par_eq_parF_of_separating M T hM hT]
  exact mem_nonexpandingConverters.mp
    (parRight_mem_nonexpandingConverters (c := c) h0 h1) L M

theorem edist_parF_right_le {c : Set Uni.{u}} {T : Phi.{u}}
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : RandomSystems.support M ⊆ c)
    (hT : Disjoint (RandomSystems.support T) c) :
    edist (parF L T) (parF M T) ≤ edist L M := by
  rw [edist_def, edist_def]
  exact sup_le_sup (advFullyDefined_parF_right_le h0 h1 hL hM hT)
    (advFullyDefined_parF_right_le h0 h1 hM hL hT)

/-- **The conditional form of `IsNonexpandingPar Φ`** — MauRen11 Definition 3's
inequality, with the hypotheses the signed carrier and the moving splitting
actually force:

* a common separating splitting `c` for the two points in the *left* slot,
  missing the frame `b`'s face;
* sub-probability for each of the two **fixed partners** used in the two
  triangle legs — `b` on the first leg, `a'` on the second — and not for all
  four points.

`IsNonexpandingPar Phi` as a bare instance is **not obtainable** (the class
carries no hypotheses and the carrier is signed and of arbitrary weight); this
is the deliverable in its place, and its hypothesis shape is now pinned. -/
theorem edist_parF_parF_le {c : Set Uni.{u}} {a a' b b' : Phi.{u}}
    (ha : RandomSystems.support a ⊆ c) (ha' : RandomSystems.support a' ⊆ c)
    (hb : Disjoint (RandomSystems.support b) c)
    (hb0 : ∀ t, 0 ≤ ofPhi b t) (hb1 : (ofPhi b).weight ≤ 1)
    (ha'0 : ∀ t, 0 ≤ ofPhi a' t) (ha'1 : (ofPhi a').weight ≤ 1) :
    edist (parF a b) (parF a' b') ≤ edist a a' + edist b b' :=
  (edist_triangle (parF a b) (parF a' b) (parF a' b')).trans
    (add_le_add (edist_parF_right_le hb0 hb1 ha ha' hb)
      (edist_parF_left_le ha'0 ha'1 b b'))

/-! ### CR18 Definition 5.7 at `parF` — the two clauses, hypothesised

`Relaxation.ParCompatible` *is* Definition 5.7, and
`Relaxation.epsilonRelaxation_parCompatible` proves it for the `ε`-ball — but
it takes `[IsNonexpandingPar Φ]`, which is **not obtainable at this carrier**
(`edist_parF_parF_le`'s docstring; spike G6.f), and the registry gate
`scripts/ledgerAudit.sh` check 5 keeps it uninstantiated.  What the carrier
supports is the two containments of Definition 5.7 one clause at a time, each
with the hypotheses its slot forces — and the asymmetry is the table above:
the frame on the left costs sub-probability only, the frame on the right also
costs a common separating splitting for the two points compared.

The partner is a whole specification, as Definition 5.7's own "this definition
naturally extends to specifications" asks; the hypotheses are quantified over
its laws. -/

/-- **Definition 5.7, second clause, at `parF`** — the frame on the LEFT:
`[𝒯, 𝓡ᵋ] ⊆ [𝒯, 𝓡]ᵋ`.

`parF T ·` is a fixed-splitting map for each partner law `T`, so the
containment costs exactly what `parF_left_mem_nonexpandingConverters` costs —
sub-probability of the partner — and nothing about faces. -/
theorem epsilonRelaxation_parF_left_subset (ε : ℝ≥0∞) (𝓡 𝒯 : Specification Phi.{u})
    (h0 : ∀ T ∈ 𝒯, ∀ t, 0 ≤ ofPhi T t) (h1 : ∀ T ∈ 𝒯, (ofPhi T).weight ≤ 1) :
    𝒯 ∥ Relaxation.epsilonRelaxation ε 𝓡 ⊆
      Relaxation.epsilonRelaxation ε (𝒯 ∥ 𝓡) := by
  rintro x ⟨T, hT, y, hy, rfl⟩
  obtain ⟨r, hr, hyr⟩ := Relaxation.mem_epsilonRelaxation_iff.mp hy
  exact Relaxation.mem_epsilonRelaxation_iff.mpr
    ⟨T ∥ r, AbstractCryptography.par_mem_par hT hr,
      (edist_parF_left_le (h0 T hT) (h1 T hT) y r).trans hyr⟩

/-- **Definition 5.7, first clause, at `parF`, on the face-bounded part of the
ball** — the form a consumer can actually discharge.

`parF · T` moves its own splitting with its argument, so beyond sub-probability
of the partner the right slot needs one splitting `c` that carries *both*
points compared, and one of them is an arbitrary member of the `ε`-ball rather
than a law of `𝓡`.  Restricting the ball to its `c`-faced part is the honest
way to say that, and it demands nothing of the laws it drops.  The unrestricted
clause is `epsilonRelaxation_parF_right_subset`, one hypothesis away. -/
theorem epsilonRelaxation_parF_right_subset_of_support {c : Set Uni.{u}} (ε : ℝ≥0∞)
    (𝓡 𝒯 : Specification Phi.{u})
    (h0 : ∀ T ∈ 𝒯, ∀ t, 0 ≤ ofPhi T t) (h1 : ∀ T ∈ 𝒯, (ofPhi T).weight ≤ 1)
    (hT : ∀ T ∈ 𝒯, Disjoint (RandomSystems.support T) c)
    (h𝓡 : ∀ R ∈ 𝓡, RandomSystems.support R ⊆ c) :
    {L | L ∈ Relaxation.epsilonRelaxation ε 𝓡 ∧ RandomSystems.support L ⊆ c} ∥ 𝒯 ⊆
      Relaxation.epsilonRelaxation ε (𝓡 ∥ 𝒯) := by
  rintro x ⟨y, ⟨hy, hyc⟩, T, hT', rfl⟩
  obtain ⟨r, hr, hyr⟩ := Relaxation.mem_epsilonRelaxation_iff.mp hy
  exact Relaxation.mem_epsilonRelaxation_iff.mpr
    ⟨r ∥ T, AbstractCryptography.par_mem_par hr hT',
      (edist_parF_right_le (h0 T hT') (h1 T hT') hyc (h𝓡 r hr) (hT T hT')).trans hyr⟩

/-- **Definition 5.7, first clause, at `parF`** — the frame on the RIGHT:
`[𝓡ᵋ, 𝒯] ⊆ [𝓡, 𝒯]ᵋ`.

Here `parF · T` moves its own splitting with its argument, so beyond
sub-probability of the partner the clause needs one splitting `c` that carries
both points compared — every law of `𝓡` *and* every law of the `ε`-ball around
it — and misses the partner's face.  That is `edist_parF_right_le`'s price, and
it cannot be dropped: `parF_absorb` is what a partner inside the splitting
does instead.

The clause over the whole ball is the printed form; the version that asks
nothing of the laws it drops is
`epsilonRelaxation_parF_right_subset_of_support`, of which this is the
corollary at a face-bounded ball. -/
theorem epsilonRelaxation_parF_right_subset {c : Set Uni.{u}} (ε : ℝ≥0∞)
    (𝓡 𝒯 : Specification Phi.{u})
    (h0 : ∀ T ∈ 𝒯, ∀ t, 0 ≤ ofPhi T t) (h1 : ∀ T ∈ 𝒯, (ofPhi T).weight ≤ 1)
    (hT : ∀ T ∈ 𝒯, Disjoint (RandomSystems.support T) c)
    (h𝓡 : ∀ R ∈ 𝓡, RandomSystems.support R ⊆ c)
    (hball : ∀ L ∈ Relaxation.epsilonRelaxation ε 𝓡, RandomSystems.support L ⊆ c) :
    Relaxation.epsilonRelaxation ε 𝓡 ∥ 𝒯 ⊆
      Relaxation.epsilonRelaxation ε (𝓡 ∥ 𝒯) := by
  refine subset_trans ?_ (epsilonRelaxation_parF_right_subset_of_support ε 𝓡 𝒯 h0 h1 hT h𝓡)
  rintro x ⟨y, hy, T, hT', rfl⟩
  exact AbstractCryptography.par_mem_par ⟨hy, hball y hy⟩ hT'

end Metric

/-! ### MauRen11 §6.2's `α∣β` at this `Σ`

**The footnote, read.**  MauRen11 p. 13 defines parallel converter composition
by `(α∣β)ⁱ(R‖S) := αⁱR ‖ βⁱS`, and fn. 23 immediately warns: "Note that
`(α∣β)ⁱT` need not be explicitly defined if `T` is not of the form `T = R‖S`.
Note also that `α∣1 ≠ α`."  Taken at face value that refutes `∣ := *`, which is
total and satisfies `α ∣ 1 = α`.

**Why the objection does not reach this `Σ`.**  Both halves of fn. 23 are the
same observation, and the observation is fn. 20 on the same page: "For every
`i ∈ I`, the `i`-interface of `R‖S` consists of the two `i`-interfaces of `R`
and `S` merged into a single interface, **by some addressing mechanism that is
not (yet) of interest at this level of abstraction**."  With addressing
deferred, `α` at the `i`-interface of `R‖S` reaches the *merged* interface and
may talk to both halves, while `α∣1` reaches only `R`'s half — two different
operators, hence `α∣1 ≠ α`; and `(α∣β)ⁱT` needs the halves to exist at all,
hence the partiality.

Our `Σ` **is** the addressing fn. 20 defers (the ruling that MauRen11 fn. 20
defers addressing and the Jost rendering supplies it; R7'''s addressing is
value-level).  An element of `converterMonoidAt` is an endomorphism of `Φ` that
already names the queries it acts on: `attachAt i E` runs the engine exactly at
the queries of `i` and *is the resource* everywhere else
(`System.attachEngineFully_transparent`).  There is no re-pointing step in
which the same `α` could be aimed at a merged interface instead: applied to `L`
and applied to `parF L M`, one and the same element acts at one and the same
addresses.  So `α ∣ 1 = α` is not an error here, it is the correct semantics —
and it is the tree's own reading already, recorded at
`AbstractCryptography.Constructs.par_left`: "the paper carries the **same** `π`
across the arrow, because in the concrete interface model `π` attached to
`[ℛ, 𝒯]` acts only on `ℛ`'s interfaces."

**Totality.**  Fn. 23 *permits* partiality; it does not require it, and the
abstract `Par` class asks for a total binary operation.  `∣ := *` is total, and
on the regime where MauRen11 defines `α∣β` — a composite `parF L M` of
separated faces with each converter confined to its own leg — it computes the
paper's value; that is `attachAt_parF` / `smul_parF` below.  Off that
regime `*` is serial composition, exactly as `parF` is not parallel composition
off separated faces (`parF_absorb`).  The discipline is the same on both sides
of the action: a total operation whose regime is carried by hypothesis, never
by the instance.

**Commutativity, where it is meant.**  `α ∣ β = β ∣ α` is `attachAt_comm` at
disjoint interfaces — the operation is symmetric exactly where the paper's is,
and the class asks for no law at all (`Par` "carrying no laws"). -/
instance instParConverterMonoidAt :
    AbstractCryptography.Par ↥converterMonoidAt.{u} :=
  ⟨fun α β => α * β⟩

/-- `α ∣ β` is multiplication in the interface-indexed `Σ`; see
`instParConverterMonoidAt` for the fn. 23 ruling. -/
theorem par_converterMonoidAt_eq_mul (α β : ↥converterMonoidAt.{u}) :
    AbstractCryptography.Par.par α β = α * β := rfl

/-- **`α ∣ 1 = α` at this `Σ`** — the equation MauRen11 fn. 23 denies for an
un-addressed converter set, and which holds here because the interface is a
component of the element.  Recorded as a theorem so that the ruling above is
checkable rather than only argued. -/
@[simp] theorem par_converterMonoidAt_one (α : ↥converterMonoidAt.{u}) :
    AbstractCryptography.Par.par α (1 : ↥converterMonoidAt.{u}) = α :=
  mul_one α

/-! ## M5 — the framing law at `parF`, and `SMulParClass`'s shape

`ParFrame.lean` proves the carrier statement at a *fixed* splitting.  Here it is
read at `parF`, whose splitting is the left argument's own face and therefore
**moves when the left argument is converted**: `attachAt i E L` need not have
`L`'s face, so `parF (attachAt i E L) M` is a `par` at a different splitting
than `parF L M` is.  Canonicity closes the gap exactly as it does for the
metric's right slot, and the bookkeeping it needs is
`support_attachAt_subset` — attaching at `i` adds at most the addresses of `i`,
so a left argument inside `c` stays inside `c` provided `i ⊆ c`.

**What `SMulParClass` gets, and what it does not.**  The class field is
unconditional,

  `smul_par (α β) (R S) : (α ∥ β) • (R ∥ S) = (α • R) ∥ (β • S)`,

and at this carrier the equation is false without hypotheses on *both* sides of
the action: `parF` is parallel composition only on separated faces
(`parF_absorb`), and an element of `converterMonoidAt` is confined to a leg only
by hypothesis — the closure also contains blocks and parallel frames, which are
not attachments at all.  So `SMulParClass ↥converterMonoidAt Phi` is
uninstantiable for the same reason `IsNonexpandingPar Phi` is (G6.f), and the
conditional theorem is the deliverable.  `smul_parF` below is that theorem *in
the class's own shape*, so that the mismatch is a matter of hypotheses and not
of statement. -/

section Framing

variable {i j c : Set Uni.{u}}
  {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}

/-- **The framing law at `parF`, left leg** — MauRen16 §2.2's `αⁱ[𝓡, 𝓣] =
[αⁱ𝓡, 𝓣]`, with the hypotheses this carrier forces: the interface inside a
splitting that holds the left leg's face and misses the right leg's.

The conversion of the left argument is invisible to the election of the
splitting, because `support_attachAt_subset` keeps the converted face inside the
same `c`; that is the step a statement drafted from "`parF`'s splitting is
`support L`" cannot take. -/
theorem attachAt_parF (hic : i ⊆ c) (hReq : System.RequestsWithin i E)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    attachAt i E (parF L M) = parF (attachAt i E L) M := by
  have hAL : RandomSystems.support (attachAt i E L) ⊆ c :=
    (support_attachAt_subset i E L).trans (Set.union_subset hL hic)
  rw [← par_eq_parF_of_separating L M hL hM, attachAt_par hic hReq,
    par_eq_parF_of_separating (attachAt i E L) M hAL hM]

/-- **The framing law at `parF`, right leg**: the interface sits off the
splitting, so it is the right leg that is converted. -/
theorem attachAt_parF_right (hjc : j ⊆ cᶜ) (hReq : System.RequestsWithin j F)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    attachAt j F (parF L M) = parF L (attachAt j F M) := by
  have hjdis : Disjoint j c := Set.disjoint_left.mpr fun q hq hqc => hjc hq hqc
  have hFM : Disjoint (RandomSystems.support (attachAt j F M)) c :=
    Set.disjoint_of_subset_left (support_attachAt_subset j F M)
      (Set.disjoint_union_left.mpr ⟨hM, hjdis⟩)
  rw [← par_eq_parF_of_separating L M hL hM, attachAt_par_right hjc hReq,
    par_eq_parF_of_separating L (attachAt j F M) hL hFM]

/-- **MauRen11 §6.2's `(α∣β)ⁱ(𝓡‖𝓢) = αⁱ𝓡 ‖ βⁱ𝓢` at this carrier**, on the
attachment generators: the two converters act at interfaces on opposite sides of
one splitting that separates the two legs.

Both halves are needed and neither is symmetric to the other by accident: the
right leg is converted first (its splitting is the *complement*, so the left
leg's face still elects `c`), and then the left, whose conversion is absorbed by
`support_attachAt_subset`. -/
theorem attachAt_mul_parF (hic : i ⊆ c) (hjc : j ⊆ cᶜ)
    (hE : System.RequestsWithin i E) (hF : System.RequestsWithin j F)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    (attachAt i E * attachAt j F) (parF L M)
      = parF (attachAt i E L) (attachAt j F M) := by
  have hjdis : Disjoint j c := Set.disjoint_left.mpr fun q hq hqc => hjc hq hqc
  have hFM : Disjoint (RandomSystems.support (attachAt j F M)) c :=
    Set.disjoint_of_subset_left (support_attachAt_subset j F M)
      (Set.disjoint_union_left.mpr ⟨hM, hjdis⟩)
  show attachAt i E (attachAt j F (parF L M)) = _
  rw [attachAt_parF_right hjc hF hL hM, attachAt_parF hic hE hL hFM]

/-- **`SMulParClass`'s field, at the metric-facing `Σ`, with its hypotheses
named.**  `α ∥ β` is `α * β` (`instParConverterMonoidAt`), `R ∥ S` is `parF`,
and the two converters are the attachment generators the equation holds for.

Landing this as an *instance* would require the equation for every pair of
elements of the closure — including blocks and parallel frames — and for every
pair of resources, separated or not; both are false.  This is the honest form,
and it is the class's statement verbatim once the hypotheses are supplied. -/
theorem smul_parF (hic : i ⊆ c) (hjc : j ⊆ cᶜ)
    (hE : System.RequestsWithin i E) (hF : System.RequestsWithin j F)
    {α β : ↥converterMonoidAt.{u}}
    (hα : (α : Function.End Phi.{u}) = attachAt i E)
    (hβ : (β : Function.End Phi.{u}) = attachAt j F)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    AbstractCryptography.Par.par α β • AbstractCryptography.Par.par L M
      = AbstractCryptography.Par.par (α • L) (β • M) := by
  show (α : Function.End Phi.{u}) ((β : Function.End Phi.{u}) (parF L M))
    = parF ((α : Function.End Phi.{u}) L) ((β : Function.End Phi.{u}) M)
  rw [hα, hβ]
  exact attachAt_mul_parF hic hjc hE hF hL hM

/-- The one-sided reading at the `Σ` level: `α ∣ 1 = α` (the fn. 23 ruling),
so context insensitivity in the left slot costs only the left leg's
hypotheses. -/
theorem smul_parF_left (hic : i ⊆ c) (hE : System.RequestsWithin i E)
    {α : ↥converterMonoidAt.{u}} (hα : (α : Function.End Phi.{u}) = attachAt i E)
    {L M : Phi.{u}} (hL : RandomSystems.support L ⊆ c)
    (hM : Disjoint (RandomSystems.support M) c) :
    AbstractCryptography.Par.par α (1 : ↥converterMonoidAt.{u})
        • AbstractCryptography.Par.par L M
      = AbstractCryptography.Par.par (α • L) M := by
  rw [par_converterMonoidAt_one]
  show (α : Function.End Phi.{u}) (parF L M) = parF ((α : Function.End Phi.{u}) L) M
  rw [hα]
  exact attachAt_parF hic hE hL hM

/-! ### The hypothesis set is inhabited: `⊣` through a frame

MauRen16 §3.4's blocking converter is an interface-local attachment whose engine
never moves (`exists_attachAt_eq_block`), so `System.RequestsWithin` is free and
only the two face clauses survive.  That makes `⊣` the framing law's first
inhabited instance, and the two theorems below are simultaneously a §3.4
endpoint and the receipt that `attachAt_parF` / `smul_parF_left` are not
conditionals on an unsatisfiable premise. -/

/-- **`⊣` passes through a parallel frame**: blocking a set of addresses on the
left leg's side of the splitting does not touch the right leg. -/
theorem block_parF {Q c : Set Uni.{u}} (hQc : Q ⊆ c) {L M : Phi.{u}}
    (hL : RandomSystems.support L ⊆ c) (hM : Disjoint (RandomSystems.support M) c) :
    block Q (parF L M) = parF (block Q L) M := by
  obtain ⟨Z, hZreq, hZ⟩ := exists_attachAt_eq_block Q
  rw [← hZ]
  exact attachAt_parF hQc hZreq hL hM

/-- The same at `Σ`: `⊣` is an element of `converterMonoidAt`
(`blockConverterAt`) satisfying `smul_parF_left`'s premise, so the framing law's
`Σ`-level form has an inhabited instance. -/
theorem smul_parF_blockConverterAt {Q c : Set Uni.{u}} (hQc : Q ⊆ c) {L M : Phi.{u}}
    (hL : RandomSystems.support L ⊆ c) (hM : Disjoint (RandomSystems.support M) c) :
    AbstractCryptography.Par.par (blockConverterAt Q) (1 : ↥converterMonoidAt.{u})
        • AbstractCryptography.Par.par L M
      = AbstractCryptography.Par.par (blockConverterAt Q • L) M := by
  obtain ⟨Z, hZreq, hZ⟩ := exists_attachAt_eq_block Q
  exact smul_parF_left hQc hZreq ((coe_blockConverterAt Q).trans hZ.symm) hL hM

end Framing

/-! ### The abstract consumers -/

section Consumers

open AbstractCryptography (Specification Constructs Relaxation)

open scoped AbstractCryptography

/-- Specification-level parallel composition is now available at `Phi`, and
with it the membership calculus (`mem_par_iff`, `par_mem_par`,
`singleton_par_singleton`) and the statability of
`Relaxation.ParCompatible`. -/
example (R S : Specification Phi.{u}) : Specification Phi.{u} := R ∥ S

example {R S : Specification Phi.{u}} {r s : Phi.{u}} (hr : r ∈ R) (hs : s ∈ S) :
    parF r s ∈ R ∥ S := AbstractCryptography.par_mem_par hr hs

example (R S : Phi.{u}) :
    ({R} : Specification Phi.{u}) ∥ {S} = {parF R S} :=
  AbstractCryptography.singleton_par_singleton R S


/-- **MauRen16 §2.2 / MauRen11 Definition 7(iii) through the abstract theorem**
— the shape the abstract layer supports, kept for the record.

`Specification/Parallel.lean` proves `Constructs.par_left` from three instance
arguments at `Ω := Specification Phi`, `Γ := ↥converterMonoidAt`.  Two of the
three are now instances: `Par Phi` (`instParPhi`) and `Par ↥converterMonoidAt`
(`instParConverterMonoidAt`).  The third, `SMulParClass ↥converterMonoidAt Phi`,
is **unconditional and false at this carrier** — see the M5 header: `parF` is
parallel composition only on separated faces and an element of the closure is
confined to a leg only by hypothesis — so this route stays conditional on a
hypothesis nothing can supply.

`constructs_parF_left` below is the same law *proved directly* from the framing
theorem with the hypotheses named, and is the usable form. -/
theorem contextInsensitive_par_left
    [AbstractCryptography.SMulParClass ↥converterMonoidAt.{u} Phi.{u}]
    {π : ↥converterMonoidAt.{u}} {R S : Specification Phi.{u}}
    (T : Specification Phi.{u}) (h : R —[π]→ S) :
    R ∥ T —[π ∥ (1 : ↥converterMonoidAt.{u})]→ S ∥ T :=
  Constructs.par_left T h

/-- **MauRen16 §2.2 / MauRen11 Definition 7(iii) at this carrier, unconditional
on any class** — matrix row 6's receipt, and the audit's C5.

JM20 Theorem 1.2 / MauRen11 Definition 7(iii): a construction in the left
parallel component survives an unchanged right context, with the protocol
extended by `∥ 1` — which at this `Σ` *is* the protocol
(`par_converterMonoidAt_one`).

The hypotheses are exactly the framing law's, lifted to specifications by being
asked of every member: one splitting `c` holding every source resource's face
and missing every context resource's, the protocol an attachment inside `c`
reaching only its own interface.  Nothing is asked of `S` — the target
specification is whatever the construction lands in.

This is the statement `contextInsensitive_par_left` could not make: it needs no
`SMulParClass` instance, because it consumes the conditional framing theorem
instead of the unconditional class field. -/
theorem constructs_parF_left {i c : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hic : i ⊆ c) (hReq : System.RequestsWithin i E)
    {π : ↥converterMonoidAt.{u}} (hπ : (π : Function.End Phi.{u}) = attachAt i E)
    {R S : Specification Phi.{u}} (T : Specification Phi.{u})
    (hR : ∀ r ∈ R, RandomSystems.support r ⊆ c)
    (hT : ∀ t ∈ T, Disjoint (RandomSystems.support t) c)
    (h : R —[π]→ S) :
    R ∥ T —[π ∥ (1 : ↥converterMonoidAt.{u})]→ S ∥ T := by
  rintro x ⟨y, ⟨r, hr, t, ht, rfl⟩, rfl⟩
  show AbstractCryptography.Par.par π (1 : ↥converterMonoidAt.{u})
      • AbstractCryptography.Par.par r t ∈ S ∥ T
  rw [smul_parF_left hic hReq hπ (hR r hr) (hT t ht)]
  exact AbstractCryptography.par_mem_par (h (Set.smul_mem_smul_set hr)) ht

/-- **MauRen11 Definition 7(iii)'s two-sided form at this carrier**: both legs
carry a protocol, `α` inside the splitting and `β` outside it — MauRen11 §6.2's
`α∣β` doing the work `∥ 1` did above.

Both source specifications' faces have to be separated by the *same* splitting,
which is what a two-leg statement means on this carrier and is discharged by
construction on the `PDS.copy` surface (`face_copy_disjoint`). -/
theorem constructs_parF {i j c : Set Uni.{u}}
    {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hic : i ⊆ c) (hjc : j ⊆ cᶜ)
    (hE : System.RequestsWithin i E) (hF : System.RequestsWithin j F)
    {α β : ↥converterMonoidAt.{u}}
    (hα : (α : Function.End Phi.{u}) = attachAt i E)
    (hβ : (β : Function.End Phi.{u}) = attachAt j F)
    {R S T T' : Specification Phi.{u}}
    (hR : ∀ r ∈ R, RandomSystems.support r ⊆ c)
    (hT : ∀ t ∈ T, Disjoint (RandomSystems.support t) c)
    (h : R —[α]→ S) (h' : T —[β]→ T') :
    R ∥ T —[α ∥ β]→ S ∥ T' := by
  rintro x ⟨y, ⟨r, hr, t, ht, rfl⟩, rfl⟩
  show AbstractCryptography.Par.par α β • AbstractCryptography.Par.par r t ∈ S ∥ T'
  rw [smul_parF hic hjc hE hF hα hβ (hR r hr) (hT t ht)]
  exact AbstractCryptography.par_mem_par (h (Set.smul_mem_smul_set hr))
    (h' (Set.smul_mem_smul_set ht))

/-! ### JM20 Corollary 1, item 2 — the parallel half, at the carrier

`AbstractCryptography.Constructs.epsilonRelaxation_par` consumes **two**
unconditional classes, `SMulParClass Sigma Φ` and `IsNonexpandingPar Φ`, and
neither is obtainable here: the first for the reasons in the M5 header, the
second because the carrier is signed and of arbitrary weight (G6.f — the
conditional form is `edist_parF_parF_le`).  So the abstract theorem does **not**
fire at `Φ`, and the endpoint is assembled from the two conditional halves
instead: the framing law moves the protocol inside the left leg, and
`edist_parF_right_le` — which is `IsNonexpandingPar`'s fn.-9 half at the
conditional hypotheses — carries the radius across the frame. -/

section Cor1

open scoped ENNReal

/-- **JM20 Corollary 1, item 2 at this carrier**: `ℛ —π→ 𝒮ᵋ ⟹ [ℛ, 𝒯] —π→
[𝒮, 𝒯]ᵋ`, on resources, with the hypotheses this carrier forces.

The two halves are visible in the proof and are the two things the abstract
theorem takes from classes: the protocol passes through the frame
(`smul_parF_left`, the conditional `SMulParClass`), and the radius survives the
frame (`edist_parF_right_le`, the conditional `IsNonexpandingPar`).  The
sub-probability clauses on `𝒯` are the ones `parRight_mem_nonexpandingConverters`
needs and are not bookkeeping: the frame is a converter only if it does not
inflate mass. -/
theorem edist_smul_parF_le {i c : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hic : i ⊆ c) (hReq : System.RequestsWithin i E)
    {π : ↥converterMonoidAt.{u}} (hπ : (π : Function.End Phi.{u}) = attachAt i E)
    {L L' T : Phi.{u}} {ε : ℝ≥0∞}
    (hL : RandomSystems.support L ⊆ c) (hL' : RandomSystems.support L' ⊆ c)
    (hT : Disjoint (RandomSystems.support T) c)
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1)
    (h : edist (π • L) L' ≤ ε) :
    edist (AbstractCryptography.Par.par π (1 : ↥converterMonoidAt.{u}) • parF L T)
      (parF L' T) ≤ ε := by
  have hAL : RandomSystems.support (π • L) ⊆ c := by
    show RandomSystems.support ((π : Function.End Phi.{u}) L) ⊆ c
    rw [hπ]
    exact (support_attachAt_subset i E L).trans (Set.union_subset hL hic)
  have hstep : AbstractCryptography.Par.par π (1 : ↥converterMonoidAt.{u}) • parF L T
      = parF (π • L) T := smul_parF_left hic hReq hπ hL hT
  rw [hstep]
  exact (edist_parF_right_le h0 h1 hAL hL' hT).trans h

/-- **The specification reading of `edist_smul_parF_le`** — JM20 Corollary 1
item 2 in the arrow notation, on singleton specifications, through
`constructs_singleton_epsilonRelaxation_iff`.  This is the row-6/row-4 endpoint
the parallel half of Corollary 1 was missing at the metric carrier. -/
theorem constructs_epsilonRelaxation_parF {i c : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hic : i ⊆ c) (hReq : System.RequestsWithin i E)
    {π : ↥converterMonoidAt.{u}} (hπ : (π : Function.End Phi.{u}) = attachAt i E)
    {L L' T : Phi.{u}} {ε : ℝ≥0∞}
    (hL : RandomSystems.support L ⊆ c) (hL' : RandomSystems.support L' ⊆ c)
    (hT : Disjoint (RandomSystems.support T) c)
    (h0 : ∀ t, 0 ≤ ofPhi T t) (h1 : (ofPhi T).weight ≤ 1)
    (h : ({L} : Specification Phi.{u}) —[π]→
      Relaxation.epsilonRelaxation ε ({L'} : Specification Phi.{u})) :
    ({parF L T} : Specification Phi.{u}) —[π ∥ (1 : ↥converterMonoidAt.{u})]→
      Relaxation.epsilonRelaxation ε ({parF L' T} : Specification Phi.{u}) :=
  AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr
    (edist_smul_parF_le hic hReq hπ hL hL' hT h0 h1
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mp h))

end Cor1

/-- **MauRen16 §4.3 at this carrier** — matrix row 45: an equation `πR = Sβ`
with an *inadmissible* right factor `β` becomes a construction statement by
paying a parallel resource, `R —π→ ([S, β̄])∗`.

The abstract theorem is proved; all it wanted was `Par Φ`, so this is a
one-liner now.  `[S, β̄]` is `parF S betaRes`, and `H` is MauRen16 §3.4's
admitted class at the adversary interface, `converterMonoidWithin A`.

`β ∉ H` is deliberately not carried — it is what makes the rephrasing worth
doing, and the implication holds for every `β`.

**Home.**  This belongs beside `converterMonoidWithin` in
`StarFullyDefined.lean`, and cannot live there: that module is *imported* by
this one, and the statement needs the `Par Phi` instance this one registers. -/
theorem constructs_star_par_converterMonoidWithin {A : Set Uni.{u}}
    {π β : ↥converterMonoidAt.{u}} {R S betaRes : Phi.{u}}
    (σ : ↥converterMonoidAt.{u}) (hσ : σ ∈ converterMonoidWithin A)
    (connect : σ • (S ∥ betaRes) = β • S)
    (equation : π • R = β • S) :
    ({R} : Specification Phi.{u}) —[π]→
      (Relaxation.star (converterMonoidWithin A) : Relaxation Phi.{u})
        ({S ∥ betaRes} : Specification Phi.{u}) :=
  AbstractCryptography.constructs_star_par_of_smul_eq σ hσ connect equation

/-! ### MauRen16 §2.1's admitted constructor set `Γ` at this carrier — matrix row 2

`Constructs π 𝓡 𝒮` exhibits the constructor and restricts it to nothing;
MauRen16 §2.1 restricts it to an admitted set — "typically one considers a
certain set `Γ` of constructors, possibly restricted in terms of efficiency or
implementation cost" — and phrases impossibility as the negation of that
existential, `ℛ ↛ 𝒮 :⟺ ¬∃ γ ∈ Γ : ℛ —γ→ 𝒮`.  `Unconstructible` has carried `Γ`
at this tree since RS-A; `AbstractCryptography.Constructible` is its positive
form, and this section is its instantiation here.

**Two readings, because the carrier supplies two classes.**

* **`Γ` = the metric-facing `Σ` itself**, inside all endomorphisms of the
  carrier: `Sigma := Function.End Phi`, `Γ := ↑converterMonoidAt`.  This is
  §3.5's model 1, "the converter set includes all systems": every constructor
  the tree can name is admitted, and what the statement records is that the
  *unadmitted* endomorphisms of `Φ` — the ones carrying no absorption, hence no
  Definition 2 receipt — are excluded.  Every in-tree `Constructs` endpoint at
  `↥converterMonoidAt` feeds `constructible_of_constructs_converterMonoidAt`
  verbatim, because membership is exactly what the subtype carries.
* **`Γ` = the honest class `converterMonoidWithin B`**, inside the metric-facing
  `Σ`: `Sigma := ↥converterMonoidAt`, `Γ := ↑(converterMonoidWithin B)`.  This
  is §3.5's closing paragraph — "one could consider different converter sets for
  honest parties and for dishonest parties" — with `Γ` at the honest interface
  `B` and the paper's `Σ`, the class the `∗`-relaxation ranges over, at the
  adversary interface `A`.  It is the reading in which `Constructible.star` and
  `Constructible.epsilonRelaxation_trans` fire: the first wants the two classes
  to commute, which is `commute_converterMonoidWithin` at `Disjoint B A`, and
  the second wants `IsNonexpandingSMul ↥converterMonoidAt Phi`, which
  `MetricFullyDefined.lean` registers.

Only the second reading can carry the `ε`-calculus: `IsNonexpandingSMul` is
false at `Function.End Phi` — an arbitrary endomorphism is not a converter —
so the first reading is deliberately confined to the algebra.  Both classes are
`Submonoid`s, which is MauRen16 footnote 6's closure requirement, so
`Constructible.trans` fires in either. -/

section ConstructorSet

open AbstractCryptography (Constructible Unconstructible)

open scoped ENNReal

/-- **The generic entry: `Γ` = the metric-facing `Σ`.**  Any construction whose
constructor is an element of `↥converterMonoidAt` is a construction within the
admitted set — the membership is the subtype's own second component, so *every*
`Constructs` endpoint in this tree is a `Constructible` endpoint at no cost.

`Constructs.constructible` is the abstract combinator; nothing here needs a
wrapper, because `π ∈ (↑converterMonoidAt : Set (Function.End Phi))` and
`π ∈ converterMonoidAt` are the same proposition. -/
theorem constructible_of_constructs_converterMonoidAt {π : ↥converterMonoidAt.{u}}
    {𝓡 𝓢 : Specification Phi.{u}} (h : Constructs π 𝓡 𝓢) :
    𝓡 —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→ 𝓢 :=
  Constructs.constructible π.2 h

/-- **Possibility and impossibility over one and the same `Γ`, at this
carrier.**  Matrix rows 2 and 3 quantify over the same admitted set now: the
impossibility statement the tree already carried is, definitionally, the
negation of the possibility statement above.  Until `Constructible` was
instantiated here, the carrier's impossibility side named a class its
possibility side could not. -/
theorem unconstructible_converterMonoidAt_iff {𝓡 𝓢 : Specification Phi.{u}} :
    Unconstructible (converterMonoidAt.{u} : Set (Function.End Phi.{u})) 𝓡 𝓢 ↔
      ¬ 𝓡 —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→ 𝓢 :=
  AbstractCryptography.unconstructible_iff_not_constructible

/-- **A named constructor, admitted**: an interface-indexed attachment carrying
the engine class is a constructor of `Γ`, so a law it sends to `M` is a
construction of `{M}` from `{L}` within the admitted set.  The constructor is
exhibited (`attachAt i E`) and the membership is the carrier's own
(`attachAt_mem_converterMonoidAt`); the `Γ`-statement then hides the
constructor, which is what §2.1's existential does. -/
theorem constructible_attachAt {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinUniformBudget E)
    {L M : Phi.{u}} (h : attachAt i E L = M) :
    ({L} : Specification Phi.{u}) —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→
      ({M} : Specification Phi.{u}) :=
  Constructs.constructible (attachAt_mem_converterMonoidAt i hIT hβ)
    (AbstractCryptography.constructs_singleton_iff.mpr h)

/-- **Footnote 6's closure, fired at the carrier on two concrete
constructions.**  Two interface-indexed attachments chained through `M`
construct `{N}` from `{L}` within the admitted set, and the composite label
`attachAt j F * attachAt i E` never appears in the statement: the `Submonoid`
structure of `converterMonoidAt` is exactly what lets `Constructible` forget it
— "converters `α` and `β` from this particular set `Σ` can be composed to a new
converter … and this composition is closed".

The two interfaces are unconstrained: the constructions compose serially, one
after the other, and nothing here asks them to commute. -/
theorem constructible_trans_attachAt {i j : Set Uni.{u}}
    {E F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hE : System.InnerTotal E) (hEβ : System.AnswersWithinUniformBudget E)
    (hF : System.InnerTotal F) (hFβ : System.AnswersWithinUniformBudget F)
    {L M N : Phi.{u}} (h : attachAt i E L = M) (h' : attachAt j F M = N) :
    ({L} : Specification Phi.{u}) —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→
      ({N} : Specification Phi.{u}) :=
  Constructible.trans (constructible_attachAt hE hEβ h) (constructible_attachAt hF hFβ h')

/-- **MauRen16 §4.2 Lemma 5 as a `Γ`-restricted construction** — the
indifferentiability endpoint of `StarFullyDefined.lean` read on the possibility
side of §2.1.  A simulator `σ` admitted at the adversary interface `A` with
`πR ≈ᵋ Sσ` witnesses `R —[∈ Σ]→ (S∗)ᵋ`: the protocol is no longer exhibited,
but it is confined to the metric-facing `Σ`, which is the statement §2.1 asks
for and the one an impossibility result has to contradict. -/
theorem constructible_star_epsilonRelaxation_of_simulator_at {A : Set Uni.{u}}
    {π σ : ↥converterMonoidAt.{u}} (hσ : σ ∈ converterMonoidWithin A)
    {R S : Phi.{u}} {ε : ℝ≥0∞} (h : edist (π • R) (σ • S) ≤ ε) :
    ({R} : Specification Phi.{u}) —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→
      Relaxation.epsilonRelaxation ε
        ((Relaxation.star (converterMonoidWithin A) : Relaxation Phi.{u}) {S}) :=
  constructible_of_constructs_converterMonoidAt
    (constructs_star_epsilonRelaxation_of_simulator_at hσ h)

/-- **Row 6's context-insensitivity endpoint as a `Γ`-restricted
construction**: an admitted constructor in the left parallel component
survives an unchanged right context, with the extended protocol `π ∥ 1` still
admitted.  The hypotheses are `constructs_parF_left`'s and are not weakened —
the point is only that the conclusion is now a statement about the admitted
set rather than about one exhibited protocol. -/
theorem constructible_parF_left {i c : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hic : i ⊆ c) (hReq : System.RequestsWithin i E)
    {π : ↥converterMonoidAt.{u}} (hπ : (π : Function.End Phi.{u}) = attachAt i E)
    {R S : Specification Phi.{u}} (T : Specification Phi.{u})
    (hR : ∀ r ∈ R, RandomSystems.support r ⊆ c)
    (hT : ∀ t ∈ T, Disjoint (RandomSystems.support t) c)
    (h : R —[π]→ S) :
    R ∥ T —[∈ (converterMonoidAt.{u} : Set (Function.End Phi.{u}))]→ S ∥ T :=
  constructible_of_constructs_converterMonoidAt (constructs_parF_left hic hReq hπ T hR hT h)

/-! #### The second reading: `Γ` = the honest class, `Σ` = the class `∗` relaxes by -/

/-- **The generic entry at the restricted class.**  A construction whose
constructor is admitted at the honest interface `B` is a construction within
`Γ := converterMonoidWithin B`.  This is the reading §3.5's closing paragraph
asks for, and the one under which the two laws below have content. -/
theorem constructible_of_constructs_converterMonoidWithin {B : Set Uni.{u}}
    {π : ↥converterMonoidAt.{u}} (hπ : π ∈ converterMonoidWithin B)
    {𝓡 𝓢 : Specification Phi.{u}} (h : Constructs π 𝓡 𝓢) :
    𝓡 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→ 𝓢 :=
  Constructs.constructible hπ h

/-- **MauRen16 §4.1 Lemma 3 on the possibility side**: `𝓡 —[∈ Γ]→ 𝓢 ⟹ 𝓡∗ —[∈ Γ]→
𝓢∗`, with the constructor confined to the honest class at `B` and the `∗`
relaxing by the class at the disjoint adversary interface `A`.

This is where the two-class separation earns its keep: `Constructible.star`
asks that *every* admitted constructor commute with *every* converter the
relaxation may attach, and on this carrier that is
`commute_converterMonoidWithin` — i.e. `attachAt_comm` lifted along the two
closures.  No closure of `Γ` is spent; the same constructor witnesses both
statements. -/
theorem constructible_star_converterMonoidWithin {A B : Set Uni.{u}} (hAB : Disjoint B A)
    {𝓡 𝓢 : Specification Phi.{u}}
    (h : 𝓡 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→ 𝓢) :
    (Relaxation.star (converterMonoidWithin A) : Relaxation Phi.{u}) 𝓡
      —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→
      (Relaxation.star (converterMonoidWithin A) : Relaxation Phi.{u}) 𝓢 :=
  Constructible.star (fun _ hπ _ hβ => commute_converterMonoidWithin hAB hπ hβ) h

/-- **JM20 Corollary 1.1 / MauRen16 Lemma 1∘2 on the possibility side**: the
error budgets add along a chain whose constructors are only known to be
admitted at `B`.  The composite label is forgotten, so `Γ` has to hold it —
footnote 6 again — and the `ε`-balls belong to the ambient class, which is the
`IsNonexpandingSMul ↥converterMonoidAt Phi` instance of
`MetricFullyDefined.lean`.  The two classes visibly do different jobs, which is
the whole reason `Γ` is a second parameter. -/
theorem constructible_epsilonRelaxation_trans_converterMonoidWithin {B : Set Uni.{u}}
    {𝓡 𝓢 𝓣 : Specification Phi.{u}} {ε ε' : ℝ≥0∞}
    (h : 𝓡 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→
      Relaxation.epsilonRelaxation ε 𝓢)
    (h' : 𝓢 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→
      Relaxation.epsilonRelaxation ε' 𝓣) :
    𝓡 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→
      Relaxation.epsilonRelaxation (ε + ε') 𝓣 :=
  Constructible.epsilonRelaxation_trans h h'

/-- **§3.5's "a larger admitted set proves more constructions", at the
carrier**: a construction carried out by honest converters confined to `B` is a
fortiori one carried out within the class at any larger interface.  The
transfer is `converterMonoidWithin_mono`; nothing is asked of either class. -/
theorem constructible_mono_converterMonoidWithin {B B' : Set Uni.{u}} (hB : B ⊆ B')
    {𝓡 𝓢 : Specification Phi.{u}}
    (h : 𝓡 —[∈ (converterMonoidWithin B : Set ↥converterMonoidAt.{u})]→ 𝓢) :
    𝓡 —[∈ (converterMonoidWithin B' : Set ↥converterMonoidAt.{u})]→ 𝓢 :=
  Constructible.mono_constructors (converterMonoidWithin_mono hB) h

end ConstructorSet

end Consumers

end

end RandomSystems

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.StarFullyDefined
import RandomSystems.System.FilterPhi

/-!
# The converter class: a converter is what satisfies the axioms, not what a
generator list happens to contain

CR18's objects are defined **by** the property that makes the theorem true.
Ours were built from primitives, so those properties became proof obligations:
a new converter forced a widening of `converterMonoidAt`'s generator list, every
application needed a membership bridge, and CR18 equation (6.1) — one sentence
in the paper — needed a bespoke induction because nothing in the tree could say
"the composite only consults the resource where it asks".

This module inverts that.  `IsConverterAt i K π` is the class of converters at
interface `i` with request budget `K`; the interface and the budget are
**data**, so composition *computes* them.  Everything the tree proves about
converters is then proved **once over the class**, and a construction enters by
discharging the axioms once, at its constructor — never per application.

## The four axioms

* **A1 `ActsWithin i`** — interface discipline.  A converter at `i` leaves a
  converter at a disjoint interface alone: MauRen16 §3.3's `(αR)β = α(Rβ)`.  A
  black-box map has no requests, so `System.RequestsWithin` cannot be *its*
  clause; it is the clause on the partner, and the axiom is the equation
  `RequestsWithin` exists to buy.
* **A2 `Absorbs`** — absorption.  Every outer interaction is a fixed
  post-processing of an inner one, uniformly in the resource.  This is
  `System.exists_absorb_*`'s statement verbatim, at `X = Y = Uni`, so every
  landed receipt is a field value.
* **A3 `LocalWithin K`** — locality, the one genuinely new axiom: the composite
  depends on the resource only where it consults it, and the reach is the
  budget.  See the discussion below for why the agreement is length-indexed.
* **A4 `RequestsAtMost K`** — the budget, read as CR18 Definition 3.10's query
  limit: below `K` requests per outer query the filter `[r]` is invisible.

## Why A3's agreement is length-indexed

The naive statement — "two resources that agree at the queries the converter
puts to them give equal composites" — is unusable as a *hypothesis*, because
the queries the converter puts depend on the resource: the composite consults
`R` at `keptPrefix R xs ++ [q]`, and the deletion pass itself reads `R`.  So
the agreement region cannot mention the converter's own trace.  What is both
sound and usable is agreement on a region determined by the **outer** history
alone, and A4's budget is exactly what makes that region finite: after an outer
history `l` the composite can have built a resource history no longer than
`K * l.length`.  A3 therefore reads: *resources agreeing on every history of
length at most `K * l.length` give composites agreeing at `l`.*

The agreement is on `S.1` — the raw partial function — rather than on
`System.answer`.  The two forms are interchangeable up to one step
(`answer_congr_of_eq_below` below is the bridge the attachment instance uses),
and the `S.1` form is the one whose *hypothesis* is directly available at the
consumer: `filterQueries r R` and `R` agree on `S.1` below `r` by unfolding.

## What is proved once over the class

* nonexpansion (from A2), hence membership in `nonexpandingConverters` and
  every `ε`-transport that quantifies over it;
* commutation at disjoint interfaces (from A1);
* filter absorption (A4 from A3): `π` cannot tell `R` from `[r]R` while its
  reach stays inside `r`;
* the **pullback restriction** — the outer domain filter that tracks the
  induced request count.  It is adequate *by construction*, which is what turns
  CR18 equation (6.1) into an unfolding (`filterPhi_mul_filterQueries`).

## Presentation choices, disclosed

* A converter is a **deterministic** transformation of systems, lifted to `Φ`
  by the pushforward.  This is forced by A2, whose landed shape quantifies over
  deterministic systems, and it is CR18 Definition 3.17's own layering: a
  probabilistic converter is a *law over* deterministic ones.  The mixture
  layer therefore sits above this class, not inside it.
* The class is named `converterClass` rather than `Sigma`: `Sigma` is Lean
  core's dependent pair and shadowing it inside `RandomSystems` is a trap.
  `↥converterClass` is the subtype the specification asks for, and it carries
  `Monoid`, `MulAction Φ` and `IsNonexpandingSMul` by the ambient `Submonoid`
  instances.
* The budget `K` counts resource queries **per outer query**, pass-through
  included.  So the identity is `(∅, 1)` and stacking *multiplies*:
  `K * K'`.  (Counting only the *extra* queries would make the identity `0` at
  the cost of a law that is neither additive nor multiplicative.)
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u

/-! ## The carrier of the class -/

/-- A deterministic converter is a transformation of deterministic systems at
the universal alphabet.  CR18 Definition 3.8's converter *acts*; this is the
action, with the program abstracted away. -/
abbrev SystemMap : Type (u + 1) :=
  DDS Uni.{u} Uni.{u} → DDS Uni.{u} Uni.{u}

/-! ## A1 — interface discipline -/

/-- **A1: `g` acts only at `i`.**  Whatever is attached at an interface
disjoint from `i` passes through `g` untouched — MauRen16 §3.3's
`(αR)β = α(Rβ)`, which is the equation `System.RequestsWithin` exists to buy.

`RequestsWithin` itself cannot be the axiom: a map has no requests to confine.
It appears here as the clause on the *partner*, exactly as the landed
`attachEngineFully_comm` consumes it. -/
def ActsWithin (i : Set Uni.{u}) (g : SystemMap.{u}) : Prop :=
  ∀ (j : Set Uni.{u}), Disjoint i j →
    ∀ F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}), RequestsWithin j F →
      ∀ R : DDS Uni.{u} Uni.{u},
        g (attachEngineFully j F R) = attachEngineFully j F (g R)

/-- A1 is monotone in the interface: a converter at `i` is a converter at any
larger interface, because there is less left to commute with. -/
theorem ActsWithin.mono {i i' : Set Uni.{u}} (h : i ⊆ i') {g : SystemMap.{u}}
    (hg : ActsWithin i g) : ActsWithin i' g :=
  fun j hj F hF R => hg j (Set.disjoint_of_subset_left h hj) F hF R

/-- A1 holds of the identity at the empty interface: it commutes with
everything. -/
theorem actsWithin_id : ActsWithin (∅ : Set Uni.{u}) (id : SystemMap.{u}) :=
  fun _ _ _ _ _ => rfl

/-- **A1 composes, and the interfaces union.**  This is the computing form the
combinator layer needs: a composite acts at the union of what its parts act
at. -/
theorem ActsWithin.comp {i i' : Set Uni.{u}} {g h : SystemMap.{u}}
    (hg : ActsWithin i g) (hh : ActsWithin i' h) :
    ActsWithin (i ∪ i') (g ∘ h) := by
  intro j hj F hF R
  have hij : Disjoint i j := hj.mono_left Set.subset_union_left
  have hij' : Disjoint i' j := hj.mono_left Set.subset_union_right
  show g (h (attachEngineFully j F R)) = attachEngineFully j F (g (h R))
  rw [hh j hij' F hF R, hg j hij F hF (h R)]

/-! ## A2 — absorption -/

/-- **A2: the environment absorbs `g`.**  Every interaction with the converted
system, at every environment and length, is a *fixed* post-processing of an
interaction with the bare system — the choice of inner environment, length and
post-processing depending on the outer pair but **not** on the system.

This is `System.exists_absorb_*`'s statement at `X = Y = Uni`, unchanged: every
landed receipt is a field value. -/
def Absorbs (g : SystemMap.{u}) : Prop :=
  ∀ (e : DDE.Total Uni.{u} Uni.{u}) (n : ℕ),
    ∃ (e' : DDE.Total Uni.{u} Uni.{u}) (m : ℕ)
      (p : List (Uni.{u} × Option Uni.{u}) → List (Uni.{u} × Option Uni.{u})),
      ∀ s : DDS Uni.{u} Uni.{u},
        DDE.Total.transcript (g s) e n = p (DDE.Total.transcript s e' m)

/-- The identity is absorbed: the environment runs itself. -/
theorem absorbs_id : Absorbs (id : SystemMap.{u}) :=
  fun e n => ⟨e, n, id, fun _ => rfl⟩

/-- **A2 composes**: the post-processings compose, and so do the environments.
Nothing is chosen twice — the outer witness is applied at the inner converted
system, and the inner witness at the result. -/
theorem Absorbs.comp {g h : SystemMap.{u}} (hg : Absorbs g) (hh : Absorbs h) :
    Absorbs (g ∘ h) := by
  intro e n
  obtain ⟨e₁, m₁, p₁, hp₁⟩ := hg e n
  obtain ⟨e₂, m₂, p₂, hp₂⟩ := hh e₁ m₁
  exact ⟨e₂, m₂, p₁ ∘ p₂, fun s => by
    show DDE.Total.transcript (g (h s)) e n = p₁ (p₂ _)
    rw [hp₁ (h s), hp₂ s]⟩

/-! ## A3 — locality -/

/-- **A3: `g R` depends on `R` only where `g` consults it.**  After an outer
history `l` the converter can have built a resource history no longer than
`K * l.length`, so two resources that agree on every history of that length
give composites that agree at `l`.

The agreement region is determined by the *outer* history alone.  That is
forced: the region the composite actually reads is
`keptPrefix R xs ++ [q]`, which depends on `R`, so an agreement indexed by the
consulted points is not a usable hypothesis. -/
def LocalWithin (K : ℕ) (g : SystemMap.{u}) : Prop :=
  ∀ (R R' : DDS Uni.{u} Uni.{u}) (l : List Uni.{u}),
    (∀ zs : List Uni.{u}, zs.length ≤ K * l.length → R.1 zs = R'.1 zs) →
      (g R).1 l = (g R').1 l

/-- A3 is monotone in the budget: a wider reach is a weaker hypothesis to
supply and so a weaker statement. -/
theorem LocalWithin.mono {K K' : ℕ} (hKK : K ≤ K') {g : SystemMap.{u}}
    (hg : LocalWithin K g) : LocalWithin K' g :=
  fun R R' l hagree => hg R R' l fun zs hzs =>
    hagree zs (hzs.trans (Nat.mul_le_mul_right _ hKK))

/-- The identity consults the resource exactly at the history it is asked
about: budget `1`. -/
theorem localWithin_id : LocalWithin 1 (id : SystemMap.{u}) :=
  fun _ _ l hagree => hagree l (by simp)

/-- **A3 composes, and the budgets multiply.**  An outer query costs `g` at
most `K` queries to `h`, each of which costs `h` at most `K'` queries to the
resource. -/
theorem LocalWithin.comp {K K' : ℕ} {g h : SystemMap.{u}}
    (hg : LocalWithin K g) (hh : LocalWithin K' h) :
    LocalWithin (K * K') (g ∘ h) := by
  intro R R' l hagree
  refine hg (h R) (h R') l fun zs hzs => hh R R' zs fun ws hws => hagree ws ?_
  calc ws.length ≤ K' * zs.length := hws
    _ ≤ K' * (K * l.length) := Nat.mul_le_mul_left _ hzs
    _ = K * K' * l.length := by ring

/-! ## A4 — the request budget, as CR18 Definition 3.10's query limit -/

/-- **A4: `g` puts at most `K` queries to the resource per outer query.**  On a
black-box map the count is not observable directly; what is observable is its
consequence, and it is the one CR18 uses: while the reach stays inside `r`, the
filter `[r]` is invisible to the converter (CR18 Definition 3.10, printed
p. 62). -/
def RequestsAtMost (K : ℕ) (g : SystemMap.{u}) : Prop :=
  ∀ (R : DDS Uni.{u} Uni.{u}) (r : ℕ) (l : List Uni.{u}), K * l.length ≤ r →
    (g (filterQueries r R)).1 l = (g R).1 l

/-- **A4 follows from A3 on this carrier**: `[r]R` and `R` agree at every
history of length at most `r` by unfolding, and A3's reach is inside `r`.  The
axiom is kept as a field because it is what consumers cite, but no instance
ever proves it — the smart constructor `IsConverterMapAt.of_local` supplies
it. -/
theorem LocalWithin.requestsAtMost {K : ℕ} {g : SystemMap.{u}}
    (hg : LocalWithin K g) : RequestsAtMost K g := by
  intro R r l hle
  refine hg _ _ l fun zs hzs => ?_
  have hlen : zs.length ≤ r := hzs.trans hle
  exact Part.ext' ⟨fun h => h.1, fun h => ⟨h, hlen⟩⟩ fun _ _ => rfl

/-! ## The class -/

/-- **The converter class at the deterministic level**: interface `i`, request
budget `K`, and the four axioms.  Both indices are data, so the composition
laws compute them. -/
structure IsConverterMapAt (i : Set Uni.{u}) (K : ℕ) (g : SystemMap.{u}) : Prop where
  /-- **A1**: `g` acts only at `i`. -/
  interface : ActsWithin i g
  /-- **A2**: the environment absorbs `g`. -/
  absorbs : Absorbs g
  /-- **A3**: `g R` depends on `R` only where `g` consults it. -/
  locality : LocalWithin K g
  /-- **A4**: `g` asks at most `K` questions per outer query. -/
  budget : RequestsAtMost K g

/-- **The smart constructor**: A4 is derived, so an instance discharges three
axioms, never four. -/
theorem IsConverterMapAt.of_local {i : Set Uni.{u}} {K : ℕ} {g : SystemMap.{u}}
    (h1 : ActsWithin i g) (h2 : Absorbs g) (h3 : LocalWithin K g) :
    IsConverterMapAt i K g :=
  ⟨h1, h2, h3, h3.requestsAtMost⟩

theorem IsConverterMapAt.mono {i i' : Set Uni.{u}} {K K' : ℕ} {g : SystemMap.{u}}
    (h : IsConverterMapAt i K g) (hi : i ⊆ i') (hK : K ≤ K') :
    IsConverterMapAt i' K' g :=
  .of_local (h.interface.mono hi) h.absorbs (h.locality.mono hK)

/-- **The identity is a converter**, at the empty interface and budget `1`. -/
theorem isConverterMapAt_id :
    IsConverterMapAt (∅ : Set Uni.{u}) 1 (id : SystemMap.{u}) :=
  .of_local actsWithin_id absorbs_id localWithin_id

/-- **Converters compose, and the class computes**: interfaces union, budgets
multiply.  This is the law the combinator layer needs — no composite ever
re-proves an axiom. -/
theorem IsConverterMapAt.comp {i i' : Set Uni.{u}} {K K' : ℕ} {g h : SystemMap.{u}}
    (hg : IsConverterMapAt i K g) (hh : IsConverterMapAt i' K' h) :
    IsConverterMapAt (i ∪ i') (K * K') (g ∘ h) :=
  .of_local (hg.interface.comp hh.interface) (hg.absorbs.comp hh.absorbs)
    (hg.locality.comp hh.locality)

end

end System

end RandomSystems

namespace RandomSystems

noncomputable section

open Probability (Distribution)

open scoped ENNReal

universe u

/-! ## The class at Φ

A converter acts on laws by the pushforward of its deterministic action — CR18
Definition 3.17's layering, where a *probabilistic* converter is a law over
deterministic ones and its action is the mixture. -/

/-- **The converter class at Φ**: `π` is a converter at interface `i` with
request budget `K` when it is the pushforward of a deterministic converter map
satisfying A1–A4 at `(i, K)`.

Both indices are data.  `IsConverterAt` is what an application should *have*;
it is never what an application should *prove* — the constructors below prove
it once each, and composition computes the indices. -/
def IsConverterAt (i : Set Uni.{u}) (K : ℕ) (π : Function.End Phi.{u}) : Prop :=
  ∃ g : System.SystemMap.{u}, System.IsConverterMapAt i K g ∧
    π = fun L => Distribution.fTransform g L

theorem IsConverterAt.mono {i i' : Set Uni.{u}} {K K' : ℕ} {π : Function.End Phi.{u}}
    (h : IsConverterAt i K π) (hi : i ⊆ i') (hK : K ≤ K') : IsConverterAt i' K' π :=
  let ⟨g, hg, hπ⟩ := h; ⟨g, hg.mono hi hK, hπ⟩

/-- **The identity is a converter**, at the empty interface and budget `1`. -/
theorem isConverterAt_one :
    IsConverterAt (∅ : Set Uni.{u}) 1 (1 : Function.End Phi.{u}) :=
  ⟨id, System.isConverterMapAt_id, by
    funext L
    exact (Finsupp.mapDomain_id (v := L)).symm⟩

/-- **Converters compose and the class computes**: interfaces union, budgets
multiply.  Nothing is re-proved at a composite. -/
theorem IsConverterAt.mul {i i' : Set Uni.{u}} {K K' : ℕ} {π ρ : Function.End Phi.{u}}
    (hπ : IsConverterAt i K π) (hρ : IsConverterAt i' K' ρ) :
    IsConverterAt (i ∪ i') (K * K') (π * ρ) := by
  obtain ⟨g, hg, rfl⟩ := hπ
  obtain ⟨h, hh, rfl⟩ := hρ
  refine ⟨g ∘ h, hg.comp hh, ?_⟩
  funext L
  exact Distribution.fTransform_fTransform g h L

/-- **The class as a submonoid of `Function.End Φ`** — the object MauRen16 §3.3
calls `Σ`, now *specified* rather than generated.  `↥converterClass` is the
subtype, and it carries `Monoid` and `MulAction Φ` by the ambient instances.

Named `converterClass` and not `Sigma`: `Sigma` is Lean core's dependent pair,
and shadowing it inside this namespace is a trap. -/
def converterClass : Submonoid (Function.End Phi.{u}) where
  carrier := {π | ∃ (i : Set Uni.{u}) (K : ℕ), IsConverterAt i K π}
  one_mem' := ⟨∅, 1, isConverterAt_one⟩
  mul_mem' := fun ⟨i, K, hπ⟩ ⟨i', K', hρ⟩ => ⟨i ∪ i', K * K', hπ.mul hρ⟩

@[simp] theorem mem_converterClass {π : Function.End Phi.{u}} :
    π ∈ converterClass.{u} ↔ ∃ (i : Set Uni.{u}) (K : ℕ), IsConverterAt i K π :=
  Iff.rfl

theorem IsConverterAt.mem_converterClass {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π) : π ∈ converterClass.{u} :=
  ⟨i, K, h⟩

/-! ## Theorem 1 — nonexpansion, from A2 alone

MauRen16 Definition 2 is a consequence of the class, not of a generator
induction.  This is the dependency inversion the design intends: the generated
monoid existed so that nonexpansion could be proved generator by generator;
here it is derived from the axiom the sources assume. -/

/-- **A converter never helps a distinguisher** — from A2, in one step.  The
whole of `PDS.advFullyDefined_fTransform_le`'s hypothesis *is* A2. -/
theorem IsConverterAt.mem_nonexpandingConverters {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π) :
    π ∈ nonexpandingConverters.{u} := by
  obtain ⟨g, hg, rfl⟩ := h
  exact fun RL SL => PDS.advFullyDefined_fTransform_le g RL SL hg.absorbs

/-- **The class is nonexpanding**, wholesale.  Every `ε`-transport stated over
`nonexpandingConverters` therefore holds over the class with nothing to
re-prove. -/
theorem converterClass_le_nonexpandingConverters :
    converterClass.{u} ≤ nonexpandingConverters.{u} :=
  fun _ ⟨_, _, h⟩ => h.mem_nonexpandingConverters

/-- The class acts non-expandingly — the typeclass the abstract `ε`-relaxation
calculus consumes (`Relaxation.epsilonRelaxation_compatible`,
`Constructs.epsilonRelaxation_trans`).  Derived, not chosen. -/
instance : AbstractCryptography.IsNonexpandingSMul (converterClass.{u}) Phi.{u} :=
  ⟨fun σ => nonexpandingConverters_le_nonexpandingEnd
    (converterClass_le_nonexpandingConverters σ.2)⟩

/-- **MauRen16 Definition 2 over the class**: applying a converter to both
sides never increases the distance. -/
theorem edist_apply_le_of_isConverterAt {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π) (L M : Phi.{u}) :
    edist (π L) (π M) ≤ edist L M :=
  edist_apply_le_of_mem_nonexpandingConverters h.mem_nonexpandingConverters L M

/-- **JM20 Corollary 1.1 item 1 over the class**: errors add along a chain. -/
theorem constructs_epsilonRelaxation_trans_class
    {σ τ : converterClass.{u}} {L M N : Phi.{u}} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : edist (σ • L) M ≤ ε₁) (h₂ : edist (τ • M) N ≤ ε₂) :
    edist ((τ * σ) • L) N ≤ ε₁ + ε₂ :=
  AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mp
    (AbstractCryptography.Constructs.epsilonRelaxation_trans
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₁)
      (AbstractCryptography.constructs_singleton_epsilonRelaxation_iff.mpr h₂))

/-! ## Theorem 2 — commutation at disjoint interfaces, from A1

`attachAt_comm` generalized: one side is now any member of the class, not
another attachment. -/

/-- **MauRen16 §3.3's `(αR)β = α(Rβ)` over the class**: a converter at `i`
commutes with an attachment at a disjoint interface.  This is A1 pushed forward
along the distribution — the whole content is the axiom. -/
theorem IsConverterAt.commute_attachAt {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π)
    {j : Set Uni.{u}} (hij : Disjoint i j)
    {F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hF : System.RequestsWithin j F) :
    π * attachAt j F = attachAt j F * π := by
  obtain ⟨g, hg, rfl⟩ := h
  funext L
  show Distribution.fTransform g
      (Distribution.fTransform (System.attachEngineFully j F) L) =
    Distribution.fTransform (System.attachEngineFully j F)
      (Distribution.fTransform g L)
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform]
  exact congrFun (congrArg Distribution.fTransform
    (funext fun R => hg.interface j hij F hF R)) L

/-- The `ActCommute` receipt over the class — the form the abstract grouping
layer consumes. -/
theorem IsConverterAt.actCommute_attachAt {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π)
    {j : Set Uni.{u}} (hij : Disjoint i j)
    {F : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hF : System.RequestsWithin j F) :
    AbstractCryptography.ActCommute Phi.{u} π (attachAt j F) := fun L => by
  show (π * attachAt j F) L = (attachAt j F * π) L
  rw [h.commute_attachAt hij hF]

/-! ## Theorem 3 — filter absorption, from A3 and A4

CR18 Definition 3.10's `[r]` is invisible to a converter whose reach stays
inside `r`.  Stated at Φ, and once. -/

/-- **The query limit is invisible below the reach**, at one outer history.
A4 pushed to Φ is not available pointwise (a law is not a history), so the
statement that travels is the system-level one; this is it, and it is the
ingredient the outer restriction consumes. -/
theorem System.filterDom_comp_filterQueries {K : ℕ} {g : System.SystemMap.{u}}
    (hg : System.RequestsAtMost K g) (P : List Uni.{u} → Prop) (hP : PrefixClosed P)
    (r : ℕ) (hadm : ∀ l, P l → K * l.length ≤ r) (S : System.DDS Uni.{u} Uni.{u}) :
    System.filterDom P hP (g (System.filterQueries r S)) =
      System.filterDom P hP (g S) := by
  apply Subtype.ext
  funext l
  have hmem : ∀ (T : System.DDS Uni.{u} Uni.{u}) (v : Uni.{u}),
      v ∈ (System.filterDom P hP T).1 l ↔ (v ∈ T.1 l ∧ P l) := by
    intro T v
    constructor
    · rintro ⟨⟨hd, hp⟩, hv⟩; exact ⟨⟨hd, hv⟩, hp⟩
    · rintro ⟨⟨hd, hv⟩, hp⟩; exact ⟨⟨hd, hp⟩, hv⟩
  refine Part.ext fun v => ?_
  by_cases hPl : P l
  · rw [hmem, hmem, hg S r l (hadm l hPl)]
  · rw [hmem, hmem]
    simp [hPl]

/-- **CR18 equation (6.1), over the class** (printed p. 126): "the filter `[r]`
is irrelevant because the restriction implied by `θ_r` guarantees that at most
`r` queries are made".

Nothing about any particular converter enters: the hypothesis is that the outer
restriction admits only histories whose induced request count — `K` per query,
the converter's own budget datum — stays inside `r`.  With the *pullback*
restriction of the next declaration that hypothesis is `le_rfl`, which is the
sense in which equation (6.1) becomes an unfolding rather than a theorem. -/
theorem IsConverterAt.filterPhi_mul_filterQueries {i : Set Uni.{u}} {K : ℕ}
    {π : Function.End Phi.{u}} (h : IsConverterAt i K π)
    (P : List Uni.{u} → Prop) (hP : PrefixClosed P) (r : ℕ)
    (hadm : ∀ l, P l → K * l.length ≤ r) :
    filterPhi P hP * π * filterQueries.{u} r = filterPhi P hP * π := by
  obtain ⟨g, hg, rfl⟩ := h
  funext L
  show Distribution.fTransform (System.filterDom P hP)
      (Distribution.fTransform g
        (Distribution.fTransform (System.filterQueries r) L)) =
    Distribution.fTransform (System.filterDom P hP)
      (Distribution.fTransform g L)
  rw [Distribution.fTransform_fTransform, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  exact congrFun (congrArg Distribution.fTransform (funext fun S =>
    System.filterDom_comp_filterQueries hg.budget P hP r hadm S)) L

/-! ## Theorem 4 — the pullback restriction

CR18's `θ_r` is *defined* here rather than characterized: the outer restriction
that tracks a resource-side bound of `r` through a converter of budget `K` is
the domain filter at "the induced count is within `r`".  Adequacy is
`le_rfl`. -/

/-- **The pullback of a resource-side query bound along a converter**: the outer
histories whose induced request count stays inside `r`.  For a converter of
budget `K` the induced count after `l` is at most `K * l.length`, so this is
that predicate and nothing else. -/
def pullbackLimit (K r : ℕ) : List Uni.{u} → Prop :=
  fun l => K * l.length ≤ r

theorem prefixClosed_pullbackLimit (K r : ℕ) :
    PrefixClosed (pullbackLimit.{u} K r) :=
  fun _ _ hpre hle =>
    le_trans (Nat.mul_le_mul_left _ hpre.length_le) hle

/-- **CR18's `θ_r`, at a converter of budget `K`** (printed p. 126): the outer
domain filter that tracks the resource-side bound `r`. -/
def pullbackRestriction (K r : ℕ) : Function.End Phi.{u} :=
  filterPhi (pullbackLimit.{u} K r) (prefixClosed_pullbackLimit K r)

/-- **Adequacy by construction**: under the pullback restriction the inner
query limit is redundant.  CR18 equation (6.1) with no side condition left to
check — the admission hypothesis of the previous theorem is `le_rfl` at this
filter, which is precisely what "the restriction implied by `θ_r` guarantees
that at most `r` queries are made" means. -/
theorem IsConverterAt.pullbackRestriction_mul_filterQueries {i : Set Uni.{u}}
    {K : ℕ} {π : Function.End Phi.{u}} (h : IsConverterAt i K π) (r : ℕ) :
    pullbackRestriction.{u} K r * π * filterQueries.{u} r =
      pullbackRestriction.{u} K r * π :=
  h.filterPhi_mul_filterQueries _ _ r fun _ hl => hl

end

end RandomSystems

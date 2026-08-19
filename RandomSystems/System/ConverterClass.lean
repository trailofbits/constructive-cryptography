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

namespace RandomSystems

namespace System

noncomputable section

open Classical
open Converter (InLabel)
open Converter.DDC (CIn ofEngine unlabel resolve)

universe u v w

/-! ## Reading the class's `S.1` agreement as the tree's `answer` agreement

A3 quantifies over agreement of the raw partial function below a length; the
landed interpreter lemmas quantify over agreement of `System.answer`.  The two
are one step apart, and the step is the deletion pass: a kept prefix is no
longer than what it scanned, so `S.1`-agreement below `N` gives `answer`
agreement one query short of `N`. -/

section Bridge

variable {X : Type v} {Y : Type w}


theorem answer_eq_toOption (S : DDS X Y) (l : List X) (x : X) :
    answer S l x = (S.1 (keptPrefix S l ++ [x])).toOption := by
  rw [answer_eq]; rfl

theorem keptPrefix_congr_of_apply_eq {R R' : DDS X Y} {N : ℕ}
    (h : ∀ zs : List X, zs.length ≤ N → R.1 zs = R'.1 zs) :
    ∀ l : List X, l.length ≤ N → keptPrefix R l = keptPrefix R' l := by
  intro l
  induction l using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l x ih =>
      intro hlen
      simp only [List.length_append, List.length_singleton] at hlen
      rw [keptPrefix_append_singleton, keptPrefix_append_singleton, ih (by omega)]
      have hdom : keptPrefix R' l ++ [x] ∈ dom R ↔ keptPrefix R' l ++ [x] ∈ dom R' := by
        have hk : (keptPrefix R' l ++ [x]).length ≤ N := by
          have := keptPrefix_length_le R' l
          simp only [List.length_append, List.length_singleton]; omega
        show (R.1 _).Dom ↔ (R'.1 _).Dom
        rw [h _ hk]
      by_cases hd : keptPrefix R' l ++ [x] ∈ dom R'
      · rw [if_pos (hdom.mpr hd), if_pos hd]
      · rw [if_neg (fun hc => hd (hdom.mp hc)), if_neg hd]

theorem answer_congr_of_apply_eq {R R' : DDS X Y} {N : ℕ}
    (h : ∀ zs : List X, zs.length ≤ N → R.1 zs = R'.1 zs) (l : List X) (x : X)
    (hl : l.length + 1 ≤ N) : answer R l x = answer R' l x := by
  have hk := keptPrefix_congr_of_apply_eq h l (by omega)
  rw [answer_eq_toOption, answer_eq_toOption, hk,
    h (keptPrefix R' l ++ [x]) (by
      have := keptPrefix_length_le R' l
      simp only [List.length_append, List.length_singleton]; omega)]

variable {i : Set Uni.{u}} {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
  {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ} {R R' : DDS Uni.{u} Uni.{u}}

theorem attachEngineFullyDrive_congr_of_apply_eq
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) (hK1 : 1 ≤ K) :
    ∀ (rest done : List Uni.{u}) (st : List (CIn Uni.{u} Uni.{u}) × List Uni.{u}),
      (∀ zs : List Uni.{u}, zs.length ≤ K * (done ++ rest).length → R.1 zs = R'.1 zs) →
      st.2.length ≤ K * done.length →
        attachEngineFullyDrive i E R st rest = attachEngineFullyDrive i E R' st rest := by
  intro rest
  induction rest with
  | nil => intro done st _ _; rfl
  | cons q rest ih =>
      intro done st hagree hlen
      have hcons : done ++ q :: rest = (done ++ [q]) ++ rest := by simp
      have hstep : K * (done ++ [q]).length = K * done.length + K := by
        simp only [List.length_append, List.length_singleton]; ring
      have hmono : K * (done ++ [q]).length ≤ K * (done ++ q :: rest).length := by
        rw [hcons]
        exact Nat.mul_le_mul_left _ (by simp)
      have hbelow : ∀ zs : List Uni.{u}, zs.length ≤ K * (done ++ [q]).length →
          R.1 zs = R'.1 zs := fun zs hzs => hagree zs (hzs.trans hmono)
      have hrd : attachEngineFullyRound i E R st q = attachEngineFullyRound i E R' st q := by
        by_cases hq : q ∈ i
        · rw [attachEngineFullyRound_mem E R st hq, attachEngineFullyRound_mem E R' st hq]
          refine resolve_congr_of_answer_eq hβ
            (β ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)) _ st.2 le_rfl ?_
          intro zs x hzs
          have hb := hK ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)
          exact answer_congr_of_apply_eq hbelow zs x (by rw [hstep]; omega)
        · rw [attachEngineFullyRound_not_mem E R st hq,
            attachEngineFullyRound_not_mem E R' st hq,
            keptPrefix_congr_of_apply_eq hbelow st.2 (by rw [hstep]; omega),
            hbelow (keptPrefix R' st.2 ++ [q]) (by
              have hkl := keptPrefix_length_le R' st.2
              have hmul : K * (done.length + 1) = K * done.length + K := by ring
              simp only [List.length_append, List.length_singleton]
              omega)]
      show (attachEngineFullyRound i E R st q).bind _ = (attachEngineFullyRound i E R' st q).bind _
      rw [hrd]
      refine Part.ext fun z => ?_
      simp only [Part.mem_bind_iff]
      refine exists_congr fun a => and_congr_right fun ha => ?_
      obtain ⟨v, c₂, xs₂⟩ := a
      have hlen2 : xs₂.length ≤ K * (done ++ [q]).length := by
        by_cases hq : q ∈ i
        · rw [attachEngineFullyRound_mem E R' st hq] at ha
          have := length_le_of_mem_resolve hβ R' K _ st.2
            (hK ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)) ha
          have hb := hK ((st.1 ++ [Sum.inl (InLabel.outside, q)]).map unlabel)
          rw [hstep]; omega
        · rw [attachEngineFullyRound_not_mem E R' st hq, Part.mem_map_iff] at ha
          obtain ⟨y, -, hy⟩ := ha
          have hx2 : xs₂ = st.2 ++ [q] := by
            have := congrArg (fun r => r.2.2) hy
            simpa using this.symm
          rw [hx2, hstep]
          simp only [List.length_append, List.length_singleton]
          omega
      rw [ih (done ++ [q]) (c₂, xs₂) (by rw [← hcons]; exact hagree) hlen2]

theorem attachEngineFully_congr_of_apply_eq
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) (hK1 : 1 ≤ K)
    (l : List Uni.{u})
    (hagree : ∀ zs : List Uni.{u}, zs.length ≤ K * l.length → R.1 zs = R'.1 zs) :
    (attachEngineFully i E R).1 l = (attachEngineFully i E R').1 l := by
  simp only [attachEngineFully_toPFun, attachEngineFullyRaw]
  rw [attachEngineFullyDrive_congr_of_apply_eq hβ hK hK1 l [] ([], [])
    (by simpa using hagree) (by simp)]


end Bridge

/-! ## The empty interface is the identity

`attachEngineFully ∅ F` never consults the engine — every query is foreign — and
a foreign round is the resource's own step, so the composite *is* the resource.
This is the receipt that makes A1 free at the full interface: `Disjoint univ j`
forces `j = ∅`, and there is then nothing to commute with. -/


theorem mem_dom_of_reachedAt
    {F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})} {R : DDS Uni.{u} Uni.{u}}
    {us : List Uni.{u}} (hne : us ≠ [])
    {st : List (Converter.DDC.CIn Uni.{u} Uni.{u}) × List Uni.{u}}
    (h : ReachedAt (∅ : Set Uni.{u}) F R us st) : us ∈ dom (attachEngineFully ∅ F R) := by
  obtain ⟨vs, hvs⟩ := h
  have hlen : vs.length = us.length := attachEngineFullyDrive_length ([], []) us hvs
  have hvne : vs ≠ [] := by
    intro hnil
    exact hne (List.eq_nil_of_length_eq_zero (by rw [← hlen, hnil, List.length_nil]))
  refine Part.dom_iff_mem.mpr ⟨vs.getLast hvne, ?_⟩
  rw [attachEngineFully_toPFun, mem_attachEngineFullyRaw_iff]
  exact ⟨(vs, st), hvs, List.getLast?_eq_some_getLast hvne⟩

theorem attachEngineFully_empty_aux (F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}))
    (R : DDS Uni.{u} Uni.{u}) : ∀ us : List Uni.{u},
    ((us = [] ∨ us ∈ dom R) → ReachedAt (∅ : Set Uni.{u}) F R us ([], us)) ∧
      (attachEngineFully ∅ F R).1 us = R.1 us := by
  intro us
  induction us using List.reverseRecOn with
  | nil =>
      refine ⟨fun _ => reachedAt_nil _ F R, ?_⟩
      rw [Part.eq_none_iff'.mpr (empty_not_mem (attachEngineFully ∅ F R)),
        Part.eq_none_iff'.mpr (empty_not_mem R)]
  | append_singleton us q ih =>
      obtain ⟨ihr, iha⟩ := ih
      by_cases hus : us = [] ∨ us ∈ dom R
      · have hkept : keptPrefix R us = us :=
          keptPrefix_eq_self_of_mem_or_empty R hus.symm
        have hst := ihr hus
        refine ⟨fun hmem => ?_, ?_⟩
        · have hR : keptPrefix R us ++ [q] ∈ dom R := by
            rw [hkept]
            rcases hmem with h | h
            · exact absurd h (by simp)
            · exact h
          exact attachEngineFully_reached_concat_not_mem hst (by simp) hR
        · rw [attachEngineFully_transparent hst (by simp), hkept]
      · rw [not_or] at hus
        obtain ⟨hne, hnd⟩ := hus
        have hRnone : R.1 (us ++ [q]) = Part.none := by
          refine Part.eq_none_iff.mpr fun v hv => hnd ?_
          exact prefix_closed R ⟨[q], rfl⟩ hne (Part.dom_iff_mem.mpr ⟨v, hv⟩)
        have hnodom : us ∉ dom (attachEngineFully ∅ F R) := by
          intro hc
          refine hnd ?_
          show (R.1 us).Dom
          rw [← iha]
          exact hc
        refine ⟨fun hmem => ?_, ?_⟩
        · exfalso
          rcases hmem with h | h
          · exact absurd h (by simp)
          · exact hnd (prefix_closed R ⟨[q], rfl⟩ hne h)
        · rw [hRnone, attachEngineFully_concat_eq_none
            (fun hex => hnodom (mem_dom_of_reachedAt hne hex.choose_spec)) q]

theorem attachEngineFully_empty (F : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u}))
    (R : DDS Uni.{u} Uni.{u}) : attachEngineFully (∅ : Set Uni.{u}) F R = R :=
  Subtype.ext (funext fun us => (attachEngineFully_empty_aux F R us).2)

theorem actsWithin_univ (g : SystemMap.{u}) : ActsWithin (Set.univ : Set Uni.{u}) g := by
  intro j hj F _ R
  have hj0 : j = ∅ := Set.univ_disjoint.mp hj
  subst hj0
  rw [attachEngineFully_empty, attachEngineFully_empty]


/-! ## The interface-local locality of attachment

The landed `attachEngineFullyDrive_congr_of_answer_eq` is stated at
`i = Set.univ` and at a general cost function, with the docstring's own
observation that the interface-local statement "would need `cost` to pay for
foreign queries as well".  A3's uniform budget pays for them: a foreign round
is one query, and `K ≥ 1`.  So the interface-local statement is available, and
this is it. -/


end

end System

end RandomSystems

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u

/-! ## Introduction form (2): the interactive converter — a program with its
discipline

CR18 Definition 3.8's converter *is* a system at the converter alphabets: "given
what I have seen, my next move".  `attachEngineFully i E` is that program
applied, and the class membership below is the whole of what an application
needs — it never states an axiom of its own, only the two elementary conditions
on its own program (it always reacts, and its rounds are bounded) that
`ConverterEntry.lean`'s crossing already asks for. -/

/-- **The program constructor satisfies the axioms.**  `RequestsWithin` gives
A1 (through the landed commutation), the engine class gives A2 (through the
landed absorption), and the uniform bound gives A3 with reach `max K 1` — the
`max` reconciles the two genres exactly as `exists_absorb_attachEngineFully`'s
does, since a foreign query costs one resource query whatever the engine's
budget is. -/
theorem isConverterMapAt_attachEngineFully {i : Set Uni.{u}}
    {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hReq : RequestsWithin i E) (hIT : InnerTotal E)
    (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) :
    IsConverterMapAt i (max K 1) (attachEngineFully i E) :=
  .of_local
    (fun _ hij _ hF R => attachEngineFully_comm hij hReq hF R)
    (fun e n => exists_absorb_attachEngineFully hIT hβ hK e n)
    (fun _ _ l hagree =>
      attachEngineFully_congr_of_apply_eq hβ (fun l => (hK l).trans (le_max_left _ _))
        (le_max_right _ _) l hagree)

/-- **The program constructor with no interface claimed.**  A1 is free at the
full interface (`actsWithin_univ`), so an engine whose requests are not confined
still enters the class — it just cannot be commuted past anything. -/
theorem isConverterMapAt_attachEngineFully_univ {i : Set Uni.{u}}
    {E : DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hIT : InnerTotal E) (hβ : AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) :
    IsConverterMapAt (Set.univ : Set Uni.{u}) (max K 1) (attachEngineFully i E) :=
  .of_local (actsWithin_univ _)
    (fun e n => exists_absorb_attachEngineFully hIT hβ hK e n)
    (fun _ _ l hagree =>
      attachEngineFully_congr_of_apply_eq hβ (fun l => (hK l).trans (le_max_left _ _))
        (le_max_right _ _) l hagree)

/-! ## Introduction form (1), partial: the function-pair converters

A converter that neither keeps state across the resource nor asks twice is a
*function pair*: a pre-map on the outgoing query and a post-map on the incoming
answer, the pre-map allowed to decline.  The two landed members of that family
are the domain filter (a pre-map that declines on the history) and the
relabelling (a pre-map and a post-map that rename).  Both are proved here
directly; the general `funPair` combinator that subsumes them is the next
dispatch's, and nothing below depends on which of the two shapes it is written
in. -/

theorem mem_filterDom_iff {X : Type u} {Y : Type u} (P : List X → Prop)
    (hP : PrefixClosed P) (S : DDS X Y) (l : List X) (v : Y) :
    v ∈ (filterDom P hP S).1 l ↔ (v ∈ S.1 l ∧ P l) := by
  constructor
  · rintro ⟨⟨hd, hp⟩, hv⟩; exact ⟨⟨hd, hv⟩, hp⟩
  · rintro ⟨⟨hd, hv⟩, hp⟩; exact ⟨⟨hd, hp⟩, hv⟩

/-- **CR18 §3.4.3's domain filter is a converter** (unnumbered prose, printed
p. 62): a declining function pair.  Interface `Set.univ` — it inspects every
query — and budget `1`: it relays at most the query it was given. -/
theorem isConverterMapAt_filterDom (P : List Uni.{u} → Prop) (hP : PrefixClosed P) :
    IsConverterMapAt (Set.univ : Set Uni.{u}) 1 (filterDom P hP) :=
  .of_local (actsWithin_univ _) (fun e n => exists_absorb_filterDom P hP e n)
    (fun R R' l hagree => by
      have h := hagree l (by simp)
      refine Part.ext fun v => ?_
      rw [mem_filterDom_iff, mem_filterDom_iff, h])

/-- **Relabelling is a converter**: a total function pair.  Interface
`Set.univ`, budget `1` — one renamed query out per query in. -/
theorem isConverterMapAt_relabel (f g : Uni.{u} → Uni.{u}) :
    IsConverterMapAt (Set.univ : Set Uni.{u}) 1 (relabel f g) :=
  .of_local (actsWithin_univ _) (fun e n => exists_absorb_relabel f g e n)
    (fun R R' l hagree => by
      show (R.1 (l.map f)).map g = (R'.1 (l.map f)).map g
      rw [hagree (l.map f) (by simp)])

end

end System

/-! ## The instances at Φ, and the demotion of the generated monoid -/

noncomputable section

open Probability (Distribution)

universe u

/-- **The program constructor, at Φ.**  Everything an application has to supply
is a fact about its own program; no converter-theory obligation is left over. -/
theorem isConverterAt_attachAt {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    {β : List (Uni.{u} ⊕ Option Uni.{u}) → ℕ} {K : ℕ}
    (hReq : System.RequestsWithin i E) (hIT : System.InnerTotal E)
    (hβ : System.AnswersWithinBudget E β) (hK : ∀ l, β l ≤ K) :
    IsConverterAt i (max K 1) (attachAt i E) :=
  ⟨System.attachEngineFully i E,
    System.isConverterMapAt_attachEngineFully hReq hIT hβ hK, rfl⟩

/-- The same at CR18 Definition 3.8's packaged bound, and with no interface
claimed: `AnswersWithinUniformBudget` is the existential form, so the budget it
yields is existential too. -/
theorem exists_isConverterAt_attachAt {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinUniformBudget E) :
    ∃ K : ℕ, IsConverterAt (Set.univ : Set Uni.{u}) K (attachAt i E) := by
  obtain ⟨β, K, hβ, hK⟩ := hβ
  exact ⟨max K 1, ⟨System.attachEngineFully i E,
    System.isConverterMapAt_attachEngineFully_univ hIT hβ hK, rfl⟩⟩

/-- **CR18 §3.4.3's filter, at Φ.** -/
theorem isConverterAt_filterPhi (P : List Uni.{u} → Prop) (hP : PrefixClosed P) :
    IsConverterAt (Set.univ : Set Uni.{u}) 1 (filterPhi P hP) :=
  ⟨System.filterDom P hP, System.isConverterMapAt_filterDom P hP, rfl⟩

/-- MauRen16 §3.4's `⊣` is the filter at the query-avoiding predicate. -/
theorem isConverterAt_block (Q : Set Uni.{u}) :
    IsConverterAt (Set.univ : Set Uni.{u}) 1 (block Q) :=
  block_eq_filterPhi Q ▸ isConverterAt_filterPhi _ _

/-- CR18 Definition 3.10's query limit is the filter at the length predicate. -/
theorem isConverterAt_filterQueries (q : ℕ) :
    IsConverterAt (Set.univ : Set Uni.{u}) 1 (filterQueries.{u} q) :=
  ⟨System.filterQueries q,
    System.isConverterMapAt_filterDom _ (prefixClosed_length_le q), rfl⟩

/-- **Relabelling, at Φ.** -/
theorem isConverterAt_relabelLaw (f g : Uni.{u} → Uni.{u}) :
    IsConverterAt (Set.univ : Set Uni.{u}) 1
      (PDS.relabelLaw f g : Function.End Phi.{u}) :=
  ⟨System.relabel f g, System.isConverterMapAt_relabel f g, rfl⟩

/-! ### The generated monoid, demoted

The generated `converterMonoidAt` is kept — nothing that consumes it breaks —
but it is no longer the definition of a converter.  Its attachment family and
its domain-filter family are *instances* of the class, which is the
"every generator is an instance" half of the demotion.

Its two **parallel-frame** families are not, and the reason is structural
rather than a missing proof: `fun RL => par c RL TL` at a law-valued partner
`TL` is not the pushforward of any deterministic system map — it sends a point
mass to a *mixture* — so it cannot satisfy an A2 that quantifies over
deterministic systems.  A parallel frame introduces a resource rather than
transforming one, and the law-valued partner is where that shows.  Its home is
the mixture layer above this class (CR18 Definition 3.17;
`attachLawAt_apply_eq_sum` is the landed decomposition and
`mem_nonexpandingConverters_of_sum` the landed averaging step). -/

theorem attachAt_mem_converterClass {i : Set Uni.{u}}
    {E : System.DDS (Uni.{u} ⊕ Option Uni.{u}) (Uni.{u} ⊕ Uni.{u})}
    (hIT : System.InnerTotal E) (hβ : System.AnswersWithinUniformBudget E) :
    attachAt i E ∈ converterClass.{u} :=
  let ⟨_, h⟩ := exists_isConverterAt_attachAt hIT hβ
  h.mem_converterClass

theorem filterPhi_mem_converterClass (P : List Uni.{u} → Prop) (hP : PrefixClosed P) :
    filterPhi P hP ∈ converterClass.{u} :=
  (isConverterAt_filterPhi P hP).mem_converterClass

theorem block_mem_converterClass (Q : Set Uni.{u}) : block Q ∈ converterClass.{u} :=
  (isConverterAt_block Q).mem_converterClass

theorem filterQueries_mem_converterClass (q : ℕ) :
    filterQueries.{u} q ∈ converterClass.{u} :=
  (isConverterAt_filterQueries q).mem_converterClass

end

end RandomSystems

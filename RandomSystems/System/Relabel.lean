/-
Copyright (c) 2024-2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.System.ProbabilisticSystem

/-!
# Relabelling and blocking — the trivial converter generators

LiuZhang §3.3.3's trivial converters "perform no computation, and only
connect systems themselves": on the history-function carrier they are pure
function composition, and this module provides the two composition-shaped
generators of the converter monoid `Σ` (the third, `connect`, is the trace
and lives elsewhere):

* `relabel f g` — **relabelling**: precompose the input history with
  `map f`, postcompose the answer with `g`.  Re-encoding an alphabet is a
  construction, not an equality; the carrier is functorial in its alphabets
  and `relabel` is that functoriality (`relabel_id`, `relabel_relabel`).
* `block Z` — MauRen16 §3.4's `⊣` at an interface set: restrict the domain
  to histories that never address `Z`.  Blocking is composition with a
  partial identity — `filterDom` at the interface predicate — exactly the
  shape in which `attachAt_blkDDC` computed the old zoo's `⊣`.

Both transport `Valid` with no side conditions and lift to the
probabilistic layer as pushforwards (`PDS.relabelLaw`, `PDS.blockLaw`),
where the functor laws follow from `fTransform` composition.
-/

namespace RandomSystems

namespace System

noncomputable section

open Classical

universe u v u' v' w u'' v''

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}

/-! ## Relabelling -/

/-- **Relabelling**: the trivial converter given by an input translation
`f : X' → X` and an output translation `g : Y → Y'`, acting by history
pre-composition and answer post-composition — no state, no queries of its
own. -/
def relabel (f : X' → X) (g : Y → Y') (S : DDS X Y) : DDS X' Y' :=
  ⟨fun l => (S.1 (l.map f)).map g, by
    constructor
    · exact fun h => S.2.1 h
    · intro l₁ l₂ hpre hne hdom
      exact S.2.2 (hpre.map f)
        (fun hmap => hne (List.map_eq_nil_iff.mp hmap)) hdom⟩

@[simp]
theorem mem_dom_relabel (f : X' → X) (g : Y → Y') (S : DDS X Y)
    (l : List X') :
    l ∈ dom (relabel f g S) ↔ l.map f ∈ dom S :=
  Iff.rfl

/-- Relabelling translates the output and nothing else. -/
theorem output_relabel (f : X' → X) (g : Y → Y') (S : DDS X Y)
    (l : List X') (h : l ∈ dom (relabel f g S)) :
    output (relabel f g S) l h = g (output S (l.map f) h) :=
  rfl

/-- Functoriality, identity: relabelling by identities is the identity —
MauRen16 §3.3's `id ∈ Σ`, in generator form. -/
@[simp]
theorem relabel_id (S : DDS X Y) : relabel id id S = S := by
  apply Subtype.ext
  funext l
  simp only [relabel, List.map_id]
  exact Part.ext' Iff.rfl fun _ _ => rfl

/-- Functoriality, composition: consecutive relabellings compose as
functions — contravariantly on queries, covariantly on answers. -/
theorem relabel_relabel {X'' : Type u''} {Y'' : Type v''}
    (f' : X'' → X') (g' : Y' → Y'') (f : X' → X) (g : Y → Y')
    (S : DDS X Y) :
    relabel f' g' (relabel f g S) = relabel (f ∘ f') (g' ∘ g) S := by
  apply Subtype.ext
  funext l
  simp [relabel, Part.map_map]

/-! ## Blocking -/

variable {P : Type u} {A : Type v} {B : Type w}

/-- MauRen16 §3.4's `⊣` at an interface set `Z`: the trivial converter that
silences the interfaces in `Z`, by restricting the domain to histories that
never address them.  Blocking is composition with a partial identity — a
domain restriction, not an interactive object. -/
def block (Z : Set P) (S : Resource P A B) : Resource P A B :=
  filterDom (fun l => ∀ p ∈ l, p.1 ∉ Z)
    (by
      intro l₁ l₂ hpre h p hp
      exact h p (hpre.subset hp))
    S

@[simp]
theorem mem_dom_block (Z : Set P) (S : Resource P A B) (l : List (P × A)) :
    l ∈ dom (block Z S) ↔ l ∈ dom S ∧ ∀ p ∈ l, p.1 ∉ Z :=
  Iff.rfl

/-- Blocking preserves the original output wherever it is defined. -/
theorem output_block (Z : Set P) (S : Resource P A B) (l : List (P × A))
    (h : l ∈ dom (block Z S)) :
    output (block Z S) l h = output S l h.1 :=
  rfl

/-- Blocking nothing is the identity. -/
@[simp]
theorem block_empty (S : Resource P A B) : block (∅ : Set P) S = S := by
  apply Subtype.ext
  funext l
  exact Part.ext' (by simp [block]) (fun _ _ => rfl)

/-- A tag-preserving relabelling commutes with blocking: the block predicate
reads only interface tags, which the relabelling fixes. -/
theorem block_relabel (Z : Set P) (f : P × A → P × A)
    (hf : ∀ p, (f p).1 = p.1) (g : B → B) (S : Resource P A B) :
    block Z (relabel f g S) = relabel f g (block Z S) := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨hdom, hpred⟩
    refine ⟨hdom, fun p hp => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    rw [hf q]
    exact hpred q hq
  · rintro ⟨hdom, hpred⟩
    refine ⟨hdom, fun q hq => ?_⟩
    have h := hpred (f q) (List.mem_map_of_mem hq)
    rwa [hf q] at h

/-- MauRen16 §3.4's `⊣` at a query set: silence the queries in `Q`.  The
tagged form `block` is the instance at `{p | p.1 ∈ Z}`, and the whole
operation is CR18 Definition 3.10's domain filter at the query-avoiding
predicate (`prefixClosed_forall_not_mem`). -/
def blockSet {X : Type u} {Y : Type v} (Q : Set X) (S : DDS X Y) :
    DDS X Y :=
  filterDom (fun l => ∀ q ∈ l, q ∉ Q) (prefixClosed_forall_not_mem Q) S

/-- The block is the domain filter at the query-avoiding predicate — CR18
Definition 3.10 read at MauRen16 §3.4's `⊣`. -/
theorem blockSet_eq_filterDom {X : Type u} {Y : Type v} (Q : Set X)
    (S : DDS X Y) :
    blockSet Q S =
      filterDom (fun l => ∀ q ∈ l, q ∉ Q) (prefixClosed_forall_not_mem Q) S :=
  rfl

@[simp]
theorem mem_dom_blockSet {X : Type u} {Y : Type v} (Q : Set X)
    (S : DDS X Y) (l : List X) :
    l ∈ dom (blockSet Q S) ↔ l ∈ dom S ∧ ∀ q ∈ l, q ∉ Q :=
  Iff.rfl

theorem output_blockSet {X : Type u} {Y : Type v} (Q : Set X)
    (S : DDS X Y) (l : List X) (h : l ∈ dom (blockSet Q S)) :
    output (blockSet Q S) l h = output S l h.1 :=
  rfl

@[simp]
theorem blockSet_empty {X : Type u} {Y : Type v} (S : DDS X Y) :
    blockSet (∅ : Set X) S = S := by
  apply Subtype.ext
  funext l
  exact Part.ext' (by simp [blockSet]) (fun _ _ => rfl)

/-- Consecutive query-set blocks merge into the union. -/
theorem blockSet_blockSet {X : Type u} {Y : Type v} (Q₁ Q₂ : Set X)
    (S : DDS X Y) :
    blockSet Q₁ (blockSet Q₂ S) = blockSet (Q₁ ∪ Q₂) S := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨⟨hdom, h₂⟩, h₁⟩
    refine ⟨hdom, fun q hq => ?_⟩
    simp only [Set.mem_union, not_or]
    exact ⟨h₁ q hq, h₂ q hq⟩
  · rintro ⟨hdom, h⟩
    exact ⟨⟨hdom, fun q hq hQ₂ => h q hq (Set.mem_union_right _ hQ₂)⟩,
      fun q hq hQ₁ => h q hq (Set.mem_union_left _ hQ₁)⟩

/-- The tagged block is the query-set block at the tag cylinder. -/
theorem block_eq_blockSet {P : Type u} {A : Type v} {B : Type w}
    (Z : Set P) (S : Resource P A B) :
    block Z S = blockSet {p : P × A | p.1 ∈ Z} S :=
  rfl

/-- Consecutive blocks merge: blocking is a homomorphism from `(Set P, ∪)`
to domain restrictions. -/
theorem block_block (Z₁ Z₂ : Set P) (S : Resource P A B) :
    block Z₁ (block Z₂ S) = block (Z₁ ∪ Z₂) S := by
  apply Subtype.ext
  funext l
  refine Part.ext' ?_ (fun _ _ => rfl)
  constructor
  · rintro ⟨⟨hdom, h₂⟩, h₁⟩
    refine ⟨hdom, fun p hp => ?_⟩
    simp only [Set.mem_union, not_or]
    exact ⟨h₁ p hp, h₂ p hp⟩
  · rintro ⟨hdom, h⟩
    exact ⟨⟨hdom, fun p hp hZ₂ => h p hp (Set.mem_union_right _ hZ₂)⟩,
      fun p hp hZ₁ => h p hp (Set.mem_union_left _ hZ₁)⟩

end

end System

/-! ## The probabilistic layer

The generators lift to `PDS` as pushforwards; the functor laws follow from
`fTransform` composition, with no new content. -/

namespace PDS

noncomputable section

open Probability (Distribution)

universe u v u' v' w u'' v''

variable {X : Type u} {Y : Type v} {X' : Type u'} {Y' : Type v'}

/-- Relabelling, lifted to probabilistic systems by pushforward. -/
def relabelLaw (f : X' → X) (g : Y → Y') : PDS X Y → PDS X' Y' :=
  Distribution.fTransform (System.relabel f g)

@[simp]
theorem relabelLaw_id (S : PDS X Y) : relabelLaw id id S = S := by
  rw [relabelLaw,
    show System.relabel (X := X) (Y := Y) id id = id from
      funext System.relabel_id,
    Distribution.fTransform_id]

theorem relabelLaw_relabelLaw {X'' : Type u''} {Y'' : Type v''}
    (f' : X'' → X') (g' : Y' → Y'') (f : X' → X) (g : Y → Y')
    (S : PDS X Y) :
    relabelLaw f' g' (relabelLaw f g S) = relabelLaw (f ∘ f') (g' ∘ g) S := by
  rw [relabelLaw, relabelLaw, relabelLaw, Distribution.fTransform_fTransform]
  exact congrFun (congrArg _ (funext (System.relabel_relabel f' g' f g))) S

variable {P : Type u} {A : Type v} {B : Type w}

/-- Blocking, lifted to probabilistic systems by pushforward. -/
def blockLaw (Z : Set P) : PDS (P × A) B → PDS (P × A) B :=
  Distribution.fTransform (System.block Z)

@[simp]
theorem blockLaw_empty (S : PDS (P × A) B) : blockLaw (∅ : Set P) S = S := by
  rw [blockLaw,
    show System.block (∅ : Set P) (A := A) (B := B) = id from
      funext System.block_empty,
    Distribution.fTransform_id]

theorem blockLaw_blockLaw (Z₁ Z₂ : Set P) (S : PDS (P × A) B) :
    blockLaw Z₁ (blockLaw Z₂ S) = blockLaw (Z₁ ∪ Z₂) S := by
  rw [blockLaw, blockLaw, blockLaw, Distribution.fTransform_fTransform]
  exact congrFun (congrArg _ (funext (System.block_block Z₁ Z₂))) S

end

end PDS

end RandomSystems

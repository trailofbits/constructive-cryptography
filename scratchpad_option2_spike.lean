/-
Option-2 spike: Φ := PDS 𝒰 𝒰 with 𝒰 := Σ X : Type u, X.

REAL here (no sorry, no axiom): the carrier, the canonical embedding of an
arbitrary `PDS X Y`, specifications mixing signatures, Σ as a generated
submonoid of plain endomorphisms, generalized blocking with its merge law,
the support/encoding receipt, and Adv/serial-composition instantiation.

POSITED (section variables, clearly named `h…`): the in-Φ parallel merge and
the support-addressed attachment family with its disjoint commutation — the
two pieces whose real construction is the existing interleaving machinery
re-addressed by support.  The MR16 §7 grouping layer is then consumed FOR
REAL over the posited base.
-/
import RandomSystems.Converter.Sigma
import RandomSystems.System.Environment

namespace Scratch

open RandomSystems
open Probability (Distribution)
open Classical
open scoped ENNReal

noncomputable section

universe u

/-! ## §1 The carrier: one fiber, no packaging -/

/-- The universal alphabet: every `u`-typed value, canonically addressed by
its type. -/
def Uni : Type (u + 1) := Σ X : Type u, X

/-- MR16 §2.3's Φ — literally one PDS type.  No `mk`, no `⊥`. -/
def Phi' : Type (u + 1) := PDS Uni.{u} Uni.{u}

/-- A specification is a set of resources; signatures mix freely. -/
abbrev Spec := Set Phi'.{u}

/-! ## §2 The canonical embedding: all PDS fit, as a theorem-shape -/

/-- Decode a universal query at alphabet `X`: defined iff it lies in `X`'s
copy.  The one place a type equality appears. -/
def decode (X : Type u) (q : Uni.{u}) : Part X :=
  ⟨q.1 = X, fun h => h ▸ q.2⟩

/-- Decode a history entrywise. -/
def decodeList (X : Type u) : List Uni.{u} → Part (List X)
  | [] => Part.some []
  | q :: t => (decode X q).bind fun x => (decodeList X t).map (x :: ·)

/-- The canonical embedding of an arbitrary system: decode every query at
`X`, run `S`, re-encode the answer at `Y`.  A foreign query is out of
domain — partiality by undefinedness, not an error element. -/
def embedRaw {X Y : Type u} (S : System.DDS X Y) :
    System.Raw Uni.{u} Uni.{u} := fun l =>
  ((decodeList X l).bind fun lx => S.1 lx).map fun y => (⟨Y, y⟩ : Uni.{u})

def embedD {X Y : Type u} (S : System.DDS X Y) :
    System.DDS Uni.{u} Uni.{u} :=
  System.validate (embedRaw S)

/-- The embedding at the probabilistic level. -/
def embed {X Y : Type u} : PDS X Y → Phi'.{u} :=
  Distribution.fTransform embedD

/-- Mixed-signature specifications type-check with no packaging: a spec
holding a `Bool`-resource and an `ℕ`-resource. -/
example (S₁ : PDS Bool Bool) (S₂ : PDS Nat Nat) : Spec.{0} :=
  {embed S₁, embed S₂}

/-! ## §3 Support: the interface set is derived, not data -/

/-- The queries a system can ever answer. -/
def dsupport (S : System.DDS Uni.{u} Uni.{u}) : Set Uni.{u} :=
  {q | ∃ l ∈ System.dom S, q ∈ l}

/-- A defined decoding certifies every entry's address. -/
theorem decodeList_dom_mem {X : Type u} :
    ∀ {l : List Uni.{u}}, (decodeList X l).Dom → ∀ q ∈ l, q.1 = X := by
  intro l
  induction l with
  | nil =>
      intro _ q hq
      exact absurd hq (List.not_mem_nil)
  | cons a t ih =>
      intro h q hq
      obtain ⟨ha, hrest⟩ := Part.bind_dom.mp h
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact ha
      · exact ih hrest q hq'

/-- **Encoding receipt**: an embedded system's support lies in its own
alphabet's copy — the signature recovered as a theorem about the element,
not carried as data on it. -/
theorem dsupport_embedD {X Y : Type u} (S : System.DDS X Y) :
    dsupport (embedD S) ⊆ {q | q.1 = X} := by
  rintro q ⟨l, hl, hq⟩
  have hraw : (embedRaw S l).Dom := hl.2 l (List.prefix_refl _) hl.1
  obtain ⟨hdec, -⟩ := hraw
  exact decodeList_dom_mem hdec q hq

/-! ## §3b The literal union: "the set of all PDS X Y, for all X Y" -/

/-- The union itself, written down as asked: one `Set`, indexed by all
alphabets at once.  An element is a bare behavior; `∈` says it is (the
inclusion of) a typed PDS for SOME signature. -/
def PhiSet : Set Phi'.{u} :=
  ⋃ (X : Type u) (Y : Type u), Set.range (embed (X := X) (Y := Y))

/-- Every typed PDS is literally a member — no packaging in the element. -/
example {X Y : Type u} (S : PDS X Y) : embed S ∈ PhiSet.{u} :=
  Set.mem_iUnion.mpr ⟨X, Set.mem_iUnion.mpr ⟨Y, ⟨S, rfl⟩⟩⟩

/-- Membership is a property, not data: an element of the union is an
untyped behavior, and *which* signature witnesses it is existential. -/
example (R : Phi'.{u}) (h : R ∈ PhiSet.{u}) :
    ∃ (X Y : Type u) (S : PDS X Y), embed S = R := by
  obtain ⟨_, ⟨X, rfl⟩, _, ⟨Y, rfl⟩, S, hS⟩ := h
  exact ⟨X, Y, S, hS⟩

/-! ## §4 Σ: converters are plain functions; MR16 §3 structure -/

/-- MauRen16 §3.4's `⊣`, generalized to an arbitrary query set: silence the
queries in `Q`.  Tagged blocking is the special case `Q = Z ×ˢ univ`. -/
def blockD (Q : Set Uni.{u}) (S : System.DDS Uni.{u} Uni.{u}) :
    System.DDS Uni.{u} Uni.{u} :=
  System.filterDom (fun l => ∀ q ∈ l, q ∉ Q)
    (fun _ _ hpre h q hq => h q (hpre.subset hq)) S

def blockLaw' (Q : Set Uni.{u}) : Function.End Phi'.{u} :=
  Distribution.fTransform (blockD Q)

/-- Blocks merge — the fiber proof transfers verbatim to the support-based
form. -/
theorem blockD_blockD (Q₁ Q₂ : Set Uni.{u})
    (S : System.DDS Uni.{u} Uni.{u}) :
    blockD Q₁ (blockD Q₂ S) = blockD (Q₁ ∪ Q₂) S := by
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

/-- Σ as the generated submonoid of the endomorphisms of the ONE Φ:
relabelling (now an ordinary converter, no glue role) and blocking; the
attachment family joins below. -/
def SigmaMonoid : Submonoid (Function.End Phi'.{u}) :=
  Submonoid.closure
    (Set.range (fun fg : (Uni.{u} → Uni.{u}) × (Uni.{u} → Uni.{u}) =>
        (PDS.relabelLaw fg.1 fg.2 : Function.End Phi'.{u})) ∪
      Set.range blockLaw')

/-- `id ∈ Σ` and closure under composition: submonoid structure. -/
example : (1 : Function.End Phi'.{u}) ∈ SigmaMonoid.{u} :=
  Submonoid.one_mem _

example (π σ : Function.End Phi'.{u}) (hπ : π ∈ SigmaMonoid.{u})
    (hσ : σ ∈ SigmaMonoid.{u}) : π * σ ∈ SigmaMonoid.{u} :=
  Submonoid.mul_mem _ hπ hσ

/-! ## §5 Posited: in-Φ parallel and support-addressed attachment -/

section Posited

variable (par' : Phi'.{u} → Phi'.{u} → Phi'.{u})
variable (Engine : Type (u + 1))
variable (att : Set Uni.{u} → Engine → Function.End Phi'.{u})
variable (hatt_comm : ∀ {Q₁ Q₂ : Set Uni.{u}}, Disjoint Q₁ Q₂ →
    ∀ E F, AbstractCryptography.ActCommute Phi'.{u} (att Q₁ E) (att Q₂ F))

/-- **MR16 §7 consumed for real** over the posited base: parties are labels,
each party owning a disjoint address set; the pairwise axiom holds, so
grouped order invariance follows from the abstract layer with no new code. -/
example {ι : Type} (addr : ι → Set Uni.{u})
    (hdisj : Pairwise (Function.onFun Disjoint addr)) :
    AbstractCryptography.PairwiseOrderInvariant Phi'.{u}
      (fun i E => att (addr i) E) :=
  fun _ _ hij E F => hatt_comm (hdisj hij) E F

example {ι : Type} (addr : ι → Set Uni.{u})
    (hdisj : Pairwise (Function.onFun Disjoint addr)) {Z₁ Z₂ : Set ι}
    (h : Disjoint Z₁ Z₂) :
    AbstractCryptography.OrderInvariant Phi'.{u}
      (AbstractCryptography.attachedWithin
        (fun i E => att (addr i) E) Z₁).subtype
      (AbstractCryptography.attachedWithin
        (fun i E => att (addr i) E) Z₂).subtype :=
  AbstractCryptography.orderInvariant_attachedWithin _
    (fun _ _ hij E F => hatt_comm (hdisj hij) E F) h

/-! ## §6 Composition at every level, inside the one Φ -/

/-- Context embedding: a protocol `π` written for `R` applies unchanged to
`R` in a larger context — addresses are absolute, so embedding is
invisible. -/
example (π : Function.End Phi'.{u}) (R C : Phi'.{u}) : Phi'.{u} :=
  π (par' R C)

/-- A 3-party MPC shape: per-party converters at disjoint addresses,
composed in Σ, applied to a resource assembled in Φ. -/
example (πA πB πE : Function.End Phi'.{u}) (K N : Phi'.{u}) : Phi'.{u} :=
  (πA * πB * πE) (par' K N)

/-- Random-systems interop: the Lanzenberger metric applies verbatim —
Φ IS a PDS type, so `Adv` needs no lifting. -/
example (R S : Phi'.{u}) : ℝ≥0∞ := PDS.Adv R S

/-- A construction-statement shape across the levels: real resource,
protocol, ideal resource in context — one algebra end to end. -/
example (π : Function.End Phi'.{u}) (R S C : Phi'.{u}) : Prop :=
  PDS.Adv (π (par' R C)) (par' S C) = 0

end Posited

end

end Scratch

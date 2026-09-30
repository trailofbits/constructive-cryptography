import RandomSystems.Converter.ConverterAttachment
import Mathlib.CategoryTheory.Types.Basic

/-!
# Interfaces, resources and converters

An interface is the tuple `A = (I, X, Y, D)`: finitely many labels, finite input and output
alphabets at each label, and a finite domain of input histories, prefix-closed and without
the empty history. A resource on `A` is a random system on these alphabets over this domain
that replies at the queried interface. A converter from `A` to `B` is the behavior of a PDC
from `B`'s domain (inside) to `A`'s domain (outside); it acts on resources by attachment.
Interfaces and converters are an instance of `Category`, with serial composition and the
identity; attachment is a contravariant functor to types.
Sources: MR16, §3 (printed pp. 6–8); Jost, Definitions 2.2.1–2.2.2 (printed pp. 16–18);
CR18, Definitions 3.8, 3.9 and 3.17 (printed pp. 61–64).

## Main definitions

* `Interface`: labels, alphabets and a finite domain
* `Interface.queryBudget I X Y q`: the domain of at most `q` queries
* `Interface.portBudget I X Y q`: the domain of at most `q i` queries at each label `i`
* `Interface.Resource A`: resources on `A`
* `Interface.Resource.ofPDS`, `Interface.ofDeterministic`: the resource of a PDS of
  deterministic resources, and of one deterministic resource
* `Interface.Converter A B`: converters from `A` to `B`, concretely behaviors of PDCs
* `Interface.category`: the category of interfaces and converters
* `Interface.ofDDC`: the converter of a DDC from `B`'s domain to `A`'s
* `Interface.attach`: attachment of a converter to a resource

## Main results

* `Interface.Resource.exists_ofPDS`: every resource is the resource of a PDS
* `Interface.identity_attach`: attaching the identity leaves a resource unchanged
* `Interface.comp_smul`: attaching a serial composition attaches the inner converter first
* `Interface.ofDDC_apply`: the converter of a DDC is one on its transcripts
-/

namespace SystemAlgebra

open CategoryTheory

/-- The interface-and-domain tuple indexing a class of resources. -/
structure Interface where
  /-- Local interface labels. -/
  I : Type
  /-- Input alphabet at each interface. -/
  X : I → Type
  /-- Output alphabet at each interface. -/
  Y : I → Type
  [instFintypeI : Fintype I]
  [instFintypeX : ∀ i, Fintype (X i)]
  [instFintypeY : ∀ i, Fintype (Y i)]
  /-- The domain of input histories. -/
  domain : List (Σ i, X i) → Prop
  /-- Silent before the first query, and closed under nonempty prefixes. -/
  nonempty_prefix : ¬ domain [] ∧ ∀ {p h}, p <+: h → p ≠ [] → domain h → domain p
  /-- A bound on the number of queries. -/
  bound : ℕ
  length_le : ∀ h, domain h → h.length ≤ bound

attribute [instance] Interface.instFintypeI Interface.instFintypeX Interface.instFintypeY

namespace Interface

/-- The domain of at most `q` queries. -/
abbrev queryBudget (I : Type) [Fintype I] (X Y : I → Type) [∀ i, Fintype (X i)]
    [∀ i, Fintype (Y i)] (q : ℕ) : Interface where
  I := I
  X := X
  Y := Y
  domain h := h ≠ [] ∧ h.length ≤ q
  nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne hd => ⟨hne, hp.length_le.trans hd.2⟩⟩
  bound := q
  length_le _ hd := hd.2

/-- The domain of at most `q i` queries at each label `i`. -/
abbrev portBudget (I : Type) [Fintype I] (X Y : I → Type) [∀ i, Fintype (X i)]
    [∀ i, Fintype (Y i)] (q : I → ℕ) : Interface where
  I := I
  X := X
  Y := Y
  domain h := h ≠ [] ∧ ∀ i, (restrict i h).length ≤ q i
  nonempty_prefix := ⟨fun h => h.1 rfl, fun hp hne hd =>
    ⟨hne, fun i => (restrict_prefix i hp).length_le.trans (hd.2 i)⟩⟩
  bound := ∑ i, q i
  length_le h hd := (length_eq_sum_restrict h).trans_le (Finset.sum_le_sum fun i _ => hd.2 i)

/-- The input domain of `A`, as a domain of random systems. -/
abbrev inputDomain (A : Interface) : Domain (Σ i, A.X i) (Σ i, A.Y i) :=
  Domain.ofInputs A.domain A.bound A.length_le

/-- Resources on `A`: random systems over its domain replying at the queried interface. -/
def Resource (A : Interface) :=
  {R : RandomSystem (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain // R.RepliesAtQueriedInterface}

/-- The behavior of a PDS of deterministic resources with domain `A.domain`. -/
noncomputable def Resource.ofPDS {A : Interface}
    (P : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h}) : Resource A :=
  ⟨RandomSystem.ofPDS P.1 P.2 (fun s _ _ _ _ => s.2.2.2 _),
    RandomSystem.ofPDS_repliesAtQueriedInterface P⟩

/-- Every resource is the behavior of a PDS of deterministic resources. -/
theorem Resource.exists_ofPDS {A : Interface} (R : Resource A) :
    ∃ Q : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h},
      Resource.ofPDS Q = R := by
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation A.nonempty_prefix R.1 R.2
  exact ⟨Q, Subtype.ext (RandomSystem.ext hQ)⟩

/-- A deterministic resource, as its point distribution. -/
noncomputable def ofDeterministic {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h) :
    Resource A :=
  Resource.ofPDS ⟨Finsupp.single ⟨s, hs⟩ 1, Probability.Distribution.isProbDist_single _⟩

open Classical in
theorem ofDeterministic_mass {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (ofDeterministic s hs).1 h =
      if Replies s (h.map Prod.fst) (h.map Prod.snd) then 1 else 0 := by
  simp [ofDeterministic, Resource.ofPDS, RandomSystem.ofPDS, behaviorMass,
    Probability.Distribution.mass, Finsupp.sum]

/-- Converters from `A` to `B`: behaviors of PDCs from `B`'s domain (inside) to `A`'s
domain (outside). -/
abbrev Converter (A B : Interface) :=
  PDCBehavior A.I B.I A.X A.Y B.X B.Y B.domain B.bound B.length_le A.domain A.bound A.length_le

/-- Interfaces and converters form a category under serial composition. -/
noncomputable instance category : Category Interface where
  Hom := Converter
  id A := PDCBehavior.id A.nonempty_prefix
  comp α β := PDCBehavior.comp α β
  id_comp {A _} α := PDCBehavior.id_comp α A.nonempty_prefix
  comp_id {_ B} α := PDCBehavior.comp_id α B.nonempty_prefix
  assoc α β γ := PDCBehavior.comp_assoc α β γ

/-- The converter of a DDC from `B`'s domain to `A`'s domain. -/
noncomputable def ofDDC {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α) : A ⟶ B :=
  PDCBehavior.ofDDC α hα

/-- The converter of a DDC gives probability one to its transcripts and zero to all others. -/
theorem ofDDC_apply {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α)
    (t : List ((Σ l, twoFam A.X B.Y l) × (Σ l, twoFam A.Y B.X l))) :
    (ofDDC α hα).1 t = open Classical in
      if Replies α (t.map Prod.fst) (t.map Prod.snd) then 1 else 0 :=
  PDCBehavior.ofDDC_apply α hα t

/-- Attachment of a converter to a resource. -/
noncomputable def attach {A B : Interface} (α : A ⟶ B) (R : Resource B) : Resource A :=
  ⟨PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2,
    PDCBehavior.attach_repliesAtQueriedInterface _ _ α R.1 R.2⟩

/-- The action of a converter on a resource is attachment. As a default instance, an arrow
whose domains are still to be inferred takes them from the resource it acts on. -/
@[default_instance high]
noncomputable instance {A B : Interface} : HSMul (A ⟶ B) (Resource B) (Resource A) :=
  ⟨attach⟩

theorem smul_val {A B : Interface} (α : A ⟶ B) (R : Resource B) :
    (α • R).1 = PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2 := rfl

/-- **Attaching the identity** leaves a resource unchanged. -/
theorem identity_attach {A : Interface} (R : Resource A) : (𝟙 A • R : Resource A) = R :=
  Subtype.ext (PDCBehavior.attach_id A.nonempty_prefix R.1 R.2)

/-- **Serial attachment** (MR16 §3.3, printed p. 7: “(β ∘ α)ⁱR = βⁱ(αⁱR)”): attaching a
serial composition attaches the inner converter first. -/
theorem comp_smul {A B C : Interface} (α : A ⟶ B) (β : B ⟶ C) (R : Resource C) :
    (α ≫ β) • R = α • (β • R) :=
  Subtype.ext (PDCBehavior.attach_comp C.nonempty_prefix A.nonempty_prefix B.nonempty_prefix
    α β R.1 R.2)

theorem comp_eq {A B C : Interface} (α : A ⟶ B) (β : B ⟶ C) :
    α ≫ β = PDCBehavior.comp α β := rfl

end Interface

end SystemAlgebra

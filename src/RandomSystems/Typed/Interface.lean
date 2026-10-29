import RandomSystems.Converter.ConverterAttachment

/-!
# Interfaces, typed systems and typed converters

An interface is the tuple `A = (I, X, Y, D)`: finitely many labels, finite input and output
alphabets at each label, and a finite domain of input histories, prefix-closed and without
the empty history. A typed system on `A` is a random system on these alphabets over this domain
that replies at the queried interface. A typed converter from `A` to `B` is the behavior of a PDC
from `B`'s domain (inside) to `A`'s domain (outside); it acts on typed systems by the
attachment of PDC behaviors.
Sources: MR16, §3 (printed pp. 6–8); Jost, Definitions 2.2.1–2.2.2 (printed pp. 16–18);
CR18, Definitions 3.8, 3.9 and 3.17 (printed pp. 61–64).

## Main definitions

* `Interface`: labels, alphabets and a finite domain
* `Interface.queryBudget I X Y q`: the domain of at most `q` queries
* `Interface.portBudget I X Y q`: the domain of at most `q i` queries at each label `i`
* `TypedSystem A`: typed systems on `A`
* `TypedSystem.ofPDS`, `TypedSystem.ofDeterministic`: the typed system of a PDS of
  deterministic systems, and of one deterministic system
* `TypedConverter A B`: typed converters from `A` to `B`, behaviors of PDCs
* `TypedConverter.comp`, `TypedConverter.id`: serial composition and the identity, of PDC
  behaviors
* `TypedConverter.ofDDC`: the typed converter of a DDC from `B`'s domain to `A`'s
* `TypedConverter.attach`: attachment of a typed converter to a typed system

## Main results

* `TypedSystem.exists_ofPDS`: every typed system is the typed system of a PDS
* `TypedConverter.identity_attach`: attaching the identity leaves a typed system unchanged
* `TypedConverter.comp_smul`: attaching a serial composition attaches the inner converter first
* `TypedConverter.ofDDC_apply`: the typed converter of a DDC is one on its transcripts
* `TypedConverter.ofDDC_eq_comp`: a DDC equal to the trimmed serial wiring of `α` (outside) and
  `β` (inside) is `comp (ofDDC α) (ofDDC β)`, whatever bound it is certified with
-/

namespace SystemAlgebra

/-- The interface-and-domain tuple indexing a class of typed systems. -/
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

end Interface

/-- Typed systems on `A`: random systems over its domain replying at the queried interface. -/
def TypedSystem (A : Interface) :=
  {R : RandomSystem (Σ i, A.X i) (Σ i, A.Y i) A.inputDomain // R.RepliesAtQueriedInterface}

/-- The behavior of a PDS of deterministic systems with domain `A.domain`. -/
noncomputable def TypedSystem.ofPDS {A : Interface}
    (P : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h}) : TypedSystem A :=
  ⟨RandomSystem.ofPDS P.1 P.2 (fun s _ _ _ _ => s.2.2.2 _),
    RandomSystem.ofPDS_repliesAtQueriedInterface P⟩

/-- Every typed system is the behavior of a PDS of deterministic systems. -/
lemma TypedSystem.exists_ofPDS {A : Interface} (R : TypedSystem A) :
    ∃ Q : Probability.Distribution.ProbDist {s : InterfaceSystem A.I A.X A.Y //
      IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h},
      TypedSystem.ofPDS Q = R := by
  obtain ⟨Q, hQ⟩ := RandomSystem.exists_resource_presentation A.nonempty_prefix R.1 R.2
  exact ⟨Q, Subtype.ext (RandomSystem.ext hQ)⟩

/-- A deterministic system, as its point distribution. -/
noncomputable def TypedSystem.ofDeterministic {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h) :
    TypedSystem A :=
  TypedSystem.ofPDS ⟨Finsupp.single ⟨s, hs⟩ 1, Probability.Distribution.isProbDist_single _⟩

open Classical in
lemma TypedSystem.ofDeterministic_mass {A : Interface} (s : InterfaceSystem A.I A.X A.Y)
    (hs : IsDDS s ∧ SystemAlgebra.RepliesAtQueriedInterface s ∧ ∀ h, (s h).Dom ↔ A.domain h)
    (h : List ((Σ i, A.X i) × (Σ i, A.Y i))) :
    (TypedSystem.ofDeterministic s hs).1 h =
      if Replies s (h.map Prod.fst) (h.map Prod.snd) then 1 else 0 := by
  simp [TypedSystem.ofDeterministic, TypedSystem.ofPDS, RandomSystem.ofPDS, behaviorMass,
    Probability.Distribution.mass, Finsupp.sum]

/-- Typed converters from `A` to `B`: behaviors of PDCs from `B`'s domain (inside) to `A`'s
domain (outside). -/
@[instance_reducible] def TypedConverter (A B : Interface) :=
  PDCBehavior A.I B.I A.X A.Y B.X B.Y B.domain B.bound B.length_le A.domain A.bound A.length_le

namespace TypedConverter

/-- Serial composition of typed converters: the composition of their PDC behaviors, `α` outside
and `β` inside. -/
noncomputable def comp {A B C : Interface} (α : TypedConverter A B) (β : TypedConverter B C) :
    TypedConverter A C :=
  PDCBehavior.comp α β

/-- The identity typed converter: the identity PDC behavior on `A`'s domain. -/
protected noncomputable def id (A : Interface) : TypedConverter A A :=
  PDCBehavior.id A.nonempty_prefix

/-- The typed converter of a DDC from `B`'s domain to `A`'s domain. -/
noncomputable def ofDDC {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α) : TypedConverter A B :=
  PDCBehavior.ofDDC α hα

/-- The typed converter of a DDC gives probability one to its transcripts and zero to all
others. -/
lemma ofDDC_apply {A B : Interface} (α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y)
    {b : ℕ} (hα : IsDDCFrom B.domain A.domain b α)
    (t : List ((Σ l, twoFam A.X B.Y l) × (Σ l, twoFam A.Y B.X l))) :
    (ofDDC α hα).1 t = open Classical in
      if Replies α (t.map Prod.fst) (t.map Prod.snd) then 1 else 0 :=
  PDCBehavior.ofDDC_apply α hα t

/-- **A direct DDC presents the serial composition.** For DDCs `α` (outside, `A` to `B`) and
`β` (inside, `B` to `C`), a DDC `γ = trim (serialM α β)` certified with its own bound `c` gives
`ofDDC γ hγ = comp (ofDDC α hα) (ofDDC β hβ)`, although `c` need not be the product bound
`b * a` of `IsDDCFrom.comp`.

```text
    A ┌───┐ B ┌───┐ C             A ┌────────────────────────┐ C
  ────┤ α ├───┤ β ├────    =    ────┤ γ = trim (serialM α β) ├────
      └───┘   └───┘                 └────────────────────────┘
```

This is a presentation bridge of the repository, not a source statement: a typed converter is
a cumulative behavior, which does not depend on the bound certified for a DDC. The bound is the
finite bound on consecutive inside outputs of Jost, Definition 2.2.2 (printed pp. 17–18). The
attachment law of serial composition, MR16 §3.3 (printed p. 7), “(β ∘ α)ⁱR = βⁱ(αⁱR)” with the
paper's `β` outside, is `comp_smul`. -/
lemma ofDDC_eq_comp {A B C : Interface}
    {α : InsideOutsideSystem A.I B.I A.X A.Y B.X B.Y}
    {β : InsideOutsideSystem B.I C.I B.X B.Y C.X C.Y}
    {γ : InsideOutsideSystem A.I C.I A.X A.Y C.X C.Y} {a b c : Nat}
    (hα : IsDDCFrom B.domain A.domain a α) (hβ : IsDDCFrom C.domain B.domain b β)
    (hγ : IsDDCFrom C.domain A.domain c γ) (he : γ = trim (serialM α β)) :
    ofDDC γ hγ = comp (ofDDC α hα) (ofDDC β hβ) := by
  -- `PDCBehavior.comp_ofDDC`: the composition is `ofDDC (trim (serialM α β))` with bound `b * a`.
  change PDCBehavior.ofDDC γ hγ =
    PDCBehavior.comp (PDCBehavior.ofDDC α hα) (PDCBehavior.ofDDC β hβ)
  rw [PDCBehavior.comp_ofDDC]
  subst γ
  -- The behavior of a DDC depends on its replies, not on the chosen certificate.
  apply PDCBehavior.ext
  intro t
  simp only [PDCBehavior.ofDDC_apply]

/-- Attachment of a typed converter to a typed system. -/
noncomputable def attach {A B : Interface} (α : TypedConverter A B) (R : TypedSystem B) :
    TypedSystem A :=
  ⟨PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2,
    PDCBehavior.attach_repliesAtQueriedInterface _ _ α R.1 R.2⟩

/-- The action of a typed converter on a typed system is attachment. -/
noncomputable instance {A B : Interface} :
    HSMul (TypedConverter A B) (TypedSystem B) (TypedSystem A) :=
  ⟨attach⟩

lemma smul_val {A B : Interface} (α : TypedConverter A B) (R : TypedSystem B) :
    (α • R).1 = PDCBehavior.attach B.nonempty_prefix A.nonempty_prefix α R.1 R.2 := rfl

/-- **Attaching the identity** leaves a typed system unchanged. -/
lemma identity_attach {A : Interface} (R : TypedSystem A) :
    (TypedConverter.id A • R : TypedSystem A) = R :=
  Subtype.ext (PDCBehavior.attach_id A.nonempty_prefix R.1 R.2)

/-- **Serial attachment** (MR16 §3.3, printed p. 7: “(β ∘ α)ⁱR = βⁱ(αⁱR)”): attaching a
serial composition attaches the inner converter first. -/
theorem comp_smul {A B C : Interface} (α : TypedConverter A B) (β : TypedConverter B C)
    (R : TypedSystem C) : comp α β • R = α • (β • R) :=
  Subtype.ext (PDCBehavior.attach_comp C.nonempty_prefix A.nonempty_prefix B.nonempty_prefix
    α β R.1 R.2)

end TypedConverter

end SystemAlgebra

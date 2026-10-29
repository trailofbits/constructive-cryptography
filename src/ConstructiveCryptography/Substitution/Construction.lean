import ConstructiveCryptography.Substitution.Implication

set_option autoImplicit false

/-!
# Construction from implication witnesses

A construction with a simulator is given by implication witnesses between the real systems
and the simulated ideal systems (Banfi, Definition 2.4.3). Two such constructions compose
serially: the witnesses concatenate, with the assumption families tagged by `Sum`, and the
simulators compose (Banfi, Theorem 2.4.4). The equality of the two attached middle resources
is a hypothesis.

## Proof chain

```text
(π₂ ≫ π₁) real ═ π₂(π₁ real)        attach_serial
               ≃…≃ π₂(σ₁ middle)   inner chain, mapped by π₂
               ═ σ'(π₂ middle)      commutes
               ≃…≃ σ'(σ₂ ideal)    outer chain, mapped by σ'
               ═ (σ' ≫ σ₂) ideal    attach_serial
```

Here `π₁ = innerProtocol`, `π₂ = outerProtocol`, `σ₁ = innerSimulator`,
`σ₂ = outerSimulator`, `σ' = transportedSimulator`, and `π₂(R)` abbreviates
`attach outerProtocol R`, so `(π₂ ≫ π₁) real = π₂(π₁ real)`. `═` is exact equality of
resources, `≃…≃` a chain of premise uses. The inner uses are counted in `ι`, the outer uses
in `κ`, and the combined count of each name equals its original count; no error is involved.

## Main results

* `SubstitutionRelation.Implication.exists_serial_simulators`: concatenation of witnesses
* `Specification.Constructs.derivable_serial_simulators`: serial composition of
  constructions

Source: Banfi 2023, §2.4.
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory

universe u v w x y

-- `C` is the category of interfaces; `A ⟶ B` is a converter with outside `A`, inside `B`.
variable {C : Type u} [Category.{v} C]
-- `Phi A` is the type of resources on `A`; `attach α : Phi B → Phi A` for `α : A ⟶ B`.
variable {Phi : C → Type w} [ResourceTheory C Phi]
-- ι (iota) names the inner construction's assumptions and κ (kappa) the outer one's; the
-- combined family is `ι ⊕ κ`, with `Sum.inl i` inner and `Sum.inr k` outer names.
variable {ι : Type x} {κ : Type y}
-- `innerBoundary i : C` and `outerBoundary k : C` are the interfaces of those assumptions.
variable {innerBoundary : ι → C} {outerBoundary : κ → C}
-- `innerSystems i b` and `outerSystems k b` are their systems `X_{i,b}`, `X_{k,b}`.
variable {innerSystems : ∀ i, Bool → Phi (innerBoundary i)}
variable {outerSystems : ∀ i, Bool → Phi (outerBoundary i)}

/-- Serial real/ideal implications combine their named assumptions, compose
the protocol and simulators, and preserve each source family's use counts.

Banfi, Theorem 2.4.4 (printed p. 29), identifies the composite simulator as
"`σ₁σ₂`" and concludes implication under
"`s₁,₁, s₁,₂, ..., s₂,₁, s₂,₂, ...`". The explicit witness below also retains
the counts defined in Section 2.3.1 (printed p. 14). `commutes` is the exact
middle equality used in the displayed source proof.

The combined witness is `(reindex Sum.inl inner).map outerProtocol` appended to
`(reindex Sum.inr outer).map transportedSimulator`; see the module's proof chain. -/
theorem SubstitutionRelation.Implication.exists_serial_simulators
    -- Decidable equality on ι and κ is needed to count uses with `usageCount`.
    [DecidableEq ι] [DecidableEq κ]
    -- `A` is the outer interface, `B` the intermediate one and `D` the real resource's.
    {A B D : C}
    -- `innerUses + 1` and `outerUses + 1` are the numbers of steps of `inner` and `outer`.
    {innerUses outerUses : Nat}
    -- `inner` is a witness on `B` over the ι-family; `outer` is a witness on `A` over κ.
    (inner : Implication innerBoundary innerSystems B innerUses)
    (outer : Implication outerBoundary outerSystems A outerUses)
    -- `innerProtocol = π₁` (pi) builds `B` from `D`; `outerProtocol = π₂` builds `A` from `B`.
    (innerProtocol : B ⟶ D) (outerProtocol : A ⟶ B)
    -- `innerSimulator = σ₁` (sigma) acts on `B`; `outerSimulator = σ₂` acts on `A`;
    -- `transportedSimulator = σ'` is σ₁ moved to `A`, related to σ₁ only by `commutes`.
    (innerSimulator : B ⟶ B) (transportedSimulator outerSimulator : A ⟶ A)
    -- `real : Phi D` is the starting resource, `middle : Phi B` the intermediate ideal and
    -- `ideal : Phi A` the final ideal.
    (real : Phi D) (middle : Phi B) (ideal : Phi A)
    -- `innerLeft`, `innerRight` identify `inner`'s endpoints as `π₁ real` and `σ₁ middle`.
    (innerLeft : inner.targetLeft = attach innerProtocol real)
    (innerRight : inner.targetRight = attach innerSimulator middle)
    -- `outerLeft`, `outerRight` identify `outer`'s endpoints as `π₂ middle` and `σ₂ ideal`.
    (outerLeft : outer.targetLeft = attach outerProtocol middle)
    (outerRight : outer.targetRight = attach outerSimulator ideal)
    -- `commutes` is `π₂(σ₁ middle) = σ'(π₂ middle)` for this one resource only; weaker than
    -- the converter equation of
    -- `Specification.Constructs.substitutionRelaxation_serial_simulators`.
    (commutes : attach outerProtocol (attach innerSimulator middle) =
      attach transportedSimulator (attach outerProtocol middle)) :
    -- `combined` is a witness on `A` over `ι ⊕ κ` from `(π₂ ≫ π₁) real` to `(σ' ≫ σ₂) ideal`,
    -- using each `Sum.inl i` as often as `inner` uses `i` and each `Sum.inr k` as often as
    -- `outer` uses `k`.
    ∃ combined : Implication (Sum.elim innerBoundary outerBoundary)
        (Sum.rec innerSystems outerSystems) A ((innerUses + 1) + outerUses),
      combined.targetLeft = attach (outerProtocol ≫ innerProtocol) real ∧
      combined.targetRight = attach (transportedSimulator ≫ outerSimulator) ideal ∧
      (∀ i, combined.usageCount (Sum.inl i) = inner.usageCount i) ∧
      (∀ i, combined.usageCount (Sum.inr i) = outer.usageCount i) := by
  let combinedBoundary : ι ⊕ κ → C := Sum.elim innerBoundary outerBoundary
  let combinedSystems : ∀ i, Bool → Phi (combinedBoundary i) :=
    Sum.rec innerSystems outerSystems
  -- Include both source lists, then apply the source's two transformations.
  let first := (reindex (largerBoundary := combinedBoundary)
    (largerSystems := combinedSystems) Sum.inl inner).map outerProtocol
  let second := (reindex (largerBoundary := combinedBoundary)
    (largerSystems := combinedSystems) Sum.inr outer).map transportedSimulator
  -- The supplied `commutes` equation identifies the end of the mapped inner chain with the
  -- start of the mapped outer chain.
  have join : first.targetRight = second.targetLeft := by
    change attach outerProtocol inner.targetRight =
      attach transportedSimulator outer.targetLeft
    rw [innerRight, outerLeft]
    exact commutes
  refine ⟨first.append second join, ?_, ?_, ?_, ?_⟩
  · -- The real endpoint carries the serial protocol in attachment order.
    change attach outerProtocol inner.targetLeft = _
    rw [innerLeft, attach_serial]
  · -- The ideal endpoint carries the serial simulator in attachment order.
    change attach transportedSimulator outer.targetRight = _
    rw [outerRight, attach_serial]
  · intro assumption
    -- The first family occurs only in the first segment; mapping adds no uses.
    rw [usageCount_append]
    simp only [first, second, usageCount_map]
    simp only [usageCount, reindex, Sum.inl.injEq, reduceCtorEq,
      Finset.filter_false, Finset.card_empty, Nat.add_zero]
  · intro assumption
    -- The second family occurs only in the second segment, with its old counts.
    rw [usageCount_append]
    simp only [first, second, usageCount_map]
    simp only [usageCount, reindex, Sum.inr.injEq, reduceCtorEq,
      Finset.filter_false, Finset.card_empty, Nat.zero_add]

/-- Singleton CC constructions under two assumption families compose into
construction under their combined family, with the explicit serial simulator.

Banfi, Definition 2.4.3 (printed p. 28), requires
"`(s₁, s₂, ...) ⇒ π REAL ≃ σ IDEAL`"; Theorem 2.4.4 (printed p. 29) composes
these implications. MR16, Definition 1 (printed p. 11), defines construction
by "`π R ⊆ S`". The target set below is exactly the resources satisfying
the named implication to the simulated ideal. Unlike installing a generic
relaxation, stating this specification needs no additional diagonal axiom.

Derivability is only the existence of a chain; no premise is asserted, and the use counts of
`exists_serial_simulators` are dropped from the statement. -/
theorem Specification.Constructs.derivable_serial_simulators
    -- `A` is the outer interface, `B` the intermediate one and `D` the real resource's.
    {A B D : C}
    -- `innerProtocol = π₁` (pi) builds `B` from `D`; `outerProtocol = π₂` builds `A` from `B`.
    {innerProtocol : B ⟶ D} {outerProtocol : A ⟶ B}
    -- `innerSimulator = σ₁` (sigma) acts on `B`, `outerSimulator = σ₂` on `A`, and
    -- `transportedSimulator = σ'` is σ₁ moved to `A`.
    {innerSimulator : B ⟶ B} {transportedSimulator outerSimulator : A ⟶ A}
    -- `real : Phi D` is the starting resource, `middle : Phi B` and `ideal : Phi A` the ideals.
    {real : Phi D} {middle : Phi B} {ideal : Phi A}
    -- `inner`: π₁ constructs from `{real}` the resources on `B` derivable over the ι-family to
    -- `σ₁ middle`.
    (inner : Constructs innerProtocol {real}
      {resource | SubstitutionRelation.derivable innerBoundary innerSystems resource
        (attach innerSimulator middle)})
    -- `outer`: π₂ constructs from `{middle}` the resources on `A` derivable over the κ-family
    -- to `σ₂ ideal`.
    (outer : Constructs outerProtocol {middle}
      {resource | SubstitutionRelation.derivable outerBoundary outerSystems resource
        (attach outerSimulator ideal)})
    -- `commutes` is the single-resource equality `π₂(σ₁ middle) = σ'(π₂ middle)`.
    (commutes : attach outerProtocol (attach innerSimulator middle) =
      attach transportedSimulator (attach outerProtocol middle)) :
    -- `π₂ ≫ π₁` constructs from `{real}` the resources on `A` derivable over `ι ⊕ κ` to
    -- `(σ' ≫ σ₂) ideal`.
    Constructs (outerProtocol ≫ innerProtocol) {real}
      {resource | SubstitutionRelation.derivable (Sum.elim innerBoundary outerBoundary)
        (Sum.rec innerSystems outerSystems) resource
        (attach (transportedSimulator ≫ outerSimulator) ideal)} := by
  classical
  -- The two singleton constructions supply the actual finite implication witnesses.
  rw [constructs_iff] at inner outer ⊢
  obtain ⟨innerUses, innerProof, innerLeft, innerRight⟩ := inner real (Set.mem_singleton _)
  obtain ⟨outerUses, outerProof, outerLeft, outerRight⟩ := outer middle (Set.mem_singleton _)
  obtain ⟨combined, realEq, idealEq, _, _⟩ :=
    SubstitutionRelation.Implication.exists_serial_simulators innerProof outerProof
      innerProtocol outerProtocol innerSimulator transportedSimulator outerSimulator
      real middle ideal innerLeft innerRight outerLeft outerRight commutes
  -- The combined witness establishes membership in the resulting specification.
  intro resource admitted
  obtain rfl := Set.mem_singleton_iff.mp admitted
  exact ⟨(innerUses + 1) + outerUses, combined, realEq, idealEq⟩

end ConstructiveCryptography.CryptographicAlgebra

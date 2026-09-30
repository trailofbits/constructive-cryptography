import ConstructiveCryptography.Substitution.Implication

set_option autoImplicit false

/-!
# Construction from implication witnesses

A construction with a simulator is given by implication witnesses between the real systems
and the simulated ideal systems (Banfi, Definition 2.4.3). Two such constructions compose
serially: the witnesses concatenate, with the assumption families tagged by `Sum`, and the
simulators compose (Banfi, Theorem 2.4.4). The equality of the two attached middle resources
is a hypothesis.

## Main results

* `SubstitutionRelation.Implication.exists_serial_simulators`: concatenation of witnesses
* `Specification.Constructs.derivable_serial_simulators`: serial composition of
  constructions

Source: Banfi 2023, §2.4.
-/

namespace ConstructiveCryptography.CryptographicAlgebra

open CategoryTheory

universe u v w x y

variable {C : Type u} [Category.{v} C]
variable {Phi : C → Type w} [ResourceTheory C Phi]
variable {ι : Type x} {κ : Type y}
variable {innerBoundary : ι → C} {outerBoundary : κ → C}
variable {innerSystems : ∀ i, Bool → Phi (innerBoundary i)}
variable {outerSystems : ∀ i, Bool → Phi (outerBoundary i)}

/-- Serial real/ideal implications combine their named assumptions, compose
the protocol and simulators, and preserve each source family's use counts.

Banfi, Theorem 2.4.4 (printed p. 29), identifies the composite simulator as
"`σ₁σ₂`" and concludes implication under
"`s₁,₁, s₁,₂, ..., s₂,₁, s₂,₂, ...`". The explicit witness below also retains
the counts defined in Section 2.3.1 (printed p. 14). `commutes` is the exact
middle equality used in the displayed source proof. -/
theorem SubstitutionRelation.Implication.exists_serial_simulators
    [DecidableEq ι] [DecidableEq κ]
    {A B D : C} {innerUses outerUses : Nat}
    (inner : Implication innerBoundary innerSystems B innerUses)
    (outer : Implication outerBoundary outerSystems A outerUses)
    (innerProtocol : B ⟶ D) (outerProtocol : A ⟶ B)
    (innerSimulator : B ⟶ B) (transportedSimulator outerSimulator : A ⟶ A)
    (real : Phi D) (middle : Phi B) (ideal : Phi A)
    (innerLeft : inner.targetLeft = attach innerProtocol real)
    (innerRight : inner.targetRight = attach innerSimulator middle)
    (outerLeft : outer.targetLeft = attach outerProtocol middle)
    (outerRight : outer.targetRight = attach outerSimulator ideal)
    (commutes : attach outerProtocol (attach innerSimulator middle) =
      attach transportedSimulator (attach outerProtocol middle)) :
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
  -- Locality identifies the inner simulated ideal with the outer real leg.
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
relaxation, stating this specification needs no additional diagonal axiom. -/
theorem Specification.Constructs.derivable_serial_simulators
    {A B D : C} {innerProtocol : B ⟶ D} {outerProtocol : A ⟶ B}
    {innerSimulator : B ⟶ B} {transportedSimulator outerSimulator : A ⟶ A}
    {real : Phi D} {middle : Phi B} {ideal : Phi A}
    (inner : Constructs innerProtocol {real}
      {resource | SubstitutionRelation.derivable innerBoundary innerSystems resource
        (attach innerSimulator middle)})
    (outer : Constructs outerProtocol {middle}
      {resource | SubstitutionRelation.derivable outerBoundary outerSystems resource
        (attach outerSimulator ideal)})
    (commutes : attach outerProtocol (attach innerSimulator middle) =
      attach transportedSimulator (attach outerProtocol middle)) :
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

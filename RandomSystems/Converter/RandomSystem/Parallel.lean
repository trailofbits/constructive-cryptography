/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RandomSystems.Converter.RandomSystem
import RandomSystems.Converter.Parallel
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Ordered parallel composition of normalized random systems

Jost, Section 2.2.2 (printed p. 17), says: “A finite set of resources with
disjoint interface sets can be viewed as a single one.” This supports ordered
tagged routing. Liu--Maurer 2020, “Parallel Composition” (printed p. 9), says:
“One can take several independent ... resources ... and form” the displayed
product-interface resource; Definition 5 (printed p. 10) defines its
conditional law as the product of the component conditional laws.

Lanzenberger, Definition 2.13 (printed p. 14), says: “The parallel composition
of a family ... of `(X,Y)`-DDS is the `(X × [n],Y)`-DDS denoted by
`[s₁,...,sₙ]`.” The binary dependent-interface operation below is the tagged
generalization, lifted to normalized finite-support laws and their quotient.
No second carrier and no symmetry are introduced.
-/

namespace RandomSystems.Ambient

noncomputable section

open Probability (Distribution)
open scoped ENNReal

universe u v

/-! ## Ordered parallel on probabilistic and quotient random systems -/

namespace DDC

private theorem ofDDS_empty_eq_forwarding :
    DDC.ofDDS (DDS.empty : DDS Interface.empty.{u, v}) =
      RandomSystems.Ambient.DDC.forwarding
        Interface.empty.{u, v} := by
  apply DDC.ext
  intro history _
  exact PEmpty.elim history.outer.head

private noncomputable def fixRight {A B : Interface.{u, v}}
    (right : DDS B) : DDC (Interface.parallel A B) A :=
  relabel (.refl (Interface.parallel A B))
    (Interface.Equiv.parallelEmptyRight A)
    (parallel (RandomSystems.Ambient.DDC.forwarding A)
      (DDC.ofDDS right))

private theorem applySystem_fixRight
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B) :
    applySystem (fixRight right) left = DDS.parallel left right := by
  let oldConverter := parallel
    (RandomSystems.Ambient.DDC.forwarding A) (DDC.ofDDS right)
  let oldSystem := DDS.parallel left
    (DDS.empty : DDS Interface.empty.{u, v})
  have relabelledSystem :
      DDS.relabel (Interface.Equiv.parallelEmptyRight A) oldSystem = left := by
    exact DDS.relabel_parallel_empty_right left
  conv_lhs => rw [← relabelledSystem]
  calc
    applySystem (fixRight right)
        (DDS.relabel (Interface.Equiv.parallelEmptyRight A) oldSystem) =
      DDS.relabel (.refl (Interface.parallel A B))
        (applySystem oldConverter oldSystem) := by
          exact applySystem_relabel_eq (.refl (Interface.parallel A B))
            (Interface.Equiv.parallelEmptyRight A) oldConverter oldSystem
    _ = DDS.parallel left right := by
      rw [applySystem_parallel_eq, applySystem_forwarding_eq,
        applySystem_ofDDS_eq, DDS.relabel_refl]

private noncomputable def fixLeft {A B : Interface.{u, v}}
    (left : DDS A) : DDC (Interface.parallel A B) B :=
  relabel (.refl (Interface.parallel A B))
    (Interface.Equiv.parallelEmptyLeft B)
    (parallel (DDC.ofDDS left)
      (RandomSystems.Ambient.DDC.forwarding B))

private theorem applySystem_fixLeft
    {A B : Interface.{u, v}} (left : DDS A) (right : DDS B) :
    applySystem (fixLeft left) right = DDS.parallel left right := by
  let oldConverter := parallel (DDC.ofDDS left)
    (RandomSystems.Ambient.DDC.forwarding B)
  let oldSystem := DDS.parallel
    (DDS.empty : DDS Interface.empty.{u, v}) right
  have relabelledSystem :
      DDS.relabel (Interface.Equiv.parallelEmptyLeft B) oldSystem = right := by
    exact DDS.relabel_parallel_empty_left right
  conv_lhs => rw [← relabelledSystem]
  calc
    applySystem (fixLeft left)
        (DDS.relabel (Interface.Equiv.parallelEmptyLeft B) oldSystem) =
      DDS.relabel (.refl (Interface.parallel A B))
        (applySystem oldConverter oldSystem) := by
          exact applySystem_relabel_eq (.refl (Interface.parallel A B))
            (Interface.Equiv.parallelEmptyLeft B) oldConverter oldSystem
    _ = DDS.parallel left right := by
      rw [applySystem_parallel_eq, applySystem_ofDDS_eq,
        applySystem_forwarding_eq, DDS.relabel_refl]

end DDC

namespace PDS

private theorem prod_single_right {A B : Type*} (law : Distribution A)
    (value : B) :
    Distribution.prod law (Finsupp.single value 1) =
      Distribution.fTransform (fun a => (a, value)) law := by
  ext pair
  obtain ⟨a, b⟩ := pair
  rw [Distribution.prod_apply]
  by_cases equal : b = value
  · subst b
    rw [Distribution.fTransform_injective_apply law (fun a => (a, value))
      (by intro x y h; exact congrArg Prod.fst h)]
    simp
  · rw [Distribution.fTransform_apply_of_forall_ne]
    · simp [equal]
    · intro a'
      exact fun h => equal (congrArg Prod.snd h).symm

private theorem prod_single_left {A B : Type*} (value : A)
    (law : Distribution B) :
    Distribution.prod (Finsupp.single value 1) law =
      Distribution.fTransform (fun b => (value, b)) law := by
  ext pair
  obtain ⟨a, b⟩ := pair
  rw [Distribution.prod_apply]
  by_cases equal : a = value
  · subst a
    rw [Distribution.fTransform_injective_apply law (fun b => (value, b))
      (by intro x y h; exact congrArg Prod.snd h)]
    simp
  · rw [Distribution.fTransform_apply_of_forall_ne]
    · simp [equal]
    · intro b'
      exact fun h => equal (congrArg Prod.fst h).symm

/-- Independent ordered parallel of normalized system laws.

Liu--Maurer 2020, “Parallel Composition” (printed p. 9): “One can take several
independent ... resources ... and form” the displayed product-interface
resource. Definition 5 (printed p. 10) defines its conditional law as the
product of the component conditional laws. The declaration below is the
normalized finite-support deterministic-mixture specialization. -/
noncomputable def parallel {A B : Interface.{u, v}}
    (left : PDS A) (right : PDS B) : PDS (Interface.parallel A B) :=
  ⟨Distribution.fTransform
      (fun systems => DDS.parallel systems.1 systems.2)
      (Distribution.prod left.1 right.1),
    Distribution.fTransform_isProbDist _
      (Distribution.prod_isProbDist left.1 right.1 left.2 right.2)⟩

@[simp]
theorem parallel_ofDDS_eq {A B : Interface.{u, v}}
    (left : DDS A) (right : DDS B) :
    parallel (ofDDS left) (ofDDS right) = ofDDS (DDS.parallel left right) := by
  -- Compare the normalized laws underlying the two point PDSs.
  apply Subtype.ext
  change Distribution.fTransform _
      (Distribution.prod (Finsupp.single left 1)
        (Finsupp.single right 1)) = _
  rw [prod_single_right, Distribution.fTransform_fTransform]
  -- Both laws put unit mass on the same deterministic parallel DDS.
  ext candidate
  simp [ofDDS, Distribution.fTransform]

/-- DDC attachment commutes with independent ordered parallel.

Jost, Proposition 2.2.3 (printed p. 18), gives the one-sided equation
`π[R,S] = [πR,S]` for disjoint interface sets. Applying it once to each
component gives the two-sided equation below. -/
theorem apply_parallel_eq
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (left : PDS B₁) (right : PDS B₂) :
    apply (DDC.parallel leftConverter rightConverter) (parallel left right) =
      parallel (apply leftConverter left) (apply rightConverter right) := by
  -- Compare the underlying normalized finite-support laws.
  apply Subtype.ext
  -- Rewrite attachment and parallel as deterministic distribution transformations.
  change Distribution.fTransform
      (applySystem (DDC.parallel leftConverter rightConverter))
      (Distribution.fTransform
        (fun systems => DDS.parallel systems.1 systems.2)
        (Distribution.prod left.1 right.1)) = _
  rw [Distribution.fTransform_fTransform,
    show (parallel (apply leftConverter left)
      (apply rightConverter right)).1 =
        Distribution.fTransform
          (fun systems => DDS.parallel systems.1 systems.2)
          (Distribution.prod
            (apply leftConverter left).1
            (apply rightConverter right).1) from rfl,
    show (apply leftConverter left).1 =
        Distribution.fTransform (applySystem leftConverter) left.1 from rfl,
    show (apply rightConverter right).1 =
        Distribution.fTransform (applySystem rightConverter) right.1 from rfl,
    ← Distribution.fTransform_prod,
    Distribution.fTransform_fTransform]
  -- Pointwise, the deterministic DDC parallel-attachment law applies.
  apply Distribution.fTransform_congr
  intro systems _
  exact DDC.applySystem_parallel_eq leftConverter rightConverter
    systems.1 systems.2

private theorem parallel_eq_sum_right
    {A B : Interface.{u, v}} (left : PDS A) (right : PDS B) :
    (parallel left right).1 =
      ∑ system ∈ right.1.support,
        right.1 system • (apply (DDC.fixRight system) left).1 := by
  change Distribution.fTransform
      (fun systems => DDS.parallel systems.1 systems.2)
      (Distribution.prod left.1 right.1) = _
  rw [Distribution.prod_eq_sum_right,
    Distribution.fTransform_sum]
  apply Finset.sum_congr rfl
  intro system _
  rw [Distribution.fTransform_smul,
    Distribution.fTransform_fTransform]
  apply congrArg (fun law => right.1 system • law)
  apply congrArg (fun transform => Distribution.fTransform transform left.1)
  funext leftSystem
  exact (DDC.applySystem_fixRight leftSystem system).symm

theorem equivalent_parallel_left
    {A B : Interface.{u, v}} {left left' : PDS A}
    (equivalent : PDS.equivalent left left') (right : PDS B) :
    PDS.equivalent (parallel left right) (parallel left' right) := by
  -- Fix an arbitrary finite observation of the joint system.
  intro environment rounds
  -- Expand the right PDS as a finite mixture of deterministic contexts.
  unfold PDS.trLaw RandomSystems.Ambient.trLaw
  rw [parallel_eq_sum_right left right,
    parallel_eq_sum_right left' right,
    Distribution.fTransform_sum, Distribution.fTransform_sum]
  apply Finset.sum_congr rfl
  intro system _
  rw [Distribution.fTransform_smul, Distribution.fTransform_smul]
  apply congrArg (fun law => right.1 system • law)
  -- DDC non-expansion transports the left equivalence through each context.
  exact equivalent_apply (DDC.fixRight system) equivalent environment rounds

private theorem prod_eq_sum_left {A B : Type*}
    (left : Distribution A) (right : Distribution B) :
    Distribution.prod left right =
      ∑ a ∈ left.support,
        left a • Distribution.fTransform (fun b => (a, b)) right := by
  calc
    Distribution.prod left right =
        Distribution.fTransform Prod.swap (Distribution.prod right left) :=
      (Distribution.fTransform_swap_prod right left).symm
    _ = Distribution.fTransform Prod.swap
          (∑ a ∈ left.support,
            left a • Distribution.fTransform (fun b => (b, a)) right) := by
      rw [Distribution.prod_eq_sum_right]
    _ = ∑ a ∈ left.support,
          Distribution.fTransform Prod.swap
            (left a • Distribution.fTransform (fun b => (b, a)) right) :=
      Distribution.fTransform_sum _ _ _
    _ = ∑ a ∈ left.support,
          left a • Distribution.fTransform (fun b => (a, b)) right := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Distribution.fTransform_smul,
        Distribution.fTransform_fTransform]
      congr 2

private theorem parallel_eq_sum_left
    {A B : Interface.{u, v}} (left : PDS A) (right : PDS B) :
    (parallel left right).1 =
      ∑ system ∈ left.1.support,
        left.1 system • (apply (DDC.fixLeft system) right).1 := by
  change Distribution.fTransform
      (fun systems => DDS.parallel systems.1 systems.2)
      (Distribution.prod left.1 right.1) = _
  rw [prod_eq_sum_left, Distribution.fTransform_sum]
  apply Finset.sum_congr rfl
  intro system _
  rw [Distribution.fTransform_smul,
    Distribution.fTransform_fTransform]
  apply congrArg (fun law => left.1 system • law)
  apply congrArg (fun transform => Distribution.fTransform transform right.1)
  funext rightSystem
  exact (DDC.applySystem_fixLeft system rightSystem).symm

theorem equivalent_parallel_right
    {A B : Interface.{u, v}} (left : PDS A) {right right' : PDS B}
    (equivalent : PDS.equivalent right right') :
    PDS.equivalent (parallel left right) (parallel left right') := by
  -- Fix an arbitrary finite observation of the joint system.
  intro environment rounds
  -- Expand the left PDS as a finite mixture of deterministic contexts.
  unfold PDS.trLaw RandomSystems.Ambient.trLaw
  rw [parallel_eq_sum_left left right,
    parallel_eq_sum_left left right',
    Distribution.fTransform_sum, Distribution.fTransform_sum]
  apply Finset.sum_congr rfl
  intro system _
  rw [Distribution.fTransform_smul, Distribution.fTransform_smul]
  apply congrArg (fun law => left.1 system • law)
  -- DDC non-expansion transports the right equivalence through each context.
  exact equivalent_apply (DDC.fixLeft system) equivalent environment rounds

theorem equivalent_parallel
    {A B : Interface.{u, v}}
    {left left' : PDS A} {right right' : PDS B}
    (leftEquivalent : PDS.equivalent left left')
    (rightEquivalent : PDS.equivalent right right') :
    PDS.equivalent (parallel left right) (parallel left' right') :=
  equivalent_trans
    (equivalent_parallel_left leftEquivalent right)
    (equivalent_parallel_right left' rightEquivalent)

/-- Holding the right resource fixed, ordered parallel composition does not
increase ambient observation advantage. -/
theorem advantage_parallel_left_le
    {A B : Interface.{u, v}} (left left' : PDS A) (right : PDS B) :
    advantage (parallel left right) (parallel left' right) ≤
      advantage left left' := by
  refine iSup_le fun environment => iSup_le fun rounds => ?_
  -- Expand the fixed right PDS as a finite mixture of deterministic contexts.
  unfold PDS.trLaw RandomSystems.Ambient.trLaw
  rw [parallel_eq_sum_right left right,
    parallel_eq_sum_right left' right,
    Distribution.fTransform_sum, Distribution.fTransform_sum]
  simp_rw [Distribution.fTransform_smul]
  let observed := fun system : DDS B =>
    Distribution.fTransform
      (fun deterministicSystem => transcript deterministicSystem environment rounds)
      (apply (DDC.fixRight system) left).1
  let observed' := fun system : DDS B =>
    Distribution.fTransform
      (fun deterministicSystem => transcript deterministicSystem environment rounds)
      (apply (DDC.fixRight system) left').1
  have mixtureBound : Probability.statDist
      (∑ system ∈ right.1.support, right.1 system • observed system)
      (∑ system ∈ right.1.support, right.1 system • observed' system) ≤
      ∑ system ∈ right.1.support,
        right.1 system * Probability.statDist (observed system) (observed' system) :=
    Probability.statDist_sum_le right.1.support (fun system => right.1 system)
      observed observed' (fun system _ => right.2.1 system)
  calc
    -- Statistical distance is convex under the common mixture weights.
    ENNReal.ofReal (Probability.statDist
        (∑ system ∈ right.1.support, right.1 system • observed system)
        (∑ system ∈ right.1.support, right.1 system • observed' system)) ≤
      ENNReal.ofReal (∑ system ∈ right.1.support,
        right.1 system * Probability.statDist (observed system) (observed' system)) :=
      ENNReal.ofReal_le_ofReal mixtureBound
    _ = ∑ system ∈ right.1.support,
        ENNReal.ofReal (right.1 system) *
          ENNReal.ofReal (Probability.statDist (observed system) (observed' system)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro system supported
        exact ENNReal.ofReal_mul (right.2.1 system)
      · intro system _
        exact mul_nonneg (right.2.1 system)
          (Probability.statDist_nonneg _ _)
    _ ≤ ∑ system ∈ right.1.support,
        ENNReal.ofReal (right.1 system) * advantage left left' := by
      apply Finset.sum_le_sum
      intro system supported
      apply mul_le_mul_right
      -- Each deterministic right resource is one ordinary converter context.
      calc
        ENNReal.ofReal
            (Probability.statDist (observed system) (observed' system)) ≤
          advantage (apply (DDC.fixRight system) left)
            (apply (DDC.fixRight system) left') :=
          le_iSup_of_le environment (le_iSup_of_le rounds le_rfl)
        _ ≤ advantage left left' :=
          advantage_apply_le (DDC.fixRight system) left left'
    _ = advantage left left' := by
      -- The normalized right PDS has total weight one.
      rw [← Finset.sum_mul]
      have weightSum : ∑ system ∈ right.1.support, right.1 system = 1 := by
        rw [← Distribution.weight_eq_sum_of_support_subset right.1
          (fun _ supported => supported)]
        exact right.2.2
      have nonnegative : ∀ system ∈ right.1.support,
          0 ≤ right.1 system := fun system _ => right.2.1 system
      rw [← ENNReal.ofReal_sum_of_nonneg nonnegative, weightSum]
      simp

/-- Holding the left resource fixed, ordered parallel composition does not
increase ambient observation advantage. -/
theorem advantage_parallel_right_le
    {A B : Interface.{u, v}} (left : PDS A) (right right' : PDS B) :
    advantage (parallel left right) (parallel left right') ≤
      advantage right right' := by
  refine iSup_le fun environment => iSup_le fun rounds => ?_
  -- Expand the fixed left PDS as a finite mixture of deterministic contexts.
  unfold PDS.trLaw RandomSystems.Ambient.trLaw
  rw [parallel_eq_sum_left left right,
    parallel_eq_sum_left left right',
    Distribution.fTransform_sum, Distribution.fTransform_sum]
  simp_rw [Distribution.fTransform_smul]
  let observed := fun system : DDS A =>
    Distribution.fTransform
      (fun deterministicSystem => transcript deterministicSystem environment rounds)
      (apply (DDC.fixLeft system) right).1
  let observed' := fun system : DDS A =>
    Distribution.fTransform
      (fun deterministicSystem => transcript deterministicSystem environment rounds)
      (apply (DDC.fixLeft system) right').1
  have mixtureBound : Probability.statDist
      (∑ system ∈ left.1.support, left.1 system • observed system)
      (∑ system ∈ left.1.support, left.1 system • observed' system) ≤
      ∑ system ∈ left.1.support,
        left.1 system * Probability.statDist (observed system) (observed' system) :=
    Probability.statDist_sum_le left.1.support (fun system => left.1 system)
      observed observed' (fun system _ => left.2.1 system)
  calc
    -- Statistical distance is convex under the common mixture weights.
    ENNReal.ofReal (Probability.statDist
        (∑ system ∈ left.1.support, left.1 system • observed system)
        (∑ system ∈ left.1.support, left.1 system • observed' system)) ≤
      ENNReal.ofReal (∑ system ∈ left.1.support,
        left.1 system * Probability.statDist (observed system) (observed' system)) :=
      ENNReal.ofReal_le_ofReal mixtureBound
    _ = ∑ system ∈ left.1.support,
        ENNReal.ofReal (left.1 system) *
          ENNReal.ofReal (Probability.statDist (observed system) (observed' system)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      · apply Finset.sum_congr rfl
        intro system supported
        exact ENNReal.ofReal_mul (left.2.1 system)
      · intro system _
        exact mul_nonneg (left.2.1 system)
          (Probability.statDist_nonneg _ _)
    _ ≤ ∑ system ∈ left.1.support,
        ENNReal.ofReal (left.1 system) * advantage right right' := by
      apply Finset.sum_le_sum
      intro system supported
      apply mul_le_mul_right
      -- Each deterministic left resource is one ordinary converter context.
      calc
        ENNReal.ofReal
            (Probability.statDist (observed system) (observed' system)) ≤
          advantage (apply (DDC.fixLeft system) right)
            (apply (DDC.fixLeft system) right') :=
          le_iSup_of_le environment (le_iSup_of_le rounds le_rfl)
        _ ≤ advantage right right' :=
          advantage_apply_le (DDC.fixLeft system) right right'
    _ = advantage right right' := by
      -- The normalized left PDS has total weight one.
      rw [← Finset.sum_mul]
      have weightSum : ∑ system ∈ left.1.support, left.1 system = 1 := by
        rw [← Distribution.weight_eq_sum_of_support_subset left.1
          (fun _ supported => supported)]
        exact left.2.2
      have nonnegative : ∀ system ∈ left.1.support,
          0 ≤ left.1 system := fun system _ => left.2.1 system
      rw [← ENNReal.ofReal_sum_of_nonneg nonnegative, weightSum]
      simp

/-- Independent ordered parallel composition is jointly non-expanding. -/
theorem advantage_parallel_le
    {A B : Interface.{u, v}} (left left' : PDS A)
    (right right' : PDS B) :
    advantage (parallel left right) (parallel left' right') ≤
      advantage left left' + advantage right right' := by
  calc
    -- Insert the mixed pair and apply the triangle inequality.
    advantage (parallel left right) (parallel left' right') ≤
        advantage (parallel left right) (parallel left' right) +
          advantage (parallel left' right) (parallel left' right') :=
      advantage_triangle _ _ _
    _ ≤ advantage left left' + advantage right right' :=
      -- Bound the two one-sided changes independently.
      add_le_add (advantage_parallel_left_le left left' right)
        (advantage_parallel_right_le left' right right')

end PDS
namespace RandomSystem

/-- Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with
disjoint interface sets can be viewed as a single one.” This is the quotient
lift of the independent ordered PDS parallel operation. -/
noncomputable def parallel {A B : Interface.{u, v}} :
    RandomSystem A → RandomSystem B →
      RandomSystem (Interface.parallel A B) :=
  Quotient.lift₂
    (fun left right => ofPDS (PDS.parallel left right))
    (fun _ _ _ _ leftEquivalent rightEquivalent =>
      ofPDS_eq_iff.mpr
        (PDS.equivalent_parallel leftEquivalent rightEquivalent))

@[simp]
theorem parallel_ofPDS_eq {A B : Interface.{u, v}}
    (left : PDS A) (right : PDS B) :
    parallel (ofPDS left) (ofPDS right) =
      ofPDS (PDS.parallel left right) := rfl

/-- Jost, Proposition 2.2.3 (printed p. 18): “if S is another resource such
that the interface sets of R and S are disjoint”, converter attachment to one
component commutes with adjoining the other. This is the two-component
quotient lift. -/
theorem apply_parallel_eq
    {A₁ B₁ A₂ B₂ : Interface.{u, v}}
    (leftConverter : DDC A₁ B₁) (rightConverter : DDC A₂ B₂)
    (left : RandomSystem B₁) (right : RandomSystem B₂) :
    apply (DDC.parallel leftConverter rightConverter)
        (parallel left right) =
      parallel (apply leftConverter left) (apply rightConverter right) := by
  -- Choose normalized PDS representatives of both quotient resources.
  induction left using Quotient.ind with
  | _ leftPresentation =>
      induction right using Quotient.ind with
      | _ rightPresentation =>
          -- Apply the PDS parallel-attachment equation.
          change ofPDS
              (PDS.apply (DDC.parallel leftConverter rightConverter)
                (PDS.parallel leftPresentation rightPresentation)) =
            ofPDS (PDS.parallel
              (PDS.apply leftConverter leftPresentation)
              (PDS.apply rightConverter rightPresentation))
          rw [PDS.apply_parallel_eq]

/-- Ordered parallel composition is jointly non-expanding on observational
random systems. -/
theorem edist_parallel_le
    {A B : Interface.{u, v}}
    (left left' : RandomSystem A) (right right' : RandomSystem B) :
    edist (parallel left right) (parallel left' right') ≤
      edist left left' + edist right right' := by
  -- Choose normalized PDS representatives of all four quotient resources.
  induction left using Quotient.ind with
  | _ leftPresentation =>
      induction left' using Quotient.ind with
      | _ leftPresentation' =>
          induction right using Quotient.ind with
          | _ rightPresentation =>
              induction right' using Quotient.ind with
              | _ rightPresentation' =>
                  -- Apply joint non-expansion of the PDS parallel operation.
                  exact PDS.advantage_parallel_le
                    leftPresentation leftPresentation'
                    rightPresentation rightPresentation'

end RandomSystem

/-! ## Ordered quotient parallel laws -/
namespace PDS

private theorem prod_single_right_local {A B : Type*}
    (law : Distribution A) (value : B) :
    Distribution.prod law (Finsupp.single value 1) =
      Distribution.fTransform (fun a => (a, value)) law := by
  ext pair
  obtain ⟨a, b⟩ := pair
  rw [Distribution.prod_apply]
  by_cases equal : b = value
  · subst b
    rw [Distribution.fTransform_injective_apply law (fun a => (a, value))
      (by intro x y h; exact congrArg Prod.fst h)]
    simp
  · rw [Distribution.fTransform_apply_of_forall_ne]
    · simp [equal]
    · intro a'
      exact fun h => equal (congrArg Prod.snd h).symm

private theorem prod_single_left_local {A B : Type*}
    (value : A) (law : Distribution B) :
    Distribution.prod (Finsupp.single value 1) law =
      Distribution.fTransform (fun b => (value, b)) law := by
  ext pair
  obtain ⟨a, b⟩ := pair
  rw [Distribution.prod_apply]
  by_cases equal : a = value
  · subst a
    rw [Distribution.fTransform_injective_apply law (fun b => (value, b))
      (by intro x y h; exact congrArg Prod.snd h)]
    simp
  · rw [Distribution.fTransform_apply_of_forall_ne]
    · simp [equal]
    · intro b'
      exact fun h => equal (congrArg Prod.fst h).symm

/-- Reassociation of independent ordered laws is exactly attachment of the
canonical dependent interface equivalence. -/
theorem apply_parallel_assoc_eq
    {A B C : Interface.{u, v}}
    (first : PDS A) (second : PDS B) (third : PDS C) :
    apply (Interface.Equiv.parallelAssoc A B C).toDDC
        (parallel (parallel first second) third) =
      parallel first (parallel second third) := by
  -- Compare the normalized laws underlying the two bracketings.
  apply Subtype.ext
  change Distribution.fTransform
      (applySystem (Interface.Equiv.parallelAssoc A B C).toDDC)
      (Distribution.fTransform
        (fun systems => DDS.parallel systems.1 systems.2)
        (Distribution.prod
          (Distribution.fTransform
            (fun systems => DDS.parallel systems.1 systems.2)
            (Distribution.prod first.1 second.1))
          third.1)) =
    Distribution.fTransform
      (fun systems => DDS.parallel systems.1 systems.2)
      (Distribution.prod first.1
        (Distribution.fTransform
          (fun systems => DDS.parallel systems.1 systems.2)
          (Distribution.prod second.1 third.1)))
  rw [Distribution.fTransform_prod_left,
    Distribution.fTransform_fTransform,
    ← Distribution.fTransform_assoc_prod,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_prod_right,
    Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  -- It remains to reassociate each deterministic triple.
  apply Distribution.fTransform_congr
  intro systems _
  change applySystem (Interface.Equiv.parallelAssoc A B C).toDDC
      (DDS.parallel (DDS.parallel systems.1 systems.2.1) systems.2.2) =
    DDS.parallel systems.1 (DDS.parallel systems.2.1 systems.2.2)
  rw [DDC.applySystem_toDDC_eq]
  -- The canonical interface relabeling reassociates DDS parallel.
  exact DDS.relabel_parallel_assoc systems.1 systems.2.1 systems.2.2

/-- The deterministic empty law is the left unit after the canonical
dependent relabeling. -/
theorem apply_parallel_empty_left_eq
    {A : Interface.{u, v}} (system : PDS A) :
    apply (Interface.Equiv.parallelEmptyLeft A).toDDC
        (parallel (ofDDS (DDS.empty : DDS Interface.empty.{u, v})) system) =
      system := by
  -- Compare the normalized law with the original PDS law.
  apply Subtype.ext
  change Distribution.fTransform
      (applySystem (Interface.Equiv.parallelEmptyLeft A).toDDC)
      (Distribution.fTransform
        (fun systems => DDS.parallel systems.1 systems.2)
        (Distribution.prod (Finsupp.single DDS.empty 1) system.1)) = system.1
  rw [prod_single_left_local, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  calc
    Distribution.fTransform _ system.1 =
        Distribution.fTransform id system.1 := by
      -- Pointwise, the empty DDS is the left unit after relabeling.
      apply Distribution.fTransform_congr
      intro deterministicSystem _
      change applySystem (Interface.Equiv.parallelEmptyLeft A).toDDC
          (DDS.parallel DDS.empty deterministicSystem) =
        id deterministicSystem
      rw [DDC.applySystem_toDDC_eq]
      exact DDS.relabel_parallel_empty_left deterministicSystem
    _ = system.1 := Distribution.fTransform_id system.1

/-- The deterministic empty law is the right unit after the canonical
dependent relabeling. -/
theorem apply_parallel_empty_right_eq
    {A : Interface.{u, v}} (system : PDS A) :
    apply (Interface.Equiv.parallelEmptyRight A).toDDC
        (parallel system (ofDDS (DDS.empty : DDS Interface.empty.{u, v}))) =
      system := by
  -- Compare the normalized law with the original PDS law.
  apply Subtype.ext
  change Distribution.fTransform
      (applySystem (Interface.Equiv.parallelEmptyRight A).toDDC)
      (Distribution.fTransform
        (fun systems => DDS.parallel systems.1 systems.2)
        (Distribution.prod system.1 (Finsupp.single DDS.empty 1))) = system.1
  rw [prod_single_right_local, Distribution.fTransform_fTransform,
    Distribution.fTransform_fTransform]
  calc
    Distribution.fTransform _ system.1 =
        Distribution.fTransform id system.1 := by
      -- Pointwise, the empty DDS is the right unit after relabeling.
      apply Distribution.fTransform_congr
      intro deterministicSystem _
      change applySystem (Interface.Equiv.parallelEmptyRight A).toDDC
          (DDS.parallel deterministicSystem DDS.empty) =
        id deterministicSystem
      rw [DDC.applySystem_toDDC_eq]
      exact DDS.relabel_parallel_empty_right deterministicSystem
    _ = system.1 := Distribution.fTransform_id system.1

end PDS

namespace RandomSystem

/-- Jost, Section 2.2.2 (printed p. 17), defines “the (canonical) dummy
resource, where every party has an empty interface set.” -/
noncomputable def empty : RandomSystem Interface.empty.{u, v} :=
  ofPDS (PDS.ofDDS DDS.empty)

/-- Reassociation of ordered parallel on the observational quotient. This is
the quotient lift of the chosen tagged-sum/product representation. -/
theorem apply_parallel_assoc_eq
    {A B C : Interface.{u, v}}
    (first : RandomSystem A) (second : RandomSystem B)
    (third : RandomSystem C) :
    apply (Interface.Equiv.parallelAssoc A B C).toDDC
        (parallel (parallel first second) third) =
      parallel first (parallel second third) := by
  -- Choose normalized PDS representatives of the three resources.
  induction first using Quotient.ind with
  | _ firstPresentation =>
      induction second using Quotient.ind with
      | _ secondPresentation =>
          induction third using Quotient.ind with
          | _ thirdPresentation =>
              -- Apply the PDS reassociation equation.
              change ofPDS
                  (PDS.apply (Interface.Equiv.parallelAssoc A B C).toDDC
                    (PDS.parallel
                      (PDS.parallel firstPresentation secondPresentation)
                      thirdPresentation)) =
                ofPDS (PDS.parallel firstPresentation
                  (PDS.parallel secondPresentation thirdPresentation))
              rw [PDS.apply_parallel_assoc_eq]

/-- The chosen ordered tagged representation also has a left unit after the
canonical relabeling. Jost explicitly displays only the right-unit equation;
this left-unit equality is proved for the present representation. -/
theorem apply_parallel_empty_left_eq
    {A : Interface.{u, v}} (system : RandomSystem A) :
    apply (Interface.Equiv.parallelEmptyLeft A).toDDC
        (parallel empty system) = system := by
  -- Choose a normalized PDS representative.
  induction system using Quotient.ind with
  | _ presentation =>
      -- Apply the PDS left-unit equation.
      change ofPDS
          (PDS.apply (Interface.Equiv.parallelEmptyLeft A).toDDC
            (PDS.parallel (PDS.ofDDS DDS.empty) presentation)) =
        ofPDS presentation
      rw [PDS.apply_parallel_empty_left_eq]

/-- Jost, Section 2.2.2 (printed p. 17), states: “By definition, we thus have
that `[R, □] = R` for all resources `R`.”  This is the corresponding right-unit
law on the observational quotient. -/
theorem apply_parallel_empty_right_eq
    {A : Interface.{u, v}} (system : RandomSystem A) :
    apply (Interface.Equiv.parallelEmptyRight A).toDDC
        (parallel system empty) = system := by
  -- Choose a normalized PDS representative.
  induction system using Quotient.ind with
  | _ presentation =>
      -- Apply the PDS right-unit equation.
      change ofPDS
          (PDS.apply (Interface.Equiv.parallelEmptyRight A).toDDC
            (PDS.parallel presentation (PDS.ofDDS DDS.empty))) =
        ofPDS presentation
      rw [PDS.apply_parallel_empty_right_eq]

end RandomSystem

end

end RandomSystems.Ambient

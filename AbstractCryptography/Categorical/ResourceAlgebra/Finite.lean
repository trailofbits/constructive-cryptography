/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import AbstractCryptography.Categorical.ResourceAlgebra

set_option autoImplicit false

/-!
# Finite ordered parallel composition

Finite parallel composition is derived by recursion from the ordered binary
operation of `ResourceAlgebra`.  It introduces no additional parallel
structure and no symmetry assumption.  Repeated copies of the same interface
remain separately routed because their resulting interface is an iterated
tensor, not the original interface.

Jost, Section 2.2.2 (printed p. 17): “A finite set of resources with disjoint
interface sets can be viewed as a single one.”  Theorem 2.2.5 (printed p. 19)
states the parallel construction property, and Section 4.2.2 (printed p. 51)
says that it “is just associativity.”
-/

namespace AbstractCryptography.Categorical.ResourceAlgebra.Finite

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v w

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {Phi : Opposite C ⥤ Type w}
variable [ResourceAlgebra C Phi]

/-- Right-associated interface of a finite ordered family of interfaces. -/
def interface : (n : Nat) → (Fin n → C) → C
  | 0, _ => 𝟙_ C
  | n + 1, interfaces =>
      interfaces 0 ⊗ interface n (fun i => interfaces i.succ)

/-- Ordered parallel composition of a heterogeneous indexed resource family. -/
def resources : (n : Nat) → (interfaces : Fin n → C) →
    ((i : Fin n) → Resource Phi (interfaces i)) →
      Resource Phi (interface n interfaces)
  | 0, _, _ => dummy (C := C) (Phi := Phi)
  | n + 1, interfaces, family =>
      parallel (Phi := Phi) (family 0)
        (resources n (fun i => interfaces i.succ) (fun i => family i.succ))

/-- Ordered parallel composition of a heterogeneous indexed converter family. -/
def converters : (n : Nat) →
    (outer inner : Fin n → C) →
    ((i : Fin n) → (outer i ⟶ inner i)) →
      (interface n outer ⟶ interface n inner)
  | 0, _, _, _ => 𝟙 _
  | n + 1, outer, inner, family =>
      family 0 ⊗ₘ converters n
        (fun i => outer i.succ) (fun i => inner i.succ)
        (fun i => family i.succ)

/-- Ordered parallel composition of a heterogeneous indexed specification
family. -/
def specifications : (n : Nat) → (interfaces : Fin n → C) →
    ((i : Fin n) → Specification Phi (interfaces i)) →
      Specification Phi (interface n interfaces)
  | 0, _, _ =>
      AbstractCryptography.Categorical.ResourceAlgebra.Specification.dummy
        (C := C) (Phi := Phi)
  | n + 1, interfaces, family =>
      AbstractCryptography.Categorical.ResourceAlgebra.Specification.parallel
        (Phi := Phi) (family 0)
        (specifications n (fun i => interfaces i.succ)
          (fun i => family i.succ))

/-- Sum of a finite indexed family of error bounds. -/
noncomputable def errorSum : (n : Nat) → (Fin n → ENNReal) → ENNReal
  | 0, _ => 0
  | n + 1, errors => errors 0 + errorSum n (fun i => errors i.succ)

/-- The ordered parallel of componentwise identity converters is the identity
converter at the assembled boundary. -/
@[simp]
theorem converters_identity (n : Nat) (interfaces : Fin n → C) :
    converters n interfaces interfaces (fun i => 𝟙 (interfaces i)) =
      𝟙 (interface n interfaces) := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      -- Separate the first identity converter from the remaining family.
      change (𝟙 (interfaces 0)) ⊗ₘ
          converters n (fun i => interfaces i.succ)
            (fun i => interfaces i.succ)
            (fun i => 𝟙 (interfaces i.succ)) = _
      -- Apply the induction hypothesis, then tensorial preservation of identity.
      rw [inductionHypothesis (fun i => interfaces i.succ)]
      exact converter_parallel_identity _ _

/-- Ordered parallel preserves pointwise serial converter composition. -/
theorem converters_serial (n : Nat)
    (outer middle inner : Fin n → C)
    (first : (i : Fin n) → (outer i ⟶ middle i))
    (second : (i : Fin n) → (middle i ⟶ inner i)) :
    converters n outer inner (fun i => first i ≫ second i) =
      converters n outer middle first ≫
        converters n middle inner second := by
  induction n with
  | zero =>
      change (𝟙 (𝟙_ C)) = (𝟙 (𝟙_ C)) ≫ (𝟙 (𝟙_ C))
      simp
  | succ n inductionHypothesis =>
      -- Separate the first pair of serial converters from the remaining family.
      change (first 0 ≫ second 0) ⊗ₘ
          converters n (fun i => outer i.succ) (fun i => inner i.succ)
            (fun i => first i.succ ≫ second i.succ) =
        (first 0 ⊗ₘ converters n
            (fun i => outer i.succ) (fun i => middle i.succ)
            (fun i => first i.succ)) ≫
          (second 0 ⊗ₘ converters n
            (fun i => middle i.succ) (fun i => inner i.succ)
            (fun i => second i.succ))
      -- Use the induction hypothesis and tensor bifunctoriality.
      rw [inductionHypothesis (fun i => outer i.succ)
        (fun i => middle i.succ) (fun i => inner i.succ)
        (fun i => first i.succ) (fun i => second i.succ)]
      exact converter_parallel_serial _ _ _ _

/-- Attachment by an indexed converter family is pointwise before finite
parallel composition.

Jost, Proposition 2.2.3 (printed p. 18): “if `S` is another resource such that
the interface sets of `R` and `S` are disjoint,” attachment to `R` leaves `S`
unchanged. -/
theorem attach_resources (n : Nat) (outer inner : Fin n → C)
    (family : (i : Fin n) → (outer i ⟶ inner i))
    (systems : (i : Fin n) → Resource Phi (inner i)) :
    attach (Phi := Phi) (converters n outer inner family)
        (resources n inner systems) =
      resources n outer
        (fun i => attach (Phi := Phi) (family i) (systems i)) := by
  induction n with
  | zero =>
      -- The empty converter family is identity on the dummy resource.
      change attach (Phi := Phi) (𝟙 _) _ = _
      exact attach_identity _
  | succ n inductionHypothesis =>
      -- Separate the first converter/resource pair from the remaining family.
      change attach (Phi := Phi)
          (family 0 ⊗ₘ converters n
            (fun i => outer i.succ) (fun i => inner i.succ)
            (fun i => family i.succ))
          (parallel (Phi := Phi) (systems 0)
            (resources n (fun i => inner i.succ)
              (fun i => systems i.succ))) = _
      -- Binary attachment locality and the induction hypothesis give the result.
      rw [attach_parallel,
        inductionHypothesis (fun i => outer i.succ)
          (fun i => inner i.succ) (fun i => family i.succ)
          (fun i => systems i.succ)]
      rfl

/-- Pointwise admitted resources belong to the ordered parallel
specification. -/
theorem resources_mem_specifications (n : Nat) (interfaces : Fin n → C)
    (systems : (i : Fin n) → Resource Phi (interfaces i))
    (family : (i : Fin n) → Specification Phi (interfaces i))
    (admitted : ∀ i, systems i ∈ family i) :
    resources n interfaces systems ∈ specifications n interfaces family := by
  induction n with
  | zero =>
      -- The empty resource is the unique member of the dummy specification.
      exact Set.mem_singleton _
  | succ n inductionHypothesis =>
      -- Parallel membership is witnessed by the first component and the tail.
      exact ⟨systems 0, admitted 0,
        resources n (fun i => interfaces i.succ) (fun i => systems i.succ),
        inductionHypothesis (fun i => interfaces i.succ)
          (fun i => systems i.succ) (fun i => family i.succ)
          (fun i => admitted i.succ), rfl⟩

/-- Pointwise exact constructions compose in finite ordered parallel.

Jost, Theorem 2.2.5 (printed p. 19):
“R —π→ S =⇒ [R,T] —π→ [S,T].” -/
theorem constructs (n : Nat) (outer inner : Fin n → C)
    (family : (i : Fin n) → (outer i ⟶ inner i))
    (source : (i : Fin n) → Specification Phi (inner i))
    (target : (i : Fin n) → Specification Phi (outer i))
    (construction : ∀ i,
      AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
        (Phi := Phi)
        (family i) (source i) (target i)) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs
      (Phi := Phi)
      (converters n outer inner family)
      (specifications n inner source) (specifications n outer target) := by
  induction n with
  | zero =>
      -- The empty family is identity construction of the dummy specification.
      exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructs_identity _
  | succ n inductionHypothesis =>
      -- Compose the first construction in parallel with the induction result.
      exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.Constructs.parallel
        (construction 0)
        (inductionHypothesis (fun i => outer i.succ)
          (fun i => inner i.succ) (fun i => family i.succ)
          (fun i => source i.succ) (fun i => target i.succ)
          (fun i => construction i.succ))

/-- Pointwise approximate constructions compose in finite ordered parallel,
with the sum of their error bounds. -/
theorem constructs_within (n : Nat) (outer inner : Fin n → C)
    (family : (i : Fin n) → (outer i ⟶ inner i))
    (source : (i : Fin n) → Specification Phi (inner i))
    (target : (i : Fin n) → Specification Phi (outer i))
    (errors : Fin n → ENNReal)
    (construction : ∀ i,
      AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
        (Phi := Phi)
        (family i) (source i) (target i) (errors i)) :
    AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin
      (Phi := Phi)
      (converters n outer inner family)
      (specifications n inner source) (specifications n outer target)
      (errorSum n errors) := by
  induction n with
  | zero =>
      -- The empty family is zero-error identity construction.
      exact
        AbstractCryptography.Categorical.ResourceAlgebra.Specification.constructsWithin_identity _
  | succ n inductionHypothesis =>
      -- Binary approximate parallel adds the first and remaining errors.
      exact AbstractCryptography.Categorical.ResourceAlgebra.Specification.ConstructsWithin.parallel
        (construction 0)
        (inductionHypothesis (fun i => outer i.succ)
          (fun i => inner i.succ) (fun i => family i.succ)
          (fun i => source i.succ) (fun i => target i.succ)
          (fun i => errors i.succ) (fun i => construction i.succ))

/-- Finite ordered parallel is non-expanding with the componentwise sum of
distances. -/
theorem distance_resources_le (n : Nat) (interfaces : Fin n → C)
    (left right : (i : Fin n) → Resource Phi (interfaces i)) :
    distance (Phi := Phi) (resources n interfaces left)
        (resources n interfaces right) ≤
      errorSum n (fun i => distance (Phi := Phi) (left i) (right i)) := by
  induction n with
  | zero =>
      -- Both empty families are the same dummy resource.
      exact le_of_eq (distance_self _)
  | succ n inductionHypothesis =>
      -- Binary non-expansion separates the first and remaining components.
      exact (distance_parallel_le
        (Phi := Phi) (left 0) (right 0)
        (resources n (fun i => interfaces i.succ) (fun i => left i.succ))
        (resources n (fun i => interfaces i.succ) (fun i => right i.succ))).trans
          (add_le_add le_rfl
            (inductionHypothesis (fun i => interfaces i.succ)
              (fun i => left i.succ)
              (fun i => right i.succ)))

end AbstractCryptography.Categorical.ResourceAlgebra.Finite

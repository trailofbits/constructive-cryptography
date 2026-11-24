module

public import ConstructiveCryptography.Tactics.Basic
public import ConstructiveCryptography.CryptographicAlgebra.Star
public import ConstructiveCryptography.Specification
public import ConstructiveCryptography.Specification.Action
public import ConstructiveCryptography.Specification.Parallel
public import ConstructiveCryptography.Specification.Star.Metric
public import ConstructiveCryptography.Specification.Game
public meta import ConstructiveCryptography.Tactics.Basic

/-!
# Constructive Cryptography proof automation

The commands assemble constructions from explicit component equalities, distance bounds,
and simulators. `cc_normalize` applies attachment, parallel, and coherence laws in any
`CryptographicAlgebra`; the interface instance supplies their random-systems interpretation.

Whiskering acts on one side of a parallel resource. Interchange orders attachments on
opposite ports with the right-port converter outside; same-port order remains explicit.
The `•` lemmas below expose the existing abstract laws to the simplifier's term index.

## References

1. U. Maurer and R. Renner. *From Indifferentiability to Constructive Cryptography (and Back)*.
   TCC 2016-B, §§3–4.
2. D. Jost. *On Generalizations of Composable Security*. ETH thesis 26723, 2020, §2.2.
-/

section SmulNormalization

-- `C` carries interfaces and converters; `Φ A` carries resources on interface `A : C`.
-- In every rule, `f : A ⟶ B` presents `A` by using a resource on `B`.

open CategoryTheory MonoidalCategory ConstructiveCryptography

/-- Identity attachment leaves a resource unchanged in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.smul_identity
    {C : Type*} [Category* C] {Φ : C → Type*} [ResourceTheory C Φ] {A : C} (R : Φ A) :
    (𝟙 A) • R = R :=
  attach_identity R

/-- Serial attachment associates in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.smul_serial
    {C : Type*} [Category* C] {Φ : C → Type*} [ResourceTheory C Φ] {A B D : C}
    (f : A ⟶ B) (g : B ⟶ D) (R : Φ D) :
    (f ≫ g) • R = f • (g • R) :=
  attach_serial f g R

/-- Parallel attachment distributes over parallel resources in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.smul_parallel
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A A' B B' : C}
    (f : A' ⟶ A) (g : B' ⟶ B) (R : Φ A) (S : Φ B) :
    (f ⊗ₘ g) • parallel R S = parallel (f • R) (g • S) :=
  attach_parallel f g R S

/-- The associator regroups three resources. This spelling lets `cc_normalize` match `•`
directly when the resource carrier is abstract. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.associator_hom_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A B D : C} (L : Φ A) (M : Φ B) (R : Φ D) :
    (α_ A B D).hom • parallel L (parallel M R) = parallel (parallel L M) R :=
  associator_hom_attach L M R

/-- The inverse associator regroups three resources in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.associator_inv_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A B D : C} (L : Φ A) (M : Φ B) (R : Φ D) :
    (α_ A B D).inv • parallel (parallel L M) R = parallel L (parallel M R) :=
  parallel_assoc L M R

/-- The forward left unitor adjoins `dummy` on the left in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.leftUnitor_hom_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A : C} (R : Φ A) :
    (λ_ A).hom • R = parallel (dummy (C := C)) R :=
  leftUnitor_hom_attach R

/-- The inverse left unitor drops a left `dummy` resource in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.leftUnitor_inv_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A : C} (R : Φ A) :
    (λ_ A).inv • parallel (dummy (C := C)) R = R :=
  parallel_dummy_left R

/-- The forward right unitor adjoins `dummy` on the right in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.rightUnitor_hom_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A : C} (R : Φ A) :
    (ρ_ A).hom • R = parallel R (dummy (C := C)) :=
  rightUnitor_hom_attach R

/-- The inverse right unitor drops a right `dummy` resource in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.rightUnitor_inv_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A : C} (R : Φ A) :
    (ρ_ A).inv • parallel R (dummy (C := C)) = R :=
  parallel_dummy_right R

/-- Left-whiskering acts on the right component of a parallel resource in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.whiskerLeft_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A B B' : C}
    (β : B' ⟶ B) (R : Φ A) (S : Φ B) :
    (A ◁ β) • parallel R S = parallel R (β • S) :=
  attach_whiskerLeft β R S

/-- Right-whiskering acts on the left component of a parallel resource in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.whiskerRight_smul
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A A' B : C}
    (α : A' ⟶ A) (R : Φ A) (S : Φ B) :
    (α ▷ B) • parallel R S = parallel (α • R) S :=
  attach_whiskerRight α R S

/-- Right-whiskering moves inside left-whiskering in public `•` notation. -/
@[cc_normalization] public lemma ConstructiveCryptography.CryptographicAlgebra.whisker_smul_comm
    {C : Type*} [Category* C] [MonoidalCategory C] {Φ : C → Type*}
    [ResourceTheory C Φ] [CryptographicAlgebra C Φ] {A A' B B' : C}
    (α : A' ⟶ A) (β : B' ⟶ B) (R : Φ (A ⊗ B)) :
    (α ▷ B') • ((A ◁ β) • R) = (A' ◁ β) • ((α ▷ B) • R) :=
  whisker_attach_comm α β R

end SmulNormalization

@[expose] public meta section

namespace ConstructiveCryptography

attribute [cc_normalization]
  CryptographicAlgebra.attach_identity
  CryptographicAlgebra.attach_serial
  CryptographicAlgebra.converter_parallel_identity
  CryptographicAlgebra.converter_parallel_serial
  CryptographicAlgebra.attach_parallel
  CryptographicAlgebra.attach_whiskerLeft
  CryptographicAlgebra.attach_whiskerRight
  CryptographicAlgebra.whisker_attach_comm
  CryptographicAlgebra.parallel_assoc
  CryptographicAlgebra.associator_hom_attach
  CryptographicAlgebra.parallel_dummy_left
  CryptographicAlgebra.leftUnitor_hom_attach
  CryptographicAlgebra.parallel_dummy_right
  CryptographicAlgebra.rightUnitor_hom_attach
  CryptographicAlgebra.Specification.parallel_singleton
  CryptographicAlgebra.Specification.star_idem
  CategoryTheory.Category.id_comp
  CategoryTheory.Category.comp_id
  CategoryTheory.Category.assoc
  CategoryTheory.MonoidalCategory.comp_whiskerRight
  CategoryTheory.MonoidalCategory.whiskerLeft_comp
  CategoryTheory.MonoidalCategory.whiskerLeft_id
  CategoryTheory.MonoidalCategory.id_whiskerRight
  zero_add
  add_zero
  Set.mem_singleton_iff

end ConstructiveCryptography

/-- Expose the canonical equality, distance, or pointwise obligation for a
singleton or scalar-error construction. -/
syntax (name := ccConstruct) "cc_construct" : tactic

macro_rules
  | `(tactic| cc_construct) =>
      `(tactic|
        first
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr
          | apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr
          | fail "cc_construct expected a typed singleton or scalar-error construction goal")

/-- Close a supported construction goal from one explicit mathematical
witness. -/
syntax (name := ccConstructUsing) "cc_construct" " using " term : tactic

macro_rules
  | `(tactic| cc_construct using $fact) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr $fact
               | exact $fact)
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr $fact
               | exact ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr $fact
               | exact $fact)
          | fail "cc_construct could not use the supplied equality, distance bound, or pointwise proof")

/-- Close a typed attachment or construction consequence of one explicit
converter equality. -/
syntax (name := ccTransport) "cc_transport" " using " term : tactic

macro_rules
  | `(tactic| cc_transport using $same) =>
      `(tactic|
        first
          | exact $same
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.attach_eq_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.attach_eq_of_converter_eq
                $same _
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                $same
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
                $same
          | fail "cc_transport expected attachment equality or construction equivalence induced by the supplied converter equality")

/-- Replace the converter in a supplied construction using one explicit
equality. -/
syntax (name := ccReplaceConverterInConstruction)
  "cc_transport " term " using " term : tactic

macro_rules
  | `(tactic| cc_transport $construction using $same) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule "replace converter in exact construction, left-to-right" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in exact construction, right-to-left" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_iff_of_converter_eq
                     $same).mpr $construction)
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule "replace converter in approximate construction, left-to-right" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mp $construction
               | cc_exact_rule "replace converter in approximate construction, right-to-left" =>
                   (ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff_of_converter_eq
                     $same).mpr $construction)
          | fail "cc_transport could not replace the converter in the supplied construction using the supplied equality")

/-- Apply Maurer--Renner's explicit simulator proof step. -/
syntax (name := ccSimulator) "cc_simulator " term : tactic

macro_rules
  | `(tactic| cc_simulator $simulator) =>
      `(tactic|
        first
          | refine ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator
              $simulator ?_ ?_
          | fail "cc_simulator expected a typed singleton construction into the scalar relaxation of a star specification")

/-- Pull an explicitly compatible relaxation through the outer leg of a
serial construction. -/
syntax (name := ccRelax) "cc_relax" " using " term "," term " with " term : tactic

macro_rules
  | `(tactic| cc_relax using $inner, $outer with $compatibility) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_serial
              $compatibility $inner $outer
          | fail "cc_relax could not apply the typed serial relaxation theorem to the supplied constructions and compatibility proof")

/-- Apply the selected fibre-distance triangle inequality through an explicit
intermediate resource. -/
syntax (name := ccTriangle) "cc_triangle" " via " term : tactic

macro_rules
  | `(tactic| cc_triangle via $intermediate) =>
      `(tactic|
        first
          | refine (ConstructiveCryptography.CryptographicAlgebra.distance_triangle
              _ $intermediate _).trans (add_le_add ?_ ?_)
          | fail "cc_triangle expected a typed resource-distance goal with an additive bound")

/-- Select converter-attachment or ordered-parallel non-expansion. -/
syntax (name := ccNonexpand) "cc_nonexpand" : tactic

macro_rules
  | `(tactic| cc_nonexpand) =>
      `(tactic|
        first
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _
          | exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le _ _ _ _
          | fail "cc_nonexpand expected a converter-attachment or ordered-parallel distance goal")

/-- Compose two constructions in execution order. -/
syntax (name := ccCompose) "cc_compose " term "," term : tactic

macro_rules
  | `(tactic| cc_compose $inner, $outer) =>
      `(tactic|
        first
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
                _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                         $inner $outer))
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                         $inner $outer)))
          | (change ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
                _ _ _ _
             first
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial" =>
                   ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
                     $inner $outer
               | cc_exact_rule
                   "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
                   (by
                     simpa only [CategoryTheory.Category.assoc, add_assoc] using
                       (ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
                         $inner $outer)))
          | fail "cc_compose expected two composable typed construction proofs")

/-- Compose two simulator-target constructions using one explicit
composition-order commutation equality. -/
syntax (name := ccComposeSimulators)
  "cc_compose_simulators " term "," term " using " term : tactic

macro_rules
  | `(tactic| cc_compose_simulators $inner, $outer using $commutes) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators
                $inner $outer $commutes
          | fail "cc_compose_simulators expected two typed simulator-target constructions and an explicit composition-order commutation equality")

/-- Compose two construction proofs in ordered parallel. -/
syntax (name := ccParallel) "cc_parallel " term "," term : tactic

macro_rules
  | `(tactic| cc_parallel $left, $right) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel
                $left $right
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel
                $left $right
          | fail "cc_parallel expected two typed constructions for ordered parallel composition")

/-- Extend a construction by a fixed right specification context. -/
syntax (name := ccContextLeft)
  "cc_context_left " term " using " term : tactic

macro_rules
  | `(tactic| cc_context_left $context using $construction) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context
                $construction $context
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context
                (ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $construction $context
          | fail "cc_context_left expected a typed construction and a fixed right specification context")

/-- Extend a construction by a fixed left specification context. -/
syntax (name := ccContextRight)
  "cc_context_right " term " using " term : tactic

macro_rules
  | `(tactic| cc_context_right $context using $construction) =>
      `(tactic|
        first
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context
                $context $construction
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context" =>
              ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context
                (ConstructiveCryptography.CryptographicAlgebra.Specification.epsilonRelaxation_parallelCompatible _)
                $context $construction
          | fail "cc_context_right expected a typed construction and a fixed left specification context")

open Lean in
/-- Build the proof term underlying `cc_chain` by folding named constructions
from left to right. -/
meta partial def mkCCConstructionChainTerm
    {m : Type → Type} [Monad m] [MonadQuotation m]
    (constructions : TSyntaxArray `term) (kind : Nat) : m Term := do
  if h : 0 < constructions.size then
    let rec go (index : Nat) (accumulator : Term) : m Term := do
      if hindex : index < constructions.size then
        let next := constructions[index]
        let combined ← match kind with
          | 0 =>
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial
                  $accumulator $next)
          | 1 =>
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation
                  $accumulator $next)
          | _ =>
              ``(ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial
                  $accumulator $next)
        go (index + 1) combined
      else
        pure accumulator
    go 1 constructions[0]
  else
    ``(by fail "cc_chain requires at least two named construction proofs")

/-- Compose an explicit list of at least two named typed constructions. -/
syntax (name := ccChain) "cc_chain" "[" term,* "]" : tactic

macro_rules
  | `(tactic| cc_chain [$constructions:term,*]) => do
      let constructionArray := constructions.getElems
      if constructionArray.size < 2 then
        Lean.Macro.throwError
          "cc_chain requires at least two named construction proofs"
      let exactChain ← mkCCConstructionChainTerm constructionArray 0
      let scalarChain ← mkCCConstructionChainTerm constructionArray 1
      let approximateChain ← mkCCConstructionChainTerm constructionArray 2
      `(tactic|
        first
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial" =>
              $exactChain
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation" =>
              $scalarChain
          | cc_exact_rule "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial" =>
              $approximateChain
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial; CategoryTheory.Category.assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc] using $exactChain)
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $scalarChain)
          | cc_exact_rule
              "ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial; CategoryTheory.Category.assoc; add_assoc" =>
              (by
                simpa only [CategoryTheory.Category.assoc, add_assoc] using $approximateChain)
          | fail "cc_chain could not compose the supplied typed construction proofs")


open Lean Elab Tactic

/-- Report the categorical CC rules whose conclusions match the current goal.
The fixed table performs no environment search. -/
elab "cc?" : tactic => withMainContext do
  let exactSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_iff.mpr)
  let scalarSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_singleton_epsilonRelaxation_iff.mpr)
  let scalarGeneral ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_epsilonRelaxation_iff.mpr)
  let approximateSingleton ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_singleton_iff.mpr)
  let approximateGeneral ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructsWithin_iff.mpr)
  let simulator ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.constructs_of_simulator)
  let relaxation ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_serial)
  let exactSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial)
  let scalarSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_epsilonRelaxation)
  let approximateSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.serial)
  let simulatorSerial ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.serial_simulators)
  let exactParallel ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.parallel)
  let approximateParallel ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.parallel)
  let exactLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.left_context)
  let exactRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.right_context)
  let approximateLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.left_context)
  let approximateRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin.right_context)
  let relaxedLeftContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_left_context)
  let relaxedRightContext ← `(tactic|
    apply ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs.relax_right_context)
  let distanceTriangle ← `(tactic|
    refine (ConstructiveCryptography.CryptographicAlgebra.distance_triangle
      _ ?_ _).trans (add_le_add ?_ ?_))
  let attachmentNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_attach_le _ _ _)
  let parallelLeftNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le _ _ _)
  let parallelRightNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le _ _ _)
  let parallelJointNonexpansion ← `(tactic|
    exact ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le _ _ _ _)
  let candidates := #[
    ("cc_construct — constructs_singleton_iff", exactSingleton),
    ("cc_construct — constructs_singleton_epsilonRelaxation_iff", scalarSingleton),
    ("cc_construct — constructs_epsilonRelaxation_iff", scalarGeneral),
    ("cc_construct — constructsWithin_singleton_iff", approximateSingleton),
    ("cc_construct — constructsWithin_iff", approximateGeneral),
    ("cc_simulator simulator — constructs_of_simulator", simulator),
    ("cc_relax using inner, outer with compatibility — Constructs.relax_serial", relaxation),
    ("cc_compose inner, outer — Constructs.serial", exactSerial),
    ("cc_compose inner, outer — Constructs.serial_epsilonRelaxation", scalarSerial),
    ("cc_compose inner, outer — ConstructsWithin.serial", approximateSerial),
    ("cc_compose_simulators inner, outer using commutation — Constructs.serial_simulators", simulatorSerial),
    ("cc_parallel left, right — Constructs.parallel", exactParallel),
    ("cc_parallel left, right — ConstructsWithin.parallel", approximateParallel),
    ("cc_context_left context using construction — Constructs.left_context", exactLeftContext),
    ("cc_context_right context using construction — Constructs.right_context", exactRightContext),
    ("cc_context_left context using construction — ConstructsWithin.left_context", approximateLeftContext),
    ("cc_context_right context using construction — ConstructsWithin.right_context", approximateRightContext),
    ("cc_context_left context using construction — Constructs.relax_left_context", relaxedLeftContext),
    ("cc_context_right context using construction — Constructs.relax_right_context", relaxedRightContext),
    ("cc_triangle via intermediate — distance_triangle", distanceTriangle),
    ("cc_nonexpand — distance_attach_le", attachmentNonexpansion),
    ("cc_nonexpand — distance_parallel_left_le", parallelLeftNonexpansion),
    ("cc_nonexpand — distance_parallel_right_le", parallelRightNonexpansion),
    ("cc_nonexpand — distance_parallel_le", parallelJointNonexpansion)
  ]
  let mut applicable : Array String := #[]
  for (label, candidate) in candidates do
    if ← ccRuleAppliesWithoutChangingGoal candidate then
      applicable := applicable.push label
  if applicable.isEmpty then
    logInfo "No categorical CC rule in the bounded diagnostic table matches this goal."
  else
    logInfo m!"Categorical CC rule candidates (goal unchanged):\n  {
      "\n  ".intercalate applicable.toList}"

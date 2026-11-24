module

public import ConstructiveCryptography.Notation
public import Probability.Kernel
public import RandomSystems.Typed.Context
public import RandomSystems.Typed.QueryRouting

/-!
# Parallel projections, shared randomness, and naturality

Focused tests for `TypedConverter.projectLeft`, `TypedConverter.projectRight`, and their
`Interface` instance laws on unequal interfaces with unequal query allowances:

* Projecting `R ∥ S` returns the selected component (`projectLeft_smul_parallel`,
  `projectRight_smul_parallel`, and `cc_normalize`), preserving only that component's domain and
  query allowance without assuming commutativity.
* Projecting `sample k ← P; R k ∥ S k` preserves the single retained draw `k ← P` and yields
  the marginal `sample k ← P; R k` or `sample k ← P; S k` without resampling, verified on
  two-query transcripts.
* Both projections are natural with respect to nontrivial converters on the retained component
  (and on both components simultaneously), at both the converter level and when attached to a
  joint system with retained shared randomness.
-/

@[expose] public section

namespace SystemAlgebra.Tests.ParallelProjections

open CategoryTheory CategoryTheory.MonoidalCategory Probability
open scoped SystemAlgebra

/-- Inside left interface: two Boolean ports, Boolean queries and replies, total budget `5`. -/
abbrev leftInside : Interface :=
  Interface.queryBudget Bool (fun _ => Bool) (fun _ => Bool) 5

/-- Outside left interface: one unit port, Boolean queries and replies, total budget `3`.
Strictly different ports and query allowance from `leftInside` and from both right interfaces. -/
abbrev leftOutside : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 3

/-- Inside right interface: one unit port, unit queries, `Fin 3` replies, total budget `2`. -/
abbrev rightInside : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Fin 3) 2

/-- Outside right interface: one unit port, unit queries, Boolean replies, total budget `1`. -/
abbrev rightOutside : Interface :=
  Interface.queryBudget Unit (fun _ => Unit) (fun _ => Bool) 1

/-- Left component for shared key `k`: on port `i` and query `x`, returns `xor i k`. -/
noncomputable def leftBranch
    -- `k` is the shared Boolean key retained across all queries.
    (k : Bool) : TypedSystem leftInside :=
  TypedSystem.ofFunction (A := leftInside) (fun (i : Bool) (_ : Bool) => xor i k)

/-- Right component for shared key `k`: returns `1 : Fin 3` when `k = true` and `0` otherwise. -/
noncomputable def rightBranch
    -- `k` is the shared Boolean key retained across all queries.
    (k : Bool) : TypedSystem rightInside :=
  TypedSystem.ofFunction (A := rightInside) (fun (_ : Unit) (_ : Unit) =>
    if k then (1 : Fin 3) else 0)

/-- Joint parallel system sharing one uniform Boolean draw `k` across both unequal components:
`sample k ← 𝒰[Bool]; leftBranch k ∥ rightBranch k`. -/
noncomputable def jointShared : TypedSystem (leftInside ⊗ rightInside) :=
  sample k ← 𝒰[Bool].1; leftBranch k ∥ rightBranch k

/-- Nontrivial converter on the left component: routes query `x` on port `()` to port `x` with
query `x`, and negates the Boolean reply; changes both port structure and budget (`3 ≤ 5`). -/
noncomputable def leftConverter : TypedConverter leftOutside leftInside :=
  TypedConverter.routing
    (fun u => ⟨u.2, u.2⟩)
    (fun _ r => !r.2)
    (fun _ h => Interface.queryBudget_domain_map _ (show 3 ≤ 5 by omega) h)

/-- Nontrivial converter on the right component: forwards the unit query and tests whether the
`Fin 3` reply equals `1`; changes both reply alphabet and budget (`1 ≤ 2`). -/
noncomputable def rightConverter : TypedConverter rightOutside rightInside :=
  TypedConverter.routing
    (fun _ => ⟨(), ()⟩)
    (fun _ r => r.2 == (1 : Fin 3))
    (fun _ h => Interface.queryBudget_domain_map _ (show 1 ≤ 2 by omega) h)

/-! ## Unit converters and their categorical instance -/

-- The categorical unitors use the systems-level converters in both directions.
example : (ρ_ leftInside).hom = TypedConverter.rightUnitorHom leftInside := rfl
example : (ρ_ leftInside).inv = TypedConverter.rightUnitorInv leftInside := rfl
example : (λ_ rightInside).hom = TypedConverter.leftUnitorHom rightInside := rfl
example : (λ_ rightInside).inv = TypedConverter.leftUnitorInv rightInside := rfl

-- Cancellation crosses the typed-converter and categorical composition notations.
example : TypedConverter.rightUnitorInv leftInside ≫ TypedConverter.rightUnitorHom leftInside =
    𝟙 leftInside := TypedConverter.rightUnitorInv_comp_hom leftInside

example : TypedConverter.leftUnitorHom rightInside ≫ TypedConverter.leftUnitorInv rightInside =
    𝟙 (Interface.unit ⊗ rightInside) := TypedConverter.leftUnitorHom_comp_inv rightInside

/-! ## Projecting parallel resources on unequal interfaces -/

/-- Left projection of `R ∥ S` returns `R` via the instance law. -/
example (R : TypedSystem leftInside) (S : TypedSystem rightInside) :
    TypedConverter.projectLeft leftInside rightInside • (R ∥ S) = R :=
  Interface.projectLeft_smul_parallel R S

/-- Right projection of `R ∥ S` returns `S` via the instance law. -/
example (R : TypedSystem leftInside) (S : TypedSystem rightInside) :
    TypedConverter.projectRight leftInside rightInside • (R ∥ S) = S :=
  Interface.projectRight_smul_parallel R S

/-- `cc_normalize` fires on binary projections without extra lemmas. -/
example (R : TypedSystem leftInside) (S : TypedSystem rightInside) :
    TypedConverter.projectLeft leftInside rightInside • (R ∥ S) = R := by
  cc_normalize

example (R : TypedSystem leftInside) (S : TypedSystem rightInside) :
    TypedConverter.projectRight leftInside rightInside • (R ∥ S) = S := by
  cc_normalize

/-- The categorical factorization of `projectLeft` and `projectRight` through the unitors and
`discard` holds definitionally. -/
example :
    (TypedConverter.projectLeft leftInside rightInside :
      leftInside ⟶ leftInside ⊗ rightInside) =
      (ρ_ leftInside).inv ≫ (𝟙 leftInside ⊗ₘ TypedConverter.discard rightInside) :=
  Interface.projectLeft_eq leftInside rightInside

example :
    (TypedConverter.projectRight leftInside rightInside :
      rightInside ⟶ leftInside ⊗ rightInside) =
      (λ_ rightInside).inv ≫ (TypedConverter.discard leftInside ⊗ₘ 𝟙 rightInside) :=
  Interface.projectRight_eq leftInside rightInside

/-- The retained interface keeps its own query allowance (`5` on the left, `2` on the right),
independent of the discarded component's allowance. -/
example : leftInside.domain (List.replicate 5 ⟨false, false⟩) := by
  refine ⟨List.cons_ne_nil _ _, ?_⟩
  simp only [List.length_replicate, le_refl]

example : ¬ rightInside.domain (List.replicate 3 ⟨(), ()⟩) := by
  intro h
  have hb := h.2
  simp only [List.length_replicate] at hb
  omega

/-! ## Projecting shared randomness without resampling -/

/-- Projecting the left component of `jointShared` returns the left marginal on the same draw. -/
example :
    TypedConverter.projectLeft leftInside rightInside • jointShared =
      sample k ← 𝒰[Bool].1; leftBranch k :=
  Interface.projectLeft_smul_sample_parallel 𝒰[Bool].1 leftBranch rightBranch

/-- Projecting the right component of `jointShared` returns the right marginal on the same draw. -/
example :
    TypedConverter.projectRight leftInside rightInside • jointShared =
      sample k ← 𝒰[Bool].1; rightBranch k :=
  Interface.projectRight_smul_sample_parallel 𝒰[Bool].1 leftBranch rightBranch

/-- `cc_normalize` hoists the projection under the retained draw and reduces the body. -/
example :
    TypedConverter.projectLeft leftInside rightInside • jointShared =
      sample k ← 𝒰[Bool].1; leftBranch k := by
  unfold jointShared
  cc_normalize

example :
    TypedConverter.projectRight leftInside rightInside • jointShared =
      sample k ← 𝒰[Bool].1; rightBranch k := by
  unfold jointShared
  cc_normalize

/-- Two repeated queries to the left projection of `jointShared` return `(true, true)` with
probability `1 / 2` (the probability of the single draw `k = true`), not `(1 / 2)² = 1 / 4`. -/
lemma projectLeft_jointShared_consistent_mass :
    (TypedConverter.projectLeft leftInside rightInside • jointShared).1
      [(⟨false, false⟩, ⟨false, true⟩), (⟨false, false⟩, ⟨false, true⟩)] = (1 / 2 : ℝ) := by
  rw [show TypedConverter.projectLeft leftInside rightInside • jointShared =
      TypedSystem.sample 𝒰[Bool].1 leftBranch from
    Interface.projectLeft_smul_sample_parallel 𝒰[Bool].1 leftBranch rightBranch]
  -- Evaluate the retained-draw mixture of deterministic functions on the two-query transcript.
  unfold leftBranch
  rw [TypedSystem.sample_ofFunction_mass_eq]
  have hlen :
      ([⟨false, false⟩, ⟨false, false⟩] : List (Σ i : Bool, leftInside.X i)).length ≤ 5 := by
    norm_num only [List.length_cons, List.length_nil]
  simp only [List.map_cons, List.map_nil, hlen, ne_eq, reduceCtorEq, not_false_eq_true,
    or_true, true_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    Sigma.mk.inj_iff, heq_eq_eq, Bool.false_xor, and_self]
  -- Only `k = true` produces reply `true` on both queries, contributing its single draw weight.
  rw [Distribution.mass_eq_sum]
  simp only [Fintype.sum_bool, Distribution.ProbDist.uniform, Distribution.uniform_apply,
    Fintype.card_bool, Nat.cast_ofNat, Bool.true_eq_false, ite_true, ite_false, add_zero]

/-- Conflicting replies `(true, false)` to the same query have probability `0` under the left
projection of `jointShared`, confirming that `k` is retained and never resampled. -/
lemma projectLeft_jointShared_conflicting_mass :
    (TypedConverter.projectLeft leftInside rightInside • jointShared).1
      [(⟨false, false⟩, ⟨false, true⟩), (⟨false, false⟩, ⟨false, false⟩)] = 0 := by
  rw [show TypedConverter.projectLeft leftInside rightInside • jointShared =
      TypedSystem.sample 𝒰[Bool].1 leftBranch from
    Interface.projectLeft_smul_sample_parallel 𝒰[Bool].1 leftBranch rightBranch]
  unfold leftBranch
  rw [TypedSystem.sample_ofFunction_mass_eq]
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and, Bool.false_xor]
  -- No single Boolean draw `k` satisfies both `true = k` and `false = k`.
  rw [Distribution.mass_eq_sum]
  simp only [Fintype.sum_bool, Bool.true_eq_false, Bool.false_eq_true, and_false, false_and,
    ite_false, add_zero]

/-! ## Naturality with nontrivial converters -/

/-- Left projection commutes with the nontrivial converter `leftConverter` on the retained side. -/
example :
    (TypedConverter.projectLeft leftOutside rightInside :
      leftOutside ⟶ leftOutside ⊗ rightInside) ≫ (leftConverter ⊗ₘ 𝟙 rightInside) =
      leftConverter ≫ (TypedConverter.projectLeft leftInside rightInside :
        leftInside ⟶ leftInside ⊗ rightInside) :=
  Interface.projectLeft_comp_whiskerRight leftConverter

/-- Right projection commutes with the nontrivial converter `rightConverter` on the retained
side. -/
example :
    (TypedConverter.projectRight leftInside rightOutside :
      rightOutside ⟶ leftInside ⊗ rightOutside) ≫ (𝟙 leftInside ⊗ₘ rightConverter) =
      rightConverter ≫ (TypedConverter.projectRight leftInside rightInside :
        rightInside ⟶ leftInside ⊗ rightInside) :=
  Interface.projectRight_comp_whiskerLeft rightConverter

/-- Two-sided naturality absorbs a nontrivial converter on the hidden component as well. -/
example :
    (TypedConverter.projectLeft leftOutside rightOutside :
      leftOutside ⟶ leftOutside ⊗ rightOutside) ≫ (leftConverter ⊗ₘ rightConverter) =
      leftConverter ≫ (TypedConverter.projectLeft leftInside rightInside :
        leftInside ⟶ leftInside ⊗ rightInside) :=
  Interface.projectLeft_comp_tensor leftConverter rightConverter

example :
    (TypedConverter.projectRight leftOutside rightOutside :
      rightOutside ⟶ leftOutside ⊗ rightOutside) ≫ (leftConverter ⊗ₘ rightConverter) =
      rightConverter ≫ (TypedConverter.projectRight leftInside rightInside :
        rightInside ⟶ leftInside ⊗ rightInside) :=
  Interface.projectRight_comp_tensor leftConverter rightConverter

/-- Attachment-level naturality on the correlated shared-sample system `jointShared`: applying
`leftConverter ⊗ₘ 𝟙 rightInside` before `projectLeft` equals applying `leftConverter` after it. -/
lemma projectLeft_naturality_on_jointShared :
    TypedConverter.projectLeft leftOutside rightInside •
      ((leftConverter ⊗ₘ 𝟙 rightInside) • jointShared) =
      leftConverter • (TypedConverter.projectLeft leftInside rightInside • jointShared) :=
  Interface.projectLeft_smul_tensor_smul leftConverter (𝟙 rightInside) jointShared

/-- Evaluating `leftConverter` on `leftBranch k` shows it transforms the retained system
nontrivially: query `x` returns `!(xor x k)` on the narrower interface `leftOutside`. -/
lemma leftConverter_smul_leftBranch (k : Bool) :
    leftConverter • leftBranch k =
      TypedSystem.ofFunction (A := leftOutside) (fun (_ : Unit) (x : Bool) => !(xor x k)) := by
  unfold leftConverter leftBranch
  exact TypedConverter.routing_smul_ofFunction _ _ _ _

/-- Combining naturality, shared-draw projection, and the converter's functional law yields
the transformed marginal system directly on `leftOutside`. -/
example :
    TypedConverter.projectLeft leftOutside rightInside •
      ((leftConverter ⊗ₘ 𝟙 rightInside) • jointShared) =
      sample k ← 𝒰[Bool].1;
        TypedSystem.ofFunction (A := leftOutside) (fun (_ : Unit) (x : Bool) => !(xor x k)) := by
  rw [projectLeft_naturality_on_jointShared]
  unfold jointShared
  rw [Interface.projectLeft_smul_sample_parallel, TypedConverter.smul_sample]
  simp only [leftConverter_smul_leftBranch]

/-! ## Axiom checks -/

#print axioms SystemAlgebra.TypedConverter.leftUnitorHom_comp_inv
#print axioms SystemAlgebra.TypedConverter.leftUnitorInv_comp_hom
#print axioms SystemAlgebra.TypedConverter.rightUnitorHom_comp_inv
#print axioms SystemAlgebra.TypedConverter.rightUnitorInv_comp_hom
#print axioms SystemAlgebra.TypedConverter.comp_leftUnitor_inv
#print axioms SystemAlgebra.TypedConverter.comp_rightUnitor_inv

#print axioms SystemAlgebra.TypedConverter.eq_discard
#print axioms SystemAlgebra.TypedConverter.comp_discard
#print axioms SystemAlgebra.TypedConverter.projectLeft
#print axioms SystemAlgebra.TypedConverter.projectRight
#print axioms SystemAlgebra.TypedConverter.projectLeft_smul_parallel
#print axioms SystemAlgebra.TypedConverter.projectRight_smul_parallel
#print axioms SystemAlgebra.TypedConverter.projectLeft_smul_sample_parallel
#print axioms SystemAlgebra.TypedConverter.projectRight_smul_sample_parallel
#print axioms SystemAlgebra.TypedConverter.projectLeft_comp_parallel
#print axioms SystemAlgebra.TypedConverter.projectRight_comp_parallel
#print axioms SystemAlgebra.TypedConverter.projectLeft_comp_parallel_id
#print axioms SystemAlgebra.TypedConverter.projectRight_comp_parallel_id
#print axioms SystemAlgebra.Interface.projectLeft_smul_parallel
#print axioms SystemAlgebra.Interface.projectRight_smul_parallel
#print axioms SystemAlgebra.Interface.projectLeft_smul_sample_parallel
#print axioms SystemAlgebra.Interface.projectRight_smul_sample_parallel
#print axioms SystemAlgebra.Interface.projectLeft_comp_whiskerRight
#print axioms SystemAlgebra.Interface.projectRight_comp_whiskerLeft

end SystemAlgebra.Tests.ParallelProjections

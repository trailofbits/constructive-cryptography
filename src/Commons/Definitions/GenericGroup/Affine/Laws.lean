module

public import Commons.Definitions.GenericGroup.Affine
public import Commons.Definitions.AbstractModel.RegisterDDC.Laws
public import Probability.AffineEvaluation

/-!
# Affine presentation of dense extraction

`affine_operate_map` supplies the register interpretation contract. The generic register-map
and attachment laws give `extractionDDS_eq_affine`: evaluate coefficient pairs only at the
observation resource. The command domain, replies and original secret remain unchanged.
-/

@[expose] public section

namespace Commons.GenericGroup

open SystemAlgebra Probability Commons.AbstractModel

variable
  -- `F` carries secrets and coefficients; `ι` names registers on the unchanged command domain.
  {F ι : Type} [Semiring F] [DecidableEq ι]

/-- Evaluating after an affine operation equals operating on the evaluated operands. -/
lemma affine_operate_map
    -- `x` is the fixed argument; `o` acts on the coefficient tuples `a`.
    (x : F) (o : Operation)
    (a : Fin (operationArity o) → F × F) :
    operate o ((affineEvaluation x) ∘ a) =
      affineEvaluation x (affineOperate o a) := by
  cases o with
  | add =>
    change (a 0).1 * x + (a 0).2 + ((a 1).1 * x + (a 1).2) =
      ((a 0).1 + (a 1).1) * x + ((a 0).2 + (a 1).2)
    rw [add_mul, add_add_add_comm]
  | one =>
    change (1 : F) = 0 * x + 1
    rw [zero_mul, zero_add]

/-- The same dense DDS evaluates affine operands only at the observation boundary. -/
lemma extractionDDS_eq_affine
    -- The original command domain, permutation `π`, and secret `x` remain fixed.
    (input : ι) (k : ℕ) (π : Equiv.Perm F) (x : F) :
    ((denseModel F).extractionDDS input k (π, x)).1 =
      trim (apply ((denseModel F).registersDDC input k affineOperate (1, 0)).1
        (relabel ((denseModel F).observationsDDS k π).1
          (Sigma.map id (fun _ a => (affineEvaluation x) ∘ a)) id)) := by
  have start : affineEvaluation x (1, 0) = x := by
    simp only [affineEvaluation, one_mul, add_zero]
  -- Transport register contents while keeping every outside command and reply fixed.
  have registers := (denseModel F).registersDDC_relabel_of_map input k affineOperate
    operate (affineEvaluation x) (affine_operate_map x) (1, 0) x start
  calc
    _ = trim (apply ((denseModel F).registersDDC input k operate x).1
        ((denseModel F).observationsDDS k π).1) := rfl
    _ = trim (apply
        (relabel ((denseModel F).registersDDC input k affineOperate (1, 0)).1 id
          (insideMap (Sigma.map id (fun _ a => affineEvaluation x ∘ a))))
        ((denseModel F).observationsDDS k π).1) := by rw [registers]
    _ = _ := congrArg trim (apply_relabel_inside_queries _ _ _)

end Commons.GenericGroup

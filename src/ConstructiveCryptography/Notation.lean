import ConstructiveCryptography.InterfaceAlgebra
import ConstructiveCryptography.Tactics.Categorical

/-!
# Notation for interfaces

Scoped notation for the CC operations on interfaces: `Δ R S` for the distance, `R ∥ S` for
parallel composition, `S —[α]→ T` and `S —[α; ε]→ T` for exact and approximate construction,
and `R ≃[ε] S` for substitution within `ε` for the admitted distinguishers
(`Interface.AdmissibleDistinguishers`). The compatibility laws of the distance are restated with `∥`, the concrete
parallel composition, for the `cc_nonexpand` tactic, and `cc_normalize` applies locality,
`(α ⊗ₘ β) • (R ∥ S) = α • R ∥ β • S`, whether the interfaces are written with `⊗` or with
`Interface.tensor`.
-/

namespace SystemAlgebra

open CategoryTheory CategoryTheory.MonoidalCategory

/-- The CC distance of two resources on an interface. Both arguments are elaborated as
resources on an interface, so arrows acting on them take their domains from the resources. -/
scoped macro "Δ " R:term:max S:term:max : term =>
  `(ConstructiveCryptography.CryptographicAlgebra.distance
    ($R : Interface.Resource _) ($S : Interface.Resource _))

scoped infixl:70 " ∥ " =>
  Interface.parallel

scoped notation:50 source " —[" converter "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.Constructs
    converter source target

scoped notation:50 source " —[" converter "; " error "]→ " target:51 =>
  ConstructiveCryptography.CryptographicAlgebra.Specification.ConstructsWithin
    converter source target error

/-- Substitution within `error` for the admitted distinguishers of the instance in scope:
`R ≃[ε] S` is `SubstitutesWithin (distinguisherAdvantage admissible) ε R S`. -/
scoped notation:50 R:51 " ≃[" error "] " S:51 =>
  ConstructiveCryptography.CryptographicAlgebra.DistinguisherAdvantage.SubstitutesWithin
    (Interface.distinguisherAdvantage Interface.AdmissibleDistinguishers.admissible) error R S

namespace Interface

attribute [cc_normalization] comp_smul identity_attach

theorem tensor_smul {A B C D : Interface} (α : A ⟶ B) (β : C ⟶ D)
    (R : Resource B) (S : Resource D) :
    (α ⊗ₘ β) • (R ∥ S) = (α • R) ∥ (β • S) :=
  ConstructiveCryptography.CryptographicAlgebra.attach_parallel
    α β R S

open Lean Meta Simp in
/-- `tensor_smul` whatever the spelling of the interfaces: the action of `α ⊗ₘ β` on `R ∥ S`,
with its types written through `⊗` or through `Interface.tensor`, is `α • R ∥ β • S`. The
two spellings agree only up to unfolding the monoidal structure, which `simp` does not do, so
the rule is keyed on the action alone and matches its arguments here. -/
simproc [cc_normalization] tensorSmul (@HSMul.hSMul _ _ _ _ _ _) := fun e => do
  let_expr HSMul.hSMul _ _ _ _ f x := e | return .continue
  let_expr MonoidalCategoryStruct.tensorHom _ _ _ A B C D α β := f | return .continue
  let_expr Interface.parallel _ _ R S := x | return .continue
  let proof := mkAppN (mkConst ``tensor_smul) #[A, B, C, D, α, β, R, S]
  let_expr Eq _ lhs rhs := ← inferType proof | return .continue
  unless ← withDefault (isDefEq e lhs) do return .continue
  return .visit { expr := rhs, proof? := some (← mkExpectedTypeHint proof (← mkEq e rhs)) }

theorem distance_smul_le {A B : Interface} (α : A ⟶ B) (R S : Resource B) :
    Δ (α • R) (α • S) ≤ Δ R S :=
  ConstructiveCryptography.CryptographicAlgebra.distance_attach_le
    α R S

/-- The hybrid inequality, with both endpoints inferred from the goal. -/
theorem distance_triangle {A : Interface} {R T : Resource A} (S : Resource A) :
    Δ R T ≤ Δ R S + Δ S T :=
  ConstructiveCryptography.CryptographicAlgebra.distance_triangle
    R S T

theorem distance_parallel_left_le {A B : Interface}
    (R S : Resource A) (T : Resource B) : Δ (R ∥ T) (S ∥ T) ≤ Δ R S :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le
    R S T

theorem distance_parallel_right_le {A B : Interface}
    (R : Resource A) (S T : Resource B) : Δ (R ∥ S) (R ∥ T) ≤ Δ S T :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le
    R S T

theorem distance_parallel_le {A B : Interface}
    (R S : Resource A) (T U : Resource B) :
    Δ (R ∥ T) (S ∥ U) ≤ Δ R S + Δ T U :=
  ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le
    R S T U

end Interface

-- The compatibility laws, stated with the concrete parallel composition.
-- Reducible-only matching avoids unfolding probabilities on inapplicable rules.
scoped macro_rules
  | `(tactic| cc_nonexpand) => `(tactic|
      first
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_left_le" =>
          Interface.distance_parallel_left_le _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_right_le" =>
          Interface.distance_parallel_right_le _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_parallel_le" =>
          Interface.distance_parallel_le _ _ _ _
      | with_reducible cc_exact_rule
          "ConstructiveCryptography.CryptographicAlgebra.distance_attach_le" =>
          Interface.distance_smul_le _ _ _)

end SystemAlgebra

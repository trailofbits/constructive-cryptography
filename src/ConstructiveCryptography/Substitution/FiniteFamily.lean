module

public import RandomSystems.Typed.ParallelAllContext
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Substitution.Quantitative
public import Mathlib.Basic.ENNReal.BigOperators

/-!
# Finite-family hybrids in a common context

`parallelAllImplication R S order context` builds an existing implication witness from
`context • (∥ k, R k)` to `context • (∥ k, S k)`. The supplied equivalence `order` selects the
replacement order. Every hybrid retains the same outside converter and tagged component
interfaces; a step changes only `R (order i)` to `S (order i)`.

```text
H m k = S k, if order⁻¹(k) < m; otherwise R k
ρᵢ = context ≫ parallelAllContext (H i) (order i)

context • (∥ k, R k) = ρ₀ • R (order 0)
          Δ ≤ error (order 0)
                    → ρ₀ • S (order 0) = ρ₁ • R (order 1)
                    → … → ρₙ • S (order n) = context • (∥ k, S k)
                         each step: Δ ≤ error (order i)
```

`TypedConverter.parallelAllContext_smul` in `RandomSystems.Typed.ParallelAllContext` proves
`parallelAllContext R k • S = ∥ j, Function.update R k S j`. Serial attachment and the
prefix-update equations in `parallelAllImplication` identify the consecutive hybrids.
`distance_smul_parallelAll_le_sum` applies the implication distance bound:
converter non-expansion transports each component bound, then the hybrid errors add. Its
empty-family case has identical endpoints and zero distance.
`distance_parallelAll_update_le` specializes common-context non-expansion to two families
differing at one tag, so a normalized component update has its own local distance bound.

`substitutesWithin_smul_parallelAll` transports component contracts for a chosen observation
model through the same witness. Each reduction, its admissibility proof, and its advantage
equation are explicit. `Implication.substitutesWithin` then sums the budgets evaluated at
those actual reduced distinguishers. Per-component converters fit inside the common context
by `TypedConverter.comp context (⨂ₘ k, α k)`, preserving their declared interfaces.

The witness implements the exact joins of [1, Lemma 2.3.2, p. 16], with independent families
provided by `parallelAll`. The order selects the hybrid chain while the assembled system
keeps its component tags.
The distance bound is order-independent; the chosen-model losses depend on the hybrid absorbed
by each reduction. Only the component index is finite.

## References

1. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

open ConstructiveCryptography.CryptographicAlgebra
open scoped SystemAlgebra NNReal BigOperators
namespace SystemAlgebra.Substitution

-- `K` names the finite components; `A k` fixes each component's ports, alphabets and domain.
-- `C` is the outside interface of their common converter context.
variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Interface} {C : Interface}

/-- Replacing one component of an independent family costs at most that component's distance.
The exact isolation equation exposes the common converter, whose attachment is non-expanding. -/
lemma distance_parallelAll_update_le
    -- `R j` supplies the fixed components for `j ≠ k`; `k` is the changed component's tag.
    (R : ∀ j, TypedSystem (A j)) (k : K)
    -- `S`, `T` are the replacement pair at the same component interface `A k`.
    (S T : TypedSystem (A k)) :
    Δ (∥ j, Function.update R k S j) (∥ j, Function.update R k T j) ≤ Δ S T := by
  rw [← TypedConverter.parallelAllContext_smul R k S,
    ← TypedConverter.parallelAllContext_smul R k T]
  exact Interface.distance_smul_le (TypedConverter.parallelAllContext R k) S T

/-- The family after `m` replacements: component `k` is `S k` exactly when its position in
`order` is below `m`, and is `R k` otherwise. All members keep their original interfaces. -/
def parallelAllHybrid
    -- `R k`, `S k` are the component pair; `order` chooses each component's position.
    (R S : ∀ k, TypedSystem (A k)) {n : Nat} (order : Fin n ≃ K)
    -- `m` is the replacement-prefix length; `k` selects the returned component.
    (m : Nat) (k : K) : TypedSystem (A k) :=
  if (order.symm k).val < m then S k else R k

/-- Absorb the common assembly and the fixed prefix/suffix systems of hybrid `i`, exposing
only component `order i` to the inside. Its before/after attachments form one hybrid link. -/
noncomputable def parallelAllHybridContext
    -- `R k`, `S k` are the component pair; `order` chooses their replacement order.
    (R S : ∀ k, TypedSystem (A k)) {n : Nat} (order : Fin n ≃ K)
    -- `context` is the common outside converter; `i` selects the component left open.
    (context : TypedConverter C (⨂ k, A k)) (i : Fin n) : TypedConverter C (A (order i)) :=
  TypedConverter.comp context
    (TypedConverter.parallelAllContext (parallelAllHybrid R S order i.val) (order i))

/-- Replace each component once, with exact endpoints and adjacent joins, in the supplied order.
The “independent systems” of [1, Lemma 2.3.2, p. 16] are `R (order i)`, `S (order i)`;
its transformations are `parallelAllHybridContext R S order context i`. Their attachments
are consecutive `parallelAllHybrid` families, giving the witness's exact `link_eq`. -/
noncomputable def parallelAllImplication
    -- `R k` and `S k` are the before/after systems at the same component interface.
    (R S : ∀ k, TypedSystem (A k))
    -- `order` lists every component exactly once; the witness has `n + 1` steps.
    {n : Nat} (order : Fin (n + 1) ≃ K)
    -- `context` is the common outside assembly, including any fixed component converters.
    (context : TypedConverter C (⨂ k, A k)) :
    SubstitutionRelation.Implication A (fun k b => if b then S k else R k) C n := by
  -- The prefix uses replacements, and the remaining components retain their original systems.
  let H := parallelAllHybrid R S order
  -- Before step `i`, its selected component still equals `R (order i)`.
  have hbefore (i : Fin (n + 1)) : Function.update (H i.val) (order i) (R (order i)) = H i.val := by
    apply Function.update_eq_self_iff.mpr
    simp only [H, parallelAllHybrid, Equiv.symm_apply_apply, lt_self_iff_false, ite_false]
  -- Updating only the selected component extends the replacement prefix by one.
  have hafter (i : Fin (n + 1)) :
      Function.update (H i.val) (order i) (S (order i)) = H (i.val + 1) := by
    funext k
    by_cases hk : k = order i
    · subst k
      simp only [Function.update_self, H, parallelAllHybrid, Equiv.symm_apply_apply,
        Nat.lt_succ_self, ite_true]
    · -- At any other index, crossing this position leaves prefix membership unchanged.
      rw [Function.update_of_ne hk]
      have hki : (order.symm k).val ≠ i.val := by
        intro he
        apply hk
        exact (order.apply_symm_apply k).symm.trans (congrArg order (Fin.ext he))
      have hiff : (order.symm k).val < i.val + 1 ↔ (order.symm k).val < i.val := by omega
      simp only [H, parallelAllHybrid, hiff]
  -- The empty and full prefixes are exactly the claimed endpoint families.
  have hzero : H 0 = R := by
    funext k
    exact ite_eq_right (Nat.not_lt_zero _)
  have hlast : H (n + 1) = S := by
    funext k
    exact ite_eq_left (order.symm k).isLt
  -- Absorb every fixed component and the common assembly into the step's converter.
  let ρ := parallelAllHybridContext R S order context
  -- The isolation equation identifies the two ends of this step with consecutive hybrids.
  have hleft (i : Fin (n + 1)) : ρ i • R (order i) = context • (∥ k, H i.val k) := by
    change TypedConverter.comp context
      (TypedConverter.parallelAllContext (H i.val) (order i)) • _ = _
    rw [TypedConverter.comp_smul, TypedConverter.parallelAllContext_smul, hbefore]
  have hright (i : Fin (n + 1)) : ρ i • S (order i) = context • (∥ k, H (i.val + 1) k) := by
    change TypedConverter.comp context
      (TypedConverter.parallelAllContext (H i.val) (order i)) • _ = _
    rw [TypedConverter.comp_smul, TypedConverter.parallelAllContext_smul, hafter]
  -- Record these exact equations in the existing implication carrier.
  exact {
    targetLeft := context • (∥ k, R k)
    targetRight := context • (∥ k, S k)
    index := order
    -- Forward direction selects `R k` as the left side and `S k` as the right side.
    direction := fun _ => false
    transformation := ρ
    start_eq := by
      change context • (∥ k, R k) = ρ 0 • R (order 0)
      simpa only [Fin.val_zero, hzero] using (hleft 0).symm
    link_eq := fun i => by
      change ρ i.castSucc • S (order i.castSucc) = ρ i.succ • R (order i.succ)
      rw [hright, hleft]
      rfl
    end_eq := by
      change context • (∥ k, S k) = ρ (Fin.last n) • S (order (Fin.last n))
      simpa only [Fin.val_last, hlast] using (hright (Fin.last n)).symm }

/-- Local component errors add after attachment to one common context.
[1, §2.3.1, p. 15]: “collect the sum of such pᵢ's into a value ε”. The independent products
and explicit domain-preserving converters supply its transformed hybrid steps. -/
theorem distance_smul_parallelAll_le_sum
    -- `R k` and `S k` are the before/after component systems.
    (R S : ∀ k, TypedSystem (A k))
    -- `order` chooses the replacement order, including the empty family when `n = 0`.
    {n : Nat} (order : Fin n ≃ K)
    -- `context` is shared by both assemblies; `error k` is component `k`'s scalar budget.
    (context : TypedConverter C (⨂ k, A k)) (error : K → ℝ≥0)
    -- `step k` is only the local bound; the conclusion sums these budgets without truncation.
    (step : ∀ k, Δ (R k) (S k) ≤ error k) :
    Δ (context • (∥ k, R k)) (context • (∥ k, S k)) ≤ (∑ k, error k : ℝ≥0) := by
  cases n with
  | zero =>
    -- An empty index has only one family, so both assemblies are equal.
    have heq : R = S := by funext k; exact Fin.elim0 (order.symm k)
    rw [heq, distance_self]
    exact bot_le
  | succ n =>
    -- The existing implication theorem transports local bounds through each isolation converter.
    have hc := (parallelAllImplication R S order context).distance_le
      (fun i => (error (order i) : ENNReal)) (fun i => step (order i))
    change Δ (context • (∥ k, R k)) (context • (∥ k, S k)) ≤ _ at hc
    -- Reindex the error sum by the supplied order; the systems retain their original tags.
    rw [Equiv.sum_comp order (fun k => (error k : ENNReal))] at hc
    simpa only [ENNReal.ofNNReal_finsetSum] using hc

/-- Component contracts in a chosen observation model give a bound for the assembled pair.
[1, §2.3.3, p. 16] evaluates the loss as “ε′(Dκ) = ε(Dκρ)”. Here `d` is `Dκ`, the
named hybrid context is `ρ`, and `reduce i d` is `Dκρ`. The joins of
[1, Lemma 2.3.2, p. 16] sum these transformed losses. -/
theorem substitutesWithin_smul_parallelAll
    -- `R k` and `S k` are the local pair; `order` lists the replacement chain.
    (R S : ∀ k, TypedSystem (A k)) {n : Nat} (order : Fin n ≃ K)
    -- `context` is the outside converter shared by both families.
    (context : TypedConverter C (⨂ k, A k))
    -- `D B` carries tests on interface `B`; `model` selects their advantage and admissibility.
    {D : Interface → Type} (model : DistinguisherAdvantage Interface TypedSystem D)
    -- `reduce i` absorbs the witness's actual step converter into the outside distinguisher.
    (reduce : ∀ i : Fin n, D C → D (A (order i)))
    -- `closed` admits tests after absorbing `context` and the fixed `S` prefix / `R` suffix;
    -- this is the per-step closure required in [1, §2.3.3, p. 16].
    (closed : ∀ i d, d ∈ model.admissible C → reduce i d ∈ model.admissible (A (order i)))
    -- `hadvantage` relates the outside advantage to the local advantage under that same reduction.
    (hadvantage : ∀ i d (U V : TypedSystem (A (order i))), model.advantage C d
      (parallelAllHybridContext R S order context i • U)
      (parallelAllHybridContext R S order context i • V) =
      model.advantage (A (order i)) (reduce i d) U V)
    -- `error k` is the local test-dependent budget, and `step k` is the component contract.
    (error : ∀ k, D (A k) → ENNReal)
    (step : ∀ k, model.SubstitutesWithin (error k) (R k) (S k)) :
    model.SubstitutesWithin (fun d => ∑ i, error (order i) (reduce i d))
      (context • (∥ k, R k)) (context • (∥ k, S k)) := by
  cases n with
  | zero =>
    -- The empty family has identical assemblies and zero advantage for every admitted test.
    have heq : R = S := by funext k; exact Fin.elim0 (order.symm k)
    rw [heq]
    intro d _
    rw [model.advantage_self]
    exact bot_le
  | succ n =>
    -- Exact joins let the existing hybrid theorem sum the transformed contracts.
    apply SubstitutionRelation.Implication.substitutesWithin model
      (parallelAllImplication R S order context) (fun i d => error (order i) (reduce i d))
    intro i
    -- Closure and the advantage equation transport this local premise through its converter.
    exact DistinguisherAdvantage.SubstitutesWithin.attach model
      ((parallelAllImplication R S order context).transformation i) (reduce i) (closed i)
      (hadvantage i) (step (order i))

end SystemAlgebra.Substitution

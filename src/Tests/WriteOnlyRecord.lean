module

public import RandomSystems.Typed.WriteOnlyRecord
public import ConstructiveCryptography.Notation

/-!
# Tests for write-only record erasure

Exercises `TypedConverter.WriteOnlyRecord` and `TypedConverter.recordAndForward` using CC's custom
notation (`•`, `∥`, `≫`, `⊗ₘ`, `𝟙`, `sample k ←$ P`):
* Function-backed record erasure beside both a fixed function (`TypedSystem.ofFunction`) and an
  arbitrary stateful/probabilistic system `H`, for unequal interfaces and budgets.
* Composed consumers using only the named erasure equality under outer converters (`α ≫ record`),
  retained shared randomness (`sample k ←$ P; Y k ∥ H k`), parallel contexts (`record ⊗ₘ β`), and
  `cc_normalize`.
* Standard-axiom audit on all exported theorems.
-/

@[expose] public section

set_option autoImplicit false

namespace Tests.WriteOnlyRecord

open CategoryTheory CategoryTheory.MonoidalCategory
open Probability SystemAlgebra
open scoped SystemAlgebra

/-- Main interface `A`: two queries on `Bool → Bool`. -/
abbrev MainPort : Interface :=
  Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool) 2

/-- Write-only log interface `B`: unequal query/reply alphabets (`Bool × Bool → Unit`) and
budget `3` (`≥ 2`). -/
abbrev LogPort : Interface :=
  Interface.queryBudget Unit (fun _ => Bool × Bool) (fun _ => Unit) 3

/-- Record every `(x, y)` pair to `LogPort`. -/
def logPair : ∀ i : MainPort.I, MainPort.X i → MainPort.Y i → Option (Σ j : LogPort.I, LogPort.X j)
  | (), x, y => some ⟨(), (x, y)⟩

lemma logPair_admitted :
    ∀ h : List ((Σ i, MainPort.X i) × (Σ i, MainPort.Y i)),
      MainPort.domain (h.map Prod.fst) → (∀ z ∈ h, z.2.1 = z.1.1) →
      h.filterMap (TypedConverter.recordExchange logPair) = [] ∨
        LogPort.domain (h.filterMap (TypedConverter.recordExchange logPair)) := by
  intro h hA _
  by_cases hne : h.filterMap (TypedConverter.recordExchange logPair) = []
  · exact Or.inl hne
  · refine Or.inr ⟨hne, ?_⟩
    have hlen : (h.filterMap (TypedConverter.recordExchange logPair)).length ≤ h.length :=
      List.length_filterMap_le _ _
    have hAb : h.length ≤ 2 := by simpa using MainPort.length_le _ hA
    omega

/-- Function-backed recorder instance on `MainPort ⟶ MainPort ⊗ LogPort`. -/
noncomputable def logConverter : MainPort ⟶ (MainPort ⊗ LogPort) :=
  TypedConverter.recordAndForward logPair logPair_admitted

/-- Erasing a function-backed log system beside an arbitrary `Y`. -/
example (Y : TypedSystem MainPort) (f : ∀ j, LogPort.X j → LogPort.Y j) :
    logConverter • (Y ∥ TypedSystem.ofFunction f) = Y :=
  TypedConverter.recordAndForward_smul_parallel_ofFunction logPair logPair_admitted Y f

/-- Erasing an arbitrary stateful/probabilistic log system `H` beside an arbitrary `Y`. -/
example (Y : TypedSystem MainPort) (H : TypedSystem LogPort) :
    logConverter • (Y ∥ H) = Y :=
  TypedConverter.recordAndForward_smul_parallel logPair logPair_admitted Y H

/-- A composed consumer transports erasure through any outer converter `α` using only the named
equality (no program-level reasoning). -/
example {Outer : Interface} (α : Outer ⟶ MainPort)
    (Y : TypedSystem MainPort) (H : TypedSystem LogPort) :
    (α ≫ logConverter) • (Y ∥ H) = α • Y :=
  TypedConverter.comp_smul_parallel_of_erases α
    (TypedConverter.recordAndForward_smul_parallel logPair logPair_admitted Y H)

/-- Shared randomness is preserved: erasing `H k` inside a retained sample `sample k ←$ P`
keeps the same draw `k` for `Y k`, both directly and under an outer converter `α`. -/
example {Outer : Interface} {K : Type} (α : Outer ⟶ MainPort) (P : Distribution.ProbDist K)
    (Y : K → TypedSystem MainPort) (H : K → TypedSystem LogPort) :
    (α ≫ logConverter) • (sample k ←$ P; (Y k ∥ H k)) = sample k ←$ P; α • Y k :=
  TypedConverter.comp_smul_sample_parallel_of_erases α P Y H fun k =>
    TypedConverter.recordAndForward_smul_parallel logPair logPair_admitted (Y k) (H k)

/-- `cc_normalize` composes cleanly with write-only record erasure in a parallel context and
inside a retained sample. -/
example {C D : Interface} {K : Type} (β : C ⟶ D) (P : Distribution.ProbDist K)
    (Y : K → TypedSystem MainPort) (H : K → TypedSystem LogPort) (Z : K → TypedSystem D) :
    (logConverter ⊗ₘ β) • (sample k ←$ P; ((Y k ∥ H k) ∥ Z k)) =
      sample k ←$ P; (Y k ∥ (β • Z k)) := by
  cc_normalize
  congr 1
  funext k
  rw [logConverter, TypedConverter.recordAndForward_smul_parallel]

#print axioms TypedConverter.WriteOnlyRecord.smul_parallel
#print axioms TypedConverter.comp_smul_parallel_of_erases
#print axioms TypedConverter.smul_sample_parallel_of_erases
#print axioms TypedConverter.comp_smul_sample_parallel_of_erases
#print axioms TypedConverter.parallel_smul_parallel_of_erases
#print axioms TypedConverter.recordAndForward_writeOnlyRecord
#print axioms TypedConverter.recordAndForward_smul_parallel
#print axioms TypedConverter.recordAndForward_smul_parallel_ofFunction

end Tests.WriteOnlyRecord

import RandomSystems.Cumulative.ParallelAll

/-!
# Finite parallel systems: boundary cases

Boundary cases of `RandomSystem.parallelAll` and `Domain.parallelAll`, writing `h|k` for the
projection of `h` to component `k`:

* empty family `K = Empty`: `[]` has mass `1`, the empty product; `parallelAllInputs`
  excludes `[]`;
* two components tagged by `Bool`: an interleaved history has mass `R true (h|true) ·
  R false (h|false)`;
* after an exchange `(true(()), false ⇒ ())` with a wrong reply tag, no query is admitted;
* after one exchange with `true`, whose bound is `0`, no query to `false` is admitted;
* components with alphabets `Bool`/`Unit` and `Unit`/`Bool` form a parallel domain.
-/

namespace SystemAlgebra.Tests

noncomputable section

section Empty

-- The empty family: no components, so `D` and `R` are the unique functions on `Empty`.
variable (D : ∀ _k : Empty, Domain Unit Unit)
  (R : ∀ k : Empty, RandomSystem Unit Unit (D k))

-- `(parallelAll R) [] = ∏ k ∈ ∅, … = 1`, as for every random system.
example : (RandomSystem.parallelAll R) [] = 1 := RandomSystem.mass_nil _

-- `parallelAllInputs E []` fails its first clause `h ≠ []`.
example : ¬ parallelAllInputs (K := Empty) (I := fun _ => Unit)
    (F := fun _ _ => Unit) (fun k => nomatch k) [] := by
  simp [parallelAllInputs]

end Empty

section Interleaved

-- Two arbitrary components `R k : RandomSystem Unit Unit (D k)`, `k : Bool`.
variable (D : ∀ _k : Bool, Domain Unit Unit)
  (R : ∀ k : Bool, RandomSystem Unit Unit (D k))

-- Interleaving:
--   h       = (true(()), true ⇒ ()) (false(()), false ⇒ ())
--   h|true  = [((), ())]        h|false = [((), ())]
-- so `(parallelAll R) h = R true [((), ())] · R false [((), ())]`.
example : RandomSystem.parallelAll R
    [(⟨true, ()⟩, ⟨true, ()⟩), (⟨false, ()⟩, ⟨false, ()⟩)] =
      R true [((), ())] * R false [((), ())] := by
  rw [RandomSystem.parallelAll_mass]
  simp [RandomSystem.parallelAllConsistent, RandomSystem.restrictExchanges]

-- Wrong tag: the history `(true(()), false ⇒ ())` is not tag consistent, so no query is
-- admitted after it, whatever `D` is.
example : ¬ (Domain.parallelAll D).admits
    [(⟨true, ()⟩, ⟨false, ()⟩)] ⟨true, ()⟩ := by
  intro hd
  -- Consistency at the single exchange would give `true = false`.
  have htag := hd.1 (⟨⟨true, ()⟩, ⟨false, ()⟩⟩) (by simp)
  cases htag

/-- The domain admitting no query: `admits h x = False` for all `h`, `x`, and `bound = 0`. As a
component domain in `Domain.parallelAll`, it allows `|h|k| ≤ 0`, so any exchange with that
component exhausts it. -/
def zeroDomain : Domain Unit Unit where
  admits := fun _ _ => False
  bound := 0
  length_lt := by intro _ _ h; cases h

-- Exhausted other component: after `h = (true(()), true ⇒ ())`, the query `false(())` needs
-- `|h|true| = 1 ≤ zeroDomain.bound = 0`, which fails.
example : ¬ (Domain.parallelAll (fun _ : Bool => zeroDomain)).admits
    [(⟨true, ()⟩, ⟨true, ()⟩)] ⟨false, ()⟩ := by
  intro hd
  -- The bound clause for the other component `true ≠ false` reduces to `1 ≤ 0`.
  have hbound := hd.2.1 true (by simp)
  simp [RandomSystem.restrictExchanges, zeroDomain] at hbound

end Interleaved

-- Heterogeneous alphabets: component `true` has inputs `Bool` and replies `Unit`, component
-- `false` has inputs `Unit` and replies `Bool`; `Domain.parallelAll` combines their domains.
example (D : ∀ b : Bool,
    Domain (if b then Bool else Unit) (if b then Unit else Bool)) :
    Domain (Σ b : Bool, if b then Bool else Unit)
      (Σ b : Bool, if b then Unit else Bool) :=
  Domain.parallelAll D

-- The main definition and the transcript law use only the standard axioms.
#print axioms SystemAlgebra.RandomSystem.parallelAll
#print axioms SystemAlgebra.RandomSystem.replies_parAll_iff

end
end SystemAlgebra.Tests

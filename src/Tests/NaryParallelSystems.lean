import RandomSystems.Cumulative.ParallelAllPresentation

/-!
# Finite parallel systems: boundary cases

Boundary cases of `RandomSystem.parallelAll` and `Domain.parallelAll`, writing `h|k` for the
projection of `h` to component `k`:

* empty family `K = Empty`: `[]` has mass `∏ k ∈ ∅, … = 1`; `parallelAllInputs` excludes `[]`;
* two components tagged by `Bool`: an interleaved history has mass `R true (h|true) ·
  R false (h|false)`;
* wrong reply tag: after `(true(()), false ⇒ ())` no query is admitted, and that history has
  mass `0`;
* exhausted other component, with `true` of bound `0` and `false` admitting one query: after
  `(true(()), true ⇒ ())` the query `false(())` is rejected only by the bound on `true`, and
  that history has mass `0`;
* heterogeneous alphabets `Bool`/`Unit` and `Unit`/`Bool`: a parallel domain and a parallel
  random system;
* infinite tags `K = ℕ`: the transcript law of `parAll` needs no finiteness of `K`.
-/

namespace SystemAlgebra.Tests

noncomputable section

section Empty

-- The empty family: no components, so `D` and `R` are the unique functions on `Empty`.
variable (D : ∀ _k : Empty, Domain Unit Unit)
  (R : ∀ k : Empty, RandomSystem Unit Unit (D k))

-- `[]` is consistent and has empty projections, so `(parallelAll R) [] = ∏ k ∈ ∅, … = 1`.
example : (RandomSystem.parallelAll R) [] = 1 := by
  rw [RandomSystem.parallelAll_mass]
  simp only [RandomSystem.parallelAllConsistent, List.not_mem_nil, IsEmpty.forall_iff,
    ↓reduceIte, Finset.univ_eq_empty, RandomSystem.restrictExchanges,
    eq_rec_constant, dite_eq_ite, List.filterMap_nil, Finset.prod_empty]

example (P : ∀ _k : Empty, Probability.Distribution Unit)
    (s : ∀ _k : Empty, Unit → System Unit Unit) :
    RandomSystem.parallelAll R [] =
      (Probability.Distribution.piDep P).mass (fun st =>
        Replies (parAll (fun k => s k (st k))) [] []) := by
  apply RandomSystem.parallelAll_mass_of_presentations R P s
  intro k
  cases k

-- `parallelAllInputs E []` fails its first clause `h ≠ []`.
example : ¬ parallelAllInputs (K := Empty) (I := fun _ => Unit)
    (F := fun _ _ => Unit) (fun k => nomatch k) [] := by
  simp only [parallelAllInputs, ne_eq, not_true_eq_false, List.map_nil, restrict_nil, true_or,
    implies_true, and_true, not_false_eq_true]

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
  simp only [RandomSystem.parallelAllConsistent, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, and_self, ↓reduceIte, Fintype.univ_bool,
    RandomSystem.restrictExchanges, eq_rec_constant, dite_eq_ite, Finset.mem_singleton,
    Bool.true_eq_false, not_false_eq_true, Finset.prod_insert, Option.some.injEq,
    List.filterMap_cons_some, Bool.false_eq_true, List.filterMap_cons_none, List.filterMap_nil,
    Finset.prod_singleton]

-- Wrong tag: the history `(true(()), false ⇒ ())` is not tag consistent, so no query is
-- admitted after it, whatever `D` is.
example : ¬ (Domain.parallelAll D).admits
    [(⟨true, ()⟩, ⟨false, ()⟩)] ⟨true, ()⟩ := by
  intro hd
  -- Consistency at the single exchange would give `true = false`.
  have htag := hd.1 _ (List.mem_singleton_self _)
  cases htag

-- The same inconsistent history has mass `0` by the defining equation, whatever `R` is.
example : RandomSystem.parallelAll R [(⟨true, ()⟩, ⟨false, ()⟩)] = 0 := by
  rw [RandomSystem.parallelAll_mass]
  simp only [RandomSystem.parallelAllConsistent, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, Bool.true_eq_false, ↓reduceIte]

/-- The domain admitting no query: `admits h x = False` for all `h`, `x`, and `bound = 0`. As a
component domain in `Domain.parallelAll`, it allows `|h|k| ≤ 0`, so one exchange with that
component exhausts it. -/
def zeroDomain : Domain Unit Unit where
  admits := fun _ _ => False
  bound := 0
  length_lt := by intro _ _ h; cases h

/-- A single query: `admits h () ↔ h = []`, with bound `1`. -/
def oneQueryDomain : Domain Unit Unit where
  admits h _ := h = []
  bound := 1
  length_lt h _ hh := by subst hh; exact Nat.zero_lt_one

/-- Component domains `true ↦ zeroDomain` (bound `0`, admits nothing) and
`false ↦ oneQueryDomain` (bound `1`, admits `()` at `[]`). -/
def boundaryDomains : Bool → Domain Unit Unit
  | true => zeroDomain
  | false => oneQueryDomain

-- The queried component accepts: `false` admits `()` at its empty history `h|false = []`.
example : boundaryDomains false [] () := rfl

-- Exhausted other component: after `h = (true(()), true ⇒ ())`, the query `false(())` is
-- consistent and admitted by `false`, but needs `|h|true| = 1 ≤ zeroDomain.bound = 0`.
example : ¬ (Domain.parallelAll boundaryDomains).admits
    [(⟨true, ()⟩, ⟨true, ()⟩)] ⟨false, ()⟩ := by
  intro hd
  -- The bound clause for the other component `true ≠ false` reduces to `1 ≤ 0`.
  have hbound := hd.2.1 true (by simp only [ne_eq, Bool.true_eq_false, not_false_eq_true])
  simp only [RandomSystem.restrictExchanges, eq_rec_constant, dite_eq_ite, ↓reduceIte,
    Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, List.length_cons,
    List.length_nil, zero_add, boundaryDomains, zeroDomain, nonpos_iff_eq_zero,
      one_ne_zero] at hbound

-- That history has mass `0`: `|h|true| = 1 > 0` gives `R true [((), ())] = 0`, a zero factor
-- of `R true (h|true) · R false []`.
example (R : ∀ k, RandomSystem Unit Unit (boundaryDomains k)) :
    RandomSystem.parallelAll R [(⟨true, ()⟩, ⟨true, ()⟩)] = 0 := by
  have hz : R true [((), ())] = 0 :=
    (R true).mass_eq_zero_of_bound_lt Nat.zero_lt_one
  rw [RandomSystem.parallelAll_mass]
  simp only [RandomSystem.parallelAllConsistent, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, ↓reduceIte, Fintype.univ_bool, RandomSystem.restrictExchanges, eq_rec_constant,
    dite_eq_ite, Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    Finset.prod_insert, Option.some.injEq, List.filterMap_cons_some, List.filterMap_nil, hz,
    Finset.prod_singleton, List.filterMap_cons_none, zero_mul]

end Interleaved

-- Heterogeneous alphabets: component `true` has inputs `Bool` and replies `Unit`, component
-- `false` has inputs `Unit` and replies `Bool`; `Domain.parallelAll` combines their domains.
example (D : ∀ b : Bool,
    Domain (if b then Bool else Unit) (if b then Unit else Bool)) :
    Domain (Σ b : Bool, if b then Bool else Unit)
      (Σ b : Bool, if b then Unit else Bool) :=
  Domain.parallelAll D

-- The same heterogeneous family of random systems, given finite alphabets, has the parallel
-- random system `parallelAll R` on `Domain.parallelAll D`.
example (D : ∀ b : Bool,
    Domain (if b then Bool else Unit) (if b then Unit else Bool))
    [∀ b : Bool, Fintype (if b then Bool else Unit)]
    [∀ b : Bool, Fintype (if b then Unit else Bool)]
    (R : ∀ b, RandomSystem (if b then Bool else Unit) (if b then Unit else Bool) (D b)) :
    RandomSystem (Σ b : Bool, if b then Bool else Unit)
      (Σ b : Bool, if b then Unit else Bool) (Domain.parallelAll D) :=
  RandomSystem.parallelAll R

-- Infinite tag set `K = ℕ`: the transcript law of the deterministic `parAll s` applies
-- unchanged, since `replies_parAll_iff` does not assume `Fintype K`.
example (s : ℕ → System Unit Unit) (h : List ((Σ _ : ℕ, Unit) × (Σ _ : ℕ, Unit))) :
    Replies (parAll s) (h.map Prod.fst) (h.map Prod.snd) ↔
      RandomSystem.parallelAllConsistent h ∧
        ∀ k, Replies (s k) ((RandomSystem.restrictExchanges k h).map Prod.fst)
          ((RandomSystem.restrictExchanges k h).map Prod.snd) :=
  RandomSystem.replies_parAll_iff s h

-- The main definition and the transcript law use only the standard axioms.
#print axioms SystemAlgebra.RandomSystem.parallelAll
#print axioms SystemAlgebra.RandomSystem.replies_parAll_iff
#print axioms SystemAlgebra.RandomSystem.parallelAll_mass_of_presentations

end
end SystemAlgebra.Tests

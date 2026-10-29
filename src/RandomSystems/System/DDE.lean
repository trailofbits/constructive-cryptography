import RandomSystems.System.Basic

/-!
# Deterministic environments

An environment is a query function with prefix-closed domain; it stops where it is
undefined and outputs no decision. Source: Lanzenberger, *A Theory of Random
Systems, Games, and Hardness Amplification*, Definition 2.11.

## Main definitions

* `DDE X Y`: deterministic environments
* `QueryBounded n E`: `E` asks at most `n` queries
* `DDE.ofQueries xs`: the environment that asks the fixed queries `xs`
* `limitQueries σ n`: a partial strategy `σ` truncated after `n` queries, on every reply history
* `DDE.limitQueries E n`: the same truncation of `E`, as a prefix-closed environment

`mem_limitQueries` gives the query rule and `DDE.limitQueries_queryBounded` the bound;
`CumulativeObservation` and `Distance.Decision` use them to observe a system at its domain
bound.
-/

namespace SystemAlgebra

/-- A deterministic environment, as a partial function of received replies. -/
abbrev DDE (X Y : Type) :=
  {e : System Y X // ∀ ys y, (e (ys ++ [y])).Dom → (e ys).Dom}

/-- The environment makes at most `n` queries. -/
def QueryBounded {X Y : Type} (n : ℕ) (E : DDE X Y) : Prop :=
  ∀ ys, (E.1 ys).Dom → ys.length < n

/-- The strategy `σ` limited to its first `n` queries:
`limitQueries σ n ys = σ ys` if `|ys| < n`, and is undefined otherwise. -/
def limitQueries {A B : Type} (σ : List B →. A) (n : ℕ) : List B →. A := fun ys =>
  if ys.length < n then σ ys else Part.none

/-- The next query is unchanged before the limit, and absent at or beyond it. -/
lemma mem_limitQueries {A B : Type} {σ : List B →. A} {n : ℕ} {ys : List B} {x : A} :
    x ∈ limitQueries σ n ys ↔ ys.length < n ∧ x ∈ σ ys := by
  change x ∈ (if ys.length < n then σ ys else Part.none) ↔ _
  split_ifs with hn <;> simp only [hn, true_and, false_and, Part.notMem_none]

namespace DDE

/-- Issue a fixed list of queries, then stop, independently of the replies. -/
def ofQueries {X Y : Type} (xs : List X) : DDE X Y :=
  ⟨fixedQueries xs, by
    intro ys y hd
    simp [fixedQueries, Part.ofOption_dom] at hd ⊢
    omega⟩

variable {A B : Type}

/-- `SystemAlgebra.limitQueries` as an environment: follow `E` for at most `n` queries,
stopping also on reply histories impossible for the system. -/
def limitQueries (E : DDE A B) (n : ℕ) : DDE A B :=
  ⟨SystemAlgebra.limitQueries E.1 n, by
    -- Prefix closure: a query after `ys ++ [y]` lies below `n`, so `E` also queries after `ys`.
    intro ys y hd
    change (if (ys ++ [y]).length < n then E.1 (ys ++ [y]) else Part.none).Dom at hd
    change (if ys.length < n then E.1 ys else Part.none).Dom
    by_cases hn : (ys ++ [y]).length < n
    · rw [if_pos hn] at hd
      rw [if_pos (by simp only [List.length_append, List.length_singleton] at hn; omega)]
      exact E.2 ys y hd
    · rw [if_neg hn] at hd
      exact hd.elim⟩

/-- The limited environment is bounded by `n` on every reply history. -/
lemma limitQueries_queryBounded (E : DDE A B) (n : ℕ) : QueryBounded n (limitQueries E n) := by
  intro ys hd
  exact (mem_limitQueries.mp (Part.get_mem hd)).1

end DDE

end SystemAlgebra

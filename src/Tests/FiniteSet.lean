module

public import Probability.FiniteSet

/-!
# Finite encodings of empty and sparse alphabets

An empty source admits zero codes. The supported naturals `7` and `42` round-trip to distinct
codes even though the source alphabet is infinite.
-/

@[expose] public section

namespace Tests.FiniteSet

/-- The decoder into `Empty` forces the finite alphabet to be empty too. -/
lemma empty_encoding :
    ∃ (code : Empty → Fin 0) (decode : Fin 0 ↪ Empty),
      ∀ x, decode (code x) = x := by
  obtain ⟨n, code, decode, _⟩ := (Set.finite_empty : (∅ : Set Empty).Finite).exists_fin_encoding
  cases n with
  | zero => exact ⟨code, decode, fun x => Empty.elim x⟩
  | succ n => exact Empty.elim (decode 0)

/-- An empty support in a nonempty source still admits total encoding and decoding. -/
example : ∃ (n : ℕ) (_ : ℕ → Fin n) (_ : Fin n ↪ ℕ), 0 < n := by
  obtain ⟨n, code, decode, _⟩ := (Set.finite_empty : (∅ : Set ℕ).Finite).exists_fin_encoding
  exact ⟨n, code, decode, (Nat.zero_le (code 0).val).trans_lt (code 0).isLt⟩

/-- Both supported naturals decode exactly; consequently their codes cannot coincide. -/
lemma sparse_encoding :
    ∃ (n : ℕ) (code : ℕ → Fin n) (decode : Fin n ↪ ℕ),
      decode (code 7) = 7 ∧ decode (code 42) = 42 ∧ code 7 ≠ code 42 := by
  obtain ⟨n, code, decode, inverse⟩ :=
    ((Set.finite_singleton 42).insert 7).exists_fin_encoding
  have seven := inverse 7 (Set.mem_insert 7 {42})
  have fortyTwo := inverse 42 (Set.mem_insert_of_mem 7 rfl)
  refine ⟨n, code, decode, seven, fortyTwo, ?_⟩
  intro same
  have impossible : (7 : ℕ) = 42 := seven.symm.trans ((congrArg decode same).trans fortyTwo)
  cases impossible

#print axioms Set.Finite.exists_fin_encoding
#print axioms empty_encoding
#print axioms sparse_encoding

end Tests.FiniteSet

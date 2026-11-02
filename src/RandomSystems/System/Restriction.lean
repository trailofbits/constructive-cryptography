module

public import RandomSystems.System.Basic

/-!
# Projection of tagged query schedules

`restrict k` selects the inputs addressed to component `k` and removes their tags.
`restrict_map_of_nodup` computes that projection for a list with at most one input per
component: it is the selected singleton if the component occurs, and the empty list otherwise.
This connects an explicitly ordered call schedule to each component's own input history.
-/

@[expose] public section

namespace SystemAlgebra

-- `K` names components and `A k` carries the input addressed to component `k`.
variable {K : Type} {A : K → Type}

open Classical in
/-- Projecting a list with one tagged value per distinct index selects exactly that value. -/
lemma restrict_map_of_nodup
    -- `ks` lists distinct component indices; `x k` is the value carried at index `k`.
    (ks : List K) (hks : ks.Nodup) (x : ∀ k, A k) (k : K) :
    restrict k (ks.map fun j => (⟨j, x j⟩ : Σ j, A j)) =
      if k ∈ ks then [x k] else [] := by
  induction ks with
  | nil => simp only [List.map_nil, restrict_nil, List.not_mem_nil, ↓reduceIte]
  | cons j ks ih =>
    obtain ⟨hj, ht⟩ := List.nodup_cons.mp hks
    by_cases he : j = k
    · -- The selected head cannot occur again in the tail.
      subst j
      simp only [List.map_cons, restrict_cons_self, ih ht, hj, ↓reduceIte,
        List.mem_cons_self]
    · -- Another component's head is omitted by projection.
      rw [List.map_cons, restrict_cons_ne he, ih ht]
      simp only [List.mem_cons, Ne.symm he, false_or]

end SystemAlgebra

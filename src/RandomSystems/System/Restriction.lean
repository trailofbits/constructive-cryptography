module

public import RandomSystems.System.Basic

/-!
# Projection of tagged query schedules

`restrict k` selects the inputs addressed to component `k` and removes their tags.
`restrict_map_of_nodup` computes that projection for a list with at most one input per
component: it is the selected singleton if the component occurs, and the empty list otherwise.
This connects an explicitly ordered call schedule to each component's own input history.
`restrict_map_sigmaCongrLeft` transports this projection through a reindexing equivalence;
finite-family domain proofs reuse it without introducing interface assumptions.
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

open Classical in
/-- **The restriction after reindexing** at `e k'` is the restriction at `k'`. -/
lemma restrict_map_sigmaCongrLeft {K' : Type} (e : K' ≃ K) {F : K → Type}
    (l : List (Σ k', F (e k'))) (k' : K') :
    restrict (e k') (l.map (Equiv.sigmaCongrLeft e)) = restrict k' l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    obtain ⟨a, x⟩ := x
    -- `sigmaCongrLeft e ⟨a, x⟩` is `⟨e a, x⟩`.
    change restrict (e k') (⟨e a, x⟩ :: l.map (Equiv.sigmaCongrLeft e)) = restrict k' (⟨a, x⟩ :: l)
    by_cases ha : a = k'
    · subst ha
      rw [restrict_cons_self, restrict_cons_self, ih]
    · rw [restrict_cons_ne (e.injective.ne ha), restrict_cons_ne ha, ih]


end SystemAlgebra

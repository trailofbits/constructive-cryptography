module

public import RandomSystems.Converter.QueryBound

/-!
# Certified finite-horizon converter restrictions

`IsDDCFrom.filterDom_of_insideQueriesBounded` restricts a certified converter to `q` outside
inputs. Its inside domain is intersected with the query bound `k q`, and its outside domain
with the horizon `q`. The converter retains its existing per-invocation bound and replies.
The total-query contract supplies the stronger inside-domain certificate.
-/

@[expose] public section

namespace SystemAlgebra

/-- Restricting outside inputs certifies the corresponding finite inside and outside domains. -/
lemma IsDDCFrom.filterDom_of_insideQueriesBounded
    -- `O`, `J` label outside/inside ports, with query/reply families `U`, `V` and `X`, `Y`.
    {O J : Type} {U V : O → Type} {X Y : J → Type}
    -- `E`, `F` admit inside and outside input histories, respectively.
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop}
    {b : ℕ} {α : InsideOutsideSystem O J U V X Y}
    -- `ha` certifies the original domains and per-invocation bound; `bound` counts total queries.
    (ha : IsDDCFrom E F b α) {k : ℕ → ℕ} (bound : InsideQueriesBounded α k)
    -- `mono` lets the total bound grow with the outside horizon `q`.
    (mono : Monotone k) (q : ℕ) :
    IsDDCFrom (fun xs => E xs ∧ xs.length ≤ k q) (fun us => F us ∧ us.length ≤ q) b
      (filterDom (fun xs => (outsideInputs xs).length ≤ q) α) := by
  let cutoff := fun xs : List (Σ l, twoFam U Y l) => (outsideInputs xs).length ≤ q
  -- Projecting an input prefix preserves its outside-input length bound.
  have prefixClosed : ∀ {xs ys}, xs <+: ys → xs ≠ [] → cutoff ys → cutoff xs := by
    rintro xs ys ⟨zs, rfl⟩ _ hy
    change (outsideInputs xs).length ≤ q
    change (outsideInputs (xs ++ zs)).length ≤ q at hy
    rw [outsideInputs_append, List.length_append] at hy
    exact (Nat.le_add_right _ _).trans hy
  have inclusion : ∀ xs y, y ∈ filterDom cutoff α xs → y ∈ α xs :=
    fun xs y hy => ((filterDom_mem_iff cutoff α xs y).mp hy).2
  -- A retained transcript uses at most k q inside queries, on the original inside domain.
  have queries (T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l)))
      (hr : Replies (filterDom cutoff α) (T.map Prod.fst) (T.map Prod.snd)) :
      insideQueries (T.map Prod.snd) = [] ∨
        E (insideQueries (T.map Prod.snd)) ∧ (insideQueries (T.map Prod.snd)).length ≤ k q := by
    by_cases empty : T.map Prod.fst = []
    · have nil : T = [] := List.map_eq_nil_iff.mp empty
      subst T
      exact Or.inl rfl
    · have outside := ((filterDom_dom cutoff α _).mp (hr.dom empty)).1
      have original := hr.mono inclusion
      exact (ha.queries T original).imp_right fun admitted =>
        ⟨admitted, (bound T original).trans (mono outside)⟩
  refine ⟨ha.isDDC.filterDom cutoff prefixClosed, ?_, queries⟩
  intro T x hr
  -- The answer domain gains exactly the outside cutoff; the queries fact supplies its inside part.
  rw [filterDom_dom, ha.answers T x (hr.mono inclusion)]
  constructor
  · rintro ⟨hcut, hphase, hnext, hF, _⟩
    exact ⟨hphase, hnext, ⟨hF, hcut⟩, queries T hr⟩
  · rintro ⟨hphase, hnext, ⟨hF, hcut⟩, hE⟩
    exact ⟨hcut, hphase, hnext, hF, hE.imp_right And.left⟩

end SystemAlgebra

module

public import RandomSystems.Converter.QueryBound.Defs

/-!
# Query bounds under restriction and serial composition

`InsideQueriesBounded.of_le` inherits a bound when replies are restricted.
`insideQueriesBounded_id` counts one inside query per outside input.
`InsideQueriesBounded.comp` composes total-query functions through the actual intermediate
transcript. `IsDDCFrom.insideQueriesBounded_of_domain` supplies a constant bound from a bounded
inside domain; domain preservation remains the existing `IsDDCFrom.mapsDomain` contract.
-/

@[expose] public section

namespace SystemAlgebra

-- Outside ports `O` expose `U`/`V`; inside ports `J` expose `X`/`Y`.
variable {O J : Type} {U V : O → Type} {X Y : J → Type}

/-- Restricting the replies of a system preserves every total inside-query bound. -/
lemma InsideQueriesBounded.of_le
    {α β : InsideOutsideSystem O J U V X Y} {k : ℕ → ℕ}
    (bound : InsideQueriesBounded α k)
    -- `hle` includes each reply of `β` among those of `α` at the same input history.
    (hle : ∀ xs y, y ∈ β xs → y ∈ α xs) : InsideQueriesBounded β k :=
  fun T hr => bound T (hr.mono hle)

/-- Identity forwards exactly one inside query for every received outside input. -/
lemma insideQueriesBounded_id : InsideQueriesBounded (idConverter J X Y) id := by
  intro T hr
  rw [insideQueries_eq_of_replies_id hr]
  exact le_rfl

/-- A bounded inside domain bounds all emitted queries, including a pending final query. -/
lemma IsDDCFrom.insideQueriesBounded_of_domain
    {E : List (Σ j, X j) → Prop} {F : List (Σ o, U o) → Prop} {b m : ℕ}
    {α : InsideOutsideSystem O J U V X Y} (ha : IsDDCFrom E F b α)
    -- `hE` bounds every admitted inside-query history by `m`.
    (hE : ∀ xs, E xs → xs.length ≤ m) : InsideQueriesBounded α (fun _ => m) := by
  intro T hr
  rcases ha.queries T hr with empty | admitted
  · rw [empty]
    exact Nat.zero_le m
  · exact hE _ admitted

/-- Serial query bounds compose in the order of the outer then inner converter. -/
lemma InsideQueriesBounded.comp
    -- `M` labels the intermediate query/reply families `Xm`, `Ym`.
    {M : Type} {Xm Ym : M → Type}
    {E : List (Σ j, X j) → Prop} {F : List (Σ m, Xm m) → Prop}
    {G : List (Σ o, U o) → Prop} {bβ bα : ℕ}
    {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}
    -- `hβ`, `hα` certify the exact domains needed by the serial transcript law.
    (hβ : IsDDCFrom F G bβ β) (hα : IsDDCFrom E F bα α)
    -- `kβ`, `kα` are the outer and inner total-query bounds.
    {kβ kα : ℕ → ℕ} (outer : InsideQueriesBounded β kβ) (inner : InsideQueriesBounded α kα)
    -- `mono` lets the inner cost absorb the bound on intermediate queries.
    (mono : Monotone kα) : InsideQueriesBounded (trim (serialM β α)) (kα ∘ kβ) := by
  intro T hr
  obtain ⟨Tb, Ta, hb, ha, ho, hm, hi⟩ := hβ.serial_transcripts hα hr
  -- The exposed queries are the inner queries; the inner inputs are the outer queries.
  calc
    (insideQueries (T.map Prod.snd)).length = (insideQueries (Ta.map Prod.snd)).length :=
      congrArg List.length hi.symm
    _ ≤ kα (outsideInputs (Ta.map Prod.fst)).length := inner Ta ha
    _ = kα (insideQueries (Tb.map Prod.snd)).length := congrArg (fun xs => kα xs.length) hm
    _ ≤ kα (kβ (outsideInputs (Tb.map Prod.fst)).length) := mono (outer Tb hb)
    _ = (kα ∘ kβ) (outsideInputs (T.map Prod.fst)).length :=
      congrArg (fun xs => kα (kβ xs.length)) ho

end SystemAlgebra

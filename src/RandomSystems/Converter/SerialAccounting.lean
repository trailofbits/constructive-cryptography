import RandomSystems.Converter.Calls

/-!
# Aggregate work of certified serial converters

The serial composite `trim (serialM β α)`, in category order: the outer converter `β` receives
the outside inputs `o(u)` and issues intermediate queries `m(x)`; the inner converter `α`
receives those and issues the exposed inside queries `j(z)`.

```text
        o(u)  ┌───┐  m(x)  ┌───┐  j(z)
  ───────────►│   ├───────►│   ├───────►
              │ β │        │ α │
  ◄───────────┤   │◄───────┤   │◄───────
       o ⇒ v  └───┘  m ⇒ y └───┘  j ⇒ w
```

On a partial transcript `T` of the composite, with `Tb` the outer component transcript,

```text
  ∑_{j(z) ∈ insideQueries T} work (j, z)  ≤  ∑_{m(x) ∈ insideQueries Tb} cost (m, x)
                                          ≤  budget (outsideInputs T),
```

the first step from a cost bound on every inner transcript, the second from an outer budget on
every outer transcript. A final pending query is already an output and is charged on both
sides. Costs may depend on query values, not only on port labels. Everything is derived from
the existing serial transcript laws; the converters and their domains are unchanged.

## Main results

* `IsDDCFrom.comp_query_charge_le`: exposed work is at most the inner costs of the actual
  intermediate queries
* `IsDDCFrom.comp_callConverter_query_count_le`: a direct inner call rule, one unit per query
* `IsDDCFrom.comp_query_charge_le_budget`: an input-only budget from a universal outer bound

Jost, Definition 2.2.2, printed p. 18, bounds a different quantity, the length of one run of
inside outputs: “There is a finite upper bound on the number of consecutive outputs of the form
(y, I′) ∈ X × Iin.” The bounds here are aggregate totals over a transcript.
-/

namespace SystemAlgebra

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}
  {E : List (Σ j, X j) → Prop} {F : List (Σ m, Xm m) → Prop}
  {G : List (Σ o, U o) → Prop} {bβ bα : ℕ}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}

/-- **Aggregate serial work**: if every partial transcript `Ta` of the inner converter satisfies

`∑_{j(z) ∈ insideQueries Ta} work (j, z) ≤ ∑_{m(x) ∈ outsideInputs Ta} cost (m, x)`,

then every partial transcript `T` of `trim (serialM β α)` has a transcript `Tb` of `β` with the
same outside inputs and

`∑_{j(z) ∈ insideQueries T} work (j, z) ≤ ∑_{m(x) ∈ insideQueries Tb} cost (m, x)`.

The charge runs over the intermediate queries `β` actually issued. A pending invocation is
included, since `hinner` quantifies over partial inner transcripts. -/
theorem IsDDCFrom.comp_query_charge_le (hβ : IsDDCFrom F G bβ β)
    (hα : IsDDCFrom E F bα α) (work : (Σ j, X j) → ℕ) (cost : (Σ m, Xm m) → ℕ)
    (hinner : ∀ Ta : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l)),
      Replies α (Ta.map Prod.fst) (Ta.map Prod.snd) →
      ((insideQueries (Ta.map Prod.snd)).map work).sum ≤
        ((outsideInputs (Ta.map Prod.fst)).map cost).sum)
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (trim (serialM β α)) (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ Tb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      ((insideQueries (T.map Prod.snd)).map work).sum ≤
        ((insideQueries (Tb.map Prod.snd)).map cost).sum := by
  -- Exposed work is the inner transcript's work (`hi`); the inner inputs are the outer
  -- queries (`hm`), so `hinner Ta` rewrites to the claim.
  obtain ⟨Tb, Ta, hb, ha, ho, hm, hi⟩ := hβ.serial_transcripts hα hr
  refine ⟨Tb, hb, ho, ?_⟩
  simpa only [hm, hi] using hinner Ta ha

/-- **Serial query count with a direct inner call rule**: if the inner converter is
`callConverter call F` and each invocation `u` issues an inside query only while it holds fewer
than `cost u` replies, on arbitrary reply lists `rs`,

`(call u rs).isRight → rs.length < cost u`,

then every partial transcript `T` of the composite has a transcript `Tb` of `β` with the same
outside inputs and

`|insideQueries T| ≤ ∑_{m(x) ∈ insideQueries Tb} cost (m, x)`.

The cost may depend on the whole intermediate query value, not only on its port. -/
lemma IsDDCFrom.comp_callConverter_query_count_le (hβ : IsDDCFrom F G bβ β)
    (call : (u : Σ m, Xm m) → List (Σ j, Y j) → Ym u.1 ⊕ (Σ j, X j))
    (cost : (Σ m, Xm m) → ℕ)
    (hphase : ∀ u replies, (call u replies).isRight = true → replies.length < cost u)
    (hα : IsDDCFrom E F bα (callConverter call F))
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (trim (serialM β (callConverter call F)))
      (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ Tb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      (insideQueries (T.map Prod.snd)).length ≤
        ((insideQueries (Tb.map Prod.snd)).map cost).sum := by
  -- `comp_query_charge_le` with unit work, whose sum is a length; `hinner` is
  -- `callConverter_query_count`: `|insideQueries Ta| ≤ ∑_{m(x) ∈ outsideInputs Ta} cost (m, x)`.
  simpa only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] using
    hβ.comp_query_charge_le hα (fun _ => 1) cost
    (fun Ta ha => by
      simpa only [List.map_const', List.sum_replicate, smul_eq_mul, mul_one] using
        callConverter_query_count call cost hphase F Ta ha) hr

/-- **Input-only serial budget**: under the inner hypothesis of `comp_query_charge_le` and an
outer bound on every partial transcript `Tb` of `β`,

`∑_{m(x) ∈ insideQueries Tb} cost (m, x) ≤ budget (outsideInputs Tb)`,

every partial transcript `T` of the composite satisfies

`∑_{j(z) ∈ insideQueries T} work (j, z) ≤ budget (outsideInputs T)`.

The outer bound is assumed on all outer transcripts, not inferred from one execution, and is
not replaced by a worst-case product of consecutive-query bounds. -/
lemma IsDDCFrom.comp_query_charge_le_budget (hβ : IsDDCFrom F G bβ β)
    (hα : IsDDCFrom E F bα α) (work : (Σ j, X j) → ℕ) (cost : (Σ m, Xm m) → ℕ)
    (budget : List (Σ o, U o) → ℕ)
    (hinner : ∀ Ta : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l)),
      Replies α (Ta.map Prod.fst) (Ta.map Prod.snd) →
      ((insideQueries (Ta.map Prod.snd)).map work).sum ≤
        ((outsideInputs (Ta.map Prod.fst)).map cost).sum)
    (houter : ∀ Tb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) →
      ((insideQueries (Tb.map Prod.snd)).map cost).sum ≤
        budget (outsideInputs (Tb.map Prod.fst)))
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (trim (serialM β α)) (T.map Prod.fst) (T.map Prod.snd)) :
    ((insideQueries (T.map Prod.snd)).map work).sum ≤
      budget (outsideInputs (T.map Prod.fst)) := by
  -- work (T) ≤ cost (Tb) by `comp_query_charge_le`; cost (Tb) ≤ budget (outsideInputs Tb)
  -- by `houter`, and `outsideInputs Tb = outsideInputs T` (`ho`).
  obtain ⟨Tb, hb, ho, hw⟩ := hβ.comp_query_charge_le hα work cost hinner hr
  exact hw.trans (ho ▸ houter Tb hb)

end SystemAlgebra

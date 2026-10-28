import RandomSystems.Converter.Calls

/-!
# Aggregate work of certified serial converters

```text
outside inputs ──β──► intermediate queries ──α──► exposed inside queries
                   cost (port, query)           work (port, query)
```

`comp_query_charge_le` bounds actual composite work by the inner costs charged to the
outer converter's intermediate queries. A final pending query is already an output and
is included in the charge. `comp_query_charge_le_budget` additionally requires an outer
bound for every reply transcript; it cannot infer an input-only bound from one execution.

Jost, Definition 2.2.2, printed p. 18: “There is a finite upper bound on the number of
consecutive outputs”. That is a converter capability, not an aggregate-cost theorem.
The results here derive aggregate accounting from the existing serial transcript laws
and explicit component inequalities, without changing Jost's converter structure or the
selected input domains. Costs may depend on query values as well as interface labels.
-/

namespace SystemAlgebra

variable {O M J : Type} {U V : O → Type} {Xm Ym : M → Type} {X Y : J → Type}
  {E : List (Σ j, X j) → Prop} {F : List (Σ m, Xm m) → Prop}
  {G : List (Σ o, U o) → Prop} {bβ bα : ℕ}
  {β : InsideOutsideSystem O M U V Xm Ym} {α : InsideOutsideSystem M J Xm Ym X Y}

/-- The two component transcripts of a serial converter retain all intermediate and
exposed queries, including a final query whose reply has not arrived. -/
lemma IsDDCFrom.serial_transcripts (hβ : IsDDCFrom F G bβ β)
    (hα : IsDDCFrom E F bα α)
    {T : List ((Σ l, twoFam U Y l) × (Σ l, twoFam V X l))}
    (hr : Replies (trim (serialM β α)) (T.map Prod.fst) (T.map Prod.snd)) :
    ∃ (Tb : List ((Σ l, twoFam U Ym l) × (Σ l, twoFam V Xm l)))
      (Ta : List ((Σ l, twoFam Xm Y l) × (Σ l, twoFam Ym X l))),
      Replies β (Tb.map Prod.fst) (Tb.map Prod.snd) ∧
      Replies α (Ta.map Prod.fst) (Ta.map Prod.snd) ∧
      outsideInputs (Tb.map Prod.fst) = outsideInputs (T.map Prod.fst) ∧
      outsideInputs (Ta.map Prod.fst) = insideQueries (Tb.map Prod.snd) ∧
      insideQueries (Ta.map Prod.snd) = insideQueries (T.map Prod.snd) := by
  -- The existing partial serial invariant records the idle and pending cases alike.
  rw [replies_trim_iff] at hr
  obtain ⟨_, _, Tb, Ta, _, hb, _, ha, ho, hm, hi, _⟩ := hβ.serial_idle hα T hr
  exact ⟨Tb, Ta, hb, ha, ho, hm, hi⟩

/-- Actual serial work is bounded by the sum of input-dependent inner costs over the
outer converter's actual intermediate queries. Pending invocations are included by the
component hypothesis, which quantifies over every partial reply transcript. -/
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
  -- Match exposed work to the inner transcript and intermediate charges to the outer one.
  obtain ⟨Tb, Ta, hb, ha, ho, hm, hi⟩ := hβ.serial_transcripts hα hr
  refine ⟨Tb, hb, ho, ?_⟩
  simpa only [hm, hi] using hinner Ta ha

/-- A direct inner call rule supplies the aggregate hypothesis from its arbitrary-reply
phase bound. The cost can depend on the complete intermediate query value. -/
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
  -- Charge one unit per actual inner query, and reserve each invocation's advertised cost.
  simpa using hβ.comp_query_charge_le hα (fun _ => 1) cost
    (fun Ta ha => by simpa using callConverter_query_count call cost hphase F Ta ha) hr

/-- An input-only aggregate bound needs the outer cost inequality on every reply trace.
Neither the intermediate query values nor their exact domain are replaced by a worst-case
product of consecutive-query bounds. -/
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
  -- Apply the universal outer bound to the actual intermediate transcript.
  obtain ⟨Tb, hb, ho, hw⟩ := hβ.comp_query_charge_le hα work cost hinner hr
  exact hw.trans (ho ▸ houter Tb hb)

end SystemAlgebra

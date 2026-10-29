import RandomSystems.Converter.ParallelAll
import Tests.CompositionalCosts

/-!
# Canonical n-ary converters

Checks for `tensorAllL` on small families, with `t` for `true`, `f` for `false`:

* bound: `K = Empty` gives `∅.sup b = 0`; `K = Bool` with `b t = 2`, `b f = 3` gives
  `max = 3`, not `2 + 3 = 5`;
* routing: the raw rule `tensorAllRaw forwardRules` returns the inside reply at `t` outside at
  `t`; `canon` rejects an inside reply before any outside query;
* partial components: `partialFamily` (budgets `t ↦ 0`, `f ↦ 1`) has the certificate
  `IsDDCFrom.tensorAllL`, so a first query to `f` is answered and a first query to `t` is not.

```text
  ⟨t,()⟩(n) ──▶ ┌──────────────────────┐                   budget 0: undefined on every
                │ limitedForwarder 0   │                   nonempty history
                └──────────────────────┘
  ⟨f,()⟩(n) ──▶ ┌──────────────────────┐ ──▶ ⟨f,()⟩(n)     budget 1: one outside query
  ⟨f,()⟩ ⇒ m ◀─ │ limitedForwarder 1   │ ◀── ⟨f,()⟩ ⇒ m
                └──────────────────────┘
```
-/

namespace SystemAlgebra.Tests

noncomputable section

/-- The empty family of converters on unit alphabets, `emptyConverters : ∀ k : Empty, _`. Its
joint alphabets `Σ k, O k` and `Σ k, J k` are empty. -/
def emptyConverters : ∀ _k : Empty,
    InsideOutsideSystem Unit Unit (fun _ => Unit) (fun _ => Unit)
      (fun _ => Unit) (fun _ => Unit) :=
  fun k => nomatch k

-- `⨂ₖ` of the empty family has bound `∅.sup b = 0`.
example : IsDDC 0 (tensorAllL emptyConverters) := by
  have h : ∀ k : Empty, IsDDC 0 (emptyConverters k) := fun k => nomatch k
  -- `IsDDC.tensorAllL` gives the bound `Finset.univ.sup b`, which is `0` over `Empty`.
  simpa only [Finset.univ_eq_empty, Finset.sup_eq_bot_of_isEmpty, Nat.bot_eq_zero] using
    IsDDC.tensorAllL (b := fun _ : Empty => 0) h

namespace NaryParallelConverters

-- Any converters with bounds `b t = 2`, `b f = 3` on ℕ-valued ports: the joint bound is
-- `max 2 3 = 3`, although the sum is 5.
example (a : Bool → InsideOutsideSystem Unit Unit (fun _ => ℕ) (fun _ => ℕ)
    (fun _ => ℕ) (fun _ => ℕ)) (ha : ∀ k, IsDDC (if k then 2 else 3) (a k)) :
    IsDDC 3 (tensorAllL a) := by
  convert IsDDC.tensorAllL ha using 1
  -- `Finset.univ.sup b = sup {t, f} b = max 2 3 = 3`.
  norm_num [Fintype.univ_bool, Finset.sup_insert, Finset.sup_singleton]

/-- Raw forwarding rules, `forwardRules k = forwardAll` for each `k : Bool`: on the last input,
`()(n) ↦ inside ()(n)` and `() ⇒ n ↦ outside () ⇒ n`, on every nonempty history. This is a raw
rule, not a DDC: it also answers inadmissible histories, and no certificate is asserted for it;
only `canon` restricts it to admissible histories. -/
def forwardRules : Bool → InsideOutsideSystem Unit Unit (fun _ => ℕ) (fun _ => ℕ)
    (fun _ => ℕ) (fun _ => ℕ) :=
  fun _ => forwardAll Unit (fun _ => ℕ) (fun _ => ℕ)

-- Routing: after `⟨t,()⟩(7)` and the inside reply `⟨t,()⟩ ⇒ 11`, the raw rule replies
-- `⟨t,()⟩ ⇒ 11` outside: component `t` sees `h|t = [()(7), () ⇒ 11]` and forwards `11`.
example : tensorAllRaw forwardRules
    [⟨⟨none, ⟨true, ()⟩⟩, 7⟩, ⟨⟨some (), ⟨true, ()⟩⟩, 11⟩] =
      Part.some ⟨⟨none, ⟨true, ()⟩⟩, 11⟩ := by
  simp only [tensorAllRaw, relabel, tensorAllOutputs, tensorAllInputs, Equiv.symm_mk,
    Equiv.coe_fn_mk, parAll, List.map_cons, List.map_nil, List.getLast?_cons_cons,
    List.getLast?_singleton, forwardRules, forwardAll, restrict_cons_self, restrict, ↓reduceDIte,
    Part.map_some]

-- Canonicalization rejects an inside reply `⟨f,()⟩ ⇒ 11` before any outside query, although
-- the raw rule would forward it.
example : tensorAllL forwardRules [⟨⟨some (), ⟨false, ()⟩⟩, 11⟩] = Part.none := by
  apply if_neg
  intro ha
  -- At `[]` there is no reply, so only outside labels are admitted (`admitAfter none`).
  have hz := ((admissible_snoc (h := [])).mp ha).2.2
  change Admits (tensorAllRaw forwardRules) [] _ at hz
  rw [Admits, replyLabel_tensorAllRaw_nil] at hz
  cases hz

open CompositionalCosts

/-- A certified partial family, `partialFamily k = limitedForwarder (if k then 0 else 1)`
(`Tests.CompositionalCosts`): component `k` forwards like `forwardAll` while its outside
inputs `h` satisfy `1 ≤ |h| ≤ q_k`, and is undefined otherwise; `q_t = 0`, so `t` never
answers. -/
noncomputable def partialFamily : Bool → InsideOutsideSystem Unit Unit (fun _ => ℕ)
    (fun _ => ℕ) (fun _ => ℕ) (fun _ => ℕ) :=
  fun k => limitedForwarder (if k then 0 else 1)

/-- `⨂ₖ partialFamily k` is a DDC from `parallelAllInputs E` to `parallelAllInputs E`, with
`E k = queryDomain q_k` (`1 ≤ |h| ≤ q_k`) and bound `max 1 1 = 1`: each projection `h|k` is
`[]` or in `E k`. Since `E t` is empty, `t` may only stay untouched. -/
lemma partialFamily_isDDCFrom : IsDDCFrom
    (parallelAllInputs fun k : Bool => queryDomain (if k then 0 else 1))
    (parallelAllInputs fun k : Bool => queryDomain (if k then 0 else 1)) 1
    (tensorAllL partialFamily) := by
  -- `IsDDCFrom.tensorAllL` on the component certificates, bound `sup {t, f} (fun _ => 1) = 1`.
  convert IsDDCFrom.tensorAllL
    (fun k : Bool => limitedForwarder_isDDCFrom (if k then 0 else 1)) using 1
  · simp only [Fintype.univ_bool, Finset.sup_insert, Finset.sup_singleton, max_self]
  · rfl

-- The first query `⟨f,()⟩(7)` is answered: `h|f = [()(7)] ∈ queryDomain 1`, and `h|t = []`,
-- so the never-answering component `t` does not block the joint domain.
example : (tensorAllL partialFamily [⟨⟨none, ⟨false, ()⟩⟩, 7⟩]).Dom := by
  -- By the certificate, answering is membership in the joint domain after `[]`.
  apply (partialFamily_isDDCFrom.answers [] _ (replies_nil _)).mpr
  refine ⟨admitted_nil _, rfl, ?_, Or.inl rfl⟩
  simp only [outsideInputs, List.map_nil, List.nil_append, List.map_cons, splitIn,
    restrict_cons_self, restrict_nil]
  -- Nonempty, and each projection is in its domain or empty.
  refine ⟨List.cons_ne_nil _ _, fun k => ?_⟩
  cases k
  -- `f`: `|h|f| = 1 ≤ 1`.
  · right
    simp only [List.map_cons, List.map_nil, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
      restrict_cons_self, restrict_nil]
    norm_num [queryDomain]
  -- `t`: `h|t = []`.
  · left
    simp only [List.map_cons, List.map_nil, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
      restrict_cons_ne (show false ≠ true by intro h; cases h), restrict_nil]

-- The first query `⟨t,()⟩(7)` is not answered: `h|t = [()(7)]` is nonempty and
-- `queryDomain 0` requires `1 ≤ |h|t| ≤ 0`.
example : ¬ (tensorAllL partialFamily [⟨⟨none, ⟨true, ()⟩⟩, 7⟩]).Dom := by
  intro hd
  -- An answer would put the outside inputs in `parallelAllInputs E`.
  have hq := ((partialFamily_isDDCFrom.answers [] _ (replies_nil _)).mp hd).2.2.1
  simp only [outsideInputs, List.map_nil, List.nil_append, List.map_cons, splitIn,
    restrict_cons_self, restrict_nil] at hq
  -- Its `t`-projection `[()(7)]` is neither `[]` nor of length `≤ 0`.
  have ht := hq.2 true
  simp only [List.map_cons, List.map_nil, Equiv.sigmaAssoc, Equiv.coe_fn_mk,
    restrict_cons_self, restrict_nil] at ht
  norm_num [queryDomain] at ht

end NaryParallelConverters

#print axioms SystemAlgebra.IsDDC.tensorAllL
#print axioms SystemAlgebra.IsDDCFrom.tensorAllL
#print axioms SystemAlgebra.PDCBehavior.tensorAll_apply
#print axioms SystemAlgebra.PDCBehavior.tensorAll_ofDDC

end
end SystemAlgebra.Tests

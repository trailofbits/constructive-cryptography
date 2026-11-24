module

public import RandomSystems.Converter.ConditionalCall
public import RandomSystems.Typed.CallRuleFunctional

/-!
# Typed realization of conditional oracle calls

The conditional oracle-call converter of `RandomSystems.Converter.ConditionalCall`, attached to a
fixed oracle `f` on the inside interface `B`, computes on outside input `u = (o, x)` the pure
reply `pureReply u` when `branch u` holds and `answer u (j, f_j a)` with `(j, a) = request u`
otherwise.

## Main definitions

* `TypedConverter.conditionalCall`: certified typed converter over `callConverter` keeping
  `A.domain`, requiring nonempty oracle-branch request sequences to lie in `B.domain`

## Main results

* `TypedConverter.ofDDC_conditionalCallConverter_smul_ofFunction`: fixed-oracle behavior for any
  DDC certificate on `conditionalCallConverter`, via `ofDDC_callConverter_smul_ofFunction`
* `TypedConverter.conditionalCall_smul_ofFunction`: fixed-oracle behavior of
  `TypedConverter.conditionalCall`
-/

@[expose] public section

namespace SystemAlgebra

/-- **Conditional converter attached to a fixed oracle**: on each outside input `u = (o, x)`,
the converter computes `pureReply u` if `branch u`, and `answer u (j, f_j a)` where
`(j, a) = request u` otherwise, proved directly via `ofDDC_callConverter_smul_ofFunction`. -/
lemma TypedConverter.ofDDC_conditionalCallConverter_smul_ofFunction {A B : Interface}
    (branch : (Σ o, A.X o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, A.X o) → A.Y u.1)
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (ha : IsDDCFrom B.domain A.domain 1
      (conditionalCallConverter branch pureReply request answer A.domain))
    (f : ∀ j, B.X j → B.Y j) :
    TypedConverter.ofDDC
        (conditionalCallConverter branch pureReply request answer A.domain) ha •
        TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u =>
        if branch ⟨o, u⟩ then pureReply ⟨o, u⟩
        else answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) := by
  apply TypedConverter.ofDDC_callConverter_smul_ofFunction
    (conditionalCall branch pureReply request answer) ha f
    (fun o u =>
      if branch ⟨o, u⟩ then pureReply ⟨o, u⟩
      else answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩)
    (fun u => if branch u then [] else [request u])
  · intro u n hn
    by_cases hb : branch u
    · simp only [hb, ↓reduceIte, List.length_nil, Nat.not_lt_zero] at hn
    · have hn0 : n = 0 := by
        simp only [hb, ↓reduceIte, List.length_singleton] at hn
        omega
      subst n
      simp only [hb, ↓reduceIte, List.take_zero, List.map_nil, conditionalCall,
        List.getElem_cons_zero]
  · intro u
    by_cases hb : branch u
    · simp only [hb, ↓reduceIte, conditionalCall]
    · simp only [hb, ↓reduceIte, List.map_singleton, conditionalCall]

/-- On outside input `u`, reply `pureReply u` immediately when `branch u` holds; otherwise query
`request u = (j, a)` once and return `answer u (j, y)` on reply `y`. Keeps the caller's outside
domain `A.domain`, requiring every nonempty sequence of oracle-branch requests to lie in
`B.domain`. -/
noncomputable def TypedConverter.conditionalCall {A B : Interface}
    (branch : (Σ o, A.X o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, A.X o) → A.Y u.1)
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (hmap : ∀ us, A.domain us → conditionalRequests branch request us ≠ [] →
      B.domain (conditionalRequests branch request us)) :
    TypedConverter A B :=
  TypedConverter.ofDDC
    (conditionalCallConverter branch pureReply request answer A.domain)
    (conditionalCallConverter_isDDCFrom branch pureReply request answer
      A.nonempty_prefix.2 hmap)

/-- Attaching `TypedConverter.conditionalCall` to a fixed oracle `f` evaluates `pureReply` on
inputs satisfying `branch` and `answer u (j, f_j a)` with `(j, a) = request u` otherwise. -/
lemma TypedConverter.conditionalCall_smul_ofFunction {A B : Interface}
    (branch : (Σ o, A.X o) → Prop) [DecidablePred branch]
    (pureReply : (u : Σ o, A.X o) → A.Y u.1)
    (request : (Σ o, A.X o) → Σ j, B.X j)
    (answer : (u : Σ o, A.X o) → (Σ j, B.Y j) → A.Y u.1)
    (hmap : ∀ us, A.domain us → conditionalRequests branch request us ≠ [] →
      B.domain (conditionalRequests branch request us))
    (f : ∀ j, B.X j → B.Y j) :
    TypedConverter.conditionalCall branch pureReply request answer hmap •
        TypedSystem.ofFunction f =
      TypedSystem.ofFunction (fun o u =>
        if branch ⟨o, u⟩ then pureReply ⟨o, u⟩
        else answer ⟨o, u⟩ ⟨(request ⟨o, u⟩).1, f (request ⟨o, u⟩).1 (request ⟨o, u⟩).2⟩) :=
  TypedConverter.ofDDC_conditionalCallConverter_smul_ofFunction
    branch pureReply request answer _ f

end SystemAlgebra

# Counting and event-mass leaves

Use this route only after an H, CE, coupling, identical-until-bad, or direct
argument has produced a concrete mass, fiber-cardinality, disagreement, or
finite-sum obligation.

## Fix the probability statement

Record the distribution, its nonnegativity or probability proof, the exact
event, decidability requirements, fixed versus quantified variables, and the
bound required by the consuming theorem.

For a finite family of events, the live generic union endpoint is
`Probability.probBad_iUnion_le` in `Probability.StatisticalDistance`:

```lean
theorem probBad_iUnion_le
    {D : Distribution A} (hD : D.NonNeg)
    (B : A → Prop) (P : ι → A → Prop)
    (hB : ∀ a, B a → ∃ p, P p a) :
    probBad D B ≤ ∑ p, D.evalPred (P p)
```

Supply the event cover separately from each individual mass estimate. Do not
cite the removed `RandomSystems.CR18.mass_biUnion_le` or
`SwitchingLemma.lean` API.

## Respect the caller's quantifiers

- An H weighted-cell endpoint requires an ideal cell-mass bound for every
  pair-admissible environment.
- Conditional equivalence requires one bound on the supremum winning
  probability of the blind game; `PDG.supWinProb_le` reduces this to every
  winner.
- A coupling leaf uses the chosen joint law and its disagreement event.
- Identical-until-bad uses the source law shared by the two pushforwards.

Do not exchange these scopes without a proved bridge.

## Choose the least lossy calculation

Before a union bound, consider exact fibers, disjoint partitions, sequential
conditional products, system-factor ratios, expectation of a transcript
defect, symmetry/orbit counting, or direct disagreement mass. Keep the chain
visible:

```text
event membership
-> cover or fiber statement
-> cardinality/mass identity
-> numerical inequality
-> consuming RS certificate
```

Check casts among `Nat`, `NNReal`, and `Real`, and verify the final RS root's
axioms rather than only the counting lemma.

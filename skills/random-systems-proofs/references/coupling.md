# Honest coupling route

Use a coupling when a nonnegative joint law of the two compared observations
has tractable disagreement and proved marginals.

## Live probability surface

`Probability.Coupling` distinguishes:

- `IsCoupling J X Y`, the two-marginal predicate for a joint distribution;
- `Probability.Coupling X Y`, the bundled honest coupling carrying
  nonnegativity and marginal proofs;
- `Coupling.prDisagree`, the disagreement probability;
- `coupling_bound`, which proves `statDist X Y ≤ C.prDisagree`; and
- `optimal_coupling_exists`, which attains equality for nonnegative equal-weight
  laws.

The usual proof obligations are:

```text
joint law
├── nonnegativity
├── first marginal = X
├── second marginal = Y
└── disagreement mass <= epsilon
```

For two laws with the same pushforward along a map, inspect
`Probability.FiberCoupling`:

- `exists_nonneg_coupling_of_fTransform_eq` gives an honest fiber-supported
  coupling under nonnegativity and equal-weight hypotheses;
- `exists_coupling_of_fTransform_eq` is the signed-carrier statement and must
  not be passed to an honest-coupling theorem without proving nonnegativity.

## Interaction boundary

A maximal coupling of two completed transcript laws is not automatically a
causal online coupling of interactive systems. State whether the proof needs a
law-level joint, a shared-source identical-until-bad argument, or a sequential
construction. For shared-source maps, prefer
`statDist_fTransform_le_mass_of_eq_off` when it exactly matches the proof.

Keep coupling separate from conditional equivalence, representative selection,
and signed virtual joints. They can contribute to the same comparison only
through explicit bridge theorems.

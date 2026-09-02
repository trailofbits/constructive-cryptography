# H-coefficient route

Use this route when the two systems' transcript-system factors satisfy a
one-sided ratio, possibly partitioned into finitely many defect cells.

## Live layers

`Probability.StatisticalDistance` owns the distribution-level kernels,
including finite-support ratio, expectation, partition, equality-on-good, and
pushforward forms. `RandomSystems.TranscriptFactor` proves that a concrete
transcript law is a common nonnegative environment factor times the system
factor. `RandomSystems.Technique.HCoefficient` combines those facts and takes
the supremum over pair-admissible deterministic environments.

The current RS endpoints are:

- `PDS.trLaw_partition_finiteSupport_le` for one environment;
- `PDS.advantage_le_weighted_cells` for finitely many ratio-defect cells; and
- `PDS.advantage_le_of_ratio` for one uniform ratio defect.

## Choose the narrowest endpoint

```text
uniform system-factor ratio
  -> advantage_le_of_ratio

finite cell partition + per-cell ideal mass bounds
  -> advantage_le_weighted_cells

one fixed admissible environment
  -> trLaw_partition_finiteSupport_le
```

The ratio orientation is:

```text
(1 - eps cell) * transcriptSystemFactor T transcript
  <= transcriptSystemFactor S transcript
```

Do not swap `S` and `T` without a proved weight/symmetry bridge.

## Principal obligations

- nonnegativity of both PDS laws;
- equal weights, and ideal weight one for the uniform endpoint;
- the pointwise system-factor ratio;
- for weighted cells, a uniform ideal transcript-mass bound for every
  pair-admissible environment; and
- the finite cell type and decidable equality required by the endpoint.

This current route does not require the obsolete fixed-query `PFunPDS`
`HTechnique/Derivation` API. Do not cite old `adv_le_of_fixedQuery_eq_on_good`
or `htechnique_*` tactics unless a live import and signature are first found.

Use [transcript-factorization.md](transcript-factorization.md) when proving the
system-factor formulas, and [counting.md](counting.md) when discharging cell
mass bounds.

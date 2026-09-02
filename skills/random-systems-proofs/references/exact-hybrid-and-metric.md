# Exact reshaping, hybrids, and metric bounds

Use this route before introducing a game, bad event, or coupling when a direct
equality or standard metric inequality already exposes the desired leaf.

## Fixed-interface advantage

`RandomSystems.Distance` owns:

- `PDS.advantage` for pair-admissible compatible stopping DDEs;
- `PDS.advantageOnDomain` for a named domain and globally halting DDEs;
- `PDS.Adv` for the common-domain presentation;
- `advantage_eq_advantageOnDomain` and related restriction bridges; and
- the corresponding self, weight-sensitive symmetry, and triangle theorems.

Do not write `Adv(S,T)` until the common-domain hypotheses required by that
notation and theorem are in scope. Do not use symmetry unless equal weights
have been proved.

## Standard reshaping moves

- Use `PDS.advantageOnDomain_triangle` or `PDS.Adv_triangle` for a named
  intermediate system.
- Use `Probability.statDist_fTransform_le` for deterministic post-processing.
- Use `Probability.statDist_fTransform_le_mass_of_eq_off` when two readings of
  one nonnegative source law agree outside an explicit bad event.
- Use `Probability.statDist_le_of_fTransform_eq` or an extension theorem only
  with its exact hypotheses.
- Use exact filter, relabel, observation, or transcript-law equalities before
  applying an inequality.

A hybrid must be named and both legs must retain the original observation
scope. Data processing applies to a deterministic map of one execution law;
information revealed during interaction may alter later queries and requires a
different system model or simulation argument.

## Layer boundary

Converter attachment and parallel-context non-expansion live under
`RandomSystems.Converter` and the CC integration surface. Use this reference
for the fixed-interface RS leaf after the CC proof identifies it; do not smuggle
resource composition into a `PDS` triangle calculation.

# Bounded observation restriction

Use this route when a common-domain theorem needs a finite compatible stopping
observer but the ambient DDE carrier is not globally bounded.

`RandomSystems.ObservationRestriction` implements Lanzenberger's finite-system
observation scope without changing the system carrier. Given a reference DDS,
an environment, and a round bound,
`System.DDE.boundedDomainRestriction` retains exactly queries whose reconstructed
complete query history lies in the reference DDS domain.

## Live properties

- `boundedDomainRestriction_halts` supplies the explicit stopping bound.
- `envConsistent_boundedDomainRestriction` and
  `boundedDomainRestriction_compatible` establish the observer equations and
  compatibility with systems sharing the reference domain.
- `trN_boundedDomainRestriction_eq` preserves bounded interactions.
- `trLaw_boundedDomainRestriction_eq` preserves the stabilized transcript law
  under the theorem's compatibility, domain, stopping, and bound hypotheses.
- `PDS.advantage_le_advantageOnDomain_of_reference`,
  `advantage_le_advantageOnDomain`, and
  `advantage_eq_advantageOnDomain` lift the restriction to advantage.

## Boundary

This is a literal DDE observation restriction. It is not converter attachment,
MauRen11 choice setting, total completion, or support-wise absorption. Choose a
reference DDS from an actual common-domain witness and retain the explicit
round/stopping hypotheses.

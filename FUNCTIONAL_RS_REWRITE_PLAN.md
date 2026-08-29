# ResourceAlgebra migration: acceptance gate

This plan remains only while the current migration candidate is awaiting
verification. The architecture and module ownership are in `THEORY.md` and
`README.md`.

## Candidate boundary

The candidate has one carrier-independent `ResourceAlgebra`, one optional
query-indexed DDC implementation, one ambient `RandomSystemsCC` instance, and
CBC-MAC as a consumer. `RandomSystems` remains a standalone fixed-interface
library. The common-domain carrier is an embedded source-specific
restriction, not another ambient model.

The previous flat action, independent parallel classes, MR11 surface, and
Random Systems compatibility tree are archived rather than exported. The
committed baseline is on `codex/legacy-pre-resource-algebra`; the final
pre-cleanup worktree is on
`codex/pre-cleanup-resource-algebra-snapshot`.

Jost's basic typed attachment, ordered parallel, and context-insensitivity
laws are represented. The MR11-dependent implementation of Jost's separate
Section 4.2 context-restricted construction theory was archived, not ported.
No acceptance claim may say that theorem family is present.

Event algebra, unfinished FROST and sponge proofs, and the separate
`informalization/` worktree are outside this migration.

## Pending verification

Review the candidate in these six layers:

- carrier-independent resources, converters, specifications, attachment,
  metric, ordered tensor, and `ResourceAlgebra` laws;
- exact and approximate construction, relaxation, star, contexts, finite
  converter tuples, and multiparty assembly;
- fixed-interface Random Systems and its distance and H-coefficient results;
- ambient DDC functions, attachment, serial, parallel, observation, quotient
  action, and common-domain restriction;
- the sole `RandomSystemsCC` instantiation; and
- CBC objects, attachment equations, probability bound, distance, and final
  construction.

For every layer, check source correspondence, hypotheses, equality or
quotient, partiality, naming, ownership, imports, ergonomics, and one
representative consumer.

Run the focused and downstream builds prescribed by `AGENTS.md`, including:

```sh
lake build AbstractCryptography ConstructiveCryptography
lake build ConstructiveCryptographyMultipartyComputation
lake build RandomSystems RandomSystemsConverter RandomSystemsCC
lake build RandomSystemsCCInstantiationTests Applications.CBCMAC
lake build AbstractCryptographySelectedSurfaceTests
lake build AbstractCryptographyProofAutomationTests
lake build AbstractCryptographyCalcChainTests
lake build AbstractCryptographyControlledNaturalLanguageTests
lake build AbstractCryptographyConstructionWorkflowTests
lake build ConstructiveCryptographySelectedSurfaceTests
scripts/publicDependencyAudit.sh
```

Also check public axioms, forbidden proof placeholders and limit overrides,
source dependency closures, physical absence of retired modules, uniqueness
of the ambient instance and parallel foundation, public naming and
documentation, `git diff --check`, and required sibling consumers.

Do not commit, merge, or push until this gate is accepted. After acceptance,
remove this plan, perform one final diff review, and commit the verified tree.

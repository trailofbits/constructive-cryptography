# MPC and FROST: active remaining work

This plan contains only the unresolved concrete FROST security work. The
abstract AC/CC and Random Systems architecture is documented in `THEORY.md`.

## Target

Instantiate the carrier-independent FROST statements over the current
query-indexed random-system carrier and discharge the DKG, signing, and
unforgeability leaves:

```text
RandomSystems
  -> RandomSystems.Converter
  -> RandomSystemsCC
  -> ConstructiveCryptography.MultipartyComputation
  -> Applications.Frost.Construction
```

The governing sources are MauRen16 for construction, LiuMau20 for the
multiparty statement, RFC 9591 for FROST, and the selected DKG and
threshold-signature security papers cited by the owning declarations. Read
the source pages before fixing a simulator or reduction hypothesis.

## Current abstract surface

Reuse these declarations rather than introducing another model:

- `Finite.ConverterTuple` for the party converters;
- `ConstructsForAll` and `ConstructsForAdversaryStructure` for dishonest-set
  quantification;
- `zStar` for closure under an explicitly selected endomorphism submonoid;
- `AdversaryStructure`, `Q3`, and `threshold` for corruption patterns;
- `gameSpec` for bounded test outputs;
- `constructs_keys_of_simulators` and
  `constructs_tss_from_keys_of_simulators` for the two stages;
- `constructs_and_gameSpec_of_simulators`,
  `threshold_constructs_and_gameSpec`, and `threshold_unforgeability` for
  final assembly.

The assumed broadcast and authenticated channels are base resources. Their
construction is outside this plan. The dishonest-majority FROST endpoint is
`threshold_unforgeability`; the `Q3` result remains available only for a
future broadcast de-idealization.

## Remaining concrete work

- Define the assumed network, threshold-key, and threshold-signing resources
  as query-indexed normalized random systems, with party routing in their
  interface types.
- Define DKG, signing, and simulator converters as current branch-finite DDCs.
  Prove their attachment equations as function equalities and obtain query
  bounds through the existing constructors.
- Complete the bias-absorbing key ideal, prove the RO-programming coupling,
  and discharge `constructs_keys_of_simulators`.
- Define the gated signer resource, prove the real/ideal transcript coupling,
  and discharge `constructs_tss_from_keys_of_simulators` using the existing
  FROST correctness algebra.
- State forgery tests as bounded functions on the ideal resource, prove the
  OMDL/AOMDL reduction and forking bound, and establish membership in
  `gameSpec`. The hardness assumption remains explicit.
- Apply `constructs_and_gameSpec_of_simulators`, then expose
  `threshold_unforgeability`. Use `threshold_constructs_and_gameSpec` only
  when the additional `Q3` conclusion is needed.

## Modeling constraints

- Use only the selected `ResourceAlgebra` and ambient random-system action.
- Do not introduce a second fixed-interface carrier, universal resource type, or
  second parallel operation.
- Correlation among dishonest parties is represented by selected joint
  endomorphisms or by the resource, not another tuple-action model.
- Keep scalar construction error and bounded game-test output distinct.
- Keep deterministic FROST algebra separate from probabilistic carrier
  arguments.
- Do not import or recreate retired MR11 or compatibility surfaces.
- Do not raise heartbeat limits or enumerate `Fin n` for a generic theorem.

## Completion criteria

The plan is complete when the three concrete leaves and final assembly contain
no `sorry`, the only cryptographic assumption is the named hardness
hypothesis, every carrier and quotient obligation uses the current APIs, and
the focused plus downstream verification gates pass.

Delete this file when those conditions hold and move lasting guidance to
source documentation or `THEORY.md`.

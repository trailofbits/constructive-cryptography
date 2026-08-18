# Sponge indifferentiability: active concrete proof

This file contains only unresolved work. General AC proof guidance is in
`LIBRARY_GUIDE.md`; operational rules are in `AGENTS.md`.

## Target

Instantiate `Applications.Sponge.sponge_indifferentiable` for the BDPV
algebraic sponge: construct a random oracle from a public random permutation
with a capacity-collision bound of order `N² / |F|^c`.

The live abstract endpoint is deliberately generic:

```lean
Indifferentiable H error RPerm RO
```

The concrete random permutation, random oracle, sponge converter, BDPV
simulator, query budget, and distance proof belong in `RandomSystemsCC`.

Primary authority: Bertoni–Daemen–Peeters–Van Assche, EUROCRYPT 2008, together
with MauRen16's indifferentiability-to-construction endpoint. Re-read the exact
simulator and bound before fixing Lean definitions.

## Fixed modeling direction

- The real resource is a public random permutation.
- The real converter is deterministic once that permutation is fixed.
- The ideal resource is a random oracle.
- The ideal converter is the probabilistic BDPV simulator; its capacity coins
  are internal simulator randomness, not an extra public resource.
- Public permutation access remains visible to the distinguisher in both
  worlds.
- The final AC statement is obtained through the generic
  `Indifferentiable.construct`; do not introduce a sponge-specific duplicate
  construction predicate.

These choices must be rechecked against the current fixed-signature RS API
before implementation. Historical typed-resource prototypes are not evidence.

## Open work

### 1. Freeze signatures and query accounting

Define fixed signatures for:

- the public forward/inverse permutation interface;
- the sponge hash interface;
- the ideal random-oracle interface;
- the simulator's access to the ideal oracle.

State exactly what `N` counts: permutation queries, oracle queries, total
converter steps, or a proved transformation among them. Prove applicability
and output-signature preservation for every converter.

### 2. Define the concrete worlds

1. Define `RPerm` and `RO` on the selected behavioral quotient.
2. Define the sponge converter realizing `Applications.Sponge.hash`.
3. Prove the functional-core/converter correspondence.
4. Define the BDPV simulator as a legal probabilistic reactive converter.
5. Prove converter well-formedness, totality, and query-budget bounds.

### 3. Prove the simulator invariants

State and prove the graph/table invariants needed by the forward and inverse
permutation branches:

- consistency with all previous oracle answers;
- injectivity of assigned permutation points;
- freshness of capacity values on the good event;
- preservation under every simulator transition;
- correspondence between the table and the observable transcript.

Keep the invariant in one named structure or predicate. Do not scatter
slightly different versions across transition lemmas.

### 4. Establish transcript laws and the bad-event bound

1. Define the extended transcript/reveal used by the proof.
2. Define the capacity-collision bad event.
3. Show equality or the required ratio identity on good transcripts.
4. Bound bad mass by the exact product expression from BDPV.
5. Derive the advertised quadratic upper bound as a separate arithmetic
   corollary.
6. Connect the transcript statement to the selected RS distinguishing metric.

Use the standard section order from `LIBRARY_GUIDE.md`:

```text
Model
Representatives
TranscriptExtension
BadEvent
GoodRatio
BadMass
MainLemma
ConstructionOrReduction
```

The combinatorics and simulator invariant remain explicit; only the final
distance/construction shell should be automated.

### 5. Assemble the AC theorem

1. Package the simulator in the selected simulator submonoid.
2. Prove `edist (sponge • RPerm) (simulator • RO) ≤ error`.
3. build `Indifferentiable H error RPerm RO`;
4. apply `Applications.Sponge.sponge_indifferentiable`;
5. expose both the exact product bound and the simpler quadratic corollary.

## Reuse rules

Search the current RS tree before adding probability or counting lemmas.
Likely reusable areas include finite-distribution pushforwards, statistical
distance data processing, transcript factorization, permutation fiber counts,
falling-factorial/product identities, and union bounds. Upstream a helper only
when it is representation-independent and has at least two consumers.

Do not revive deleted `ResourceTheory`, `ProtocolIndifferentiable`, or old
`RandomSystemsCC.Sponge` APIs. Build against the live fixed-signature quotient
and converter action.

## Completion criteria

The concrete proof is complete only when:

- all real/ideal/simulator systems are live RS definitions;
- applicability, totality, quotient congruence, and cost/query bounds are
  proved;
- simulator invariants and the capacity-collision bound contain no `sorry`;
- the distance theorem is connected to the AC metric without a global
  instance diamond;
- the final construction uses the generic AC indifferentiability endpoint;
- focused RS, AC application, and downstream builds pass under ordinary
  heartbeat limits.

Delete this file when those conditions hold. Move reusable proof guidance to
`LIBRARY_GUIDE.md` or `AGENTS.md`, not to a completion log.

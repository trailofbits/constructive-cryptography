# Constructive Cryptography and Random Systems in Lean

A Lean 4 library formalizing Maurer-style Constructive Cryptography,
fixed-interface Random Systems, and their formal connection.
This repository is the theory backend: concrete cryptographic applications
belong in separate Lake projects that import it through Git.

> **Status.** This is an active research library without a tagged release.
> Downstream projects should pin a commit for reproducible proofs.

## Use as a dependency

Add the repository to the downstream project's `lakefile.lean`:

```lean
require ConstructiveCryptography from git
  "https://github.com/trailofbits/constructive-cryptography.git" @ "main"
```

The dependency name is `ConstructiveCryptography`, matching the Lake package.
The current tree uses:

```text
leanprover/lean4:v4.33.1
```

Use the same value in the downstream `lean-toolchain`, then fetch the
dependency and Mathlib cache:

```sh
lake update ConstructiveCryptography
lake exe cache get
```

Tracking `main` follows the latest theory backend. Replace `main` with a
release tag or commit hash when reproducibility matters.

## Modules

| Module | Description |
|---|---|
| `Probability` | Finite distributions, expectation, statistical distance, couplings, counting, and universal hashing |
| `ConstructiveCryptography` | The MR16/Jost/Liu resource algebra, specifications, exact and approximate construction, distance, ordered parallel composition, notation, and proof language |
| `ConstructiveCryptography.MultipartyComputation` | Generic multiparty converter families and adversary structures |
| `RandomSystems` | Fixed-interface DDSs, DDEs, PDSs, uniform functions and permutations, distance, parallel composition, and proof techniques |
| `RandomSystems.TranscriptFactor` | Exact factorization of fixed-interface transcript laws and filtered function-evaluator system factors |
| `RandomSystems.Converter` | Query-indexed DDCs, attachment, serial composition, cumulative random systems, the scoped categorical action, and the common-domain bridge |
| `Rendering.Widget` | Optional diagrams for Constructive Cryptography declarations |

## Architecture

Arrows mean “imports.”

```text
ConstructiveCryptography.MultipartyComputation
└── ConstructiveCryptography

RandomSystems.Converter
└── RandomSystems
    └── Probability
```

The dependency boundary is strict:

- `ConstructiveCryptography` defines the resource algebra without
  importing Random Systems;
- `RandomSystems` is usable without converters or Constructive Cryptography;
- `RandomSystems.Converter` is an optional extension of the standalone
  Random Systems layer;
- the probabilistic-converter category and `RandomSystemsCC` adapter are being
  developed separately and are not exported by this release boundary;
- no production theory module imports an application.

## Documentation

- [`THEORY.md`](THEORY.md) describes the mathematical objects, operations,
  laws, and layer boundaries.
- [`CC_BY_HAND.md`](CC_BY_HAND.md) reconstructs the development in dependency
  order.

## Development

```sh
git clone https://github.com/trailofbits/constructive-cryptography.git
cd constructive-cryptography
lake exe cache get
lake build
lake build RandomSystemsConverter
lake build ConstructiveCryptographyTests
lake build RandomSystemsTests
```

Tests are grouped by owning theory under `Tests/` and are never re-exported
by public roots. Contributor requirements for source fidelity, naming,
documentation, and verification are in [`AGENTS.md`](AGENTS.md).

## References

- Ueli Maurer and Renato Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016.
- Daniel Jost, *On Generalizations of Composable Security*, ETH Zurich, 2020.
- Chen-Da Liu-Zhang and Ueli Maurer, *Synchronous Constructive Cryptography*,
  TCC 2020.
- Chen-Da Liu-Zhang, *Multi-Party Computation: Definitions, Enhanced Security
  Guarantees and Efficiency*, ETH Zurich, 2021.
- David Lanzenberger, *A Theory of Random Systems, Games, and Hardness
  Amplification*, ETH Zurich, 2023.
- Ueli Maurer, *Indistinguishability of Random Systems*, EUROCRYPT 2002.

The exact source-to-declaration mapping and modeling qualifications are
recorded in [`THEORY.md`](THEORY.md).

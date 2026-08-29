# Constructive Cryptography

A Lean 4 formalization of Maurer-style Abstract and Constructive Cryptography,
with a fixed-interface Random Systems library and a query-indexed random-system
instantiation of the abstract construction calculus.

## Dependency structure

```text
Applications
    -> ConstructiveCryptography
    -> AbstractCryptography

Applications.CBCMAC
    -> RandomSystemsCC -> AbstractCryptography
                       -> RandomSystems.Converter -> RandomSystems
```

`RandomSystems` has no dependency on the abstract AC/CC layers. It can be
imported alone for fixed-interface random-system proofs. Converter attachment is
an optional extension, and the concrete AC/CC adapters live above both layers.

## Public roots

| Import | Purpose |
|---|---|
| `AbstractCryptography` | Carrier-independent specifications, constructions, resource algebra, metrics, and relaxations |
| `ConstructiveCryptography` | MR16-track exact and approximate construction notation and composition |
| `RandomSystems` | Fixed-interface DDS, DDE, PDS, observation, equivalence, distance, ordered parallel composition, and partial H-coefficient bounds |
| `RandomSystems.Converter` | Branch-finite DDCs, attachment, serial and ordered parallel composition, observation factorization, probability action, and common-domain bridges |
| `RandomSystemsCC` | The single `ResourceAlgebra` instance for query-indexed interfaces, DDCs, and normalized random systems, plus common-domain non-expansion |
| `Applications.CBCMAC` | CBC-MAC resources, converters, attachment equations, probability bound, and CC construction |

## Module ownership

- `AbstractCryptography/Categorical.lean` owns the carrier-independent
  interface-indexed functor, fibre distance, and basic construction relation.
  `AbstractCryptography/Categorical/ResourceAlgebra.lean` adds the selected
  ordered resource parallel and its non-expansion laws.
- The `RandomSystems` root owns only fixed-interface Random Systems
  mathematics. It does not import converters, AC, CC, or applications.
- `RandomSystems/Converter.lean` is the optional query-indexed DDC root. Its
  imported modules under `RandomSystems/Converter/` own the concrete
  interface category, DDCs, attachment, and induced random-system functor,
  but no construction judgment.
- `RandomSystemsCC/` owns the abstract-layer instances. Focused concrete
  consequences, such as multiparty converter decompositions, are imported
  directly rather than re-exported by the root.
- `RandomSystemsCC/ResourceAlgebra.lean` installs the only concrete ambient
  `ResourceAlgebra`. `RandomSystemsCC/CommonDomain.lean` supplies
  non-expansion for the normalized specialization of Lanzenberger's
  common-domain subcarrier; it does not install a second parallel algebra.
- `Applications/CBCMAC/` owns the scheme-specific definitions and proof. No
  CBC object is part of the generic RS or RSCC layers.

The categorical layer does not postulate an untyped universal resource. An
interface records a query type and the answer type selected by each query;
each interface has its own resource fibre. The query-indexed DDC category
supplies the sole ambient `ResourceAlgebra`. The categorical common-domain
bridge uses Lanzenberger's normalized specialization; its arrows preserve that
embedded image.

## Building

```sh
lake exe cache get
lake build
lake build RandomSystems RandomSystemsConverter RandomSystemsCC
lake build RandomSystemsCCInstantiationTests Applications.CBCMAC
scripts/publicDependencyAudit.sh
git diff --check
```

The Lean toolchain is pinned in `lean-toolchain`.

## Reading order

1. Read `THEORY.md` for the mathematical objects, operations, laws, and layer
   boundaries.
2. Read `AbstractCryptography/Categorical.lean` for the abstract
   interface-indexed construction calculus.
3. Import `RandomSystems` and follow `DDS.lean`, `DDE.lean`, `PDS.lean`,
   `Observation.lean`, `RandomSystem.lean`, and `Distance.lean` for the
   fixed-interface theory.
4. Read `RandomSystems/Converter/DDC.lean` and
   `RandomSystems/Converter/ApplySystem.lean` before the serial, parallel, and
   probability-action modules.
5. Read `RandomSystemsCC/ResourceAlgebra.lean` for the ambient CC
   instantiation and `RandomSystemsCC/CommonDomain.lean` for the restricted
   common-domain adapter, then `Applications/CBCMAC.lean` for a complete
   application.
6. Use `CC_BY_HAND.md` to reconstruct the development in dependency order.

## Primary references

- Ueli Maurer and Renato Renner, *From Indifferentiability to Constructive
  Cryptography (and Back)*, TCC 2016.
- Daniel Jost, *On Generalizations of Composable Security*, ETH Zurich, 2020.
- Chen-Da Liu-Zhang, *Multi-Party Computation: Definitions, Enhanced Security
  Guarantees and Efficiency*, ETH Zurich, 2021.
- David Lanzenberger, *A Theory of Random Systems, Games, and Hardness
  Amplification*, ETH Zurich, 2023.
- Ueli Maurer, *Indistinguishability of Random Systems*, EUROCRYPT 2002.

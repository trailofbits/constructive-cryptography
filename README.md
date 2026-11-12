# Constructive Cryptography on Random Systems

This library formalizes Constructive Cryptography in Lean 4 [1, 2]. Abstract laws describe
resources, converters and security; random systems instantiate them [3, 4]. Constructions
and proofs assemble components through those laws.

## Libraries

[THEORY.md](THEORY.md) explains the mathematical layers and their connections.
Sources are under `src/`; each library's documentation gives its objects and laws.

| Library | Purpose |
|---|---|
| [Probability](src/Probability/README.md) | Finite probability laws and bounds. |
| [RandomSystems](src/RandomSystems/README.md) | Systems, converters, interaction, distances and games. |
| [ConstructiveCryptography](src/ConstructiveCryptography/README.md) | Abstract resource laws, security and compositional proofs. |
| [Instances](src/ConstructiveCryptography/Instances.lean) | Typed random systems instantiate the abstract laws. |
| [DSL and proof commands](src/ConstructiveCryptography/DSL/GRAMMAR.md) | Mathematical declarations and calculations over components. |
| [Commons](src/Commons.lean) | Reusable ideal systems, security notions and cryptographic primitives. |
| [Examples](src/Examples/README.md) | Complete constructions and security arguments. |
| [Tests](src/Tests.lean) | Regression tests and axiom audits. |

## Building

```sh
lake build
```

The toolchain and the Mathlib version are pinned in `lean-toolchain` and
`lake-manifest.json`. The axiom audits in `Tests` print the axioms of the main
results; the accepted envelope is `propext`, `Classical.choice` and
`Quot.sound`.

## Notes on AI usage

Most code and documentation were written with AI assistance under the authors' direction.
Lean checks proofs; source correspondence requires human review. Module docstrings provide
source quotations and page references for that review.

## Contributing

Contributor rules are in [AGENTS.md](AGENTS.md).
The [reuse guide](REUSE.md) maps common objects to their owners and gives the assembly and
definition-review workflow.

## License

MIT; see [LICENSE](LICENSE).

## References

1. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back). In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016. Cryptology ePrint Archive, Paper 2016/903.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, Diss. ETH No. 26723, ETH Zurich, 2020.
3. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
4. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.

Further references are in [THEORY.md](THEORY.md#references) and the owning modules.

# Constructive Cryptography on Random Systems

This repository formalizes Constructive Cryptography [1, 2] in Lean 4. The
framework is instantiated on a theory of random systems [3, 4] in which a
resource answers exactly on a declared domain of input histories, and a
converter may stop at random. The algebra of resources and converters is also
stated in category-theoretic terms; a categorical model of composable security
is given in [7].

## Libraries

The sources are under `src/`; module names follow their paths there. [THEORY.md](THEORY.md)
summarizes the theory layer by layer, with links to the Lean declarations.

| Library | Content |
|---|---|
| `Probability` | finitely supported distributions, statistical distance, couplings, expectation, counting |
| `RandomSystems` | systems and automata; deterministic converters and programs; distributions over deterministic systems; random systems given by their cumulative probabilities; probabilistic converters, attachment and parallel composition; transcript distance and distinguishers; games |
| `ConstructiveCryptography.Specification`, `.Construction` | specifications, constructions and relaxations over any carrier |
| `ConstructiveCryptography.CryptographicAlgebra` | the classes of cryptographic algebras: resource theories, parallel composition, compatible pseudo-metrics and distinguisher classes, relaxations |
| `ConstructiveCryptography` (top level) | interfaces, resources and converters on random systems, and their instances of the classes; filters, contexts, sources, automata, functional resources, game bounds; notation |
| `ConstructiveCryptography.Substitution` | the substitution calculus for constructions [6] |
| `ConstructiveCryptography.DSL` | a compiler from component declarations to resources and converters |
| `ConstructiveCryptography.Tactics` | proof commands, including the substitution calculations `cc_calc` |
| `Commons` | common ideal systems (URF, URP and their strong and tweakable forms), the CDH assumption as a pair of systems, the security notions as pairs of systems [6]: symmetric encryption (real-or-random and left-or-right CPA) and authenticated encryption (ind-cca, int-ptxt, int-ctxt, ae), public-key encryption and KEMs (IND-CPA, IND-CCA), MACs and signatures (EUF-CMA, SUF-CMA), PRGs, universal hashing (UHF, DUF) and collision resistance, and the schemes SHA-256, SHA-3, SHAKE, Keccak-256, ML-KEM [9] and ML-DSA [10] (the last two adapted from VCVio [11]) with known-answer tests, in the order of [8] |
| `Examples` | authenticated encryption, AES, AEAD, substitutions on interfaces, the proof commands |
| `Tests` | axiom audits, counterexamples, DSL diagnostics and semantics, tests of the substitution calculus |

Module docstrings cite the source of each definition and theorem, with the
printed page.

## Building

```sh
lake build
```

The toolchain and the Mathlib version are pinned in `lean-toolchain` and
`lake-manifest.json`. The axiom audits in `Tests` print the axioms of the main
results; the accepted envelope is `propext`, `Classical.choice` and
`Quot.sound`.

## Notes on AI usage

This library is developed with AI coding assistants, which wrote most of its
Lean code and documentation under the direction of the authors. Lean checks
every proof, and the axiom audits confirm that the main results depend only on
the axioms listed above. Lean does not check that a definition matches the
source it cites; module docstrings quote the source statements, with their
printed pages, so that this correspondence can be reviewed.

## Contributing

Contributor rules are in [AGENTS.md](AGENTS.md).

## License

MIT; see [LICENSE](LICENSE).

## References

1. U. Maurer and R. Renner. From Indifferentiability to Constructive Cryptography (and Back). In *Theory of Cryptography (TCC 2016-B)*, LNCS 9985, Springer, 2016. Cryptology ePrint Archive, Paper 2016/903.
2. D. Jost. *On Generalizations of Composable Security*. Doctoral thesis, Diss. ETH No. 26723, ETH Zurich, 2020.
3. D. Lanzenberger and U. Maurer. Coupling of Random Systems. In *Theory of Cryptography (TCC 2020)*, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1187.
4. U. Maurer. *Cryptography Foundations*. Lecture notes, ETH Zurich, Spring 2018.
5. C.-D. Liu-Zhang and U. Maurer. Synchronous Constructive Cryptography. In *Theory of Cryptography (TCC 2020)*, LNCS 12552, pp. 439–472, Springer, 2020. Cryptology ePrint Archive, Paper 2020/1226.
6. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis, Diss. ETH No. 29663, ETH Zurich, 2023.
7. A. Broadbent and M. Karvonen. Categorical composable cryptography: extended version. *Logical Methods in Computer Science* 19(4), Paper 30, 2023. doi:10.46298/lmcs-19(4:30)2023. arXiv:2208.13232.
8. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
9. National Institute of Standards and Technology. *Module-Lattice-Based Key-Encapsulation Mechanism Standard*. FIPS 203, 2024. doi:10.6028/NIST.FIPS.203.
10. National Institute of Standards and Technology. *Module-Lattice-Based Digital Signature Standard*. FIPS 204, 2024. doi:10.6028/NIST.FIPS.204.
11. VCVio: a formal verification framework for cryptographic proofs in Lean. https://github.com/Verified-zkEVM/VCVio, commit `f5119c6`.

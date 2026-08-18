/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Frost.Algebra
import Applications.Frost.Protocol
import Applications.Frost.Rfc9591
import Applications.Frost.Construction

/-!
# FROST (RFC 9591): the umbrella root

Each layer owns one concern; see the submodule headers for sources and
modeling boundaries.

* `Applications.Frost.Algebra` — the complete correctness algebra over any
  field `F` and `F`-module `V` (Shamir, Schnorr, aggregation; M3).
* `Applications.Frost.Protocol` — the RFC 9591 functional core: signing and
  the Komlo–Goldberg DKG as pure deterministic maps with explicit
  randomness, and their correctness theorems.
* `Applications.Frost.Rfc9591` — the executable wire-level
  FROST(secp256k1, SHA-256) ciphersuite validated by the RFC test vectors
  (`FrostRfc9591Tests`).
* `Applications.Frost.Construction` — the carrier-free two-stage CC
  construction statements (`frost_end_to_end`, `frost_end_to_end_eps`,
  `frost_threshold`, `frost_threshold_unforgeability`; M4).

Everything that *instantiates* these layers — the concrete group
(`FrostGroup`, secp256k1), the typed random-systems carrier bridge, and
the eventual simulator/game leaves — lives in the sibling
`random-systems` repository under `RandomSystemsCC.Frost`: instantiation
is carrier content, and the theorems here fire there by application.
-/

/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga, Claude
-/
import Applications.Sha256
import Applications.Secp256k1
import Applications.Frost
import Applications.CBCMAC

/-!
# Applications: implementations of the standards

Executable Lean implementations of published cryptographic standards:

* **FIPS 180-4** — SHA-256 (`Applications.Sha256`).
* **SEC 1 / SEC 2** — the secp256k1 curve and its field/scalar
  arithmetic (`Applications.Secp256k1`).
* **RFC 9591** — FROST, the two-round Schnorr threshold signature
  protocol (`Applications.Frost`), together with FROST's Shamir/Lagrange
  algebra and its functional core.
* **CBC-MAC** — the normalized functional random-system construction and its
  collision bound (`Applications.CBCMAC`).

These are downstream consumers, not another theory layer.
`Applications.Sha256` and `Applications.Secp256k1` are standalone; this root
also imports `Applications.Frost`, which imports
`ConstructiveCryptography.MultipartyComputation`. The `Applications` Lake
target additionally owns `Applications.Sponge`, which uses the same
`ResourceAlgebra` construction calculus. Dependencies point from
applications into the theory layers, never back.
-/

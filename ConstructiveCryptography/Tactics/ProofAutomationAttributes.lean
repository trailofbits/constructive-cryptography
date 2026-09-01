/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import Mathlib.Tactic.Attr.Register

/-!
# Constructive Cryptography proof-automation attributes

The attributes live in this tiny dependency-free registration module because
Lean cannot consume a newly registered simp attribute in the same module that
declares it.  Semantic rules are selected only by
`ConstructiveCryptography.Tactics.ProofAutomation`; CC definition modules do
not import this metaprogramming layer.
-/

/-- Terminating equations that put selected CC expressions into the documented
paper normal form. -/
register_simp_attr cc_normalization

/-- Explicitly registered commutation, support, membership, applicability, and
action facts that may discharge CC side conditions. -/
register_simp_attr cc_side_condition

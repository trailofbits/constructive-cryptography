/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Authors: Marc Ilunga
-/
import ConstructiveCryptographyDemoSupport

/-!
# A presentation demo for Abstract and Constructive Cryptography

**MR11-DEFERRED (provenance fence, 2026-08-17): MauRen11 constructs
quarantined pending the MR11 reconciliation task.  No MR16-track file may
import this module — enforced by `scripts/ledgerAudit.sh`.  See `LEDGER.md`
PROVENANCE FENCE.**

This non-default module is an audience-facing demonstration of what the
formalized AC/CC layer buys us.  It has two acts.

## Act I: a secure channel by composition

MauRen11, Section 1.7 (PDF and printed page 6), gives the motivating example:

* a secure MAC constructs an authenticated channel from an insecure channel
  and an authentication key;
* secure symmetric encryption constructs a secure channel from an
  authenticated channel and an encryption key; therefore
* their composition constructs a secure channel from the insecure channel and
  the two keys.

The formal proof below is the compositional shell of that argument:

```text
(authenticationKey ∥ insecureChannel) ∥ encryptionKey
  -- macProtocol ∥ 1, error macError -->
authenticatedChannel ∥ encryptionKey
  -- encryptionProtocol, error encryptionError -->
secureChannel
```

The leaf assumptions are intentionally genuine construction statements.  A
concrete random-system development supplies those statements by proving the
protocol-specific probability and combinatorics.  AC then performs the
mechanical context extension and composition, checks the order of converter
multiplication, and adds the error bounds.

The theorem is presented twice under one shared ambient AC context.  The first
declaration uses ordinary Lean and names the two library theorems used by the
proof.  The second declaration states and proves the same result using the
controlled-language presentation layer.  This makes the comparison about
notation and proof language, rather than about repeated infrastructure or two
different mathematical examples.

Suggested live AI prompt:

> Starting from
> `mac_then_encryption_constructs_secure_channel_in_lean`, present the same
> argument as `mac_then_encryption_constructs_secure_channel`.  Keep the
> authenticated-channel intermediate resource explicit, use the paper-facing
> controlled language, and do not unfold `Constructs`.

## Act II: formalization checks the algebra

MauRen11, Appendix C.3, Theorem 4 (PDF pages 18--19), proves that a plain
channel cannot construct any resource `target` satisfying
`target * middle * target ≠ target` for every middle system.  The printed
proof writes the final middle system in the order `aliceSimulator *
bobSimulator`.  Direct substitution into its displayed equations instead
produces `bobSimulator * aliceSimulator`.  The theorem remains correct, but
the formal calculation makes the order check unavoidable.

Suggested live AI prompt:

> Reprove `plain_channel_impossibility_demo` from the first three equations in
> `Abstraction`.  Do not invoke `not_abstraction_plainChannel`.  Present the
> final equality as a calculation and explain the simulator order.

The intended lesson is not that AI should invent the cryptographic leaf
theorems.  It should recognize the canonical construction workflow, assemble
the routine AC/CC obligations transparently, and leave protocol-specific
mathematics visible.
-/

open AbstractCryptography
open scoped AbstractCryptography CryptoControlledNaturalLanguage

namespace ConstructiveCryptographyDemo

section ParallelConstructionComparison

/- The two presentations below share one ambient AC context.  Declaring it
once keeps infrastructure out of both theorem headers without bundling it. -/
variable {Converter Resource : Type*}
variable [Monoid Converter] [MulAction Converter Resource]
variable [PseudoEMetricSpace Resource]
variable [IsNonexpandingSMul Converter Resource]
variable [Par Converter] [Par Resource]
variable [SMulParClass Converter Resource]
variable [IsNonexpandingPar Resource]

/-! ### Ordinary Lean -/

/-- MauRen11 Section 1.7, stated and proved using ordinary Lean syntax. -/
theorem mac_then_encryption_constructs_secure_channel_in_lean
    (authenticationKey insecureChannel encryptionKey
      authenticatedChannel secureChannel : Resource)
    (macProtocol encryptionProtocol : Converter)
    (macError encryptionError : ENNReal)
    (macConstruction :
      ⟪authenticationKey ∥ insecureChannel⟫
        —[macProtocol; macError]→ ⟪authenticatedChannel⟫)
    (encryptionConstruction :
      ⟪authenticatedChannel ∥ encryptionKey⟫
        —[encryptionProtocol; encryptionError]→ ⟪secureChannel⟫) :
    ⟪(authenticationKey ∥ insecureChannel) ∥ encryptionKey⟫
      —[encryptionProtocol * (macProtocol ∥ 1);
        macError + encryptionError]→ ⟪secureChannel⟫ := by
  have authenticatedChannelWithEncryptionKey :
      ⟪(authenticationKey ∥ insecureChannel) ∥ encryptionKey⟫
        —[macProtocol ∥ 1; macError]→
      ⟪authenticatedChannel ∥ encryptionKey⟫ :=
    Constructs.epsilonRelaxation_par_resource macConstruction encryptionKey
  exact Constructs.epsilonRelaxation_trans
    authenticatedChannelWithEncryptionKey encryptionConstruction

/-! ### The same proof in controlled natural language -/

/-- MauRen11 Section 1.7: a secure MAC followed by secure symmetric
encryption constructs a secure channel.  The protocol on the right acts
first, so the composed converter is
`encryptionProtocol * (macProtocol ∥ 1)`. -/
Theorem mac_then_encryption_constructs_secure_channel
  Given Resources authenticationKey, insecureChannel, encryptionKey,
    authenticatedChannel, secureChannel
  Given Protocols macProtocol, encryptionProtocol
  Given Error Bounds macError, encryptionError
  Assume
    (macConstruction :
      ⟪authenticationKey ∥ insecureChannel⟫
        —[macProtocol; macError]→ ⟪authenticatedChannel⟫)
    (encryptionConstruction :
      ⟪authenticatedChannel ∥ encryptionKey⟫
        —[encryptionProtocol; encryptionError]→ ⟪secureChannel⟫)
  Conclusion
    ⟪(authenticationKey ∥ insecureChannel) ∥ encryptionKey⟫
      —[encryptionProtocol * (macProtocol ∥ 1);
        macError + encryptionError]→ ⟪secureChannel⟫
  Proof
    We have authenticatedChannelWithEncryptionKey :
        ⟪(authenticationKey ∥ insecureChannel) ∥ encryptionKey⟫
          —[macProtocol ∥ 1; macError]→
        ⟪authenticatedChannel ∥ encryptionKey⟫ by
      With encryptionKey as the right parallel context,
        the construction follows from macConstruction

    The construction follows by composing
      authenticatedChannelWithEncryptionKey
        ("The MAC construction leaves the encryption key unchanged.") and
      encryptionConstruction
        ("Encryption turns the authenticated channel into a secure channel.")
  QED

end ParallelConstructionComparison

namespace PlainChannelImpossibility

section

variable {System : Type*} [Monoid System]

/-- Presentation reproof of MauRen11 Appendix C.3, Theorem 4.  The library's
canonical theorem is `AbstractCryptography.TwoParty.not_abstraction_plainChannel`;
this copy deliberately exposes the short paper calculation for the demo. -/
Theorem plain_channel_impossibility_demo
  Given Systems plainChannel, target
  Given Protocols aliceProtocol, bobProtocol
  Assume
    (plain : AbstractCryptography.TwoParty.IsPlainChannel plainChannel)
    (cannotSandwich : ∀ middle,
      target * middle * target ≠ target)
  Conclusion
    ¬ AbstractCryptography.TwoParty.Abstraction
      aliceProtocol bobProtocol plainChannel target
  Proof
    intro allegedConstruction
    obtain ⟨aliceSimulator, bobSimulator, bothHonest,
      bobDishonest, aliceDishonest, _bothDishonest⟩ := allegedConstruction

    rw [plain aliceProtocol bobProtocol] at bothHonest
    rw [plain.mul_left aliceProtocol] at bobDishonest
    rw [plain.mul_right bobProtocol] at aliceDishonest

    -- Substitution puts Bob's simulator before Alice's simulator.
    apply cannotSandwich (bobSimulator * aliceSimulator)
    calc
      target * (bobSimulator * aliceSimulator) * target
          = (target * bobSimulator) * (aliceSimulator * target) := by
              simp only [mul_assoc]
      _ = aliceProtocol * bobProtocol := by
            rw [← bobDishonest, ← aliceDishonest]
      _ = target := bothHonest
  QED

end

end PlainChannelImpossibility

end ConstructiveCryptographyDemo

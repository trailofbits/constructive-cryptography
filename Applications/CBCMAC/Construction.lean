/-
Copyright (c) 2026 Trail of Bits. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Applications.CBCMAC.Probability
import RandomSystemsCC.ResourceAlgebra

set_option autoImplicit false

/-!
# CBC construction

Maurer 2002, Theorem 6 (printed p. 17), gives the collision bound used below.
The restricted CC statement follows the CR18 fallback registered for this
application: Theorem 6.1 (printed p. 126) states the construction from
`[r]R` using `θ_r CBC`.  No CR18 random-system implementation is imported;
only that application statement is represented using the accepted ambient
DDS/DDC/PDS model.

Because the normalized finite-support carrier requires a finite message type,
the result is the explicit bounded-message specialization.  The argument
`blockForm` is already the prefix-free encoded and padded block sequence.
-/

namespace Applications.CBCMAC

noncomputable section

open AbstractCryptography.Categorical
open AbstractCryptography.Categorical.ResourceAlgebra
open RandomSystems.Ambient

universe u

variable {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X]
  [AddCommGroup X]
variable {M : Type u} [Fintype M] [DecidableEq M]

/-- Maurer 2002, Theorem 6 (printed p. 17), specifies `n` as “the total number
of blocks of all k messages issued by the distinguisher.” This is the
`C(R)`-versus-ideal collision leg on the normalized finite-message quotient. -/
theorem cbc_distance_le [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : CBCCombinatorics.PrefixFree blockForm) :
    edist (RandomSystem.ofPDS (realPDS blockForm limit))
        (RandomSystem.ofPDS (idealPDS blockForm limit)) ≤
      CBCCombinatorics.cbcEpsilon X limit := by
  -- Quotient distance is the ambient advantage already bounded at the PDS level.
  rw [RandomSystem.edist_ofPDS_eq]
  exact realPDS_advantage_le blockForm limit prefixFree

/-- CR18, Theorem 6.1 (printed p. 126), states that if “the block-former of the
CBC-converter is prefix-free”, then `[r]R` constructs `θ_r V` using
`θ_r CBC`.  This is its normalized finite-message instantiation. -/
theorem cbc_constructs_within [Nontrivial M]
    (blockForm : M → List X) (limit : Nat)
    (prefixFree : CBCCombinatorics.PrefixFree blockForm) :
    ResourceAlgebra.Specification.ConstructsWithin
      (Phi := Interface.randomSystems)
      (DDC.serial (theta blockForm limit) (cbc blockForm))
      ({RandomSystem.ofPDS (restrictedRandomFunction limit)} :
        ResourceAlgebra.Specification Interface.randomSystems
          (Interface.single X X))
      ({RandomSystem.ofPDS (idealPDS blockForm limit)} :
        ResourceAlgebra.Specification Interface.randomSystems
          (Interface.single M X))
      (CBCCombinatorics.cbcEpsilon X limit) := by
  -- Singleton source membership fixes the only attached real resource.
  intro resource member
  have resourceEqual : resource =
      RandomSystem.ofPDS (restrictedRandomFunction limit) :=
    Set.mem_singleton_iff.mp member
  subst resource
  refine ⟨RandomSystem.ofPDS (idealPDS blockForm limit),
    Set.mem_singleton _, ?_⟩
  change edist
      (RandomSystem.apply
        (DDC.serial (theta blockForm limit) (cbc blockForm))
        (RandomSystem.ofPDS (restrictedRandomFunction limit)))
      (RandomSystem.ofPDS (idealPDS blockForm limit)) ≤
    CBCCombinatorics.cbcEpsilon X limit
  -- Serial attachment is CBC followed by the `θ_r` restriction.
  rw [RandomSystem.apply_ofPDS_eq, PDS.apply_serial_eq]
  change edist
      (RandomSystem.ofPDS (realPDS blockForm limit))
      (RandomSystem.ofPDS (idealPDS blockForm limit)) ≤
    CBCCombinatorics.cbcEpsilon X limit
  -- Apply the normalized observational CBC distance bound.
  exact cbc_distance_le blockForm limit prefixFree

end

end Applications.CBCMAC

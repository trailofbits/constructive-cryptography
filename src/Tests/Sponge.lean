module

public import Commons.Schemes.Sponge.Basic

/-!
# Contract and unit tests for the byte-oriented sponge construction

Exercises `Commons.Schemes.Sponge.Basic`: boundary `pad10*1` padding cases, standard SHA-3 and
Keccak-256 parameter validity and rate-block alignment, padding and block injectivity, sponge
recording locality, and collision avoidance under decoupled capacity/digest invariants.
-/

@[expose] public section

namespace SpongeTests

open Commons.Sponge

/-- A small 4-byte sponge (2-byte rate, 2-byte capacity, 1-byte digest, suffix `0x06`) for
boundary tests. -/
def smallParameters : Parameters := ⟨4, 2, 1, 0x06⟩

lemma smallParameters_valid : smallParameters.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

/-- Empty input pads to one full rate block `[0x06, 0x80]`. -/
lemma small_pad_empty : spongePadding smallParameters [] = [0x06, 0x80] := by
  rfl

/-- An input of length `rateBytes - 1` exercises the `padZeros = 0` branch, ORing `0x80` directly
into the suffix byte. -/
lemma small_pad_single_byte_or : spongePadding smallParameters [0x2A] = [0x2A, 0x86] := by
  rfl

/-- An input of length `rateBytes` wraps into two complete rate blocks. -/
lemma small_pad_full_block :
    spongePadding smallParameters [0x11, 0x22] = [0x11, 0x22, 0x06, 0x80] := by
  rfl

/-- Distinct messages never share the same padded byte string or block sequence under SHA3-256. -/
lemma sha3_256_padding_and_blocks_injective :
    Function.Injective (spongePadding sha3_256) ∧ Function.Injective (paddedBlocks sha3_256) :=
  ⟨spongePadding_injective sha3_256 sha3_256_valid.2.2.2.2.1 sha3_256_valid.2.2.2.2.2,
    paddedBlocks_injective sha3_256 sha3_256_valid.1
      sha3_256_valid.2.2.2.2.1 sha3_256_valid.2.2.2.2.2⟩

/-- Every SHA-3 and Keccak-256 parameter set satisfies `Parameters.Valid` and produces
rate-aligned padded inputs. -/
lemma standard_params_block_aligned (input : List (BitVec 8)) :
    sha3_224.rateBytes ∣ (spongePadding sha3_224 input).length ∧
      sha3_256.rateBytes ∣ (spongePadding sha3_256 input).length ∧
      sha3_384.rateBytes ∣ (spongePadding sha3_384 input).length ∧
      sha3_512.rateBytes ∣ (spongePadding sha3_512 input).length ∧
      keccak256.rateBytes ∣ (spongePadding keccak256 input).length :=
  ⟨spongePadding_length_dvd sha3_224 sha3_224_valid.1 input,
    spongePadding_length_dvd sha3_256 sha3_256_valid.1 input,
    spongePadding_length_dvd sha3_384 sha3_384_valid.1 input,
    spongePadding_length_dvd sha3_512 sha3_512_valid.1 input,
    spongePadding_length_dvd keccak256 keccak256_valid.1 input⟩

/-- Any permutation agreeing with `recordSponge` matches `spongeHash` on the recorded input. -/
lemma small_recordSponge_local (π ρ : Equiv.Perm (ByteState smallParameters.stateBytes))
    (input : List (BitVec 8))
    (hρ : AgreesWith (recordSponge smallParameters π [] input) ρ) :
    spongeHash smallParameters ρ input = spongeHash smallParameters π input := by
  have hπ : AgreesWith (recordSponge smallParameters π [] input) π :=
    recordSponge_agrees smallParameters π [] (fun _ h => by cases h) input
  exact (recordSponge_local smallParameters π ρ [] input hπ hρ).2

/-- A valid sponge is collision-free on covered inputs under decoupled capacity and digest
invariants. -/
lemma sha3_256_collision_free_on_table
    (table : List (PermutationEdge (ByteState sha3_256.stateBytes)))
    (hg : CapacityCollisionFree (capacityPart sha3_256) (zeroState sha3_256.capacityBytes) table)
    (hdig : Set.InjOn (digestPart sha3_256) (forwardOutputs table))
    (π : Equiv.Perm (ByteState sha3_256.stateBytes)) (ha : AgreesWith table π)
    (first second : List (BitVec 8))
    (hf : ∀ x ∈ spongeCalls sha3_256 π first, ∃ edge ∈ table, edge.input = x)
    (hs : ∀ x ∈ spongeCalls sha3_256 π second, ∃ edge ∈ table, edge.input = x)
    (he : spongeHash sha3_256 π first = spongeHash sha3_256 π second) :
    first = second :=
  input_eq_of_spongeHash_eq sha3_256 sha3_256_valid table hg hdig π ha first second hf hs he

/-! ## Axiom audit of key exported theorems -/

#print axioms Commons.Sponge.spongePadding_length
#print axioms Commons.Sponge.spongePadding_length_dvd
#print axioms Commons.Sponge.spongePadding_injective
#print axioms Commons.Sponge.paddedBlocks_injective
#print axioms Commons.Sponge.recordSponge_local
#print axioms Commons.Sponge.input_eq_of_spongeHash_eq

end SpongeTests

module

public import Commons.Schemes.Sponge.Collision
public import ConstructiveCryptography.Notation
public import ConstructiveCryptography.Tactics.Substitution

/-!
# Contract tests for adaptive sponge collision resistance

Exercises `Commons.Schemes.Sponge.Collision` on `sha3_256`, `sha3_384`, `sha3_512`, and a small
4-byte sponge: tight `freshCapacities` preservation, adaptive capacity-collision and combined
sponge-collision bounds on `StrongURP`, unset-transcript collision-freeness of `spongeHash`,
and `cc_normalize` / `cc_calc statistical` compatibility under CC custom notation.
-/

@[expose] public section

namespace SpongeCollisionTests

open CategoryTheory SystemAlgebra Commons Commons.Sponge Commons.StrongURP
open scoped SystemAlgebra

/-- Tight `freshCapacities` test: an edge whose fresh endpoint collides only with a previous
forward edge's *input* (not its fresh output) still preserves `CapacityCollisionFree`. -/
lemma freshCapacities_strictly_tighter_than_occupied :
    let e1 : PermutationEdge (Fin 4) := ⟨1, 2, false⟩
    let e2 : PermutationEdge (Fin 4) := ⟨3, 1, false⟩
    CapacityCollisionFree (id : Fin 4 → Fin 4) (0 : Fin 4) (insertEdge [e1] e2) := by
  intro e1 e2
  have h0 : CapacityCollisionFree (id : Fin 4 → Fin 4) 0 ([] : List (PermutationEdge (Fin 4))) :=
    capacityCollisionFree_nil id 0
  have h1 : CapacityCollisionFree (id : Fin 4 → Fin 4) 0 [e1] := by
    apply capacityCollisionFree_append_of_fresh id 0 [] h0 e1
    simp only [freshCapacities, PermutationEdge.freshEndpoint, List.map_nil, List.toFinset_nil,
      Finset.mem_insert, Finset.notMem_empty, or_false, Bool.false_eq_true, ↓reduceIte, id_eq, e1]
    intro h
    have hv : (2 : Nat) = 0 := congrArg Fin.val h
    omega
  apply capacityCollisionFree_insertEdge_of_fresh id 0 [e1] h1 e2
  intro _
  simp only [freshCapacities, PermutationEdge.freshEndpoint, List.map_cons, List.map_nil,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty, or_false,
    Bool.false_eq_true, ↓reduceIte, id_eq, e1, e2]
  rintro (h | h)
  · have hv : (1 : Nat) = 0 := congrArg Fin.val h
    omega
  · have hv : (1 : Nat) = 2 := congrArg Fin.val h
    omega

/-- Small 4-byte sponge (2-byte rate, 2-byte capacity, 1-byte output, suffix `0x06`). -/
def smallParameters : Parameters := ⟨4, 2, 1, 0x06⟩

lemma smallParameters_valid : smallParameters.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

/-- Concrete 3-query adaptive bound on the 4-byte sponge: `C(4, 2) = 6`, `C(3, 2) = 3`. -/
lemma small_spongeCollisionGame_win_le
    {winner : TypedGame (Bidirectional (ByteState smallParameters.stateBytes) 3) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState smallParameters.stateBytes) 3)) :
    winner (spongeCollisionGame smallParameters 3) ≤ spongeCollisionBound smallParameters 3 :=
  spongeCollisionGame_win_le smallParameters smallParameters_valid 3
    (by rw [card_byteState]; change 3 < 256 ^ 4; omega) hw

/-- Concrete adaptive capacity-collision bound for SHA3-256 on `StrongURP`. -/
lemma sha3_256_capacityCollision_win_le (q : ℕ) (hq : q < 256 ^ 200)
    {winner : TypedGame (Bidirectional (ByteState sha3_256.stateBytes) q) → ℝ}
    (hw : winner ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState sha3_256.stateBytes) q)) :
    winner (capacityCollisionGame sha3_256 q) ≤ capacityCollisionBound sha3_256 q :=
  capacityCollisionGame_win_le sha3_256 sha3_256_valid q
    (by rw [card_byteState]; exact hq) hw

/-- Concrete adaptive combined sponge-collision bounds for SHA3-256, SHA3-384, and SHA3-512. -/
lemma sha3_suite_spongeCollision_win_le (q : ℕ) (hq : q < 256 ^ 200)
    {w256 : TypedGame (Bidirectional (ByteState sha3_256.stateBytes) q) → ℝ}
    (hw256 : w256 ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState sha3_256.stateBytes) q))
    {w384 : TypedGame (Bidirectional (ByteState sha3_384.stateBytes) q) → ℝ}
    (hw384 : w384 ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState sha3_384.stateBytes) q))
    {w512 : TypedGame (Bidirectional (ByteState sha3_512.stateBytes) q) → ℝ}
    (hw512 : w512 ∈ ConstructiveCryptography.Games.winners
      (Bidirectional (ByteState sha3_512.stateBytes) q)) :
    w256 (spongeCollisionGame sha3_256 q) ≤ spongeCollisionBound sha3_256 q ∧
      w384 (spongeCollisionGame sha3_384 q) ≤ spongeCollisionBound sha3_384 q ∧
      w512 (spongeCollisionGame sha3_512 q) ≤ spongeCollisionBound sha3_512 q :=
  ⟨spongeCollisionGame_win_le sha3_256 sha3_256_valid q (by rw [card_byteState]; exact hq) hw256,
    spongeCollisionGame_win_le sha3_384 sha3_384_valid q (by rw [card_byteState]; exact hq) hw384,
    spongeCollisionGame_win_le sha3_512 sha3_512_valid q (by rw [card_byteState]; exact hq) hw512⟩

/-- Unset transcripts of `spongeCollisionGame sha3_256 q` preclude `spongeHash` collisions on all
covered inputs. -/
lemma sha3_256_unset_no_collision (q : ℕ)
    (h : List ((Σ i, (Bidirectional (ByteState sha3_256.stateBytes) q).X i) ×
      Σ i, (Bidirectional (ByteState sha3_256.stateBytes) q).Y i))
    (hunset : (spongeCollisionGame sha3_256 q).1.1 (unsetMBOs h) ≠ 0)
    (π : Equiv.Perm (ByteState sha3_256.stateBytes))
    (ha : AgreesWith (transcriptTable q h) π)
    (first second : List (BitVec 8))
    (hf : ∀ x ∈ spongeCalls sha3_256 π first, ∃ edge ∈ transcriptTable q h, edge.input = x)
    (hs : ∀ x ∈ spongeCalls sha3_256 π second, ∃ edge ∈ transcriptTable q h, edge.input = x)
    (he : spongeHash sha3_256 π first = spongeHash sha3_256 π second) :
    first = second :=
  spongeCollisionGame_unset_no_collision sha3_256 sha3_256_valid q h hunset π ha first second
    hf hs he

/-- Compatibility with `cc_normalize` and `cc_calc statistical` under CC custom notation:
attaching a serial converter composition `α ≫ β` to `StrongURP` transports the collision distance
bound cleanly and chains with a second statistical hop. -/
lemma sha3_256_cc_calc_attach (q : ℕ) (hq : q < 256 ^ 200)
    {A B : Interface} (α : A ⟶ B) (β : B ⟶ Bidirectional (ByteState sha3_256.stateBytes) q)
    {T : TypedSystem (Bidirectional (ByteState sha3_256.stateBytes) q)}
    {U : TypedSystem A} {δ : ENNReal}
    (hc : spongeCollisionGame sha3_256 q |≡ T)
    (hnext : Δ ((α ≫ β) • T) U ≤ δ) :
    Δ (α • (β • StrongURP (ByteState sha3_256.stateBytes) (q := q))) U ≤
      ENNReal.ofReal (spongeCollisionBound sha3_256 q) + δ := by
  have hnorm : α • (β • StrongURP (ByteState sha3_256.stateBytes) (q := q)) =
      (α ≫ β) • StrongURP (ByteState sha3_256.stateBytes) (q := q) := by
    cc_normalize
  rw [hnorm]
  cc_calc statistical
    (α ≫ β) • StrongURP (ByteState sha3_256.stateBytes) (q := q)
      ≈[ENNReal.ofReal (spongeCollisionBound sha3_256 q)] (α ≫ β) • T :=
        spongeCollisionGame_attach_dist_le sha3_256 sha3_256_valid q
          (by rw [card_byteState]; exact hq) (α ≫ β) hc
    _ ≈[δ] U := hnext

/-- Substitution-relation corollary (`≃[...]`) for SHA3-256 against any admissible distinguisher
class. -/
lemma sha3_256_substitutesWithin
    [ConstructiveCryptography.AdmissibleDistinguishers Interface TypedDistinguisher]
    (q : ℕ) (hq : q < 256 ^ 200)
    {T : TypedSystem (Bidirectional (ByteState sha3_256.stateBytes) q)}
    (hc : spongeCollisionGame sha3_256 q |≡ T) :
    StrongURP (ByteState sha3_256.stateBytes) (q := q) ≃[fun _ =>
      ENNReal.ofReal (spongeCollisionBound sha3_256 q)] T :=
  spongeCollisionGame_substitutesWithin sha3_256 sha3_256_valid q
    (by rw [card_byteState]; exact hq) hc

/-! ## Axiom audit of key exported theorems -/

#print axioms Commons.Sponge.capacityCollisionFree_append_of_fresh
#print axioms Commons.Sponge.capacityCollisionFree_insertEdge_of_fresh
#print axioms Commons.Sponge.capacityCollisionGame_win_le
#print axioms Commons.Sponge.capacityCollisionGame_dist_le
#print axioms Commons.Sponge.spongeCollisionGame_win_le
#print axioms Commons.Sponge.spongeCollisionGame_unset_no_collision
#print axioms Commons.Sponge.spongeCollisionGame_dist_le
#print axioms Commons.Sponge.spongeCollisionGame_attach_dist_le
#print axioms Commons.Sponge.spongeCollisionGame_substitutesWithin

end SpongeCollisionTests

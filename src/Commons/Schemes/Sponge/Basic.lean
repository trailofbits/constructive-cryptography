module

public import Commons.Schemes.Sponge.Table
public import Mathlib.Data.List.OfFn

/-!
# Generic byte-oriented sponge construction

Starting at zero, inject each padded rate block into the state and apply the permutation `π`.
The digest is the first `outputBytes` of the final state [1, §§4, 5.1].

```text
message ──paddedBlocks──▶ blocks ──absorbBlocks (absorbBlock p) π──▶ state ──digestPart──▶ digest
```

`flatten_paddedBlocks` recovers the padded bytes, and `spongePadding_injective` recovers the
message. `recordSponge_local` shows that the recorded permutation pairs suffice to reproduce
its digest. For covered messages, `input_eq_of_spongeHash_eq` uses distinct forward digests
to recover the final state and the table's rooted-path law to recover the blocks [2, §4.3].

The executable Keccak-f[1600] implementation lives in `Commons.Schemes.Hash.Keccak`.

## References

[1] National Institute of Standards and Technology, *SHA-3 Standard: Permutation-Based Hash and
Extendable-Output Functions*, FIPS PUB 202, August 2015.

[2] Guido Bertoni, Joan Daemen, Michaël Peeters, and Gilles Van Assche, *On the
Indifferentiability of the Sponge Construction*, EUROCRYPT 2008, LNCS 4965, pp. 181–197.
-/

@[expose] public section

namespace Commons.Sponge

/-- A fixed-width byte vector of length `n`. -/
abbrev ByteState (n : Nat) := Fin n → BitVec 8

/-- The all-zero byte vector of length `n`. -/
def zeroState (n : Nat) : ByteState n := fun _ => 0

/-- Parameters of a byte-oriented single-squeeze sponge construction [1, §4]. -/
structure Parameters where
  /-- Total state width in bytes (`r + c`). -/
  stateBytes : Nat
  /-- Rate width in bytes (`r`). -/
  rateBytes : Nat
  /-- Digest output width in bytes. -/
  outputBytes : Nat
  /-- Domain-separation suffix byte carrying the first `1` bit of `pad10*1`. -/
  suffix : BitVec 8
  deriving DecidableEq

/-- The capacity width `stateBytes - rateBytes` in bytes. -/
def Parameters.capacityBytes (p : Parameters) : Nat :=
  p.stateBytes - p.rateBytes

/-- Well-formedness of sponge parameters: positive rate strictly below the state width, positive
digest fitting within one rate block, and a nonzero suffix in the low seven bits so setting the
final high bit `0x80` cannot erase the suffix. -/
def Parameters.Valid (p : Parameters) : Prop :=
  0 < p.rateBytes ∧
    p.rateBytes < p.stateBytes ∧
    0 < p.outputBytes ∧
    p.outputBytes ≤ p.rateBytes ∧
    p.suffix ≠ 0 ∧
    p.suffix.toNat < 128

/-- Helper for discharging `Parameters.Valid` from natural-number bounds. -/
lemma Parameters.valid_of_toNat {s r o n : Nat} {sfx : BitVec 8}
    (hr : 0 < r) (hrs : r < s) (ho : 0 < o) (hor : o ≤ r)
    (hs : sfx.toNat = n) (hn0 : 0 < n) (hn1 : n < 128) :
    (Parameters.mk s r o sfx).Valid := by
  refine ⟨hr, hrs, ho, hor, ?_, hs ▸ hn1⟩
  intro h
  have hv : sfx.toNat = 0 := congrArg BitVec.toNat h
  omega

/-- SHA3-224 parameters: 200-byte state, 144-byte rate, 28-byte digest, suffix `0x06` [1, §6.1]. -/
def sha3_224 : Parameters := ⟨200, 144, 28, 0x06⟩

/-- SHA3-256 parameters: 200-byte state, 136-byte rate, 32-byte digest, suffix `0x06` [1, §6.1]. -/
def sha3_256 : Parameters := ⟨200, 136, 32, 0x06⟩

/-- SHA3-384 parameters: 200-byte state, 104-byte rate, 48-byte digest, suffix `0x06` [1, §6.1]. -/
def sha3_384 : Parameters := ⟨200, 104, 48, 0x06⟩

/-- SHA3-512 parameters: 200-byte state, 72-byte rate, 64-byte digest, suffix `0x06` [1, §6.1]. -/
def sha3_512 : Parameters := ⟨200, 72, 64, 0x06⟩

/-- Keccak-256 parameters: 200-byte state, 136-byte rate, 32-byte digest, suffix `0x01`. -/
def keccak256 : Parameters := ⟨200, 136, 32, 0x01⟩

lemma sha3_224_valid : sha3_224.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

lemma sha3_256_valid : sha3_256.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

lemma sha3_384_valid : sha3_384.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

lemma sha3_512_valid : sha3_512.Valid :=
  Parameters.valid_of_toNat (n := 6) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

lemma keccak256_valid : keccak256.Valid :=
  Parameters.valid_of_toNat (n := 1) (by omega) (by omega) (by omega) (by omega) rfl
    (by omega) (by omega)

/-- The rate prefix (first `rateBytes` bytes) of a sponge state. -/
def ratePart (p : Parameters) (state : ByteState p.stateBytes) : ByteState p.rateBytes :=
  fun i => if h : i.val < p.stateBytes then state ⟨i.val, h⟩ else 0

/-- The capacity suffix (bytes from `rateBytes` to `stateBytes`) of a sponge state. -/
def capacityPart (p : Parameters) (state : ByteState p.stateBytes) :
    ByteState p.capacityBytes :=
  fun i => if h : p.rateBytes + i.val < p.stateBytes then state ⟨p.rateBytes + i.val, h⟩ else 0

/-- The digest prefix (first `outputBytes` bytes) of a sponge state. -/
def digestPart (p : Parameters) (state : ByteState p.stateBytes) : ByteState p.outputBytes :=
  fun i => if h : i.val < p.stateBytes then state ⟨i.val, h⟩ else 0

/-- XOR a single rate block into the rate bytes of `state`, leaving the capacity untouched. -/
def absorbBlock (p : Parameters) (state : ByteState p.stateBytes) (block : ByteState p.rateBytes) :
    ByteState p.stateBytes :=
  fun i => if h : i.val < p.rateBytes then state i ^^^ block ⟨i.val, h⟩ else state i

lemma capacityPart_zeroState (p : Parameters) :
    capacityPart p (zeroState p.stateBytes) = zeroState p.capacityBytes := by
  funext i
  simp only [capacityPart, zeroState, dite_eq_ite, ite_self]

/-- Absorbing any rate block preserves the capacity portion of the state. -/
lemma capacityPart_absorbBlock (p : Parameters) (state : ByteState p.stateBytes)
    (block : ByteState p.rateBytes) :
    capacityPart p (absorbBlock p state block) = capacityPart p state := by
  funext i
  simp only [capacityPart, absorbBlock]
  split_ifs with h1 h2
  · omega
  · rfl
  · rfl

/-- When `rateBytes ≤ stateBytes`, absorbing a block is injective in the block at every state. -/
lemma absorbBlock_injective (p : Parameters) (hr : p.rateBytes ≤ p.stateBytes)
    (state : ByteState p.stateBytes) :
    Function.Injective (absorbBlock p state) := by
  intro a b h
  funext i
  have hi : i.val < p.stateBytes := Nat.lt_of_lt_of_le i.isLt hr
  have he := congrFun h ⟨i.val, hi⟩
  simp only [absorbBlock, i.isLt, ↓reduceDIte] at he
  have hcancel := congrArg (fun x => state ⟨i.val, hi⟩ ^^^ x) he
  simpa only [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor] using hcancel

/-- The number of rate blocks produced by padding an input of length `bytes`. -/
def paddedBlockCount (p : Parameters) (bytes : Nat) : Nat :=
  (bytes + p.rateBytes) / p.rateBytes

/-- Multi-rate `pad10*1` byte padding with domain-separation suffix [1, §5.1]: append `p.suffix`,
pad with zero bytes to a multiple of `p.rateBytes`, and set the final byte's high bit `0x80`. -/
def spongePadding (p : Parameters) (input : List (BitVec 8)) : List (BitVec 8) :=
  let padZeros := (p.rateBytes - (input.length + 1) % p.rateBytes) % p.rateBytes
  let raw := input ++ [p.suffix] ++ List.replicate padZeros 0
  raw.dropLast ++ [raw.getLastD 0 ||| 0x80]

lemma paddedBlockCount_mono (p : Parameters) {a b : Nat} (hab : a ≤ b) :
    paddedBlockCount p a ≤ paddedBlockCount p b := by
  apply Nat.div_le_div_right
  omega

lemma paddedBlockCount_pos (p : Parameters) (bytes : Nat) (hr : 0 < p.rateBytes) :
    0 < paddedBlockCount p bytes := by
  apply Nat.div_pos
  · omega
  · exact hr

/-- Multi-rate padding rounds the input to `paddedBlockCount p input.length` rate blocks. -/
theorem spongePadding_length (p : Parameters) (hr : 0 < p.rateBytes) (input : List (BitVec 8)) :
    (spongePadding p input).length = paddedBlockCount p input.length * p.rateBytes := by
  simp only [spongePadding, List.length_append, List.length_dropLast, List.length_singleton,
    List.length_replicate, paddedBlockCount]
  rw [Nat.sub_add_cancel (by omega : 1 ≤ input.length + 1 +
    (p.rateBytes - (input.length + 1) % p.rateBytes) % p.rateBytes)]
  rw [show input.length + p.rateBytes = (input.length + 1) + p.rateBytes - 1 by omega]
  generalize input.length + 1 = a
  generalize p.rateBytes = r at hr ⊢
  have hm := Nat.mod_lt a hr
  have he := Nat.mod_add_div a r
  rw [Nat.mul_comm r] at he
  by_cases hz : a % r = 0
  · have hq : (a + r - 1) / r = a / r := by
      apply Nat.div_eq_of_lt_le
      · omega
      · simp only [Nat.add_mul, Nat.one_mul]; omega
    rw [hq, hz, Nat.sub_zero, Nat.mod_self]
    omega
  · have hpad : (r - a % r) % r = r - a % r := Nat.mod_eq_of_lt (by omega)
    have hq : (a + r - 1) / r = a / r + 1 := by
      apply Nat.div_eq_of_lt_le
      · simp only [Nat.add_mul, Nat.one_mul]; omega
      · simp only [Nat.add_mul, Nat.one_mul]; omega
    rw [hq, hpad]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- The length of `spongePadding p input` is divisible by `p.rateBytes`. -/
theorem spongePadding_length_dvd (p : Parameters) (hr : 0 < p.rateBytes)
    (input : List (BitVec 8)) :
    p.rateBytes ∣ (spongePadding p input).length := by
  rw [spongePadding_length p hr input]
  exact Nat.dvd_mul_left p.rateBytes (paddedBlockCount p input.length)

lemma spongePadding_ne_nil (p : Parameters) (hr : 0 < p.rateBytes) (input : List (BitVec 8)) :
    spongePadding p input ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [spongePadding_length p hr input, List.length_nil] at hl
  have hpos : 0 < paddedBlockCount p input.length * p.rateBytes :=
    Nat.mul_pos (paddedBlockCount_pos p input.length hr) hr
  omega

/-- A nonzero marker symbol separates an arbitrary prefix from trailing zero padding. -/
lemma append_marker_zeros_injective {α : Type*} {marker zero : α} (hne : marker ≠ zero)
    (first second : List α) (n m : Nat)
    (he : first ++ marker :: List.replicate n zero =
      second ++ marker :: List.replicate m zero) :
    first = second := by
  have cancel (n m : Nat) (a b : List α)
      (h : List.replicate n zero ++ marker :: a = List.replicate m zero ++ marker :: b) :
      a = b := by
    induction n generalizing m with
    | zero =>
      cases m with
      | zero => exact (List.cons.inj h).2
      | succ m => exact False.elim (hne (List.cons.inj h).1)
    | succ n ih =>
      cases m with
      | zero => exact False.elim (hne (List.cons.inj h).1.symm)
      | succ m => exact ih m (List.cons.inj h).2
  apply List.reverse_inj.mp
  apply cancel n m
  simpa only [List.reverse_append, List.reverse_cons, List.reverse_replicate, List.append_assoc,
    List.singleton_append] using congrArg List.reverse he

/-- A nonzero domain suffix in the low seven bits makes `spongePadding p` injective. -/
theorem spongePadding_injective (p : Parameters) (hs : p.suffix ≠ 0)
    (hlow : p.suffix.toNat < 128) :
    Function.Injective (spongePadding p) := by
  have hmark : p.suffix ||| (0x80 : BitVec 8) ≠ 0x80 := by
    have hlo : (p.suffix ||| (0x80 : BitVec 8)).toNat % 128 = p.suffix.toNat := by
      change (p.suffix.toNat ||| 128) % (2 ^ 7) = p.suffix.toNat
      rw [Nat.or_mod_two_pow, Nat.mod_eq_of_lt hlow]
      have hzero : 128 % 2 ^ 7 = 0 := by omega
      rw [hzero, Nat.or_zero]
    intro he
    rw [he] at hlo
    change 0 = p.suffix.toNat at hlo
    exact hs (BitVec.eq_of_toNat_eq hlo.symm)
  let zeros (input : List (BitVec 8)) :=
    (p.rateBytes - (input.length + 1) % p.rateBytes) % p.rateBytes
  have shape (input : List (BitVec 8)) : spongePadding p input = match zeros input with
      | 0 => input ++ [p.suffix ||| 0x80]
      | n + 1 => input ++ [p.suffix] ++ List.replicate n 0 ++ [0x80] := by
    unfold spongePadding
    change _ = match zeros input with | 0 => _ | n + 1 => _
    cases hz : zeros input with
    | zero =>
      simp only [zeros] at hz
      simp only [hz, List.replicate_zero, List.append_nil, List.dropLast_concat,
        List.getLastD_concat]
    | succ n =>
      simp only [zeros] at hz
      simp only [hz, List.replicate_succ', ← List.append_assoc, List.dropLast_concat,
        List.getLastD_concat]
      rfl
  intro first second he
  rw [shape first, shape second] at he
  cases hf : zeros first with
  | zero =>
    cases hh : zeros second with
    | zero =>
      simp only [hf, hh] at he
      exact List.append_cancel_right he
    | succ m =>
      simp only [hf, hh] at he
      exact False.elim (hmark (by
        simpa only [List.getLastD_concat] using congrArg (fun xs => xs.getLastD 0) he))
  | succ n =>
    cases hh : zeros second with
    | zero =>
      simp only [hf, hh] at he
      exact False.elim (hmark (by
        simpa only [List.getLastD_concat] using congrArg (fun xs => xs.getLastD 0) he.symm))
    | succ m =>
      simp only [hf, hh] at he
      have hc := List.append_cancel_right he
      apply append_marker_zeros_injective hs first second n m
      simpa only [List.append_assoc, List.singleton_append] using hc

/-- Prepending a full rate block leaves the remaining padding unchanged. -/
lemma spongePadding_append_block (p : Parameters) (first rest : List (BitVec 8))
    (hf : first.length = p.rateBytes) :
    spongePadding p (first ++ rest) = first ++ spongePadding p rest := by
  have hm : ((first ++ rest).length + 1) % p.rateBytes =
      (rest.length + 1) % p.rateBytes := by
    rw [List.length_append, hf, Nat.add_assoc, Nat.add_mod_left]
  unfold spongePadding
  rw [hm]
  cases hz : (p.rateBytes - (rest.length + 1) % p.rateBytes) % p.rateBytes with
  | zero =>
    simp only [List.replicate_zero, List.append_nil, ← List.append_assoc,
      List.dropLast_concat, List.getLastD_concat]
  | succ n =>
    simp only [List.replicate_succ', ← List.append_assoc, List.dropLast_concat,
      List.getLastD_concat]

/-- The padded input split into consecutive fixed-width rate blocks. -/
def paddedBlocks (p : Parameters) (input : List (BitVec 8)) : List (ByteState p.rateBytes) :=
  let padded := spongePadding p input
  (List.range (paddedBlockCount p input.length)).map fun k i =>
    padded.getD (p.rateBytes * k + i.val) 0

/-- The number of rate blocks equals `paddedBlockCount p input.length`. -/
lemma length_paddedBlocks (p : Parameters) (input : List (BitVec 8)) :
    (paddedBlocks p input).length = paddedBlockCount p input.length := by
  simp only [paddedBlocks, List.length_map, List.length_range]

/-- Every padded input has at least one rate block when `0 < p.rateBytes`. -/
lemma paddedBlocks_ne_nil (p : Parameters) (hr : 0 < p.rateBytes) (input : List (BitVec 8)) :
    paddedBlocks p input ≠ [] := by
  intro h
  have hl := congrArg List.length h
  rw [length_paddedBlocks, List.length_nil] at hl
  exact (Nat.ne_of_gt (paddedBlockCount_pos p input.length hr)) hl

/-- Flattening fixed-width slices of a list whose length is `m * r` recovers the list. -/
lemma flatten_blockSlices {α : Type*} (xs : List α) (m r : Nat) (fallback : α)
    (hlen : xs.length = m * r) :
    ((List.range m).map fun k =>
      List.ofFn (fun i : Fin r => xs.getD (r * k + i.val) fallback)).flatten = xs := by
  calc
    _ = (List.ofFn fun k : Fin m =>
          List.ofFn fun i : Fin r => xs.getD (r * k.val + i.val) fallback).flatten := by
      apply congrArg List.flatten
      apply List.ext_getElem
      · simp only [List.length_map, List.length_range, List.length_ofFn]
      · intro i hi hj
        simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    -- Reading the blocks in order gives the flat byte at index `r * k + i`.
    _ = List.ofFn (fun i : Fin (r * m) => xs.getD i.val fallback) :=
      (List.ofFn_mul' (m := r) (n := m) (fun i => xs.getD i.val fallback)).symm
    _ = xs := by
      apply List.ext_getElem
      · simpa only [List.length_ofFn, Nat.mul_comm r m] using hlen.symm
      · intro i hi hj
        simp only [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
          Option.getD_some]

/-- Flattening `paddedBlocks p input` recovers the exact padded byte string. -/
lemma flatten_paddedBlocks (p : Parameters) (hr : 0 < p.rateBytes) (input : List (BitVec 8)) :
    ((paddedBlocks p input).map List.ofFn).flatten = spongePadding p input := by
  simp only [paddedBlocks, List.map_map, Function.comp_def]
  exact flatten_blockSlices (spongePadding p input) (paddedBlockCount p input.length)
    p.rateBytes 0 (spongePadding_length p hr input)

/-- Distinct inputs produce distinct sequences of rate blocks under valid padding parameters. -/
theorem paddedBlocks_injective (p : Parameters) (hr : 0 < p.rateBytes) (hs : p.suffix ≠ 0)
    (hlow : p.suffix.toNat < 128) :
    Function.Injective (paddedBlocks p) := by
  intro first second he
  apply spongePadding_injective p hs hlow
  rw [← flatten_paddedBlocks p hr first, ← flatten_paddedBlocks p hr second, he]

/-- Prepending a full rate block adds that block at the front of `paddedBlocks`. -/
lemma paddedBlocks_append_block (p : Parameters) (hr : 0 < p.rateBytes)
    (first rest : List (BitVec 8)) (hf : first.length = p.rateBytes) :
    paddedBlocks p (first ++ rest) =
      (fun i => first.getD i.val 0) :: paddedBlocks p rest := by
  have hcost : paddedBlockCount p (first ++ rest).length = paddedBlockCount p rest.length + 1 := by
    simp only [paddedBlockCount, List.length_append, hf]
    rw [show p.rateBytes + rest.length + p.rateBytes =
      (rest.length + p.rateBytes) + p.rateBytes by omega, Nat.add_div_right _ hr]
  simp only [paddedBlocks, spongePadding_append_block p first rest hf, hcost,
    List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · funext i
    have hi : i.val < first.length := by rw [hf]; exact i.isLt
    simp only [Nat.mul_zero, Nat.zero_add, List.getD_eq_getElem?_getD,
      List.getElem?_append_left hi]
  · apply List.map_congr_left
    intro k _
    funext i
    dsimp only [Function.comp_def]
    have hge : first.length ≤ p.rateBytes * (k + 1) + i.val := by
      rw [hf, Nat.mul_add, Nat.mul_one]
      omega
    have hsub : p.rateBytes * (k + 1) + i.val - first.length = p.rateBytes * k + i.val := by
      rw [hf, Nat.mul_add, Nat.mul_one]
      omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hge, hsub]

/-- Prepending a fixed-width rate block prefixes that block to `paddedBlocks`. -/
lemma paddedBlocks_append_rateBlock (p : Parameters) (hr : 0 < p.rateBytes)
    (first : ByteState p.rateBytes) (rest : List (BitVec 8)) :
    paddedBlocks p (List.ofFn first ++ rest) = first :: paddedBlocks p rest := by
  rw [paddedBlocks_append_block p hr _ _ (List.length_ofFn ..)]
  congr 1
  funext i
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, ↓reduceDIte,
    Option.getD_some]

/-- The sponge hash function over an arbitrary state permutation `π` [1, §4]. -/
def spongeHash (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (input : List (BitVec 8)) : ByteState p.outputBytes :=
  digestPart p (absorbBlocks (absorbBlock p) π (zeroState p.stateBytes) (paddedBlocks p input))

/-- The permutation inputs queried while evaluating `spongeHash p π input`. -/
def spongeCalls (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (input : List (BitVec 8)) : List (ByteState p.stateBytes) :=
  absorptionCalls (absorbBlock p) π (zeroState p.stateBytes) (paddedBlocks p input)

/-- Record all forward permutation edges queried while evaluating `spongeHash p π input`. -/
def recordSponge (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (input : List (BitVec 8)) :
    List (PermutationEdge (ByteState p.stateBytes)) :=
  recordAbsorption (absorbBlock p) π table (zeroState p.stateBytes) (paddedBlocks p input)

lemma recordSponge_subset (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (input : List (BitVec 8)) :
    ∀ edge ∈ table, edge ∈ recordSponge p π table input :=
  recordAbsorption_subset (absorbBlock p) π table (zeroState p.stateBytes) (paddedBlocks p input)

lemma length_recordSponge_le (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (input : List (BitVec 8)) :
    (recordSponge p π table input).length ≤ table.length + paddedBlockCount p input.length := by
  rw [← length_paddedBlocks p input]
  exact length_recordAbsorption_le (absorbBlock p) π table (zeroState p.stateBytes)
    (paddedBlocks p input)

lemma recordSponge_agrees (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (ha : AgreesWith table π)
    (input : List (BitVec 8)) :
    AgreesWith (recordSponge p π table input) π :=
  recordAbsorption_agrees (absorbBlock p) π table ha (zeroState p.stateBytes)
    (paddedBlocks p input)

lemma recordSponge_covers (p : Parameters) (π : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (input : List (BitVec 8)) :
    ∀ x ∈ spongeCalls p π input, ∃ edge ∈ recordSponge p π table input, edge.input = x :=
  recordAbsorption_covers (absorbBlock p) π table (zeroState p.stateBytes) (paddedBlocks p input)

/-- Any two permutations agreeing with `recordSponge p π table input` record the same edges and
produce the same sponge digest on `input`. -/
theorem recordSponge_local (p : Parameters) (π ρ : Equiv.Perm (ByteState p.stateBytes))
    (table : List (PermutationEdge (ByteState p.stateBytes))) (input : List (BitVec 8))
    (hπ : AgreesWith (recordSponge p π table input) π)
    (hρ : AgreesWith (recordSponge p π table input) ρ) :
    recordSponge p ρ table input = recordSponge p π table input ∧
      spongeHash p ρ input = spongeHash p π input := by
  have hloc :=
    recordAbsorption_local (absorbBlock p) π ρ table (zeroState p.stateBytes)
      (paddedBlocks p input) hπ hρ
  exact ⟨hloc.1, congrArg (digestPart p) hloc.2⟩

/-- No two distinct covered inputs can collide under `spongeHash` when the table is
capacity-collision-free and forward outputs have distinct digests [2, §4.3]. -/
theorem input_eq_of_spongeHash_eq (p : Parameters) (hp : p.Valid)
    (table : List (PermutationEdge (ByteState p.stateBytes)))
    -- `hg` separates reached states by capacity; `hdig` separates forward outputs by digest.
    (hg : CapacityCollisionFree (capacityPart p) (zeroState p.capacityBytes) table)
    (hdig : Set.InjOn (digestPart p) (forwardOutputs table))
    (π : Equiv.Perm (ByteState p.stateBytes)) (ha : AgreesWith table π)
    (first second : List (BitVec 8))
    (hf : ∀ x ∈ spongeCalls p π first, ∃ edge ∈ table, edge.input = x)
    (hs : ∀ x ∈ spongeCalls p π second, ∃ edge ∈ table, edge.input = x)
    (he : spongeHash p π first = spongeHash p π second) :
    first = second := by
  obtain ⟨rate_pos, rate_lt_state, _, _, suffix_ne, suffix_low⟩ := hp
  -- Padding gives each covered message a last forward output, where the digest is injective.
  have reached (msg : List (BitVec 8))
      (covered : ∀ x ∈ spongeCalls p π msg, ∃ edge ∈ table, edge.input = x) :
      absorbBlocks (absorbBlock p) π (zeroState p.stateBytes) (paddedBlocks p msg) ∈
        forwardOutputs table :=
    absorbBlocks_mem_forwardOutputs (capacityPart p) (zeroState p.capacityBytes)
      (absorbBlock p) (capacityPart_absorbBlock p) table hg π ha (zeroState p.stateBytes)
      (Or.inl (capacityPart_zeroState p)) _ (paddedBlocks_ne_nil p rate_pos msg) covered
  have hstate := hdig (reached first hf) (reached second hs) he
  -- The common final state fixes the rooted path, hence every absorbed block.
  have hblocks : paddedBlocks p first = paddedBlocks p second :=
    blocks_eq_of_absorbBlocks_eq (capacityPart p) (zeroState p.capacityBytes)
      (absorbBlock p) (capacityPart_absorbBlock p)
      (absorbBlock_injective p rate_lt_state.le)
      (zeroState p.stateBytes) (capacityPart_zeroState p) table hg π ha
      (paddedBlocks p first) (paddedBlocks p second) hf hs hstate
  exact paddedBlocks_injective p rate_pos suffix_ne suffix_low hblocks

end Commons.Sponge

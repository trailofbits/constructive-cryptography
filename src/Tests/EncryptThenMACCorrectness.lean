module

public import Commons.Constructions.EncryptThenMAC.Correctness

/-!
# Encrypt-then-MAC correctness clients

The symbolic client supplies only the two correctness contracts. In the concrete client,
encryption returns its retained fair bit and the MAC returns its own retained fair bit.
The unequal pair `(false, true)` has probability `1/4`, distinguishing independent keys from
one shared bit; decryption of that pair retains the same probability and returns the message.
-/

@[expose] public section

namespace EncryptThenMACCorrectnessTests

open Commons SystemAlgebra Probability Probability.Distribution

/-- Supplied component contracts recover a message from its supported assembly reply. -/
example
    -- `K`, `L` carry independent component keys; `M`, `C`, `T` are the interface alphabets.
    {K L M C T : Type} [Fintype K] [Fintype L] [Fintype M] [Fintype C] [Fintype T]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [DecidableEq C]
    -- The client supplies each component and its correctness proof.
    (scheme : SymmetricEncryption K M C) (mac : MAC L C T)
    (henc : scheme.Correct) (hmac : mac.Correct) (m : M) (ct : C × T) :
    (encryptThenMAC.system scheme mac 2).1
        [(⟨.enc, m⟩, ⟨.enc, ct⟩), (⟨.dec, ct⟩, ⟨.dec, some m⟩)] =
      (encryptThenMAC.system scheme mac 2).1 [(⟨.enc, m⟩, ⟨.enc, ct⟩)] :=
  encryptThenMAC.system.enc_dec_eq_of_correct scheme mac henc hmac 2 [] (by rfl) m ct

noncomputable section

/-- A retained fair key bit is the ciphertext of `()`; decryption accepts exactly that bit. -/
def cipher : SymmetricEncryption Bool Unit Bool where
  gen := 𝒰[Bool]
  enc := fun k _ => ProbDist.single k
  dec := fun k c => if c == k then some () else none

/-- A retained fair key bit is the tag of every ciphertext; verification accepts exactly it. -/
def mac : MAC Bool Bool Bool where
  gen := 𝒰[Bool]
  tag := fun k _ => ProbDist.single k
  verify := fun k _ t => t == k

/-- Every supported ciphertext equals the retained key, so decryption returns `()`. -/
lemma cipher_correct : cipher.Correct := by
  intro k _ m c hc
  have he : c = k := (Finsupp.mem_support_single _ _ _).mp hc |>.1
  subst c
  cases m
  simp only [cipher, beq_self_eq_true, ↓reduceIte]

/-- Every supported tag equals the retained authentication key, so it verifies. -/
lemma mac_correct : mac.Correct := by
  intro k _ m t ht
  have he : t = k := (Finsupp.mem_support_single _ _ _).mp ht |>.1
  subst t
  simp only [mac, beq_self_eq_true]

/-- Unequal encryption/MAC key bits have mass `1/4` under the actual assembly. -/
lemma independent_keys_mass :
    (encryptThenMAC.system cipher mac 2).1 [(⟨.enc, ()⟩, ⟨.enc, (false, true)⟩)] = 1 / 4 := by
  have hd : (AE Unit (Bool × Bool) 2).inputDomain [] ⟨.enc, ()⟩ := by
    refine ⟨List.cons_ne_nil _ _, ?_⟩
    change 1 ≤ 2
    omega
  let h : List ((Σ i, (AE Unit (Bool × Bool) 2).X i) ×
      (Σ i, (AE Unit (Bool × Bool) 2).Y i)) :=
    [] ++ [(⟨.enc, ()⟩, ⟨.enc, (false, true)⟩)]
  change (encryptThenMAC.system cipher mac 2).1 h = _
  -- The two generated bits are independent coordinates of the retained product law.
  rw [encryptThenMAC.system.eq_keyed, TypedSystem.keyed_mass]
  change (prodProbDist cipher.gen mac.gen).1.sum (fun keys w => w *
    (TypedSystem.ofMemoryless (AE Unit (Bool × Bool) 2)
      (encryptThenMAC.system.replyLaw cipher mac keys)).1 h) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, TypedSystem.ofMemoryless_val,
    h, RandomSystem.memoryless_snoc, ite_eq_left hd, RandomSystem.mass_nil,
    RandomSystem.portLaw_apply_mk, encryptThenMAC.system.replyLaw, cipher, mac,
    ProbDist.jointLaw, ProbDist.bind_val, ProbDist.map_val, ProbDist.single,
    bindK_single, one_smul, fTransform_single, prodProbDist, Distribution.prod_apply,
    ProbDist.uniform, uniform_apply, Fintype.card_bool, Finsupp.single_apply,
    Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, and_true, and_false,
    ↓reduceIte, mul_one, mul_zero, zero_add, add_zero]
  norm_num

/-- Decryption retains both component keys after their unequal encryption/tag reply. -/
lemma retained_keys_roundtrip :
    (encryptThenMAC.system cipher mac 2).1
      [(⟨.enc, ()⟩, ⟨.enc, (false, true)⟩),
       (⟨.dec, (false, true)⟩, ⟨.dec, some ()⟩)] = 1 / 4 := by
  exact (encryptThenMAC.system.enc_dec_eq_of_correct cipher mac cipher_correct mac_correct
    2 [] (by rfl) () (false, true)).trans independent_keys_mass

end

#print axioms AE.system.eq_keyed
#print axioms MAC.system.eq_keyed
#print axioms encryptThenMAC.system.eq_keyed
#print axioms encryptThenMAC.system.enc_dec_eq_of_correct
#print axioms retained_keys_roundtrip

end EncryptThenMACCorrectnessTests

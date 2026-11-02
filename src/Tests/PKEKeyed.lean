module

public import Commons.Definitions.PublicKeyEncryption.Keyed

/-!
# PKE retained keys and fresh replies

`four_exchange_mass` samples correlated keys `(b, !b)` for a fair bit `b`, observes the public
key, asks the same encryption query twice with different replies, and decrypts. The consistent
transcript has mass `1/8`; an incompatible decryption reply has mass zero. The transcript checks
fresh encryption coins and the key correlation between public-key publication and decryption.
-/

@[expose] public section

open SystemAlgebra Probability Probability.Distribution Commons

namespace Tests.PKEKeyed

noncomputable section

/-- Retain `(b, !b)` for a fair bit `b`; each encryption returns a fresh fair bit.
Decryption returns `some ()` exactly when the secret key is true. -/
def scheme : PublicKeyEncryption Bool Bool Unit Bool where
  gen := (𝒰[Bool]).map (fun b => (b, !b))
  enc := fun _ _ => 𝒰[Bool]
  dec := fun sk _ => if sk then some () else none

/-- With public key `true`, two unequal ciphertexts and decryption `none` have mass `1/8`;
a decryption reply `some ()` is incompatible with the retained secret key. -/
lemma four_exchange_mass
    -- `d` selects `some ()` when true and `none` when false at the decryption port.
    (d : Bool) :
    (PKE.system.perPort (budget := fun _ => 4) scheme).1
      [(⟨.publicKey, ()⟩, ⟨.publicKey, true⟩),
        (⟨.enc, ()⟩, ⟨.enc, false⟩), (⟨.enc, ()⟩, ⟨.enc, true⟩),
        (⟨.dec, true⟩, ⟨.dec, if d then some () else none⟩)] =
      (if d then 0 else 1 / 8) := by
  -- Each of these four queries is admitted by every per-port allowance of four.
  have admitted (h : List ((Σ i, (PKE Bool Unit Bool 0).X i) ×
      (Σ i, (PKE Bool Unit Bool 0).Y i))) (x : Σ i, (PKE Bool Unit Bool 0).X i)
      (hl : h.length < 4) : (PKE.perPort Bool Unit Bool (fun _ => 4)).inputDomain h x := by
    refine ⟨List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _), fun i => ?_⟩
    apply (length_restrict_le i _).trans
    simp only [List.length_append, List.length_map, List.length_singleton]
    omega
  -- Express the four exchanges as successive extensions for the chain rule.
  let h : List ((Σ i, (PKE Bool Unit Bool 0).X i) ×
      (Σ i, (PKE Bool Unit Bool 0).Y i)) :=
    ((([] ++ [(⟨.publicKey, ()⟩, ⟨.publicKey, true⟩)]) ++
      [(⟨.enc, ()⟩, ⟨.enc, false⟩)]) ++ [(⟨.enc, ()⟩, ⟨.enc, true⟩)] ++
      [(⟨.dec, true⟩, ⟨.dec, if d then some () else none⟩)])
  change (PKE.system.perPort (budget := fun _ => 4) scheme).1 h = _
  -- Average the whole transcript over the one shared bit that selects both keys.
  rw [PKE.system.perPort_eq_keyed, TypedSystem.keyed]
  change (TypedSystem.sample
    (fTransform (fun b : Bool => (b, !b)) (uniform Bool))
    (fun k => TypedSystem.ofMemoryless (PKE.perPort Bool Unit Bool (fun _ => 4))
      (PKE.system.replyLaw scheme k))).1 h = _
  rw [TypedSystem.sample_fTransform, TypedSystem.sample_mass]
  change (uniform Bool).sum (fun b w => w *
    (TypedSystem.ofMemoryless (PKE.perPort Bool Unit Bool (fun _ => 4))
      (PKE.system.replyLaw scheme (b, !b))).1 h) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [Fintype.sum_bool, uniform_apply, Fintype.card_bool,
    TypedSystem.ofMemoryless_val, Bool.not_false, Bool.not_true]
  -- The observed public key selects `b = true`; its two encryption draws contribute one half each.
  cases d <;> simp only [h, RandomSystem.memoryless_snoc, RandomSystem.mass_nil,
    RandomSystem.portLaw_apply_mk, PKE.system.replyLaw, scheme, ProbDist.single,
    Finsupp.single_eq_same, ProbDist.uniform, uniform_apply, Fintype.card_bool,
    Bool.false_eq_true, ite_false, ite_true, Finsupp.single_apply,
    reduceCtorEq, ite_self, zero_mul, mul_zero, zero_add]
  split_ifs with h₄ h₃ h₂ h₁
  · norm_num
  -- All remaining branches deny an admitted prefix.
  all_goals
    exfalso
    first | apply h₁ | apply h₂ | apply h₃ | apply h₄
    apply admitted
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end

#print axioms PublicKeyEncryption.encryptions_map
#print axioms TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
#print axioms PKE.system.perPort_eq_keyed
#print axioms PKE.INDCCA.systems_eq_keyed
#print axioms four_exchange_mass

end Tests.PKEKeyed

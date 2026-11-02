module

public import Commons.Constructions.HashAndSign

/-!
# Hash-and-sign clients

The client uses a constant hash with the supplied construction. Its component retains
correlated keys `(b, !b)` and signs by pairing the secret key with a fresh fair bit. Two
messages therefore share one digest but can receive different signatures. `four_exchange_mass`
checks the retained public key, these fresh replies and verification under the same pair.
-/

@[expose] public section

namespace HashAndSignTests

open Commons SystemAlgebra Probability Probability.Distribution

noncomputable section

/-- The converter exists with empty public-key and signature alphabets. -/
example : TypedConverter (Signing Empty Bool Empty 1) (Signing Empty Unit Empty 1) :=
  hashAndSign (fun _ => ()) 1

/-- Retain `(b, !b)` for a fair bit `b`; sign `()` with `(!b, r)` for a fresh fair bit `r`.
Verification checks the first signature coordinate against the public key's complement. -/
def scheme : SignatureScheme Bool Bool Unit (Bool × Bool) where
  gen := (𝒰[Bool]).map (fun b => (b, !b))
  sign := fun sk _ => prodProbDist (ProbDist.single sk) 𝒰[Bool]
  verify := fun pk _ σ => σ.1 == !pk

/-- At supported keys and signatures, `σ.1 = sk = !pk`, so verification accepts. -/
lemma scheme_correct : scheme.Correct := by
  intro pk sk hkeys m σ hσ
  obtain ⟨b, _, hkeys⟩ := mem_support_fTransform _ _ hkeys
  have hfirst := (Finset.mem_product.mp (support_prod_subset _ _ hσ)).1
  have hs : σ.1 = sk := (Finsupp.mem_support_single _ _ _).mp hfirst |>.1
  change (σ.1 == !pk) = true
  rw [hs]
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hkeys
  exact beq_self_eq_true _

/-- At budget `q`, hash Boolean messages to `()` and use `scheme`'s one retained pair. -/
def client
    -- `q` is the shared outside and inside query allowance.
    (q : ℕ) : TypedSystem (Signing Bool Bool (Bool × Bool) q) :=
  hashAndSign.system (fun _ => ()) scheme q

/-- Supplied signature correctness makes the constant-hash client accept its signing reply. -/
example
    -- `m` is either Boolean message; `σ` is the observed signing reply.
    (m : Bool) (σ : Bool × Bool) :
    (client 2).1 [(⟨.sign, m⟩, ⟨.sign, σ⟩), (⟨.verify, (m, σ)⟩, ⟨.verify, true⟩)] =
      (client 2).1 [(⟨.sign, m⟩, ⟨.sign, σ⟩)] :=
  hashAndSign.system.sign_verify_eq_of_correct
    (fun _ => ()) scheme scheme_correct 2 [] (by rfl) m σ

/-- Public key `true` and two distinct supported signatures have mass `1/2 · 1/2 · 1/2 = 1/8`
when `valid = true`, and mass zero when `valid = false`. -/
lemma four_exchange_mass
    -- `valid` is the observed verification reply: `true` is forced by the supported signature.
    (valid : Bool) :
    (client 4).1
      [(⟨.publicKey, ()⟩, ⟨.publicKey, true⟩),
       (⟨.sign, false⟩, ⟨.sign, (false, false)⟩),
       (⟨.sign, true⟩, ⟨.sign, (false, true)⟩),
       (⟨.verify, (true, (false, true))⟩, ⟨.verify, valid⟩)] =
      if valid then 1 / 8 else 0 := by
  -- Write successive exchanges as extensions for the fixed-key chain rule.
  let h : List ((Σ i, (Signing Bool Bool (Bool × Bool) 0).X i) ×
      (Σ i, (Signing Bool Bool (Bool × Bool) 0).Y i)) :=
    ((([] ++ [(⟨.publicKey, ()⟩, ⟨.publicKey, true⟩)]) ++
      [(⟨.sign, false⟩, ⟨.sign, (false, false)⟩)]) ++
      [(⟨.sign, true⟩, ⟨.sign, (false, true)⟩)]) ++
      [(⟨.verify, (true, (false, true))⟩, ⟨.verify, valid⟩)]
  change (client 4).1 h = _
  -- Average the complete transcript over the one fair bit controlling both keys.
  rw [client, hashAndSign.system.eq_keyed, TypedSystem.keyed]
  change (TypedSystem.sample
    (fTransform (fun b : Bool => (b, !b)) (uniform Bool))
    (fun keys => TypedSystem.ofMemoryless (Signing Bool Bool (Bool × Bool) 4)
      (hashAndSign.system.replyLaw (fun _ => ()) scheme keys))).1 h = _
  rw [TypedSystem.sample_fTransform, TypedSystem.sample_mass]
  change (uniform Bool).sum (fun b w => w *
    (TypedSystem.ofMemoryless (Signing Bool Bool (Bool × Bool) 4)
      (hashAndSign.system.replyLaw (fun _ => ()) scheme (b, !b))).1 h) = _
  rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
  simp only [Fintype.sum_bool, uniform_apply, Fintype.card_bool,
    TypedSystem.ofMemoryless_val, Bool.not_false, Bool.not_true]
  -- Publication fixes `b = true`; the two fresh signing bits contribute one half each.
  cases valid <;> simp only [h, RandomSystem.memoryless_snoc, RandomSystem.mass_nil,
    RandomSystem.portLaw_apply_mk, hashAndSign.system.replyLaw, hashAndSign.input,
    SignatureScheme.system.replyLaw, scheme, prodProbDist, Distribution.prod_apply,
    ProbDist.single, Finsupp.single_eq_same, ProbDist.uniform, uniform_apply, Fintype.card_bool,
    Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false,
    beq_self_eq_true,
    ite_false, ite_true, Finsupp.single_apply, ite_self,
    zero_mul, mul_zero, zero_add]
  split_ifs with h₄ h₃ h₂ h₁
  · norm_num
  -- A remaining branch would deny an admitted prefix.
  all_goals
    exfalso
    first | apply h₁ | apply h₂ | apply h₃ | apply h₄
    apply Interface.queryBudget_inputDomain_iff.mpr
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

end

#print axioms SignatureScheme.system.eq_keyed
#print axioms hashAndSign.system.eq_keyed
#print axioms hashAndSign.system.sign_verify_eq_of_correct
#print axioms four_exchange_mass

end HashAndSignTests

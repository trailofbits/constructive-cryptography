module

public import Commons.Definitions.PublicKeyEncryption
public import Commons.Definitions.Cipher
public import RandomSystems.Typed.Keyed

/-!
# Retained-key clients

The PKE assembly retains one generated pair, exposes its public key, samples encryption
replies freshly, and decrypts with its secret key. Its private-key type needs no finite
enumeration. The block-cipher contract identifies deterministic keyed replies with the
existing scheme system.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

open Probability Probability.Distribution SystemAlgebra Commons

noncomputable section

/-- Retain the generated pair; encrypt freshly under its public key.
[1, Definition 11.1, p. 436]: encryption is “a probabilistic algorithm”. -/
example
    -- `PK`, `M`, `C` are the finite interface alphabets; `SK` carries the retained secret key.
    -- Only the support of the generated key pair must be finite.
    {PK SK M C : Type} [Fintype PK] [Fintype M] [Fintype C]
    -- `scheme` supplies the algorithms; `q` bounds calls at each PKE port.
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ)
    -- `h` is the past transcript, followed by encryption query `m` and proposed reply `c`.
    (h : List ((Σ i, (PKE.perPort PK M C q).X i) ×
      (Σ i, (PKE.perPort PK M C q).Y i))) (m : M) (c : C)
    (admitted : (PKE.perPort PK M C q).domain (h.map Prod.fst ++ [⟨.enc, m⟩])) :
    let ν : PK × SK → ∀ i, (PKE.perPort PK M C q).X i →
        ProbDist ((PKE.perPort PK M C q).Y i) := fun
      | (pk, _), .publicKey => fun _ => ProbDist.single pk
      | (pk, _), .enc => scheme.enc pk
      | (_, sk), .dec => fun c => ProbDist.single (scheme.dec sk c)
    (TypedSystem.keyed scheme.gen ν).1 (h ++ [(⟨.enc, m⟩, ⟨.enc, c⟩)]) =
      ∑ keys ∈ scheme.gen.1.support, scheme.gen keys *
        (TypedSystem.ofMemoryless _ (ν keys)).1 h * scheme.enc keys.1 m c := by
  exact TypedSystem.keyed_snoc _ _ h .enc m c admitted

/-- The existing block-cipher system retains one uniform key for all evaluations. -/
example
    -- `K` carries the uniformly sampled key, and `X` the blocks.
    {K X : Type} [Fintype K] [Nonempty K] [Fintype X]
    -- `cipher` supplies the permutation at each key; `q` bounds evaluation calls.
    (cipher : BlockCipher K X) (q : ℕ) :
    (TypedSystem.keyed 𝒰[K] fun k _ x => ProbDist.single (cipher.encrypt k x) :
      TypedSystem (Evaluation X X q)) = cipher.system :=
  TypedSystem.keyed_single _ _

/-- Two reads of one retained Boolean cannot disagree, even with allowance for both queries. -/
example :
    (TypedSystem.keyed 𝒰[Bool] (fun b _ _ => ProbDist.single b) :
      TypedSystem (Interface.source Bool 2)).1
        [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)] = 0 := by
  rw [TypedSystem.keyed_single, TypedSystem.sample_mass]
  apply Finset.sum_eq_zero
  intro b _
  have hzero : (TypedSystem.ofFunction (A := Interface.source Bool 2) (fun _ _ => b)).1
      [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)] = 0 := by
    by_contra hne
    -- Both replies would have to equal the same retained bit.
    have answers := TypedSystem.ofFunction_answers
      (A := Interface.source Bool 2) (fun _ _ => b) _ hne
    have hfalse : false = b := sigma_mk_injective
      (answers _ (List.mem_cons_self ..))
    have htrue : true = b := sigma_mk_injective
      (answers _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    exact Bool.noConfusion (hfalse.trans htrue.symm)
  rw [hzero, mul_zero]

/-- Conditional fresh draws can disagree: a specified pair of fair replies has mass `1/4`. -/
example :
    (TypedSystem.keyed (ProbDist.single ()) (fun _ _ _ => 𝒰[Bool]) :
      TypedSystem (Interface.source Bool 2)).1
        [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), true⟩)] = 1 / 4 := by
  rw [TypedSystem.keyed_mass]
  simp only [ProbDist.single, Finsupp.support_single () (by norm_num : (1 : ℝ) ≠ 0),
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul, TypedSystem.ofMemoryless_val]
  change RandomSystem.memoryless (Interface.source Bool 2).inputDomain
    (RandomSystem.portLaw fun _ _ => 𝒰[Bool])
    ([(⟨(), ()⟩, ⟨(), false⟩)] ++ [(⟨(), ()⟩, ⟨(), true⟩)]) = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, Interface.source,
    Interface.queryBudget, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.length_cons, List.length_nil, List.cons_ne_nil, not_false_eq_true,
    and_self, ite_true, RandomSystem.portLaw_apply_mk, ProbDist.uniform,
    uniform_apply, Fintype.card_bool]
  change RandomSystem.memoryless (Interface.source Bool 2).inputDomain
    (RandomSystem.portLaw fun _ _ => 𝒰[Bool])
    ([] ++ [(⟨(), ()⟩, ⟨(), false⟩)]) * _ = _
  rw [RandomSystem.memoryless_snoc]
  norm_num only [Interface.inputDomain, Domain.ofInputs, Interface.source,
    Interface.queryBudget, List.map_nil, List.nil_append, List.length_cons, List.length_nil,
    List.cons_ne_nil, not_false_eq_true, and_self, ite_true,
    RandomSystem.portLaw_apply_mk, ProbDist.uniform, uniform_apply, Fintype.card_bool,
    RandomSystem.mass_nil]
  change (if _ then (1 : ℝ) * (1 / (Fintype.card Bool : ℝ)) else 0) *
    (1 / (Fintype.card Bool : ℝ)) = 1 / 4
  norm_num

/-- Two allowed reads of the retained fair bit both give `false` with mass `1/2`. -/
example :
    (TypedSystem.keyed 𝒰[Bool] (fun b _ _ => ProbDist.single b) :
      TypedSystem (Interface.source Bool 2)).1
        [(⟨(), ()⟩, ⟨(), false⟩), (⟨(), ()⟩, ⟨(), false⟩)] = 1 / 2 := by
  rw [TypedSystem.keyed_single, TypedSystem.sample_mass]
  have hs : (𝒰[Bool]).1.support = Finset.univ := by
    ext b
    simp [Finsupp.mem_support_iff, ProbDist.uniform, uniform_apply]
  rw [hs]
  simp [ProbDist.uniform, uniform_apply, TypedSystem.ofFunction_mass,
    Interface.source, Interface.queryBudget]

#print axioms TypedSystem.keyed_snoc
#print axioms TypedSystem.keyed_single

end

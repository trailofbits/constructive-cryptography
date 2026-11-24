module

public import Commons.Definitions.Hash
public import ConstructiveCryptography.CryptographicAlgebra.DistinguisherAction
public import RandomSystems.Typed.KeyedAutomaton
public import RandomSystems.Typed.ProbProgramAttachment
public import RandomSystems.Typed.QueryRouting

/-!
# Retained-key presentation and one-query collision lifting

`Hash.Real.eq_sample` identifies the DSL system `Hash.Real H` with one uniform key `k ←$ 𝒰[K]`
retained for the whole interaction and the deterministic replies `Hash.reply H k`: `key()`
returns `k` and `collide(m₀, m₁)` returns whether `H(k, m₀) = H(k, m₁)`.
`Hash.Ideal.eq_sample` gives the ideal system the replies of the identity hash.

The DSL program draws the key on its first query; `Hash.Real.body_probCombine` gives the
optional-key transition contract, and `TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key`
moves the draw to initialization, as in `Commons.Definitions.MAC.Keyed`.

`Hash.extractConverter extract` is a stateless one-query router (`TypedConverter.routing`)
forwarding `key()` and mapping `collide p` to `collide (extract p)`. Scope: `extract : M' × M' →
M × M` is a key-independent pair extractor, covering unkeyed hashes (`K = Unit`) and
key-independent domain extensions rather than key-dependent or multi-query extraction. On the
retained-key presentation it transports both systems (`Hash.extractConverter_smul_real`,
`Hash.extractConverter_smul_ideal`), lifting collision resistance (`Hash.CR.of_extractor`) and
exact distinguisher advantage (`Hash.CR.advantage_eq_of_extractor`).

```text
               ┌──────────────────────────────┐            ┌───────────────┐
  key()    ──► │ forward key()                │ ─ key() ─► │ k ←$ 𝒰[K]     │
  collide p──► │ forward collide(extract p)   │ ─ ...   ─► │ Hash.reply H k│
               └──────────────────────────────┘            └───────────────┘
```

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace Commons

open ConstructiveCryptography ConstructiveCryptography.CryptographicAlgebra
open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra SystemAlgebra.DSL

noncomputable section

-- `K` carries keys and `M` messages; replies of `collide` are Booleans.
variable {K M T : Type} [Fintype K] [Nonempty K] [Fintype M]

/-- Deterministic collision-system replies at key `k`: `key()` returns `k`, and
`collide(m₀, m₁)` returns `decide (H k m₀ = H k m₁)` [1, Attack Game 8.1, p. 290]. -/
def Hash.reply (H : K → M → T) [DecidableEq T] (k : K) :
    -- Budget `0` names the port alphabets, which are shared by every query budget.
    ∀ i, (KeyedCollision K M 0).X i → (KeyedCollision K M 0).Y i
  | .key => fun _ => k
  | .collide => fun p => decide (H k p.1 = H k p.2)

omit [Nonempty K] in
/-- A single fresh source is a one-state fresh probabilistic automaton. -/
lemma Hash.source_eq_ofProbAutomaton (P : ProbDist K) (n : ℕ) :
    TypedSystem.source P n =
      TypedSystem.ofProbAutomaton (Interface.source K n) (ProbStep.fresh fun _ _ => P)
        (ProbDist.single ()) := by
  rw [TypedSystem.source_eq_ofMemoryless]
  exact Subtype.ext (RandomSystem.ofProbAutomaton_eq_memoryless
    (Interface.source K n).inputDomain (ProbStep.memoryless_fresh (fun _ _ => P))
    (ProbDist.single ())).symm

/-- The DSL body draws a missing key once, then keeps it and replies by `Hash.reply H k`. -/
lemma Hash.Real.body_probCombine
    (H : K → M → T) [DecidableEq T] (keys : Option K)
    (i : KeyedCollision.Port) (x : (KeyedCollision K M 0).X i) :
    (Hash.Real.body H).probCombine (ProbStep.fresh fun _ _ => Hash.Real.law1 H)
      (Hash.Real.bound_spec H) (keys, ()) i x =
    match keys with
    | none => (ProbDist.uniform K).bind fun k =>
        (ProbDist.single (Hash.reply H k i x)).map (fun y => ((some k, ()), y))
    | some k => (ProbDist.single (Hash.reply H k i x)).map (fun y => ((some k, ()), y)) := by
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, Hash.Real.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, ProbDist.map_val,
      fTransform_fTransform, Function.comp_def, ProbStep.tagged,
      List.nil_append, ↓reduceDIte, Hash.reply, ProbDist.bind_val,
      ProbDist.single, fTransform_single, bindK_single_comp] <;> rfl

/-- **Retained-key presentation**: `Hash.Real H` samples one `k ←$ 𝒰[K]` and answers every
query by `Hash.reply H k`. -/
theorem Hash.Real.eq_sample (H : K → M → T) [DecidableEq T] (q : ℕ) :
    Hash.Real (budget := q) H =
      (sample k ←$ 𝒰[K];
        TypedSystem.ofFunction (A := KeyedCollision K M q) (Hash.reply H k)) := by
  rw [Hash.Real, Hash.Real.program, Hash.Real.randomness, Hash.source_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  have hi : (ProbDist.single ()).map (fun r => ((none : Option K), r)) =
      ProbDist.single (none, ()) := Subtype.ext (fTransform_single _ _ _)
  rw [hi]
  exact (TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
    (A := KeyedCollision K M q) (ProbDist.uniform K)
    (fun k i x => ProbDist.single (Hash.reply H k i x)) _ (by
      intro keys i x
      cases keys <;> exact Hash.Real.body_probCombine H _ i x)).trans
    (TypedSystem.keyed_single _ _)

/-- The ideal DSL body draws a missing key once, then keeps it and replies by the identity
hash's `Hash.reply`. -/
lemma Hash.Ideal.body_probCombine [DecidableEq M] (keys : Option K)
    (i : KeyedCollision.Port) (x : (KeyedCollision K M 0).X i) :
    (Hash.Ideal.body K M).probCombine (ProbStep.fresh fun _ _ => Hash.Ideal.law1 K M)
      (Hash.Ideal.bound_spec K M) (keys, ()) i x =
    match keys with
    | none => (ProbDist.uniform K).bind fun k =>
        (ProbDist.single (Hash.reply (fun (_ : K) (m : M) => m) k i x)).map
          (fun y => ((some k, ()), y))
    | some k => (ProbDist.single (Hash.reply (fun (_ : K) (m : M) => m) k i x)).map
        (fun y => ((some k, ()), y)) := by
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, Hash.Ideal.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, ProbDist.map_val,
      fTransform_fTransform, Function.comp_def, ProbStep.tagged,
      List.nil_append, ↓reduceDIte, Hash.reply, ProbDist.bind_val,
      ProbDist.single, fTransform_single, bindK_single_comp] <;> rfl

/-- **Retained-key presentation of `Hash.Ideal`**: one `k ←$ 𝒰[K]` with identity-hash replies. -/
theorem Hash.Ideal.eq_sample [DecidableEq M] (q : ℕ) :
    Hash.Ideal K M (budget := q) =
      (sample k ←$ 𝒰[K];
        TypedSystem.ofFunction (A := KeyedCollision K M q)
          (Hash.reply (fun (_ : K) (m : M) => m) k)) := by
  rw [Hash.Ideal, Hash.Ideal.program, Hash.Ideal.randomness, Hash.source_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  have hi : (ProbDist.single ()).map (fun r => ((none : Option K), r)) =
      ProbDist.single (none, ()) := Subtype.ext (fTransform_single _ _ _)
  rw [hi]
  exact (TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
    (A := KeyedCollision K M q) (ProbDist.uniform K)
    (fun k i x => ProbDist.single (Hash.reply (fun (_ : K) (m : M) => m) k i x)) _ (by
      intro keys i x
      cases keys <;> exact Hash.Ideal.body_probCombine _ i x)).trans
    (TypedSystem.keyed_single _ _)

/-! ### Key-independent one-query extraction converter -/

-- `M'` carries the outer messages whose candidate pairs are translated to pairs in `M`.
variable {M' : Type} [Fintype M']

/-- Forward `key()` and map `collide p` to `collide (extract p)`. -/
def Hash.extractRequest (extract : M' × M' → M × M) {q : ℕ} :
    (Σ o, (KeyedCollision K M' q).X o) → Σ j, (KeyedCollision K M q).X j
  | ⟨.key, u⟩ => ⟨.key, u⟩
  | ⟨.collide, p⟩ => ⟨.collide, extract p⟩

/-- Return the inside reply at the forwarded port unchanged (off-port branches are unreachable). -/
def Hash.extractAnswer {q : ℕ} :
    (u : Σ o, (KeyedCollision K M' q).X o) → (Σ j, (KeyedCollision K M q).Y j) →
      (KeyedCollision K M' q).Y u.1
  | ⟨.key, _⟩, ⟨.key, k⟩ => k
  | ⟨.key, _⟩, ⟨.collide, _⟩ => Classical.arbitrary K
  | ⟨.collide, _⟩, ⟨.collide, b⟩ => b
  | ⟨.collide, _⟩, ⟨.key, _⟩ => false

omit [Nonempty K] in
/-- Mapping each outside query to one inside query preserves the query-budget domain. -/
lemma Hash.extractRequest_domain (extract : M' × M' → M × M) {q : ℕ}
    (us : List (Σ o, (KeyedCollision K M' q).X o)) (hus : (KeyedCollision K M' q).domain us) :
    (KeyedCollision K M q).domain (us.map (Hash.extractRequest extract)) :=
  ⟨fun he => hus.1 (List.map_eq_nil_iff.mp he), (List.length_map _).trans_le hus.2⟩

/-- **Key-independent one-query extraction converter** (stateless router; covers unkeyed hashes
and key-independent domain extensions). -/
def Hash.extractConverter (extract : M' × M' → M × M) (q : ℕ) :
    KeyedCollision K M' q ⟶ KeyedCollision K M q :=
  TypedConverter.routing (Hash.extractRequest extract) Hash.extractAnswer
    (Hash.extractRequest_domain extract)

/-- Transport of fixed-key collision replies through `Hash.extractConverter`. -/
lemma Hash.extractConverter_smul_ofFunction {T' : Type} [DecidableEq T] [DecidableEq T']
    (H : K → M → T) (G : K → M' → T') (extract : M' × M' → M × M) (q : ℕ) (k : K)
    (hreal : ∀ p, H k (extract p).1 = H k (extract p).2 ↔ G k p.1 = G k p.2) :
    Hash.extractConverter extract q • TypedSystem.ofFunction (A := KeyedCollision K M q)
        (Hash.reply H k) =
      TypedSystem.ofFunction (A := KeyedCollision K M' q) (Hash.reply G k) := by
  rw [Hash.extractConverter, TypedConverter.routing_smul_ofFunction]
  congr 1
  funext o u
  cases o
  · rfl
  · exact decide_eq_decide.mpr (hreal u)

/-- **Real-system transport**: `Hash.extractConverter extract q • Hash.Real H = Hash.Real G`. -/
theorem Hash.extractConverter_smul_real {T' : Type} [DecidableEq T] [DecidableEq T']
    (H : K → M → T) (G : K → M' → T') (extract : M' × M' → M × M) (q : ℕ)
    (hreal : ∀ k p, H k (extract p).1 = H k (extract p).2 ↔ G k p.1 = G k p.2) :
    Hash.extractConverter extract q • Hash.Real (budget := q) H =
      Hash.Real (budget := q) G := by
  rw [Hash.Real.eq_sample, Hash.Real.eq_sample, TypedConverter.smul_sample]
  congr 1
  funext k
  exact Hash.extractConverter_smul_ofFunction H G extract q k (hreal k)

/-- **Ideal-system transport**:
`Hash.extractConverter extract q • Hash.Ideal K M = Hash.Ideal K M'`. -/
theorem Hash.extractConverter_smul_ideal [DecidableEq M] [DecidableEq M']
    (extract : M' × M' → M × M) (q : ℕ)
    (hideal : ∀ p, (extract p).1 = (extract p).2 ↔ p.1 = p.2) :
    Hash.extractConverter extract q • Hash.Ideal K M (budget := q) =
      Hash.Ideal K M' (budget := q) := by
  rw [Hash.Ideal.eq_sample, Hash.Ideal.eq_sample, TypedConverter.smul_sample]
  congr 1
  funext k
  exact Hash.extractConverter_smul_ofFunction _ _ extract q k hideal

/-! ### Collision lifting through the extraction converter -/

/-- **One-query collision lifting**: a key-independent collision/equality-preserving extractor
lifts `Hash.CR H error` to `Hash.CR G (d ↦ error (dα))`. -/
theorem Hash.CR.of_extractor {T' : Type} [DecidableEq M] [DecidableEq M']
    [DecidableEq T] [DecidableEq T'] [AdmissibleDistinguishers Interface TypedDistinguisher]
    {q : ℕ}
    (H : K → M → T) (G : K → M' → T') (extract : M' × M' → M × M)
    (hreal : ∀ k p, H k (extract p).1 = H k (extract p).2 ↔ G k p.1 = G k p.2)
    (hideal : ∀ p, (extract p).1 = (extract p).2 ↔ p.1 = p.2)
    (closed : AdmissibleDistinguishers.ClosedUnder (Phi := TypedSystem)
      (D := TypedDistinguisher) (Hash.extractConverter (K := K) extract q))
    {error : TypedDistinguisher (KeyedCollision K M q) → ENNReal} (h : Hash.CR H error) :
    Hash.CR G (fun d => error (TypedDistinguisher.absorb d (Hash.extractConverter extract q))) :=
  AdmissibleDistinguishers.substitutesWithin_context (Hash.extractConverter extract q) closed h
    (Hash.extractConverter_smul_real H G extract q hreal)
    (Hash.extractConverter_smul_ideal extract q hideal)

/-- **Lossless advantage transport** for every outer collision distinguisher `d`. -/
theorem Hash.CR.advantage_eq_of_extractor {T' : Type} [DecidableEq M] [DecidableEq M']
    [DecidableEq T] [DecidableEq T'] {q : ℕ}
    (H : K → M → T) (G : K → M' → T') (extract : M' × M' → M × M)
    (hreal : ∀ k p, H k (extract p).1 = H k (extract p).2 ↔ G k p.1 = G k p.2)
    (hideal : ∀ p, (extract p).1 = (extract p).2 ↔ p.1 = p.2)
    (d : TypedDistinguisher (KeyedCollision K M' q)) :
    d.advantage (Hash.Real (budget := q) G) (Hash.Ideal K M' (budget := q)) =
      (TypedDistinguisher.absorb d (Hash.extractConverter extract q)).advantage
        (Hash.Real (budget := q) H) (Hash.Ideal K M (budget := q)) := by
  rw [← Hash.extractConverter_smul_real H G extract q hreal,
    ← Hash.extractConverter_smul_ideal (K := K) extract q hideal]
  rfl

end

end Commons

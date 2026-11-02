module

public import Commons.Definitions.PublicKeyEncryption
public import RandomSystems.Typed.KeyedAutomaton
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Retained-key presentation of public-key encryption

`PKE.system.perPort_eq_keyed` identifies the existing program attached to its sources with
one key pair sampled from `scheme.gen` and fresh replies from `PKE.system.replyLaw`.
Public-key reads and decryption use that pair; repeated encryption calls draw independently
conditional on it.
The operations follow [1, Definition 11.1, p. 436]: “E is a probabilistic algorithm” and
“D is a deterministic algorithm”. The retained pair is that of the existing PKE system.

`PublicKeyEncryption.encryptions_map` gives the encryption table's coordinate marginal.
`PKE.system.body_probCombine` uses it for one invocation, including the initial key draw.
The full equality attaches the existing independent sources and simulates the optional key
state by `scheme.gen` before initialization and the point law at the stored pair afterwards.
`TypedSystem.ofProbAutomaton_eq_keyed`, in `RandomSystems.Typed.KeyedAutomaton`, then removes
this state representation without changing the interface's domain.

```text
  publicKey(), enc(m), dec(c) ──► [retain (pk, sk) ∼ scheme.gen]
                                      │
                         pk, fresh c ∼ scheme.enc pk m, scheme.dec sk c
```

`PKE.INDCCA.systems_eq_keyed` rewrites both systems through the same correspondence and keeps
`PKE.CCA` as the converter of the transformed system. It retains the random-message
substitution of [2, Definition 2.3.5, p. 20], whose fake decryption oracle
“returns the originally input message” on replay.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
2. F. Banfi. *A Composable Treatment of Anonymous Communication*. Doctoral thesis,
   Diss. ETH No. 29663, ETH Zurich, 2023.
-/

@[expose] public section

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra

namespace Commons

noncomputable section

-- `PK`, `SK` carry keys; `M`, `C` carry messages and ciphertexts.
variable {PK SK M C : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype C]
  [DecidableEq PK] [DecidableEq M]

omit [Fintype SK] [Fintype C] in
/-- Selecting the entry `(pk, m)` of an independent encryption table gives `scheme.enc pk m`. -/
lemma PublicKeyEncryption.encryptions_map
    -- `scheme` supplies the encryption laws; `pk`, `m` select the requested ciphertext.
    (scheme : PublicKeyEncryption PK SK M C) (pk : PK) (m : M) :
    scheme.encryptions.map (fun f => f (pk, m)) = scheme.enc pk m := by
  -- Every other coordinate has weight one in the existing product-marginal law.
  apply Subtype.ext
  change marginalAt (Distribution.pi (fun pm : PK × M => (scheme.enc pm.1 pm.2).1)) (pk, m) = _
  rw [marginalAt_pi]
  simp only [IsProbability.weight_eq_one, Finset.prod_const_one, one_smul]

/-- At retained `keys = (pk, sk)`, publish `pk`, encrypt freshly under `pk`, and decrypt under `sk`.
The reply law uses the existing public-key, encryption and decryption ports. -/
def PKE.system.replyLaw
    -- `scheme` supplies the algorithms; `keys` is the one pair shared by all three ports.
    (scheme : PublicKeyEncryption PK SK M C) (keys : PK × SK) :
    -- `i` selects public-key publication, encryption or decryption, with its typed query.
    ∀ i, (PKE PK M C 0).X i → ProbDist ((PKE PK M C 0).Y i)
  | .publicKey, _ => ProbDist.single keys.1
  | .enc, m => scheme.enc keys.1 m
  | .dec, c => ProbDist.single (scheme.dec keys.2 c)

/-- The existing source ports draw key pairs on the left and encryption tables on the right. -/
def PKE.system.randomnessLaw
    -- `scheme.gen` and `scheme.encryptions` supply the two independent source laws.
    (scheme : PublicKeyEncryption PK SK M C) :
    -- `j = inl ()` selects the key law; `j = inr ()` selects the table law, on unit triggers.
    ∀ j : Unit ⊕ Unit,
      Sum.rec (motive := fun _ => Type) (fun _ : Unit => Unit) (fun _ : Unit => Unit) j →
      ProbDist (Sum.rec (motive := fun _ => Type)
        (fun _ : Unit => PK × SK) (fun _ : Unit => PK × M → C) j) :=
  RandomSystem.parallelLaw (fun _ _ => scheme.gen) (fun _ _ => scheme.encryptions)

/-- One invocation draws the key only if absent, then keeps it while sampling its reply law. -/
lemma PKE.system.body_probCombine
    -- `scheme` supplies the source laws; `keys = none` marks the first invocation.
    (scheme : PublicKeyEncryption PK SK M C) (keys : Option (PK × SK))
    -- `i(x)` is the current query at any of the three PKE ports.
    (i : PKE.Port) (x : (PKE PK M C 0).X i) :
    (PKE.system.body scheme).probCombine (ProbStep.fresh (PKE.system.randomnessLaw scheme))
      (PKE.system.bound_spec scheme) (keys, ()) i x =
    match keys with
    | none => scheme.gen.bind fun k => (PKE.system.replyLaw scheme k i x).map
        (fun y => ((some k, ()), y))
    | some k => (PKE.system.replyLaw scheme k i x).map (fun y => ((some k, ()), y)) := by
  -- Evaluating the freshly sampled table contributes only its requested ciphertext marginal.
  have henc (k : PK × SK) (m : M) :
      bindK scheme.encryptions.1 (fun table =>
        Finsupp.single ((some k, ()), table (k.1, m)) 1) =
      fTransform (fun y => ((some k, ()), y)) (scheme.enc k.1 m).1 := by
    rw [bindK_single_comp]
    exact congrArg Subtype.val ((ProbDist.map_map (fun y => ((some k, ()), y))
      (fun table => table (k.1, m)) scheme.encryptions).symm.trans
      (congrArg (ProbDist.map (fun y => ((some k, ()), y))) (scheme.encryptions_map k.1 m)))
  -- The six cases are the three query types, before and after the first key draw.
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, PKE.system.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, PKE.system.randomnessLaw,
      RandomSystem.parallelLaw, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, ProbStep.tagged, List.nil_append, List.cons_append,
      ↓reduceDIte, PKE.system.replyLaw, ProbDist.bind_val, ProbDist.single, fTransform_single,
      henc]

/-- The two independent source components give fresh transitions with their parallel law. -/
lemma PKE.system.randomness_eq_ofProbAutomaton
    -- `scheme` selects the laws; `q` is the existing source allowance at each component.
    (scheme : PublicKeyEncryption PK SK M C) (q : ℕ) :
    PKE.system.randomness scheme q = TypedSystem.ofProbAutomaton _
      (ProbStep.fresh (PKE.system.randomnessLaw scheme)) (ProbDist.single ()) := by
  rw [PKE.system.randomness, TypedSystem.source_eq_ofMemoryless,
    TypedSystem.source_eq_ofMemoryless, TypedSystem.parallel_ofMemoryless]
  exact Subtype.ext (RandomSystem.ofProbAutomaton_eq_memoryless _
    (ProbStep.memoryless_fresh _) _).symm

/-- The PKE system retains one generated pair and draws each encryption reply freshly.
Equality of cumulative probabilities covers all admitted adaptive and repeated queries. -/
theorem PKE.system.perPort_eq_keyed
    -- `scheme` gives the key law and algorithms; `q` bounds calls separately at each PKE port.
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ) :
    PKE.system.perPort (budget := q) scheme =
      TypedSystem.keyed (A := PKE.perPort PK M C q) scheme.gen (PKE.system.replyLaw scheme) := by
  -- Attach the source automaton through the bounded program with its existing domain proof.
  rw [PKE.system.perPort, PKE.system.randomness_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  let transition : ProbStep (PK × SK) PKE.Port (PKE PK M C 0).X (PKE PK M C 0).Y :=
    fun k i x => (PKE.system.replyLaw scheme k i x).map fun y => (k, y)
  -- Before initialization, represent the missing key by its law; afterwards keep its value.
  let K : Option (PK × SK) × Unit → ProbDist (PK × SK)
    | (none, _) => scheme.gen
    | (some k, _) => ProbDist.single k
  -- Every invocation ends with a stored pair, so the kernel commutes with every transition.
  have hsim := TypedSystem.ofProbAutomaton_eq_of_simulation
    (A := PKE.perPort PK M C q)
    ((PKE.system.body scheme).probCombine (ProbStep.fresh (PKE.system.randomnessLaw scheme))
      (PKE.system.bound_spec scheme)) transition K (fun _ _ => True)
    (by intros; trivial)
    (by
      intro xs s x _ _
      rcases s with ⟨keys, ⟨⟩⟩
      unfold ProbStep.SimulatesAt ProbStep.outcome
      rw [PKE.system.body_probCombine scheme keys x.1 x.2]
      cases keys <;>
        simp only [K, transition, ProbDist.bind_val, ProbDist.map_val, ProbDist.single,
          bindK_single, one_smul, fTransform_bindK, bindK_bindK, fTransform_fTransform,
          bindK_fTransform, Function.comp_def, ProbStep.tagged, fTransform_single,
          bindK_single_comp])
    ((ProbDist.single ()).map (fun r => (none, r))) (by intros; trivial)
  -- The initial optional state represents exactly `scheme.gen`, including the empty transcript.
  have hi : (((ProbDist.single ()).map (fun r => (none, r))).bind K) = scheme.gen := by
    apply Subtype.ext
    simp only [ProbDist.bind_val, ProbDist.map_val, ProbDist.single, fTransform_single,
      bindK_single, one_smul, K]
  rw [hi] at hsim
  -- A fixed-state automaton is the existing retained-key system.
  exact hsim.trans (TypedSystem.ofProbAutomaton_eq_keyed scheme.gen _)

/-- Both IND-CCA systems use the same retained-key presentation; the transformation is `PKE.CCA`. -/
lemma PKE.INDCCA.systems_eq_keyed
    -- Replay lookup compares ciphertexts; the uniform replacement message needs a nonempty `M`.
    [DecidableEq C] [Nonempty M]
    -- `scheme` selects the primitive; `q` gives the common per-port domain of both systems.
    (scheme : PublicKeyEncryption PK SK M C) (q : PKE.Port → ℕ) :
    PKE.INDCCA.systems scheme q =
      (TypedSystem.keyed (A := PKE.perPort PK M C q) scheme.gen (PKE.system.replyLaw scheme),
        PKE.CCA.perPort PK M C •
          TypedSystem.keyed (A := PKE.perPort PK M C q) scheme.gen
            (PKE.system.replyLaw scheme)) := by
  rw [PKE.INDCCA.systems, PKE.system.perPort_eq_keyed]

end
end Commons

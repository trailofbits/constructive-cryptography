module

public import Commons.Definitions.Signature
public import RandomSystems.Typed.KeyedAutomaton
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Retained-key presentation of signatures

`SignatureScheme.system.eq_keyed` identifies the attached source program with one retained
pair `(pk, sk) ∼ scheme.gen` and fresh replies from `SignatureScheme.system.replyLaw`.
The public-key and verification ports use `pk`; every signing call draws its reply under `sk`.
This realizes “S is a probabilistic algorithm” [1, Definition 13.1, p. 528] and
“V is a deterministic algorithm” [1, Definition 13.1, p. 529].

`SignatureScheme.system.randomness_eq_ofProbAutomaton` presents the two sources as a fresh
automaton. `SignatureScheme.system.body_probCombine` selects the current signing-table
coordinate using `ProbDist.map_pi_apply_comp`. The program attachment law in
`RandomSystems.Typed.ProbProgramAttachment` and the optional-key simulation in
`RandomSystems.Typed.KeyedAutomaton` turn these transition equations into cumulative equality
with the retained-pair system, on its declared query domain.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra

noncomputable section

-- `PK`, `SK` carry verification and signing keys, `M` messages, and `Sig` signatures.
-- The DSL alphabets are finite; decidable equality indexes the `SK × M` signing table.
variable {PK SK M Sig : Type} [Fintype PK] [Fintype SK] [Fintype M] [Fintype Sig]
  [DecidableEq SK] [DecidableEq M]

/-- At `keys = (pk, sk)`, publish `pk`, sign `m` with law `scheme.sign sk m`, and
verify `(m, σ)` with the point law at `scheme.verify pk m σ`. -/
def SignatureScheme.system.replyLaw
    -- `scheme` supplies the operations; `keys` is shared by all three ports.
    (scheme : SignatureScheme PK SK M Sig) (keys : PK × SK) :
    -- Budget `0` names the port alphabets, which are shared by every query budget.
    ∀ i, (Signing PK M Sig 0).X i → ProbDist ((Signing PK M Sig 0).Y i)
  | .publicKey, () => ProbDist.single keys.1
  | .sign, m => scheme.sign keys.2 m
  | .verify, ms => ProbDist.single (scheme.verify keys.1 ms.1 ms.2)

/-- `randomnessLaw (inl ()) () = scheme.gen`;
`randomnessLaw (inr ()) () = scheme.signatures`. -/
def SignatureScheme.system.randomnessLaw
    -- `scheme` supplies the normalized key and table laws.
    (scheme : SignatureScheme PK SK M Sig) :
    -- `j` selects a unit-triggered source; budget `0` names its budget-independent alphabets.
    ∀ j, ((Interface.source (PK × SK) 0).tensor (Interface.source (SK × M → Sig) 0)).X j →
      ProbDist (((Interface.source (PK × SK) 0).tensor (Interface.source (SK × M → Sig) 0)).Y j) :=
  RandomSystem.parallelLaw (fun _ _ => scheme.gen) (fun _ _ => scheme.signatures)

/-- Draw a missing key pair once, then keep it while drawing the current reply from its law. -/
lemma SignatureScheme.system.body_probCombine
    -- `scheme` supplies the source laws; `keys = none` means no key pair has been drawn.
    (scheme : SignatureScheme PK SK M Sig) (keys : Option (PK × SK))
    -- `i(x)` is the current typed query at one of the three ports.
    (i : Signing.Port) (x : (Signing PK M Sig 0).X i) :
    (SignatureScheme.system.body scheme).probCombine
      (ProbStep.fresh (SignatureScheme.system.randomnessLaw scheme))
      (SignatureScheme.system.bound_spec scheme) (keys, ()) i x =
    match keys with
    | none => scheme.gen.bind fun k => (SignatureScheme.system.replyLaw scheme k i x).map
        (fun y => ((some k, ()), y))
    | some k => (SignatureScheme.system.replyLaw scheme k i x).map
        (fun y => ((some k, ()), y)) := by
  -- The requested table coordinate has exactly its normalized signing law.
  have hreply (k : PK × SK) (m : M) :
      bindK scheme.signatures.1 (fun f => Finsupp.single ((some k, ()), f (k.2, m)) 1) =
      fTransform (fun y => ((some k, ()), y)) (scheme.sign k.2 m).1 := by
    rw [bindK_single_comp]
    exact congrArg Subtype.val (ProbDist.map_pi_apply_comp
      (fun km : SK × M => scheme.sign km.1 km.2) (k.2, m) (fun y => ((some k, ()), y)))
  -- Each port either initializes the key or reuses it, then follows its reply law.
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, SignatureScheme.system.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, SignatureScheme.system.randomnessLaw,
      RandomSystem.parallelLaw, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, ProbStep.tagged, List.nil_append, List.cons_append,
      ↓reduceDIte, SignatureScheme.system.replyLaw, ProbDist.bind_val, ProbDist.single,
      fTransform_single, hreply]

/-- The two source components are fresh transitions with their parallel reply law. -/
lemma SignatureScheme.system.randomness_eq_ofProbAutomaton
    -- `scheme` selects the laws; `q` is the source allowance at each component.
    (scheme : SignatureScheme PK SK M Sig) (q : ℕ) :
    SignatureScheme.system.randomness scheme q = TypedSystem.ofProbAutomaton
      ((Interface.source (PK × SK) q).tensor (Interface.source (SK × M → Sig) q))
      (ProbStep.fresh (SignatureScheme.system.randomnessLaw scheme)) (ProbDist.single ()) :=
  TypedSystem.parallel_source_eq_ofProbAutomaton scheme.gen scheme.signatures q q

/-- On `Signing PK M Sig q`, `system scheme = keyed scheme.gen (replyLaw scheme)`:
retain one key pair and draw each query's reply from its law at that pair. -/
theorem SignatureScheme.system.eq_keyed
    -- `scheme` gives the key law and operations; `q` is the total query budget.
    (scheme : SignatureScheme PK SK M Sig) (q : ℕ) :
    SignatureScheme.system (budget := q) scheme =
      TypedSystem.keyed (A := Signing PK M Sig q) scheme.gen
        (SignatureScheme.system.replyLaw scheme) := by
  -- Attach the fresh source automaton through the program's bounded-domain contract.
  rw [SignatureScheme.system, SignatureScheme.system.program,
    SignatureScheme.system.randomness_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  -- The program's initial `none` pairs with the source's unit state.
  have hi : (ProbDist.single ()).map (fun r => ((none : Option (PK × SK)), r)) =
      ProbDist.single (none, ()) := Subtype.ext (fTransform_single _ _ _)
  rw [hi]
  -- The optional key's local transition law moves its single draw to initialization.
  exact TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
    (A := Signing PK M Sig q) scheme.gen (SignatureScheme.system.replyLaw scheme) _ (by
      intro keys i x
      cases keys <;> exact SignatureScheme.system.body_probCombine scheme _ i x)

end

end Commons

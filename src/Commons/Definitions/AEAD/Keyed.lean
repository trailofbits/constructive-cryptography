module

public import Commons.Definitions.AEAD
public import RandomSystems.Typed.KeyedAutomaton
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Retained-key presentation of symmetric encryption

`AE.system.eq_keyed` identifies the attached source program with one key from `scheme.gen`
and fresh replies from `AE.system.replyLaw`. The two ports share this key throughout the
interaction. In the source program, each `enc` call draws a fresh `scheme.encryptions` table.
`scheme.enc` models `E`, whose “encryption function E” may “be a probabilistic algorithm”;
`scheme.dec` models `D`, using “deterministic decryption algorithms” [1, §2.2.1, p. 14].

`AE.system.randomness_eq_ofProbAutomaton` presents both sources as one fresh automaton;
`TypedConverter.ofProgram_smul_ofProbAutomaton` attaches the program to it.
`AE.system.body_probCombine` then selects its table coordinate with
`ProbDist.map_pi_apply_comp`, giving the optional-key transition contract.
`TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key` turns this contract into cumulative
equality with one retained key, on the selected query domain.

## References

1. D. Boneh and V. Shoup. *A Graduate Course in Applied Cryptography*. Version 0.6, 2023.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra

noncomputable section

-- `K` carries retained keys, `M` messages, and `C` ciphertexts.
-- The DSL interfaces require finite alphabets; decidable equality indexes the `K × M` table.
variable {K M C : Type} [Fintype K] [Fintype M] [Fintype C]
  [DecidableEq K] [DecidableEq M]

/-- At `key`, `replyLaw enc m = scheme.enc key m` and
`replyLaw dec c = δ(scheme.dec key c)`. -/
def AE.system.replyLaw
    -- `scheme` supplies the operations; `key` is shared by both ports.
    (scheme : SymmetricEncryption K M C) (key : K) :
    -- Budget `0` names the port alphabets, which are shared by every query budget.
    ∀ i, (AE M C 0).X i → ProbDist ((AE M C 0).Y i)
  | .enc, m => scheme.enc key m
  | .dec, c => ProbDist.single (scheme.dec key c)

/-- `randomnessLaw (inl ()) () = scheme.gen`;
`randomnessLaw (inr ()) () = scheme.encryptions`. -/
def AE.system.randomnessLaw
    -- `scheme` supplies the normalized key and table laws.
    (scheme : SymmetricEncryption K M C) :
    -- `j` selects a unit-triggered source; budget `0` names its budget-independent alphabets.
    ∀ j, ((Interface.source K 0).tensor (Interface.source (K × M → C) 0)).X j →
      ProbDist (((Interface.source K 0).tensor (Interface.source (K × M → C) 0)).Y j) :=
  RandomSystem.parallelLaw (fun _ _ => scheme.gen) (fun _ _ => scheme.encryptions)

/-- Draw a missing key once, then keep it while drawing the current reply from its law. -/
lemma AE.system.body_probCombine
    -- `scheme` supplies the source laws; `keys = none` means no key has been drawn.
    (scheme : SymmetricEncryption K M C) (keys : Option K)
    -- `i(x)` is the current typed query at either port.
    (i : AE.Port) (x : (AE M C 0).X i) :
    (AE.system.body scheme).probCombine (ProbStep.fresh (AE.system.randomnessLaw scheme))
      (AE.system.bound_spec scheme) (keys, ()) i x =
    match keys with
    | none => scheme.gen.bind fun k => (AE.system.replyLaw scheme k i x).map
        (fun y => ((some k, ()), y))
    | some k => (AE.system.replyLaw scheme k i x).map (fun y => ((some k, ()), y)) := by
  -- The requested table coordinate has exactly its normalized encryption law.
  have hreply (k : K) (m : M) :
      bindK scheme.encryptions.1 (fun f => Finsupp.single ((some k, ()), f (k, m)) 1) =
      fTransform (fun y => ((some k, ()), y)) (scheme.enc k m).1 := by
    rw [bindK_single_comp]
    exact congrArg Subtype.val (ProbDist.map_pi_apply_comp
      (fun km : K × M => scheme.enc km.1 km.2) (k, m) (fun y => ((some k, ()), y)))
  -- Each port either initializes the key or reuses it, then follows its reply law.
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, AE.system.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, AE.system.randomnessLaw,
      RandomSystem.parallelLaw, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, ProbStep.tagged, List.nil_append, List.cons_append,
      ↓reduceDIte, AE.system.replyLaw, ProbDist.bind_val, ProbDist.single, fTransform_single,
      hreply]

/-- The two source components are fresh transitions with their parallel reply law. -/
lemma AE.system.randomness_eq_ofProbAutomaton
    -- `scheme` selects the laws; `q` is the source allowance at each component.
    (scheme : SymmetricEncryption K M C) (q : ℕ) :
    AE.system.randomness scheme q = TypedSystem.ofProbAutomaton
      ((Interface.source K q).tensor (Interface.source (K × M → C) q))
      (ProbStep.fresh (AE.system.randomnessLaw scheme)) (ProbDist.single ()) :=
  TypedSystem.parallel_source_eq_ofProbAutomaton scheme.gen scheme.encryptions q q

/-- On `AE M C q`, `system scheme = keyed scheme.gen (replyLaw scheme)`:
retain one key and draw each query's reply from its law at that key. -/
theorem AE.system.eq_keyed
    -- `scheme` gives the key law and operations; `q` is the total query budget.
    (scheme : SymmetricEncryption K M C) (q : ℕ) :
    AE.system (budget := q) scheme =
      TypedSystem.keyed (A := AE M C q) scheme.gen (AE.system.replyLaw scheme) := by
  -- Attach the fresh source automaton through the program's bounded-domain contract.
  rw [AE.system, AE.system.program, AE.system.randomness_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  -- The program's initial `none` pairs with the source's unit state.
  have hi : (ProbDist.single ()).map (fun r => ((none : Option K), r)) =
      ProbDist.single (none, ()) := Subtype.ext (fTransform_single _ _ _)
  rw [hi]
  -- The optional key's local transition law moves its single draw to initialization.
  exact TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
    (A := AE M C q) scheme.gen (AE.system.replyLaw scheme) _ (by
      intro keys i x
      cases keys <;> exact AE.system.body_probCombine scheme _ i x)

end

end Commons

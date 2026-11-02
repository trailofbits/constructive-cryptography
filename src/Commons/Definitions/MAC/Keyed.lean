module

public import Commons.Definitions.MAC
public import RandomSystems.Typed.KeyedAutomaton
public import RandomSystems.Typed.ProbProgramAttachment

/-!
# Retained-key presentation of message authentication

`MAC.system.eq_keyed` identifies the attached source program with one key from `mac.gen`
and fresh replies from `MAC.system.replyLaw`. The two ports share this key throughout the
interaction. In the source program, each `tag` call draws a fresh `mac.tags` table.
`mac.tag` models `S` and `mac.verify` models `V`: “S is a probabilistic algorithm” and
“V is a deterministic algorithm” [1, Definition 6.1, p. 217].

`MAC.system.randomness_eq_ofProbAutomaton` presents both sources as one fresh automaton;
`TypedConverter.ofProgram_smul_ofProbAutomaton` attaches the program to it.
`MAC.system.body_probCombine` then selects its table coordinate with
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

-- `K` carries retained keys, `M` messages, and `T` tags.
-- The DSL interfaces require finite alphabets; decidable equality indexes the `K × M` table.
variable {K M T : Type} [Fintype K] [Fintype M] [Fintype T]
  [DecidableEq K] [DecidableEq M]

/-- At `key`, `replyLaw tag m = mac.tag key m` and
`replyLaw verify (m,t) = δ(mac.verify key m t)`. -/
def MAC.system.replyLaw
    -- `mac` supplies the operations; `key` is shared by both ports.
    (mac : MAC K M T) (key : K) :
    -- Budget `0` names the port alphabets, which are shared by every query budget.
    ∀ i, (Tagging M T 0).X i → ProbDist ((Tagging M T 0).Y i)
  | .tag, m => mac.tag key m
  | .verify, mt => ProbDist.single (mac.verify key mt.1 mt.2)

/-- `randomnessLaw (inl ()) () = mac.gen`;
`randomnessLaw (inr ()) () = mac.tags`. -/
def MAC.system.randomnessLaw
    -- `mac` supplies the normalized key and table laws.
    (mac : MAC K M T) :
    -- `j` selects a unit-triggered source; budget `0` names its budget-independent alphabets.
    ∀ j, ((Interface.source K 0).tensor (Interface.source (K × M → T) 0)).X j →
      ProbDist (((Interface.source K 0).tensor (Interface.source (K × M → T) 0)).Y j) :=
  RandomSystem.parallelLaw (fun _ _ => mac.gen) (fun _ _ => mac.tags)

/-- Draw a missing key once, then keep it while drawing the current reply from its law. -/
lemma MAC.system.body_probCombine
    -- `mac` supplies the source laws; `keys = none` means no key has been drawn.
    (mac : MAC K M T) (keys : Option K)
    -- `i(x)` is the current typed query at either port.
    (i : Tagging.Port) (x : (Tagging M T 0).X i) :
    (MAC.system.body mac).probCombine (ProbStep.fresh (MAC.system.randomnessLaw mac))
      (MAC.system.bound_spec mac) (keys, ()) i x =
    match keys with
    | none => mac.gen.bind fun k => (MAC.system.replyLaw mac k i x).map
        (fun y => ((some k, ()), y))
    | some k => (MAC.system.replyLaw mac k i x).map (fun y => ((some k, ()), y)) := by
  -- The requested table coordinate has exactly its normalized tagging law.
  have hreply (k : K) (m : M) :
      bindK mac.tags.1 (fun f => Finsupp.single ((some k, ()), f (k, m)) 1) =
      fTransform (fun y => ((some k, ()), y)) (mac.tag k m).1 := by
    rw [bindK_single_comp]
    exact congrArg Subtype.val (ProbDist.map_pi_apply_comp
      (fun km : K × M => mac.tag km.1 km.2) (k, m) (fun y => ((some k, ()), y)))
  -- Each port either initializes the key or reuses it, then follows its reply law.
  apply Subtype.ext
  cases keys <;> cases i <;>
    simp only [Program.probCombine, Program.probInvoke, MAC.system.body,
      callProg, returnProg, ProbStep.outcome, ProbStep.fresh, MAC.system.randomnessLaw,
      RandomSystem.parallelLaw, ProbDist.map_val, fTransform_fTransform, bindK_fTransform,
      Function.comp_def, ProbStep.tagged, List.nil_append, List.cons_append,
      ↓reduceDIte, MAC.system.replyLaw, ProbDist.bind_val, ProbDist.single, fTransform_single,
      hreply]

/-- The two source components are fresh transitions with their parallel reply law. -/
lemma MAC.system.randomness_eq_ofProbAutomaton
    -- `mac` selects the laws; `q` is the source allowance at each component.
    (mac : MAC K M T) (q : ℕ) :
    MAC.system.randomness mac q = TypedSystem.ofProbAutomaton
      ((Interface.source K q).tensor (Interface.source (K × M → T) q))
      (ProbStep.fresh (MAC.system.randomnessLaw mac)) (ProbDist.single ()) :=
  TypedSystem.parallel_source_eq_ofProbAutomaton mac.gen mac.tags q q

/-- On `Tagging M T q`, `system mac = keyed mac.gen (replyLaw mac)`:
retain one key and draw each query's reply from its law at that key. -/
theorem MAC.system.eq_keyed
    -- `mac` gives the key law and operations; `q` is the total query budget.
    (mac : MAC K M T) (q : ℕ) :
    MAC.system (budget := q) mac =
      TypedSystem.keyed (A := Tagging M T q) mac.gen (MAC.system.replyLaw mac) := by
  -- Attach the fresh source automaton through the program's bounded-domain contract.
  rw [MAC.system, MAC.system.program, MAC.system.randomness_eq_ofProbAutomaton,
    TypedConverter.ofProgram_smul_ofProbAutomaton]
  -- The program's initial `none` pairs with the source's unit state.
  have hi : (ProbDist.single ()).map (fun r => ((none : Option K), r)) =
      ProbDist.single (none, ()) := Subtype.ext (fTransform_single _ _ _)
  rw [hi]
  -- The optional key's local transition law moves its single draw to initialization.
  exact TypedSystem.ofProbAutomaton_eq_keyed_of_optional_key
    (A := Tagging M T q) mac.gen (MAC.system.replyLaw mac) _ (by
      intro keys i x
      cases keys <;> exact MAC.system.body_probCombine mac _ i x)

end

end Commons

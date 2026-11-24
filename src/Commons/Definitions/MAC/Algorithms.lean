module

public import Commons.Definitions.MAC
public import RandomSystems.Typed.Memoryless

/-!
# Memoryless presentation of MAC algorithms

`MAC.algorithms.eq_ofMemoryless` identifies the stateless `MAC.algorithms` system with
`TypedSystem.ofMemoryless (MACAlgorithms K M T q) (MAC.algorithms.replyLaw mac)`. Each
`tag(k, m)` call draws a fresh independent tag from `mac.tag k m`, and each `verify(k, m, t)`
call returns the point mass at `mac.verify k m t`.
-/

@[expose] public section

namespace Commons

open SystemAlgebra SystemAlgebra.DSL Probability Probability.Distribution
open scoped SystemAlgebra

noncomputable section

-- `K` carries keys, `M` messages, and `T` tags; decidable equality indexes the `K × M` table.
variable {K M T : Type} [Fintype K] [Fintype M] [Fintype T]
  [DecidableEq K] [DecidableEq M]

/-- At `tag (k, m)`, reply with `mac.tag k m`; at `verify (k, m, t)`, reply with the point mass
at `mac.verify k m t`. -/
def MAC.algorithms.replyLaw
    -- `mac` supplies the tagging law and deterministic verification predicate.
    (mac : MAC K M T) :
    ∀ i, MACAlgorithms.Input K M T i → ProbDist (MACAlgorithms.Output T i)
  | .tag, (k, m) => mac.tag k m
  | .verify, (k, m, t) => ProbDist.single (mac.verify k m t)

/-- Each invocation of `MAC.algorithms` against fresh tag tables draws from `replyLaw`. -/
lemma MAC.algorithms.memorylessReplyLaw_eq
    -- `mac` supplies the tagging law and verification predicate; `s` is the DSL state.
    (mac : MAC K M T) (s : Option Unit)
    (i : MACAlgorithms.Port) (x : MACAlgorithms.Input K M T i) :
    (MAC.algorithms.body mac).memorylessReplyLaw (fun _ _ => MAC.algorithms.law1 mac) s i x
        1 [] = (MAC.algorithms.replyLaw mac i x).1 := by
  cases s <;> cases i with
  | tag =>
    rcases x with ⟨k, m⟩
    have htag : bindK (MAC.algorithms.law1 mac).1 (fun f => Finsupp.single (f (k, m)) 1) =
        (mac.tag k m).1 := by
      rw [bindK_single_comp]
      exact congrArg Subtype.val
        (ProbDist.map_pi_apply (fun km : K × M => mac.tag km.1 km.2) (k, m))
    simp only [Program.memorylessReplyLaw, MAC.algorithms.body, callProg, returnProg,
      List.nil_append, ↓reduceDIte, MAC.algorithms.replyLaw, htag]
  | verify =>
    rcases x with ⟨k, m, t⟩
    simp only [Program.memorylessReplyLaw, MAC.algorithms.body, returnProg,
      MAC.algorithms.replyLaw, ProbDist.single]

/-- `MAC.algorithms` on `MACAlgorithms K M T q` is the memoryless system of its reply laws. -/
theorem MAC.algorithms.eq_ofMemoryless
    -- `mac` gives the tagging law and verification predicate; `q` is the total query budget.
    (mac : MAC K M T) (q : ℕ) :
    MAC.algorithms (budget := q) mac =
      TypedSystem.ofMemoryless (MACAlgorithms K M T q) (MAC.algorithms.replyLaw mac) := by
  rw [MAC.algorithms, MAC.algorithms.program, MAC.algorithms.randomness]
  refine TypedConverter.ofProgram_smul_ofMemoryless (A := MACAlgorithms K M T q)
    (B := Interface.source (lawType (MAC.algorithms.law1 mac)) (1 * q))
    (none : Option Unit) (MAC.algorithms.body mac) (MAC.algorithms.bound_spec mac) _
    (TypedSystem.source_eq_ofMemoryless (MAC.algorithms.law1 mac) (1 * q))
    (MAC.algorithms.memorylessReplyLaw_eq mac)

end

end Commons

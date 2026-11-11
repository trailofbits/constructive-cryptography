module

public import Commons.Definitions.ReplyTransform
public import RandomSystems.Typed.Filter

/-!
# Reply transformation clients

`flippedBitSource` applies `Bool.not` to fresh fair bits with two permitted evaluations.
Its contract uses the normalized mapped law directly. A zero-query source checks the empty
domain. `falseQueries` admits only Boolean queries equal to `false`; projecting pair replies
preserves that restriction and its two-query allowance.
-/

@[expose] public section

namespace Tests.ReplyTransform

open Commons Commons.Evaluation SystemAlgebra Probability.Distribution

/-- Each of two permitted evaluations draws a fresh fair bit and returns its negation. -/
noncomputable def flippedBitSource :
    TypedSystem (Evaluation.perPort Unit Bool (fun _ => 2)) :=
  mapReplies Bool.not (fun _ => 2) •
    MemorylessSource.perPort Bool 𝒰[Bool] (budget := fun _ => 2)

/-- Negating each fresh fair bit yields the source of the pushed-forward law. -/
lemma flippedBitSource_eq :
    flippedBitSource =
      MemorylessSource.perPort Bool ((𝒰[Bool]).map Bool.not) (budget := fun _ => 2) := by
  rw [flippedBitSource, mapReplies_smul_memorylessSource]

example :
    TypedConverter.mapReplies (Interface.source Bool 2) (fun _ => Bool.not) •
        TypedSystem.source 𝒰[Bool] 2 =
      TypedSystem.source ((𝒰[Bool]).map Bool.not) 2 := by
  rw [TypedConverter.mapReplies_smul_source]

-- Zero permitted queries still give a well-typed converter and source contract.
example :
    TypedConverter.mapReplies (Interface.source Bool 0) (fun _ => Bool.not) •
        TypedSystem.source 𝒰[Bool] 0 =
      TypedSystem.source ((𝒰[Bool]).map Bool.not) 0 := by
  rw [TypedConverter.mapReplies_smul_source]

/-- One port accepts at most two Boolean queries, each equal to `false`, and replies in `Bool²`. -/
abbrev falseQueries : Interface :=
  (Interface.queryBudget Unit (fun _ => Bool) (fun _ => Bool × Bool) 2).restrict
    (fun xs => ∀ x ∈ xs, x.2 = false)
    (fun _ _ hp hd x hx => hd x (hp.subset hx))

-- Project the fresh pair reply while retaining the restricted query domain.
example :
    TypedConverter.mapReplies falseQueries (fun _ => Prod.snd) •
        TypedSystem.ofMemoryless falseQueries (fun _ _ => 𝒰[Bool × Bool]) =
      TypedSystem.ofMemoryless (falseQueries.withReplies (fun _ => Bool))
        (fun _ _ => (𝒰[Bool × Bool]).map Prod.snd) := by
  rw [TypedConverter.mapReplies_smul_ofMemoryless]

example : (falseQueries.withReplies (fun _ => Bool)).domain = falseQueries.domain := rfl

-- Changing reply alphabets preserves both admitted and rejected queries.
example : (falseQueries.withReplies (fun _ => Bool)).domain [⟨(), false⟩] := by
  norm_num [falseQueries, Interface.restrict, Interface.queryBudget]

example : ¬ (falseQueries.withReplies (fun _ => Bool)).domain [⟨(), true⟩] := by
  intro admitted
  exact Bool.noConfusion (admitted.2 ⟨(), true⟩ (List.mem_singleton_self _))

#print axioms TypedConverter.mapReplies_smul_ofMemoryless
#print axioms mapReplies_smul_memorylessSource
#print axioms flippedBitSource_eq

end Tests.ReplyTransform

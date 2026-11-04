module

public import Commons.Definitions.ReplyTransform

/-!
# Reply transformation clients

A client supplies an ordinary function and rewrites with its source contract.
`TypedConverter.mapReplies`
accepts arbitrary restricted input domains, including an empty source domain.
-/

@[expose] public section

namespace Tests.ReplyTransform

open Commons Commons.Evaluation SystemAlgebra Probability.Distribution

-- `f` maps finite inside replies `X` to finite outside replies `Y`; `P` is the fresh inside law.
variable {X Y : Type} [Fintype X] [Fintype Y] (f : X → Y) (P : ProbDist X)

example (q : ℕ) :
    mapReplies f (fun _ => q) • MemorylessSource.perPort X P (budget := fun _ => q) =
      MemorylessSource.perPort Y (P.map f) (budget := fun _ => q) := by
  rw [mapReplies_smul_memorylessSource]

-- Zero permitted queries still give a well-typed converter and source contract.
example :
    TypedConverter.mapReplies (Interface.source X 0) (fun _ => f) • TypedSystem.source P 0 =
      TypedSystem.source (P.map f) 0 := by
  rw [TypedConverter.mapReplies_smul_source]

-- `A` may restrict query values and their order; reply mapping leaves that domain intact.
example (A : Interface) (g : ∀ i, A.Y i → Y) (ν : ∀ i, A.X i → ProbDist (A.Y i)) :
    TypedConverter.mapReplies A g • TypedSystem.ofMemoryless A ν =
      TypedSystem.ofMemoryless (A.withReplies (fun _ => Y)) (fun i x => (ν i x).map (g i)) := by
  rw [TypedConverter.mapReplies_smul_ofMemoryless]

example (A : Interface) :
    (A.withReplies (fun _ => Y)).domain = A.domain := rfl

#print axioms TypedConverter.mapReplies_smul_ofMemoryless
#print axioms mapReplies_smul_memorylessSource

end Tests.ReplyTransform

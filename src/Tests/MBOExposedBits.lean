module

public import Tests.GameEventReflection

/-!
# Unset bits through a tagged connection

The existing two-call interaction exposes an unset reply when both inside bits are unset.
The same law applies before its last outside reply. Changing that reply's bit to true violates
`TaggedMBO` while leaving the inside replies unchanged.
-/

@[expose] public section

namespace Tests.MBOExposedBits

open SystemAlgebra Tests.GameEventReflection

/-- Both inside replies are false, and the completed outside reply carries that same bit. -/
lemma completed_tagged : TaggedMBO (RandomSystem.parallelLeft (completed false)) := by
  change TaggedMBO (U := outside.X) (V := outside.Y) (X := inside.X) (Y := inside.Y)
    ((([] ++
    [(⟨⟨none, ()⟩, ()⟩, ⟨⟨some (), ()⟩, ()⟩)]) ++
    [(⟨⟨some (), ()⟩, (false, false)⟩, ⟨⟨some (), ()⟩, ()⟩)]) ++
    [(⟨⟨some (), ()⟩, (false, false)⟩, ⟨⟨none, ()⟩, (false, false)⟩)])
  exact taggedMBO_snoc.mpr ⟨taggedMBO_snoc.mpr
    ⟨taggedMBO_snoc.mpr ⟨by simp [TaggedMBO], rfl⟩, rfl⟩, rfl⟩

/-- The two retained inside replies both have their MBO unset. -/
lemma completed_inside_false :
    ∀ z ∈ RandomSystem.parallelRight (completed false), z.2.2.2 = false := by
  intro z hz
  change z ∈ [(⟨(), ()⟩, ⟨(), (false, false)⟩),
    (⟨(), ()⟩, ⟨(), (false, false)⟩)] at hz
  rcases (List.mem_cons.mp hz) with rfl | hz
  · rfl
  · obtain rfl := List.mem_singleton.mp hz
    rfl

/-- Each query and reply in the five-exchange interaction belongs to the same component. -/
lemma completed_consistent : RandomSystem.parallelConsistent (completed false) := by
  intro z hz
  simp only [completed, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The bridge derives the outside bit from the inside bits and the actual tagged execution. -/
theorem completed_exposed_false : ∀ v ∈
    exposedReplies (resourceRoute (U := outside.X)) ((completed false).map Prod.snd),
    v.2.2 = false :=
  exposedReplies_all_false_of_parallelRight_all_false (completed_follows false)
    completed_consistent completed_tagged completed_inside_false

/-- Before the last outside reply, the same bit-transport law needs no completion certificate. -/
example :
    (connectionQueries (resourceRoute (U := outside.X)) resourceInput [⟨(), ()⟩]
      (((completed false).take 4).map Prod.snd)).Dom ∧
    ∀ v ∈ exposedReplies (resourceRoute (U := outside.X))
      (((completed false).take 4).map Prod.snd), v.2.2 = false := by
  constructor
  · exact Nat.zero_lt_succ 0
  · apply exposedReplies_all_false_of_parallelRight_all_false
      ((completed_follows false).of_prefix (List.take_prefix 4 _))
    · exact fun z hz => completed_consistent z ((List.take_prefix 4 _).subset hz)
    · have tagged : TaggedMBO (RandomSystem.parallelLeft ((completed false).take 4) ++
          [(⟨⟨some (), ()⟩, (false, false)⟩, ⟨⟨none, ()⟩, (false, false)⟩)]) :=
        completed_tagged
      exact (taggedMBO_snoc.mp tagged).1
    · exact completed_inside_false

/-- Keep the first four exchanges and change only the exposed reply's MBO to true. -/
def mismatched : List (JointQuery × JointReply) :=
  (completed false).take 4 ++
    [(⟨none, ⟨⟨some (), ()⟩, (false, false)⟩⟩,
      ⟨none, ⟨⟨none, ()⟩, (false, true)⟩⟩)]

/-- A forged true outside bit cannot satisfy the forwarding contract. -/
example : ¬ TaggedMBO (RandomSystem.parallelLeft mismatched) := by
  intro tagged
  change TaggedMBO (RandomSystem.parallelLeft ((completed false).take 4) ++
    [(⟨⟨some (), ()⟩, (false, false)⟩, ⟨⟨none, ()⟩, (false, true)⟩)]) at tagged
  have last := (taggedMBO_snoc.mp tagged).2
  have output := congrArg outputMBO last
  change some true = some false at output
  cases output

#print axioms TaggedMBO.outputMBO_eq_false_of_inputMBO_eq_false
#print axioms exposedReplies_all_false_of_parallelRight_all_false
#print axioms completed_exposed_false

end Tests.MBOExposedBits

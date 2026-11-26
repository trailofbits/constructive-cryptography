module

public import RandomSystems.DDC.DDCRelabel

/-!
# Attachment with partial resources and noninjective maps

A forwarding converter calls a resource that replies twice and then stops. Query reduction
modulo two and reply reduction modulo three commute across attachment, including the
undefined third response. The two individual map directions retain the same contracts.
-/

@[expose] public section

namespace Tests.AttachmentRelabel

open SystemAlgebra

/-- Reply to query `n` by `n+1`, then `n+2`; stop before the third reply. -/
def twoReplies : InterfaceSystem Unit (fun _ => ℕ) (fun _ => ℕ)
  | [q] => Part.some ⟨(), q.2 + 1⟩
  | [_, q] => Part.some ⟨(), q.2 + 2⟩
  | _ => Part.none

/-- Reduce each query modulo two, retaining its unit port. -/
def queryMap (q : Σ _ : Unit, ℕ) : Σ _ : Unit, ℕ := ⟨(), q.2 % 2⟩

/-- Reduce each reply modulo three, retaining its unit port. -/
def replyMap (y : Σ _ : Unit, ℕ) : Σ _ : Unit, ℕ := ⟨(), y.2 % 3⟩

example : queryMap ⟨(), 1⟩ = queryMap ⟨(), 3⟩ := rfl
example : replyMap ⟨(), 1⟩ = replyMap ⟨(), 4⟩ := rfl

/-- The actual attached forwarding system has the mapped resource's complete history function. -/
lemma combined_attachment :
    apply (relabel (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
      (insideMap replyMap) (insideMap queryMap)) twoReplies =
      relabel twoReplies queryMap replyMap := by
  rw [apply_relabel_inside_both]
  exact apply_forwardAll (by simp [SilentAtEmpty, relabel, twoReplies])

/-- The first mapped input `3 ↦ 1` receives `2 ↦ 2`. -/
example :
    apply (relabel (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
      (insideMap replyMap) (insideMap queryMap)) twoReplies [⟨(), 3⟩] =
      Part.some ⟨(), 2⟩ := by
  rw [combined_attachment]
  rfl

/-- The same attachment preserves the partial resource's missing third reply. -/
example :
    apply (relabel (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
      (insideMap replyMap) (insideMap queryMap)) twoReplies
        [⟨(), 3⟩, ⟨(), 5⟩, ⟨(), 7⟩] = Part.none := by
  rw [combined_attachment]
  exact Part.map_none replyMap

example :
    apply (relabel (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
      id (insideMap queryMap)) twoReplies =
      apply (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
        (relabel twoReplies queryMap id) :=
  apply_relabel_inside_queries _ _ queryMap

example :
    apply (relabel (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
      (insideMap replyMap) id) twoReplies =
      apply (forwardAll Unit (fun _ => ℕ) (fun _ => ℕ))
        (relabel twoReplies id replyMap) :=
  apply_relabel_inside _ _ replyMap

#print axioms SystemAlgebra.insideMap_id
#print axioms SystemAlgebra.apply_relabel_inside_both
#print axioms SystemAlgebra.apply_relabel_inside
#print axioms SystemAlgebra.apply_relabel_inside_queries
#print axioms combined_attachment

end Tests.AttachmentRelabel

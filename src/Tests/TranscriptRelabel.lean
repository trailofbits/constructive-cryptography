module

public import RandomSystems.Distance.Coupling

/-!
# Transcript relabeling with partial interaction

Two distinct natural replies collapse to one visible value. The system then refuses a third
query, although its environment keeps asking. A second environment stops after one reply.
-/

@[expose] public section

namespace Tests.TranscriptRelabel

open SystemAlgebra

/-- Answer the first query with `0`, the second with `2`, and no others. -/
def twoReplies : System Unit ℕ
  | [_] => Part.some 0
  | [_, _] => Part.some 2
  | _ => Part.none

/-- Erase the reply value: in particular, `0` and `2` have the same visible image. -/
def eraseReply (_ : ℕ) : Unit := ()

/-- Ask again after every visible reply history. -/
def askForever : List Unit →. Unit := fun _ => Part.some ()

/-- Ask once, then stop after receiving the first reply. -/
def askOnce : List Unit →. Unit
  | [] => Part.some ()
  | _ :: _ => Part.none

/-- The many-to-one map really identifies the two replies observed in the test. -/
example : eraseReply 0 = eraseReply 2 ∧ (0 : ℕ) ≠ 2 :=
  ⟨rfl, Nat.zero_ne_add_one 1⟩

/-- The original interaction stops at the system's undefined third reply. -/
lemma original_transcript :
    twoReplies.tr (fun ys => askForever (ys.map eraseReply)) 4 = [((), 0), ((), 2)] := by
  simp only [System.tr, askForever, Part.some_dom, ↓reduceDIte, twoReplies,
    List.map_nil, Part.get_some, List.nil_append, List.map_cons, List.cons_append,
    Part.not_none_dom]

/-- Relabeling preserves that partial stop and maps both distinct replies to `()`. -/
example : (relabel twoReplies id eraseReply).tr askForever 4 = [((), ()), ((), ())] := by
  rw [System.tr_relabel_output, original_transcript]
  rfl

/-- Stopping by the environment also commutes with the same reply map. -/
example : (relabel twoReplies id eraseReply).tr askOnce 4 = [((), ())] := by
  rw [System.tr_relabel_output]
  simp only [System.tr, askOnce, List.map_nil, Part.some_dom, ↓reduceDIte, twoReplies,
    Part.get_some, List.nil_append, List.map_cons, Part.not_none_dom, Prod.map_apply, id_eq]

#print axioms System.tr_relabel_output
#print axioms original_transcript

end Tests.TranscriptRelabel

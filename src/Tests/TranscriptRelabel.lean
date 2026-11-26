module

public import RandomSystems.System.Transcript

/-!
# Transcript relabeling with partial interaction

Two distinct natural replies collapse to one visible value. The system then refuses a third
query, although its environment keeps asking. Query maps may also identify distinct values;
early-stopping callers and the zero horizon retain their behavior.
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

/-- Both Boolean outside queries address the same inside unit query. -/
def eraseQuery (_ : Bool) : Unit := ()

/-- Ask `true` first and `false` thereafter, without stopping. -/
def askBoolean : List Unit →. Bool := fun ys => Part.some ys.isEmpty

/-- Ask `true` once and stop after the first natural-number reply. -/
def askBooleanOnce : List ℕ →. Bool
  | [] => Part.some true
  | _ :: _ => Part.none

example : eraseQuery false = eraseQuery true ∧ false ≠ true :=
  ⟨rfl, Bool.false_ne_true⟩

/-- Noninjective query and reply maps preserve the system's refusal of its third query. -/
lemma combined_transcript :
    ((relabel twoReplies eraseQuery eraseReply).tr askBoolean 4).map
      (Prod.map eraseQuery id) = [((), ()), ((), ())] := by
  have caller : (fun ys : List ℕ => (askBoolean (ys.map eraseReply)).map eraseQuery) =
      (fun ys => askForever (ys.map eraseReply)) := by
    funext ys
    rfl
  rw [System.tr_relabel, caller, original_transcript]
  rfl

/-- Query relabeling retains the caller's early stop. -/
example : ((relabel twoReplies eraseQuery id).tr askBooleanOnce 4).map
    (Prod.map eraseQuery id) = [((), 0)] := by
  rw [System.tr_relabel_input]
  simp only [System.tr, askBooleanOnce, Part.map, List.map_nil, Part.some_dom,
    ↓reduceDIte, twoReplies, Part.get_some, List.nil_append, List.map_cons,
    Part.not_none_dom]

/-- A zero observation horizon returns no exchanges, independently of both maps. -/
example : (relabel twoReplies eraseQuery eraseReply).tr askBoolean 0 = [] := rfl

#print axioms System.tr_relabel
#print axioms System.tr_relabel_input
#print axioms combined_transcript

#print axioms System.tr_relabel_output
#print axioms original_transcript

end Tests.TranscriptRelabel

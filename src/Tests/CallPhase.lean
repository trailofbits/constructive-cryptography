module

public import RandomSystems.Converter.ConditionalCall

/-!
# Direct-call phase regression

A Boolean query `true` returns `false` locally; `false` queries the inside and forwards its
reply. The tests cover a pending call, the local branch, and a second invocation after a reply.
The new phase law applies to actual transcripts supplied by the fixed-function call law.
-/

@[expose] public section

namespace SystemAlgebra.Tests.CallPhase

/-- One port carrying Boolean values on either side of the converter. -/
abbrev Message := Σ l : Two Unit Unit, twoFam (fun _ => Bool) (fun _ => Bool) l

/-- An outside message carrying `b`. -/
def outside (b : Bool) : Message := ⟨⟨none, ()⟩, b⟩

/-- An inside message carrying `b`. -/
def inside (b : Bool) : Message := ⟨⟨some (), ()⟩, b⟩

/-- The local branch is selected by the query `true`. -/
def pureBranch (u : Σ _ : Unit, Bool) : Prop := u.2 = true

instance : DecidablePred pureBranch := fun u => inferInstanceAs (Decidable (u.2 = true))

/-- `true` returns `false`; `false` makes one query and forwards its reply. -/
def call (u : Σ _ : Unit, Bool) (rs : List (Σ _ : Unit, Bool)) :
    Bool ⊕ (Σ _ : Unit, Bool) :=
  conditionalCall pureBranch (fun _ => false) id (fun _ r => r.2) u rs

/-- The converter uses the same conditional rule at every outside invocation. -/
noncomputable def converter :=
  callConverter (O := Unit) (J := Unit) (U := fun _ => Bool) (V := fun _ => Bool)
    (X := fun _ => Bool) (Y := fun _ => Bool) call (fun _ => True)

/-- An inside query can occur only before this invocation receives its first reply. -/
lemma phase (u : Σ _ : Unit, Bool) (rs : List (Σ _ : Unit, Bool))
    (h : (call u rs).isRight = true) : rs = [] := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    by_cases hp : pureBranch u <;>
      simp only [call, conditionalCall, hp, ↓reduceIte, Sum.isRight_inl,
        Bool.false_eq_true] at h

/-- Two `false` queries, each answered `true` by the inside, form a valid converter transcript. -/
lemma two_calls : Replies converter
    [outside false, inside true, outside false, inside true]
    [inside false, outside true, inside false, outside true] := by
  unfold converter call
  have h := replies_conditionalCallConverter_ofFunction
    pureBranch (fun _ => false) id (fun _ r => r.2)
    (F := fun _ => True) (fun {_ _} _ _ _ => trivial)
    (fun _ b => !b) [⟨(), false⟩, ⟨(), false⟩] trivial
  simpa only [conditionalCallConverter, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, pureBranch, Bool.false_eq_true, ↓reduceIte, id_eq,
    callTranscript, callSteps, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Bool.not_false, outside, inside] using h

/-- The first inside reply is admitted while the invocation has no earlier replies. -/
example : ∃ u, currentCall [outside false].reverse [] = some (u, []) := by
  have hr : Replies converter
      ([outside false] ++ [inside true] ++ [outside false] ++ [inside true])
      ([inside false] ++ [outside true] ++ [inside false] ++ [outside true]) := two_calls
  have hr := (replies_snoc.mp (replies_snoc.mp (replies_snoc.mp hr).1).1).1
  exact callConverter_currentCall_of_admits_inside (V := fun _ => Bool)
    call phase (fun _ => True)
    [(outside false, inside false)] hr ⟨(), true⟩ rfl

/-- A completed first call does not carry its `true` reply into the pending second call. -/
example : ∃ u,
    currentCall [outside false, inside true, outside false].reverse [] = some (u, []) := by
  have hr : Replies converter
      ([outside false, inside true, outside false] ++ [inside true])
      ([inside false, outside true, inside false] ++ [outside true]) := two_calls
  have hr := (replies_snoc.mp hr).1
  exact callConverter_currentCall_of_admits_inside (V := fun _ => Bool)
    call phase (fun _ => True)
    [(outside false, inside false), (inside true, outside true),
      (outside false, inside false)] hr ⟨(), false⟩ rfl

/-- The zero-query branch has an actual reply and admits no subsequent inside reply. -/
example : Replies converter [outside true] [outside false] ∧
    ¬ converterAdmits [(outside true, outside false)] (inside true) := by
  constructor
  · unfold converter call
    have h := replies_conditionalCallConverter_ofFunction
      pureBranch (fun _ => false) id (fun _ r => r.2)
      (F := fun _ => True) (fun {_ _} _ _ _ => trivial)
      (fun _ b => !b) [⟨(), true⟩] trivial
    simpa only [conditionalCallConverter, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, pureBranch, ↓reduceIte, callTranscript, callSteps,
      List.map_cons, List.map_nil, outside, inside] using h
  · intro h
    cases h

#print axioms callConverter_currentCall_of_admits_inside

end SystemAlgebra.Tests.CallPhase

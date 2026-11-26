module

public import RandomSystems.Converter.CallRelabel

/-!
# Current-call message-map regression

Inside replies carry a Boolean port and a pair of bits. The map forgets the port and the second
bit, retaining the first at the single target port. Outside ports and values are natural numbers.
-/

@[expose] public section

namespace SystemAlgebra.Tests.CallRelabel

/-- Outside inputs are natural numbers; inside messages carry a Boolean port and two bits. -/
abbrev Input := Σ l : Two Nat Bool, twoFam (fun _ => Nat) (fun _ => Bool × Bool) l

/-- `forget (j, (b, c)) = ((), b)` identifies ports and drops the second bit. -/
def forget (r : Σ _ : Bool, Bool × Bool) : Σ _ : Unit, Bool := ⟨(), r.2.1⟩

/-- Outside input `7` at port `3`. -/
def outside : Input := ⟨⟨none, 3⟩, 7⟩

/-- Inside message `(b,c)` at Boolean port `j`. -/
def reply (j b c : Bool) : Input := ⟨⟨some (), j⟩, (b, c)⟩

/-- Mapping preserves the retained outside input of a pending call. -/
example : currentCall ([outside].map (insideMap forget)) [] = some (⟨3, 7⟩, []) := by
  exact (currentCall_insideMap forget [outside] []).trans rfl

/-- The newest call's reply is retained; the preceding invocation and its reply are discarded. -/
example : currentCall
    ([reply false true false, outside, reply true false true, outside].map (insideMap forget))
    [] = some (⟨3, 7⟩, [⟨(), true⟩]) := by
  exact (currentCall_insideMap forget
    [reply false true false, outside, reply true false true, outside] []).trans rfl

/-- Two different inside messages become the same retained reply. -/
example :
    currentCall ([reply false true false, outside].map (insideMap forget)) [] =
      currentCall ([reply true true true, outside].map (insideMap forget)) [] := by
  calc
    _ = (currentCall [reply false true false, outside] []).map
        (fun (u, rs) => (u, rs.map forget)) := currentCall_insideMap forget _ []
    _ = (currentCall [reply true true true, outside] []).map
        (fun (u, rs) => (u, rs.map forget)) := rfl
    _ = _ := (currentCall_insideMap forget _ []).symm

/-- An accumulator alone does not create an invocation when there is no outside input. -/
example : currentCall (([] : List Input).map (insideMap forget))
    ([⟨false, (true, false)⟩].map forget) = none := by
  exact (currentCall_insideMap forget ([] : List Input) [⟨false, (true, false)⟩]).trans rfl

#print axioms currentCall_insideMap

end SystemAlgebra.Tests.CallRelabel

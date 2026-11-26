module

public import RandomSystems.Converter.Calls
public import RandomSystems.DDC.DDCRelabel

/-!
# Changing the inside messages of a call

`currentCall_insideMap` maps the replies of the current invocation while retaining its outside
input. The map may change inside ports or identify different replies. This lets a converter
presentation change its inside message representation without reconstructing its call history.
-/

@[expose] public section

namespace SystemAlgebra

/-- Mapping inside messages commutes with reading the current invocation:
`(u, replies) ↦ (u, replies.map f)`. The same map acts on the reply accumulator `rs`. -/
lemma currentCall_insideMap
    -- `O` carries outside ports and `U o` their inputs; `J`, `J'` carry the two inside formats.
    {O J J' : Type} {U : O → Type} {Y : J → Type} {Y' : J' → Type}
    -- `f` changes the complete inside message, including its port; outside inputs stay fixed.
    (f : (Σ j, Y j) → Σ j, Y' j)
    -- `h` lists inputs newest first; `rs` contains the replies collected so far.
    (h : List (Σ l, twoFam U Y l)) (rs : List (Σ j, Y j)) :
    currentCall (h.map (insideMap f)) (rs.map f) =
      (currentCall h rs).map (fun (u, replies) => (u, replies.map f)) := by
  induction h generalizing rs with
  | nil => rfl
  | cons z h ih =>
    rcases z with ⟨⟨_ | ⟨⟩, i⟩, z⟩
    · rfl
    -- An inside reply is mapped before it is added to this invocation's accumulator.
    · simpa only [List.map_cons, insideMap, currentCall, Sigma.eta] using ih (⟨i, z⟩ :: rs)

end SystemAlgebra
